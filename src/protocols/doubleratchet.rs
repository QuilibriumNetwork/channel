use ed448_goldilocks_plus::elliptic_curve::ops::MulByGenerator;
use ed448_goldilocks_plus::{subtle, CompressedEdwardsY, EdwardsPoint, Scalar};
use rand::rngs::OsRng;
use rand::RngCore;
use sha2::Sha512;
use hkdf::Hkdf;
use aes_gcm::{Aes256Gcm, Nonce};
use aes_gcm::aead::{Aead, Payload};
use std::collections::HashMap;
use subtle::ConstantTimeEq;

const DOUBLE_RATCHET_PROTOCOL_VERSION: u16 = 1;
const DOUBLE_RATCHET_PROTOCOL: u16 = 1 << 8 + DOUBLE_RATCHET_PROTOCOL_VERSION;

const CHAIN_KEY: u8 = 0x01;
const MESSAGE_KEY: u8 = 0x02;
const AEAD_KEY: u8 = 0x03;

pub struct DoubleRatchetParticipant {
    sending_ephemeral_private_key: Scalar,
    receiving_ephemeral_key: EdwardsPoint,
    root_key: Vec<u8>,
    sending_chain_key: Vec<u8>,
    current_sending_header_key: Vec<u8>,
    current_receiving_header_key: Vec<u8>,
    next_sending_header_key: Vec<u8>,
    next_receiving_header_key: Vec<u8>,
    receiving_chain_key: Vec<u8>,
    current_sending_chain_length: u32,
    previous_sending_chain_length: u32,
    current_receiving_chain_length: u32,
    previous_receiving_chain_length: u32,
    skipped_keys_map: HashMap<Vec<u8>, HashMap<u32, Vec<u8>>>,
}

#[derive(Clone, Debug)]
pub struct MessageCiphertext {
    pub ciphertext: Vec<u8>,
    pub initialization_vector: Vec<u8>,
    pub associated_data: Option<Vec<u8>>,
}

#[derive(Clone, Debug)]
pub struct P2PChannelEnvelope {
    pub protocol_identifier: u16,
    pub message_header: MessageCiphertext,
    pub message_body: MessageCiphertext,
}

impl DoubleRatchetParticipant {
    pub fn new(
        session_key: &[u8],
        sending_header_key: &[u8],
        next_receiving_header_key: &[u8],
        is_sender: bool,
        sending_ephemeral_private_key: Scalar,
        receiving_ephemeral_key: EdwardsPoint,
    ) -> Result<Self, Box<dyn std::error::Error>> {
        let mut participant = DoubleRatchetParticipant {
            sending_ephemeral_private_key,
            receiving_ephemeral_key,
            root_key: vec![],
            sending_chain_key: vec![],
            current_sending_header_key: sending_header_key.to_vec(),
            current_receiving_header_key: vec![],
            next_sending_header_key: vec![],
            next_receiving_header_key: next_receiving_header_key.to_vec(),
            receiving_chain_key: vec![],
            current_sending_chain_length: 0,
            previous_sending_chain_length: 0,
            current_receiving_chain_length: 0,
            previous_receiving_chain_length: 0,
            skipped_keys_map: HashMap::new(),
        };

        if is_sender {
            let dh_output = receiving_ephemeral_key * sending_ephemeral_private_key;
            let hkdf = Hkdf::<Sha512>::new(Some(session_key), &dh_output.compress().to_bytes());
            let mut rkck = [0u8; 96];
            let err = hkdf.expand(b"quilibrium-double-ratchet", &mut rkck);
            if err.is_err() {
              return Err("invalid length".into());
            }

            participant.root_key = rkck[..32].to_vec();
            participant.sending_chain_key = rkck[32..64].to_vec();
            participant.next_sending_header_key = rkck[64..].to_vec();
        } else {
            participant.root_key = session_key.to_vec();
            participant.next_sending_header_key = next_receiving_header_key.to_vec();
            participant.next_receiving_header_key = sending_header_key.to_vec();
        }
  
        Ok(participant)
    }

    pub fn ratchet_encrypt(&mut self, message: &[u8]) -> Result<P2PChannelEnvelope, Box<dyn std::error::Error>> {
        let mut envelope = P2PChannelEnvelope {
            protocol_identifier: DOUBLE_RATCHET_PROTOCOL,
            message_header: MessageCiphertext::default(),
            message_body: MessageCiphertext::default(),
        };

        let (new_chain_key, message_key, aead_key) = ratchet_keys(&self.sending_chain_key);
        self.sending_chain_key = new_chain_key;

        let header = self.encode_header();
        envelope.message_header = self.encrypt(&header, &self.current_sending_header_key, None)?;

        envelope.message_body = self.encrypt(
            message,
            &message_key,
            Some(&[&aead_key[..], &envelope.message_header.ciphertext[..]].concat()),
        )?;

        self.current_sending_chain_length += 1;

        Ok(envelope)
    }

    pub fn ratchet_decrypt(&mut self, envelope: &P2PChannelEnvelope) -> Result<Vec<u8>, Box<dyn std::error::Error>> {
        if let Some(plaintext) = self.try_skipped_message_keys(envelope)? {
            return Ok(plaintext);
        }

        let (header, should_ratchet) = self.decrypt_header(&envelope.message_header, &self.current_receiving_header_key)?;

        let (receiving_ephemeral_key, previous_receiving_chain_length, current_receiving_chain_length) = 
            self.decode_header(&header)?;

        if should_ratchet {
            self.skip_message_keys(previous_receiving_chain_length)?;
            self.ratchet_ephemeral_keys(&receiving_ephemeral_key)?;
        }

        self.skip_message_keys(current_receiving_chain_length)?;

        let (new_chain_key, message_key, aead_key) = ratchet_keys(&self.receiving_chain_key);

        let plaintext = self.decrypt(
            &envelope.message_body,
            &message_key,
            Some(&[&aead_key[..], &envelope.message_header.ciphertext[..]].concat()),
        )?;

        self.receiving_chain_key = new_chain_key;
        self.current_receiving_chain_length += 1;

        Ok(plaintext)
    }

    fn ratchet_ephemeral_keys(&mut self, new_receiving_ephemeral_key: &EdwardsPoint) -> Result<(), Box<dyn std::error::Error>> {
        self.previous_sending_chain_length = self.current_sending_chain_length;
        self.current_sending_chain_length = 0;
        self.current_receiving_chain_length = 0;
        self.current_sending_header_key = self.next_sending_header_key.clone();
        self.current_receiving_header_key = self.next_receiving_header_key.clone();
        self.receiving_ephemeral_key = *new_receiving_ephemeral_key;
    
        // Perform DH and KDF to get new root key and receiving chain key
        let dh_output = new_receiving_ephemeral_key * self.sending_ephemeral_private_key;
        let hkdf = Hkdf::<Sha512>::new(Some(&self.root_key), &dh_output.compress().to_bytes());
        let mut rkck = [0u8; 96];
        hkdf.expand(b"quilibrium-double-ratchet", &mut rkck);
    
        self.root_key = rkck[..32].to_vec();
        self.receiving_chain_key = rkck[32..64].to_vec();
        self.next_receiving_header_key = rkck[64..].to_vec();
    
        // Generate new sending ephemeral key
        self.sending_ephemeral_private_key = Scalar::random(&mut OsRng);
    
        // Perform DH and KDF to get new root key and sending chain key
        let dh_output = new_receiving_ephemeral_key * self.sending_ephemeral_private_key;
        let hkdf = Hkdf::<Sha512>::new(Some(&self.root_key), &dh_output.compress().to_bytes());
        let mut rkck2 = [0u8; 96];
        hkdf.expand(b"quilibrium-double-ratchet", &mut rkck2);
    
        self.root_key = rkck2[..32].to_vec();
        self.sending_chain_key = rkck2[32..64].to_vec();
        self.next_sending_header_key = rkck2[64..].to_vec();
        
        Ok(())
    }

    fn try_skipped_message_keys(&self, envelope: &P2PChannelEnvelope) -> Result<Option<Vec<u8>>, Box<dyn std::error::Error>> {
        for (receiving_header_key, skipped_keys) in &self.skipped_keys_map {
            if let Ok((header, _)) = self.decrypt_header(&envelope.message_header, receiving_header_key) {
                let (_, _, current) = self.decode_header(&header)?;
                if let Some(key_pair) = skipped_keys.get(&current) {
                    let message_key = &key_pair[..32];
                    let aead_key = &key_pair[32..];
                    return self.decrypt(
                        &envelope.message_body,
                        message_key,
                        Some(&[aead_key, &envelope.message_header.ciphertext[..]].concat()),
                    ).map(Some);
                }
            }
        }
        Ok(None)
    }

    fn skip_message_keys(&mut self, until: u32) -> Result<(), Box<dyn std::error::Error>> {
        if self.current_receiving_chain_length + 100 < until {
            return Err("Skip limit exceeded".into());
        }

        if !self.receiving_chain_key.is_empty() {
            while self.current_receiving_chain_length < until {
                let (new_chain_key, message_key, aead_key) = ratchet_keys(&self.receiving_chain_key);
                self.skipped_keys_map
                    .entry(self.current_receiving_header_key.clone())
                    .or_insert_with(HashMap::new)
                    .insert(self.current_receiving_chain_length, [&message_key[..], &aead_key[..]].concat());
                self.receiving_chain_key = new_chain_key;
                self.current_receiving_chain_length += 1;
            }
        }

        Ok(())
    }

    fn encode_header(&self) -> Vec<u8> {
        let mut header = Vec::new();
        header.extend_from_slice(&EdwardsPoint::mul_by_generator(&self.sending_ephemeral_private_key).compress().to_bytes());
        header.extend_from_slice(&self.previous_sending_chain_length.to_be_bytes());
        header.extend_from_slice(&self.current_sending_chain_length.to_be_bytes());
        header
    }

    fn decrypt_header(&self, ciphertext: &MessageCiphertext, receiving_header_key: &[u8]) 
        -> Result<(Vec<u8>, bool), Box<dyn std::error::Error>> {
        match self.decrypt(ciphertext, receiving_header_key, None) {
            Ok(header) => Ok((header, false)),
            Err(_) if receiving_header_key.ct_eq(self.current_receiving_header_key.as_slice()).into() => {
                self.decrypt(ciphertext, &self.next_receiving_header_key, None)
                    .map(|header| (header, true))
            },
            Err(e) => Err(e),
        }
    }

    fn decode_header(&self, header: &[u8]) -> Result<(EdwardsPoint, u32, u32), Box<dyn std::error::Error>> {
        if header.len() < 57 {  // 57 bytes for EdwardsPoint + 8 bytes for two u32
            return Err("Malformed header".into());
        }

        let receiving_ephemeral_key = CompressedEdwardsY(header[..57].try_into().unwrap()).decompress();
        if receiving_ephemeral_key.is_none().into() {
            return Err("Malformed point".into());
        }
        let previous_receiving_chain_length = u32::from_be_bytes(header[57..61].try_into()?);
        let current_receiving_chain_length = u32::from_be_bytes(header[61..65].try_into()?);

        Ok((receiving_ephemeral_key.unwrap(), previous_receiving_chain_length, current_receiving_chain_length))
    }

    fn encrypt(&self, plaintext: &[u8], key: &[u8], associated_data: Option<&[u8]>) 
      -> Result<MessageCiphertext, Box<dyn std::error::Error>> {
        use aes_gcm::KeyInit;
        let mut iv = [0u8; 12];
        OsRng.fill_bytes(&mut iv);

        let cipher = Aes256Gcm::new_from_slice(key).unwrap();
        let nonce = Nonce::from_slice(&iv);
        
        let mut associated_data = associated_data.unwrap_or(&[]);
        let mut aad = [0u8; 32];
        if associated_data.len() == 0 {
          OsRng.fill_bytes(&mut aad);
          associated_data = &aad
        }
        
        let ciphertext = cipher.encrypt(nonce, Payload{
            msg: plaintext,
            aad: associated_data,
        }).map_err(|e| format!("Encryption failed: {}", e))?;
      
      Ok(MessageCiphertext {
        ciphertext,
        initialization_vector: iv.to_vec(),
        associated_data: Some(associated_data.to_vec()),
      })
    }
    
    fn decrypt(&self, ciphertext: &MessageCiphertext, key: &[u8], associated_data: Option<&[u8]>) 
      -> Result<Vec<u8>, Box<dyn std::error::Error>> {
        use aes_gcm::KeyInit;
        if key.len() != 32 {
          return Err(format!("Invalid key length").into());
        }
        let cipher = Aes256Gcm::new_from_slice(key).unwrap();
        let nonce = Nonce::from_slice(&ciphertext.initialization_vector);

        let associated_data = associated_data.unwrap_or_else(|| ciphertext.associated_data.as_ref().unwrap());

        cipher.decrypt(nonce, Payload{
            msg: ciphertext.ciphertext.as_slice(),
            aad: associated_data,
        }).map_err(|e| format!("Decryption failed: {}", e).into())
    }

    pub fn rotate_sending_key(&mut self) -> Result<(), Box<dyn std::error::Error>> {
        self.sending_ephemeral_private_key = Scalar::random(&mut OsRng);
        self.ratchet_ephemeral_keys(&self.receiving_ephemeral_key.clone())
    }

    pub fn get_public_key(&self) -> EdwardsPoint {
        EdwardsPoint::mul_by_generator(&self.sending_ephemeral_private_key)
    }
}

fn ratchet_keys(input_key: &[u8]) -> (Vec<u8>, Vec<u8>, Vec<u8>) {
  use hmac::Mac;
  let mut aead_key = [0u8; 64];
  let mut message_key = [0u8; 64];
  let mut chain_key = [0u8; 64];

  let mut hmac_aead = hmac::Hmac::<Sha512>::new_from_slice(input_key).unwrap();
  hmac_aead.update(&[AEAD_KEY]);
  aead_key.copy_from_slice(&hmac_aead.finalize().into_bytes());

  let mut hmac_message = hmac::Hmac::<Sha512>::new_from_slice(input_key).unwrap();
  hmac_message.update(&[MESSAGE_KEY]);
  message_key.copy_from_slice(&hmac_message.finalize().into_bytes());

  let mut hmac_chain = hmac::Hmac::<Sha512>::new_from_slice(input_key).unwrap();
  hmac_chain.update(&[CHAIN_KEY]);
  chain_key.copy_from_slice(&hmac_chain.finalize().into_bytes());

  (chain_key[..32].to_vec(), message_key[..32].to_vec(), aead_key[..32].to_vec())
}

// Implementation for MessageCiphertext
impl Default for MessageCiphertext {
  fn default() -> Self {
      MessageCiphertext {
          ciphertext: Vec::new(),
          initialization_vector: Vec::new(),
          associated_data: None,
      }
  }
}

// Implementation for P2PChannelEnvelope
impl P2PChannelEnvelope {
  pub fn new(protocol_identifier: u16) -> Self {
      P2PChannelEnvelope {
          protocol_identifier,
          message_header: MessageCiphertext::default(),
          message_body: MessageCiphertext::default(),
      }
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use ed448_goldilocks_plus::Scalar;

  #[test]
  fn test_double_ratchet_communication() {
      let session_key = [0u8; 32];
      let sending_header_key = [1u8; 32];
      let next_receiving_header_key = [2u8; 32];

      let alice_ephemeral = Scalar::random(&mut OsRng);
      let bob_ephemeral = Scalar::random(&mut OsRng);

      let alice_public = EdwardsPoint::mul_by_generator(&alice_ephemeral);
      let bob_public = EdwardsPoint::mul_by_generator(&bob_ephemeral);

      let mut alice = DoubleRatchetParticipant::new(
          &session_key,
          &sending_header_key,
          &next_receiving_header_key,
          true,
          alice_ephemeral,
          bob_public,
      ).unwrap();

      let mut bob = DoubleRatchetParticipant::new(
          &session_key,
          &sending_header_key,
          &next_receiving_header_key,
          false,
          bob_ephemeral,
          alice_public,
      ).unwrap();

      // Test message exchange
      let message = b"Hello, Bob!";
      let envelope = alice.ratchet_encrypt(message).unwrap();

      let decrypted = bob.ratchet_decrypt(&envelope).unwrap();
      assert_eq!(message, decrypted.as_slice());

      let response = b"Hello, Alice!";
      let envelope = bob.ratchet_encrypt(response).unwrap();
      let delayed = alice.ratchet_encrypt(b"force another step").unwrap();
      let decrypted = alice.ratchet_decrypt(&envelope).unwrap();
      assert_eq!(response, decrypted.as_slice());

      // Test multiple messages
      for _ in 0..10 {
          let message = b"Secure communication test";
          let envelope = alice.ratchet_encrypt(message).unwrap();
          let decrypted = bob.ratchet_decrypt(&envelope).unwrap();
          assert_eq!(message, decrypted.as_slice());

          let response = b"Acknowledged";
          let envelope = bob.ratchet_encrypt(response).unwrap();
          let decrypted = alice.ratchet_decrypt(&envelope).unwrap();
          assert_eq!(response, decrypted.as_slice());
      }

      let decrypted = bob.ratchet_decrypt(&delayed).unwrap();
      assert_eq!(b"force another step", decrypted.as_slice());
  }
}