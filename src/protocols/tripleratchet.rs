use std::collections::HashMap;
use std::hash::Hash;
use ed448_goldilocks_plus::elliptic_curve::group::GroupEncoding;
use ed448_goldilocks_plus::elliptic_curve::Group;
use rand::rngs::OsRng;
use rand::{CryptoRng, RngCore};
use sha2::{Sha512, Digest};
use hkdf::Hkdf;
use aes_gcm::{Aes256Gcm, Key, KeyInit, Nonce};
use aes_gcm::aead::{Aead, Payload};
use ed448_goldilocks_plus::{subtle, CompressedEdwardsY, EdwardsPoint, Scalar};
use serde::{Serialize, Deserialize};
use thiserror::Error;
use subtle::ConstantTimeEq;

use super::doubleratchet::{DoubleRatchetParticipant, MessageCiphertext, P2PChannelEnvelope};
use super::feldman::{Feldman, FeldmanReveal};
use super::x3dh::{receiver_x3dh, sender_x3dh};

const TRIPLE_RATCHET_PROTOCOL_VERSION: u16 = 1;
const TRIPLE_RATCHET_PROTOCOL: u16 = 2 << 8 + TRIPLE_RATCHET_PROTOCOL_VERSION;

#[derive(Clone, Copy, PartialEq)]
enum TripleRatchetRound {
    Uninitialized,
    Initialized,
    Committed,
    Revealed,
    Reconstructed,
}

#[derive(Error, Debug)]
pub enum TripleRatchetError {
    #[error("Crypto error: {0}")]
    CryptoError(String),
    #[error("Invalid data: {0}")]
    InvalidData(String),
    #[error("Skip limit exceeded")]
    SkipLimitExceeded,
    #[error("Malformed header")]
    MalformedHeader,
}

#[derive(Clone, Serialize, Deserialize, Debug)]
pub struct PeerInfo {
    pub(crate) public_key: Vec<u8>,
    pub(crate) identity_public_key: Vec<u8>,
    pub(crate) signed_pre_public_key: Vec<u8>,
}

pub struct TripleRatchetParticipant {
    peer_key: Scalar,
    sending_ephemeral_private_key: Scalar,
    receiving_ephemeral_keys: HashMap<Vec<u8>, Scalar>,
    receiving_group_key: Option<Vec<u8>>,
    root_key: Vec<u8>,
    sending_chain_key: Vec<u8>,
    current_header_key: Vec<u8>,
    next_header_key: Vec<u8>,
    receiving_chain_key: HashMap<Vec<u8>, Vec<u8>>,
    current_sending_chain_length: u32,
    previous_sending_chain_length: u32,
    current_receiving_chain_length: HashMap<Vec<u8>, u32>,
    previous_receiving_chain_length: HashMap<Vec<u8>, u32>,
    peer_id_map: HashMap<Vec<u8>, usize>,
    id_peer_map: HashMap<usize, PeerInfo>,
    skipped_keys_map: HashMap<Vec<u8>, HashMap<Vec<u8>, HashMap<u32, Vec<u8>>>>,
    peer_channels: HashMap<Vec<u8>, DoubleRatchetParticipant>,
    dkg_ratchet: Feldman,
    next_dkg_ratchet: Feldman,
    async_dkg_ratchet: bool,
    should_ratchet: bool,
    should_dkg_ratchet: HashMap<Vec<u8>, bool>,
    async_dkg_pubkey: Option<EdwardsPoint>,
    threshold: usize,
}

impl TripleRatchetParticipant {
    pub fn new(
        peers: &[PeerInfo],
        peer_key: Scalar,
        identity_key: Scalar,
        signed_pre_key: Scalar,
        threshold: usize,
        async_dkg_ratchet: bool,
    ) -> Result<(Self, HashMap<Vec<u8>, P2PChannelEnvelope>), TripleRatchetError> {
        let mut participant = TripleRatchetParticipant {
            peer_key,
            sending_ephemeral_private_key: Scalar::random(&mut OsRng),
            receiving_ephemeral_keys: HashMap::new(),
            receiving_group_key: None,
            root_key: vec![],
            sending_chain_key: vec![],
            current_header_key: vec![],
            next_header_key: vec![],
            receiving_chain_key: HashMap::new(),
            current_sending_chain_length: 0,
            previous_sending_chain_length: 0,
            current_receiving_chain_length: HashMap::new(),
            previous_receiving_chain_length: HashMap::new(),
            peer_id_map: HashMap::new(),
            id_peer_map: HashMap::new(),
            skipped_keys_map: HashMap::new(),
            peer_channels: HashMap::new(),
            dkg_ratchet: Feldman::new(
                threshold,
                peers.len() + 1,
                0, // This will be set later
                Scalar::random(&mut OsRng),
                EdwardsPoint::generator(),
            ),
            next_dkg_ratchet: Feldman::new(
                threshold,
                peers.len() + 1,
                0, // This will be set later
                Scalar::random(&mut OsRng),
                EdwardsPoint::generator(),
            ),
            async_dkg_ratchet: async_dkg_ratchet,
            should_ratchet: true,
            should_dkg_ratchet: HashMap::new(),
            async_dkg_pubkey: None,
            threshold: threshold,
        };

        let mut peer_basis = peers.to_vec();
        peer_basis.push(PeerInfo {
            public_key: (peer_key * EdwardsPoint::generator()).compress().to_bytes().to_vec(),
            identity_public_key: (identity_key * EdwardsPoint::generator()).compress().to_bytes().to_vec(),
            signed_pre_public_key: (signed_pre_key * EdwardsPoint::generator()).compress().to_bytes().to_vec(),
        });

        peer_basis.sort_by(|a, b| a.public_key.cmp(&b.public_key));

        let mut init_messages = HashMap::new();
        let mut sender = false;

        for (i, peer) in peer_basis.iter().enumerate() {
            participant.peer_id_map.insert(peer.public_key.clone(), i + 1);
            participant.id_peer_map.insert(i + 1, peer.clone());

            if peer.public_key.ct_eq(&(peer_key * EdwardsPoint::generator()).compress().to_bytes().to_vec()).into() {
                sender = true;
                participant.dkg_ratchet.set_id(i + 1);
                participant.next_dkg_ratchet.set_id(i + 1);
            } else {
                participant.skipped_keys_map.insert(peer.public_key.clone(), HashMap::new());
                participant.current_receiving_chain_length.insert(peer.public_key.clone(), 0);
                participant.previous_receiving_chain_length.insert(peer.public_key.clone(), 0);

                let session_key = if sender {
                    sender_x3dh(
                        &identity_key,
                        &signed_pre_key,
                        &EdwardsPoint::from_bytes(peer.identity_public_key.as_slice().into()).unwrap(),
                        &EdwardsPoint::from_bytes(peer.signed_pre_public_key.as_slice().into()).unwrap(),
                        96,
                    )
                } else {
                    receiver_x3dh(
                        &identity_key,
                        &signed_pre_key,
                        &EdwardsPoint::from_bytes(peer.identity_public_key.as_slice().into()).unwrap(),
                        &EdwardsPoint::from_bytes(peer.signed_pre_public_key.as_slice().into()).unwrap(),
                        96,
                    )
                }.unwrap();

                let peer_channel = DoubleRatchetParticipant::new(
                    &session_key[..32],
                    &session_key[32..64],
                    &session_key[64..],
                    sender,
                    signed_pre_key.clone(),
                    EdwardsPoint::from_bytes(peer.signed_pre_public_key.as_slice().into()).unwrap(),
                ).unwrap();

                participant.peer_channels.insert(peer.public_key.clone(), peer_channel);

                if sender {
                    let init_message = participant.peer_channels
                        .get_mut(&peer.public_key)
                        .unwrap()
                        .ratchet_encrypt(b"init").unwrap();
                    init_messages.insert(peer.public_key.clone(), init_message);
                }
            }
        }

        Ok((participant, init_messages))
    }

    pub fn get_peer_id_map(&self) -> HashMap<Vec<u8>, usize> {
        return self.peer_id_map.clone();
    }

    pub fn initialize(&mut self, init_messages: &HashMap<Vec<u8>, P2PChannelEnvelope>) 
        -> Result<HashMap<Vec<u8>, P2PChannelEnvelope>, TripleRatchetError> {
        for (k, m) in init_messages {
            let msg = self.peer_channels.get_mut(k).unwrap().ratchet_decrypt(m).unwrap();
            if msg != b"init" {
                return Err(TripleRatchetError::InvalidData("Invalid init message".into()));
            }
        }

        self.dkg_ratchet.sample_polynomial(&mut OsRng);

        let result = self.dkg_ratchet.get_poly_frags().unwrap();

        let mut result_map = HashMap::new();
        for (k, v) in result {
            let test: bool = self.id_peer_map[&k].public_key.ct_eq(&(self.peer_key * EdwardsPoint::generator()).compress().to_bytes()).into();
            if !test {
                let envelope = self.peer_channels
                    .get_mut(&self.id_peer_map[&k].public_key)
                    .unwrap()
                    .ratchet_encrypt(&v);
                result_map.insert(self.id_peer_map[&k].public_key.clone(), envelope.unwrap());
            }
        }

        Ok(result_map)
    }

    pub fn receive_poly_frag(&mut self, peer_id: &[u8], frag: &P2PChannelEnvelope) 
        -> Result<Option<HashMap<Vec<u8>, P2PChannelEnvelope>>, TripleRatchetError> {
        let b = self.peer_channels.get_mut(peer_id).unwrap().ratchet_decrypt(frag).unwrap();

        let result = self.dkg_ratchet.set_poly_frag_for_party(
            *self.peer_id_map.get(peer_id).unwrap(),
            &b,
        ).unwrap();

        if result.is_some() {
            let mut envelopes = HashMap::new();
            for (k, c) in &mut self.peer_channels {

                let envelope = c.ratchet_encrypt(&result.clone().unwrap()).unwrap();
                envelopes.insert(k.clone(), envelope);
            }
            Ok(Some(envelopes))
        } else {
            Ok(None)
        }
    }

    pub fn receive_commitment(&mut self, peer_id: &[u8], zkcommit: &P2PChannelEnvelope) 
        -> Result<Option<HashMap<Vec<u8>, P2PChannelEnvelope>>, TripleRatchetError> {
        let b = self.peer_channels.get_mut(peer_id).unwrap().ratchet_decrypt(zkcommit).unwrap();

        let result = self.dkg_ratchet.receive_commitments(
            *self.peer_id_map.get(peer_id).unwrap(),
            &b,
        ).unwrap();

        if let Some(reveal) = result {
            let d = serde_json::to_vec(&reveal).unwrap();
            let mut envelopes = HashMap::new();
            for (k, c) in &mut self.peer_channels {
                let envelope = c.ratchet_encrypt(&d).unwrap();
                envelopes.insert(k.clone(), envelope);
            }
            Ok(Some(envelopes))
        } else {
            Ok(None)
        }
    }

    pub fn recombine(&mut self, peer_id: &[u8], reveal: &P2PChannelEnvelope) -> Result<(), Box<dyn std::error::Error>> {
        let b = self.peer_channels.get_mut(peer_id).unwrap().ratchet_decrypt(reveal).unwrap();

        let rev: FeldmanReveal = serde_json::from_slice(&b).unwrap();

        let done = self.dkg_ratchet.recombine(
            *self.peer_id_map.get(peer_id).unwrap(),
            &rev,
        ).unwrap();

        if !done {
            return Ok(());
        }

        let sess = Sha512::digest(&self.dkg_ratchet.public_key_bytes());
        let hkdf = Hkdf::<Sha512>::new(
            Some(&sess),
            &self.dkg_ratchet.public_key_bytes(),
        );
        let mut rkck = [0u8; 96];
        let result = hkdf.expand(b"quilibrium-triple-ratchet", &mut rkck);
        if result.is_err() {
          return Err(Box::new(TripleRatchetError::CryptoError("invalid length".to_owned())));
        }

        self.root_key = rkck[..32].to_vec();
        self.current_header_key = rkck[32..64].to_vec();
        self.next_header_key = rkck[64..].to_vec();
        self.receiving_group_key = Some(self.dkg_ratchet.public_key().to_bytes().to_vec());
        Ok(())
    }

    pub fn ratchet_encrypt(&mut self, message: &[u8]) -> Result<P2PChannelEnvelope, Box<dyn std::error::Error>> {
        if self.should_ratchet {
            self.ratchet_sender_ephemeral_keys()?;
        }

        if self.async_dkg_ratchet && self.async_dkg_pubkey.is_some() && self.should_dkg_ratchet.len() == self.threshold {
            self.receiving_group_key = Some(self.dkg_ratchet.public_key().to_bytes().to_vec());
            let sess = Sha512::digest(&self.dkg_ratchet.public_key_bytes());
            let hkdf = Hkdf::<Sha512>::new(
                Some(&sess),
                &self.dkg_ratchet.public_key_bytes(),
            );
            let mut rkck = [0u8; 96];
            let result = hkdf.expand(b"quilibrium-triple-ratchet", &mut rkck);
            if result.is_err() {
                return Err(Box::new(TripleRatchetError::CryptoError("invalid length".to_owned())));
            }

            self.root_key = rkck[..32].to_vec();
            self.current_header_key = rkck[32..64].to_vec();
            self.next_header_key = rkck[64..].to_vec();
            self.async_dkg_pubkey = None;
        }

        let dkg_pub: Option<(Vec<u8>, Vec<u8>)> = if (self.async_dkg_ratchet && self.should_dkg_ratchet.len() > 0) || self.async_dkg_pubkey.is_some() {
            if self.async_dkg_pubkey.is_none() {
                self.should_dkg_ratchet = HashMap::new();
                self.async_dkg_pubkey = Some(Scalar::random(&mut OsRng) * EdwardsPoint::generator());
            }

            let pubkey = self.async_dkg_pubkey.unwrap();
            let invpub = self.dkg_ratchet.mul_share(&pubkey.compress().to_bytes());
            if invpub.is_err() {
                return Err(Box::new(invpub.unwrap_err()));
            }
            self.should_dkg_ratchet.insert((self.peer_key * EdwardsPoint::generator()).compress().to_bytes().to_vec(), true);

            Some((invpub.unwrap(), pubkey.compress().to_bytes().to_vec()))
        } else { None };

        let mut envelope = P2PChannelEnvelope {
            protocol_identifier: TRIPLE_RATCHET_PROTOCOL,
            message_header: MessageCiphertext::default(),
            message_body: MessageCiphertext::default(),
        };

        let (new_chain_key, message_key, aead_key) = ratchet_keys(&self.sending_chain_key);

        self.sending_chain_key = new_chain_key;

        let header = self.encode_header(dkg_pub);
        envelope.message_header = self.encrypt(&header, &self.current_header_key, None)?;
        envelope.message_body = self.encrypt(
            message,
            &message_key,
            Some(&[&aead_key[..], &envelope.message_header.ciphertext[..]].concat()),
        )?;

        self.current_sending_chain_length += 1;

        Ok(envelope)
    }

    pub fn ratchet_decrypt(&mut self, envelope: &P2PChannelEnvelope) -> Result<(Vec<u8>, bool), Box<dyn std::error::Error>> {
      if let Some(plaintext) = self.try_skipped_message_keys(envelope)? {
          return Ok((plaintext, false));
      }

      let header_key = self.current_header_key.clone();
      let (header, mut should_dkg_ratchet, should_advance_dkg_ratchet) = self.decrypt_header(&envelope.message_header, &header_key)?;

      let (sender_key, receiving_ephemeral_key, previous_receiving_chain_length, current_receiving_chain_length, dkg_pub) = 
          self.decode_header(&header)?;

      let should_ratchet = self.receiving_ephemeral_keys.get(&sender_key.compress().to_bytes().to_vec()).map(|k| !k.eq(&receiving_ephemeral_key)).unwrap_or(true);
      if should_ratchet {
          self.skip_message_keys(&sender_key, previous_receiving_chain_length)?;
          self.ratchet_receiver_ephemeral_keys(&sender_key, &receiving_ephemeral_key)?;
      }

      self.skip_message_keys(&sender_key, current_receiving_chain_length)?;

      let (new_chain_key, message_key, aead_key) = ratchet_keys(
          &self.receiving_chain_key[&sender_key.compress().to_bytes().to_vec()],
      );

      self.receiving_chain_key.insert(sender_key.compress().to_bytes().to_vec(), new_chain_key);

      *self.current_receiving_chain_length.entry(sender_key.compress().to_bytes().to_vec()).or_insert(0) += 1;

      if should_advance_dkg_ratchet {
          self.receiving_group_key = Some(self.dkg_ratchet.public_key().to_bytes().to_vec());
          let sess = Sha512::digest(&self.dkg_ratchet.public_key_bytes());
          let hkdf = Hkdf::<Sha512>::new(
              Some(&sess),
              &self.dkg_ratchet.public_key_bytes(),
          );
          let mut rkck = [0u8; 96];
          let result = hkdf.expand(b"quilibrium-triple-ratchet", &mut rkck);
          if result.is_err() {
              return Err(Box::new(TripleRatchetError::CryptoError("invalid length".to_owned())));
          }

          self.root_key = rkck[..32].to_vec();
          self.current_header_key = rkck[32..64].to_vec();
          self.next_header_key = rkck[64..].to_vec();
      }

      let plaintext = self.decrypt(
          &envelope.message_body,
          &message_key,
          Some(&[&aead_key[..], &envelope.message_header.ciphertext[..]].concat()),
      )?;

      if dkg_pub.is_some() {
          should_dkg_ratchet = false;
          let (other_invpub, pubkey) = dkg_pub.unwrap();
          self.async_dkg_pubkey = Some(pubkey);

          let invpub = self.dkg_ratchet.mul_share(&pubkey.compress().to_bytes());
          if invpub.is_err() {
              return Err(Box::new(invpub.unwrap_err()));
          }

          let invvec = invpub.unwrap();
          let inv = invvec.as_slice();
          let other = &other_invpub.compress().to_bytes();

          let other_id = self.peer_id_map.get(&sender_key.compress().to_bytes().to_vec());
          if other_id.is_none() {
              return Err(Box::new(TripleRatchetError::MalformedHeader))
          }

          let our_id = self.peer_id_map.get(&(self.peer_key * EdwardsPoint::generator()).compress().to_bytes().to_vec());
          let (shares, ids) = if our_id.unwrap() < other_id.unwrap() {
              (vec![inv, other], [*our_id.unwrap(), *other_id.unwrap()])
          } else {
              (vec![other, inv], [*other_id.unwrap(), *our_id.unwrap()])
          };

          let next_pub = self.dkg_ratchet.combine_mul_share(shares, &ids);
          if next_pub.is_err() {
              return Err(Box::new(next_pub.unwrap_err()));
          }

          let next = EdwardsPoint::from_bytes(next_pub.unwrap().as_slice().into());
          if next.is_none().into() {
            return Err(Box::new(TripleRatchetError::MalformedHeader));
          }
      }

      Ok((plaintext, should_dkg_ratchet))
  }

  fn ratchet_sender_ephemeral_keys(&mut self) -> Result<(), Box<dyn std::error::Error>> {
      let receiving_group_key = self.receiving_group_key.as_ref().ok_or_else(|| TripleRatchetError::CryptoError("Receiving group key not set".into()))?;
      self.sending_ephemeral_private_key = Scalar::random(&mut OsRng);
      let dh_output = (self.sending_ephemeral_private_key * EdwardsPoint::from_bytes(receiving_group_key.as_slice().into()).unwrap()).compress().to_bytes();
      
      let hkdf = Hkdf::<Sha512>::new(Some(&self.root_key), &dh_output);
      let mut rkck2 = [0u8; 96];
      let result = hkdf.expand(b"quilibrium-triple-ratchet", &mut rkck2);
      if result.is_err() {
        return Err(Box::new(TripleRatchetError::CryptoError("invalid length".to_owned())));
      }

      self.root_key = rkck2[..32].to_vec();
      self.sending_chain_key = rkck2[32..64].to_vec();
      self.should_ratchet = false;

      Ok(())
  }

  fn ratchet_receiver_ephemeral_keys(&mut self, peer_key: &EdwardsPoint, new_ephemeral_key: &Scalar) -> Result<(), Box<dyn std::error::Error>> {
      self.previous_sending_chain_length = self.current_sending_chain_length;
      self.current_sending_chain_length = 0;
      *self.current_receiving_chain_length.entry(peer_key.compress().to_bytes().to_vec()).or_insert(0) = 0;
      self.receiving_ephemeral_keys.insert(peer_key.compress().to_bytes().to_vec(), new_ephemeral_key.clone());

      let receiving_group_key = self.receiving_group_key.as_ref().ok_or_else(|| TripleRatchetError::CryptoError("Receiving group key not set".into()))?;
      let dh_output = (new_ephemeral_key * EdwardsPoint::from_bytes(receiving_group_key.as_slice().into()).unwrap()).compress().to_bytes();

      let hkdf = Hkdf::<Sha512>::new(Some(&self.root_key), &dh_output);
      let mut rkck = [0u8; 96];
      let result = hkdf.expand(b"quilibrium-triple-ratchet", &mut rkck);
      if result.is_err() {
        return Err(Box::new(TripleRatchetError::CryptoError("invalid length".to_owned())));
      }

      self.root_key = rkck[..32].to_vec();
      self.receiving_chain_key.insert(peer_key.compress().to_bytes().to_vec(), rkck[32..64].to_vec());
      self.should_ratchet = true;

      if self.async_dkg_ratchet {
          self.should_dkg_ratchet = HashMap::new();
          self.should_dkg_ratchet.insert(peer_key.compress().to_bytes().to_vec(), true);
          self.async_dkg_pubkey = None;
      }

      Ok(())
  }

  fn try_skipped_message_keys(&mut self, envelope: &P2PChannelEnvelope) -> Result<Option<Vec<u8>>, Box<dyn std::error::Error>> {
      for (receiving_header_key, skipped_keys) in &self.skipped_keys_map.clone() {
          if let Ok((header, _, _)) = self.decrypt_header(&envelope.message_header, receiving_header_key) {
              let (peer_key, _, _, current, _) = self.decode_header(&header)?;
              if let Some(peer_skipped_keys) = skipped_keys.get(&peer_key.compress().to_bytes().to_vec()) {
                  if let Some(key_pair) = peer_skipped_keys.get(&current) {
                      let message_key = &key_pair[..32];
                      let aead_key = &key_pair[32..];
                      let plaintext = self.decrypt(
                          &envelope.message_body,
                          message_key,
                          Some(&[aead_key, &envelope.message_header.ciphertext].concat()),
                      )?;
                      return Ok(Some(plaintext));
                  }
              }
          }
      }
      Ok(None)
  }

  fn skip_message_keys(&mut self, sender_key: &EdwardsPoint, until: u32) -> Result<(), Box<dyn std::error::Error>> {
      let mut current = *self.current_receiving_chain_length.entry(sender_key.compress().to_bytes().to_vec()).or_insert(0);
      if current + 100 < until {
          return Err(Box::new(TripleRatchetError::SkipLimitExceeded));
      }

      if let Some(chain_key) = self.receiving_chain_key.get_mut(&sender_key.compress().to_bytes().to_vec()) {
          while current < until {
              let (new_chain_key, message_key, aead_key) = ratchet_keys(chain_key);
              self.skipped_keys_map
                  .entry(self.current_header_key.clone())
                  .or_insert_with(HashMap::new)
                  .entry(sender_key.compress().to_bytes().to_vec())
                  .or_insert_with(HashMap::new)
                  .insert(current, [message_key, aead_key].concat());
              *chain_key = new_chain_key;
              current += 1;
              *self.current_receiving_chain_length.entry(sender_key.compress().to_bytes().to_vec()).or_insert(0) += 1;
          }
      }

      Ok(())
  }

  fn encode_header(&self, dkg_pub: Option<(Vec<u8>, Vec<u8>)>) -> Vec<u8> {
      let mut header = Vec::new();
      header.extend_from_slice(&(self.peer_key * EdwardsPoint::generator()).compress().to_bytes().to_vec());
      header.extend_from_slice(&self.sending_ephemeral_private_key.to_bytes());
      header.extend_from_slice(&self.previous_sending_chain_length.to_be_bytes());
      header.extend_from_slice(&self.current_sending_chain_length.to_be_bytes());
      if dkg_pub.is_some() {
        let (invpub, pubkey) = dkg_pub.unwrap();
        header.extend(invpub);
        header.extend(pubkey);
      }
      header
  }

  fn decrypt_header(&mut self, ciphertext: &MessageCiphertext, receiving_header_key: &[u8]) -> Result<(Vec<u8>, bool, bool), Box<dyn std::error::Error>> {
      match self.decrypt(ciphertext, receiving_header_key, None) {
          Ok(header) => {
              Ok((header, self.async_dkg_ratchet, false))
          },
          Err(_) if receiving_header_key == self.current_header_key => {
              if self.async_dkg_ratchet && self.async_dkg_pubkey.is_some() {
                  let receiving_group_key = Some(self.dkg_ratchet.public_key().to_bytes().to_vec());
                  let sess = Sha512::digest(&self.dkg_ratchet.public_key_bytes());
                  let hkdf = Hkdf::<Sha512>::new(
                      Some(&sess),
                      &self.dkg_ratchet.public_key_bytes(),
                  );
                  let mut rkck = [0u8; 96];
                  let result = hkdf.expand(b"quilibrium-triple-ratchet", &mut rkck);
                  if result.is_err() {
                      return Err(Box::new(TripleRatchetError::CryptoError("invalid length".to_owned())));
                  }
        
                  let current_header_key = rkck[32..64].to_vec();
                  match self.decrypt(ciphertext, &current_header_key, None) {
                      Ok(header) => Ok((header, true, true)),
                      Err(e) => Err(Box::new(e)),
                  }
              } else {
                  match self.decrypt(ciphertext, &self.next_header_key, None) {
                      Ok(header) => Ok((header, true, false)),
                      Err(e) => Err(Box::new(e)),
                  }
              }
          },
          Err(e) => Err(Box::new(e)),
      }
  }

  fn decode_header(&self, header: &[u8]) -> Result<(EdwardsPoint, Scalar, u32, u32, Option<(EdwardsPoint, EdwardsPoint)>), TripleRatchetError> {
      if header.len() < 121 {
          return Err(TripleRatchetError::MalformedHeader);
      }

      let sender_key = EdwardsPoint::from_bytes(header[..57].into()).unwrap();
      let receiving_ephemeral_key = Scalar::from_bytes(header[57..113].try_into().unwrap());
      let previous_receiving_chain_length = u32::from_be_bytes(header[113..117].try_into().unwrap());
      let current_receiving_chain_length = u32::from_be_bytes(header[117..121].try_into().unwrap());

      let dkg_pub = if header.len() == 235 {
          let invpub = EdwardsPoint::from_bytes(header[121..178].into()).into_option();
          let pubkey = EdwardsPoint::from_bytes(header[178..].into()).into_option();
          if invpub.is_none() || pubkey.is_none() {
            None
          } else {
            Some((invpub.unwrap(), pubkey.unwrap()))
          }
      } else {
          None
      };

      Ok((sender_key, receiving_ephemeral_key, previous_receiving_chain_length, current_receiving_chain_length, dkg_pub))
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

  fn decrypt(&self, ciphertext: &MessageCiphertext, key: &[u8], associated_data: Option<&[u8]>) -> Result<Vec<u8>, TripleRatchetError> {
      use aes_gcm::KeyInit;
      if key.len() != 32 {
        return Err(TripleRatchetError::InvalidData("Invalid key length".to_string()));
      }
      let cipher = Aes256Gcm::new_from_slice(key).unwrap();
      let nonce = Nonce::from_slice(&ciphertext.initialization_vector);

      let associated_data = associated_data.unwrap_or_else(|| ciphertext.associated_data.as_ref().unwrap());

      cipher.decrypt(nonce, Payload{
          msg: &ciphertext.ciphertext.as_ref(),
          aad: associated_data.as_ref(),
      }).map_err(|e| TripleRatchetError::CryptoError(e.to_string()))
  }
}

fn ratchet_keys(input: &[u8]) -> (Vec<u8>, Vec<u8>, Vec<u8>) {
  let mut output = [0u8; 96];
  let hkdf = Hkdf::<Sha512>::new(None, input);
  hkdf.expand(b"quilibrium-triple-ratchet-keys", &mut output).unwrap();
  (output[..32].to_vec(), output[32..64].to_vec(), output[64..].to_vec())
}