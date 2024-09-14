pub(crate) mod protocols;

#[cfg(test)]
mod tests {

    use std::collections::HashMap;

    use super::*;
    use ed448_goldilocks_plus::{Scalar, elliptic_curve::Group, EdwardsPoint};
    use protocols::{doubleratchet::P2PChannelEnvelope, tripleratchet::{PeerInfo, TripleRatchetParticipant}};

    #[test]
    fn test_four_party_triple_ratchet_communication() {    
        let mut rng = rand::thread_rng();
        let mut keys: Vec<(Scalar, Scalar, Scalar)> = (0..4)
            .map(|_| (Scalar::random(&mut rng), Scalar::random(&mut rng), Scalar::random(&mut rng)))
            .collect();

        keys.sort_by(|a, b| (a.0 * EdwardsPoint::generator()).compress().to_bytes().cmp(&(b.0 * EdwardsPoint::generator()).compress().to_bytes()));
    
        let mut peer_infos: Vec<PeerInfo> = keys
            .iter()
            .map(|(peer_key, identity_key, signed_pre_key)| PeerInfo {
                public_key: (peer_key * EdwardsPoint::generator()).compress().to_bytes().to_vec(),
                identity_public_key: (identity_key * EdwardsPoint::generator()).compress().to_bytes().to_vec(),
                signed_pre_public_key: (signed_pre_key * EdwardsPoint::generator()).compress().to_bytes().to_vec(),
            })
            .collect();

        // mirror the internal order so we can use by index:
        peer_infos.sort_by(|a, b| a.public_key.cmp(&b.public_key));
    
        let mut participants: Vec<TripleRatchetParticipant> = Vec::new();
        let mut init_messages: HashMap<Vec<u8>, HashMap<Vec<u8>, P2PChannelEnvelope>> = HashMap::new();
        let mut frag_messages: HashMap<Vec<u8>, HashMap<Vec<u8>, P2PChannelEnvelope>> = HashMap::new();
        let mut commitment_messages: HashMap<Vec<u8>, HashMap<Vec<u8>, P2PChannelEnvelope>> = HashMap::new();
        let mut reveal_messages: HashMap<Vec<u8>, HashMap<Vec<u8>, P2PChannelEnvelope>> = HashMap::new();

        for i in 0..4 {
            init_messages.insert(peer_infos[i].public_key.clone(), HashMap::new());
            frag_messages.insert(peer_infos[i].public_key.clone(), HashMap::new());
            commitment_messages.insert(peer_infos[i].public_key.clone(), HashMap::new());
            reveal_messages.insert(peer_infos[i].public_key.clone(), HashMap::new());
        }

        for i in 0..4 {
            let other_peers: Vec<PeerInfo> = peer_infos.iter().enumerate()
                .filter(|&(j, _)| j != i)
                .map(|(_, peer)| peer.clone())
                .collect();
    
            let (participant, init_msg) = TripleRatchetParticipant::new(
                &other_peers,
                keys[i].0.clone(),
                keys[i].1.clone(),
                keys[i].2.clone(),
                3,
                false,
            ).unwrap();
            
            participants.push(participant);

            for (j, env) in init_msg.iter() {
                init_messages.get_mut(j).unwrap().insert(peer_infos[i].public_key.clone(), env.clone());
            }
        }
    
        // Exchange initial messages and get frags:
        for i in 0..4 {
            let result = participants[i].initialize(&init_messages[&peer_infos[i].public_key.clone()]).unwrap();
            for (j, env) in result.iter() {
                frag_messages.get_mut(j).unwrap().insert(peer_infos[i].public_key.clone(), env.clone());
            }
        }

        // Exchange frags and receive commitments once all frags have been distributed:
        for i in 0..4 {
            for (p, envelope) in frag_messages[&peer_infos[i].public_key.clone()].iter() {
                if let Some(out) = participants[i].receive_poly_frag(&p, envelope).unwrap() {
                    for (j, env) in out.iter() {
                        commitment_messages.get_mut(j).unwrap().insert(peer_infos[i].public_key.clone(), env.clone());
                    }
                }
            }
        }

        // Exchange commitments and produce reveals:
        for i in 0..4 {
            for (p, envelope) in commitment_messages[&peer_infos[i].public_key.clone()].iter() {
                if let Some(reveal_msg) = participants[i].receive_commitment(&p, envelope).unwrap() {
                    for (j, env) in reveal_msg.iter() {
                        reveal_messages.get_mut(j).unwrap().insert(peer_infos[i].public_key.clone(), env.clone());
                    }
                }
            }
        }
    
        // Collect reveals and confirm zkpoks are valid, produce group key:
        for i in 0..4 {
            for (j, env) in reveal_messages[&peer_infos[i].public_key.clone()].iter() {
                participants[i].recombine(j, &env.clone()).unwrap();
            }
        }
    
        // Test sending and receiving messages
        let test_messages = [
            "hello there",
            "general kenobi",
            "you are a bold one",
            "*mechanical laughter*",
        ];
    
        for (i, message) in test_messages.iter().enumerate() {
            let encrypted = participants[i].ratchet_encrypt(message.as_bytes()).unwrap();
            for j in 0..4 {
                if i != j {
                    let decrypted = participants[j].ratchet_decrypt(&encrypted).unwrap();
                    assert_eq!(message.as_bytes(), decrypted.0.as_slice(), "Message decryption failed for Participant {}", j);
                }
            }
        }

        for _ in 0..5 {
            for i in 0..4 {
                let message1 = format!("test 1 {}", i + 1);
                let message2 = format!("test 2 {}", i + 1);
                let encrypted1 = participants[i].ratchet_encrypt(message1.as_bytes()).unwrap();
                let encrypted2 = participants[i].ratchet_encrypt(message2.as_bytes()).unwrap();

                for j in 0..4 {
                    if i != j {
                      let decrypted1 = participants[j].ratchet_decrypt(&encrypted1).unwrap();
                      assert_eq!(message1.as_bytes(), decrypted1.0.as_slice(), "Round message decryption failed for Participant {}", j);
                      let decrypted2 = participants[j].ratchet_decrypt(&encrypted2).unwrap();
                      assert_eq!(message2.as_bytes(), decrypted2.0.as_slice(), "Round message decryption failed for Participant {}", j);
                    }
                }
            }
        }
    }

    #[test]
    fn test_four_party_async_triple_ratchet_communication() {    
        let mut rng = rand::thread_rng();
        let mut keys: Vec<(Scalar, Scalar, Scalar)> = (0..4)
            .map(|_| (Scalar::random(&mut rng), Scalar::random(&mut rng), Scalar::random(&mut rng)))
            .collect();

        keys.sort_by(|a, b| (a.0 * EdwardsPoint::generator()).compress().to_bytes().cmp(&(b.0 * EdwardsPoint::generator()).compress().to_bytes()));
    
        let mut peer_infos: Vec<PeerInfo> = keys
            .iter()
            .map(|(peer_key, identity_key, signed_pre_key)| PeerInfo {
                public_key: (peer_key * EdwardsPoint::generator()).compress().to_bytes().to_vec(),
                identity_public_key: (identity_key * EdwardsPoint::generator()).compress().to_bytes().to_vec(),
                signed_pre_public_key: (signed_pre_key * EdwardsPoint::generator()).compress().to_bytes().to_vec(),
            })
            .collect();

        // mirror the internal order so we can use by index:
        peer_infos.sort_by(|a, b| a.public_key.cmp(&b.public_key));
    
        let mut participants: Vec<TripleRatchetParticipant> = Vec::new();
        let mut init_messages: HashMap<Vec<u8>, HashMap<Vec<u8>, P2PChannelEnvelope>> = HashMap::new();
        let mut frag_messages: HashMap<Vec<u8>, HashMap<Vec<u8>, P2PChannelEnvelope>> = HashMap::new();
        let mut commitment_messages: HashMap<Vec<u8>, HashMap<Vec<u8>, P2PChannelEnvelope>> = HashMap::new();
        let mut reveal_messages: HashMap<Vec<u8>, HashMap<Vec<u8>, P2PChannelEnvelope>> = HashMap::new();

        for i in 0..4 {
            init_messages.insert(peer_infos[i].public_key.clone(), HashMap::new());
            frag_messages.insert(peer_infos[i].public_key.clone(), HashMap::new());
            commitment_messages.insert(peer_infos[i].public_key.clone(), HashMap::new());
            reveal_messages.insert(peer_infos[i].public_key.clone(), HashMap::new());
        }

        for i in 0..4 {
            let other_peers: Vec<PeerInfo> = peer_infos.iter().enumerate()
                .filter(|&(j, _)| j != i)
                .map(|(_, peer)| peer.clone())
                .collect();
    
            let (participant, init_msg) = TripleRatchetParticipant::new(
                &other_peers,
                keys[i].0.clone(),
                keys[i].1.clone(),
                keys[i].2.clone(),
                2,
                true,
            ).unwrap();
            
            participants.push(participant);

            for (j, env) in init_msg.iter() {
                init_messages.get_mut(j).unwrap().insert(peer_infos[i].public_key.clone(), env.clone());
            }
        }
    
        // Exchange initial messages and get frags:
        for i in 0..4 {
            let result = participants[i].initialize(&init_messages[&peer_infos[i].public_key.clone()]).unwrap();
            for (j, env) in result.iter() {
                frag_messages.get_mut(j).unwrap().insert(peer_infos[i].public_key.clone(), env.clone());
            }
        }

        // Exchange frags and receive commitments once all frags have been distributed:
        for i in 0..4 {
            for (p, envelope) in frag_messages[&peer_infos[i].public_key.clone()].iter() {
                if let Some(out) = participants[i].receive_poly_frag(&p, envelope).unwrap() {
                    for (j, env) in out.iter() {
                        commitment_messages.get_mut(j).unwrap().insert(peer_infos[i].public_key.clone(), env.clone());
                    }
                }
            }
        }

        // Exchange commitments and produce reveals:
        for i in 0..4 {
            for (p, envelope) in commitment_messages[&peer_infos[i].public_key.clone()].iter() {
                if let Some(reveal_msg) = participants[i].receive_commitment(&p, envelope).unwrap() {
                    for (j, env) in reveal_msg.iter() {
                        reveal_messages.get_mut(j).unwrap().insert(peer_infos[i].public_key.clone(), env.clone());
                    }
                }
            }
        }
    
        // Collect reveals and confirm zkpoks are valid, produce group key:
        for i in 0..4 {
            for (j, env) in reveal_messages[&peer_infos[i].public_key.clone()].iter() {
                participants[i].recombine(j, &env.clone()).unwrap();
            }
        }
    
        // Test sending and receiving messages
        let test_messages = [
            "hello there",
            "general kenobi",
            "you are a bold one",
            "*mechanical laughter*",
        ];
    
        for (i, message) in test_messages.iter().enumerate() {
            let encrypted = participants[i].ratchet_encrypt(message.as_bytes()).unwrap();
            for j in 0..4 {
                if i != j {
                    let decrypted = participants[j].ratchet_decrypt(&encrypted).unwrap();
                    assert_eq!(message.as_bytes(), decrypted.0.as_slice(), "Message decryption failed for Participant {}", j);
                }
            }
        }

        for _ in 0..5 {
            for i in 0..4 {
                let message1 = format!("test 1 {}", i + 1);
                let message2 = format!("test 2 {}", i + 1);
                let encrypted1 = participants[i].ratchet_encrypt(message1.as_bytes()).unwrap();
                let encrypted2 = participants[i].ratchet_encrypt(message2.as_bytes()).unwrap();

                for j in 0..4 {
                    if i != j {
                      let decrypted1 = participants[j].ratchet_decrypt(&encrypted1).unwrap();
                      assert_eq!(message1.as_bytes(), decrypted1.0.as_slice(), "Round message decryption failed for Participant {}", j);
                      let decrypted2 = participants[j].ratchet_decrypt(&encrypted2).unwrap();
                      assert_eq!(message2.as_bytes(), decrypted2.0.as_slice(), "Round message decryption failed for Participant {}", j);
                    }
                }
            }
        }
    }
}