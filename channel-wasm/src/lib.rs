use wasm_bindgen::prelude::*;
use channel::*;
use serde::{Deserialize, Serialize};

#[derive(Clone, PartialEq, Serialize, Deserialize)]
pub struct NewDoubleRatchetParameters {
  pub session_key: Vec<u8>,
  pub sending_header_key: Vec<u8>,
  pub next_receiving_header_key: Vec<u8>,
  pub is_sender: bool,
  pub sending_ephemeral_private_key: Vec<u8>,
  pub receiving_ephemeral_key: Vec<u8>
}

#[derive(Clone, PartialEq, Serialize, Deserialize)]
pub struct NewTripleRatchetParameters {
  pub peers: Vec<Vec<u8>>,
  pub peer_key: Vec<u8>,
  pub identity_key: Vec<u8>,
  pub signed_pre_key: Vec<u8>,
  pub threshold: u64,
  pub async_dkg_ratchet: bool
}

#[wasm_bindgen]
pub fn js_new_double_ratchet(params: &str) -> String {
  let json: Result<NewDoubleRatchetParameters, serde_json::Error> = serde_json::from_str(params);
  match json {
    Ok(inputs) => {
      return new_double_ratchet(&inputs.session_key, &inputs.sending_header_key, &inputs.next_receiving_header_key, inputs.is_sender, &inputs.sending_ephemeral_private_key, &inputs.receiving_ephemeral_key);
    }
    Err(e) => {
      return e.to_string();
    }
  }
}

#[wasm_bindgen]
pub fn js_double_ratchet_encrypt(params: &str) -> String {
  let json: Result<DoubleRatchetStateAndMessage, serde_json::Error> = serde_json::from_str(params);
  match json {
    Ok(ratchet_state_and_message) => {
      return serde_json::to_string(&double_ratchet_encrypt(ratchet_state_and_message)).unwrap_or_else(|e| e.to_string());
    }
    Err(e) => {
      return e.to_string();
    }
  }
}

#[wasm_bindgen]
pub fn js_double_ratchet_decrypt(params: &str) -> String {
  let json: Result<DoubleRatchetStateAndEnvelope, serde_json::Error> = serde_json::from_str(params);
  match json {
    Ok(ratchet_state_and_envelope) => {
      return serde_json::to_string(&double_ratchet_decrypt(ratchet_state_and_envelope)).unwrap_or_else(|e| e.to_string());
    }
    Err(e) => {
      return e.to_string();
    }
  }
}

#[wasm_bindgen]
pub fn js_new_triple_ratchet(params: &str) -> String {
  let json: Result<NewTripleRatchetParameters, serde_json::Error> = serde_json::from_str(params);
  match json {
    Ok(input) => {
      return serde_json::to_string(&new_triple_ratchet(&input.peers, &input.peer_key, &input.identity_key, &input.signed_pre_key, input.threshold, input.async_dkg_ratchet)).unwrap_or_else(|e| e.to_string());
    }
    Err(e) => {
      return e.to_string();
    }
  }
}

#[wasm_bindgen]
pub fn js_triple_ratchet_init_round_1(params: &str) -> String {
  let json: Result<TripleRatchetStateAndMetadata, serde_json::Error> = serde_json::from_str(params);
  match json {
    Ok(ratchet_state_and_metadata) => {
      return serde_json::to_string(&triple_ratchet_init_round_1(ratchet_state_and_metadata)).unwrap_or_else(|e| e.to_string());
    }
    Err(e) => {
      return e.to_string();
    }
  }
}

#[wasm_bindgen]
pub fn js_triple_ratchet_init_round_2(params: &str) -> String {
  let json: Result<TripleRatchetStateAndMetadata, serde_json::Error> = serde_json::from_str(params);
  match json {
    Ok(ratchet_state_and_metadata) => {
      return serde_json::to_string(&triple_ratchet_init_round_2(ratchet_state_and_metadata)).unwrap_or_else(|e| e.to_string());
    }
    Err(e) => {
      return e.to_string();
    }
  }
}

#[wasm_bindgen]
pub fn js_triple_ratchet_init_round_3(params: &str) -> String {
  let json: Result<TripleRatchetStateAndMetadata, serde_json::Error> = serde_json::from_str(params);
  match json {
    Ok(ratchet_state_and_metadata) => {
      return serde_json::to_string(&triple_ratchet_init_round_3(ratchet_state_and_metadata)).unwrap_or_else(|e| e.to_string());
    }
    Err(e) => {
      return e.to_string();
    }
  }
}

#[wasm_bindgen]
pub fn js_triple_ratchet_init_round_4(params: &str) -> String {
  let json: Result<TripleRatchetStateAndMetadata, serde_json::Error> = serde_json::from_str(params);
  match json {
    Ok(ratchet_state_and_metadata) => {
      return serde_json::to_string(&triple_ratchet_init_round_4(ratchet_state_and_metadata)).unwrap_or_else(|e| e.to_string());
    }
    Err(e) => {
      return e.to_string();
    }
  }
}

#[wasm_bindgen]
pub fn js_triple_ratchet_encrypt(params: &str) -> String {
  let json: Result<TripleRatchetStateAndMessage, serde_json::Error> = serde_json::from_str(params);
  match json {
    Ok(ratchet_state_and_message) => {
      return serde_json::to_string(&triple_ratchet_encrypt(ratchet_state_and_message)).unwrap_or_else(|e| e.to_string());
    }
    Err(e) => {
      return e.to_string();
    }
  }
}

#[wasm_bindgen]
pub fn js_triple_ratchet_decrypt(params: &str) -> String {
  let json: Result<TripleRatchetStateAndEnvelope, serde_json::Error> = serde_json::from_str(params);
  match json {
    Ok(ratchet_state_and_envelope) => {
      return serde_json::to_string(&triple_ratchet_decrypt(ratchet_state_and_envelope)).unwrap_or_else(|e| e.to_string());
    }
    Err(e) => {
      return e.to_string();
    }
  }
}

