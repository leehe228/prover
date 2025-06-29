use once_cell::sync::Lazy;
use redis::{Commands, Connection, Client, RedisError};
use serde::{Serialize, de::DeserializeOwned};
use std::env;
use bincode::{serialize as bincode_serialize, deserialize as bincode_deserialize};
use std::sync::Mutex;

/// 글로벌 싱글턴 커넥션
static REDIS: Lazy<Mutex<Connection>> = Lazy::new(|| {
    let url = env::var("REDIS_URL").unwrap_or_else(|_| "redis://redis:6379".into());
    let client = Client::open(url).expect("Invalid REDIS_URL");
    Mutex::new(client.get_connection().expect("Redis connection failed"))
});

fn encode<T: Serialize>(v: &T) -> Vec<u8>   { bincode_serialize(v).unwrap() }
fn decode<T: DeserializeOwned>(buf: Vec<u8>) -> Option<T> {
    bincode_deserialize(&buf).ok()
}

pub fn get<T: DeserializeOwned>(k: &str) -> Option<T> {
    let mut conn = match REDIS.lock() {
        Ok(c) => c,
        Err(_) => return None, 
    };

    match conn.get::<_, Vec<u8>>(k) {
        Ok(buf) => decode(buf),
        Err(_) => None,
    }
}

pub fn set<T: Serialize>(k: &str, v: &T) {
    let mut conn = REDIS.lock().expect("Redis mutex poisoned");
    if let Err(e) = conn.set::<_, _, ()>(k, encode(v)) {
        log::warn!("Redis SET failed for key {}: {}", k, e);
    }
}

/// 공통 SHA-256 key 헬퍼 (serde_json 직렬화 → hex)
pub fn sha_key<T: Serialize>(prefix: &str, value: &T) -> String {
    use sha2::{Digest, Sha256};
    let json = serde_json::to_vec(value).unwrap();
    let mut hasher = Sha256::new();
    hasher.update(json);
    format!("{}:{}", prefix, hex::encode(hasher.finalize()))
}
