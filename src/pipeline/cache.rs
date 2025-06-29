use once_cell::sync::Lazy;
use redis::{Commands, Connection, Client};
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
fn decode<T: DeserializeOwned>(buf: Vec<u8>) -> T { bincode_deserialize(&buf).unwrap() }

pub fn get<T: DeserializeOwned>(k: &str) -> Option<T> {
    let mut conn = REDIS.lock().expect("Redis mutex poisoned");
    conn.get::<_, Vec<u8>>(k).ok().map(decode)
}

pub fn set<T: Serialize>(k: &str, v: &T) {
    let mut conn = REDIS.lock().expect("Redis mutex poisoned");
    let _ : () = conn.set(k, encode(v)).unwrap();   // 실패 시 panic → 로그로 대체 가능
}

/// 공통 SHA-256 key 헬퍼 (serde_json 직렬화 → hex)
pub fn sha_key<T: Serialize>(prefix: &str, value: &T) -> String {
    use sha2::{Digest, Sha256};
    let json = serde_json::to_vec(value).unwrap();
    let mut hasher = Sha256::new();
    hasher.update(json);
    format!("{}:{}", prefix, hex::encode(hasher.finalize()))
}
