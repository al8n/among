//! Untagged serialization/deserialization support for Among<L, M, R>.
//!
//! `Among` uses default, externally-tagged representation.
//! However, sometimes it is useful to support several alternative types.
//! For example, we may have a field which is generally Map<String, i32>
//! but in typical cases Vec<String> would suffice, too.
//!
//! ```rust
//! # fn main() -> Result<(), Box<dyn std::error::Error>> {
//! use among::Among;
//! use std::collections::HashMap;
//!
//! #[derive(serde::Serialize, serde::Deserialize, Debug)]
//! #[serde(transparent)]
//! struct IntOrString {
//!     #[serde(with = "among::serde_untagged")]
//!     inner: Among<Vec<String>, HashMap<String, i32>>
//! };
//!
//! // serialization
//! let data = IntOrString {
//!     inner: Among::Left(vec!["Hello".to_string()])
//! };
//! // notice: no tags are emitted.
//! assert_eq!(serde_json::to_string(&data)?, r#"["Hello"]"#);
//!
//! // deserialization
//! let data: IntOrString = serde_json::from_str(
//!     r#"{"a": 0, "b": 14}"#
//! )?;
//! println!("found {:?}", data);
//! # Ok(())
//! # }
//! ```

use serde::{Deserialize, Deserializer, Serialize, Serializer};

#[derive(serde::Serialize, serde::Deserialize)]
#[serde(untagged)]
enum Among<L, M, R> {
  Left(L),
  Middle(M),
  Right(R),
}

pub fn serialize<L, M, R, S>(this: &super::Among<L, M, R>, serializer: S) -> Result<S::Ok, S::Error>
where
  S: Serializer,
  L: Serialize,
  M: Serialize,
  R: Serialize,
{
  let untagged = match this {
    super::Among::Left(left) => Among::Left(left),
    super::Among::Middle(middle) => Among::Middle(middle),
    super::Among::Right(right) => Among::Right(right),
  };
  untagged.serialize(serializer)
}

pub fn deserialize<'de, L, M, R, D>(deserializer: D) -> Result<super::Among<L, M, R>, D::Error>
where
  D: Deserializer<'de>,
  L: Deserialize<'de>,
  M: Deserialize<'de>,
  R: Deserialize<'de>,
{
  match Among::deserialize(deserializer) {
    Ok(Among::Left(left)) => Ok(super::Among::Left(left)),
    Ok(Among::Middle(middle)) => Ok(super::Among::Middle(middle)),
    Ok(Among::Right(right)) => Ok(super::Among::Right(right)),
    Err(error) => Err(error),
  }
}
