//! JSON impls for `IndexMap` that must live in `goport_util`, the crate of
//! `MarshalerTo` and `UnmarshalerFrom` (orphan rule): the decode of Go
//! `collections.OrderedMap`, and the `JsonMapKey` bridge for map key types
//! of the crates above.

use crate::frontend::json::{
    JsonDecoder, JsonError, MarshalerTo, UnmarshalerFrom, json_unmarshal_decode,
};
use indexmap::IndexMap;

// Go: collections/ordered_map.go:263 (*OrderedMap).UnmarshalJSONFrom
// PORT: Go `collections.OrderedMap` is `IndexMap`. `IndexMap::insert` keeps
// the first position and replaces the value, like `OrderedMap.Set`.
impl<V: UnmarshalerFrom + Default> UnmarshalerFrom for IndexMap<String, V> {
    fn unmarshal_json_from(&mut self, dec: &mut JsonDecoder<'_>) -> Result<(), JsonError> {
        let token = dec.read_token()?;
        if token.kind() == b'n' {
            // By convention, to approximate the behavior of Unmarshal itself,
            // Unmarshalers implement UnmarshalJSON([]byte("null")) as a no-op.
            return Ok(());
        }
        if token.kind() != b'{' {
            return Err(JsonError {
                message: "cannot unmarshal non-object JSON value into Map".to_string(),
            });
        }
        while dec.peek_kind() != b'}' {
            let mut key = String::new();
            let mut value = V::default();
            json_unmarshal_decode(dec, &mut key)?;
            json_unmarshal_decode(dec, &mut value)?;
            self.insert(key, value);
        }
        dec.read_token()?;
        Ok(())
    }
}

/// A map key type of a crate above `goport_util` whose `IndexMap<K, V>` has
/// its own JSON methods (lsproto `DocumentUri`, Go `map[DocumentUri]V`).
/// PORT: the orphan rule stops that crate from implementing `MarshalerTo`
/// and `UnmarshalerFrom` for `IndexMap<K, V>`. It implements this trait on
/// the key, and the two impls below call it.
pub trait JsonMapKey: Sized {
    /// `MarshalerTo::marshal_json_to` of `map`.
    fn marshal_map<V: MarshalerTo>(
        map: &IndexMap<Self, V>,
        enc: &mut String,
    ) -> Result<(), JsonError>;

    /// `UnmarshalerFrom::unmarshal_json_from` of `map`.
    fn unmarshal_map<V: UnmarshalerFrom + Default + Clone>(
        map: &mut IndexMap<Self, V>,
        dec: &mut JsonDecoder<'_>,
    ) -> Result<(), JsonError>;
}

impl<K: JsonMapKey, V: MarshalerTo> MarshalerTo for IndexMap<K, V> {
    fn marshal_json_to(&self, enc: &mut String) -> Result<(), JsonError> {
        K::marshal_map(self, enc)
    }
}

impl<K: JsonMapKey, V: UnmarshalerFrom + Default + Clone> UnmarshalerFrom for IndexMap<K, V> {
    fn unmarshal_json_from(&mut self, dec: &mut JsonDecoder<'_>) -> Result<(), JsonError> {
        K::unmarshal_map(self, dec)
    }
}
