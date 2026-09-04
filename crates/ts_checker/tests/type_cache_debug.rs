use std::collections::HashMap;

use ts_checker::semantic::{
    CacheHashKey, CanonicalSemanticStore, type_records::TypeCacheState, types::TypeFlags,
};

#[test]
fn type_cache_debug_keeps_entries_in_key_order() {
    let mut store = CanonicalSemanticStore::<()>::new();
    let string = store
        .alloc_intrinsic_type(TypeFlags::STRING, "string")
        .unwrap();
    let number = store
        .alloc_intrinsic_type(TypeFlags::NUMBER, "number")
        .unwrap();
    let entries = [
        (CacheHashKey::new(30), string),
        (CacheHashKey::new(10), number),
        (CacheHashKey::new(20), string),
    ];
    let first = TypeCacheState::Allocated(HashMap::from(entries));
    let mut other = HashMap::with_capacity(64);
    other.extend(entries.into_iter().rev());
    let second = TypeCacheState::Allocated(other);
    let expected = format!(
        "Allocated({{CacheHashKey(10): {number:?}, CacheHashKey(20): {string:?}, CacheHashKey(30): {string:?}}})"
    );
    assert_eq!(format!("{first:?}"), expected);
    assert_eq!(format!("{second:?}"), expected);
    assert_eq!(format!("{first:#?}"), format!("{second:#?}"));
    assert_eq!(first, second);

    let changed = TypeCacheState::Allocated(HashMap::from([
        (CacheHashKey::new(10), number),
        (CacheHashKey::new(20), number),
        (CacheHashKey::new(30), string),
    ]));
    assert_ne!(format!("{changed:?}"), expected);
}

#[test]
fn type_cache_debug_keeps_allocation_state() {
    assert_eq!(format!("{:?}", TypeCacheState::Unallocated), "Unallocated");
    assert_eq!(
        format!("{:?}", TypeCacheState::Allocated(HashMap::new())),
        "Allocated({})"
    );
}
