//! Go: `internal/collections/{ordered_map,ordered_set,syncmap}_test.go`.
//!
//! PORT: the port has no `collections` package. Each Go site uses the Rust
//! type that PORTING.md names for it, and these tests run the Go checks on
//! those types with the operations the port uses:
//! - `OrderedMap` is `IndexMap`: `Set` is `insert` (keeps the first
//!   position), `Delete` is `shift_remove` (keeps the order), `Clone` is
//!   `clone`, `UnmarshalJSONFrom` is `frontend/json_indexmap.rs`.
//! - `OrderedSet` is `IndexSet` (`Delete` is `shift_remove`).
//! - `SyncMap` is a `RefCell` map on one thread; a Go nil value is `None`.
//! - Go `testing.AllocsPerRun(...) < 10` in the `WithSizeHint` tests: the
//!   port does not count allocations (no custom allocator in this binary).
//!   The check here is that the size hint holds every insert with no
//!   growth, which is what keeps the Go count low.

use std::cell::RefCell;

use indexmap::{IndexMap, IndexSet};
use rustc_hash::FxHashMap;
use ts_goport::frontend::json::json_unmarshal;
use ts_goport::frontend::json_ext::LspAny;

// Go: ordered_map_test.go:138 padInt
fn pad_int(n: i32) -> String {
    format!("{n:10}")
}

// Go: ordered_map_test.go:13 TestOrderedMap
#[test]
fn test_ordered_map() {
    let mut m: IndexMap<i32, String> = IndexMap::new();

    assert!(!m.contains_key(&1));

    const N: i32 = 1000;
    const START: i32 = 1;
    const END: i32 = START + N;

    // Seed the map with ascending keys and values for easier testing.
    for i in START..END {
        m.insert(i, pad_int(i));
    }

    assert_eq!(m.len(), N as usize);

    // Attempt to overwrite existing keys in reverse order.
    for i in (START..END).rev() {
        m.insert(i, pad_int(i));
    }

    assert_eq!(m.len(), N as usize);

    for i in START..END {
        assert_eq!(m.get(&i), Some(&pad_int(i)));
    }

    for (k, v) in &m {
        assert_eq!(*v, pad_int(*k));
    }

    let keys: Vec<i32> = m.keys().copied().collect();
    assert_eq!(keys.len(), N as usize);
    assert!(keys.is_sorted());

    let values: Vec<&String> = m.values().collect();
    assert_eq!(values.len(), N as usize);
    assert!(values.is_sorted());

    assert_eq!(m.keys().next(), Some(&START));
    assert_eq!(m.values().next(), Some(&pad_int(START)));
    assert_eq!(m.iter().next(), Some((&START, &pad_int(START))));

    for i in START + 1..END {
        assert_eq!(m.shift_remove(&i), Some(pad_int(i)));
        assert!(!m.contains_key(&i));
        // Go: Get and Delete of a missing key give the zero value and false.
        assert_eq!(m.get(&i), None);
        assert_eq!(m.shift_remove(&i), None);
    }

    assert_eq!(m.len(), 1);
    assert!(m.contains_key(&START));

    assert_eq!(m.shift_remove(&START), Some(pad_int(START)));

    assert_eq!(m.len(), 0);
}

// Go: ordered_map_test.go:106 TestOrderedMapClone
#[test]
fn test_ordered_map_clone() {
    let mut m: IndexMap<i32, &str> = IndexMap::new();
    m.insert(1, "one");
    m.insert(2, "two");

    let clone = m.clone();

    assert!(!std::ptr::eq(&clone, &m));
    assert_eq!(clone.len(), 2);
    assert_eq!(clone.keys().copied().collect::<Vec<_>>(), [1, 2]);
    assert_eq!(clone.values().copied().collect::<Vec<_>>(), ["one", "two"]);

    assert_eq!(clone.get(&1), Some(&"one"));

    m.shift_remove(&1);

    assert_eq!(m.len(), 1);
    assert_eq!(clone.len(), 2);
    assert_eq!(clone.keys().copied().collect::<Vec<_>>(), [1, 2]);
    assert_eq!(clone.values().copied().collect::<Vec<_>>(), ["one", "two"]);
}

// Go: ordered_map_test.go:132 TestOrderedMapClear
#[test]
fn test_ordered_map_clear() {
    let mut m: IndexMap<i32, &str> = IndexMap::new();
    m.insert(1, "one");
    m.insert(2, "two");

    m.clear();

    assert_eq!(m.len(), 0);
}

// Go: ordered_map_test.go:148 TestOrderedMapWithSizeHint
// PORT: see the module comment (capacity in place of allocation count).
#[test]
fn test_ordered_map_with_size_hint() {
    const N: usize = 1024;
    for _ in 0..10 {
        let mut m: IndexMap<usize, usize> = IndexMap::with_capacity(N);
        let capacity = m.capacity();
        assert!(capacity >= N, "capacity = {capacity}");
        for i in 0..N {
            m.insert(i, i);
        }
        assert_eq!(m.capacity(), capacity, "the map grew after the size hint");
    }
}

// Go: ordered_map_test.go:161 TestOrderedMapUnmarshalJSON
// Go: ordered_map_test.go:170 testOrderedMapUnmarshalJSON (subtest UnmarshalJSONV2)
// PORT: Go `OrderedMap[string, any]` is `IndexMap<String, LspAny>`. The
// last Go check (a map with `int` keys) has no port: `IndexMap<i32, _>`
// has no JSON decode, so that call does not compile.
#[test]
fn test_ordered_map_unmarshal_json() {
    let mut m: IndexMap<String, LspAny> = IndexMap::new();
    let result = json_unmarshal(br#"{"a": 1, "b": "two", "c": { "d": 4 } }"#, &mut m, &[]);
    assert!(result.is_ok(), "{:?}", result.err().map(|e| e.message));

    assert_eq!(m.len(), 3);
    assert_eq!(m.get("a").cloned().unwrap_or_default(), LspAny::Number(1.0));
    assert_eq!(
        m.keys().map(String::as_str).collect::<Vec<_>>(),
        ["a", "b", "c"]
    );

    let result = json_unmarshal(b"null", &mut m, &[]);
    assert!(result.is_ok(), "{:?}", result.err().map(|e| e.message));

    let err = json_unmarshal(br#""foo""#, &mut m, &[]).expect_err("a string is not a map");
    assert!(
        err.message
            .contains("cannot unmarshal non-object JSON value into Map"),
        "{}",
        err.message
    );
}

// Go: ordered_set_test.go:11 TestOrderedSet
#[test]
fn test_ordered_set() {
    let mut s: IndexSet<i32> = IndexSet::new();

    s.insert(1);
    s.insert(2);
    s.insert(3);

    assert!(s.contains(&1));
    assert!(s.contains(&2));
    assert!(s.contains(&3));

    assert!(s.shift_remove(&2));

    let values: Vec<i32> = s.iter().copied().collect();
    assert_eq!(values.len(), 2);
    assert!(values.is_sorted());

    s.clear();

    assert_eq!(s.len(), 0);
    assert!(!s.contains(&1));
    assert!(!s.contains(&2));
    assert!(!s.contains(&3));

    let s2 = s.clone();
    assert!(!std::ptr::eq(&s, &s2));
    assert_eq!(s2.len(), 0);
}

// Go: ordered_set_test.go:42 TestOrderedSetWithSizeHint
// PORT: see the module comment (capacity in place of allocation count).
#[test]
fn test_ordered_set_with_size_hint() {
    const N: usize = 1024;
    for _ in 0..10 {
        let mut s: IndexSet<usize> = IndexSet::with_capacity(N);
        let capacity = s.capacity();
        assert!(capacity >= N, "capacity = {capacity}");
        for i in 0..N {
            s.insert(i);
        }
        assert_eq!(s.capacity(), capacity, "the set grew after the size hint");
    }
}

// Go: syncmap_test.go:10 TestSyncMapWithNil
// PORT: Go `SyncMap[string, any]` holding nil is a `RefCell` map of
// `Option` values: a stored nil is `Some(None)`, a missing key is `None`.
#[test]
fn test_sync_map_with_nil() {
    let m: RefCell<FxHashMap<String, Option<LspAny>>> = RefCell::default();

    // Go: Load of a missing key gives (nil, false).
    let got1 = m.borrow().get("foo").cloned();
    assert_eq!(got1, None);

    m.borrow_mut().insert("foo".to_string(), None);

    // Go: Load of a stored nil gives (nil, true).
    let got2 = m.borrow().get("foo").cloned();
    assert_eq!(got2, Some(None));

    // Go: LoadOrStore of a new key with nil gives (nil, false).
    let (too, loaded) = {
        let mut map = m.borrow_mut();
        match map.get("too") {
            Some(v) => (v.clone(), true),
            None => {
                map.insert("too".to_string(), None);
                (None, false)
            }
        }
    };
    assert!(!loaded);
    assert_eq!(too, None);

    // Go: Range visits the stored entries.
    assert_eq!(m.borrow().iter().count(), 2);
}
