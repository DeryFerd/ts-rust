//! Port of Go `internal/project/dirty/syncmap_test.go`.
//!
//! PORT: the Rust `SyncMap` is single-threaded (`Rc`), so the Go
//! goroutines run one after the other. The "race" in the first subtest is
//! the same two loads of one key followed by two changes.

use std::cell::RefCell;
use std::rc::Rc;

use rustc_hash::FxHashMap;
use ts_goport::project::dirty::{Cloneable, SyncMapEntry, Value, new_sync_map};

// Go: syncmap_test.go:11 testValue
// testValue is a simple cloneable type for testing
// PORT: Go `*testValue`; `Clone` shares it, `clone_` is Go `Clone`.
#[derive(Clone)]
struct TestValue(Rc<RefCell<String>>);

impl TestValue {
    fn new(data: &str) -> TestValue {
        TestValue(Rc::new(RefCell::new(data.to_string())))
    }
    fn data(&self) -> String {
        self.0.borrow().clone()
    }
    fn set(&self, data: &str) {
        *self.0.borrow_mut() = data.to_string();
    }
}

impl Cloneable for TestValue {
    fn clone_(&self) -> Self {
        TestValue::new(&self.data())
    }
}

type Entry = Rc<SyncMapEntry<String, TestValue>>;

fn base(key: &str, data: &str) -> FxHashMap<String, TestValue> {
    let mut m = FxHashMap::default();
    m.insert(key.to_string(), TestValue::new(data));
    m
}

fn value_data(e: &Entry) -> String {
    e.value().expect("entry value").data()
}

fn proxy_for(e: &Entry) -> Option<Entry> {
    e.proxy_for.borrow().clone()
}

// Go: syncmap_test.go:22 TestSyncMapProxyFor/proxy for race condition
#[test]
fn proxy_for_race_condition() {
    // Create a sync map with a base value
    let sync_map = new_sync_map(base("key1", "original"));

    // Load the same entry from multiple goroutines to simulate race condition
    let (entry1, ok) = sync_map.load(&"key1".to_string());
    assert!(ok, "entry1 should be loaded");
    let (entry2, ok) = sync_map.load(&"key1".to_string());
    assert!(ok, "entry2 should be loaded");
    let entry1 = entry1.unwrap();
    let entry2 = entry2.unwrap();

    // Both entries should exist and have the same initial value
    assert_eq!("original", value_data(&entry1));
    assert_eq!("original", value_data(&entry2));
    assert!(!entry1.dirty());
    assert!(!entry2.dirty());

    // Now try to change both entries concurrently to trigger the proxy mechanism.
    entry1.change(&mut |v: &TestValue| v.set("changed_by_entry1"));
    entry2.change(&mut |v: &TestValue| v.set("changed_by_entry2"));

    // After the race, one entry should have proxyFor set and both should reflect the same final state
    let final_value1 = value_data(&entry1);
    let final_value2 = value_data(&entry2);
    assert_eq!(
        final_value1, final_value2,
        "both entries should have the same final value"
    );

    // Both entries should be marked as dirty
    assert!(entry1.dirty());
    assert!(entry2.dirty());

    // At least one entry should have proxyFor set (the one that lost the race)
    let has_proxy = proxy_for(&entry1).is_some() || proxy_for(&entry2).is_some();
    assert!(has_proxy, "at least one entry should have proxyFor set");

    // If entry1 has a proxy, it should point to entry2, and vice versa
    if let Some(p) = proxy_for(&entry1) {
        assert!(Rc::ptr_eq(&entry2, &p), "entry1 should proxy to entry2");
    }
    if let Some(p) = proxy_for(&entry2) {
        assert!(Rc::ptr_eq(&entry1, &p), "entry2 should proxy to entry1");
    }
}

/// Loads `key` twice and changes both entries, so one becomes a proxy.
/// Returns (proxy, target).
fn proxy_pair(
    sync_map: &ts_goport::project::dirty::SyncMap<String, TestValue>,
    key: &str,
    a: &str,
    b: &str,
) -> (Entry, Entry) {
    let (entry1, ok1) = sync_map.load(&key.to_string());
    assert!(ok1);
    let (entry2, ok2) = sync_map.load(&key.to_string());
    assert!(ok2);
    let entry1 = entry1.unwrap();
    let entry2 = entry2.unwrap();

    let a = a.to_string();
    let b = b.to_string();
    entry1.change(&mut |v: &TestValue| v.set(&a));
    entry2.change(&mut |v: &TestValue| v.set(&b));

    if proxy_for(&entry1).is_some() {
        (entry1, entry2)
    } else {
        (entry2, entry1)
    }
}

// Go: syncmap_test.go:105 TestSyncMapProxyFor/proxy operations delegation
#[test]
fn proxy_operations_delegation() {
    let sync_map = new_sync_map(base("key1", "original"));

    // Force one to become a proxy by making them both dirty in sequence
    let (proxy, target) = proxy_pair(&sync_map, "key1", "changed_by_entry1", "changed_by_entry2");

    // Test that proxy operations are delegated to the target
    // Change through proxy should affect target
    proxy.change(&mut |v: &TestValue| v.set("changed_through_proxy"));
    assert_eq!("changed_through_proxy", value_data(&target));
    assert_eq!("changed_through_proxy", value_data(&proxy));

    // ChangeIf through proxy should work
    let changed = proxy.change_if(
        &mut |v: Option<&TestValue>| v.expect("value").data() == "changed_through_proxy",
        &mut |v: &TestValue| v.set("conditional_change"),
    );
    assert!(changed);
    assert_eq!("conditional_change", value_data(&target));
    assert_eq!("conditional_change", value_data(&proxy));

    // Dirty status should be consistent
    assert_eq!(target.dirty(), proxy.dirty());

    // Locked operations should work through proxy
    proxy.locked(&mut |v: &dyn Value<TestValue>| {
        v.change(&mut |val: &TestValue| val.set("locked_change"));
    });
    assert_eq!("locked_change", value_data(&target));
    assert_eq!("locked_change", value_data(&proxy));
}

// Go: syncmap_test.go:167 TestSyncMapProxyFor/proxy delete operations
#[test]
fn proxy_delete_operations() {
    let sync_map = new_sync_map(base("key1", "original"));

    // Load two entries and make one a proxy
    let (proxy, _) = proxy_pair(&sync_map, "key1", "modified", "modified2");

    // Delete through proxy should affect target
    proxy.delete();

    // Both should reflect the deletion
    let (_, exists) = sync_map.load(&"key1".to_string());
    assert!(!exists, "key should be deleted from sync map");

    // DeleteIf through proxy should work
    let sync_map2 = new_sync_map(base("key2", "test"));

    let (proxy2, _) = proxy_pair(&sync_map2, "key2", "modified", "modified2");

    proxy2.delete_if(&mut |v: Option<&TestValue>| {
        let data = v.expect("value").data();
        data == "modified2" || data == "modified"
    });

    let (_, exists2) = sync_map2.load(&"key2".to_string());
    assert!(!exists2, "key2 should be deleted conditionally");
}

// Go: syncmap_test.go:224 TestSyncMapProxyFor/no proxy when no race
#[test]
fn no_proxy_when_no_race() {
    let sync_map = new_sync_map(base("key1", "original"));

    // Load and modify a single entry - no race condition
    let (entry, ok) = sync_map.load(&"key1".to_string());
    assert!(ok);
    let entry = entry.unwrap();

    entry.change(&mut |v: &TestValue| v.set("changed"));

    // Should not have a proxy since there was no race
    assert!(
        proxy_for(&entry).is_none(),
        "entry should not have proxyFor when no race occurs"
    );
    assert!(entry.dirty());
    assert_eq!("changed", value_data(&entry));
}
