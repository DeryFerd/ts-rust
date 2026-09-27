//! Go: `internal/fswatch/eventlist_test.go`.

use ts_goport::fswatch::{EventKind, EventList};
use ts_goport::gostd::errors;

// Go: eventlist_test.go:12 (*eventList).clear (test-only)
fn clear(el: &EventList) {
    let mut locked = el.mu.lock().unwrap();
    locked.entries = None;
    locked.err = None;
}

// Go: eventlist_test.go:19 TestEventListCreateThenDelete
#[test]
fn test_event_list_create_then_delete() {
    let el = EventList::default();
    el.create("a");
    el.remove("a");
    assert_eq!(el.size(), 1, "size after create+remove");
    let got = el.get_events();
    assert!(
        got.is_empty(),
        "getEvents should drop create+delete, got {got:?}"
    );
}

// Go: eventlist_test.go:32 TestEventListDeleteThenCreate
#[test]
fn test_event_list_delete_then_create() {
    let el = EventList::default();
    el.remove("a");
    el.create("a");
    let got = el.get_events();
    assert_eq!(got.len(), 1, "expected 1 event");
    // "Assume update event when rapidly removed and created".
    assert_eq!(got[0].kind, EventKind::Update);
}

// Go: eventlist_test.go:47 TestEventListCreateDeleteCreate
#[test]
fn test_event_list_create_delete_create() {
    let el = EventList::default();
    el.create("a");
    el.remove("a");
    el.create("a");
    let got = el.get_events();
    assert_eq!(got.len(), 1, "expected 1 event");
    assert_eq!(
        got[0].kind,
        EventKind::Update,
        "create+delete+create should coalesce to update"
    );
}

// Go: eventlist_test.go:62 TestEventListErrorIsLatchedAndCleared
#[test]
fn test_event_list_error_is_latched_and_cleared() {
    let el = EventList::default();
    assert!(!el.has_error(), "fresh eventList should have no error");
    assert!(el.get_error().is_none(), "fresh getError want nil");
    el.set_error(errors::new("first"));
    el.set_error(errors::new("second")); // only first wins
    assert!(el.has_error(), "hasError should be true after setError");
    assert_eq!(el.get_error().map(|e| e.error()), Some("first".to_string()));
    clear(&el);
    assert!(!el.has_error(), "clear should drop the error");
    assert!(el.get_error().is_none(), "post-clear getError want nil");
}

// Go: eventlist_test.go:88 TestEventListDrainIsAtomic
#[test]
fn test_event_list_drain_is_atomic() {
    let el = EventList::default();
    el.create("a");
    el.update("b");
    el.set_error(errors::new("oops"));

    let (events, err) = el.drain();
    assert!(err.is_some(), "drain should return the error");
    assert_eq!(events.len(), 2, "drain should return 2 events");

    let (events2, err2) = el.drain();
    assert!(err2.is_none(), "second drain should have no error");
    assert_eq!(events2.len(), 0, "second drain should be empty");
}

// Go: eventlist_test.go:112 TestEventListDrainReturnsErrorWithEvents
#[test]
fn test_event_list_drain_returns_error_with_events() {
    let el = EventList::default();
    el.create("file.txt");
    el.set_error(errors::new("overflow"));

    let (events, err) = el.drain();
    assert!(err.is_some(), "expected error from drain");
    assert_eq!(events.len(), 1, "expected 1 event alongside error");
}
