//! Go: internal/fswatch/event.go (event kinds and the per-directory event
//! list that coalesces events inside one debounce window).
//!
//! PORT: the backend threads and the debouncer thread share an `eventList`,
//! so Go `el.mu` is a `std::sync::Mutex` over the fields it guards
//! (`EventListLocked`). Go's `*Locked` helpers take that guarded data.

use crate::fswatch::prelude::*;

use std::sync::Mutex;

// Go: event.go:6 EventKind
/// EventKind classifies a filesystem change.
///
/// PORT: Go `type EventKind int` with the consts `EventUpdate` (1) and
/// `EventDelete` (2). The shared contract (map-watch-api U1) makes it an
/// enum with the same values.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum EventKind {
    Update = 1,
    Delete = 2,
}

impl EventKind {
    // Go: event.go:13 EventKind.String
    // PORT: Go also has a `default: "unknown"` case for other ints. The
    // enum has no other values.
    pub fn string(&self) -> String {
        match self {
            EventKind::Update => "update".to_string(),
            EventKind::Delete => "delete".to_string(),
        }
    }
}

// Go: event.go:25 Event
/// Event describes a single filesystem change.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Event {
    pub kind: EventKind,
    pub path: String,
}

// Go: event.go:33 eventEntry
/// eventEntry tracks coalescing state during a debounce batch.
/// The two booleans are independent: a file can be created then deleted
/// in the same batch, which cancels out (filtered by getEvents).
#[derive(Clone, Copy, Debug, Default)]
pub struct EventEntry {
    pub is_created: bool,
    pub is_deleted: bool,
}

// Go: event.go:41 eventList
/// eventList coalesces filesystem events by path within a debounce window.
///   - create after delete → update (rapid delete+recreate)
///   - getEvents skips entries that were both created and deleted
#[derive(Default)]
pub struct EventList {
    pub mu: Mutex<EventListLocked>,
}

/// PORT: the `eventList` fields that Go `el.mu` guards.
#[derive(Default)]
pub struct EventListLocked {
    /// Go `map[string]*eventEntry`; `None` is Go's nil map.
    pub entries: Option<FxHashMap<String, EventEntry>>,
    pub err: Option<GoError>,
}

impl EventList {
    // Go: event.go:50 eventList.create
    /// create records a new-file event for path. Both create and update
    /// produce EventUpdate externally; isCreated is tracked only for
    /// coalescing (create+delete within a batch cancels out).
    pub fn create(&self, path: &str) {
        let mut el = self.mu.lock().unwrap();
        let entry = EventList::get_or_create(&mut el, path);
        if entry.is_deleted {
            // Rapid delete+recreate: clear both flags so the entry
            // emits EventUpdate (the default for non-deleted entries).
            // https://github.com/parcel-bundler/watcher/issues/72
            entry.is_deleted = false;
            entry.is_created = false;
        } else {
            entry.is_created = true;
        }
    }

    // Go: event.go:66 eventList.update
    /// update records an update event for path.
    pub fn update(&self, path: &str) {
        let mut el = self.mu.lock().unwrap();
        EventList::get_or_create(&mut el, path);
    }

    // Go: event.go:73 eventList.remove
    /// remove records a delete event for path.
    pub fn remove(&self, path: &str) {
        let mut el = self.mu.lock().unwrap();
        let entry = EventList::get_or_create(&mut el, path);
        entry.is_deleted = true;
    }

    // Go: event.go:82 eventList.size
    /// size returns the number of tracked entries (including ones that may
    /// cancel out in getEvents).
    pub fn size(&self) -> i32 {
        let el = self.mu.lock().unwrap();
        el.entries
            .as_ref()
            .map_or(0, |entries| entries.len() as i32)
    }

    // Go: event.go:90 eventList.snapshotLocked
    /// snapshotLocked returns the current set of pending events with
    /// create+delete pairs filtered out. Caller must hold el.mu.
    ///
    /// PORT: takes the data that `el.mu` guards. Go map order is random;
    /// the result order is not guaranteed in Go either.
    pub fn snapshot_locked(el: &EventListLocked) -> Vec<Event> {
        let entries = el.entries.as_ref();
        let mut out: Vec<Event> = Vec::with_capacity(entries.map_or(0, |entries| entries.len()));
        if let Some(entries) = entries {
            for (path, e) in entries {
                if e.is_created && e.is_deleted {
                    continue;
                }
                let mut kind = EventKind::Update;
                if e.is_deleted {
                    kind = EventKind::Delete;
                }
                out.push(Event {
                    kind,
                    path: path.clone(),
                });
            }
        }
        out
    }

    // Go: event.go:107 eventList.getEvents
    /// getEvents returns a snapshot of events, skipping entries that were both
    /// created and deleted. Order is not guaranteed.
    pub fn get_events(&self) -> Vec<Event> {
        let el = self.mu.lock().unwrap();
        EventList::snapshot_locked(&el)
    }

    // Go: event.go:116 eventList.drain
    /// drain atomically snapshots all pending events and the stored error,
    /// then clears the list. This prevents events added between a separate
    /// getEvents+clear from being silently dropped.
    pub fn drain(&self) -> (Vec<Event>, Option<GoError>) {
        let mut el = self.mu.lock().unwrap();
        let out = EventList::snapshot_locked(&el);
        let err = el.err.clone();
        el.entries = None;
        el.err = None;
        (out, err)
    }

    // Go: event.go:127 eventList.setError
    /// setError stores the first error encountered (later errors are ignored).
    pub fn set_error(&self, err: GoError) {
        let mut el = self.mu.lock().unwrap();
        if el.err.is_none() {
            el.err = Some(err);
        }
    }

    // Go: event.go:136 eventList.hasError
    /// hasError reports whether an error has been recorded.
    pub fn has_error(&self) -> bool {
        let el = self.mu.lock().unwrap();
        el.err.is_some()
    }

    // Go: event.go:143 eventList.getError
    /// getError returns the stored error (or nil if none).
    pub fn get_error(&self) -> Option<GoError> {
        let el = self.mu.lock().unwrap();
        el.err.clone()
    }

    // Go: event.go:149 eventList.getOrCreate
    // PORT: Go calls it with el.mu held; it takes the guarded data. Go
    // returns the map's `*eventEntry`; the port returns a mutable reference
    // into the map.
    pub fn get_or_create<'a>(el: &'a mut EventListLocked, path: &str) -> &'a mut EventEntry {
        let entries = el.entries.get_or_insert_with(FxHashMap::default);
        entries.entry(path.to_string()).or_default()
    }
}
