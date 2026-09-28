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
///
/// PORT: Go also has the unexported field `includedWatchRoot`. Code outside
/// this module builds `Event` literals, so the flag is not a field here:
/// `snapshot_since_locked` returns it beside each event, and only
/// `dirWatch.triggerCallbacks` reads it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Event {
    pub kind: EventKind,
    pub path: String,
}

// Go: event.go:32 eventEntry
/// eventEntry tracks coalescing state during a debounce batch.
#[derive(Clone, Copy, Debug, Default)]
pub struct EventEntry {
    pub created_seq: u64,
    pub updated_seq: u64,
    pub deleted_seq: u64,
    pub included_watch_root: bool,
}

impl EventEntry {
    // Go: event.go:255 eventEntry.isDeleted
    pub fn is_deleted(&self) -> bool {
        self.deleted_seq > self.created_seq && self.deleted_seq > self.updated_seq
    }

    // Go: event.go:259 eventEntry.kindSince
    pub fn kind_since(&self, start_seq: u64) -> Option<EventKind> {
        if self.deleted_seq > start_seq {
            if self.created_seq > start_seq
                && self.created_seq < self.deleted_seq
                && self.updated_seq < self.deleted_seq
            {
                return None;
            }
            return Some(EventKind::Delete);
        }
        let seq = self.created_seq.max(self.updated_seq);
        if seq > start_seq {
            return Some(EventKind::Update);
        }
        None
    }
}

// Go: event.go:42 eventList
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
    pub seq: u64,
}

impl EventList {
    // Go: event.go:52 eventList.create
    /// create records a new-file event for path. Both create and update
    /// produce EventUpdate externally; sequence state tracks coalescing
    /// (create+delete within a batch cancels out).
    pub fn create(&self, path: &str) {
        let mut el = self.mu.lock().unwrap();
        let seq = EventList::next_seq_locked(&mut el);
        EventList::create_locked(&mut el, path, seq);
    }

    // Go: event.go:59 eventList.createAt
    pub fn create_at(&self, path: &str, seq: u64) {
        let mut el = self.mu.lock().unwrap();
        EventList::advance_seq_locked(&mut el, seq);
        EventList::create_locked(&mut el, path, seq);
    }

    // Go: event.go:66 eventList.createLocked
    pub fn create_locked(el: &mut EventListLocked, path: &str, seq: u64) {
        let entry = EventList::get_or_create(el, path);
        if entry.is_deleted() {
            // Rapid delete+recreate: clear both flags so the entry
            // emits EventUpdate (the default for non-deleted entries).
            // https://github.com/parcel-bundler/watcher/issues/72
            entry.deleted_seq = 0;
            entry.created_seq = 0;
            entry.updated_seq = seq;
        } else {
            entry.created_seq = seq;
        }
    }

    // Go: event.go:81 eventList.update
    /// update records an update event for path.
    pub fn update(&self, path: &str) {
        let mut el = self.mu.lock().unwrap();
        let seq = EventList::next_seq_locked(&mut el);
        EventList::update_locked(&mut el, path, seq);
    }

    // Go: event.go:88 eventList.updateAt
    pub fn update_at(&self, path: &str, seq: u64) {
        let mut el = self.mu.lock().unwrap();
        EventList::advance_seq_locked(&mut el, seq);
        EventList::update_locked(&mut el, path, seq);
    }

    // Go: event.go:95 eventList.updateWatchRootAt
    pub fn update_watch_root_at(&self, path: &str, seq: u64) {
        let mut el = self.mu.lock().unwrap();
        EventList::advance_seq_locked(&mut el, seq);
        EventList::update_locked(&mut el, path, seq);
        EventList::get_or_create(&mut el, path).included_watch_root = true;
    }

    // Go: event.go:103 eventList.updateLocked
    pub fn update_locked(el: &mut EventListLocked, path: &str, seq: u64) {
        EventList::get_or_create(el, path).updated_seq = seq;
    }

    // Go: event.go:108 eventList.remove
    /// remove records a delete event for path.
    pub fn remove(&self, path: &str) {
        let mut el = self.mu.lock().unwrap();
        let seq = EventList::next_seq_locked(&mut el);
        EventList::remove_locked(&mut el, path, seq);
    }

    // Go: event.go:115 eventList.removeAndGetSequence
    pub fn remove_and_get_sequence(&self, path: &str) -> u64 {
        let mut el = self.mu.lock().unwrap();
        let seq = EventList::next_seq_locked(&mut el);
        EventList::remove_locked(&mut el, path, seq);
        seq
    }

    // Go: event.go:123 eventList.removeAt
    pub fn remove_at(&self, path: &str, seq: u64) {
        let mut el = self.mu.lock().unwrap();
        EventList::advance_seq_locked(&mut el, seq);
        EventList::remove_locked(&mut el, path, seq);
    }

    // Go: event.go:130 eventList.removeWatchRootAt
    pub fn remove_watch_root_at(&self, path: &str, seq: u64) {
        let mut el = self.mu.lock().unwrap();
        EventList::advance_seq_locked(&mut el, seq);
        EventList::remove_locked(&mut el, path, seq);
        EventList::get_or_create(&mut el, path).included_watch_root = true;
    }

    // Go: event.go:138 eventList.removeLocked
    pub fn remove_locked(el: &mut EventListLocked, path: &str, seq: u64) {
        let entry = EventList::get_or_create(el, path);
        entry.deleted_seq = seq;
    }

    // Go: event.go:145 eventList.size
    /// size returns the number of tracked entries (including ones that may
    /// cancel out in getEvents).
    pub fn size(&self) -> i32 {
        let el = self.mu.lock().unwrap();
        el.entries
            .as_ref()
            .map_or(0, |entries| entries.len() as i32)
    }

    // Go: event.go:153 eventList.snapshotLocked
    /// snapshotLocked returns the current set of pending events with
    /// create+delete pairs filtered out. Caller must hold el.mu.
    ///
    /// PORT: takes the data that `el.mu` guards. Go map order is random;
    /// the result order is not guaranteed in Go either.
    pub fn snapshot_locked(el: &EventListLocked) -> Vec<Event> {
        EventList::snapshot_since_locked(el, 0)
            .into_iter()
            .map(|(event, _)| event)
            .collect()
    }

    // Go: event.go:157 eventList.snapshotSinceLocked
    // PORT: each event comes with its Go `includedWatchRoot` flag (see
    // `Event`).
    pub fn snapshot_since_locked(el: &EventListLocked, start_seq: u64) -> Vec<(Event, bool)> {
        let entries = el.entries.as_ref();
        let mut out: Vec<(Event, bool)> =
            Vec::with_capacity(entries.map_or(0, |entries| entries.len()));
        if let Some(entries) = entries {
            for (path, e) in entries {
                let Some(kind) = e.kind_since(start_seq) else {
                    continue;
                };
                out.push((
                    Event {
                        kind,
                        path: path.clone(),
                    },
                    e.included_watch_root,
                ));
            }
        }
        out
    }

    // Go: event.go:171 eventList.getEvents
    /// getEvents returns a snapshot of events, skipping entries that were both
    /// created and deleted. Order is not guaranteed.
    pub fn get_events(&self) -> Vec<Event> {
        let el = self.mu.lock().unwrap();
        EventList::snapshot_locked(&el)
    }

    // Go: event.go:180 eventList.drain
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

    // Go: event.go:190 eventList.drainForSequences
    pub fn drain_for_sequences(
        &self,
        start_seqs: &[u64],
    ) -> (Vec<Vec<(Event, bool)>>, Option<GoError>) {
        let mut el = self.mu.lock().unwrap();
        let mut out: Vec<Vec<(Event, bool)>> = Vec::with_capacity(start_seqs.len());
        for &start_seq in start_seqs {
            out.push(EventList::snapshot_since_locked(&el, start_seq));
        }
        let err = el.err.clone();
        el.entries = None;
        el.err = None;
        (out, err)
    }

    // Go: event.go:204 eventList.setError
    /// setError stores the first error encountered (later errors are ignored).
    pub fn set_error(&self, err: GoError) {
        let mut el = self.mu.lock().unwrap();
        if el.err.is_none() {
            el.err = Some(err);
        }
    }

    // Go: event.go:213 eventList.hasError
    /// hasError reports whether an error has been recorded.
    pub fn has_error(&self) -> bool {
        let el = self.mu.lock().unwrap();
        el.err.is_some()
    }

    // Go: event.go:220 eventList.getError
    /// getError returns the stored error (or nil if none).
    pub fn get_error(&self) -> Option<GoError> {
        let el = self.mu.lock().unwrap();
        el.err.clone()
    }

    // Go: event.go:226 eventList.getOrCreate
    // PORT: Go calls it with el.mu held; it takes the guarded data. Go
    // returns the map's `*eventEntry`; the port returns a mutable reference
    // into the map.
    pub fn get_or_create<'a>(el: &'a mut EventListLocked, path: &str) -> &'a mut EventEntry {
        let entries = el.entries.get_or_insert_with(FxHashMap::default);
        entries.entry(path.to_string()).or_default()
    }

    // Go: event.go:238 eventList.sequence
    pub fn sequence(&self) -> u64 {
        let el = self.mu.lock().unwrap();
        el.seq
    }

    // Go: event.go:244 eventList.nextSeqLocked
    pub fn next_seq_locked(el: &mut EventListLocked) -> u64 {
        el.seq += 1;
        el.seq
    }

    // Go: event.go:249 eventList.advanceSeqLocked
    pub fn advance_seq_locked(el: &mut EventListLocked, seq: u64) {
        if seq > el.seq {
            el.seq = seq;
        }
    }
}
