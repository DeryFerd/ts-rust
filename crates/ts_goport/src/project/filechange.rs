//! Go `internal/project/filechange.go`.
//!
//! PORT: Go `collections.Set[lsproto.DocumentUri]` is `FxHashSet` (PORTING
//! default). Go copies of a `FileChangeSummary` share the set maps; the port
//! copies them (the Go callers reassign the returned summary, so the shared
//! writes are not read).

use crate::project::prelude::*;

// Go: project/filechange.go:8 excessiveChangeThreshold
pub const EXCESSIVE_CHANGE_THRESHOLD: i32 = 1000;

// Go: project/filechange.go:10 FileChangeExpander (ts#64291)
pub trait FileChangeExpander {
    fn expand_file_changes(&self, summary: FileChangeSummary) -> FileChangeSummary;
}

// Go: project/filechange.go:14 FileChangeKind
// PORT: Go `type FileChangeKind int` with iota consts. Go
// `FileChangeKindOpen` is `FileChangeKind::OPEN` (same values).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct FileChangeKind(pub i32);

impl FileChangeKind {
    pub const OPEN: FileChangeKind = FileChangeKind(0);
    pub const CLOSE: FileChangeKind = FileChangeKind(1);
    pub const CHANGE: FileChangeKind = FileChangeKind(2);
    pub const SAVE: FileChangeKind = FileChangeKind(3);
    pub const WATCH_CREATE: FileChangeKind = FileChangeKind(4);
    pub const WATCH_CHANGE: FileChangeKind = FileChangeKind(5);
    pub const WATCH_DELETE: FileChangeKind = FileChangeKind(6);

    // Go: project/filechange.go:22 FileChangeKind.IsWatchKind
    pub fn is_watch_kind(self) -> bool {
        self == FileChangeKind::WATCH_CREATE
            || self == FileChangeKind::WATCH_CHANGE
            || self == FileChangeKind::WATCH_DELETE
    }
}

// Go: project/filechange.go:26 FileChange
#[derive(Clone, Debug, Default)]
pub struct FileChange {
    pub kind: FileChangeKind,
    pub uri: lsproto::DocumentUri,
    pub version: i32,                         // Only set for Open/Change
    pub content: String,                      // Only set for Open
    pub language_kind: lsproto::LanguageKind, // Only set for Open
    pub changes: Vec<lsproto::TextDocumentContentChangePartialOrWholeDocument>, // Only set for Change
}

// Go: project/filechange.go:35 FileChangeSummary
// PORT: an empty `DocumentUri` is Go's "" (no file).
#[derive(Clone, Debug, Default)]
pub struct FileChangeSummary {
    // Only one file can be opened at a time per request
    pub opened: lsproto::DocumentUri,
    // Reopened is set if a close and open occurred for the same file in a single batch of changes.
    pub reopened: lsproto::DocumentUri,
    pub closed: FxHashSet<lsproto::DocumentUri>,
    pub changed: FxHashSet<lsproto::DocumentUri>,
    // Only set when file watching is enabled
    pub created: FxHashSet<lsproto::DocumentUri>,
    // Only set when file watching is enabled
    pub deleted: FxHashSet<lsproto::DocumentUri>,

    // IncludesWatchChangeOutsideNodeModules is true if the summary includes a create, change, or delete watch
    // event of a file outside a node_modules directory.
    pub includes_watch_change_outside_node_modules: bool,
    // InvalidateAll indicates that all cached file state should be discarded.
    pub invalidate_all: bool,
}

impl FileChangeSummary {
    // Go: project/filechange.go:54 FileChangeSummary.IsEmpty
    pub fn is_empty(&self) -> bool {
        !self.invalidate_all
            && self.opened.0.is_empty()
            && self.reopened.0.is_empty()
            && self.closed.is_empty()
            && self.changed.is_empty()
            && self.created.is_empty()
            && self.deleted.is_empty()
    }

    // Go: project/filechange.go:58 FileChangeSummary.HasExcessiveWatchEvents
    pub fn has_excessive_watch_events(&self) -> bool {
        self.invalidate_all
            || (self.created.len() + self.deleted.len() + self.changed.len()) as i32
                > EXCESSIVE_CHANGE_THRESHOLD
    }

    // Go: project/filechange.go:62 FileChangeSummary.HasExcessiveNonCreateWatchEvents
    pub fn has_excessive_non_create_watch_events(&self) -> bool {
        self.invalidate_all
            || (self.deleted.len() + self.changed.len()) as i32 > EXCESSIVE_CHANGE_THRESHOLD
    }
}

// Go: project/filechange.go:67 mergeFileChangeSummary
// mergeFileChangeSummary merges src into dst, combining their change sets.
// PORT: Go passes `src` by value; here by reference.
pub fn merge_file_change_summary(dst: &mut FileChangeSummary, src: &FileChangeSummary) {
    if src.is_empty() {
        return;
    }
    if src.invalidate_all {
        dst.invalidate_all = true;
    }
    for uri in &src.changed {
        dst.changed.insert(uri.clone());
    }
    for uri in &src.created {
        dst.created.insert(uri.clone());
    }
    for uri in &src.deleted {
        dst.deleted.insert(uri.clone());
    }
    if src.includes_watch_change_outside_node_modules {
        dst.includes_watch_change_outside_node_modules = true;
    }
}
