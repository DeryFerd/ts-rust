//! Go `internal/project/overlayfs.go`.
//!
//! PORT: one thread (project/dirty/interfaces.rs). Go `sync.Once` + value is
//! a `OnceCell`; `mu` is dropped. Go `xxh3.Uint128` is `u128`. A Go
//! `FileHandle` is `Rc<dyn FileHandle>` (nil is `None`): an `*Overlay` is
//! `Rc<Overlay>` and a `*diskFile` is `Rc<RefCell<DiskFile>>` (the dirty maps
//! change it after sharing). Go `string` results are owned `String`s.

use crate::project::prelude::*;

use crate::frontend::core_ext::get_script_kind_from_file_name;
use std::cell::{Cell, OnceCell};
use xxhash_rust::xxh3::xxh3_128;

// Go: project/overlayfs.go:17 FileContent
pub trait FileContent {
    fn content(&self) -> String;
    fn hash(&self) -> u128;
}

// Go: project/overlayfs.go:22 FileHandle
pub trait FileHandle: FileContent {
    fn file_name(&self) -> String;
    fn version(&self) -> i32;
    fn matches_disk_text(&self) -> bool;
    fn is_overlay(&self) -> bool;
    fn lsp_line_map(&self) -> Rc<lsconv::LSPLineMap>;
    fn ecma_line_info(&self) -> Rc<sourcemap::lineinfo::ECMALineInfo>;
    fn kind(&self) -> ScriptKind;
}

// Go: project/overlayfs.go:33 fileBase
// PORT: `hash` is a `Cell` because Go writes it on an overlay that may be
// shared (processChanges).
#[derive(Debug, Default)]
pub struct FileBase {
    pub file_name: String,
    pub content: String,
    pub hash: Cell<u128>,

    pub line_map: OnceCell<Rc<lsconv::LSPLineMap>>,
    pub line_info: OnceCell<Rc<sourcemap::lineinfo::ECMALineInfo>>,
}

impl FileBase {
    // Go: project/overlayfs.go:44 fileBase.FileName
    pub fn file_name(&self) -> String {
        self.file_name.clone()
    }

    // Go: project/overlayfs.go:48 fileBase.Hash
    pub fn hash(&self) -> u128 {
        self.hash.get()
    }

    // Go: project/overlayfs.go:52 fileBase.Content
    pub fn content(&self) -> String {
        self.content.clone()
    }

    // Go: project/overlayfs.go:56 fileBase.LSPLineMap
    pub fn lsp_line_map(&self) -> Rc<lsconv::LSPLineMap> {
        self.line_map
            .get_or_init(|| lsconv::compute_lsp_line_starts(&self.content))
            .clone()
    }

    // Go: project/overlayfs.go:63 fileBase.ECMALineInfo
    pub fn ecma_line_info(&self) -> Rc<sourcemap::lineinfo::ECMALineInfo> {
        self.line_info
            .get_or_init(|| {
                let line_starts = compute_ecma_line_starts(&self.content);
                Rc::new(sourcemap::lineinfo::create_ecma_line_info(
                    &self.content,
                    line_starts,
                ))
            })
            .clone()
    }
}

// Go: project/overlayfs.go:71 diskFile
// PORT: Go embeds `fileBase`; here it is the field `file_base`.
#[derive(Debug, Default)]
pub struct DiskFile {
    pub file_base: FileBase,
    pub needs_reload: bool,
    pub realpath_path: tspath::Path,
}

// Go: project/overlayfs.go:77 newDiskFile
// PORT: `content` is owned because the file keeps it.
pub fn new_disk_file(file_name: &str, content: String) -> Rc<RefCell<DiskFile>> {
    let hash = xxh3_128(content.as_bytes());
    Rc::new(RefCell::new(DiskFile {
        file_base: FileBase {
            file_name: file_name.to_string(),
            content,
            hash: Cell::new(hash),
            ..FileBase::default()
        },
        ..DiskFile::default()
    }))
}

impl DiskFile {
    // Go: project/overlayfs.go:89 diskFile.Version
    pub fn version(&self) -> i32 {
        0
    }

    // Go: project/overlayfs.go:93 diskFile.MatchesDiskText
    pub fn matches_disk_text(&self) -> bool {
        !self.needs_reload
    }

    // Go: project/overlayfs.go:97 diskFile.IsOverlay
    pub fn is_overlay(&self) -> bool {
        false
    }

    // Go: project/overlayfs.go:101 diskFile.Kind
    pub fn kind(&self) -> ScriptKind {
        get_script_kind_from_file_name(&self.file_base.file_name)
    }

    // Go: project/overlayfs.go:105 diskFile.Clone
    // PORT: Go `Clone`; `clone_` keeps it apart from `std::clone::Clone`.
    pub fn clone_(&self) -> Rc<RefCell<DiskFile>> {
        Rc::new(RefCell::new(DiskFile {
            realpath_path: self.realpath_path.clone(),
            file_base: FileBase {
                file_name: self.file_base.file_name.clone(),
                content: self.file_base.content.clone(),
                hash: Cell::new(self.file_base.hash.get()),
                ..FileBase::default()
            },
            ..DiskFile::default()
        }))
    }
}

// PORT: the dirty maps hold `*diskFile` and call its `Clone`.
impl dirty::Cloneable for Rc<RefCell<DiskFile>> {
    fn clone_(&self) -> Self {
        self.borrow().clone_()
    }
}

// Go: project/overlayfs.go:87 `var _ FileHandle = (*diskFile)(nil)`
// PORT: the methods of `fileBase` are promoted through the embedding.
impl FileContent for RefCell<DiskFile> {
    fn content(&self) -> String {
        self.borrow().file_base.content()
    }

    fn hash(&self) -> u128 {
        self.borrow().file_base.hash()
    }
}

impl FileHandle for RefCell<DiskFile> {
    fn file_name(&self) -> String {
        self.borrow().file_base.file_name()
    }

    fn version(&self) -> i32 {
        self.borrow().version()
    }

    fn matches_disk_text(&self) -> bool {
        self.borrow().matches_disk_text()
    }

    fn is_overlay(&self) -> bool {
        self.borrow().is_overlay()
    }

    fn lsp_line_map(&self) -> Rc<lsconv::LSPLineMap> {
        self.borrow().file_base.lsp_line_map()
    }

    fn ecma_line_info(&self) -> Rc<sourcemap::lineinfo::ECMALineInfo> {
        self.borrow().file_base.ecma_line_info()
    }

    fn kind(&self) -> ScriptKind {
        self.borrow().kind()
    }
}

// Go: project/overlayfs.go:118 Overlay
// PORT: Go embeds `fileBase`; here it is the field `file_base`. `version`
// and `matches_disk_text` are `Cell`s because Go writes them on an overlay
// that may be shared (processChanges).
#[derive(Debug, Default)]
pub struct Overlay {
    pub file_base: FileBase,
    pub version: Cell<i32>,
    pub kind: ScriptKind,
    pub matches_disk_text: Cell<bool>,
}

// Go: project/overlayfs.go:125 newOverlay
// PORT: `content` is owned because the overlay keeps it.
pub fn new_overlay(file_name: &str, content: String, version: i32, kind: ScriptKind) -> Overlay {
    let hash = xxh3_128(content.as_bytes());
    Overlay {
        file_base: FileBase {
            file_name: file_name.to_string(),
            content,
            hash: Cell::new(hash),
            ..FileBase::default()
        },
        version: Cell::new(version),
        kind,
        ..Overlay::default()
    }
}

impl Overlay {
    // Go: project/overlayfs.go:141 Overlay.Text
    pub fn text(&self) -> String {
        self.file_base.content.clone()
    }

    // Go: project/overlayfs.go:151 Overlay.computeMatchesDiskText
    // !!! optimization: incorporate mtime
    // PORT: Go named results `(matchesDiskText bool, exists bool)`.
    pub fn compute_matches_disk_text(&self, fs: &dyn vfs::Fs) -> (bool, bool) {
        if tspath::is_dynamic_file_name(&self.file_base.file_name) {
            return (false, false);
        }
        let (disk_content, ok) = fs.read_file(&self.file_base.file_name);
        if !ok {
            return (false, false);
        }
        (
            xxh3_128(disk_content.as_bytes()) == self.file_base.hash(),
            true,
        )
    }
}

// Go: project/overlayfs.go:116 `var _ FileHandle = (*Overlay)(nil)`
// PORT: the methods of `fileBase` are promoted through the embedding.
impl FileContent for Overlay {
    fn content(&self) -> String {
        self.file_base.content()
    }

    fn hash(&self) -> u128 {
        self.file_base.hash()
    }
}

impl FileHandle for Overlay {
    fn file_name(&self) -> String {
        self.file_base.file_name()
    }

    // Go: project/overlayfs.go:137 Overlay.Version
    fn version(&self) -> i32 {
        self.version.get()
    }

    // Go: project/overlayfs.go:146 Overlay.MatchesDiskText
    // MatchesDiskText may return false negatives, but never false positives.
    fn matches_disk_text(&self) -> bool {
        self.matches_disk_text.get()
    }

    // Go: project/overlayfs.go:162 Overlay.IsOverlay
    fn is_overlay(&self) -> bool {
        true
    }

    fn lsp_line_map(&self) -> Rc<lsconv::LSPLineMap> {
        self.file_base.lsp_line_map()
    }

    fn ecma_line_info(&self) -> Rc<sourcemap::lineinfo::ECMALineInfo> {
        self.file_base.ecma_line_info()
    }

    // Go: project/overlayfs.go:166 Overlay.Kind
    fn kind(&self) -> ScriptKind {
        self.kind
    }
}

// PORT: Go passes an `*Overlay` to `Converters.FromLSPTextChange` as an
// `lsconv.Script` (its `FileName` and `Text` methods).
impl lsconv::Script for Overlay {
    fn file_name(&self) -> &str {
        &self.file_base.file_name
    }

    fn text(&self) -> &str {
        &self.file_base.content
    }
}

// Go: project/overlayfs.go:170 overlayFS
// PORT: `mu` is dropped; `overlays` is replaced after sharing, so it is a
// `RefCell`. Go `map[tspath.Path]*Overlay` is an `IndexMap` (insertion
// order; PORT: Go map order is random), because the project collection
// ranges over the overlays when it picks inferred project roots.
pub struct OverlayFS {
    pub to_path: Rc<dyn Fn(&str) -> tspath::Path>,
    pub fs: Rc<dyn vfs::Fs>,
    pub position_encoding: lsproto::PositionEncodingKind,

    pub overlays: RefCell<IndexMap<tspath::Path, Rc<Overlay>>>,
}

// Go: project/overlayfs.go:179 newOverlayFS
pub fn new_overlay_fs(
    fs: Rc<dyn vfs::Fs>,
    overlays: IndexMap<tspath::Path, Rc<Overlay>>,
    position_encoding: lsproto::PositionEncodingKind,
    to_path: Rc<dyn Fn(&str) -> tspath::Path>,
) -> Rc<OverlayFS> {
    Rc::new(OverlayFS {
        fs,
        position_encoding,
        overlays: RefCell::new(overlays),
        to_path,
    })
}

impl OverlayFS {
    // Go: project/overlayfs.go:188 overlayFS.Overlays
    // PORT: Go returns the shared map; the port returns a copy of it.
    pub fn overlays(&self) -> IndexMap<tspath::Path, Rc<Overlay>> {
        self.overlays.borrow().clone()
    }

    // Go: project/overlayfs.go:194 overlayFS.getFile
    pub fn get_file(&self, file_name: &str) -> Option<Rc<dyn FileHandle>> {
        let path = (self.to_path)(file_name);
        let overlay = self.overlays.borrow().get(&path).cloned();
        if let Some(overlay) = overlay {
            return Some(overlay);
        }

        let (content, ok) = self.fs.read_file(file_name);
        if !ok {
            return None;
        }
        Some(new_disk_file(file_name, content))
    }

    // Go: project/overlayfs.go:211 overlayFS.processChanges
    // PORT: Go takes the slice; here a borrowed slice. The per-file events
    // keep references into it where Go keeps pointers to copies. Go ranges
    // over `fileEventMap` (random order); the port keeps the order in which
    // each URI first appears.
    pub fn process_changes(
        &self,
        changes: &[FileChange],
    ) -> (FileChangeSummary, IndexMap<tspath::Path, Rc<Overlay>>) {
        let mut result = FileChangeSummary::default();
        let mut new_overlays = self.overlays.borrow().clone();

        // Reduced collection of changes that occurred on a single file
        #[derive(Default)]
        struct FileEvents<'a> {
            open_change: Option<&'a FileChange>,
            close_change: Option<&'a FileChange>,
            watch_changed: bool,
            changes: Vec<&'a FileChange>,
            saved: bool,
            created: bool,
            deleted: bool,
        }

        let mut file_event_map: IndexMap<lsproto::DocumentUri, FileEvents<'_>> = IndexMap::new();

        for change in changes {
            let uri = &change.uri;
            if let Some(events) = file_event_map.get(uri) {
                if events.open_change.is_some() {
                    panic!("should see no changes after open");
                }
            } else {
                file_event_map.insert(uri.clone(), FileEvents::default());
            }
            let events = file_event_map
                .get_mut(uri)
                .expect("events were stored above");

            if !result.includes_watch_change_outside_node_modules
                && change.kind.is_watch_kind()
                && !uri.0.contains("/node_modules/")
            {
                result.includes_watch_change_outside_node_modules = true;
            }

            match change.kind {
                FileChangeKind::OPEN => {
                    if events.close_change.is_some() {
                        events.close_change = None;
                    }
                    events.open_change = Some(change);
                    events.watch_changed = false;
                    events.changes = Vec::new();
                    events.saved = false;
                    events.created = false;
                    events.deleted = false;
                }
                FileChangeKind::CLOSE => {
                    events.close_change = Some(change);
                    events.changes = Vec::new();
                    events.saved = false;
                    events.watch_changed = false;
                }
                FileChangeKind::CHANGE => {
                    if events.close_change.is_some() {
                        panic!("should see no changes after close");
                    }
                    events.changes.push(change);
                    events.saved = false;
                    events.watch_changed = false;
                }
                FileChangeKind::SAVE => {
                    events.saved = true;
                }
                FileChangeKind::WATCH_CREATE => {
                    if events.deleted {
                        // Delete followed by create becomes a change
                        events.deleted = false;
                        events.watch_changed = true;
                    } else {
                        events.created = true;
                    }
                }
                FileChangeKind::WATCH_CHANGE => {
                    if !events.created {
                        events.watch_changed = true;
                        events.saved = false;
                    }
                }
                FileChangeKind::WATCH_DELETE => {
                    events.watch_changed = false;
                    events.saved = false;
                    // Delete after create cancels out
                    if events.created {
                        events.created = false;
                    } else {
                        events.deleted = true;
                    }
                }
                _ => {}
            }
        }

        // Process deduplicated events per file
        for (uri, events) in &file_event_map {
            let path = uri.path(self.fs.use_case_sensitive_file_names());
            let mut o: Option<Rc<Overlay>> = new_overlays.get(&path).cloned();

            if let Some(open_change) = events.open_change {
                if !result.opened.0.is_empty() || !result.reopened.0.is_empty() {
                    panic!("can only process one file open event at a time");
                }
                if o.as_ref()
                    .is_some_and(|o| o.file_base.content != open_change.content)
                {
                    result.changed.insert(uri.clone());
                } else if o.is_none() {
                    result.opened = uri.clone();
                } else {
                    result.reopened = uri.clone();
                }
                let mut script_kind =
                    lsconv::language_kind_to_script_kind(&open_change.language_kind);
                if script_kind == ScriptKind::UNKNOWN {
                    script_kind = get_script_kind_from_file_name(&uri.file_name());
                }
                new_overlays.insert(
                    path,
                    Rc::new(new_overlay(
                        &uri.file_name(),
                        open_change.content.clone(),
                        open_change.version,
                        script_kind,
                    )),
                );
                continue;
            }

            if events.close_change.is_some() {
                if o.is_none() {
                    panic!("overlay not found for closed file: {}", uri.0);
                }
                result.closed.insert(uri.clone());
                new_overlays.shift_remove(&path);
                o = None;
            }

            if events.watch_changed {
                if let Some(cur) = o.clone() {
                    if !events.saved {
                        let (matches_disk_text, _) = cur.compute_matches_disk_text(&*self.fs);
                        if matches_disk_text != cur.matches_disk_text.get() {
                            let next = new_overlay(
                                &cur.file_base.file_name,
                                cur.file_base.content.clone(),
                                cur.version.get(),
                                cur.kind,
                            );
                            next.matches_disk_text.set(matches_disk_text);
                            let next = Rc::new(next);
                            new_overlays.insert(path.clone(), next.clone());
                            o = Some(next);
                        }
                    }
                } else {
                    result.changed.insert(uri.clone());
                }
            }

            if !events.changes.is_empty() {
                result.changed.insert(uri.clone());
                if o.is_none() {
                    panic!("overlay not found for changed file: {}", uri.0);
                }
                // PORT: the Go line map closure captures the variable `o`,
                // which the loop below reassigns; `o_cell` is that variable.
                let o_cell: Rc<RefCell<Option<Rc<Overlay>>>> = Rc::new(RefCell::new(o.clone()));
                for change in &events.changes {
                    let o_for_line_map = o_cell.clone();
                    let converters = lsconv::new_converters(
                        self.position_encoding.clone(),
                        move |_file_name: &str| -> Option<Rc<lsconv::LSPLineMap>> {
                            Some(
                                o_for_line_map
                                    .borrow()
                                    .as_ref()
                                    .expect("invalid memory address or nil pointer dereference")
                                    .file_base
                                    .lsp_line_map(),
                            )
                        },
                    );
                    for text_change in &change.changes {
                        let cur = o_cell
                            .borrow()
                            .clone()
                            .expect("invalid memory address or nil pointer dereference");
                        if let Some(partial_change) = &text_change.partial {
                            let new_content = converters
                                .from_lsp_text_change(&*cur, partial_change)
                                .apply_to(&cur.file_base.content);
                            *o_cell.borrow_mut() = Some(Rc::new(new_overlay(
                                &cur.file_base.file_name,
                                new_content,
                                change.version,
                                cur.kind,
                            )));
                        } else if let Some(whole_change) = &text_change.whole_document {
                            *o_cell.borrow_mut() = Some(Rc::new(new_overlay(
                                &cur.file_base.file_name,
                                whole_change.text.clone(),
                                change.version,
                                cur.kind,
                            )));
                        }
                    }
                    if !change.changes.is_empty() {
                        let cur = o_cell
                            .borrow()
                            .clone()
                            .expect("invalid memory address or nil pointer dereference");
                        cur.version.set(change.version);
                        cur.file_base
                            .hash
                            .set(xxh3_128(cur.file_base.content.as_bytes()));
                        cur.matches_disk_text.set(false);
                        new_overlays.insert(path.clone(), cur);
                    }
                }
                o = o_cell.borrow().clone();
            }

            if events.saved {
                if let Some(cur) = o.clone() {
                    let next = new_overlay(
                        &cur.file_base.file_name,
                        cur.file_base.content.clone(),
                        cur.version.get(),
                        cur.kind,
                    );
                    next.matches_disk_text.set(true);
                    let next = Rc::new(next);
                    new_overlays.insert(path.clone(), next.clone());
                    o = Some(next);
                } else if !events.watch_changed {
                    // File was saved but never opened via didOpen; treat as a disk change.
                    result.changed.insert(uri.clone());
                }
            }

            if events.created && o.is_none() {
                result.created.insert(uri.clone());
            }

            if events.deleted && o.is_none() {
                result.deleted.insert(uri.clone());
            }
        }

        *self.overlays.borrow_mut() = new_overlays.clone();
        (result, new_overlays)
    }
}
