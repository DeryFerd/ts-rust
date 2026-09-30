//! Go `internal/project/snapshothost.go` (ts#64163).
//!
//! PORT: one thread (project/dirty/interfaces.rs). Go `*SnapshotHost` is
//! `Rc<SnapshotHost>`: every snapshot keeps its host so `Deref` can release
//! the host's caches. The Go `atomic.Uint64` snapshot id is a `Cell`. Go
//! `Session` embeds `*SnapshotHost`; the Rust `Session` holds it in
//! `snapshot_host` and derefs to it (session.rs).

use crate::project::prelude::*;

use crate::contentmapper;
use crate::frontend::core_ext::ProjectReference;
use std::cell::Cell;

// Go: project/snapshothost.go:19 SnapshotHost
// SnapshotHost owns the services shared by a collection of immutable snapshots.
pub struct SnapshotHost {
    pub options: Rc<SessionOptions>,
    pub to_path: Rc<dyn Fn(&str) -> tspath::Path>,
    pub fs: Rc<dyn vfs::Fs>,

    pub parse_cache: Rc<ParseCache>,
    pub content_mapped_parse_cache: Rc<ContentMappedParseCache>,
    pub extended_config_cache: Rc<ExtendedConfigCache>,
    pub program_counter: Rc<ProgramCounter>,
    pub content_mapper_host: Option<Rc<dyn contentmapper::Host>>,

    pub snapshot_id: Cell<u64>,

    // PORT: the parse cache references that auto-import registry clones
    // keep after the clone, one per path (see
    // `AutoImportRegistryCloneHost::dispose`). No Go counterpart. It moved
    // from `Session` with the caches it belongs to.
    pub auto_import_parse_keys: Rc<AutoImportParseKeys>,
}

/// Go `logging.Logger` as the session logger argument of `Snapshot.Clone`,
/// `cloneForProgram` and `CloneSnapshotWithAutoImports`.
// PORT: Go passes the session's logger (a non-nil interface, also for the nop
// logger) or nil. `None` is the Go nil interface; `Some(logger)` is the
// session logger, which is itself `None` for the nop logger (see
// `logging::new_nop_logger`).
pub type SessionLogger<'a> = Option<&'a Option<Rc<dyn logging::Logger>>>;

impl SnapshotHost {
    // Go: project/snapshothost.go:33 SnapshotHost.nextSnapshotID
    pub fn next_snapshot_id(&self) -> u64 {
        // Go: s.snapshotID.Add(1)
        let id = self.snapshot_id.get() + 1;
        self.snapshot_id.set(id);
        id
    }
}

// Go: project/snapshothost.go:37 NewSnapshotHost
pub fn new_snapshot_host(init: &SessionInit) -> Rc<SnapshotHost> {
    let current_directory = init.options.current_directory.clone();
    let use_case_sensitive_file_names = init.fs.use_case_sensitive_file_names();
    let to_path: Rc<dyn Fn(&str) -> tspath::Path> = Rc::new(move |file_name: &str| {
        tspath::to_path(file_name, &current_directory, use_case_sensitive_file_names)
    });
    let mut parse_cache = init.parse_cache.clone();
    if parse_cache.is_none() {
        parse_cache = Some(new_parse_cache(RefCountCacheOptions::default()));
    }
    let mut content_mapped_parse_cache = init.content_mapped_parse_cache.clone();
    if content_mapped_parse_cache.is_none() {
        content_mapped_parse_cache = Some(new_content_mapped_parse_cache(
            RefCountCacheOptions::default(),
        ));
    }

    Rc::new(SnapshotHost {
        options: init.options.clone(),
        to_path,
        fs: init.fs.clone(),
        parse_cache: parse_cache.expect("parse cache is set above"),
        content_mapped_parse_cache: content_mapped_parse_cache
            .expect("content mapped parse cache is set above"),
        extended_config_cache: new_extended_config_cache(),
        program_counter: Rc::new(ProgramCounter::default()),
        content_mapper_host: new_content_mapper_host(init),
        snapshot_id: Cell::new(0),
        auto_import_parse_keys: Rc::new(RefCell::new(FxHashMap::default())),
    })
}

impl SnapshotHost {
    // Go: project/snapshothost.go:64 NewStandaloneRootSnapshot
    // NewStandaloneRootSnapshot creates the compatibility root for a standalone API session.
    pub fn new_standalone_root_snapshot(self: &Rc<Self>) -> Rc<Snapshot> {
        self.new_root_snapshot(0, false)
    }

    // Go: project/snapshothost.go:69 RetainSnapshot
    // RetainSnapshot adds a reference to a snapshot owned by this host.
    pub fn retain_snapshot(&self, snapshot: &Snapshot) {
        snapshot.ref_();
    }

    // Go: project/snapshothost.go:75 CloneSnapshot
    // CloneSnapshot derives a snapshot from baseSnapshot without adopting it as any
    // canonical session state or performing session side effects.
    // PORT: Go returns `(*Snapshot, error)` and returns the snapshot also with
    // an error; the port returns both values.
    pub fn clone_snapshot(
        &self,
        ctx: &Context,
        base_snapshot: &Rc<Snapshot>,
        file_changes: FileChangeSummary,
        api_request: Option<APISnapshotRequest>,
    ) -> (Rc<Snapshot>, Option<GoError>) {
        let snapshot = self.update(
            ctx,
            base_snapshot,
            SnapshotChange {
                api_request,
                file_changes,
                ..Default::default()
            },
        );
        let api_error = snapshot.api_error.clone();
        (snapshot, api_error)
    }

    // Go: project/snapshothost.go:90 SnapshotHost.update
    // update derives a snapshot from baseSnapshot without adopting it as any
    // canonical session state or performing session side effects.
    pub fn update(
        &self,
        ctx: &Context,
        base_snapshot: &Rc<Snapshot>,
        change: SnapshotChange,
    ) -> Rc<Snapshot> {
        base_snapshot.clone_(ctx, change, &base_snapshot.fs.overlays, None)
    }

    // Go: project/snapshothost.go:95 CloneSnapshotWithTemporaryFile
    // CloneSnapshotWithTemporaryFile derives a snapshot with a temporary file content override.
    pub fn clone_snapshot_with_temporary_file(
        &self,
        ctx: &Context,
        base_snapshot: &Rc<Snapshot>,
        uri: &lsproto::DocumentUri,
        new_text: String,
    ) -> Result<Rc<Snapshot>, GoError> {
        base_snapshot.clone_with_temporary_file(ctx, uri, new_text)
    }

    // Go: project/snapshothost.go:106 CloneSnapshotForProgram
    // CloneSnapshotForProgram derives an isolated snapshot containing one synthetic
    // project. The base snapshot is not adopted as canonical state.
    #[allow(clippy::too_many_arguments)]
    pub fn clone_snapshot_for_program(
        &self,
        ctx: &Context,
        base_snapshot: &Rc<Snapshot>,
        root_file_names: &[String],
        options: Option<Rc<CompilerOptions>>,
        project_references: Option<Vec<ProjectReference>>,
        config_file_parsing_diagnostics: Vec<Diagnostic>,
        old_project: Option<&Rc<RefCell<Project>>>,
        file_changes: FileChangeSummary,
    ) -> Rc<Snapshot> {
        base_snapshot.clone_for_program(
            ctx,
            root_file_names,
            options,
            project_references,
            config_file_parsing_diagnostics,
            old_project,
            file_changes,
            None,
        )
    }

    // Go: project/snapshothost.go:130 CloneSnapshotWithAutoImports
    // CloneSnapshotWithAutoImports derives a snapshot with auto-import preparation without
    // adopting the clone in the background.
    pub fn clone_snapshot_with_auto_imports(
        &self,
        ctx: &Context,
        base_snapshot: &Rc<Snapshot>,
        uri: &lsproto::DocumentUri,
        logger: SessionLogger<'_>,
    ) -> Rc<Snapshot> {
        let change = SnapshotChange {
            reason: UpdateReason::REQUESTED_LANGUAGE_SERVICE_WITH_AUTO_IMPORTS,
            resource_request: ResourceRequest {
                documents: vec![uri.clone()],
                auto_imports: uri.clone(),
                ..Default::default()
            },
            ..Default::default()
        };
        base_snapshot.clone_(ctx, change, &base_snapshot.fs.overlays, logger)
    }

    // Go: project/snapshothost.go:141 SnapshotHost.newRootSnapshot
    pub fn new_root_snapshot(
        self: &Rc<Self>,
        id: u64,
        relative_pattern_support: bool,
    ) -> Rc<Snapshot> {
        self.new_snapshot(
            id,
            Rc::new(SnapshotFS {
                to_path: self.to_path.clone(),
                fs: self.fs.clone(),
                overlays: IndexMap::default(),
                overlay_directories: FxHashMap::default(),
                disk_files: Rc::new(FxHashMap::default()),
                disk_directories: Rc::new(FxHashMap::default()),
                read_files: RefCell::new(FxHashMap::default()),
                node_modules_realpath_aliases: Rc::new(FxHashMap::default()),
            }),
            Rc::new(ConfigFileRegistry::default()),
            None,
            lsutil::new_default_user_preferences(),
            None,
            Some(new_watched_files::<FxHashMap<tspath::Path, String>>(
                "auto-import",
                lsproto::WatchKind(
                    lsproto::WatchKind::CREATE.0
                        | lsproto::WatchKind::CHANGE.0
                        | lsproto::WatchKind::DELETE.0,
                ),
                relative_pattern_support,
                Rc::new(|node_modules_dirs: &FxHashMap<tspath::Path, String>| {
                    let mut patterns: Vec<String> = Vec::with_capacity(node_modules_dirs.len());
                    // PORT: Go map order is random; the patterns are sorted below.
                    for dir in node_modules_dirs.values() {
                        patterns.push(get_recursive_glob_pattern(dir));
                    }
                    patterns.sort();
                    PatternsAndIgnored {
                        patterns_inside_workspace: patterns,
                        ..Default::default()
                    }
                }),
            )),
        )
    }

    // Go: project/snapshothost.go:170 SnapshotHost.FS
    pub fn fs(&self) -> Rc<dyn vfs::Fs> {
        self.fs.clone()
    }

    // Go: project/snapshothost.go:174 SnapshotHost.GetCurrentDirectory
    pub fn get_current_directory(&self) -> String {
        self.options.current_directory.clone()
    }

    // Go: project/snapshothost.go:178 SnapshotHost.Close
    pub fn close(&self) {
        if let Some(content_mapper_host) = &self.content_mapper_host {
            let _ = content_mapper_host.close();
        }
    }
}
