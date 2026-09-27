//! Go `internal/project/snapshot.go`.
//!
//! PORT: one thread (project/dirty/interfaces.rs). Go `*Snapshot` is
//! `Rc<Snapshot>`; the Go `atomic.Int32` ref count is a manual `Cell<i32>`
//! because `dispose` releases parse cache and extended config cache
//! entries. Go `*Project` is `Rc<RefCell<Project>>`. Go
//! `collections.Set` is `FxHashSet`. Log text uses `{:?}` for Go `%v`
//! (log only).

use crate::project::prelude::*;

use std::cell::Cell;
use std::panic::AssertUnwindSafe;
use std::time::Instant;

const NIL_DEREF: &str = "invalid memory address or nil pointer dereference";

// Go: project/snapshot.go:26 Snapshot
pub struct Snapshot {
    pub id: u64,
    pub parent_id: u64,
    pub ref_count: Cell<i32>,

    // Session options are immutable for the server lifetime,
    // so can be a pointer.
    pub session_options: Rc<SessionOptions>,
    pub to_path: Rc<dyn Fn(&str) -> tspath::Path>,
    pub converters: Rc<lsconv::Converters>,

    // Immutable state, cloned between snapshots
    pub fs: Rc<SnapshotFS>,
    pub project_collection: Rc<ProjectCollection>,
    // PORT: Go can hold nil here only inside Clone, between NewSnapshot and
    // the assignment right after it; the port passes the final registry to
    // NewSnapshot, so the field is never nil.
    pub config_file_registry: Rc<ConfigFileRegistry>,
    pub auto_imports: Option<Rc<autoimport::Registry>>,
    pub auto_imports_watch: Option<Rc<WatchedFiles<FxHashMap<tspath::Path, String>>>>,
    pub compiler_options_for_inferred_projects: Option<Rc<CompilerOptions>>,
    pub user_preferences: lsutil::UserPreferences,

    pub builder_logs: Option<Rc<logging::LogTree>>,
    pub api_error: Option<GoError>,
}

// Go: project/snapshot.go:97 (*Snapshot).LSPLineMap, as a function of the
// snapshot's file system.
// PORT: Go gives NewConverters the method value `s.LSPLineMap`, which keeps
// the snapshot alive. `s.fs` never changes after NewSnapshot, so the port's
// closure holds `s.fs` instead (no `Rc` cycle, same results).
fn lsp_line_map_of(fs: &SnapshotFS, file_name: &str) -> Option<Rc<lsconv::LSPLineMap>> {
    if let Some(file) = fs.get_file(file_name) {
        return Some(file.lsp_line_map());
    }
    None
}

// Go: project/snapshot.go:52 NewSnapshot
// NewSnapshot initializes a snapshot with refCount 1.
// The caller is responsible for calling Deref when done.
#[allow(clippy::too_many_arguments)]
pub fn new_snapshot(
    id: u64,
    fs: Rc<SnapshotFS>,
    session_options: Rc<SessionOptions>,
    config_file_registry: Rc<ConfigFileRegistry>,
    compiler_options_for_inferred_projects: Option<Rc<CompilerOptions>>,
    user_preferences: lsutil::UserPreferences,
    auto_imports: Option<Rc<autoimport::Registry>>,
    auto_imports_watch: Option<Rc<WatchedFiles<FxHashMap<tspath::Path, String>>>>,
    to_path: Rc<dyn Fn(&str) -> tspath::Path>,
) -> Rc<Snapshot> {
    let line_map_fs = fs.clone();
    let converters = lsconv::new_converters(
        session_options.position_encoding.clone(),
        move |file_name: &str| lsp_line_map_of(&line_map_fs, file_name),
    );
    let project_collection = Rc::new(ProjectCollection {
        to_path: to_path.clone(),
        config_file_registry: None,
        file_default_projects: FxHashMap::default(),
        configured_projects: FxHashMap::default(),
        open_files: open_file_paths(&fs.overlays),
        inferred_project: None,
        api_opened_projects: FxHashSet::default(),
        open_configured_projects: std::cell::OnceCell::new(),
    });
    Rc::new(Snapshot {
        id,
        parent_id: 0,
        // Go: s.refCount.Store(1)
        ref_count: Cell::new(1),

        session_options,
        to_path,
        converters,

        fs,
        config_file_registry,
        project_collection,
        compiler_options_for_inferred_projects,
        user_preferences,
        auto_imports,
        auto_imports_watch,

        builder_logs: None,
        api_error: None,
    })
}

impl Snapshot {
    // Go: project/snapshot.go:82 GetDefaultProject
    pub fn get_default_project(&self, uri: &lsproto::DocumentUri) -> Option<Rc<RefCell<Project>>> {
        self.project_collection
            .get_default_project(&uri.path(self.use_case_sensitive_file_names()))
    }

    // Go: project/snapshot.go:86 GetProjectsContainingFile
    pub fn get_projects_containing_file(
        &self,
        uri: &lsproto::DocumentUri,
    ) -> Vec<Rc<dyn ls::Project>> {
        let file_name = uri.file_name();
        let path = (self.to_path)(&file_name);
        // TODO!! sheetal may be change this to handle symlinks!!
        self.project_collection.get_projects_containing_file(&path)
    }

    // Go: project/snapshot.go:93 GetFile
    pub fn get_file(&self, file_name: &str) -> Option<Rc<dyn FileHandle>> {
        self.fs.get_file(file_name)
    }

    // Go: project/snapshot.go:97 LSPLineMap
    pub fn lsp_line_map(&self, file_name: &str) -> Option<Rc<lsconv::LSPLineMap>> {
        if let Some(file) = self.fs.get_file(file_name) {
            return Some(file.lsp_line_map());
        }
        None
    }

    // Go: project/snapshot.go:104 GetECMALineInfo
    pub fn get_ecma_line_info(
        &self,
        file_name: &str,
    ) -> Option<Rc<sourcemap::lineinfo::ECMALineInfo>> {
        if let Some(file) = self.fs.get_file(file_name) {
            return Some(file.ecma_line_info());
        }
        None
    }

    // Go: project/snapshot.go:111 GetPreferences
    pub fn get_preferences(&self, _active_file: &str) -> lsutil::UserPreferences {
        self.user_preferences.clone()
    }

    // Go: project/snapshot.go:115 UserPreferences
    pub fn user_preferences(&self) -> lsutil::UserPreferences {
        self.user_preferences.clone()
    }

    // Go: project/snapshot.go:119 Converters
    pub fn converters(&self) -> Rc<lsconv::Converters> {
        self.converters.clone()
    }

    // Go: project/snapshot.go:123 AutoImportRegistry
    pub fn auto_import_registry(&self) -> Option<Rc<autoimport::Registry>> {
        self.auto_imports.clone()
    }

    // Go: project/snapshot.go:127 ID
    pub fn id(&self) -> u64 {
        self.id
    }

    // Go: project/snapshot.go:131 UseCaseSensitiveFileNames
    pub fn use_case_sensitive_file_names(&self) -> bool {
        self.fs.fs.use_case_sensitive_file_names()
    }

    // Go: project/snapshot.go:135 ReadFile
    pub fn read_file(&self, file_name: &str) -> (String, bool) {
        let Some(handle) = self.get_file(file_name) else {
            return (String::new(), false);
        };
        (handle.content(), true)
    }

    // Go: project/snapshot.go:143 DirectoryExists
    pub fn directory_exists(&self, path: &str) -> bool {
        self.fs.fs.directory_exists(path)
    }

    // Go: project/snapshot.go:147 FileExists
    pub fn file_exists(&self, path: &str) -> bool {
        self.fs.fs.file_exists(path)
    }

    // Go: project/snapshot.go:151 GetDirectories
    pub fn get_directories(&self, path: &str) -> Vec<String> {
        self.fs.fs.get_accessible_entries(path).directories
    }

    // Go: project/snapshot.go:155 ReadDirectory
    pub fn read_directory(
        &self,
        current_dir: &str,
        path: &str,
        extensions: &[String],
        excludes: &[String],
        includes: &[String],
        depth: i32,
    ) -> Vec<String> {
        vfs::vfsmatch::read_directory(
            &*self.fs.fs,
            current_dir,
            path,
            extensions,
            excludes,
            includes,
            depth,
        )
    }
}

// Go: project/snapshot.go:13 (import of ls; Snapshot is the ls.Host of a
// language service)
impl ls::Host for Snapshot {
    fn use_case_sensitive_file_names(&self) -> bool {
        Snapshot::use_case_sensitive_file_names(self)
    }

    fn read_file(&self, path: &str) -> (String, bool) {
        Snapshot::read_file(self, path)
    }

    fn converters(&self) -> Rc<lsconv::Converters> {
        Snapshot::converters(self)
    }

    fn get_preferences(&self, active_file: &str) -> lsutil::UserPreferences {
        Snapshot::get_preferences(self, active_file)
    }

    fn get_ecma_line_info(&self, file_name: &str) -> Option<Rc<sourcemap::lineinfo::ECMALineInfo>> {
        Snapshot::get_ecma_line_info(self, file_name)
    }

    fn auto_import_registry(&self) -> Option<Rc<autoimport::Registry>> {
        Snapshot::auto_import_registry(self)
    }

    fn read_directory(
        &self,
        current_dir: &str,
        path: &str,
        extensions: &[String],
        excludes: &[String],
        includes: &[String],
        depth: i32,
    ) -> Vec<String> {
        Snapshot::read_directory(
            self,
            current_dir,
            path,
            extensions,
            excludes,
            includes,
            depth,
        )
    }

    fn get_directories(&self, path: &str) -> Vec<String> {
        Snapshot::get_directories(self, path)
    }

    fn directory_exists(&self, path: &str) -> bool {
        Snapshot::directory_exists(self, path)
    }

    fn file_exists(&self, path: &str) -> bool {
        Snapshot::file_exists(self, path)
    }
}

// Go: project/snapshot.go:159 APISnapshotRequest
// PORT: Go `*collections.Set[T]` is `Option<FxHashSet<T>>` (nil is `None`).
#[derive(Clone, Debug, Default)]
pub struct APISnapshotRequest {
    pub open_projects: Option<FxHashSet<String>>,
    pub close_projects: Option<FxHashSet<tspath::Path>>,
}

// Go: project/snapshot.go:164 ProjectTreeRequest
#[derive(Clone, Debug, Default)]
pub struct ProjectTreeRequest {
    // If null, all project trees need to be loaded, otherwise only those that are referenced
    pub referenced_projects: Option<FxHashSet<tspath::Path>>,
}

impl ProjectTreeRequest {
    // Go: project/snapshot.go:169 IsAllProjects
    pub fn is_all_projects(&self) -> bool {
        self.referenced_projects.is_none()
    }

    // Go: project/snapshot.go:173 IsProjectReferenced
    // PORT: Go `Set.Has` returns false on a nil set.
    pub fn is_project_referenced(&self, project_id: &tspath::Path) -> bool {
        self.referenced_projects
            .as_ref()
            .is_some_and(|referenced_projects| referenced_projects.contains(project_id))
    }

    // Go: project/snapshot.go:177 Projects
    // PORT: a Go nil slice is empty. Go map order is random; FxHashSet order here.
    pub fn projects(&self) -> Vec<tspath::Path> {
        let Some(referenced_projects) = &self.referenced_projects else {
            return Vec::new();
        };
        referenced_projects.iter().cloned().collect()
    }
}

// Go: project/snapshot.go:184 ResourceRequest
// PORT: Go `*ProjectTreeRequest` is `Option<ProjectTreeRequest>` (nil is `None`).
#[derive(Clone, Debug, Default)]
pub struct ResourceRequest {
    // Documents are URIs that were requested by the client.
    // The new snapshot should ensure projects for these URIs have loaded programs.
    pub documents: Vec<lsproto::DocumentUri>,
    // ConfiguredProjectDocuments are URIs for which configured projects should be loaded
    // (if disableSolutionSearching/disableReferencedProjectLoad settings allow),
    // but no inferred project should be created if no configured project is found.
    // This is used by cross-project operations like find-all-references.
    pub configured_project_documents: Vec<lsproto::DocumentUri>,
    // Update requested Projects.
    // this is used when we want to get LS and from all the Projects the file can be part of
    pub projects: Vec<tspath::Path>,
    // Update and ensure project trees that reference the projects
    // This is used to compute the solution and project tree so that
    // we can find references across all the projects in the solution irrespective of which project is open
    pub project_tree: Option<ProjectTreeRequest>,
    // AutoImports is the document URI for which auto imports should be prepared.
    pub auto_imports: lsproto::DocumentUri,
}

// Go: project/snapshot.go:204 SnapshotChange
// PORT: Go embeds `ResourceRequest`; here it is the field
// `resource_request`. Go `*core.CompilerOptions` is
// `Option<Rc<CompilerOptions>>`, Go `*lsutil.UserPreferences` is
// `Option<lsutil::UserPreferences>`, Go `*APISnapshotRequest` is
// `Option<APISnapshotRequest>` (nil is `None`).
#[derive(Clone, Default)]
pub struct SnapshotChange {
    pub resource_request: ResourceRequest,
    pub reason: UpdateReason,
    // fileChanges are the changes that have occurred since the last snapshot.
    pub file_changes: FileChangeSummary,
    // compilerOptionsForInferredProjects is the compiler options to use for inferred projects.
    // It should only be set the value in the next snapshot should be changed. If nil, the
    // value from the previous snapshot will be copied to the new snapshot.
    pub compiler_options_for_inferred_projects: Option<Rc<CompilerOptions>>,
    pub new_config: Option<lsutil::UserPreferences>,
    // ataChanges contains ATA-related changes to apply to projects in the new snapshot.
    pub ata_changes: FxHashMap<tspath::Path, Rc<ATAStateChange>>,
    pub api_request: Option<APISnapshotRequest>,
    // cleanDiskCache triggers cleaning of cached disk files not referenced by any open project.
    pub clean_disk_cache: bool,
}

// Go: project/snapshot.go:222 ATAStateChange
// ATAStateChange represents a change to a project's ATA state.
// PORT: Go `*ata.TypingsInfo` is `Option<Rc<ata::TypingsInfo>>`.
#[derive(Clone, Default)]
pub struct ATAStateChange {
    pub project_id: tspath::Path,
    // TypingsInfo is the new typings info for the project.
    pub typings_info: Option<Rc<ata::TypingsInfo>>,
    // TypingsFiles is the new list of typing files for the project.
    pub typings_files: Vec<String>,
    // TypingsFilesToWatch is the new list of typing files to watch for changes.
    pub typings_files_to_watch: Vec<String>,
    pub logs: Option<Rc<logging::LogTree>>,
}

/// Go `%v` of a slice in log text: `[a b c]`.
fn fmt_list<T: std::fmt::Display>(items: &[T]) -> String {
    let parts: Vec<String> = items.iter().map(|item| item.to_string()).collect();
    format!("[{}]", parts.join(" "))
}

/// Go `%v` of a `[]lsproto.DocumentUri` in log text.
fn fmt_uris(uris: &[lsproto::DocumentUri]) -> String {
    let parts: Vec<&str> = uris.iter().map(|uri| uri.0.as_str()).collect();
    fmt_list(&parts)
}

impl Snapshot {
    // Go: project/snapshot.go:233 Clone
    // PORT: Go `Clone` is `clone_` (Rust `Clone::clone` copies a value).
    // The deferred `recover()` is `catch_unwind` around the body
    // (`clone_body`); the panic is logged and raised again, as in Go.
    pub fn clone_(
        &self,
        ctx: &Context,
        change: SnapshotChange,
        overlays: &IndexMap<tspath::Path, Rc<Overlay>>,
        session: &Session,
    ) -> Rc<Snapshot> {
        let mut logger: Option<Rc<logging::LogTree>> = None;

        // Print in-progress logs immediately if cloning fails
        if session.options.logging_enabled {
            let result = std::panic::catch_unwind(AssertUnwindSafe(|| {
                self.clone_body(ctx, change, overlays, session, &mut logger)
            }));
            return match result {
                Ok(new_snapshot) => new_snapshot,
                Err(r) => {
                    session.logger.log(&logger.string());
                    std::panic::resume_unwind(r)
                }
            };
        }

        self.clone_body(ctx, change, overlays, session, &mut logger)
    }

    // Go: project/snapshot.go:233 Clone (the body after the deferred recover)
    // PORT: split out of `clone_` so the recover can wrap it; `logger` is
    // the Go local that the deferred function reads.
    fn clone_body(
        &self,
        ctx: &Context,
        change: SnapshotChange,
        overlays: &IndexMap<tspath::Path, Rc<Overlay>>,
        session: &Session,
        logger_out: &mut Option<Rc<logging::LogTree>>,
    ) -> Rc<Snapshot> {
        let mut change = change;

        if session.options.logging_enabled {
            *logger_out = logging::new_log_tree(&format!("Cloning snapshot {}", self.id));
            let logger = logger_out.clone();
            let get_details = || -> String {
                let mut details = String::new();
                if !change.resource_request.documents.is_empty() {
                    details += &format!(
                        " Documents: {}",
                        fmt_uris(&change.resource_request.documents)
                    );
                }
                if !change
                    .resource_request
                    .configured_project_documents
                    .is_empty()
                {
                    details += &format!(
                        " ConfiguredProjectDocuments: {}",
                        fmt_uris(&change.resource_request.configured_project_documents)
                    );
                }
                if !change.resource_request.projects.is_empty() {
                    details +=
                        &format!(" Projects: {}", fmt_list(&change.resource_request.projects));
                }
                if let Some(project_tree) = &change.resource_request.project_tree {
                    details += &format!(" ProjectTree: {}", fmt_list(&project_tree.projects()));
                }
                details
            };
            // PORT: Go `switch change.reason`; an `if` chain needs only `PartialEq`.
            let reason = &change.reason;
            if *reason == UpdateReason::DID_OPEN_FILE {
                logger.logf(&format!(
                    "Reason: DidOpenFile - {}",
                    change.file_changes.opened.0
                ));
            } else if *reason == UpdateReason::DID_CLOSE_FILE {
                logger.logf(&format!(
                    "Reason: DidCloseFile - {:?}",
                    change.file_changes.closed
                ));
            } else if *reason == UpdateReason::DID_CHANGE_COMPILER_OPTIONS_FOR_INFERRED_PROJECTS {
                logger.logf("Reason: DidChangeCompilerOptionsForInferredProjects");
            } else if *reason == UpdateReason::REQUESTED_LANGUAGE_SERVICE_PENDING_CHANGES {
                logger.logf(&format!(
                    "Reason: RequestedLanguageService (pending file changes) - {}",
                    get_details()
                ));
            } else if *reason == UpdateReason::REQUESTED_LANGUAGE_SERVICE_PROJECT_NOT_LOADED {
                logger.logf(&format!(
                    "Reason: RequestedLanguageService (project not loaded) - {}",
                    get_details()
                ));
            } else if *reason == UpdateReason::REQUESTED_LANGUAGE_SERVICE_FOR_FILE_NOT_OPEN {
                logger.logf(&format!(
                    "Reason: RequestedLanguageService (file not open) - {}",
                    get_details()
                ));
            } else if *reason == UpdateReason::REQUESTED_LANGUAGE_SERVICE_PROJECT_DIRTY {
                logger.logf(&format!(
                    "Reason: RequestedLanguageService (project dirty) - {}",
                    get_details()
                ));
            } else if *reason == UpdateReason::REQUESTED_LOAD_PROJECT_TREE {
                logger.logf(&format!(
                    "Reason: RequestedLoadProjectTree - {}",
                    get_details()
                ));
            } else if *reason == UpdateReason::IDLE_CLEAN_DISK_CACHE {
                logger.logf("Reason: IdleCleanDiskCache");
            }
        }
        let logger = logger_out.clone();

        let start = Instant::now();
        let fs = new_snapshot_fs_builder(
            session.fs.fs.clone(),
            self.fs.overlays.clone(),
            overlays.clone(),
            self.fs.disk_files.clone(),
            self.fs.disk_directories.clone(),
            self.fs.node_modules_realpath_aliases.clone(),
            session.options.position_encoding.clone(),
            self.to_path.clone(),
        );
        if change.file_changes.has_excessive_watch_events() {
            let invalidate_start = Instant::now();
            if change.file_changes.invalidate_all {
                fs.invalidate_cache();
                logger.logf(&format!(
                    "InvalidateAll: invalidated file cache in {:?}",
                    invalidate_start.elapsed()
                ));
            } else if !fs.watch_changes_overlap_cache(&change.file_changes) {
                // All watch changes/deletes are files we haven't seen; should be irrelevant to us (probably an external tool's build or something)
                change.file_changes.changed = FxHashSet::default();
                change.file_changes.deleted = FxHashSet::default();
            } else if change
                .file_changes
                .includes_watch_change_outside_node_modules
            {
                fs.invalidate_cache();
                logger.logf(&format!(
                    "Excessive watch changes detected, invalidated file cache in {:?}",
                    invalidate_start.elapsed()
                ));
            } else {
                fs.invalidate_node_modules_cache();
                logger.logf(&format!(
                    "npm install detected, invalidated node_modules cache in {:?}",
                    invalidate_start.elapsed()
                ));
            }
        } else {
            change.file_changes = fs.expand_and_filter_watch_events(change.file_changes);
            change.file_changes = self.fs.expand_realpath_aliases(change.file_changes);
            fs.mark_dirty_files(&change.file_changes);
            change.file_changes = fs.convert_open_and_close_to_changes(change.file_changes);
        }

        let mut compiler_options_for_inferred_projects =
            self.compiler_options_for_inferred_projects.clone();
        if change.compiler_options_for_inferred_projects.is_some() {
            // !!! mark inferred projects as dirty?
            compiler_options_for_inferred_projects =
                change.compiler_options_for_inferred_projects.clone();
        }

        // Compute effective customConfigFileName from user preferences
        let mut custom_config_file_name = self.config_file_registry.custom_config_file_name.clone();
        if let Some(new_config) = &change.new_config {
            custom_config_file_name = new_config.custom_config_file_name.clone();
        }

        // Go: session.snapshotID.Add(1)
        let new_snapshot_id = session.snapshot_id.get() + 1;
        session.snapshot_id.set(new_snapshot_id);
        let project_collection_builder = new_project_collection_builder(
            ctx,
            new_snapshot_id,
            fs.clone(),
            self.project_collection.clone(),
            self.config_file_registry.clone(),
            &self.project_collection.api_opened_projects,
            compiler_options_for_inferred_projects.clone(),
            self.session_options.clone(),
            &custom_config_file_name,
            session.parse_cache.clone(),
            session.extended_config_cache.clone(),
            session.client.clone(),
        );

        if !change.ata_changes.is_empty() {
            project_collection_builder
                .did_update_ata_state(&change.ata_changes, logger.fork("DidUpdateATAState"));
        }

        project_collection_builder
            .did_change_custom_config_file_name(logger.fork("DidChangeCustomConfigFileName"));

        if !change.file_changes.is_empty() {
            project_collection_builder
                .did_change_files(&change.file_changes, logger.fork("DidChangeFiles"));
        }

        let mut api_error: Option<GoError> = None;
        if let Some(api_request) = &change.api_request {
            api_error = project_collection_builder
                .handle_api_request(api_request, logger.fork("HandleAPIRequest"))
                .err();
        }

        for uri in &change.resource_request.documents {
            project_collection_builder.did_request_file(
                uri,
                false, /*configuredProjectsOnly*/
                logger.fork("DidRequestFile"),
            );
        }

        for uri in &change.resource_request.configured_project_documents {
            project_collection_builder.did_request_file(
                uri,
                true, /*configuredProjectsOnly*/
                logger.fork("DidRequestFile (optional)"),
            );
        }

        for project_id in &change.resource_request.projects {
            project_collection_builder
                .did_request_project(project_id, logger.fork("DidRequestProject"));
        }

        if let Some(project_tree) = &change.resource_request.project_tree {
            project_collection_builder
                .did_request_project_trees(project_tree, logger.fork("DidRequestProjectTrees"));
        }

        let (project_collection, config_file_registry) =
            project_collection_builder.finalize(logger.clone());

        let mut projects_with_new_program_structure: FxHashMap<tspath::Path, bool> =
            FxHashMap::default();
        for project in project_collection.projects() {
            let project = project.borrow();
            if project.program_last_update == new_snapshot_id
                && project.program_update_kind != ProgramUpdateKind::CLONED
            {
                projects_with_new_program_structure.insert(
                    project.config_file_path.clone(),
                    project.program_update_kind == ProgramUpdateKind::NEW_FILES,
                );
            }
        }

        // Clean cached disk files not touched by any open project on file open, close, delete,
        // or when explicitly requested (e.g. by an idle timer).
        let should_clean_disk_cache = change.clean_disk_cache
            || !change.file_changes.opened.0.is_empty()
            || !change.file_changes.reopened.0.is_empty()
            || !change.file_changes.closed.is_empty()
            || !change.file_changes.deleted.is_empty();
        if should_clean_disk_cache {
            // The set of seen files can change only if a program was constructed (not cloned) during this snapshot.
            // When cleanDiskCache is explicitly set, always attempt cleaning.
            if !projects_with_new_program_structure.is_empty() || change.clean_disk_cache {
                let clean_files_start = Instant::now();
                let mut removed_files = 0;
                fs.disk_files.range(&mut |entry| {
                    for project in project_collection.projects() {
                        let project = project.borrow();
                        if let Some(host) = &project.host {
                            if host.source_fs.seen_file(&entry.key()) {
                                return true;
                            }
                        }
                    }
                    entry.delete();
                    removed_files += 1;
                    true
                });
                if session.options.logging_enabled {
                    logger.logf(&format!(
                        "Removed {} cached file(s) in {:?}",
                        removed_files,
                        clean_files_start.elapsed()
                    ));
                }
            }
        }

        let mut config = self.user_preferences.clone();
        if let Some(new_config) = &change.new_config {
            config = new_config.clone();
        }

        let auto_import_host = new_auto_import_registry_clone_host(
            project_collection.clone(),
            session.parse_cache.clone(),
            fs.clone(),
            &self.session_options.current_directory,
            self.to_path.clone(),
        );
        let mut open_files: FxHashMap<tspath::Path, String> =
            FxHashMap::with_capacity_and_hasher(overlays.len(), Default::default());
        for (path, overlay) in overlays {
            open_files.insert(path.clone(), overlay.file_name());
        }
        let mut prepare_auto_imports = tspath::Path::default();
        if !change.resource_request.auto_imports.0.is_empty() {
            prepare_auto_imports = change
                .resource_request
                .auto_imports
                .path(self.use_case_sensitive_file_names());
        }
        let mut old_auto_imports = self.auto_imports.clone();
        if old_auto_imports.is_none() {
            old_auto_imports = Some(Rc::new(autoimport::new_registry(
                self.to_path.clone(),
                self.user_preferences.clone(),
            )));
        }
        let mut auto_imports_watch: Option<Rc<WatchedFiles<FxHashMap<tspath::Path, String>>>> =
            None;
        let clone_result = old_auto_imports.expect(NIL_DEREF).clone_(
            ctx,
            autoimport::RegistryChange {
                requested_file: prepare_auto_imports,
                open_files,
                changed: change.file_changes.changed.clone(),
                created: change.file_changes.created.clone(),
                deleted: change.file_changes.deleted.clone(),
                rebuilt_programs: projects_with_new_program_structure,
                user_preferences: change.new_config.clone(),
            },
            auto_import_host.clone() as Rc<dyn autoimport::RegistryCloneHost>,
            logger.fork("UpdateAutoImports"),
        );
        // PORT: Go `autoImports, err := ...`; on an error Go `autoImports` is nil.
        let auto_imports: Option<Rc<autoimport::Registry>> = match clone_result {
            Ok(auto_imports) => {
                auto_imports_watch = WatchedFiles::clone_(
                    self.auto_imports_watch.as_deref(),
                    auto_imports.node_modules_directories(),
                );
                Some(auto_imports)
            }
            Err(_) => None,
        };

        let (snapshot_fs, _) = fs.finalize();
        // PORT: Go passes nil for the config file registry and assigns it
        // right after; the port passes the final registry here.
        let mut new_snapshot = new_snapshot(
            new_snapshot_id,
            snapshot_fs.clone(),
            self.session_options.clone(),
            config_file_registry.clone(),
            compiler_options_for_inferred_projects,
            config,
            auto_imports,
            auto_imports_watch,
            self.to_path.clone(),
        );
        {
            // PORT: Go writes the new snapshot's fields before anyone else
            // sees it; the `Rc` is not shared yet.
            let s = Rc::get_mut(&mut new_snapshot).expect("new snapshot is not shared yet");
            s.parent_id = self.id;
            s.project_collection = project_collection;
            s.config_file_registry = config_file_registry;
            s.builder_logs = logger.clone();
            s.api_error = api_error;
        }

        for project in new_snapshot.project_collection.projects() {
            let project = project.borrow();
            // PORT: Go `project.Program` (the field).
            if let Some(program) = project.program {
                session.program_counter.ref_(program);
                if project.program_last_update == new_snapshot_id {
                    // If the program was updated during this clone, the project and its host are new
                    // and still retain references to the builder. Freezing clears the builder reference
                    // so it's GC'd and to ensure the project can't access any data not already in the
                    // snapshot during use. This is pretty kludgy, but it's an artifact of Program design:
                    // Program has a single host, which is expected to implement a full vfs.FS, among
                    // other things. That host is *mostly* only used during program *construction*, but a
                    // few methods may get exercised during program *use*. So, our compiler host is allowed
                    // to access caches and perform mutating effects (like acquire referenced project
                    // config files) during snapshot building, and then we call `freeze` to ensure those
                    // mutations don't happen afterwards. In the future, we might improve things by
                    // separating what it takes to build a program from what it takes to use a program,
                    // and only pass the former into NewProgram instead of retaining it indefinitely.
                    project.host.as_ref().expect(NIL_DEREF).freeze(
                        snapshot_fs.clone(),
                        new_snapshot.config_file_registry.clone(),
                    );
                }
            }
        }
        // PORT: Go map order is random; the registry map's order here (the
        // owner adds do not depend on the order).
        for config in new_snapshot.config_file_registry.configs.values() {
            let config = config.borrow();
            if let Some(command_line) = &config.command_line {
                if let Some(config_file) = &command_line.config_file {
                    for file in &config_file.extended_source_files {
                        session
                            .extended_config_cache
                            .add_owner(&(new_snapshot.to_path)(file), new_snapshot.id);
                    }
                }
            }
        }

        autoimport::RegistryCloneHost::dispose(&*auto_import_host);

        logger.logf(&format!(
            "Finished cloning snapshot {} into snapshot {} in {:?}",
            self.id,
            new_snapshot.id,
            start.elapsed()
        ));
        new_snapshot
    }

    // Go: project/snapshot.go:502 ref
    // ref increments the snapshot's reference count, preventing it from being
    // disposed until a corresponding Deref is called. The snapshot must still
    // be alive (refCount > 0) when ref is called. Only the project Session
    // should call ref(), and it should be done while holding session.snapshotMu.
    pub fn ref_(&self) {
        // Go: s.refCount.Add(1)
        let rc = self.ref_count.get() + 1;
        self.ref_count.set(rc);
        if rc <= 1 {
            panic!(
                "snapshot {}: ref on disposed snapshot, parentId={}",
                self.id, self.parent_id
            );
        }
    }

    // Go: project/snapshot.go:511 tryRef
    // tryRef attempts to increment the snapshot's reference count. If the
    // snapshot is already disposed (refCount == 0), it returns false without
    // modifying the count. On success the caller must eventually call Deref.
    // PORT: one thread, so the compare-and-swap always succeeds.
    pub fn try_ref(&self) -> bool {
        let rc = self.ref_count.get();
        if rc <= 0 {
            return false;
        }
        self.ref_count.set(rc + 1);
        true
    }

    // Go: project/snapshot.go:525 Deref
    // Deref decrements the snapshot's reference count. When the count reaches
    // zero, the snapshot is disposed and its resources are released.
    pub fn deref(&self, session: &Session) {
        // Go: s.refCount.Add(-1)
        let rc = self.ref_count.get() - 1;
        self.ref_count.set(rc);
        if rc < 0 {
            panic!(
                "snapshot {}: ref count below zero, parentId={}",
                self.id, self.parent_id
            );
        }
        if rc == 0 {
            self.dispose(session);
        }
    }

    // Go: project/snapshot.go:535 dispose
    pub fn dispose(&self, session: &Session) {
        for project in self.project_collection.projects() {
            let project = project.borrow();
            // PORT: Go `project.Program` (the field).
            if let Some(program) = project.program {
                if session.program_counter.deref(program) {
                    // This program is no longer referenced by any snapshot.
                    // Mark its checker pool as discarded so its idle-cleanup timer stops
                    // keeping the pool alive, allowing the pool and any idle checkers it
                    // still references to be reclaimed when the pool is garbage-collected.
                    if let Some(checker_pool) = &project.checker_pool {
                        checker_pool.discard();
                    }
                    for file in program.source_files() {
                        deref_program_file(
                            &session.parse_cache,
                            file.parse_options(),
                            file.text,
                            file.script_kind,
                        );
                    }
                    for file in program.duplicate_source_files() {
                        deref_program_file(
                            &session.parse_cache,
                            &file.parse_options,
                            file.text,
                            file.script_kind,
                        );
                    }
                    // PORT: Go frees the program when nothing references it.
                    // The port frees its checkers and its program version
                    // now, or when the last request on it ends. Its
                    // cross-project search thread ends after its queued jobs.
                    crate::program::ls_program::release_program(program);
                    crate::ls::release_search_thread(program);
                }
            }
        }
        // PORT: Go map order is random; the registry map's order here (the
        // releases do not depend on the order).
        for config in self.config_file_registry.configs.values() {
            let config = config.borrow();
            if let Some(command_line) = &config.command_line {
                for file in command_line.extended_source_files() {
                    session
                        .extended_config_cache
                        .release(&(session.to_path)(file), self.id);
                }
            }
        }
    }
}
