//! Go `internal/project/projectcollectionbuilder.go`.
//!
//! PORT: one thread (project/dirty/interfaces.rs). The builder is shared
//! (`Rc<ProjectCollectionBuilder>`: projects and compiler hosts keep a
//! pointer to it until `freeze`), so its methods take `self: &Rc<Self>` and
//! the fields Go writes after construction are `Cell` / `RefCell`. Go
//! `dirty.Value[*Project]` is `&dyn dirty::Value<Rc<RefCell<Project>>>`
//! (a returned one is `Rc<dyn ..>`). Go `collections.Set` and
//! `map[K]struct{}` are `FxHashSet`; Go `collections.SyncSet` is a
//! `RefCell<FxHashSet>`. `core.BreadthFirstSearchParallelEx` and the
//! parallel `core.WorkGroup` run serially in queue order. Log text uses
//! `{:?}` for Go `%v` (log only).

use crate::project::prelude::*;

use crate::frontend::{core_bfs, core_ls_ext, core_workgroup};
use std::cell::Cell;
use std::collections::VecDeque;
use std::time::Instant;

const NIL_DEREF: &str = "invalid memory address or nil pointer dereference";

// Go: project/projectcollectionbuilder.go:20 projectLoadKind
// PORT: Go `type projectLoadKind int` with iota consts; Go
// `projectLoadKindFind` is `ProjectLoadKind::FIND` (same values).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct ProjectLoadKind(pub i32);

impl ProjectLoadKind {
    // Project is not created or updated, only looked up in cache
    pub const FIND: ProjectLoadKind = ProjectLoadKind(0);
    // Project is created and then its graph is updated
    pub const CREATE: ProjectLoadKind = ProjectLoadKind(1);
}

// Go: project/projectcollectionbuilder.go:29 ProjectCollectionBuilder
pub struct ProjectCollectionBuilder {
    pub session_options: Rc<SessionOptions>,
    pub parse_cache: Rc<ParseCache>,
    pub extended_config_cache: Rc<ExtendedConfigCache>,
    pub to_path: Rc<dyn Fn(&str) -> tspath::Path>,

    pub ctx: Context,
    pub fs: Rc<SnapshotFSBuilder>,
    pub base: Rc<ProjectCollection>,
    pub compiler_options_for_inferred_projects: Option<Rc<CompilerOptions>>,
    pub config_file_registry_builder: Rc<ConfigFileRegistryBuilder>,

    pub client: Option<Rc<dyn Client>>, // optional; used for project loading notifications

    pub new_snapshot_id: u64,
    pub program_structure_changed: Cell<bool>,
    pub default_projects_invalidated: Cell<bool>,
    pub open_files_changed: Cell<bool>,

    // PORT: a Go nil map is an empty map (Go only reads it, compares it
    // with `maps.Equal`, or makes it before a write).
    pub file_default_projects: RefCell<FxHashMap<tspath::Path, tspath::Path>>,
    pub configured_projects: Rc<dirty::SyncMap<tspath::Path, Rc<RefCell<Project>>>>,
    pub inferred_project: Rc<dirty::Box<Rc<RefCell<Project>>>>,

    pub api_opened_projects: RefCell<FxHashSet<tspath::Path>>,
}

// Go: project/projectcollectionbuilder.go:55 newProjectCollectionBuilder
// PORT: Go `maps.Clone(oldAPIOpenedProjects)` copies the set, so the caller
// passes it by reference.
#[allow(clippy::too_many_arguments)]
pub fn new_project_collection_builder(
    ctx: &Context,
    new_snapshot_id: u64,
    fs: Rc<SnapshotFSBuilder>,
    old_project_collection: Rc<ProjectCollection>,
    old_config_file_registry: Rc<ConfigFileRegistry>,
    old_api_opened_projects: &FxHashSet<tspath::Path>,
    compiler_options_for_inferred_projects: Option<Rc<CompilerOptions>>,
    session_options: Rc<SessionOptions>,
    custom_config_file_name: &str,
    parse_cache: Rc<ParseCache>,
    extended_config_cache: Rc<ExtendedConfigCache>,
    client: Option<Rc<dyn Client>>,
) -> Rc<ProjectCollectionBuilder> {
    let config_file_registry_builder = new_config_file_registry_builder(
        lsproto::get_client_capabilities(ctx)
            .workspace
            .did_change_watched_files
            .relative_pattern_support,
        fs.clone(),
        old_config_file_registry,
        extended_config_cache.clone(),
        new_snapshot_id,
        session_options.clone(),
        custom_config_file_name,
        None,
    );
    Rc::new(ProjectCollectionBuilder {
        ctx: ctx.clone(),
        to_path: fs.to_path.clone(),
        fs,
        compiler_options_for_inferred_projects,
        session_options,
        parse_cache,
        extended_config_cache,
        config_file_registry_builder,
        new_snapshot_id,
        configured_projects: dirty::new_sync_map(
            old_project_collection.configured_projects.clone(),
        ),
        inferred_project: dirty::new_box(old_project_collection.inferred_project.clone()),
        api_opened_projects: RefCell::new(old_api_opened_projects.clone()),
        client,
        base: old_project_collection,
        program_structure_changed: Cell::new(false),
        default_projects_invalidated: Cell::new(false),
        open_files_changed: Cell::new(false),
        file_default_projects: RefCell::new(FxHashMap::default()),
    })
}

/// Go `tspath.Path(inferredProjectName)`.
fn inferred_project_path() -> tspath::Path {
    tspath::Path(INFERRED_PROJECT_NAME.to_string())
}

// PORT: Go `ensureCloned` (closure in Finalize). `None` is Go
// `changed == false` (the base collection is still the result).
fn ensure_cloned<'c>(
    new_project_collection: &'c mut Option<ProjectCollection>,
    base: &ProjectCollection,
) -> &'c mut ProjectCollection {
    if new_project_collection.is_none() {
        *new_project_collection = Some(ProjectCollection::clone(base));
    }
    new_project_collection.as_mut().expect("cloned above")
}

impl ProjectCollectionBuilder {
    // Go: project/projectcollectionbuilder.go:87 Finalize
    pub fn finalize(
        self: &Rc<Self>,
        _logger: Option<Rc<logging::LogTree>>,
    ) -> (Rc<ProjectCollection>, Rc<ConfigFileRegistry>) {
        // PORT: Go `changed` + `newProjectCollection := b.base`; the clone is
        // owned until it is returned.
        let mut new_project_collection: Option<ProjectCollection> = None;

        let (configured_projects, configured_projects_changed) =
            self.configured_projects.finalize_exported();
        if configured_projects_changed {
            ensure_cloned(&mut new_project_collection, &self.base).configured_projects =
                configured_projects;
        }

        if self.open_files_changed.get() {
            ensure_cloned(&mut new_project_collection, &self.base).open_files =
                open_file_paths(&self.fs.overlays);
        }

        if *self.file_default_projects.borrow() != self.base.file_default_projects {
            ensure_cloned(&mut new_project_collection, &self.base).file_default_projects =
                self.file_default_projects.borrow().clone();
        }

        let (new_inferred_project, inferred_project_changed) = self.inferred_project.finalize();
        if inferred_project_changed {
            ensure_cloned(&mut new_project_collection, &self.base).inferred_project =
                new_inferred_project;
        }

        let config_file_registry = self.config_file_registry_builder.finalize();
        let same_registry = matches!(
            &self.base.config_file_registry,
            Some(base) if Rc::ptr_eq(base, &config_file_registry)
        );
        if !same_registry {
            ensure_cloned(&mut new_project_collection, &self.base).config_file_registry =
                Some(config_file_registry.clone());
        }

        if *self.api_opened_projects.borrow() != self.base.api_opened_projects {
            ensure_cloned(&mut new_project_collection, &self.base).api_opened_projects =
                self.api_opened_projects.borrow().clone();
        }

        let new_project_collection = match new_project_collection {
            Some(cloned) => Rc::new(cloned),
            None => self.base.clone(),
        };
        (new_project_collection, config_file_registry)
    }

    // Go: project/projectcollectionbuilder.go:131 forEachProject
    pub fn for_each_project(
        self: &Rc<Self>,
        fn_: &mut dyn FnMut(&dyn dirty::Value<Rc<RefCell<Project>>>) -> bool,
    ) {
        let mut keep_going = true;
        self.configured_projects.range(&mut |entry| {
            keep_going = fn_(&**entry);
            keep_going
        });
        if !keep_going {
            return;
        }
        if self.inferred_project.value().is_some() {
            fn_(&*self.inferred_project);
        }
    }

    // Go: project/projectcollectionbuilder.go:145 HandleAPIRequest
    pub fn handle_api_request(
        self: &Rc<Self>,
        api_request: &APISnapshotRequest,
        logger: Option<Rc<logging::LogTree>>,
    ) -> Result<(), GoError> {
        // PORT: a Go nil map is an empty set.
        let mut projects_to_close: FxHashSet<tspath::Path> = FxHashSet::default();
        if let Some(close_projects) = &api_request.close_projects {
            projects_to_close = close_projects.clone();
            for project_path in close_projects {
                self.api_opened_projects.borrow_mut().remove(project_path);
            }
        }

        if let Some(open_projects) = &api_request.open_projects {
            // PORT: Go map order is random; FxHashSet order here.
            for config_file_name in open_projects {
                let config_path = (self.to_path)(config_file_name);
                if self
                    .find_or_create_project(
                        config_file_name,
                        &config_path,
                        ProjectLoadKind::CREATE,
                        logger.clone(),
                    )
                    .is_some()
                {
                    self.api_opened_projects.borrow_mut().insert(config_path);
                } else {
                    return Err(gostd::errors::errorf(
                        format!("project not found for open: {}", config_file_name),
                        vec![],
                    ));
                }
            }
        }

        // PORT: Go ranges over the live map; the keys are copied first (the
        // loop body does not change the map).
        let api_opened_projects: Vec<tspath::Path> =
            self.api_opened_projects.borrow().iter().cloned().collect();
        for config_path in api_opened_projects {
            if let (Some(entry), true) = self.configured_projects.load(&config_path) {
                self.update_program(&*entry, logger.clone());
            } else {
                return Err(gostd::errors::errorf(
                    format!("project not found for update: {}", config_path),
                    vec![],
                ));
            }
        }

        for overlay in self.fs.overlays.values() {
            let file_name = overlay.file_name();
            if let Some(entry) =
                self.find_default_configured_project(&file_name, &(self.to_path)(&file_name))
            {
                let config_file_path = entry
                    .value()
                    .expect(NIL_DEREF)
                    .borrow()
                    .config_file_path
                    .clone();
                projects_to_close.remove(&config_file_path);
            }
        }

        for project_path in &projects_to_close {
            if let (Some(entry), true) = self.configured_projects.load(project_path) {
                self.delete_configured_project(&*entry, logger.clone());
            }
        }

        Ok(())
    }

    // Go: project/projectcollectionbuilder.go:191 DidChangeFiles
    // PORT: Go passes the summary by value; here by reference.
    pub fn did_change_files(
        self: &Rc<Self>,
        summary: &FileChangeSummary,
        logger: Option<Rc<logging::LogTree>>,
    ) {
        self.open_files_changed.set(
            self.open_files_changed.get()
                || !summary.opened.0.is_empty()
                || !summary.closed.is_empty(),
        );

        let mut changed_files: Vec<tspath::Path> = Vec::with_capacity(summary.changed.len());
        for uri in &summary.changed {
            let file_name = uri.file_name();
            let path = (self.to_path)(&file_name);
            changed_files.push(path);
        }

        let config_change_logger = logger.fork("Checking for changes affecting config files");
        let config_change_result = self
            .config_file_registry_builder
            .did_change_files(summary, config_change_logger.clone());
        log_change_file_result(&config_change_result, &config_change_logger);

        self.program_structure_changed.set(
            self.mark_projects_affected_by_config_changes(&config_change_result, logger.clone()),
        );

        self.for_each_project(
            &mut |entry: &dyn dirty::Value<Rc<RefCell<Project>>>| -> bool {
                // Only consider change/delete; creates are handled by the config file registry
                if summary.has_excessive_non_create_watch_events() {
                    entry.change(&mut |p: &Rc<RefCell<Project>>| {
                        let mut p = p.borrow_mut();
                        p.dirty = true;
                        p.dirty_file_path = tspath::Path::default();
                        if logger.is_some() {
                            logger.logf(&format!(
                                "Marking project as dirty due to excessive watch changes: {}",
                                p.config_file_path
                            ));
                        }
                    });
                    return true;
                }

                // Handle closed and changed files
                self.mark_files_changed(
                    entry,
                    &changed_files,
                    lsproto::FileChangeType::CHANGED,
                    logger.clone(),
                );
                let value = entry.value().expect(NIL_DEREF);
                if value.borrow().kind == Kind::INFERRED && !summary.closed.is_empty() {
                    // PORT: Go `newRootFiles` aliases the command line's slice and
                    // `slices.Delete` edits it in place; the port edits a copy.
                    let (root_files_map, mut new_root_files) = {
                        let value = value.borrow();
                        let command_line = value.command_line.as_ref().expect(NIL_DEREF);
                        (
                            command_line.file_names_by_path().clone(),
                            command_line.file_names().to_vec(),
                        )
                    };
                    for uri in &summary.closed {
                        let file_name = uri.file_name();
                        let path = (self.to_path)(&file_name);
                        if root_files_map.contains_key(&path) {
                            // Go: slices.Delete(newRootFiles, slices.Index(newRootFiles, fileName), slices.Index(newRootFiles, fileName)+1)
                            let Some(index) = new_root_files.iter().position(|f| *f == file_name)
                            else {
                                panic!("runtime error: slice bounds out of range [-1:]");
                            };
                            new_root_files.remove(index);
                        }
                    }
                    self.update_inferred_project_roots(new_root_files, logger.clone());
                }

                // Handle deleted files
                if !summary.deleted.is_empty() {
                    let mut deleted_paths: Vec<tspath::Path> =
                        Vec::with_capacity(summary.deleted.len());
                    for uri in &summary.deleted {
                        let file_name = uri.file_name();
                        let path = (self.to_path)(&file_name);
                        deleted_paths.push(path);
                    }
                    self.mark_files_changed(
                        entry,
                        &deleted_paths,
                        lsproto::FileChangeType::DELETED,
                        logger.clone(),
                    );
                }

                // Handle created files
                if !summary.created.is_empty() {
                    let mut created_paths: Vec<tspath::Path> =
                        Vec::with_capacity(summary.created.len());
                    for uri in &summary.created {
                        let file_name = uri.file_name();
                        let path = (self.to_path)(&file_name);
                        created_paths.push(path);
                    }
                    self.mark_files_changed(
                        entry,
                        &created_paths,
                        lsproto::FileChangeType::CREATED,
                        logger.clone(),
                    );
                }

                true
            },
        );

        // Handle opened file
        if !summary.opened.0.is_empty() || !summary.reopened.0.is_empty() {
            // PORT: Go `collections.Set` (random order); `IndexSet` keeps the
            // insertion order so deletions run in a fixed order.
            let mut to_remove_projects: IndexSet<tspath::Path> = IndexSet::new();
            let file_name =
                core_ls_ext::first_non_zero([summary.opened.clone(), summary.reopened.clone()])
                    .file_name();
            let path = (self.to_path)(&file_name);
            let open_file_result = self.ensure_configured_project_and_ancestors_for_file(
                &file_name,
                &path,
                logger.clone(),
            );
            self.configured_projects.range(&mut |entry| {
                to_remove_projects.insert(entry.key());
                true
            });

            // Go: retainProjectAndReferences (closure in DidChangeFiles)
            let retain_project_and_references =
                |to_remove_projects: &mut IndexSet<tspath::Path>,
                 project: &Rc<RefCell<Project>>| {
                    // Retain project
                    // PORT: Go `project.GetProgram()` is the field read.
                    let (config_file_path, program) = {
                        let project = project.borrow();
                        (project.config_file_path.clone(), project.program)
                    };
                    to_remove_projects.shift_remove(&config_file_path);
                    if let Some(program) = program {
                        program.range_resolved_project_reference(
                            |reference_path: &tspath::Path, _, _, _| -> bool {
                                if let (_, true) = self.configured_projects.load(reference_path) {
                                    to_remove_projects.shift_remove(reference_path);
                                }
                                true
                            },
                        );
                    }
                };

            // Go: retainDefaultConfiguredProject (closure in DidChangeFiles)
            let retain_default_configured_project =
                |to_remove_projects: &mut IndexSet<tspath::Path>,
                 _open_file: &str,
                 open_file_path: &tspath::Path,
                 project: &Rc<RefCell<Project>>| {
                    // Retain project and its references
                    retain_project_and_references(&mut *to_remove_projects, project);

                    // Retain all the ancestor projects
                    self.config_file_registry_builder
                        .for_each_config_file_name_for(
                            open_file_path,
                            &mut |config_file_name: &str| {
                                if let Some(ancestor) = self.find_or_create_project(
                                    config_file_name,
                                    &(self.to_path)(config_file_name),
                                    ProjectLoadKind::FIND,
                                    logger.clone(),
                                ) {
                                    retain_project_and_references(
                                        &mut *to_remove_projects,
                                        &ancestor.value().expect(NIL_DEREF),
                                    );
                                }
                            },
                        );
                };

            let mut inferred_project_files: Vec<String> = Vec::new();
            // PORT: Go map order is random; the overlay map is an IndexMap.
            for overlay in self.fs.overlays.values() {
                let open_file = overlay.file_name();
                let open_file_path = (self.to_path)(&open_file);
                if let Some(p) = self.find_default_configured_project(&open_file, &open_file_path) {
                    retain_default_configured_project(
                        &mut to_remove_projects,
                        open_file.as_str(),
                        &open_file_path,
                        &p.value().expect(NIL_DEREF),
                    );
                } else {
                    inferred_project_files.push(overlay.file_name());
                }
            }

            for project_path in &to_remove_projects {
                if open_file_result.retain.contains(project_path) {
                    continue;
                }
                if self.api_opened_projects.borrow().contains(project_path) {
                    continue;
                }
                if let (Some(p), true) = self.configured_projects.load(project_path) {
                    self.delete_configured_project(&*p, logger.clone());
                }
            }
            self.update_inferred_project_roots(inferred_project_files, logger.clone());
            self.config_file_registry_builder.cleanup();
        }
    }

    // Go: project/projectcollectionbuilder.go:356 cleanupInferredProject
    pub fn cleanup_inferred_project(self: &Rc<Self>, logger: Option<Rc<logging::LogTree>>) {
        let mut inferred_project_files: Vec<String> = Vec::new();
        for (path, overlay) in &self.fs.overlays {
            if self
                .find_default_configured_project(&overlay.file_name(), path)
                .is_none()
            {
                inferred_project_files.push(overlay.file_name());
            }
        }
        self.update_inferred_project_roots(inferred_project_files, logger);
    }

    // Go: project/projectcollectionbuilder.go:366 ensureInferredProjectIncludesClosedFile
    pub fn ensure_inferred_project_includes_closed_file(
        self: &Rc<Self>,
        file_name: &str,
        logger: Option<Rc<logging::LogTree>>,
    ) {
        // Collect existing inferred project roots (open files not in configured projects)
        // plus this closed file.
        let mut inferred_project_files: Vec<String> = Vec::new();
        for (path, overlay) in &self.fs.overlays {
            if self
                .find_default_configured_project(&overlay.file_name(), path)
                .is_none()
            {
                inferred_project_files.push(overlay.file_name());
            }
        }
        inferred_project_files.push(file_name.to_string());
        self.update_inferred_project_roots(inferred_project_files, logger.clone());
        if self.inferred_project.value().is_some() {
            self.update_program(&*self.inferred_project, logger);
        }
    }

    // Go: project/projectcollectionbuilder.go:385 DidRequestFile
    // DidRequestFile ensures projects are loaded for the given URI.
    // If configuredProjectsOnly is true, only configured projects are loaded; no inferred project is created
    // and it is not guaranteed that there will be any project containing the file in the resulting snapshot.
    pub fn did_request_file(
        self: &Rc<Self>,
        uri: &lsproto::DocumentUri,
        configured_projects_only: bool,
        logger: Option<Rc<logging::LogTree>>,
    ) {
        let start_time = Instant::now();
        let file_name = uri.file_name();
        let path = (self.to_path)(&file_name);
        if self.default_projects_invalidated.get() {
            self.ensure_configured_project_and_ancestors_for_file(
                &file_name,
                &path,
                logger.clone(),
            );
            if !self.fs.is_open_file(&path) {
                return;
            }
        }
        if self.fs.is_open_file(&path) {
            let mut has_changes = self.program_structure_changed.get();

            // See if we can find a default project without updating a bunch of stuff.
            if let Some(result) = self.find_default_project(&file_name, &path) {
                has_changes = self.update_program(&*result, logger.clone()) || has_changes;
                if result.value().is_some() {
                    if has_changes {
                        self.cleanup_inferred_project(logger.clone());
                        if self.inferred_project.value().is_some() {
                            self.update_program(&*self.inferred_project, logger.clone());
                        }
                    }
                    return;
                }
            }

            // Make sure all projects we know about are up to date...
            self.configured_projects.range(&mut |entry| {
                has_changes = self.update_program(&**entry, logger.clone()) || has_changes;
                true
            });
            if has_changes {
                // If the structure of other projects changed, we might need to move files
                // in/out of the inferred project.
                self.cleanup_inferred_project(logger.clone());
            }

            if self.inferred_project.value().is_some() {
                self.update_program(&*self.inferred_project, logger.clone());
            }

            // At this point we should be able to find the default project for the file without
            // creating anything else. Initially, I verified that and panicked if nothing was found,
            // but that panic was getting triggered by fourslash infrastructure when it told us to
            // open a package.json file. This is something the VS Code client would never do, but
            // it seems possible that another client would. There's no point in panicking; we don't
            // really even have an error condition until it tries to ask us language questions about
            // a non-TS-handleable file.
        } else {
            let result = self.ensure_configured_project_and_ancestors_for_file(
                &file_name,
                &path,
                logger.clone(),
            );
            if result.project.is_none() && !configured_projects_only {
                // No configured project found for this closed file.
                // Add it to the inferred project so language service requests can be served.
                self.ensure_inferred_project_includes_closed_file(&file_name, logger.clone());
            }
        }

        if logger.is_some() {
            let elapsed = start_time.elapsed();
            logger.log(&format!(
                "Completed file request for {} in {:?}",
                file_name, elapsed
            ));
        }
    }

    // Go: project/projectcollectionbuilder.go:449 DidRequestProject
    pub fn did_request_project(
        self: &Rc<Self>,
        project_id: &tspath::Path,
        logger: Option<Rc<logging::LogTree>>,
    ) {
        let start_time = Instant::now();
        if project_id.as_str() == INFERRED_PROJECT_NAME {
            // Update inferred project
            if self.inferred_project.value().is_some() {
                self.update_program(&*self.inferred_project, logger.clone());
            }
        } else if let (Some(entry), true) = self.configured_projects.load(project_id) {
            self.update_program(&*entry, logger.clone());
        }

        if logger.is_some() {
            let elapsed = start_time.elapsed();
            logger.log(&format!(
                "Completed project update request for {} in {:?}",
                project_id, elapsed
            ));
        }
    }

    // Go: project/projectcollectionbuilder.go:468 DidRequestProjectTrees
    pub fn did_request_project_trees(
        self: &Rc<Self>,
        project_tree_request: &ProjectTreeRequest,
        logger: Option<Rc<logging::LogTree>>,
    ) {
        let start_time = Instant::now();

        let mut current_projects: Vec<tspath::Path> = Vec::new();
        self.configured_projects.range(&mut |sme| {
            current_projects.push(sme.key());
            true
        });

        let seen_projects: RefCell<FxHashSet<tspath::Path>> = RefCell::new(FxHashSet::default());
        // PORT: Go `core.NewWorkGroup(false)` is the parallel group, which
        // starts every queued function at once. On the dispatch thread the
        // port runs them serially in queue order (first in, first out), so
        // it builds the port's FIFO group, not `new_work_group` (LIFO).
        let wg: Rc<dyn core_workgroup::WorkGroup<'_> + '_> =
            Rc::new(core_workgroup::ParallelWorkGroup {
                done: Cell::new(false),
                wg: RefCell::new(VecDeque::new()),
            });
        for project_id in current_projects {
            let b = self;
            let wg_inner = wg.clone();
            let seen_projects = &seen_projects;
            let logger = logger.clone();
            wg.queue(Box::new(move || {
                if let (Some(entry), true) = b.configured_projects.load(&project_id) {
                    // If this project has potential project reference for any of the project we are loading ancestor tree for
                    // load this project first
                    if let Some(project) = entry.value() {
                        if project_tree_request.is_all_projects()
                            || project
                                .borrow()
                                .has_potential_project_reference(project_tree_request)
                        {
                            b.update_program(&*entry, logger.clone());
                        }
                    }
                    b.ensure_project_tree(
                        &wg_inner,
                        &entry,
                        project_tree_request,
                        seen_projects,
                        logger.clone(),
                    );
                }
            }));
        }
        wg.run_and_wait();

        if logger.is_some() {
            let elapsed = start_time.elapsed();
            logger.log(&format!(
                "Completed project tree request for {:?} in {:?}",
                project_tree_request.projects(),
                elapsed
            ));
        }
    }

    // Go: project/projectcollectionbuilder.go:499 ensureProjectTree
    pub fn ensure_project_tree<'a>(
        self: &'a Rc<Self>,
        wg: &Rc<dyn core_workgroup::WorkGroup<'a> + 'a>,
        entry: &Rc<dirty::SyncMapEntry<tspath::Path, Rc<RefCell<Project>>>>,
        project_tree_request: &'a ProjectTreeRequest,
        seen_projects: &'a RefCell<FxHashSet<tspath::Path>>,
        logger: Option<Rc<logging::LogTree>>,
    ) {
        if !seen_projects.borrow_mut().insert(entry.key()) {
            return;
        }

        let Some(project) = entry.value() else {
            return;
        };

        // PORT: Go `project.GetProgram()` is the field read.
        let Some(program) = project.borrow().program else {
            return;
        };

        // If this project disables child load ignore it
        if program
            .command_line()
            .compiler_options()
            .disable_referenced_project_load
            .is_true()
        {
            return;
        }

        // PORT: Go returns nil when the program has no root config; that is
        // an empty `Vec` here, and the loop below then does nothing.
        let children = program.get_resolved_project_references();
        if children.is_empty() {
            return;
        }
        for child_config in children {
            let Some(child_config) = child_config else {
                continue;
            };
            let wg_inner = wg.clone();
            let logger = logger.clone();
            wg.queue(Box::new(move || {
                if !project_tree_request.is_all_projects()
                    && program.range_resolved_project_reference_in_child_config(
                        &child_config,
                        |reference_path: &tspath::Path, _config, _, _| -> bool {
                            !project_tree_request.is_project_referenced(reference_path)
                        },
                    )
                {
                    return;
                }

                // Load this child project since this is referenced
                let child_config_path = child_config
                    .config_file
                    .as_ref()
                    .expect(NIL_DEREF)
                    .path
                    .clone();
                let child_project_entry = self
                    .find_or_create_project(
                        child_config.config_name(),
                        &child_config_path,
                        ProjectLoadKind::CREATE,
                        logger.clone(),
                    )
                    .expect(NIL_DEREF);
                self.update_program(&*child_project_entry, logger.clone());

                // Ensure children for this project
                self.ensure_project_tree(
                    &wg_inner,
                    &child_project_entry,
                    project_tree_request,
                    seen_projects,
                    logger.clone(),
                );
            }));
        }
    }

    // Go: project/projectcollectionbuilder.go:553 DidUpdateATAState
    // PORT: Go map order is random; FxHashMap order here (log order only).
    pub fn did_update_ata_state(
        self: &Rc<Self>,
        ata_changes: &FxHashMap<tspath::Path, Rc<ATAStateChange>>,
        logger: Option<Rc<logging::LogTree>>,
    ) {
        let update_project = |project: &dyn dirty::Value<Rc<RefCell<Project>>>,
                              ata_change: &ATAStateChange| {
            project.change_if(
                &mut |p: Option<&Rc<RefCell<Project>>>| -> bool {
                    let Some(p) = p else {
                        return false;
                    };
                    // Consistency check: the ATA demands (project options, unresolved imports) of this project
                    // has not changed since the time the ATA request was dispatched; the change can still be
                    // applied to this project in its current state.
                    let typings_info = p.borrow().compute_typings_info();
                    ata_change
                        .typings_info
                        .as_ref()
                        .expect(NIL_DEREF)
                        .equals(&typings_info)
                },
                &mut |p: &Rc<RefCell<Project>>| {
                    let mut p = p.borrow_mut();
                    // We checked before triggering this change (in Session.triggerATAForUpdatedProjects) that
                    // the set of typings files is actually different.
                    p.installed_typings_info = ata_change.typings_info.clone();
                    p.typings_files = ata_change.typings_files.clone();
                    let typings_watch_globs = get_typings_locations_globs(
                        &ata_change.typings_files_to_watch,
                        &self.session_options.typings_location,
                        &self.session_options.current_directory,
                        &p.current_directory,
                        self.fs.fs.use_case_sensitive_file_names(),
                    );
                    let typings_watch =
                        WatchedFiles::clone_(p.typings_watch.as_deref(), typings_watch_globs);
                    p.typings_watch = typings_watch;
                    p.dirty = true;
                    p.dirty_file_path = tspath::Path::default();
                },
            );
        };

        for (project_path, ata_change) in ata_changes {
            logger.embed(&ata_change.logs);
            if project_path.as_str() == INFERRED_PROJECT_NAME {
                update_project(
                    &*self.inferred_project as &dyn dirty::Value<Rc<RefCell<Project>>>,
                    &**ata_change,
                );
            } else if let (Some(project), true) = self.configured_projects.load(project_path) {
                update_project(
                    &*project as &dyn dirty::Value<Rc<RefCell<Project>>>,
                    &**ata_change,
                );
            }

            if logger.is_some() {
                logger.log(&format!("Updated ATA state for project {}", project_path));
            }
        }
    }

    // Go: project/projectcollectionbuilder.go:599 DidChangeCustomConfigFileName
    // if customConfigFileName changes, invalidate default projects.
    pub fn did_change_custom_config_file_name(
        self: &Rc<Self>,
        logger: Option<Rc<logging::LogTree>>,
    ) {
        if !self
            .config_file_registry_builder
            .did_change_custom_config_file_name(logger)
        {
            return;
        }

        // Go: b.fileDefaultProjects = nil
        *self.file_default_projects.borrow_mut() = FxHashMap::default();
        self.default_projects_invalidated.set(true);
        self.program_structure_changed.set(true);
    }

    // Go: project/projectcollectionbuilder.go:609 markProjectsAffectedByConfigChanges
    pub fn mark_projects_affected_by_config_changes(
        self: &Rc<Self>,
        config_change_result: &ChangeFileResult,
        logger: Option<Rc<logging::LogTree>>,
    ) -> bool {
        // PORT: Go map order is random; FxHashSet order here.
        for project_path in &config_change_result.affected_projects {
            let (project, ok) = self.configured_projects.load(project_path);
            if !ok {
                panic!(
                    "project {} affected by config change not found",
                    project_path
                );
            }
            let project = project.expect(NIL_DEREF);
            project.change_if(
                &mut |p: Option<&Rc<RefCell<Project>>>| -> bool {
                    let p = p.expect(NIL_DEREF).borrow();
                    !p.dirty || !p.dirty_file_path.is_empty()
                },
                &mut |p: &Rc<RefCell<Project>>| {
                    let mut p = p.borrow_mut();
                    p.dirty = true;
                    p.dirty_file_path = tspath::Path::default();
                    if logger.is_some() {
                        logger.logf(&format!(
                            "Marking project {} as dirty due to change affecting config",
                            project_path
                        ));
                    }
                },
            );
        }

        // Recompute default projects for open files that now have different config file presence.
        let mut has_changes = false;
        for path in &config_change_result.affected_files {
            let file_name = self.fs.overlays.get(path).expect(NIL_DEREF).file_name();
            let _ = self.ensure_configured_project_and_ancestors_for_file(
                &file_name,
                path,
                logger.clone(),
            );
            has_changes = true;
        }

        has_changes
    }

    // Go: project/projectcollectionbuilder.go:641 findDefaultProject
    pub fn find_default_project(
        self: &Rc<Self>,
        file_name: &str,
        path: &tspath::Path,
    ) -> Option<Rc<dyn dirty::Value<Rc<RefCell<Project>>>>> {
        if let Some(configured_project) = self.find_default_configured_project(file_name, path) {
            return Some(configured_project as Rc<dyn dirty::Value<Rc<RefCell<Project>>>>);
        }
        let key_is_inferred = matches!(
            self.file_default_projects.borrow().get(path),
            Some(key) if key.as_str() == INFERRED_PROJECT_NAME
        );
        if key_is_inferred {
            return Some(
                self.inferred_project.clone() as Rc<dyn dirty::Value<Rc<RefCell<Project>>>>
            );
        }
        if let Some(inferred_project) = self.inferred_project.value() {
            if inferred_project.borrow().contains_file(path) {
                // Go: `if b.fileDefaultProjects == nil { make(...) }` (the port map always exists).
                self.file_default_projects
                    .borrow_mut()
                    .insert(path.clone(), inferred_project_path());
                return Some(
                    self.inferred_project.clone() as Rc<dyn dirty::Value<Rc<RefCell<Project>>>>
                );
            }
        }
        None
    }

    // Go: project/projectcollectionbuilder.go:658 findDefaultConfiguredProject
    pub fn find_default_configured_project(
        self: &Rc<Self>,
        file_name: &str,
        path: &tspath::Path,
    ) -> Option<Rc<dirty::SyncMapEntry<tspath::Path, Rc<RefCell<Project>>>>> {
        let key = self.file_default_projects.borrow().get(path).cloned();
        if let Some(key) = key {
            if key.as_str() != INFERRED_PROJECT_NAME {
                if let (Some(entry), true) = self.configured_projects.load(&key) {
                    return Some(entry);
                }
            }
        }
        // Sort configured projects so we can use a deterministic "first" as a last resort.
        let mut configured_project_paths: Vec<tspath::Path> = Vec::new();
        let mut configured_projects: FxHashMap<
            tspath::Path,
            Rc<dirty::SyncMapEntry<tspath::Path, Rc<RefCell<Project>>>>,
        > = FxHashMap::default();
        self.configured_projects.range(&mut |entry| {
            configured_project_paths.push(entry.key());
            configured_projects.insert(entry.key(), entry.clone());
            true
        });
        configured_project_paths.sort();

        let (project, multiple_candidates) = find_default_configured_project_from_program_inclusion(
            file_name,
            path,
            &configured_project_paths,
            &mut |path: &tspath::Path| configured_projects.get(path).expect(NIL_DEREF).value(),
        );

        if multiple_candidates {
            if let Some(p) = self
                .find_or_create_default_configured_project_for_file(
                    file_name,
                    path,
                    ProjectLoadKind::FIND,
                    None,
                )
                .project
            {
                return Some(p);
            }
        }

        configured_projects.get(&project).cloned()
    }

    // Go: project/projectcollectionbuilder.go:687 ensureConfiguredProjectAndAncestorsForFile
    pub fn ensure_configured_project_and_ancestors_for_file(
        self: &Rc<Self>,
        file_name: &str,
        path: &tspath::Path,
        logger: Option<Rc<logging::LogTree>>,
    ) -> SearchResult {
        let mut result = self.find_or_create_default_configured_project_for_file(
            file_name,
            path,
            ProjectLoadKind::CREATE,
            logger.clone(),
        );
        if result.project.is_some() && self.fs.is_open_file(path) {
            self.create_ancestor_tree(file_name, path, &mut result, logger);
        }
        result
    }

    // Go: project/projectcollectionbuilder.go:695 createAncestorTree
    pub fn create_ancestor_tree(
        self: &Rc<Self>,
        file_name: &str,
        path: &tspath::Path,
        open_result: &mut SearchResult,
        logger: Option<Rc<logging::LogTree>>,
    ) {
        let mut project = open_result
            .project
            .as_ref()
            .expect(NIL_DEREF)
            .value()
            .expect(NIL_DEREF);
        loop {
            // Skip if project is not composite and we are only looking for solution
            let (config_file_name, config_file_path, command_line) = {
                let p = project.borrow();
                (
                    p.config_file_name.clone(),
                    p.config_file_path.clone(),
                    p.command_line.clone(),
                )
            };
            if let Some(command_line) = &command_line {
                if !command_line.compiler_options().composite.is_true()
                    || command_line
                        .compiler_options()
                        .disable_solution_searching
                        .is_true()
                {
                    return;
                }
            }

            // Get config file name
            let ancestor_config_name = self
                .config_file_registry_builder
                .get_ancestor_config_file_name(file_name, path, &config_file_name, logger.clone());
            if ancestor_config_name.is_empty() {
                return;
            }

            // find or delay load the project
            let ancestor_path = (self.to_path)(&ancestor_config_name);
            let Some(ancestor) = self.find_or_create_project(
                &ancestor_config_name,
                &ancestor_path,
                ProjectLoadKind::CREATE,
                logger.clone(),
            ) else {
                return;
            };

            open_result.retain.insert(ancestor_path);

            // If this ancestor is new and was not updated because we are just creating it for future loading
            // eg when invoking find all references or rename that could span multiple projects
            // we would make the current project as its potential project reference
            let ancestor_has_no_command_line = ancestor
                .value()
                .expect(NIL_DEREF)
                .borrow()
                .command_line
                .is_none();
            if ancestor_has_no_command_line
                && command_line
                    .as_ref()
                    .is_none_or(|command_line| command_line.compiler_options().composite.is_true())
            {
                ancestor.change(&mut |ancestor_project: &Rc<RefCell<Project>>| {
                    ancestor_project
                        .borrow_mut()
                        .set_potential_project_reference(&config_file_path);
                });
            }

            project = ancestor.value().expect(NIL_DEREF);
        }
    }

    // Go: project/projectcollectionbuilder.go:750 findOrCreateDefaultConfiguredProjectWorker
    // PORT: Go `*collections.SyncSet[searchNodeKey]` is a `RefCell<FxHashSet>`
    // and Go `collections.SyncMap` of configs is a `RefCell<FxHashMap>`.
    #[allow(clippy::too_many_arguments)]
    pub fn find_or_create_default_configured_project_worker(
        self: &Rc<Self>,
        file_name: &str,
        path: &tspath::Path,
        config_file_name: &str,
        load_kind: ProjectLoadKind,
        visited: Option<&RefCell<FxHashSet<SearchNodeKey>>>,
        fallback: Option<SearchResult>,
        logger: Option<Rc<logging::LogTree>>,
    ) -> SearchResult {
        let mut fallback = fallback;
        let configs: RefCell<FxHashMap<tspath::Path, Rc<tsoptions::ParsedCommandLine>>> =
            RefCell::new(FxHashMap::default());
        let new_visited: RefCell<FxHashSet<SearchNodeKey>>;
        let visited = match visited {
            Some(visited) => visited,
            None => {
                new_visited = RefCell::new(FxHashSet::default());
                &new_visited
            }
        };

        let search = core_bfs::breadth_first_search_parallel_ex(
            SearchNode {
                config_file_name: config_file_name.to_string(),
                load_kind,
                logger: logger.clone(),
            },
            &mut |node: &SearchNode| -> Vec<SearchNode> {
                let config = configs
                    .borrow()
                    .get(&(self.to_path)(&node.config_file_name))
                    .cloned();
                if let Some(config) = config {
                    if !config.project_references().is_empty() {
                        let mut reference_load_kind = node.load_kind;
                        if config
                            .compiler_options()
                            .disable_referenced_project_load
                            .is_true()
                        {
                            reference_load_kind = ProjectLoadKind::FIND;
                        }

                        let mut ref_logger: Option<Rc<logging::LogTree>> = None;
                        let references = config.resolved_project_reference_paths();
                        if !references.is_empty() && node.logger.is_some() {
                            ref_logger = node.logger.fork(&format!(
                                "Searching {} project references of {}",
                                references.len(),
                                node.config_file_name
                            ));
                        }
                        return references
                            .iter()
                            .map(|config_file_name| SearchNode {
                                config_file_name: config_file_name.clone(),
                                load_kind: reference_load_kind,
                                logger: ref_logger.fork(&format!(
                                    "Searching project reference {}",
                                    config_file_name
                                )),
                            })
                            .collect();
                    }
                }
                Vec::new()
            },
            &mut |node: &SearchNode| -> (bool, bool) {
                let config_file_path = (self.to_path)(&node.config_file_name);
                let config = self
                    .config_file_registry_builder
                    .find_or_acquire_config_for_file(
                        &node.config_file_name,
                        &config_file_path,
                        path,
                        node.load_kind,
                        node.logger.fork("Acquiring config for open file"),
                    );
                let Some(config) = config else {
                    node.logger
                        .log("Config file for project does not already exist");
                    return (false, false);
                };
                configs
                    .borrow_mut()
                    .insert(config_file_path.clone(), config.clone());
                if config.file_names().is_empty() {
                    // Likely a solution tsconfig.json - the search will fan out to its references.
                    node.logger
                        .log("Project does not contain file (no root files)");
                    return (false, false);
                }

                if config.compiler_options().composite == Tristate::True {
                    // For composite projects, we can get an early negative result.
                    // !!! what about declaration files in node_modules? wouldn't it be better to
                    //     check project inclusion if the project is already loaded?
                    if !config.file_names_by_path().contains_key(path) {
                        node.logger
                            .log("Project does not contain file (by composite config inclusion)");
                        return (false, false);
                    }
                }

                let Some(project) = self.find_or_create_project(
                    &node.config_file_name,
                    &config_file_path,
                    node.load_kind,
                    node.logger.clone(),
                ) else {
                    node.logger.log("Project does not already exist");
                    return (false, false);
                };

                if node.load_kind == ProjectLoadKind::CREATE {
                    // Ensure project is up to date before checking for file inclusion
                    self.update_program(&*project, node.logger.clone());
                }

                let value = project.value().expect(NIL_DEREF);
                if value.borrow().contains_file(path) {
                    let is_direct_inclusion =
                        !value.borrow().is_source_from_project_reference(path);
                    if node.logger.is_some() {
                        node.logger.logf(&format!(
                            "Project contains file {}",
                            if is_direct_inclusion {
                                "directly"
                            } else {
                                "as a source of a referenced project"
                            }
                        ));
                    }
                    return (true, is_direct_inclusion);
                }

                node.logger.log("Project does not contain file");
                (false, false)
            },
            core_bfs::BreadthFirstSearchOptions {
                visited: Some(visited),
                preprocess_level: Some(&mut |level: &core_bfs::BreadthFirstSearchLevel<
                    SearchNodeKey,
                    SearchNode,
                >| {
                    level.range(&mut |node: &SearchNode| -> bool {
                        if node.load_kind == ProjectLoadKind::FIND
                            && level.has(&SearchNodeKey {
                                config_file_name: node.config_file_name.clone(),
                                load_kind: ProjectLoadKind::CREATE,
                            })
                        {
                            // Remove find requests when a create request for the same project is already present.
                            level.delete(&SearchNodeKey {
                                config_file_name: node.config_file_name.clone(),
                                load_kind: node.load_kind,
                            });
                        }
                        true
                    });
                }),
            },
            &mut |node: &SearchNode| -> SearchNodeKey {
                SearchNodeKey {
                    config_file_name: node.config_file_name.clone(),
                    load_kind: node.load_kind,
                }
            },
        );

        let mut retain: FxHashSet<tspath::Path> = FxHashSet::default();
        let mut project: Option<Rc<dirty::SyncMapEntry<tspath::Path, Rc<RefCell<Project>>>>> = None;
        if !search.path.is_empty() {
            project = self
                .configured_projects
                .load(&(self.to_path)(&search.path[0].config_file_name))
                .0;
            // If we found a project, we retain each project along the BFS path.
            // We don't want to retain everything we visited since BFS can terminate
            // early, and we don't want to retain nondeterministically.
            for node in &search.path {
                retain.insert((self.to_path)(&node.config_file_name));
            }
        }

        if search.stopped {
            // Found a project that directly contains the file.
            return SearchResult { project, retain };
        }

        if project.is_some() {
            // If we found a project that contains the file, but it is a source from
            // a project reference, record it as a fallback.
            fallback = Some(SearchResult {
                project: project.clone(),
                retain: retain.clone(),
            });
        }

        // Look for tsconfig.json files higher up the directory tree and do the same. This handles
        // the common case where a higher-level "solution" tsconfig.json contains all projects in a
        // workspace.
        let disable_solution_searching = matches!(
            configs.borrow().get(&(self.to_path)(config_file_name)),
            Some(config) if config.compiler_options().disable_solution_searching.is_true()
        );
        if disable_solution_searching {
            if let Some(fallback) = fallback {
                return fallback;
            }
        }
        let ancestor_config_name = self
            .config_file_registry_builder
            .get_ancestor_config_file_name(file_name, path, config_file_name, logger.clone());
        if !ancestor_config_name.is_empty() {
            return self.find_or_create_default_configured_project_worker(
                file_name,
                path,
                &ancestor_config_name,
                load_kind,
                Some(visited),
                fallback,
                logger.fork(&format!(
                    "Searching ancestor config file at {}",
                    ancestor_config_name
                )),
            );
        }
        if let Some(fallback) = fallback {
            return fallback;
        }
        // If we didn't find anything, we can retain everything we visited,
        // since the whole graph must have been traversed (i.e., the set of
        // retained projects is guaranteed to be deterministic).
        for node in visited.borrow().iter() {
            retain.insert((self.to_path)(&node.config_file_name));
        }
        SearchResult {
            project: None,
            retain,
        }
    }

    // Go: project/projectcollectionbuilder.go:908 findOrCreateDefaultConfiguredProjectForFile
    pub fn find_or_create_default_configured_project_for_file(
        self: &Rc<Self>,
        file_name: &str,
        path: &tspath::Path,
        load_kind: ProjectLoadKind,
        logger: Option<Rc<logging::LogTree>>,
    ) -> SearchResult {
        let key = self.file_default_projects.borrow().get(path).cloned();
        if let Some(key) = key {
            if key.as_str() == INFERRED_PROJECT_NAME {
                // The file belongs to the inferred project
                return SearchResult::default();
            }
            let (entry, _) = self.configured_projects.load(&key);
            return SearchResult {
                project: entry,
                retain: FxHashSet::default(),
            };
        }
        let config_file_name = self
            .config_file_registry_builder
            .get_config_file_name_for_file(file_name, path, logger.clone());
        if !config_file_name.is_empty() {
            let start_time = Instant::now();
            let result = self.find_or_create_default_configured_project_worker(
                file_name,
                path,
                &config_file_name,
                load_kind,
                None,
                None,
                logger.fork(&format!(
                    "Searching for default configured project for {}",
                    file_name
                )),
            );
            if let Some(project) = &result.project {
                // Go: `if b.fileDefaultProjects == nil { make(...) }` (the port map always exists).
                let config_file_path = project
                    .value()
                    .expect(NIL_DEREF)
                    .borrow()
                    .config_file_path
                    .clone();
                self.file_default_projects
                    .borrow_mut()
                    .insert(path.clone(), config_file_path);
            }
            if logger.is_some() {
                let elapsed = start_time.elapsed();
                if let Some(project) = &result.project {
                    logger.log(&format!(
                        "Found default configured project for {}: {} (in {:?})",
                        file_name,
                        project.value().expect(NIL_DEREF).borrow().config_file_name,
                        elapsed
                    ));
                } else {
                    logger.log(&format!(
                        "No default configured project found for {} (searched in {:?})",
                        file_name, elapsed
                    ));
                }
            }
            return result;
        }
        SearchResult::default()
    }

    // Go: project/projectcollectionbuilder.go:952 findOrCreateProject
    pub fn find_or_create_project(
        self: &Rc<Self>,
        config_file_name: &str,
        config_file_path: &tspath::Path,
        load_kind: ProjectLoadKind,
        logger: Option<Rc<logging::LogTree>>,
    ) -> Option<Rc<dirty::SyncMapEntry<tspath::Path, Rc<RefCell<Project>>>>> {
        if load_kind == ProjectLoadKind::FIND {
            let (entry, _) = self.configured_projects.load(config_file_path);
            return entry;
        }
        // Go evaluates NewConfiguredProject before LoadOrStore, also when the
        // project exists (it logs and takes a watcher id).
        let (entry, _) = self.configured_projects.load_or_store(
            config_file_path.clone(),
            new_configured_project(config_file_name, config_file_path, self, logger),
        );
        entry
    }

    // Go: project/projectcollectionbuilder.go:966 updateInferredProjectRoots
    // PORT: Go sorts the caller's slice in place; the callers never read it
    // again, so the port takes the `Vec` by value.
    pub fn update_inferred_project_roots(
        self: &Rc<Self>,
        mut root_file_names: Vec<String>,
        logger: Option<Rc<logging::LogTree>>,
    ) -> bool {
        if root_file_names.is_empty() {
            if self.inferred_project.value().is_some() {
                if logger.is_some() {
                    logger.log("Deleting inferred project");
                }
                self.inferred_project.delete();
                return true;
            }
            return false;
        }

        root_file_names.sort();
        if self.inferred_project.value().is_none() {
            self.inferred_project.set(new_inferred_project(
                &self.session_options.current_directory,
                self.compiler_options_for_inferred_projects.clone(),
                &root_file_names,
                self,
                logger,
            ));
        } else {
            let mut new_compiler_options = self
                .inferred_project
                .value()
                .expect(NIL_DEREF)
                .borrow()
                .command_line
                .as_ref()
                .expect(NIL_DEREF)
                .compiler_options()
                .clone();
            if let Some(compiler_options) = &self.compiler_options_for_inferred_projects {
                new_compiler_options = compiler_options.clone();
            }
            let new_command_line = Rc::new(tsoptions::new_parsed_command_line(
                new_compiler_options,
                root_file_names.clone(),
                tspath::ComparePathsOptions {
                    use_case_sensitive_file_names: self.fs.fs.use_case_sensitive_file_names(),
                    current_directory: self.session_options.current_directory.clone(),
                },
            ));
            let changed = self.inferred_project.change_if(
                &mut |p: Option<&Rc<RefCell<Project>>>| -> bool {
                    let p = p.expect(NIL_DEREF).borrow();
                    p.command_line
                        .as_ref()
                        .expect(NIL_DEREF)
                        .file_names_by_path()
                        != new_command_line.file_names_by_path()
                },
                &mut |p: &Rc<RefCell<Project>>| {
                    if logger.is_some() {
                        logger.log(&format!(
                            "Updating inferred project config with {} root files",
                            root_file_names.len()
                        ));
                    }
                    p.borrow_mut()
                        .set_command_line(Some(new_command_line.clone()));
                },
            );
            if !changed {
                return false;
            }
        }
        true
    }

    // Go: project/projectcollectionbuilder.go:1010 updateProgram
    // updateProgram updates the program for the given project entry if necessary. It returns
    // a boolean indicating whether the update could have caused any structure-affecting changes.
    pub fn update_program(
        self: &Rc<Self>,
        entry: &dyn dirty::Value<Rc<RefCell<Project>>>,
        logger: Option<Rc<logging::LogTree>>,
    ) -> bool {
        let mut update_program = false;
        let mut delete_project = false;
        let mut files_changed = false;
        let config_file_name = entry
            .value()
            .expect(NIL_DEREF)
            .borrow()
            .config_file_name
            .clone();
        let start_time = Instant::now();
        let mut notified_loading = false;
        let mut display_name = String::new();
        entry.locked(&mut |entry: &dyn dirty::Value<Rc<RefCell<Project>>>| {
            let value = entry.value().expect(NIL_DEREF);
            if value.borrow().kind == Kind::CONFIGURED {
                let (value_config_file_name, value_config_file_path) = {
                    let value = value.borrow();
                    (
                        value.config_file_name.clone(),
                        value.config_file_path.clone(),
                    )
                };
                let command_line = self
                    .config_file_registry_builder
                    .acquire_config_for_project(
                        &value_config_file_name,
                        &value_config_file_path,
                        &value,
                        logger.fork("Acquiring config for project"),
                    );
                let Some(command_line) = command_line else {
                    delete_project = true;
                    files_changed = true;
                    return;
                };
                // Go: pointer compare `entry.Value().CommandLine != commandLine`.
                let same_command_line = matches!(
                    &entry.value().expect(NIL_DEREF).borrow().command_line,
                    Some(current) if Rc::ptr_eq(current, &command_line)
                );
                if !same_command_line {
                    update_program = true;
                    entry.change(&mut |p: &Rc<RefCell<Project>>| {
                        p.borrow_mut().set_command_line(Some(command_line.clone()));
                    });
                }
            }
            if !update_program {
                update_program = entry.value().expect(NIL_DEREF).borrow().dirty;
            }
            if update_program && self.client.is_some() {
                display_name = entry
                    .value()
                    .expect(NIL_DEREF)
                    .borrow()
                    .display_name(&self.session_options.current_directory);
                notified_loading = true;
            }
        });
        if notified_loading {
            if let Some(client) = &self.client {
                client.progress_start(diag::Project_0, args![display_name]);
            }
        }
        if delete_project {
            self.delete_configured_project(entry, logger.clone());
        }
        if update_program {
            entry.locked(&mut |entry: &dyn dirty::Value<Rc<RefCell<Project>>>| {
                entry.change(&mut |project: &Rc<RefCell<Project>>| {
                    let (old_host, old_program, old_checker_pool, current_directory) = {
                        let p = project.borrow();
                        (
                            p.host.clone(),
                            p.program,
                            p.checker_pool.clone(),
                            p.current_directory.clone(),
                        )
                    };
                    let host = new_compiler_host(
                        &current_directory,
                        project,
                        self,
                        logger.fork("CompilerHost"),
                    );
                    project.borrow_mut().host = Some(host);
                    // PORT: no mutable borrow is held while the program is
                    // built (the compiler host reads the project).
                    let result = project.borrow().create_program();
                    // PORT: Go `result.Program.GetCheckerPool().(*checkerPool)`.
                    // `ls_program::CheckerPool` has no `Any` view, so
                    // CreateProgram returns the pool its CreateCheckerPool
                    // closure made for this program (project.rs). `None` is
                    // the failed Go type assertion.
                    let checker_pool = result.checker_pool.clone().unwrap_or_else(|| {
                        panic!(
                            "interface conversion: compiler.CheckerPool is not *project.checkerPool"
                        )
                    });
                    let mut p = project.borrow_mut();
                    p.program = Some(result.program);
                    p.checker_pool = Some(checker_pool);
                    p.program_update_kind = result.update_kind;
                    p.program_last_update = self.new_snapshot_id;
                    if result.update_kind == ProgramUpdateKind::CLONED {
                        let seen_files = old_host
                            .as_ref()
                            .expect(NIL_DEREF)
                            .source_fs
                            .seen_files
                            .borrow()
                            .clone();
                        *p.host
                            .as_ref()
                            .expect(NIL_DEREF)
                            .source_fs
                            .seen_files
                            .borrow_mut() = seen_files;
                    }
                    if result.update_kind == ProgramUpdateKind::NEW_FILES {
                        files_changed = true;
                        let program_files_watch = p.clone_watchers();
                        p.program_files_watch = program_files_watch;
                    }
                    p.dirty = false;
                    p.dirty_file_path = tspath::Path::default();
                    let project_path = p.config_file_path.clone();
                    drop(p);
                    self.release_dropped_project_references(
                        old_program,
                        Some(result.program),
                        &project_path,
                    );
                    if let Some(old_checker_pool) = old_checker_pool {
                        old_checker_pool.discard();
                    }
                });
            });
        }
        if notified_loading {
            if let Some(client) = &self.client {
                client.progress_finish(diag::Project_0, args![display_name]);
            }
        }
        if update_program && logger.is_some() {
            let elapsed = start_time.elapsed();
            logger.log(&format!(
                "Program update for {} completed in {:?}",
                config_file_name, elapsed
            ));
        }
        files_changed
    }

    // Go: project/projectcollectionbuilder.go:1090 markFilesChanged
    // PORT: the two Go closures share `dirty` and `dirtyFilePath`, so they
    // are a `Cell` and a `RefCell`.
    pub fn mark_files_changed(
        self: &Rc<Self>,
        entry: &dyn dirty::Value<Rc<RefCell<Project>>>,
        paths: &[tspath::Path],
        change_type: lsproto::FileChangeType,
        logger: Option<Rc<logging::LogTree>>,
    ) {
        let dirty = Cell::new(false);
        let dirty_file_path: RefCell<tspath::Path> = RefCell::new(tspath::Path::default());
        entry.change_if(
            &mut |p: Option<&Rc<RefCell<Project>>>| -> bool {
                let p = p.expect(NIL_DEREF).borrow();
                if p.program.is_none() || p.dirty && p.dirty_file_path.is_empty() {
                    return false;
                }

                *dirty_file_path.borrow_mut() = p.dirty_file_path.clone();
                for path in paths {
                    if p.contains_file(path) {
                        dirty.set(true);
                        if change_type == lsproto::FileChangeType::DELETED {
                            *dirty_file_path.borrow_mut() = tspath::Path::default();
                            break;
                        }
                        // package.json changes can affect module resolution and package
                        // identity (e.g. dedup decisions), so they must always trigger
                        // a full rebuild rather than a single-file clone.
                        if tspath::get_base_file_name(path) == "package.json" {
                            *dirty_file_path.borrow_mut() = tspath::Path::default();
                            break;
                        }
                        let current = dirty_file_path.borrow().clone();
                        if current.is_empty() {
                            *dirty_file_path.borrow_mut() = path.clone();
                        } else if current != *path {
                            *dirty_file_path.borrow_mut() = tspath::Path::default();
                            break;
                        }
                    } else if let Some(host) = &p.host {
                        if change_type == lsproto::FileChangeType::CREATED
                            && host.source_fs.seen_file_or_missing_parent_directory(path)
                            || change_type != lsproto::FileChangeType::CREATED
                                && host.source_fs.seen_file(path)
                        {
                            dirty.set(true);
                            *dirty_file_path.borrow_mut() = tspath::Path::default();
                            break;
                        }
                    }
                }
                dirty.get() || p.dirty_file_path != *dirty_file_path.borrow()
            },
            &mut |p: &Rc<RefCell<Project>>| {
                let mut p = p.borrow_mut();
                p.dirty = true;
                p.dirty_file_path = dirty_file_path.borrow().clone();
                if logger.is_some() {
                    let dirty_file_path = dirty_file_path.borrow();
                    if !dirty_file_path.is_empty() {
                        logger.logf(&format!(
                            "Marking project {} as dirty due to changes in {}",
                            p.config_file_name, dirty_file_path
                        ));
                    } else {
                        logger.logf(&format!("Marking project {} as dirty", p.config_file_name));
                    }
                }
            },
        );
    }

    // Go: project/projectcollectionbuilder.go:1144 deleteConfiguredProject
    pub fn delete_configured_project(
        self: &Rc<Self>,
        project: &dyn dirty::Value<Rc<RefCell<Project>>>,
        logger: Option<Rc<logging::LogTree>>,
    ) {
        let (project_path, config_file_name, program) = {
            let value = project.value().expect(NIL_DEREF);
            let value = value.borrow();
            (
                value.config_file_path.clone(),
                value.config_file_name.clone(),
                value.program,
            )
        };
        if logger.is_some() {
            logger.log(&format!(
                "Deleting configured project: {}",
                config_file_name
            ));
        }
        if let Some(program) = program {
            program.range_resolved_project_reference(
                |reference_path: &tspath::Path, _config, _, _| -> bool {
                    self.config_file_registry_builder
                        .release_config_for_project(reference_path, &project_path);
                    true
                },
            );
        }
        self.config_file_registry_builder
            .release_config_for_project(&project_path, &project_path);
        project.delete();
    }

    // Go: project/projectcollectionbuilder.go:1242 releaseDroppedProjectReferences
    // releaseDroppedProjectReferences releases the config entries for project references
    // that were present in oldProgram but are no longer referenced by newProgram. Creating
    // newProgram already re-acquires the config for every reference it still resolves, so
    // only the dropped references need to be released here.
    pub fn release_dropped_project_references(
        &self,
        old_program: Option<&'static compiler::NewProgram>,
        new_program: Option<&'static compiler::NewProgram>,
        project_path: &tspath::Path,
    ) {
        let Some(old_program) = old_program else {
            return;
        };
        if new_program.is_some_and(|new_program| std::ptr::eq(old_program, new_program)) {
            return;
        }
        let mut new_references: FxHashSet<tspath::Path> = FxHashSet::default();
        if let Some(new_program) = new_program {
            new_program.range_resolved_project_reference(
                |reference_path: &tspath::Path, _, _, _| -> bool {
                    new_references.insert(reference_path.clone());
                    true
                },
            );
        }
        old_program.range_resolved_project_reference(
            |reference_path: &tspath::Path, _, _, _| -> bool {
                if !new_references.contains(reference_path) {
                    self.config_file_registry_builder
                        .release_config_for_project(reference_path, project_path);
                }
                true
            },
        );
    }
}

// Go: project/projectcollectionbuilder.go:271 isReferencedBy (closure in DidChangeFiles)
// PORT: Go defines this closure and never calls it (it only calls itself);
// it is kept for the literal port. Go `*collections.Set[*Project]` is a set
// of project addresses.
fn is_referenced_by(
    b: &Rc<ProjectCollectionBuilder>,
    project: &Rc<RefCell<Project>>,
    ref_path: &tspath::Path,
    seen_projects: &mut FxHashSet<usize>,
) -> bool {
    if !seen_projects.insert(Rc::as_ptr(project) as usize) {
        return false;
    }

    let project = project.borrow();
    if let Some(potential_project_references) = &project.potential_project_references {
        for potential_ref in potential_project_references.iter() {
            if potential_ref == ref_path {
                return true;
            }
        }
        for potential_ref in potential_project_references.iter() {
            if let (Some(ref_project), true) = b.configured_projects.load(potential_ref) {
                if is_referenced_by(
                    b,
                    &ref_project.value().expect(NIL_DEREF),
                    ref_path,
                    seen_projects,
                ) {
                    return true;
                }
            }
        }
    } else if let Some(program) = project.program {
        // PORT: Go `project.GetProgram()` is the field read.
        if !program.range_resolved_project_reference(
            |reference_path: &tspath::Path, _, _, _| -> bool { reference_path != ref_path },
        ) {
            return true;
        }
    }
    false
}

// Go: project/projectcollectionbuilder.go:347 logChangeFileResult
// PORT: Go passes the result by value; here by reference.
pub fn log_change_file_result(result: &ChangeFileResult, logger: &Option<Rc<logging::LogTree>>) {
    if !result.affected_projects.is_empty() {
        logger.logf(&format!(
            "Config file change affected projects: {:?}",
            result.affected_projects.iter().collect::<Vec<_>>()
        ));
    }
    if !result.affected_files.is_empty() {
        logger.logf(&format!(
            "Config file change affected config file lookups for {} files",
            result.affected_files.len()
        ));
    }
}

// Go: project/projectcollectionbuilder.go:734 searchNode
#[derive(Clone)]
pub struct SearchNode {
    pub config_file_name: String,
    pub load_kind: ProjectLoadKind,
    pub logger: Option<Rc<logging::LogTree>>,
}

// Go: project/projectcollectionbuilder.go:740 searchNodeKey
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct SearchNodeKey {
    pub config_file_name: String,
    pub load_kind: ProjectLoadKind,
}

// Go: project/projectcollectionbuilder.go:745 searchResult
#[derive(Clone, Default)]
pub struct SearchResult {
    pub project: Option<Rc<dirty::SyncMapEntry<tspath::Path, Rc<RefCell<Project>>>>>,
    pub retain: FxHashSet<tspath::Path>,
}
