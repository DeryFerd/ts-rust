//! Go: execute/build/orchestrator.go:239-510, the watch part of the build
//! orchestrator (`Watch`, `updateWatch`, `resetCaches`,
//! `checkTasksForEventChanges`, `computeDesiredWatches`, `DoCycle`), with
//! `rangeTask` (orchestrator.go:540) for these callers, and
//! execute/build/buildtask.go:698-717 (`updateWatch`, `resetConfig`).
//!
//! PORT: Go runs `DoCycle` from `WatchManager.RunLoop` on the goroutine
//! that called `Watch`. The port does the same on the orchestrator thread.
//! The watch manager is `Rc<RefCell<WatchManager>>` (see orchestrator.rs):
//! the loop keeps a shared borrow while `do_cycle` borrows the orchestrator
//! mutably, and `do_cycle` only takes shared borrows of the manager.
//!
//! PORT: Go `task.reportDone` and `task.done` channels are dropped (see
//! build_task.rs), so the lines that make new ones are left out. Go
//! `atomic.Bool` flags on one goroutine are plain `bool`s.
//!
//! PORT: each project compiles in this process (build_task.rs). A watch
//! cycle makes new program versions, and each is released when its task
//! reports. The old program is read from build info, as Go does in build
//! mode (buildtask.go:199).

use crate::execute::build::build_task::BuildTask;
use crate::execute::build::orchestrator::Orchestrator;
use crate::execute::tsc::compile::{Watcher, write_str};
use crate::execute::watchmanager::{can_watch_directory, is_dir_covered_by_watch};
use crate::frontend::prelude::*;
use crate::fswatch;
use crate::gostd::Context;
use std::sync::PoisonError;
use std::time::SystemTime;

impl Orchestrator {
    // Go: build/orchestrator.go:239 (*Orchestrator).Watch
    pub fn watch(&mut self, ctx: &Context) {
        self.wm.borrow().lock();

        if self.opts.testing.is_none() {
            if !self
                .opts
                .sys
                .get_environment_variable("TS_WATCH_DEBUG")
                .is_empty()
            {
                self.wm.borrow_mut().debug_log = Some(self.opts.sys.writer());
            }
            self.wm.borrow_mut().ensure_default_backend();
        }

        self.update_watch();
        let desired_dirs = self.compute_desired_watches();
        let reconciled = self.wm.borrow().reconcile_watches(&desired_dirs);
        if let Err(err) = reconciled {
            write_str(&self.opts.sys.writer(), &format!("{}\n", err.error()));
            self.wm.borrow().force_overflow();
        }
        self.reset_caches();

        self.wm.borrow().unlock();

        if self.opts.testing.is_none() {
            // PORT: Go passes the method value `o.DoCycle`.
            let wm = Rc::clone(&self.wm);
            wm.borrow().run_loop(ctx, &mut || self.do_cycle());
        }
    }

    // Go: build/orchestrator.go:264 (*Orchestrator).updateWatch
    pub fn update_watch(&self) {
        let old_cache = std::mem::take(
            &mut *self
                .host
                .m_times
                .lock()
                .unwrap_or_else(PoisonError::into_inner),
        );
        self.range_task(&mut |_path: &Path, task: &Rc<RefCell<BuildTask>>| {
            task.borrow().update_watch(self, &old_cache);
        });
    }

    // Go: build/orchestrator.go:272 (*Orchestrator).resetCaches
    pub fn reset_caches(&self) {
        // Clean out all the caches
        // PORT: Go reaches the cached file system as
        // `o.host.host.FS().(*cachedvfs.FS)`; the host keeps it as
        // `cached_fs` (host.rs).
        self.host.cached_fs.clear_cache();
        self.host.extended_config_cache.reset();
        self.host.source_files.reset();
        *self.host.config_times.borrow_mut() = FxHashMap::default();
    }

    // Go: build/orchestrator.go:281 (*Orchestrator).checkTasksForEventChanges
    // PORT: Go map iteration order is random; `changed_paths` is an
    // `FxHashMap`. The result does not depend on the order.
    pub fn check_tasks_for_event_changes(
        &self,
        changed_paths: &FxHashMap<String, fswatch::EventKind>,
        needs_config_update: &mut bool,
        needs_update: &mut bool,
    ) {
        let mut normalized_paths: FxHashMap<Path, fswatch::EventKind> =
            FxHashMap::with_capacity_and_hasher(changed_paths.len(), Default::default());
        for (event_path, kind) in changed_paths {
            normalized_paths.insert(self.to_path(event_path), *kind);
        }

        for config in &self.order {
            let path = self.to_path(config);
            let task = self.get_task(&path);
            let mut task = task.borrow_mut();

            let config_path = self.to_path(&task.config);
            if normalized_paths.contains_key(&config_path) {
                task.reset_config(self, &path);
                *needs_config_update = true;
                *needs_update = true;
                continue;
            }

            let Some(resolved) = task.resolved.clone() else {
                continue;
            };

            let mut config_changed = false;
            for file in resolved.extended_source_files() {
                let fp = self.to_path(file);
                if normalized_paths.contains_key(&fp) {
                    task.reset_config(self, &path);
                    *needs_config_update = true;
                    *needs_update = true;
                    config_changed = true;
                    break;
                }
            }
            if config_changed {
                continue;
            }

            let mut root_changed = false;
            let file_names = resolved.file_names();
            let mut roots: FxHashSet<Path> =
                FxHashSet::with_capacity_and_hasher(file_names.len(), Default::default());
            for file in file_names {
                let fp = self.to_path(file);
                roots.insert(fp.clone());
                if !root_changed && normalized_paths.contains_key(&fp) {
                    task.reset_status();
                    *needs_update = true;
                    root_changed = true;
                }
            }

            if !root_changed {
                // PORT: Go reads the entry under `buildInfoEntryMu`; one
                // thread here.
                let bi = task.build_info_entry.clone();
                if let Some(bi) = bi {
                    if let Some(build_info) = &bi.build_info {
                        let build_info_dir = get_directory_path(bi.path.as_str());
                        for file_name in build_info.file_names.iter().flatten() {
                            let fp = self.to_path(
                                &self.resolve_build_info_file_name(file_name, &build_info_dir),
                            );
                            if roots.contains(&fp) {
                                continue;
                            }
                            if normalized_paths.contains_key(&fp) {
                                task.reset_status();
                                *needs_update = true;
                                break;
                            }
                        }
                        for package_json in build_info.get_package_jsons(&build_info_dir) {
                            if self.package_json_lookup_changed(&package_json, &normalized_paths) {
                                task.reset_status();
                                *needs_update = true;
                                break;
                            }
                        }
                        for package_json in build_info.get_missing_package_jsons(&build_info_dir) {
                            if self.package_json_lookup_changed(&package_json, &normalized_paths) {
                                task.reset_status();
                                *needs_update = true;
                                break;
                            }
                        }
                    }
                }
                let package_jsons = task.package_jsons.clone();
                for package_json in &package_jsons {
                    if self.package_json_lookup_changed(package_json, &normalized_paths) {
                        task.reset_status();
                        *needs_update = true;
                        break;
                    }
                }
            }

            // PORT: Go makes new `task.reportDone` and `task.done` channels
            // here (see top).

            let new_config = Rc::new(
                resolved.reload_file_names_of_parsed_command_line(&*CompilerHost::fs(&*self.host)),
            );
            if resolved.file_names() != new_config.file_names() {
                self.host
                    .resolved_references
                    .store(path.clone(), Some(new_config.clone()));
                task.resolved = Some(new_config);
                task.reset_status();
                *needs_update = true;
            }
        }

        if !*needs_update {
            let opts = &self.compare_paths_options;
            let fs = CompilerHost::fs(&*self.host);
            for event_path in changed_paths.keys() {
                if fs.directory_exists(event_path)
                    && self.wm.borrow().is_path_under_watch(event_path, opts)
                {
                    self.range_task(&mut |_path: &Path, task: &Rc<RefCell<BuildTask>>| {
                        task.borrow_mut().reset_status();
                        // PORT: Go makes new `task.reportDone` and
                        // `task.done` channels here (see top).
                    });
                    *needs_update = true;
                    break;
                }
            }
        }
    }

    // Go: build/orchestrator.go:406 (*Orchestrator).packageJsonLookupChanged
    // PORT: Go ranges over a map (random order); the result does not depend
    // on the order.
    fn package_json_lookup_changed(
        &self,
        package_json: &str,
        changed_paths: &FxHashMap<Path, fswatch::EventKind>,
    ) -> bool {
        let package_json_path = self.to_path(package_json);
        if changed_paths.contains_key(&package_json_path) {
            return true;
        }
        for (changed_path, kind) in changed_paths {
            if *kind == fswatch::EventKind::Delete
                && contains_path(
                    changed_path.as_str(),
                    package_json_path.as_str(),
                    &self.compare_paths_options,
                )
            {
                return true;
            }
        }
        false
    }

    // Go: build/orchestrator.go:419 (*Orchestrator).computeDesiredWatches
    // PORT: Go ranges over `WildcardDirectories()` (a map, random order);
    // the result does not depend on the order.
    pub fn compute_desired_watches(&self) -> FxHashMap<String, bool> {
        let mut desired_dirs: FxHashMap<String, bool> = FxHashMap::default();
        let fs = CompilerHost::fs(&*self.host);

        for config in &self.order {
            let path = self.to_path(config);
            let task = self.get_task(&path);
            let task = task.borrow();

            // Watch config file directory
            let config_dir = get_directory_path(&task.config);
            let real_config_dir = fs.realpath(&config_dir);
            if !desired_dirs.contains_key(&real_config_dir) {
                desired_dirs.insert(real_config_dir, false);
            }

            let Some(resolved) = &task.resolved else {
                continue;
            };

            // Extended config file directories
            for cfg_path in resolved.extended_source_files() {
                let real_path = fs.realpath(cfg_path);
                let dir = get_directory_path(&real_path);
                if !desired_dirs.contains_key(&dir) {
                    desired_dirs.insert(dir, false);
                }
            }

            // Wildcard directories from tsconfig
            for (dir, recursive) in resolved.wildcard_directories() {
                let real_dir = fs.realpath(dir);
                if let Some(existing) = desired_dirs.get(&real_dir).copied() {
                    desired_dirs.insert(real_dir, existing || *recursive);
                } else {
                    desired_dirs.insert(real_dir, *recursive);
                }
            }

            // Input file directories not already covered
            for file_name in resolved.file_names() {
                let abs_path =
                    get_normalized_absolute_path(file_name, &self.opts.sys.get_current_directory());
                let dir = get_directory_path(&abs_path);
                if !is_dir_covered_by_watch(&desired_dirs, &dir, &self.compare_paths_options)
                    && can_watch_directory(&dir)
                {
                    desired_dirs.insert(dir, false);
                }
            }

            // Non-root dependency directories from buildinfo (e.g. node_modules .d.ts files).
            // PORT: Go reads the entry under `buildInfoEntryMu`; one thread here.
            let bi = task.build_info_entry.clone();
            if let Some(bi) = bi {
                if let Some(build_info) = &bi.build_info {
                    let build_info_dir = get_directory_path(bi.path.as_str());
                    let roots: FxHashSet<Path> = resolved
                        .file_names()
                        .iter()
                        .map(|file_name| self.to_path(file_name))
                        .collect();
                    for file_name in build_info.file_names.iter().flatten() {
                        let abs_path = fs.realpath(
                            &self.resolve_build_info_file_name(file_name, &build_info_dir),
                        );
                        let fp = self.to_path(&abs_path);
                        if roots.contains(&fp) {
                            continue;
                        }
                        let dir = get_directory_path(&abs_path);
                        if !is_dir_covered_by_watch(
                            &desired_dirs,
                            &dir,
                            &self.compare_paths_options,
                        ) && can_watch_directory(&dir)
                        {
                            desired_dirs.insert(dir, false);
                        }
                    }
                    for package_json in build_info.get_package_jsons(&build_info_dir) {
                        self.add_package_json_watch_dirs(&mut desired_dirs, &package_json);
                    }
                    for package_json in build_info.get_missing_package_jsons(&build_info_dir) {
                        self.add_package_json_watch_dirs(&mut desired_dirs, &package_json);
                    }
                }
            }
            for package_json in &task.package_jsons {
                self.add_package_json_watch_dirs(&mut desired_dirs, package_json);
            }
        }

        self.wm.borrow().resolve_desired_dirs(&desired_dirs)
    }

    // Go: build/orchestrator.go:503 (*Orchestrator).addWatchDir
    fn add_watch_dir(&self, desired_dirs: &mut FxHashMap<String, bool>, dir: &str) {
        if !is_dir_covered_by_watch(desired_dirs, dir, &self.compare_paths_options)
            && can_watch_directory(dir)
        {
            desired_dirs.insert(dir.to_string(), false);
        }
    }

    // Go: build/orchestrator.go:509 (*Orchestrator).addPackageJsonWatchDirs
    fn add_package_json_watch_dirs(
        &self,
        desired_dirs: &mut FxHashMap<String, bool>,
        package_json: &str,
    ) {
        let dir = get_directory_path(package_json);
        let mut dirs = vec![dir.clone()];
        let mut found_node_modules = false;
        let mut current = dir.clone();
        loop {
            let parent = get_directory_path(&current);
            if parent.is_empty() || parent == current {
                break;
            }
            dirs.push(parent.clone());
            if get_base_file_name(&parent) == "node_modules" {
                found_node_modules = true;
                let grandparent = get_directory_path(&parent);
                if !grandparent.is_empty() && grandparent != parent {
                    dirs.push(grandparent);
                }
                break;
            }
            current = parent;
        }

        if !found_node_modules {
            self.add_watch_dir(desired_dirs, &dir);
            return;
        }
        for dir in &dirs {
            self.add_watch_dir(desired_dirs, dir);
        }
    }

    // Go: build/orchestrator.go:459 (*Orchestrator).DoCycle
    // PORT: Go unlocks with `defer`; the port unlocks before each return.
    pub fn do_cycle(&mut self) {
        self.wm.borrow().lock();

        let (changed_paths, overflow) = self.wm.borrow().drain_events();
        let has_events = !changed_paths.is_empty() || overflow;

        if !has_events {
            if let Some(debug_log) = &self.wm.borrow().debug_log {
                write_str(debug_log, "[watch] DoCycle: no events, skipping\n");
            }
            self.wm.borrow().unlock();
            return;
        }

        let mut needs_config_update = false;
        let mut needs_update = false;

        if overflow {
            // Overflow: reset all tasks to force a full rebuild.
            let this: &Orchestrator = self;
            this.range_task(&mut |path: &Path, task: &Rc<RefCell<BuildTask>>| {
                task.borrow_mut().reset_config(this, path);
                // PORT: Go makes new `task.reportDone` and `task.done`
                // channels here (see top).
            });
            needs_config_update = true;
            needs_update = true;
        } else {
            // Event-driven: check only tasks affected by changed paths
            self.check_tasks_for_event_changes(
                &changed_paths,
                &mut needs_config_update,
                &mut needs_update,
            );
        }

        if !needs_update {
            self.reset_caches();
            self.wm.borrow().unlock();
            return;
        }

        (self
            .watch_status_reporter
            .as_ref()
            .expect("watch status reporter"))(&new_compiler_diagnostic(
            diag::File_change_detected_Starting_incremental_compilation,
            args![],
        ));
        if needs_config_update {
            // Generate new tasks
            self.generate_graph_reusing_old_tasks();
        }

        self.build_or_clean();
        self.update_watch();
        let desired_dirs = self.compute_desired_watches();
        let reconciled = self.wm.borrow().reconcile_watches(&desired_dirs);
        if let Err(err) = reconciled {
            write_str(&self.opts.sys.writer(), &format!("{}\n", err.error()));
            // Mark overflow so the next event triggers a full rebuild
            self.wm.borrow().force_overflow();
        }
        self.reset_caches();
        self.wm.borrow().unlock();
    }

    // Go: build/orchestrator.go:540 (*Orchestrator).rangeTask
    // PORT: the build itself uses `build_all_tasks` (orchestrator.rs). The
    // watch callers pass an `f` that touches only its own task and the host
    // caches, so the tasks run one at a time in `order`, the order in which
    // Go's goroutines take them. With `numRoutines <= 0` Go starts no
    // goroutine and runs no task; that is kept.
    pub(crate) fn range_task(&self, f: &mut dyn FnMut(&Path, &Rc<RefCell<BuildTask>>)) {
        if self.num_routines() <= 0 {
            return;
        }
        for config in &self.order {
            let path = self.to_path(config);
            let task = self.get_task(&path);
            f(&path, &task);
        }
    }
}

// Go: build/orchestrator.go:78 `var _ tsc.Watcher = (*Orchestrator)(nil)`
impl Watcher for Orchestrator {
    fn do_cycle(&mut self) {
        Orchestrator::do_cycle(self);
    }
}

impl BuildTask {
    // Go: build/buildtask.go:698 (*BuildTask).updateWatch
    // PORT: Go takes the old `*SyncMap`; the old map is passed by reference.
    pub fn update_watch(
        &self,
        orchestrator: &Orchestrator,
        old_cache: &FxHashMap<Path, Option<SystemTime>>,
    ) {
        if let Some(resolved) = &self.resolved {
            if self.can_update_js_dts_output_timestamps() {
                for output_file in resolved.get_output_file_names() {
                    orchestrator
                        .host
                        .store_m_time_from_old_cache(&output_file, old_cache);
                }
            }
        }
    }

    // Go: build/buildtask.go:714 (*BuildTask).resetConfig
    pub fn reset_config(&mut self, orchestrator: &Orchestrator, path: &Path) {
        self.dirty = true;
        orchestrator.host.resolved_references.delete(path);
    }
}
