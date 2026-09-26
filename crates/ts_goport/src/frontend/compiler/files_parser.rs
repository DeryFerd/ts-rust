//! Go: compiler/filesparser.go (parse tasks, the files parser and
//! `getProcessedFiles`).

use crate::frontend::prelude::*;
use std::sync::{Arc, Condvar, Mutex};

// Go: filesparser.go:19 parseTask
// PORT: Go `*parseTask` is shared by the root task list, sub task lists,
// `parseTaskData.tasks` and `loadedTask`, and changed through all of them.
// It is `Rc<RefCell<ParseTask>>` (`ParseTaskRef`).
#[derive(Default)]
pub struct ParseTask {
    pub normalized_file_path: String,
    pub path: Path,
    pub file: Option<Rc<ParsedSourceFile>>,
    pub lib_file: Option<Rc<LibFile>>,
    pub redirected_parse_task: Option<ParseTaskRef>,
    pub sub_tasks: Vec<ParseTaskRef>,
    pub loaded: bool,
    pub started_sub_tasks: bool,
    pub is_for_automatic_type_directive: bool,
    pub include_reason: Option<Rc<FileIncludeReason>>,
    pub package_id: PackageId,

    pub metadata: SourceFileMetaData,
    pub resolutions_in_file: ModeAwareCache<Rc<ResolvedModule>>,
    pub resolutions_trace: Vec<DiagAndArgs>,
    pub type_resolutions_in_file: ModeAwareCache<Rc<ResolvedTypeReferenceDirective>>,
    pub type_resolutions_trace: Vec<DiagAndArgs>,
    pub resolution_diagnostics: Vec<Diagnostic>,
    pub processing_diagnostics: Vec<Rc<ProcessingDiagnostic>>,
    pub import_helpers_import_specifier: Node,
    pub jsx_runtime_import_specifier: Option<Rc<JsxRuntimeImportSpecifier>>,

    pub increase_depth: bool,
    pub elide_on_depth: bool,

    pub loaded_task: Option<ParseTaskRef>,
    pub all_include_reasons: Vec<Rc<FileIncludeReason>>,
}

/// Go `*parseTask`.
pub type ParseTaskRef = Rc<RefCell<ParseTask>>;

impl ParseTask {
    // Go: filesparser.go:49 (*parseTask).FileName
    pub fn file_name(&self) -> String {
        self.normalized_file_path.clone()
    }

    // Go: filesparser.go:53 (*parseTask).Path
    pub fn path(&self) -> Path {
        self.path.clone()
    }

    // Go: filesparser.go:57 (*parseTask).load
    pub fn load(&mut self, loader: &FileLoader) {
        self.loaded = true;
        if self.is_for_automatic_type_directive {
            self.load_automatic_type_directives(loader);
            return;
        }
        // PORT: tracing is skipped.
        let redirect = loader
            .project_reference_file_mapper
            .borrow()
            .get_parse_file_redirect(&new_has_file_name(&self.normalized_file_path, &self.path));
        if !redirect.is_empty() {
            self.redirect(loader, &redirect);
            return;
        }

        if has_extension(&self.normalized_file_path) {
            let compiler_options = loader.opts.config.compiler_options();
            let allow_non_ts_extensions = compiler_options.allow_non_ts_extensions.is_true();
            if !allow_non_ts_extensions {
                let canonical_file_name = get_canonical_file_name(
                    &self.normalized_file_path,
                    loader.opts.host.fs().use_case_sensitive_file_names(),
                );
                if !loader.is_supported_extension(&canonical_file_name) {
                    if has_js_file_extension(&canonical_file_name) {
                        self.processing_diagnostics.push(new_explaining_processing_diagnostic(
                            self.include_reason.clone(),
                            diag::File_0_is_a_JavaScript_file_Did_you_mean_to_enable_the_allowJs_option,
                            args![self.normalized_file_path.clone()],
                        ));
                    } else {
                        self.processing_diagnostics.push(new_explaining_processing_diagnostic(
                            self.include_reason.clone(),
                            diag::File_0_has_an_unsupported_extension_The_only_supported_extensions_are_1,
                            args![
                                self.normalized_file_path.clone(),
                                format!("'{}'", join_flattened_extensions(&loader.supported_extensions))
                            ],
                        ));
                    }
                    return;
                }
            }
        }

        loader
            .total_file_count
            .set(loader.total_file_count.get() + 1);
        if self.lib_file.is_some() {
            loader.lib_file_count.set(loader.lib_file_count.get() + 1);
            // Default lib files are all scripts; we can safely skip looking up their package.json
            // to avoid adding spurious lookups to file watcher tracking.
            self.metadata = SourceFileMetaData {
                implied_node_format: ModuleKind::COMMON_JS,
                ..Default::default()
            };
        } else {
            self.metadata = loader.load_source_file_meta_data(&self.normalized_file_path);
        }

        let Some(file) = loader.parse_source_file(self) else {
            return;
        };

        self.file = Some(file.clone());
        self.sub_tasks = Vec::with_capacity(
            file.referenced_files.len() + file.imports.len() + file.module_augmentations.len(),
        );

        let compiler_options = loader.opts.config.compiler_options();
        if !compiler_options.no_resolve.is_true() {
            for (index, ref_) in file.referenced_files.iter().enumerate() {
                let (resolved_ref, processing_diagnostic) = loader
                    .resolve_tripleslash_path_reference(
                        &ref_.file_name,
                        &file.file_name(),
                        index as i32,
                    );
                if let Some(processing_diagnostic) = processing_diagnostic {
                    self.processing_diagnostics.push(processing_diagnostic);
                    continue;
                }
                self.add_sub_task(
                    resolved_ref.expect("resolved reference without a diagnostic"),
                    None,
                );
            }

            loader.resolve_type_reference_directives(self);
        }

        if compiler_options.no_lib != Tristate::True {
            for (index, lib) in file.lib_reference_directives.iter().enumerate() {
                let include_reason = new_file_include_reason(
                    FileIncludeKind::LIB_REFERENCE_DIRECTIVE,
                    FileIncludeData::ReferencedFile(ReferencedFileData {
                        file: self.path.clone(),
                        index: index as i32,
                        synthetic: Node::NIL,
                    }),
                );
                let (name, ok) = get_lib_file_name(&lib.file_name);
                if ok {
                    let lib_file = loader.path_for_lib_file(&name);
                    self.add_sub_task(
                        ResolvedRef {
                            file_name: lib_file.path.clone(),
                            include_reason: Some(include_reason),
                            ..Default::default()
                        },
                        Some(lib_file),
                    );
                } else {
                    self.processing_diagnostics
                        .push(new_unknown_reference_processing_diagnostic(include_reason));
                }
            }
        }

        loader.resolve_imports_and_module_augmentations(self);
    }

    // Go: filesparser.go:161 (*parseTask).redirect
    pub fn redirect(&mut self, _loader: &FileLoader, file_name: &str) {
        let redirected = Rc::new(RefCell::new(ParseTask {
            normalized_file_path: normalize_path(file_name),
            lib_file: self.lib_file.clone(),
            include_reason: self.include_reason.clone(),
            ..Default::default()
        }));
        self.redirected_parse_task = Some(redirected.clone());
        // increaseDepth and elideOnDepth are not copied to redirects, otherwise their depth would be double counted.
        self.sub_tasks = vec![redirected];
    }

    // Go: filesparser.go:171 (*parseTask).loadAutomaticTypeDirectives
    pub fn load_automatic_type_directives(&mut self, loader: &FileLoader) {
        // PORT: tracing is skipped.
        let (to_parse_type_refs, type_resolutions_in_file, type_resolutions_trace, p_diagnostics) =
            loader.resolve_automatic_type_directives(&self.normalized_file_path);
        self.type_resolutions_in_file = type_resolutions_in_file;
        self.type_resolutions_trace = type_resolutions_trace;
        self.processing_diagnostics.extend(p_diagnostics);
        for type_resolution in to_parse_type_refs {
            self.add_sub_task(type_resolution, None);
        }
    }

    // Go: filesparser.go:192 (*parseTask).addSubTask
    pub fn add_sub_task(&mut self, ref_: ResolvedRef, lib_file: Option<Rc<LibFile>>) {
        let normalized_file_path = normalize_path(&ref_.file_name);
        let sub_task = Rc::new(RefCell::new(ParseTask {
            normalized_file_path,
            lib_file,
            increase_depth: ref_.increase_depth,
            elide_on_depth: ref_.elide_on_depth,
            include_reason: ref_.include_reason,
            package_id: ref_.package_id,
            ..Default::default()
        }));
        self.sub_tasks.push(sub_task);
    }
}

// Go: filesparser.go:184 resolvedRef
#[derive(Clone, Default)]
pub struct ResolvedRef {
    pub file_name: String,
    pub increase_depth: bool,
    pub elide_on_depth: bool,
    pub include_reason: Option<Rc<FileIncludeReason>>,
    pub package_id: PackageId,
}

/// One queued run of the closure that Go `filesParser.start` passes to
/// `wg.Queue`, with the values it captures.
pub(crate) struct QueuedParseTask {
    task: ParseTaskRef,
    data: Rc<RefCell<ParseTaskData>>,
    loaded: bool,
    depth: i32,
}

// Go: filesparser.go:205 filesParser
// PORT: Go `core.WorkGroup` is single threaded here (contract 10). Go
// `singleThreadedWorkGroup` keeps queued functions in a slice and
// `RunAndWait` pops the last one first, so `queue` is a stack with the same
// order. The Go `sync.Pool` of `parseTaskData` values is not ported: a new
// value is made only when the path is new, which is the same result.
// PORT: the parses run in parallel, like the Go work group: parse workers
// parse queued files ahead of the loader (`run_prefetch_worker`), and the
// loader takes their results (`take_prefetched_parse`). The loader still
// loads files in the serial order, so store ids, resolution order and file
// order do not change.
#[derive(Default)]
pub struct FilesParser {
    pub(crate) queue: Vec<QueuedParseTask>,
    pub task_data_by_path: FxHashMap<Path, Rc<RefCell<ParseTaskData>>>,
    pub max_depth: i32,
    /// Go `singleThreaded`: no parse workers.
    pub single_threaded: bool,
}

// Go: filesparser.go:219 getParseTaskData
// PORT: Go takes the value from `parseTaskDataPool`; `putParseTaskData`
// (filesparser.go:226) returns an unused one. No pool is needed here.
fn get_parse_task_data(task: &ParseTaskRef) -> Rc<RefCell<ParseTaskData>> {
    let mut tasks = IndexMap::with_capacity(1);
    tasks.insert(task.borrow().normalized_file_path.clone(), task.clone());
    Rc::new(RefCell::new(ParseTaskData {
        tasks,
        // PORT: Go `math.MaxInt`. Depths are small, so `i32::MAX` gives the same comparisons.
        lowest_depth: i32::MAX,
        started_sub_tasks: false,
        package_id: PackageId::default(),
    }))
}

// Go: filesparser.go:231 parseTaskData
// PORT: Go iterates `tasks` (a Go map) in random order. `IndexMap` keeps
// insertion order. The map holds more than one task only when one path is
// reached through file names that differ in casing.
pub struct ParseTaskData {
    // map of tasks by file casing
    pub tasks: IndexMap<String, ParseTaskRef>,
    pub lowest_depth: i32,
    pub started_sub_tasks: bool,
    pub package_id: PackageId,
}

impl FilesParser {
    // Go: filesparser.go:240 (*filesParser).parse
    pub fn parse(&mut self, loader: &FileLoader, tasks: &[ParseTaskRef]) {
        let workers = if self.single_threaded {
            0
        } else {
            prefetch_worker_count()
        };
        if workers == 0 || PREFETCH.with(|p| p.borrow().is_some()) {
            self.run(loader, tasks);
            return;
        }
        let shared = Arc::new(PrefetchShared::new(loader));
        std::thread::scope(|scope| {
            for _ in 0..workers {
                let shared = shared.clone();
                // A worker that cannot start only makes the parse less parallel.
                let _ = std::thread::Builder::new()
                    .name("goport-parse".to_string())
                    .stack_size(PARSE_STACK_SIZE)
                    .spawn_scoped(scope, move || run_prefetch_worker(&shared));
            }
            let _prefetch = PrefetchGuard::install(shared.clone());
            self.run(loader, tasks);
        });
    }

    /// Go `parse` without the workers: queue the root tasks and run the
    /// queue until it is empty.
    fn run(&mut self, loader: &FileLoader, tasks: &[ParseTaskRef]) {
        self.start(loader, tasks, 0);
        // Go: core/workgroup.go singleThreadedWorkGroup.RunAndWait
        while let Some(queued) = self.queue.pop() {
            self.run_queued(loader, queued);
        }
    }

    // Go: filesparser.go:245 (*filesParser).start
    pub fn start(&mut self, loader: &FileLoader, tasks: &[ParseTaskRef], depth: i32) {
        for task in tasks {
            let path = loader.to_path(&task.borrow().normalized_file_path);
            task.borrow_mut().path = path.clone();
            let (data, loaded) = match self.task_data_by_path.get(&path) {
                Some(data) => (data.clone(), true),
                None => {
                    let candidate = get_parse_task_data(task);
                    self.task_data_by_path
                        .insert(path.clone(), candidate.clone());
                    self.prefetch(loader, &task.borrow(), path, depth);
                    (candidate, false)
                }
            };

            self.queue.push(QueuedParseTask {
                task: task.clone(),
                data,
                loaded,
                depth,
            });
        }
    }

    /// Queues the parse of a new task's file for a parse worker, when the
    /// queued run of the task will probably load it (`ParseTask::load`).
    /// A wrong guess only costs worker time: the loader uses a worker parse
    /// only when it gives the same result (`take_prefetched_parse`).
    fn prefetch(&self, loader: &FileLoader, task: &ParseTask, path: Path, depth: i32) {
        let Some(prefetch) = PREFETCH.with(|p| p.borrow().clone()) else {
            return;
        };
        let current_depth = if task.increase_depth {
            depth + 1
        } else {
            depth
        };
        if task.is_for_automatic_type_directive
            || task.loaded
            || task.elide_on_depth && current_depth > self.max_depth
        {
            return;
        }
        let file_name = &task.normalized_file_path;
        let script_kind = get_script_kind_from_file_name(file_name);
        if script_kind == ScriptKind::UNKNOWN
            || !has_extension(file_name)
            || !loader
                .opts
                .config
                .compiler_options()
                .allow_non_ts_extensions
                .is_true()
                && !loader.is_supported_extension(&get_canonical_file_name(
                    file_name,
                    loader.compare_paths_options.use_case_sensitive_file_names,
                ))
        {
            return;
        }
        // PORT: the metadata (package.json scope) is not known yet. Most
        // parses do not read these options; a parse that read other options
        // than the loader passes is not used.
        let external_module_indicator_options = get_external_module_indicator_options(
            file_name,
            &loader.opts.config.compiler_options(),
            &SourceFileMetaData::default(),
        );
        prefetch.queue(
            SourceFileParseOptions {
                file_name: file_name.clone(),
                path,
                external_module_indicator_options,
            },
            script_kind,
        );
    }

    /// The body of the closure that Go `start` queues.
    // Go: filesparser.go:254 (*filesParser).start (queued func)
    fn run_queued(&mut self, loader: &FileLoader, queued: QueuedParseTask) {
        let QueuedParseTask {
            task,
            data,
            loaded,
            depth,
        } = queued;

        let mut start_subtasks = false;
        if loaded {
            let name = task.borrow().normalized_file_path.clone();
            let existing_task = data.borrow().tasks.get(&name).cloned();
            if let Some(existing_task) = existing_task {
                // Go: tasks[i].loadedTask = existingTask (tasks[i] is task)
                task.borrow_mut().loaded_task = Some(existing_task);
            } else {
                let mut d = data.borrow_mut();
                d.tasks.insert(name, task.clone());
                // This is new task for file name - so load subtasks if there was loading for any other casing
                start_subtasks = d.started_sub_tasks;
            }
        }

        {
            let mut d = data.borrow_mut();
            // Propagate packageId to data if we have one and data doesn't yet
            let t = task.borrow();
            if d.package_id.name.is_empty() && !t.package_id.name.is_empty() {
                d.package_id = t.package_id.clone();
            }
        }

        let current_depth = if task.borrow().increase_depth {
            depth + 1
        } else {
            depth
        };
        {
            let mut d = data.borrow_mut();
            if current_depth < d.lowest_depth {
                // If we're seeing this task at a lower depth than before,
                // reprocess its subtasks to ensure they are loaded.
                d.lowest_depth = current_depth;
                start_subtasks = true;
                d.started_sub_tasks = true;
            }
        }

        if task.borrow().elide_on_depth && current_depth > self.max_depth {
            return;
        }

        // PORT: Go does not change `data.tasks` in this loop, so a copy of the
        // values iterates the same tasks.
        let tasks_by_file_name: Vec<ParseTaskRef> = data.borrow().tasks.values().cloned().collect();
        for task_by_file_name in tasks_by_file_name {
            let mut load_sub_tasks = start_subtasks;
            if !task_by_file_name.borrow().loaded {
                task_by_file_name.borrow_mut().load(loader);
                if task_by_file_name.borrow().redirected_parse_task.is_some() {
                    // Always load redirected task
                    load_sub_tasks = true;
                    data.borrow_mut().started_sub_tasks = true;
                }
            }
            if !task_by_file_name.borrow().started_sub_tasks && load_sub_tasks {
                task_by_file_name.borrow_mut().started_sub_tasks = true;
                let sub_tasks = task_by_file_name.borrow().sub_tasks.clone();
                let lowest_depth = data.borrow().lowest_depth;
                self.start(loader, &sub_tasks, lowest_depth);
            }
        }
    }

    // Go: filesparser.go:306 (*filesParser).getProcessedFiles
    pub fn get_processed_files(&self, loader: &FileLoader) -> ProcessedFiles {
        let total_file_count = loader.total_file_count.get() as usize;
        let lib_file_count = loader.lib_file_count.get() as usize;

        let mut missing_files: Vec<String> = Vec::new();
        let mut duplicate_source_files: Vec<DuplicateSourceFile> = Vec::new();
        let mut files: Vec<Rc<ParsedSourceFile>> =
            Vec::with_capacity(total_file_count - lib_file_count);
        // totalFileCount here since we append files to it later to construct the final list
        let mut lib_files: Vec<Rc<ParsedSourceFile>> = Vec::with_capacity(total_file_count);

        let mut files_by_path: FxHashMap<Path, Rc<ParsedSourceFile>> = FxHashMap::default();
        // stores 'filename -> file association' ignoring case
        // used to track cases when two file names differ only in casing
        let mut tasks_seen_by_name_ignore_case: Option<FxHashMap<String, ParseTaskRef>> =
            if loader.compare_paths_options.use_case_sensitive_file_names {
                Some(FxHashMap::default())
            } else {
                None
            };

        let mut include_processor = IncludeProcessor {
            file_include_reasons: FxHashMap::default(),
            ..Default::default()
        };
        let mut output_file_to_project_reference_source: Option<FxHashMap<Path, String>> =
            if !loader.opts.can_use_project_reference_source() {
                Some(FxHashMap::default())
            } else {
                None
            };
        let mut resolved_modules: FxHashMap<Path, ModeAwareCache<Rc<ResolvedModule>>> =
            FxHashMap::default();
        let mut type_resolutions_in_file: FxHashMap<
            Path,
            ModeAwareCache<Rc<ResolvedTypeReferenceDirective>>,
        > = FxHashMap::default();
        let mut source_file_meta_datas: FxHashMap<Path, SourceFileMetaData> = FxHashMap::default();
        let mut jsx_runtime_import_specifiers: Option<
            FxHashMap<Path, Rc<JsxRuntimeImportSpecifier>>,
        > = None;
        let mut import_helpers_import_specifiers: Option<FxHashMap<Path, Node>> = None;
        let mut source_files_found_searching_node_modules: FxHashSet<Path> = FxHashSet::default();
        let mut lib_files_map: FxHashMap<Path, Rc<LibFile>> = FxHashMap::default();

        let mut redirect_targets_map: Option<FxHashMap<Path, Vec<String>>> = None;
        let mut redirect_files_by_path: Option<FxHashMap<Path, RedirectsFile>> = None;
        let mut package_id_to_source_file: Option<FxHashMap<PackageId, Rc<ParsedSourceFile>>> =
            None;
        if !loader
            .opts
            .config
            .compiler_options()
            .deduplicate_packages
            .is_false()
        {
            redirect_targets_map = Some(FxHashMap::default());
            package_id_to_source_file = Some(FxHashMap::default());
        }

        // PORT: Go `seen map[*parseTaskData]string` is keyed by pointer. The
        // key here is the `Rc` pointer of the task data.
        let mut seen: FxHashMap<*const RefCell<ParseTaskData>, String> = FxHashMap::default();

        // PORT: the Go closure `collectFiles` is an explicit recursive
        // function over a struct that holds its captured variables.
        struct Collector<'a> {
            parser: &'a FilesParser,
            loader: &'a FileLoader,
            seen: &'a mut FxHashMap<*const RefCell<ParseTaskData>, String>,
            missing_files: &'a mut Vec<String>,
            duplicate_source_files: &'a mut Vec<DuplicateSourceFile>,
            files: &'a mut Vec<Rc<ParsedSourceFile>>,
            lib_files: &'a mut Vec<Rc<ParsedSourceFile>>,
            files_by_path: &'a mut FxHashMap<Path, Rc<ParsedSourceFile>>,
            tasks_seen_by_name_ignore_case: &'a mut Option<FxHashMap<String, ParseTaskRef>>,
            include_processor: &'a mut IncludeProcessor,
            output_file_to_project_reference_source: &'a mut Option<FxHashMap<Path, String>>,
            resolved_modules: &'a mut FxHashMap<Path, ModeAwareCache<Rc<ResolvedModule>>>,
            type_resolutions_in_file:
                &'a mut FxHashMap<Path, ModeAwareCache<Rc<ResolvedTypeReferenceDirective>>>,
            source_file_meta_datas: &'a mut FxHashMap<Path, SourceFileMetaData>,
            jsx_runtime_import_specifiers:
                &'a mut Option<FxHashMap<Path, Rc<JsxRuntimeImportSpecifier>>>,
            import_helpers_import_specifiers: &'a mut Option<FxHashMap<Path, Node>>,
            source_files_found_searching_node_modules: &'a mut FxHashSet<Path>,
            lib_files_map: &'a mut FxHashMap<Path, Rc<LibFile>>,
            redirect_targets_map: &'a mut Option<FxHashMap<Path, Vec<String>>>,
            redirect_files_by_path: &'a mut Option<FxHashMap<Path, RedirectsFile>>,
            package_id_to_source_file: &'a mut Option<FxHashMap<PackageId, Rc<ParsedSourceFile>>>,
            total_file_count: usize,
        }

        impl Collector<'_> {
            // Go: filesparser.go:347 collectFiles
            fn collect_files(&mut self, tasks: &[ParseTaskRef]) {
                let loader = self.loader;
                for task in tasks {
                    let mut task = task.clone();
                    let include_reason = task.borrow().include_reason.clone();
                    // Exclude automatic type directive tasks from include reason processing,
                    // as these are internal implementation details and should not contribute
                    // to the reasons for including files.
                    let (has_redirect, is_automatic) = {
                        let t = task.borrow();
                        (
                            t.redirected_parse_task.is_some(),
                            t.is_for_automatic_type_directive,
                        )
                    };
                    if !has_redirect && !is_automatic {
                        let loaded_task = task.borrow().loaded_task.clone();
                        if let Some(loaded_task) = loaded_task {
                            task = loaded_task;
                        }
                        self.parser.add_include_reason(
                            self.include_processor,
                            &task,
                            include_reason.clone(),
                        );
                    }
                    let data = self
                        .parser
                        .task_data_by_path
                        .get(&task.borrow().path)
                        .cloned();
                    if !task.borrow().loaded {
                        continue;
                    }
                    let data = data.expect("loaded parse task without task data");
                    let data_key = Rc::as_ptr(&data);

                    let normalized_file_path = task.borrow().normalized_file_path.clone();
                    let task_path = task.borrow().path.clone();

                    // ensure we only walk each task once
                    if let Some(checked_name) = self.seen.get(&data_key).cloned() {
                        if let Some(file) = task.borrow().file.clone() {
                            if checked_name != normalized_file_path {
                                self.duplicate_source_files.push(DuplicateSourceFile {
                                    parse_options: file.parse_options().clone(),
                                    script_kind: file.script_kind,
                                });
                            }
                        }
                        // PORT: equal names give equal absolute paths, so
                        // the check below only runs for different names.
                        if checked_name != normalized_file_path
                            && !loader
                                .opts
                                .config
                                .compiler_options()
                                .force_consistent_casing_in_file_names
                                .is_false()
                        {
                            // Check if it differs only in drive letters its ok to ignore that error:
                            let checked_absolute_path = get_normalized_absolute_path_without_root(
                                &checked_name,
                                &loader.compare_paths_options.current_directory,
                            );
                            let input_absolute_path = get_normalized_absolute_path_without_root(
                                &normalized_file_path,
                                &loader.compare_paths_options.current_directory,
                            );
                            if checked_absolute_path != input_absolute_path {
                                self.include_processor
                                    .add_processing_diagnostics_for_file_casing(
                                        &task_path,
                                        &checked_name,
                                        &normalized_file_path,
                                        include_reason
                                            .clone()
                                            .expect("nil pointer dereference: includeReason"),
                                    );
                            }
                        }
                        continue;
                    } else {
                        self.seen.insert(data_key, normalized_file_path.clone());
                    }

                    if let Some(tasks_seen_by_name_ignore_case) =
                        self.tasks_seen_by_name_ignore_case.as_mut()
                    {
                        let path_lower_case = to_file_name_lower_case(&task_path);
                        if let Some(task_by_ignore_case) =
                            tasks_seen_by_name_ignore_case.get(&path_lower_case)
                        {
                            let t = task_by_ignore_case.borrow();
                            self.include_processor
                                .add_processing_diagnostics_for_file_casing(
                                    &t.path,
                                    &t.normalized_file_path,
                                    &normalized_file_path,
                                    include_reason
                                        .clone()
                                        .expect("nil pointer dereference: includeReason"),
                                );
                        } else {
                            tasks_seen_by_name_ignore_case.insert(path_lower_case, task.clone());
                        }
                    }

                    {
                        let t = task.borrow();
                        for trace in &t.type_resolutions_trace {
                            loader.opts.host.trace(trace.message, trace.args.clone());
                        }
                        for trace in &t.resolutions_trace {
                            loader.opts.host.trace(trace.message, trace.args.clone());
                        }
                    }

                    let file = task.borrow().file.clone();
                    let data_package_id = data.borrow().package_id.clone();
                    let data_lowest_depth = data.borrow().lowest_depth;
                    if let Some(package_id_to_source_file) = self.package_id_to_source_file.as_mut()
                    {
                        if !data_package_id.name.is_empty() {
                            if let Some(package_id_file) =
                                package_id_to_source_file.get(&data_package_id).cloned()
                            {
                                if let Some(file) = &file {
                                    // Package deduplication keeps the first package instance in the
                                    // program, but we still parsed this file and acquired it through
                                    // the host, so snapshot disposal must release that extra owner.
                                    self.duplicate_source_files.push(DuplicateSourceFile {
                                        parse_options: file.parse_options().clone(),
                                        script_kind: file.script_kind,
                                    });
                                }
                                self.redirect_targets_map
                                    .as_mut()
                                    .expect("redirectTargetsMap is set with packageIdToSourceFile")
                                    .entry(package_id_file.path().clone())
                                    .or_default()
                                    .push(normalized_file_path.clone());
                                let redirect_files_by_path =
                                    self.redirect_files_by_path.get_or_insert_with(|| {
                                        FxHashMap::with_capacity_and_hasher(
                                            self.total_file_count,
                                            Default::default(),
                                        )
                                    });
                                let index =
                                    (self.files.len() + redirect_files_by_path.len()) as i32;
                                redirect_files_by_path.insert(
                                    task_path.clone(),
                                    RedirectsFile {
                                        index,
                                        file_name: normalized_file_path.clone(),
                                        path: task_path.clone(),
                                        target: package_id_file.path().clone(),
                                    },
                                );
                                self.files_by_path
                                    .insert(task_path.clone(), package_id_file);
                                if data_lowest_depth > 0 {
                                    self.source_files_found_searching_node_modules
                                        .insert(task_path.clone());
                                }
                                continue;
                            } else if let Some(file) = &file {
                                package_id_to_source_file
                                    .insert(data_package_id.clone(), file.clone());
                            }
                        }
                    }

                    let sub_tasks = task.borrow().sub_tasks.clone();
                    if !sub_tasks.is_empty() {
                        self.collect_files(&sub_tasks);
                    }

                    let t = task.borrow();
                    // Exclude automatic type directive tasks from include reason processing,
                    // as these are internal implementation details and should not contribute
                    // to the reasons for including files.
                    if let Some(redirected) = &t.redirected_parse_task {
                        if !loader.opts.can_use_project_reference_source() {
                            self.output_file_to_project_reference_source
                                .as_mut()
                                .expect("outputFileToProjectReferenceSource is set when project reference source is not used")
                                .insert(redirected.borrow().path.clone(), t.file_name());
                        }
                        continue;
                    }

                    if t.is_for_automatic_type_directive {
                        self.type_resolutions_in_file
                            .insert(t.path.clone(), t.type_resolutions_in_file.clone());
                        if !t.processing_diagnostics.is_empty() {
                            self.include_processor
                                .processing_diagnostics
                                .extend(t.processing_diagnostics.iter().cloned());
                        }
                        continue;
                    }

                    let path = t.path.clone();

                    if !t.processing_diagnostics.is_empty() {
                        self.include_processor
                            .processing_diagnostics
                            .extend(t.processing_diagnostics.iter().cloned());
                    }

                    let Some(file) = file else {
                        self.missing_files.push(t.normalized_file_path.clone());
                        continue;
                    };

                    if let Some(lib_file) = &t.lib_file {
                        self.lib_files.push(file.clone());
                        self.lib_files_map.insert(path.clone(), lib_file.clone());
                    } else {
                        self.files.push(file.clone());
                    }
                    self.files_by_path.insert(path.clone(), file);
                    self.resolved_modules
                        .insert(path.clone(), t.resolutions_in_file.clone());
                    self.type_resolutions_in_file
                        .insert(path.clone(), t.type_resolutions_in_file.clone());
                    self.source_file_meta_datas
                        .insert(path.clone(), t.metadata.clone());

                    if let Some(jsx_runtime_import_specifier) = &t.jsx_runtime_import_specifier {
                        self.jsx_runtime_import_specifiers
                            .get_or_insert_with(FxHashMap::default)
                            .insert(path.clone(), jsx_runtime_import_specifier.clone());
                    }
                    if t.import_helpers_import_specifier.is_some() {
                        self.import_helpers_import_specifiers
                            .get_or_insert_with(FxHashMap::default)
                            .insert(path.clone(), t.import_helpers_import_specifier);
                    }
                    if data_lowest_depth > 0 {
                        self.source_files_found_searching_node_modules.insert(path);
                    }
                }
            }
        }

        let mut collector = Collector {
            parser: self,
            loader,
            seen: &mut seen,
            missing_files: &mut missing_files,
            duplicate_source_files: &mut duplicate_source_files,
            files: &mut files,
            lib_files: &mut lib_files,
            files_by_path: &mut files_by_path,
            tasks_seen_by_name_ignore_case: &mut tasks_seen_by_name_ignore_case,
            include_processor: &mut include_processor,
            output_file_to_project_reference_source: &mut output_file_to_project_reference_source,
            resolved_modules: &mut resolved_modules,
            type_resolutions_in_file: &mut type_resolutions_in_file,
            source_file_meta_datas: &mut source_file_meta_datas,
            jsx_runtime_import_specifiers: &mut jsx_runtime_import_specifiers,
            import_helpers_import_specifiers: &mut import_helpers_import_specifiers,
            source_files_found_searching_node_modules:
                &mut source_files_found_searching_node_modules,
            lib_files_map: &mut lib_files_map,
            redirect_targets_map: &mut redirect_targets_map,
            redirect_files_by_path: &mut redirect_files_by_path,
            package_id_to_source_file: &mut package_id_to_source_file,
            total_file_count,
        };
        collector.collect_files(&loader.root_tasks);
        loader.sort_libs(&mut lib_files);

        let lib_files_len = lib_files.len() as i32;
        let mut all_files = lib_files;
        all_files.extend(files);
        if let Some(redirect_files_by_path) = redirect_files_by_path.as_mut() {
            for redirect_file in redirect_files_by_path.values_mut() {
                redirect_file.index += lib_files_len;
            }
        }

        let mut keys: Vec<Path> = loader
            .path_for_lib_file_resolutions
            .borrow()
            .keys()
            .cloned()
            .collect();
        // PORT: Go sorts by the bytes of the paths (see `compare_go_bytes`).
        keys.sort_by(|a, b| compare_go_bytes(a.as_str(), b.as_str()));
        for key in keys {
            let value = loader
                .path_for_lib_file_resolutions
                .borrow()
                .get(&key)
                .cloned()
                .expect("key from the map");
            let mut cache: ModeAwareCache<Rc<ResolvedModule>> = ModeAwareCache::default();
            cache.insert(
                ModeAwareCacheKey {
                    name: value.library_name.clone(),
                    mode: ModuleKind::COMMON_JS,
                },
                value.resolution.clone(),
            );
            resolved_modules.insert(key, cache);
            for trace in &value.trace {
                loader.opts.host.trace(trace.message, trace.args.clone());
            }
        }

        ProcessedFiles {
            finished_processing: true,
            resolver: loader.resolver.clone(),
            files: all_files,
            duplicate_source_files,
            files_by_path,
            project_reference_file_mapper: Some(loader.project_reference_file_mapper.clone()),
            resolved_modules,
            type_resolutions_in_file,
            source_file_meta_datas,
            jsx_runtime_import_specifiers,
            import_helpers_import_specifiers,
            source_files_found_searching_node_modules,
            lib_files: lib_files_map,
            missing_files,
            include_processor,
            output_file_to_project_reference_source,
            redirect_targets_map,
            redirect_files_by_path,
        }
    }

    // Go: filesparser.go:539 (*filesParser).addIncludeReason
    // PORT: Go can append a nil reason. Only the automatic type directive
    // root task has no reason, and `collectFiles` never passes it here, so a
    // nil reason is skipped.
    pub fn add_include_reason(
        &self,
        include_processor: &mut IncludeProcessor,
        task: &ParseTaskRef,
        reason: Option<Rc<FileIncludeReason>>,
    ) {
        let t = task.borrow();
        if let Some(redirected) = &t.redirected_parse_task {
            self.add_include_reason(include_processor, redirected, reason);
        } else if t.loaded {
            let Some(reason) = reason else {
                return;
            };
            if let Some(existing) = include_processor.file_include_reasons.get_mut(&t.path) {
                existing.push(reason);
            } else {
                include_processor
                    .file_include_reasons
                    .insert(t.path.clone(), vec![reason]);
            }
        }
    }
}

/// Go `strings.Join(core.Flatten(supportedExtensions), "', '")`.
pub(crate) fn join_flattened_extensions(extensions: &[Vec<String>]) -> String {
    extensions
        .iter()
        .flatten()
        .map(String::as_str)
        .collect::<Vec<_>>()
        .join("', '")
}

/// Go `&processingDiagnostic{kind: processingDiagnosticKindExplainingFileInclude, data: &includeExplainingDiagnostic{...}}`.
pub(crate) fn new_explaining_processing_diagnostic(
    diagnostic_reason: Option<Rc<FileIncludeReason>>,
    message: &'static Message,
    args: Vec<String>,
) -> Rc<ProcessingDiagnostic> {
    Rc::new(ProcessingDiagnostic {
        kind: ProcessingDiagnosticKind::EXPLAINING_FILE_INCLUDE,
        data: ProcessingDiagnosticData::IncludeExplaining(IncludeExplainingDiagnostic {
            file: Path::default(),
            diagnostic_reason,
            message,
            args,
        }),
    })
}

/// Go `&processingDiagnostic{kind: processingDiagnosticKindUnknownReference, data: includeReason}`.
pub(crate) fn new_unknown_reference_processing_diagnostic(
    include_reason: Rc<FileIncludeReason>,
) -> Rc<ProcessingDiagnostic> {
    Rc::new(ProcessingDiagnostic {
        kind: ProcessingDiagnosticKind::UNKNOWN_REFERENCE,
        data: ProcessingDiagnosticData::FileIncludeReason(include_reason),
    })
}

// ──────────────────────────────────────────────────────────────────────
// Parse prefetch
// ──────────────────────────────────────────────────────────────────────

/// Stack size of a parse worker. The parser recurses as deeply as on the
/// loading thread.
const PARSE_STACK_SIZE: usize = 1 << 30;

/// Number of parse workers next to the loading thread.
/// `GOPORT_PARSE_THREADS` sets it (0 turns prefetch off).
fn prefetch_worker_count() -> usize {
    if let Some(count) = std::env::var("GOPORT_PARSE_THREADS")
        .ok()
        .and_then(|value| value.parse().ok())
    {
        return count;
    }
    std::thread::available_parallelism()
        .map_or(1, std::num::NonZero::get)
        .min(PARSE_THREAD_CAP)
        - 1
}

/// The most parse threads, the loading thread included. 8 is the measured
/// best with glibc malloc: more workers make zod and effect parse slower.
const PARSE_THREAD_CAP: usize = 8;

/// The parse of one file by a parse worker.
struct PrefetchJob {
    /// Provisional store id offset (`new_detached_file_store`).
    job: usize,
    opts: SourceFileParseOptions,
    script_kind: ScriptKind,
    state: Mutex<PrefetchState>,
    done: Condvar,
}

enum PrefetchState {
    Queued,
    Running,
    /// The parse and the text it parsed. `None`: the file could not be
    /// read, or the parse is not usable.
    Done(Option<(DetachedParse, &'static str)>),
    /// The loader took the job; a worker must not start it.
    Claimed,
}

#[derive(Default)]
struct PrefetchQueue {
    /// Jobs no worker has taken yet. Workers take the newest first, like
    /// the loader's queue, but take `lib.dom.d.ts` before all others.
    pending: Vec<Arc<PrefetchJob>>,
    /// The queued `lib.dom.d.ts` job. It is the largest file of most
    /// programs, so its parse starts first to end before the loader needs it.
    first: Option<Arc<PrefetchJob>>,
    /// Every job by file name. A file name is queued once.
    by_name: FxHashMap<String, Arc<PrefetchJob>>,
    next_job: usize,
    closed: bool,
}

/// What a parse worker needs to guess the files that a parsed file
/// references (`queue_references`).
struct PrefetchConfig {
    current_directory: String,
    use_case_sensitive_file_names: bool,
    /// Go `defaultLibraryPath`. Empty when `libReplacement` can move lib
    /// files, so lib references are not guessed.
    default_library_path: String,
}

/// The jobs that the loading thread and the parse workers share.
struct PrefetchShared {
    queue: Mutex<PrefetchQueue>,
    ready: Condvar,
    config: PrefetchConfig,
}

thread_local! {
    /// Set on the loading thread while parse workers run.
    static PREFETCH: RefCell<Option<Arc<PrefetchShared>>> = const { RefCell::new(None) };
}

impl PrefetchShared {
    fn new(loader: &FileLoader) -> Self {
        let lib_replacement = loader
            .opts
            .config
            .compiler_options()
            .lib_replacement
            .is_true();
        Self {
            queue: Mutex::new(PrefetchQueue::default()),
            ready: Condvar::new(),
            config: PrefetchConfig {
                current_directory: loader.opts.host.get_current_directory(),
                use_case_sensitive_file_names: loader
                    .opts
                    .host
                    .fs()
                    .use_case_sensitive_file_names(),
                default_library_path: if lib_replacement {
                    String::new()
                } else {
                    loader.default_library_path.clone()
                },
            },
        }
    }

    /// Queues a parse of `opts.file_name`, unless one is queued already.
    fn queue(&self, opts: SourceFileParseOptions, script_kind: ScriptKind) {
        let mut queue = lock(&self.queue);
        if queue.closed
            || queue.next_job >= DETACHED_STORE_LIMIT
            || queue.by_name.contains_key(&opts.file_name)
        {
            return;
        }
        let job = Arc::new(PrefetchJob {
            job: queue.next_job,
            opts,
            script_kind,
            state: Mutex::new(PrefetchState::Queued),
            done: Condvar::new(),
        });
        queue.next_job += 1;
        queue
            .by_name
            .insert(job.opts.file_name.clone(), job.clone());
        if job.opts.file_name.ends_with("/lib.dom.d.ts") {
            queue.first = Some(job);
        } else {
            queue.pending.push(job);
        }
        drop(queue);
        self.ready.notify_one();
    }

    /// Queues the files that a parsed file references, so their parses do
    /// not wait until the loader loads that file: `/// <reference path>`
    /// and `/// <reference lib>` files, and relative imports that name an
    /// existing TS file. This follows `ParseTask::load`
    /// (`resolve_tripleslash_path_reference`, `path_for_lib_file`, module
    /// resolution) for the common cases; the loader checks every guess.
    fn queue_references(&self, fs: &dyn Fs, parse: &DetachedParse) {
        let config = &self.config;
        let file = &parse.file;
        let mut names = Vec::new();
        for reference in &file.referenced_files {
            let name = if is_rooted_disk_path(&reference.file_name) {
                reference.file_name.clone()
            } else {
                combine_paths(
                    &get_directory_path(file.file_name()),
                    &[&reference.file_name],
                )
            };
            names.push(normalize_path(&name));
        }
        if !config.default_library_path.is_empty() {
            for lib in &file.lib_reference_directives {
                let (name, ok) = get_lib_file_name(&lib.file_name);
                if ok {
                    names.push(normalize_path(&combine_paths(
                        &config.default_library_path,
                        &[&name],
                    )));
                }
            }
        }
        for specifier in &parse.import_specifiers {
            if let Some(name) = guess_relative_import(fs, file.file_name(), specifier) {
                names.push(name);
            }
        }
        for file_name in names {
            let script_kind = get_script_kind_from_file_name(&file_name);
            // The parser needs a normalized absolute name.
            if script_kind == ScriptKind::UNKNOWN
                || !has_extension(&file_name)
                || get_encoded_root_length(&file_name) == 0
                || file_name != normalize_path(&file_name)
            {
                continue;
            }
            let path = to_path(
                &file_name,
                &config.current_directory,
                config.use_case_sensitive_file_names,
            );
            // PORT: the options are a guess (see `FilesParser::prefetch`).
            self.queue(
                SourceFileParseOptions {
                    file_name,
                    path,
                    external_module_indicator_options: ExternalModuleIndicatorOptions::default(),
                },
                script_kind,
            );
        }
    }
}

/// Installs `PREFETCH` for the loading thread. Dropping it closes the
/// queue, so the workers stop and the thread scope can end (also when the
/// loader panics).
struct PrefetchGuard(Arc<PrefetchShared>);

impl PrefetchGuard {
    fn install(shared: Arc<PrefetchShared>) -> Self {
        PREFETCH.with(|p| *p.borrow_mut() = Some(shared.clone()));
        Self(shared)
    }
}

impl Drop for PrefetchGuard {
    fn drop(&mut self) {
        PREFETCH.with(|p| p.borrow_mut().take());
        lock(&self.0.queue).closed = true;
        self.0.ready.notify_all();
    }
}

fn lock<T>(mutex: &Mutex<T>) -> std::sync::MutexGuard<'_, T> {
    mutex
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner)
}

/// A parse worker: parses queued files, newest first (the loader's queue
/// is a stack too), until the queue closes.
fn run_prefetch_worker(shared: &PrefetchShared) {
    // Go: sys.FS() is bundled.WrapFS(osvfs.FS()). The loader reads the file
    // again through its own host and compares the text.
    let fs = crate::frontend::bundled::wrap_fs(crate::frontend::vfs::osvfs_fs());
    loop {
        let job = {
            let mut queue = lock(&shared.queue);
            loop {
                if queue.closed {
                    return;
                }
                if let Some(job) = queue.first.take().or_else(|| queue.pending.pop()) {
                    break job;
                }
                queue = shared
                    .ready
                    .wait(queue)
                    .unwrap_or_else(std::sync::PoisonError::into_inner);
            }
        };
        {
            let mut state = lock(&job.state);
            if !matches!(*state, PrefetchState::Queued) {
                continue;
            }
            *state = PrefetchState::Running;
        }
        let result = prefetch_parse(&*fs, &job);
        if let Some((parse, _)) = &result {
            shared.queue_references(&*fs, parse);
        }
        *lock(&job.state) = PrefetchState::Done(result);
        job.done.notify_all();
    }
}

/// The TS file that a relative import (`./x`, `../x.js`) of `containing`
/// most likely resolves to: the first existing file in module resolution's
/// extension order. `None` for other specifiers.
fn guess_relative_import(fs: &dyn Fs, containing: &str, specifier: &str) -> Option<String> {
    if !specifier.starts_with("./") && !specifier.starts_with("../") {
        return None;
    }
    let base = normalize_path(&combine_paths(
        &get_directory_path(containing),
        &[specifier],
    ));
    let with = |stem: &str, extensions: &[&str]| -> Vec<String> {
        extensions
            .iter()
            .map(|e| normalize_path(&format!("{stem}{e}")))
            .collect()
    };
    let candidates = if let Some(stem) = base.strip_suffix(EXTENSION_JS) {
        with(stem, &[EXTENSION_TS, EXTENSION_TSX, EXTENSION_DTS])
    } else if let Some(stem) = base.strip_suffix(EXTENSION_MJS) {
        with(stem, &[EXTENSION_MTS, EXTENSION_DMTS])
    } else if let Some(stem) = base.strip_suffix(EXTENSION_CJS) {
        with(stem, &[EXTENSION_CTS, EXTENSION_DCTS])
    } else if [EXTENSION_TS, EXTENSION_TSX, EXTENSION_MTS, EXTENSION_CTS]
        .iter()
        .any(|e| base.ends_with(e))
    {
        vec![base]
    } else if get_base_file_name(&base).contains('.') {
        return None;
    } else {
        let index = combine_paths(&base, &["index"]);
        let mut candidates = with(&base, &[EXTENSION_TS, EXTENSION_TSX, EXTENSION_DTS]);
        candidates.extend(with(&index, &[EXTENSION_TS, EXTENSION_TSX, EXTENSION_DTS]));
        candidates
    };
    candidates.into_iter().find(|name| fs.file_exists(name))
}

/// Reads and parses the file of `job` into a detached store. The parse is
/// usable only when it made no thread-local state that the loading thread
/// would need (synthetic nodes, node ids) and did not panic.
fn prefetch_parse(fs: &dyn Fs, job: &PrefetchJob) -> Option<(DetachedParse, &'static str)> {
    // A bundled lib text is embedded, so it needs no copy.
    let text = match crate::frontend::bundled::bundled_text(&job.opts.file_name) {
        Some(text) => text,
        None => {
            let (text, ok) = fs.read_file(&job.opts.file_name);
            if !ok {
                return None;
            }
            Box::leak(text.into_boxed_str())
        }
    };
    let before = (synthetic_slot_count(), next_ids());
    let parse = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        parse_source_file_detached(job.job, &job.opts, text, job.script_kind)
    }));
    let Ok(parse) = parse else {
        let _ = take_detached_file_store();
        return None;
    };
    (parse.store.is_self_contained() && (synthetic_slot_count(), next_ids()) == before)
        .then_some((parse, text))
}

/// The worker parse of `opts.file_name` with text `text`, adopted into the
/// stores of this thread, when a worker made one that equals what
/// `parse_source_file(opts, text, script_kind)` would make now. Waits for a
/// running worker parse. `None`: parse on this thread.
pub fn take_prefetched_parse(
    opts: &SourceFileParseOptions,
    text: &str,
    script_kind: ScriptKind,
) -> Option<ParsedSourceFile> {
    let shared = PREFETCH.with(|p| p.borrow().clone())?;
    let job = lock(&shared.queue).by_name.get(&opts.file_name).cloned()?;
    let mut state = lock(&job.state);
    loop {
        match std::mem::replace(&mut *state, PrefetchState::Claimed) {
            PrefetchState::Queued | PrefetchState::Claimed => return None,
            PrefetchState::Running => {
                *state = PrefetchState::Running;
                state = job
                    .done
                    .wait(state)
                    .unwrap_or_else(std::sync::PoisonError::into_inner);
            }
            PrefetchState::Done(result) => {
                drop(state);
                let (parse, parsed_text) = result?;
                let file_opts = &parse.file.parse_options;
                let same = parsed_text == text
                    && job.script_kind == script_kind
                    && file_opts.file_name == opts.file_name
                    && file_opts.path == opts.path
                    && (!parse.read_module_indicator_options
                        || file_opts.external_module_indicator_options
                            == opts.external_module_indicator_options);
                return same.then(|| adopt_detached_parse(parse, opts));
            }
        }
    }
}
