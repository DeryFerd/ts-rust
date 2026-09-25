//! Go: compiler/fileloader.go (the file loader that finds, parses and
//! resolves every program file).
//!
//! PORT: Go `opts.Tracing` spans are not ported. They do not change results.

use crate::frontend::prelude::*;
use std::cell::Cell;

// Go: fileloader.go:21 libResolution
pub struct LibResolution {
    pub library_name: String,
    pub resolution: Rc<ResolvedModule>,
    pub trace: Vec<DiagAndArgs>,
}

// Go: fileloader.go:27 LibFile
#[derive(Clone, Debug, Default)]
pub struct LibFile {
    pub name: String,
    pub path: String,
    pub replaced: bool,
}

// Go: fileloader.go:33 sourceFileFromReferenceDiagnostic
pub struct SourceFileFromReferenceDiagnostic {
    pub message: &'static Message,
    pub args: Vec<String>,
}

// Go: fileloader.go:38 fileLoader
// PORT: the Go loader is shared by the parse work group. The port is single
// threaded (contract 10), so the atomics and sync maps are `Cell` and
// `RefCell`, and `factoryMu` is not needed. `resolver` is `None` only until
// `process_all_program_files` sets it, as in Go.
pub struct FileLoader {
    pub opts: ProgramOptions,
    pub resolver: Option<Rc<Resolver>>,
    pub default_library_path: String,
    pub compare_paths_options: ComparePathsOptions,
    pub supported_extensions: Vec<Vec<String>>,
    pub supported_extensions_with_json_if_resolve_json_module: Vec<Vec<String>>,

    pub files_parser: RefCell<FilesParser>,
    pub root_tasks: Vec<ParseTaskRef>,

    pub total_file_count: Cell<i32>,
    pub lib_file_count: Cell<i32>,

    pub factory: NodeFactory,

    pub project_reference_file_mapper: Rc<RefCell<ProjectReferenceFileMapper>>,
    pub dts_directories: FxHashSet<Path>,

    pub path_for_lib_file_cache: RefCell<FxHashMap<String, Rc<LibFile>>>,
    pub path_for_lib_file_resolutions: RefCell<FxHashMap<Path, Rc<LibResolution>>>,
}

// Go: fileloader.go:62 redirectsFile
#[derive(Clone, Debug, Default)]
pub struct RedirectsFile {
    // Index of file at which this redirect file needs to be iterated
    pub index: i32,
    pub file_name: String,
    pub path: Path,
    pub target: Path,
}

// Go: fileloader.go:70 DuplicateSourceFile
// PORT: Go also keeps `Hash xxh3.Uint128` of the file text for the parse
// cache. The port has no parse cache and no xxh3 dependency, so the field is
// not here.
#[derive(Clone, Debug)]
pub struct DuplicateSourceFile {
    pub parse_options: SourceFileParseOptions,
    pub script_kind: ScriptKind,
}

impl RedirectsFile {
    // Go: fileloader.go:78 (*redirectsFile).FileName
    pub fn file_name(&self) -> String {
        self.file_name.clone()
    }

    // Go: fileloader.go:82 (*redirectsFile).Path
    pub fn path(&self) -> Path {
        self.path.clone()
    }
}

// Go: fileloader.go:86 processedFiles
// PORT: Go nil maps that stay nil until first use are `Option`. Go
// `*includeProcessor` is owned by value.
#[derive(Clone)]
pub struct ProcessedFiles {
    pub resolver: Option<Rc<Resolver>>,
    pub files: Vec<Rc<ParsedSourceFile>>,
    // duplicateSourceFiles tracks parsed files loaded during program construction
    // that were later dropped from the final program, such as losing filename
    // casing variants for the same path or files hidden behind package redirect
    // deduplication. Their parse-cache acquires still need to be balanced when
    // the program is disposed.
    pub duplicate_source_files: Vec<DuplicateSourceFile>,
    pub files_by_path: FxHashMap<Path, Rc<ParsedSourceFile>>,
    pub project_reference_file_mapper: Option<Rc<RefCell<ProjectReferenceFileMapper>>>,
    pub missing_files: Vec<String>,
    pub resolved_modules: FxHashMap<Path, ModeAwareCache<Rc<ResolvedModule>>>,
    pub type_resolutions_in_file:
        FxHashMap<Path, ModeAwareCache<Rc<ResolvedTypeReferenceDirective>>>,
    pub source_file_meta_datas: FxHashMap<Path, SourceFileMetaData>,
    pub jsx_runtime_import_specifiers: Option<FxHashMap<Path, Rc<JsxRuntimeImportSpecifier>>>,
    pub import_helpers_import_specifiers: Option<FxHashMap<Path, Node>>,
    pub lib_files: FxHashMap<Path, Rc<LibFile>>,
    // List of present unsupported extensions
    pub source_files_found_searching_node_modules: FxHashSet<Path>,
    pub include_processor: IncludeProcessor,
    // if file was included using source file and its output is actually part of program
    // this contains mapping from output to source file
    pub output_file_to_project_reference_source: Option<FxHashMap<Path, String>>,
    // Key is a file path. Value is the list of files that redirect to it (same package, different install location)
    pub redirect_targets_map: Option<FxHashMap<Path, Vec<String>>>,
    // filesByPath for redirect files
    pub redirect_files_by_path: Option<FxHashMap<Path, RedirectsFile>>,
    pub finished_processing: bool,
}

// Go: fileloader.go:117 jsxRuntimeImportSpecifier
#[derive(Clone, Debug)]
pub struct JsxRuntimeImportSpecifier {
    pub module_reference: String,
    pub specifier: Node,
}

// Go: fileloader.go:122 processAllProgramFiles
pub fn process_all_program_files(opts: ProgramOptions, single_threaded: bool) -> ProcessedFiles {
    let compiler_options = opts.config.compiler_options().clone();
    let root_files: Vec<String> = opts.config.file_names().to_vec();
    let supported_extensions =
        get_supported_extensions(&compiler_options, &[] /*extraFileExtensions*/);
    let supported_extensions_with_json_if_resolve_json_module =
        get_supported_extensions_with_json_if_resolve_json_module(
            Some(&compiler_options),
            supported_extensions.clone(),
        );
    let mut max_node_module_js_depth = 0;
    if let Some(p) = opts.config.compiler_options().max_node_module_js_depth {
        max_node_module_js_depth = p;
    }
    let current_directory = opts.host.get_current_directory().to_string();
    let mut loader = FileLoader {
        default_library_path: get_normalized_absolute_path(
            &opts.host.default_library_path(),
            &current_directory,
        ),
        compare_paths_options: ComparePathsOptions {
            use_case_sensitive_file_names: opts.host.fs().use_case_sensitive_file_names(),
            current_directory: current_directory.clone(),
        },
        files_parser: RefCell::new(FilesParser {
            max_depth: max_node_module_js_depth,
            ..Default::default()
        }),
        root_tasks: Vec::with_capacity(root_files.len() + compiler_options.lib.len()),
        supported_extensions,
        supported_extensions_with_json_if_resolve_json_module,
        resolver: None,
        total_file_count: Cell::new(0),
        lib_file_count: Cell::new(0),
        // PORT: Go uses the zero `ast.NodeFactory`, which makes synthetic nodes.
        factory: NodeFactory::new(),
        project_reference_file_mapper: Rc::new(RefCell::new(ProjectReferenceFileMapper::new(
            opts.clone(),
            opts.host.clone(),
        ))),
        dts_directories: FxHashSet::default(),
        path_for_lib_file_cache: RefCell::new(FxHashMap::default()),
        path_for_lib_file_resolutions: RefCell::new(FxHashMap::default()),
        opts,
    };
    loader.add_project_reference_tasks(single_threaded);
    let resolver_host: Rc<dyn ResolutionHost> = loader
        .project_reference_file_mapper
        .borrow()
        .host
        .clone()
        .expect("projectReferenceFileMapper.host is set until processing ends");
    loader.resolver = Some(Rc::new(new_resolver(
        resolver_host,
        compiler_options.clone(),
        &loader.opts.typings_location,
        &loader.opts.project_name,
    )));
    for (index, root_file) in root_files.iter().enumerate() {
        loader.add_root_file_task(
            root_file,
            None,
            new_file_include_reason(
                FileIncludeKind::ROOT_FILE,
                FileIncludeData::Index(index as i32),
            ),
        );
    }
    if !root_files.is_empty() && compiler_options.no_lib.is_false_or_unknown() {
        // PORT: Go `compilerOptions.Lib == nil`. `CompilerOptions.lib` is a
        // `Vec`, so an empty list is taken as nil. Go `"lib": []` gives no
        // default lib; here it gives the default lib.
        if compiler_options.lib.is_empty() {
            let name = get_default_lib_file_name(&compiler_options);
            let lib_file = loader.path_for_lib_file(&name);
            loader.add_root_task(
                &lib_file.path,
                Some(lib_file.clone()),
                new_file_include_reason(FileIncludeKind::LIB_FILE, FileIncludeData::None),
            );
        } else {
            for (index, lib) in compiler_options.lib.iter().enumerate() {
                let (name, ok) = get_lib_file_name(lib);
                if ok {
                    let lib_file = loader.path_for_lib_file(&name);
                    loader.add_root_task(
                        &lib_file.path,
                        Some(lib_file.clone()),
                        new_file_include_reason(
                            FileIncludeKind::LIB_FILE,
                            FileIncludeData::Index(index as i32),
                        ),
                    );
                }
                // !!! error on unknown name
            }
        }
    }

    if !root_files.is_empty() {
        loader.add_automatic_type_directive_tasks();
    }

    let root_tasks = loader.root_tasks.clone();
    loader.files_parser.borrow_mut().parse(&loader, &root_tasks);

    // Clear out loader and host to ensure its not used post program creation
    {
        let mut mapper = loader.project_reference_file_mapper.borrow_mut();
        mapper.loader = None;
        mapper.host = None;
    }

    let files_parser = loader.files_parser.borrow();
    files_parser.get_processed_files(&loader)
}

impl FileLoader {
    // Go: fileloader.go:187 (*fileLoader).toPath
    pub fn to_path(&self, file: &str) -> Path {
        to_path(
            file,
            &self.opts.host.get_current_directory(),
            self.opts.host.fs().use_case_sensitive_file_names(),
        )
    }

    // Go: fileloader.go:191 (*fileLoader).addRootTask
    pub fn add_root_task(
        &mut self,
        file_name: &str,
        lib_file: Option<Rc<LibFile>>,
        include_reason: Rc<FileIncludeReason>,
    ) {
        let abs_path =
            get_normalized_absolute_path(file_name, &self.opts.host.get_current_directory());
        if self
            .opts
            .config
            .compiler_options()
            .allow_non_ts_extensions
            .is_true()
            || has_extension(&abs_path)
        {
            self.root_tasks.push(Rc::new(RefCell::new(ParseTask {
                normalized_file_path: abs_path,
                lib_file,
                include_reason: Some(include_reason),
                ..Default::default()
            })));
        }
    }

    // Go: fileloader.go:202 (*fileLoader).addRootFileTask
    pub fn add_root_file_task(
        &mut self,
        file_name: &str,
        lib_file: Option<Rc<LibFile>>,
        include_reason: Rc<FileIncludeReason>,
    ) {
        let curr_dir = self.opts.host.get_current_directory().to_string();
        let abs_path = get_normalized_absolute_path(file_name, &curr_dir);
        let mut containing_file = curr_dir.clone();
        if let Some(config_file) = &self.opts.config.config_file {
            containing_file = get_normalized_absolute_path(&config_file.file_name, &curr_dir);
        }
        let (resolved_file, diagnostic) = self.get_source_file_from_reference(
            &abs_path,
            file_name,
            &containing_file,
            &include_reason,
        );
        let mut root_task = ParseTask {
            normalized_file_path: resolved_file,
            lib_file,
            include_reason: Some(include_reason.clone()),
            ..Default::default()
        };
        if let Some(diagnostic) = diagnostic {
            root_task.normalized_file_path = abs_path;
            root_task.processing_diagnostics = vec![new_explaining_processing_diagnostic(
                Some(include_reason),
                diagnostic.message,
                diagnostic.args,
            )];
        }
        self.root_tasks.push(Rc::new(RefCell::new(root_task)));
    }

    // Go: fileloader.go:229 (*fileLoader).addAutomaticTypeDirectiveTasks
    pub fn add_automatic_type_directive_tasks(&mut self) {
        let containing_directory;
        let compiler_options = self.opts.config.compiler_options();
        if !compiler_options.config_file_path.is_empty() {
            containing_directory = get_directory_path(&compiler_options.config_file_path);
        } else {
            containing_directory = self.opts.host.get_current_directory().to_string();
        }
        let containing_file_name =
            combine_paths(&containing_directory, &[INFERRED_TYPES_CONTAINING_FILE]);
        self.root_tasks.push(Rc::new(RefCell::new(ParseTask {
            normalized_file_path: containing_file_name,
            is_for_automatic_type_directive: true,
            ..Default::default()
        })));
    }

    // Go: fileloader.go:244 (*fileLoader).resolveAutomaticTypeDirectives
    #[allow(clippy::type_complexity)]
    pub fn resolve_automatic_type_directives(
        &self,
        containing_file_name: &str,
    ) -> (
        Vec<ResolvedRef>,
        ModeAwareCache<Rc<ResolvedTypeReferenceDirective>>,
        Vec<DiagAndArgs>,
        Vec<Rc<ProcessingDiagnostic>>,
    ) {
        let mut to_parse: Vec<ResolvedRef> = Vec::new();
        let mut type_resolutions_in_file: ModeAwareCache<Rc<ResolvedTypeReferenceDirective>> =
            ModeAwareCache::default();
        let mut type_resolutions_trace: Vec<DiagAndArgs> = Vec::new();
        let mut p_diagnostics: Vec<Rc<ProcessingDiagnostic>> = Vec::new();
        // PORT: Go passes the compiler host as a `module.ResolutionHost`.
        let host = CompilerResolutionHost::new(self.opts.host.clone());
        let host: &dyn ResolutionHost = &host;
        let automatic_type_directive_names =
            get_automatic_type_directive_names(self.opts.config.compiler_options(), host);
        if !automatic_type_directive_names.is_empty() {
            to_parse.reserve(automatic_type_directive_names.len());
            for name in &automatic_type_directive_names {
                // Under node16/nodenext module resolution, load `types`/ata include names as cjs resolution results by passing an `undefined` mode.
                // Under bundler module resolution, this also triggers the "import" condition to be used.
                let resolution_mode = RESOLUTION_MODE_NONE;
                let (resolved, trace) = self.resolver().resolve_type_reference_directive(
                    name,
                    containing_file_name,
                    resolution_mode,
                    None,
                );
                type_resolutions_in_file.insert(
                    ModeAwareCacheKey {
                        name: name.clone(),
                        mode: resolution_mode,
                    },
                    resolved.clone(),
                );
                type_resolutions_trace.extend(trace);
                if resolved.is_resolved() {
                    to_parse.push(ResolvedRef {
                        file_name: resolved.resolved_file_name.clone(),
                        increase_depth: resolved.is_external_library_import,
                        elide_on_depth: false,
                        include_reason: Some(new_file_include_reason(
                            FileIncludeKind::AUTOMATIC_TYPE_DIRECTIVE_FILE,
                            FileIncludeData::AutomaticTypeDirectiveFile(
                                AutomaticTypeDirectiveFileData {
                                    type_reference: name.clone(),
                                    package_id: resolved.package_id.clone(),
                                },
                            ),
                        )),
                        package_id: resolved.package_id.clone(),
                    });
                } else {
                    p_diagnostics.push(new_explaining_processing_diagnostic(
                        Some(new_file_include_reason(
                            FileIncludeKind::AUTOMATIC_TYPE_DIRECTIVE_FILE,
                            FileIncludeData::AutomaticTypeDirectiveFile(
                                AutomaticTypeDirectiveFileData {
                                    type_reference: name.clone(),
                                    package_id: PackageId::default(),
                                },
                            ),
                        )),
                        diag::Cannot_find_type_definition_file_for_0,
                        args![name],
                    ));
                }
            }
        }
        (
            to_parse,
            type_resolutions_in_file,
            type_resolutions_trace,
            p_diagnostics,
        )
    }

    // Go: fileloader.go:297 (*fileLoader).addProjectReferenceTasks
    // PORT: Go makes the project reference file mapper here. The port makes
    // it in `process_all_program_files`, because the loader struct needs a
    // value for the field. It is made from the same `opts` and host, so the
    // result is the same.
    pub fn add_project_reference_tasks(&mut self, single_threaded: bool) {
        let project_references = self.opts.config.resolved_project_reference_paths().to_vec();
        if project_references.is_empty() {
            return;
        }

        let mut parser = ProjectReferenceParser::new(self, single_threaded);
        let root_tasks = create_project_reference_parse_tasks(&project_references);
        parser.parse(root_tasks);
    }

    // Go: fileloader.go:315 (*fileLoader).sortLibs
    // PORT: Go `slices.SortFunc` is pdqsort. It is not stable for more than
    // 12 items. The port uses a stable sort. Libs with the same priority keep
    // their load order here; Go can reorder them when there are more than 12.
    pub fn sort_libs(&self, lib_files: &mut [Rc<ParsedSourceFile>]) {
        lib_files.sort_by_key(|f| self.get_default_lib_file_priority(f));
    }

    // Go: fileloader.go:321 (*fileLoader).getDefaultLibFilePriority
    pub fn get_default_lib_file_priority(&self, a: &ParsedSourceFile) -> usize {
        // defaultLibraryPath and a.FileName() are absolute and normalized; a prefix check should suffice.
        let default_library_path = remove_trailing_directory_separator(&self.default_library_path);
        let a_file_name = a.file_name();

        if a_file_name.starts_with(default_library_path)
            && a_file_name.len() > default_library_path.len()
            && a_file_name.as_bytes()[default_library_path.len()] == DIRECTORY_SEPARATOR
        {
            // avoid tspath.GetBaseFileName; we know these paths are already absolute and normalized.
            let basename = &a_file_name[a_file_name
                .rfind(DIRECTORY_SEPARATOR as char)
                .map_or(0, |i| i + 1)..];
            if basename == "lib.d.ts" || basename == "lib.es6.d.ts" {
                return 0;
            }
            let without_prefix = basename.strip_prefix("lib.").unwrap_or(basename);
            let name = without_prefix
                .strip_suffix(".d.ts")
                .unwrap_or(without_prefix);
            if let Some(index) = LIBS.iter().position(|lib| lib == name) {
                return index + 1;
            }
        }
        LIBS.len() + 2
    }

    // Go: fileloader.go:341 (*fileLoader).loadSourceFileMetaData
    pub fn load_source_file_meta_data(&self, file_name: &str) -> SourceFileMetaData {
        let package_json_scope = self
            .resolver()
            .get_package_scope_for_path(&get_directory_path(file_name));
        let module_resolution_kind = self
            .opts
            .config
            .compiler_options()
            .get_module_resolution_kind();

        let mut package_json_type = String::new();
        let mut package_json_directory = String::new();
        if let Some(scope) = package_json_scope.as_ref().filter(|scope| scope.exists()) {
            package_json_directory = scope.package_directory.clone();
            let contents = scope
                .contents
                .as_ref()
                .expect("an existing package.json scope has contents");
            let (value, ok) = contents.fields.header_fields.type_.get_value();
            if ok
                && (!file_extension_is_one_of(
                    file_name,
                    &[EXTENSION_MTS, EXTENSION_CTS, EXTENSION_MJS, EXTENSION_CJS],
                ) && ModuleResolutionKind::NODE16 <= module_resolution_kind
                    && module_resolution_kind <= ModuleResolutionKind::NODE_NEXT
                    || file_name.contains("/node_modules/"))
            {
                package_json_type = value;
            }
        }

        let implied_node_format = get_implied_node_format_for_file(file_name, &package_json_type);
        SourceFileMetaData {
            package_json_type,
            package_json_directory,
            implied_node_format,
        }
    }

    // Go: fileloader.go:364 (*fileLoader).parseSourceFile
    pub fn parse_source_file(&self, t: &ParseTask) -> Option<Rc<ParsedSourceFile>> {
        let path = self.to_path(&t.normalized_file_path);
        let options = self
            .project_reference_file_mapper
            .borrow()
            .get_compiler_options_for_file(&new_has_file_name(&t.normalized_file_path, &t.path));
        self.opts.host.get_source_file(&SourceFileParseOptions {
            file_name: t.normalized_file_path.clone(),
            path,
            external_module_indicator_options: get_external_module_indicator_options(
                &t.normalized_file_path,
                &options,
                &t.metadata,
            ),
        })
    }

    // Go: fileloader.go:378 (*fileLoader).isSupportedExtension
    pub fn is_supported_extension(&self, canonical_file_name: &str) -> bool {
        for group in &self.supported_extensions_with_json_if_resolve_json_module {
            let group: Vec<&str> = group.iter().map(String::as_str).collect();
            if file_extension_is_one_of(canonical_file_name, &group) {
                return true;
            }
        }
        false
    }

    // Go: fileloader.go:387 (*fileLoader).getSourceFileFromReference
    pub fn get_source_file_from_reference(
        &self,
        file_name: &str,
        reference_text: &str,
        containing_file: &str,
        include_reason: &FileIncludeReason,
    ) -> (String, Option<SourceFileFromReferenceDiagnostic>) {
        let options = self.opts.config.compiler_options();
        let allow_non_ts_extensions = options.allow_non_ts_extensions.is_true();
        let diagnostic_file_name = normalize_slashes(reference_text);
        let fs = self.opts.host.fs();

        if has_extension(file_name) {
            let canonical_file_name =
                get_canonical_file_name(file_name, fs.use_case_sensitive_file_names());
            if !allow_non_ts_extensions && !self.is_supported_extension(&canonical_file_name) {
                if has_js_file_extension(&canonical_file_name) {
                    return (
                        String::new(),
                        Some(SourceFileFromReferenceDiagnostic {
                            message: diag::File_0_is_a_JavaScript_file_Did_you_mean_to_enable_the_allowJs_option,
                            args: args![diagnostic_file_name],
                        }),
                    );
                }
                return (
                    String::new(),
                    Some(SourceFileFromReferenceDiagnostic {
                        message: diag::File_0_has_an_unsupported_extension_The_only_supported_extensions_are_1,
                        args: args![
                            diagnostic_file_name,
                            format!("'{}'", join_flattened_extensions(&self.supported_extensions))
                        ],
                    }),
                );
            }

            if !fs.file_exists(file_name) {
                return (
                    String::new(),
                    Some(SourceFileFromReferenceDiagnostic {
                        message: diag::File_0_not_found,
                        args: args![diagnostic_file_name],
                    }),
                );
            }

            if include_reason.is_referenced_file()
                && get_canonical_file_name(containing_file, fs.use_case_sensitive_file_names())
                    == canonical_file_name
            {
                return (
                    String::new(),
                    Some(SourceFileFromReferenceDiagnostic {
                        message: diag::A_file_cannot_have_a_reference_to_itself,
                        args: Vec::new(),
                    }),
                );
            }
            return (file_name.to_string(), None);
        }

        if allow_non_ts_extensions && fs.file_exists(file_name) {
            return (file_name.to_string(), None);
        }

        if allow_non_ts_extensions {
            return (
                String::new(),
                Some(SourceFileFromReferenceDiagnostic {
                    message: diag::File_0_not_found,
                    args: args![diagnostic_file_name],
                }),
            );
        }

        for ext in &self.supported_extensions[0] {
            let candidate = format!("{file_name}{ext}");
            if fs.file_exists(&candidate) {
                return (candidate, None);
            }
        }

        (
            String::new(),
            Some(SourceFileFromReferenceDiagnostic {
                message: diag::Could_not_resolve_the_path_0_with_the_extensions_Colon_1,
                args: args![
                    diagnostic_file_name,
                    format!(
                        "'{}'",
                        join_flattened_extensions(&self.supported_extensions)
                    )
                ],
            }),
        )
    }

    // Go: fileloader.go:434 (*fileLoader).resolveTripleslashPathReference
    pub fn resolve_tripleslash_path_reference(
        &self,
        module_name: &str,
        containing_file: &str,
        index: i32,
    ) -> (Option<ResolvedRef>, Option<Rc<ProcessingDiagnostic>>) {
        let base_path = get_directory_path(containing_file);
        let mut referenced_file_name = module_name.to_string();

        if !is_rooted_disk_path(module_name) {
            referenced_file_name = combine_paths(&base_path, &[module_name]);
        }
        let normalized_file_name = normalize_path(&referenced_file_name);
        let include_reason = new_file_include_reason(
            FileIncludeKind::REFERENCE_FILE,
            FileIncludeData::ReferencedFile(ReferencedFileData {
                file: self.to_path(containing_file),
                index,
                synthetic: Node::NIL,
            }),
        );

        let (resolved_file_name, diagnostic) = self.get_source_file_from_reference(
            &normalized_file_name,
            module_name,
            containing_file,
            &include_reason,
        );
        if let Some(diagnostic) = diagnostic {
            return (
                None,
                Some(new_explaining_processing_diagnostic(
                    Some(include_reason),
                    diagnostic.message,
                    diagnostic.args,
                )),
            );
        }

        (
            Some(ResolvedRef {
                file_name: resolved_file_name,
                include_reason: Some(include_reason),
                ..Default::default()
            }),
            None,
        )
    }

    // Go: fileloader.go:473 (*fileLoader).resolveTypeReferenceDirectives
    pub fn resolve_type_reference_directives(&self, t: &mut ParseTask) {
        let file = t
            .file
            .clone()
            .expect("resolveTypeReferenceDirectives runs on a parsed file");
        if file.type_reference_directives.is_empty() {
            return;
        }
        let meta = t.metadata.clone();

        let mut type_resolutions_in_file: ModeAwareCache<Rc<ResolvedTypeReferenceDirective>> =
            ModeAwareCache::default();
        type_resolutions_in_file.reserve(file.type_reference_directives.len());
        let mut type_resolutions_trace: Vec<DiagAndArgs> = Vec::new();
        for (index, ref_) in file.type_reference_directives.iter().enumerate() {
            let (redirect, file_name) = self
                .project_reference_file_mapper
                .borrow()
                .get_redirect_for_resolution(&new_has_file_name(file.file_name(), file.path()));
            let redirect_ref = redirect
                .as_deref()
                .map(|r| r as &dyn ModuleResolvedProjectReference);
            let resolution_mode = get_mode_for_type_reference_directive_in_file(
                ref_,
                &file,
                &meta,
                &get_compiler_options_with_redirect(
                    self.opts.config.compiler_options(),
                    redirect_ref,
                ),
            );
            let (resolved, trace) = self.resolver().resolve_type_reference_directive(
                &ref_.file_name,
                &file_name,
                resolution_mode,
                redirect_ref,
            );
            type_resolutions_in_file.insert(
                ModeAwareCacheKey {
                    name: ref_.file_name.clone(),
                    mode: resolution_mode,
                },
                resolved.clone(),
            );
            let include_reason = new_file_include_reason(
                FileIncludeKind::TYPE_REFERENCE_DIRECTIVE,
                FileIncludeData::ReferencedFile(ReferencedFileData {
                    file: t.path.clone(),
                    index: index as i32,
                    synthetic: Node::NIL,
                }),
            );
            type_resolutions_trace.extend(trace);

            if resolved.is_resolved() {
                t.add_sub_task(
                    ResolvedRef {
                        file_name: resolved.resolved_file_name.clone(),
                        increase_depth: resolved.is_external_library_import,
                        elide_on_depth: false,
                        include_reason: Some(include_reason),
                        package_id: resolved.package_id.clone(),
                    },
                    None,
                );
            } else {
                t.processing_diagnostics
                    .push(new_unknown_reference_processing_diagnostic(include_reason));
            }
        }

        t.type_resolutions_in_file = type_resolutions_in_file;
        t.type_resolutions_trace = type_resolutions_trace;
    }

    // Go: fileloader.go:526 externalHelpersModuleNameText
    // PORT: the Go constant is `EXTERNAL_HELPERS_MODULE_NAME_TEXT` in
    // checker/types.rs. It is reused here.

    // Go: fileloader.go:528 (*fileLoader).resolveImportsAndModuleAugmentations
    pub fn resolve_imports_and_module_augmentations(&self, t: &mut ParseTask) {
        let file = t
            .file
            .clone()
            .expect("resolveImportsAndModuleAugmentations runs on a parsed file");
        let meta = t.metadata.clone();

        let mut module_names: Vec<Node> =
            Vec::with_capacity(file.imports.len() + file.module_augmentations.len() + 2);

        // PORT: Go `ast.IsSourceFileJS(file)` and `ast.IsExternalModule(file)`
        // read the `ast.SourceFile` fields. The crate versions read
        // `source_file_info`, which does not exist during load, so the
        // fields of `ParsedSourceFile` are read here.
        let is_java_script_file = file.is_js();
        let is_external_module_file = file.external_module_indicator.is_some();

        let (redirect, file_name) = self
            .project_reference_file_mapper
            .borrow()
            .get_redirect_for_resolution(&new_has_file_name(file.file_name(), file.path()));
        let redirect_ref = redirect
            .as_deref()
            .map(|r| r as &dyn ModuleResolvedProjectReference);
        let options_for_file =
            get_compiler_options_with_redirect(self.opts.config.compiler_options(), redirect_ref);
        if is_java_script_file
            || (!file.is_declaration_file
                && (options_for_file.get_isolated_modules() || is_external_module_file))
        {
            if options_for_file.import_helpers.is_true() {
                let specifier =
                    self.create_synthetic_import(EXTERNAL_HELPERS_MODULE_NAME_TEXT, &file);
                module_names.push(specifier);
                t.import_helpers_import_specifier = specifier;
            }
        }

        if file.script_kind == ScriptKind::JSX || file.script_kind == ScriptKind::TSX {
            let jsx_import = get_jsx_runtime_import(
                &get_jsx_implicit_import_base_of_file(&options_for_file, &file),
                &options_for_file,
            );
            if !jsx_import.is_empty() {
                let specifier = self.create_synthetic_import(&jsx_import, &file);
                module_names.push(specifier);
                t.jsx_runtime_import_specifier = Some(Rc::new(JsxRuntimeImportSpecifier {
                    module_reference: jsx_import,
                    specifier,
                }));
            }
        }

        let imports_start = module_names.len() as i32;

        module_names.extend(file.imports.iter().copied());
        for imp in &file.module_augmentations {
            if imp.kind() == SyntaxKind::StringLiteral {
                module_names.push(*imp);
            }
            // Do nothing if it's an Identifier; we don't need to do module resolution for `declare global`.
        }

        if !module_names.is_empty() {
            let mut resolutions_in_file: ModeAwareCache<Rc<ResolvedModule>> =
                ModeAwareCache::default();
            resolutions_in_file.reserve(module_names.len());
            let mut resolutions_trace: Vec<DiagAndArgs> = Vec::new();

            for (index, entry) in module_names.iter().copied().enumerate() {
                let module_name = entry.text();
                if module_name.is_empty() {
                    continue;
                }

                let mode = get_mode_for_usage_location(
                    file.file_name(),
                    &meta,
                    entry,
                    Some(&options_for_file),
                );
                let (resolved_module, trace) = self.resolver().resolve_module_name(
                    module_name,
                    &file_name,
                    mode,
                    redirect_ref,
                );
                resolutions_in_file.insert(
                    ModeAwareCacheKey {
                        name: module_name.to_string(),
                        mode,
                    },
                    resolved_module.clone(),
                );
                resolutions_trace.extend(trace);

                if !resolved_module.is_resolved() {
                    continue;
                }

                let resolved_file_name = &resolved_module.resolved_file_name;
                let is_from_node_modules_search = resolved_module.is_external_library_import;
                // Don't treat redirected files as JS files.
                let is_js_file = !file_extension_is_one_of(
                    resolved_file_name,
                    SUPPORTED_TS_EXTENSIONS_WITH_JSON_FLAT,
                ) && self
                    .project_reference_file_mapper
                    .borrow()
                    .get_redirect_parsed_command_line_for_resolution(&new_has_file_name(
                        resolved_file_name,
                        &self.to_path(resolved_file_name),
                    ))
                    .is_none();
                let is_js_file_from_node_modules = is_from_node_modules_search
                    && is_js_file
                    && resolved_file_name.contains("/node_modules/");

                // add file to program only if:
                // - resolution was successful
                // - noResolve is falsy
                // - module name comes from the list of imports
                // - it's not a top level JavaScript module that exceeded the search max

                let import_index = index as i32 - imports_start;

                // PORT: Go passes the `*ast.SourceFile`. The crate
                // `get_resolution_diagnostic` takes the root node.
                let should_add_file = !module_name.is_empty()
                    && get_resolution_diagnostic(&options_for_file, &resolved_module, file.root)
                        .is_none()
                    && !options_for_file.no_resolve.is_true()
                    && !(is_js_file && !options_for_file.get_allow_js())
                    && (import_index < 0
                        || ((import_index as usize) < file.imports.len() && {
                            let import = file.imports[import_index as usize];
                            is_in_js_file(import) || !import.flags().intersects(NodeFlags::JS_DOC)
                        }));

                if should_add_file {
                    t.add_sub_task(
                        ResolvedRef {
                            file_name: resolved_file_name.clone(),
                            increase_depth: resolved_module.is_external_library_import,
                            elide_on_depth: is_js_file_from_node_modules,
                            include_reason: Some(new_file_include_reason(
                                FileIncludeKind::IMPORT,
                                FileIncludeData::ReferencedFile(ReferencedFileData {
                                    file: t.path.clone(),
                                    index: import_index,
                                    synthetic: if import_index < 0 { entry } else { Node::NIL },
                                }),
                            )),
                            package_id: resolved_module.package_id.clone(),
                        },
                        None,
                    );
                }
            }

            t.resolutions_in_file = resolutions_in_file;
            t.resolutions_trace = resolutions_trace;
        }
    }

    // Go: fileloader.go:634 (*fileLoader).createSyntheticImport
    pub fn create_synthetic_import(&self, text: &str, file: &ParsedSourceFile) -> Node {
        let external_helpers_module_reference =
            self.factory.new_string_literal(text, TokenFlags::NONE);
        let import_decl = self.factory.new_import_declaration(
            ModifierList::NIL,
            Node::NIL,
            external_helpers_module_reference,
            Node::NIL,
        );
        set_node_parent(external_helpers_module_reference, import_decl);
        set_node_parent(import_decl, file.root);
        external_helpers_module_reference
    }

    // Go: fileloader.go:644 (*fileLoader).pathForLibFile
    pub fn path_for_lib_file(&self, name: &str) -> Rc<LibFile> {
        if let Some(cached) = self.path_for_lib_file_cache.borrow().get(name) {
            return cached.clone();
        }

        let mut path = combine_paths(&self.default_library_path, &[name]);
        let mut replaced = false;
        if self
            .opts
            .config
            .compiler_options()
            .lib_replacement
            .is_true()
            && name != "lib.d.ts"
        {
            let library_name = get_library_name_from_lib_file_name(name);
            let resolve_from = get_inferred_library_name_resolve_from(
                self.opts.config.compiler_options(),
                &self.opts.host.get_current_directory(),
                name,
            );
            let (resolution, trace) = self.resolve_library(&library_name, &resolve_from);
            if resolution.is_resolved() {
                path = resolution.resolved_file_name.clone();
                replaced = true;
            }
            self.path_for_lib_file_resolutions
                .borrow_mut()
                .entry(self.to_path(&resolve_from))
                .or_insert_with(|| {
                    Rc::new(LibResolution {
                        library_name,
                        resolution,
                        trace,
                    })
                });
        }

        self.path_for_lib_file_cache
            .borrow_mut()
            .entry(name.to_string())
            .or_insert_with(|| {
                Rc::new(LibFile {
                    name: name.to_string(),
                    path,
                    replaced,
                })
            })
            .clone()
    }

    // Go: fileloader.go:670 (*fileLoader).resolveLibrary
    pub fn resolve_library(
        &self,
        library_name: &str,
        resolve_from: &str,
    ) -> (Rc<ResolvedModule>, Vec<DiagAndArgs>) {
        self.resolver()
            .resolve_module_name(library_name, resolve_from, ModuleKind::COMMON_JS, None)
    }

    /// Go `p.resolver`. It is set before any file is loaded.
    fn resolver(&self) -> &Resolver {
        self.resolver
            .as_ref()
            .expect("fileLoader.resolver is set before loading")
    }
}

// Go: fileloader.go:677 getLibraryNameFromLibFileName
pub fn get_library_name_from_lib_file_name(lib_file_name: &str) -> String {
    // Support resolving to lib.dom.d.ts -> @typescript/lib-dom, and
    //                      lib.dom.iterable.d.ts -> @typescript/lib-dom/iterable
    //                      lib.es2015.symbol.wellknown.d.ts -> @typescript/lib-es2015/symbol-wellknown
    let components: Vec<&str> = lib_file_name.split('.').collect();
    let mut path = String::from("@typescript/lib-");
    if components.len() > 1 {
        path.push_str(components[1]);
    }
    let mut i = 2;
    while i < components.len() && !components[i].is_empty() && components[i] != "d" {
        if i == 2 {
            path.push('/');
        } else {
            path.push('-');
        }
        path.push_str(components[i]);
        i += 1;
    }
    path
}

// Go: fileloader.go:700 getInferredLibraryNameResolveFrom
pub fn get_inferred_library_name_resolve_from(
    options: &CompilerOptions,
    current_directory: &str,
    lib_file_name: &str,
) -> String {
    let containing_directory = if !options.config_file_path.is_empty() {
        get_directory_path(&options.config_file_path)
    } else {
        current_directory.to_string()
    };
    combine_paths(
        &containing_directory,
        &[&format!("__lib_node_modules_lookup_{lib_file_name}__.ts")],
    )
}

// Go: fileloader.go:710 getModeForTypeReferenceDirectiveInFile
pub fn get_mode_for_type_reference_directive_in_file(
    ref_: &FileReference,
    file: &ParsedSourceFile,
    meta: &SourceFileMetaData,
    options: &CompilerOptions,
) -> ResolutionMode {
    if ref_.resolution_mode != RESOLUTION_MODE_NONE {
        ref_.resolution_mode
    } else {
        get_default_resolution_mode_for_file(file.file_name(), meta, options)
    }
}

// Go: fileloader.go:718 getDefaultResolutionModeForFile
// PORT: private, because program.rs has a public
// `get_default_resolution_mode_for_file` (Go program.go) with another shape.
pub(crate) fn get_default_resolution_mode_for_file(
    file_name: &str,
    meta: &SourceFileMetaData,
    options: &CompilerOptions,
) -> ResolutionMode {
    if import_syntax_affects_module_resolution(options) {
        get_implied_node_format_for_emit_worker(file_name, options.get_emit_module_kind(), meta)
    } else {
        RESOLUTION_MODE_NONE
    }
}

// Go: fileloader.go:726 getModeForUsageLocation
// PORT: private, because program.rs has a public `get_mode_for_usage_location`
// (Go program.go) with another shape. Go `options` can be nil (`None`).
pub(crate) fn get_mode_for_usage_location(
    file_name: &str,
    meta: &SourceFileMetaData,
    usage: Node,
    options: Option<&CompilerOptions>,
) -> ResolutionMode {
    let parent = usage.parent();
    if is_import_declaration(parent)
        || parent.kind() == SyntaxKind::JsImportDeclaration
        || is_export_declaration(parent)
        || is_js_doc_import_tag(parent)
    {
        let is_type_only = is_exclusively_type_only_import_or_export(parent);
        if is_type_only {
            // PORT: the Go switch on the parent kind reads `Attributes` of
            // the import declaration, export declaration or JSDoc import tag.
            // `Node::attributes` reads the field of each of these kinds.
            let (override_, ok) = match parent.kind() {
                SyntaxKind::ImportDeclaration
                | SyntaxKind::JsImportDeclaration
                | SyntaxKind::ExportDeclaration
                | SyntaxKind::JsDocImportTag => parent.attributes().get_resolution_mode_override(),
                _ => (RESOLUTION_MODE_NONE, false),
            };
            if ok {
                return override_;
            }
        }
    }
    if is_literal_type_node(parent) && is_import_type_node(parent.parent()) {
        let (override_, ok) = parent.parent().attributes().get_resolution_mode_override();
        if ok {
            return override_;
        }
    }

    if let Some(options) = options {
        if import_syntax_affects_module_resolution(options) {
            return get_emit_syntax_for_usage_location_worker(file_name, meta, usage, options);
        }
    }

    RESOLUTION_MODE_NONE
}

// Go: fileloader.go:758 importSyntaxAffectsModuleResolution
fn import_syntax_affects_module_resolution(options: &CompilerOptions) -> bool {
    let module_resolution = options.get_module_resolution_kind();
    ModuleResolutionKind::NODE16 <= module_resolution
        && module_resolution <= ModuleResolutionKind::NODE_NEXT
        || options.get_resolve_package_json_exports()
        || options.get_resolve_package_json_imports()
}

// Go: fileloader.go:764 getEmitSyntaxForUsageLocationWorker
pub(crate) fn get_emit_syntax_for_usage_location_worker(
    file_name: &str,
    meta: &SourceFileMetaData,
    usage: Node,
    options: &CompilerOptions,
) -> ResolutionMode {
    let parent = usage.parent();
    if is_require_call(parent, false /*requireStringLiteralLikeArgument*/)
        || is_external_module_reference(parent) && is_import_equals_declaration(parent.parent())
    {
        return ModuleKind::COMMON_JS;
    }
    let file_emit_mode = get_emit_module_format_of_file_worker(file_name, options, meta);
    if is_import_call(walk_up_parenthesized_expressions(parent)) {
        return if should_transform_import_call(file_name, options, file_emit_mode) {
            ModuleKind::COMMON_JS
        } else {
            ModuleKind::ES_NEXT
        };
    }
    // If we're in --module preserve on an input file, we know that an import
    // is an import. But if this is a declaration file, we'd prefer to use the
    // impliedNodeFormat. Since we want things to be consistent between the two,
    // we need to issue errors when the user writes ESM syntax in a definitely-CJS
    // file, until/unless declaration emit can indicate a true ESM import. On the
    // other hand, writing CJS syntax in a definitely-ESM file is fine, since declaration
    // emit preserves the CJS syntax.
    if file_emit_mode == ModuleKind::COMMON_JS {
        return ModuleKind::COMMON_JS;
    } else if file_emit_mode.is_non_node_esm() || file_emit_mode == ModuleKind::PRESERVE {
        return ModuleKind::ES_NEXT;
    }
    ModuleKind::NONE
}

/// Go `ast.GetJSXImplicitImportBase(options, file)` for a file that is still
/// loading.
// PORT: the crate `get_jsx_implicit_import_base` reads the pragmas through
// `source_file_info`, which does not exist during load. This is the same Go
// logic (ast/utilities.go GetJSXImplicitImportBase and
// GetPragmaFromSourceFile) on the `ParsedSourceFile` pragmas.
fn get_jsx_implicit_import_base_of_file(
    compiler_options: &CompilerOptions,
    file: &ParsedSourceFile,
) -> String {
    // Go: GetPragmaFromSourceFile, the last one wins.
    let pragma = |name: &str| file.pragmas.iter().rev().find(|pragma| pragma.name == name);
    let jsx_import_source_pragma = pragma("jsximportsource");
    let jsx_runtime_pragma = pragma("jsxruntime");
    if get_pragma_argument(jsx_runtime_pragma, "factory") == "classic" {
        return String::new();
    }
    if compiler_options.jsx == JsxEmit::REACT_JSX
        || compiler_options.jsx == JsxEmit::REACT_JSX_DEV
        || !compiler_options.jsx_import_source.is_empty()
        || jsx_import_source_pragma.is_some()
        || get_pragma_argument(jsx_runtime_pragma, "factory") == "automatic"
    {
        let mut result = get_pragma_argument(jsx_import_source_pragma, "factory");
        if result.is_empty() {
            result = compiler_options.jsx_import_source.clone();
        }
        if result.is_empty() {
            result = "react".to_string();
        }
        return result;
    }
    String::new()
}
