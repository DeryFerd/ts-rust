//! The `GOPORT_FRONTEND=go` loader: Go tsc config parsing
//! (`tsoptions.GetParsedCommandLineOfConfigFile`), the Go program loader
//! (`compiler.NewProgram`: scanner, parser, module resolution, file order)
//! and the `GoProgram` built from its node stores.
//!
//! Go: execute/tsc.go:213 (config), tsc.go:293 (host), tsc.go:301 (program).

use super::*;
use crate::ast::store::{file_store_count, file_store_file_name, file_store_parser_flags};
use crate::frontend::bundled;
use crate::frontend::compiler::{
    NewProgram, ProgramOptions, new_cached_fs_compiler_host, new_program,
};
use crate::frontend::module::ModeAwareCacheKey;
use crate::frontend::parser::{ParsedSourceFile, SourceFileParseOptions};
use crate::frontend::tsoptions::{ParseConfigHost, get_parsed_command_line_of_config_file};
use crate::frontend::tspath::Path as GoPath;
use crate::frontend::vfs::{Fs, osvfs_fs};
use rustc_hash::FxHashSet;
use std::rc::Rc;

/// The Go frontend program. It is not thread-safe, so only the loading
/// thread holds it (`GO_FRONTEND`). The checker reads `GoSharedState`.
pub(super) struct GoFrontendState {
    pub(super) program: &'static NewProgram,
}

/// Thread-safe copies of the Go frontend data that checker code reads.
/// Built once on the loading thread, before any checker exists.
// PORT: Go shares the frontend program between checker goroutines. The
// Rust frontend uses `Rc` and `RefCell`, so the values the checker asks for
// are copied here instead.
pub(super) struct GoSharedState {
    /// Go `processedFiles.resolvedModules`, by file path.
    resolved_modules: FxHashMap<String, FxHashMap<ModeAwareCacheKey, ResolvedModule>>,
    /// Go `processedFiles.jsxRuntimeImportSpecifiers`, by file path.
    jsx_runtime_import_specifiers: FxHashMap<String, (String, Node)>,
    /// Go `processedFiles.importHelpersImportSpecifiers`, by file path.
    import_helpers_import_specifiers: FxHashMap<String, Node>,
    /// Go include processor diagnostics of each program file, by file index.
    include_diagnostics: FxHashMap<usize, Vec<Diagnostic>>,
    /// Parser inputs of each program file, by file index, for lazy JSDoc.
    parse_inputs: FxHashMap<usize, LazyJsDocInput>,
    /// Go `processedFiles.sourceFilesFoundSearchingNodeModules`, by path.
    source_files_found_searching_node_modules: FxHashSet<String>,
    /// Go `Program.hasEmitBlockingDiagnostics`, by path.
    has_emit_blocking_diagnostics: FxHashSet<String>,
    /// Go `Program.toPath` inputs.
    current_directory: String,
    use_case_sensitive_file_names: bool,
}

/// What `parse_js_doc_for_node` needs from a parsed file.
struct LazyJsDocInput {
    parse_options: SourceFileParseOptions,
    text: &'static str,
    script_kind: ScriptKind,
}

thread_local! {
    /// Go `SourceFile.jsdocCache` entries added by lazy JSDoc parses on this
    /// thread. PORT: the parsed file is shared and read only, so the lazy
    /// entries live here. The slices are leaked to give `NodeSlice` a static
    /// borrow. The parsed nodes are synthetic nodes of this thread, so each
    /// thread keeps its own entries (see `WorkerSeed`).
    static LAZY_JSDOC: RefCell<FxHashMap<Node, &'static [Node]>> = RefCell::new(FxHashMap::default());
    /// The file system of a checker worker thread (Go `host.FS()`, without the cache).
    static WORKER_FS: Rc<dyn Fs> = bundled::wrap_fs(osvfs_fs());
}

/// The lazy JSDoc entries of this thread, to seed a checker worker.
pub(super) fn lazy_jsdoc_seed() -> FxHashMap<Node, &'static [Node]> {
    LAZY_JSDOC.with(|cache| cache.borrow().clone())
}

/// The number of lazy JSDoc entries on this thread.
pub(super) fn lazy_jsdoc_count() -> usize {
    LAZY_JSDOC.with(|cache| cache.borrow().len())
}

/// Installs the entries of `lazy_jsdoc_seed` on a new checker worker.
pub(super) fn install_lazy_jsdoc_seed(seed: FxHashMap<Node, &'static [Node]>) {
    LAZY_JSDOC.with(|cache| *cache.borrow_mut() = seed);
}

/// Go `tsc.System` as `ParseConfigHost` (FS and current directory).
struct System {
    fs: Rc<dyn Fs>,
    current_directory: String,
}

impl ParseConfigHost for System {
    fn fs(&self) -> Rc<dyn Fs> {
        self.fs.clone()
    }
    fn get_current_directory(&self) -> String {
        self.current_directory.clone()
    }
}

/// True unless `GOPORT_FRONTEND=legacy` selects the old ts_compiler loader.
/// The Go frontend is the default.
pub(super) fn enabled() -> bool {
    std::env::var("GOPORT_FRONTEND").map_or(true, |value| value != "legacy")
}

/// `try_load_with` for the Go frontend.
pub(super) fn try_load_with(
    config_path: &str,
    edit_options: impl FnOnce(&mut CompilerOptions),
) -> Result<&'static GoProgram, String> {
    let legacy_fs = ts_vfs::OsFileSystem::default();
    let cwd = std::env::current_dir().map_err(|e| e.to_string())?;
    let cwd = ts_path::normalize_path(&cwd.to_string_lossy().replace('\\', "/"));
    // Go: sys.FS() is bundled.WrapFS(osvfs.FS()).
    let fs = bundled::wrap_fs(osvfs_fs());
    let case_sensitivity = if fs.use_case_sensitive_file_names() {
        CaseSensitivity::Sensitive
    } else {
        CaseSensitivity::Insensitive
    };
    let mut config_abs = ts_path::resolve_path(&cwd, &[config_path]);
    // Go tsc `-p <dir>` reads `<dir>/tsconfig.json`.
    if fs.directory_exists(&config_abs) {
        config_abs = ts_path::combine_paths(&config_abs, &["tsconfig.json"]);
    }

    // Go: tsc.go:213 GetParsedCommandLineOfConfigFile with the command line
    // options. PORT: the command line raw map only marks explicit nulls,
    // and the command line here has none, so it is nil.
    let mut command_line_options = CompilerOptions::default();
    edit_options(&mut command_line_options);
    let sys = System {
        fs: fs.clone(),
        current_directory: cwd.clone(),
    };
    let (config, errors) = get_parsed_command_line_of_config_file(
        &config_abs,
        Some(&command_line_options),
        None,
        &sys,
        None,
    );
    if !errors.is_empty() {
        // Go reports these unrecoverable errors and exits.
        let messages: Vec<String> = errors
            .iter()
            .map(|d| format!("error TS{}: {}", d.code, d.localize()))
            .collect();
        return Err(messages.join("\n"));
    }
    let config = config.ok_or_else(|| format!("cannot parse {config_abs}"))?;

    // Go: tsc.go:293 NewCachedFSCompilerHost, tsc.go:301 NewProgram.
    let host = new_cached_fs_compiler_host(&cwd, fs, &bundled::lib_path(), None, None);
    let new_program: &'static NewProgram = Box::leak(Box::new(new_program(ProgramOptions {
        host,
        config: Rc::new(config),
        use_source_of_project_reference: false,
        single_threaded: Tristate::Unknown,
        typings_location: String::new(),
        project_name: String::new(),
    })));
    let options = new_program.options().clone();

    let mut parsed = FxHashMap::default();
    let mut source_file_order = Vec::new();
    for file in new_program.source_files() {
        source_file_order.push(file.store);
        parsed.insert(file.store, file.clone());
    }

    let mut files = Vec::new();
    let mut file_by_path = FxHashMap::default();
    for store in 0..file_store_count() {
        let info = match parsed.get(&store) {
            Some(file) => {
                let path = file.path().clone();
                file_by_path.insert(path.0.clone(), store);
                program_file_info(store, file, new_program, &path)
            }
            None => other_store_info(store, &cwd, case_sensitivity),
        };
        // PORT: a store that is not a program file (a config file) is never
        // bound or checked, so its root is not read.
        let root = parsed.get(&store).map_or(Node::NIL, |file| file.root);
        files.push(GoFile {
            source: None,
            root,
            parser_flags: file_store_parser_flags(store),
            info,
            node_bind: OnceLock::new(),
            file_bind: OnceLock::new(),
            flow_nodes: OnceLock::new(),
        });
    }

    let program: &'static GoProgram = Box::leak(Box::new(GoProgram {
        program: None,
        files,
        source_file_order,
        options,
        bound_symbols: OnceLock::new(),
    }));
    let frontend: &'static GoFrontendState = Box::leak(Box::new(GoFrontendState {
        program: new_program,
    }));
    GO_FRONTEND.with(|cell| {
        assert!(cell.set(frontend).is_ok(), "program already loaded");
    });
    set_prog(program);
    // After `set_prog`, like the lazy Go reads it replaces.
    let shared = GoSharedState::new(new_program, &parsed);
    let program_state: &'static ProgramState = Box::leak(Box::new(ProgramState {
        cwd,
        case_sensitivity,
        fs: legacy_fs,
        file_by_path,
        config_diagnostics: Vec::new(),
        program_diagnostics: Vec::new(),
        external_locations: Vec::new(),
        resolved_modules: OnceLock::new(),
        common_source_directory: OnceLock::new(),
        file_associations: OnceLock::new(),
        declaration_diagnostic_cache: Mutex::new(FxHashMap::default()),
        go: Some(shared),
    }));
    set_state(program_state);
    Ok(program)
}

/// `SourceFileInfo` of a program file, from the Go parser fields and the
/// Go program (metadata, default library).
fn program_file_info(
    store: usize,
    file: &ParsedSourceFile,
    p: &NewProgram,
    path: &GoPath,
) -> SourceFileInfo {
    let info = SourceFileInfo {
        file_name: file.file_name().to_string(),
        path: path.0.clone(),
        is_declaration_file: file.is_declaration_file,
        language_variant: file.language_variant,
        script_kind: file.script_kind,
        pragmas: file.pragmas.clone(),
        check_js_directive: file.check_js_directive,
        referenced_files: file.referenced_files.clone(),
        type_reference_directives: file.type_reference_directives.clone(),
        lib_reference_directives: file.lib_reference_directives.clone(),
        comment_directives: file.comment_directives.clone(),
        diagnostics: file.diagnostics.clone(),
        js_diagnostics: file.js_diagnostics.clone(),
        jsdoc_diagnostics: file.jsdoc_diagnostics.clone(),
        has_lazy_js_doc: file.has_lazy_js_doc,
        is_default_library: p.is_source_file_default_library(path),
        meta_data: p.get_source_file_meta_data(path),
        trivia: crate::ast::go_view::TriviaRuns::default(),
        late: OnceLock::new(),
    };
    let late = LateSourceFileInfo {
        file_index: store,
        external_module_indicator: file.external_module_indicator,
        reparsed_clones: file.reparsed_clones.clone(),
        imports: file.imports.clone(),
        module_augmentations: file.module_augmentations.clone(),
        ambient_module_names: file.ambient_module_names.clone(),
        uses_uri_style_node_core_modules: file.uses_uri_style_node_core_modules,
        jsdoc_cache: file.jsdoc_cache.clone(),
        post_bind: OnceLock::new(),
    };
    assert!(info.late.set(late).is_ok());
    info
}

/// `SourceFileInfo` of a store that is not a program file (a tsconfig or
/// an extended config). Only the name and the text are read, for
/// diagnostic locations.
fn other_store_info(store: usize, cwd: &str, case_sensitivity: CaseSensitivity) -> SourceFileInfo {
    let file_name = file_store_file_name(store).to_string();
    let info = SourceFileInfo {
        path: ts_path::canonicalize(&file_name, cwd, case_sensitivity),
        file_name,
        is_declaration_file: false,
        language_variant: LanguageVariant::STANDARD,
        script_kind: ScriptKind::JSON,
        pragmas: Vec::new(),
        check_js_directive: None,
        referenced_files: Vec::new(),
        type_reference_directives: Vec::new(),
        lib_reference_directives: Vec::new(),
        comment_directives: Vec::new(),
        diagnostics: Vec::new(),
        js_diagnostics: Vec::new(),
        jsdoc_diagnostics: Vec::new(),
        has_lazy_js_doc: false,
        is_default_library: false,
        meta_data: SourceFileMetaData::default(),
        trivia: crate::ast::go_view::TriviaRuns::default(),
        late: OnceLock::new(),
    };
    let late = LateSourceFileInfo {
        file_index: store,
        external_module_indicator: Node::NIL,
        reparsed_clones: Vec::new(),
        imports: Vec::new(),
        module_augmentations: Vec::new(),
        ambient_module_names: Vec::new(),
        uses_uri_style_node_core_modules: Tristate::Unknown,
        jsdoc_cache: FxHashMap::default(),
        post_bind: OnceLock::new(),
    };
    assert!(info.late.set(late).is_ok());
    info
}

impl GoSharedState {
    /// Copies what the checker reads from the frontend program.
    fn new(p: &NewProgram, parsed: &FxHashMap<usize, Rc<ParsedSourceFile>>) -> Self {
        let files = &p.processed_files;
        let resolved_modules = files
            .resolved_modules
            .iter()
            .map(|(path, cache)| {
                let cache = cache
                    .iter()
                    .map(|(key, resolved)| (key.clone(), (**resolved).clone()))
                    .collect();
                (path.0.clone(), cache)
            })
            .collect();
        let jsx_runtime_import_specifiers = files
            .jsx_runtime_import_specifiers
            .iter()
            .flatten()
            .map(|(path, s)| (path.0.clone(), (s.module_reference.clone(), s.specifier)))
            .collect();
        let import_helpers_import_specifiers = files
            .import_helpers_import_specifiers
            .iter()
            .flatten()
            .map(|(path, &specifier)| (path.0.clone(), specifier))
            .collect();
        let include_diagnostics = parsed
            .iter()
            .map(|(&store, file)| {
                let diagnostics = p
                    .include_processor
                    .get_diagnostics(p)
                    .borrow_mut()
                    .get_diagnostics_for_file(file.file_name());
                (store, diagnostics)
            })
            .collect();
        let parse_inputs = parsed
            .iter()
            .map(|(&store, file)| {
                let input = LazyJsDocInput {
                    parse_options: file.parse_options.clone(),
                    text: file.text,
                    script_kind: file.script_kind,
                };
                (store, input)
            })
            .collect();
        let source_files_found_searching_node_modules = files
            .source_files_found_searching_node_modules
            .iter()
            .map(|path| path.0.clone())
            .collect();
        let has_emit_blocking_diagnostics = p
            .has_emit_blocking_diagnostics
            .iter()
            .map(|path| path.0.clone())
            .collect();
        Self {
            has_emit_blocking_diagnostics,
            current_directory: p.get_current_directory(),
            use_case_sensitive_file_names: p.use_case_sensitive_file_names(),
            resolved_modules,
            jsx_runtime_import_specifiers,
            import_helpers_import_specifiers,
            include_diagnostics,
            parse_inputs,
            source_files_found_searching_node_modules,
        }
    }

    // Go: ast/ast.go:2614 (*SourceFile).resolveJSDoc (slow path; the caller
    // has checked the parser cache).
    pub(super) fn resolve_js_doc(&self, file: Node, node: Node) -> &'static [Node] {
        if let Some(jsdocs) = LAZY_JSDOC.with(|cache| cache.borrow().get(&node).copied()) {
            return jsdocs;
        }
        let input = self
            .parse_inputs
            .get(&file.file_index())
            .expect("not a Go frontend program file");
        let jsdocs: &'static [Node] = Box::leak(
            crate::frontend::parser::parse_js_doc_for_node(
                &input.parse_options,
                input.text,
                input.script_kind,
                node,
            )
            .into_boxed_slice(),
        );
        LAZY_JSDOC.with(|cache| cache.borrow_mut().insert(node, jsdocs));
        jsdocs
    }

    // Go: compiler/program.go:122 FileExists
    // PORT: the loading thread asks the program host (with its cache). A
    // checker worker asks its own uncached copy of the same file system.
    pub(super) fn file_exists(&self, path: &str) -> bool {
        if let Some(go) = GO_FRONTEND.with(|cell| cell.get().copied()) {
            return go.program.file_exists(path);
        }
        WORKER_FS.with(|fs| fs.file_exists(path))
    }

    // Go: compiler/program.go:494 GetResolvedModule
    pub(super) fn get_resolved_module(
        &self,
        file: Node,
        module_reference: &str,
        mode: ResolutionMode,
    ) -> Option<ResolvedModule> {
        let path = &source_file_info(file).path;
        self.resolved_modules
            .get(path)?
            .get(&ModeAwareCacheKey {
                name: module_reference.to_string(),
                mode,
            })
            .cloned()
    }

    // Go: compiler/program.go:1916 GetJSXRuntimeImportSpecifier
    pub(super) fn get_jsx_runtime_import_specifier(&self, path: &str) -> (String, Node) {
        self.jsx_runtime_import_specifiers
            .get(path)
            .cloned()
            .unwrap_or((String::new(), Node::NIL))
    }

    // Go: compiler/program.go:1922 GetImportHelpersImportSpecifier
    // Go: compiler/program.go:1225 IsEmitBlocked
    pub(super) fn is_emit_blocked(&self, emit_file_name: &str) -> bool {
        let path = crate::frontend::tspath::to_path(
            emit_file_name,
            &self.current_directory,
            self.use_case_sensitive_file_names,
        );
        self.has_emit_blocking_diagnostics.contains(&path.0)
    }

    // Go: compiler/program.go:1912 IsSourceFileFromExternalLibrary
    pub(super) fn is_source_file_from_external_library(&self, path: &str) -> bool {
        self.source_files_found_searching_node_modules
            .contains(path)
    }

    pub(super) fn get_import_helpers_import_specifier(&self, path: &str) -> Node {
        self.import_helpers_import_specifiers
            .get(path)
            .copied()
            .unwrap_or(Node::NIL)
    }

    // Go: compiler/program.go:678 GetIncludeProcessorDiagnostics (the
    // include processor part)
    pub(super) fn get_include_processor_diagnostics(&self, file: Node) -> Vec<Diagnostic> {
        self.include_diagnostics
            .get(&file.file_index())
            .cloned()
            .unwrap_or_default()
    }
}
