//! The `GOPORT_FRONTEND=go` loader: Go tsc config parsing
//! (`tsoptions.GetParsedCommandLineOfConfigFile`), the Go program loader
//! (`compiler.NewProgram`: scanner, parser, module resolution, file order)
//! and the `GoProgram` built from its node stores.
//!
//! Go: execute/tsc.go:213 (config), tsc.go:293 (host), tsc.go:301 (program).

use super::*;
use crate::ast::store::{
    file_store_file_name, file_store_parser_flags, publish_file_stores, unpublished_file_ids,
};
use crate::frontend::bundled;
use crate::frontend::compiler::{
    NewProgram, ProgramOptions, TraceFn, new_cached_fs_compiler_host, new_program,
};
use crate::frontend::module::ModeAwareCacheKey;
use crate::frontend::parser::{ParsedSourceFile, SourceFileParseOptions};
use crate::frontend::tsoptions::{
    ParseConfigHost, ParsedCommandLine, get_parsed_command_line_of_config_file,
};
use crate::frontend::tspath::Path as GoPath;
use crate::frontend::vfs::{Fs, osvfs_fs};
use rustc_hash::FxHashSet;
use std::rc::Rc;
use ts_diagnostics::Message;

/// The Go frontend program. It is not thread-safe, so only the loading
/// thread holds it (`FRONTENDS`). The checker reads `GoSharedState`.
pub(super) struct GoFrontendState {
    pub(super) program: &'static NewProgram,
}

/// Thread-safe copies of the Go frontend data that checker code reads.
/// Built once on the loading thread, before any checker exists.
// PORT: Go shares the frontend program between checker goroutines. The
// Rust frontend uses `Rc` and `RefCell`, so the values the checker asks for
// are copied here instead.
pub(super) struct GoSharedState {
    /// Go `processedFiles.resolvedModules`, by file path. Shared with the
    /// version this one was updated from when the frontend shares the map.
    resolved_modules: Arc<ResolvedModules>,
    /// Go `processedFiles.jsxRuntimeImportSpecifiers`, by file path.
    jsx_runtime_import_specifiers: FxHashMap<String, (String, Node)>,
    /// Go `processedFiles.importHelpersImportSpecifiers`, by file path.
    import_helpers_import_specifiers: FxHashMap<String, Node>,
    /// Go include processor diagnostics of each program file, by file index.
    include_diagnostics: FxHashMap<usize, Vec<Diagnostic>>,
    /// Parser inputs of each program file, by file index, for lazy JSDoc.
    /// A file id is one file version, so versions share the inputs of the
    /// files they share.
    parse_inputs: FxHashMap<usize, Arc<LazyJsDocInput>>,
    /// Go `GetParseFileRedirect` of each resolved module file name that is
    /// not a program file and has a redirect. Shared like `resolved_modules`.
    parse_file_redirects: Arc<FxHashMap<String, String>>,
    /// Go `processedFiles.redirectTargetsMap`, by path.
    redirect_targets: FxHashMap<String, Vec<String>>,
    /// Go `GetSourceFileFromReference` of each preserved `/// <reference
    /// path>` of a program file, by file index and reference file name.
    references: FxHashMap<(usize, String), Node>,
    /// Go `Program.CommonSourceDirectory`.
    common_source_directory: String,
    /// Go `processedFiles.outputFileToProjectReferenceSource`, by path.
    output_file_to_project_reference_source: FxHashMap<String, String>,
    /// Go `projectReferenceFileMapper.sourceToProjectReference`, by path.
    source_to_project_reference: FxHashMap<String, SourceOutputAndProjectReference>,
    /// Go `projectReferenceFileMapper.outputDtsToProjectReference`, by path.
    output_dts_to_project_reference: FxHashMap<String, SourceOutputAndProjectReference>,
    /// Go `projectReferenceFileMapper.opts.canUseProjectReferenceSource()`.
    can_use_project_reference_source: bool,
    /// Go `GetRedirectForResolution` of each program file, by file index.
    /// A file with no redirect has no entry.
    redirects_for_resolution: FxHashMap<usize, Arc<ResolvedProjectReference>>,
    /// Go `GetResolvedProjectReferences`.
    resolved_project_references: Vec<Option<Arc<ResolvedProjectReference>>>,
    /// Go `Program.GetSymlinkCache`. Shared with the version this one was
    /// updated from when the frontend shares the cache.
    known_symlinks: Arc<crate::modulespecifiers::symlinks::KnownSymlinks>,
    /// Go `processedFiles.sourceFilesFoundSearchingNodeModules`, by path.
    /// Shared like `resolved_modules`.
    source_files_found_searching_node_modules: Arc<FxHashSet<String>>,
    /// Go `Program.hasEmitBlockingDiagnostics`, by path.
    has_emit_blocking_diagnostics: FxHashSet<String>,
    /// Go `Program.toPath` inputs.
    current_directory: String,
    use_case_sensitive_file_names: bool,
}

type FrontendSourceOutput = crate::frontend::tsoptions::SourceOutputAndProjectReference;

/// `GoSharedState::resolved_modules`.
type ResolvedModules = FxHashMap<String, FxHashMap<ModeAwareCacheKey, ResolvedModule>>;

/// Thread-safe copies of the frontend project references. Go shares one
/// `*ParsedCommandLine` per referenced project, so each is copied once.
#[derive(Default)]
struct ProjectReferenceCopies {
    resolved: FxHashMap<*const ParsedCommandLine, Arc<ResolvedProjectReference>>,
}

impl ProjectReferenceCopies {
    fn resolved(&mut self, parsed: &Rc<ParsedCommandLine>) -> Arc<ResolvedProjectReference> {
        self.resolved
            .entry(Rc::as_ptr(parsed))
            .or_insert_with(|| {
                Arc::new(ResolvedProjectReference::new(
                    (**parsed.compiler_options()).clone(),
                    parsed.common_source_directory().to_string(),
                ))
            })
            .clone()
    }

    fn entry(&mut self, entry: &FrontendSourceOutput) -> SourceOutputAndProjectReference {
        let parsed = entry
            .resolved
            .upgrade()
            .expect("the referenced project command line is alive");
        SourceOutputAndProjectReference {
            source: entry.source.clone(),
            output_dts: entry.output_dts.clone(),
            resolved: self.resolved(&parsed),
        }
    }
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
    times: &mut CompileTimes,
) -> Result<&'static GoProgram, String> {
    let opts = load_config(config_path, edit_options, times)?;
    // Go: tsc.go:298 startTracingIfNeeded. PORT: the warning goes to stdout
    // (Go `sys.Writer()`) as Go bytes, like `trace_from_sys`. A program
    // version (`try_load_version`) does not trace, as Go tsc starts tracing
    // only here.
    if let Some(warning) = crate::tracing::start_tracing_if_needed(&opts.config, false) {
        let _ =
            crate::execute::tsc::write_go_output(&mut std::io::stdout().lock(), warning.as_bytes());
    }
    // Go: tsc.go:305 times `NewProgram`. PORT: the port's `NewProgram` is
    // `install_new_program`, which also builds the Go files, as the build
    // worker times it.
    let parse_start = std::time::Instant::now();
    let program = install_new_program(opts);
    times.parse_time = parse_start.elapsed();
    program
}

/// `try_load_version` (program.rs).
pub(super) fn try_load_version(
    config_path: &str,
    edit_options: impl FnOnce(&mut CompilerOptions),
) -> Result<&'static GoProgram, String> {
    // A new version parses with no current program, like the first load.
    let _scope = crate::core::enter_program(None);
    let cwd = current_directory()?;
    let opts = load_config(config_path, edit_options, &mut CompileTimes::default())?;
    let np: &'static NewProgram = Box::leak(Box::new(new_program(opts)));
    Ok(build_program(np, Entry::Version, cwd, None))
}

/// `update_program_version` (program.rs).
pub(super) fn update_program_version(
    old: &'static GoProgram,
    changed_file: &str,
) -> (&'static GoProgram, bool) {
    let old_np = FRONTENDS
        .with(|frontends| frontends.borrow().get(&old.id).copied())
        .expect("the old program version has no frontend on this thread")
        .program;
    let cwd = old.state.get().expect("program not loaded").cwd.clone();
    // A new version parses with no current program, like the first load.
    let _scope = crate::core::enter_program(None);
    // PORT: Go watch gives `UpdateProgram` a host whose cache no longer has
    // the changed file. A new cached host over the OS file system reads it
    // again.
    let host_cwd = old_np.get_current_directory();
    let host = new_cached_fs_compiler_host(
        &host_cwd,
        bundled::wrap_fs(osvfs_fs()),
        &bundled::lib_path(),
        None,
        Some(trace_from_sys()),
    );
    let changed_path = crate::frontend::tspath::to_path(
        changed_file,
        &host_cwd,
        old_np.use_case_sensitive_file_names(),
    );
    let (np, _, reused) = old_np.update_program(&changed_path, host);
    let np: &'static NewProgram = Box::leak(Box::new(np));
    (build_program(np, Entry::Version, cwd, Some(old)), reused)
}

/// `new_program_version` (program.rs).
pub(super) fn new_program_version(
    np: &'static NewProgram,
    previous: Option<&'static GoProgram>,
) -> &'static GoProgram {
    // The files are built and published with no current program, like the
    // first load. `build_program` makes the new version current for its
    // state.
    let _scope = crate::core::enter_program(None);
    build_program(np, Entry::Version, np.get_current_directory(), previous)
}

thread_local! {
    /// Source files that were parsed on this thread outside a program load
    /// (the language server parse cache) and are not published yet, by
    /// store id. A program that does not include such a file still
    /// publishes it, with its parser fields, so a later program can share it.
    static PARSED_UNPUBLISHED: RefCell<FxHashMap<usize, Rc<ParsedSourceFile>>> =
        RefCell::new(FxHashMap::default());

    /// Parser inputs of the files of `PARSED_UNPUBLISHED` that a publish
    /// gave no program, by store id, for lazy JSDoc
    /// (`resolve_js_doc_outside_program`).
    static OUTSIDE_PARSE_INPUTS: RefCell<FxHashMap<usize, Arc<LazyJsDocInput>>> =
        RefCell::new(FxHashMap::default());
}

/// `note_parsed_source_file` (program.rs).
pub(super) fn note_parsed_source_file(file: &Rc<ParsedSourceFile>) {
    if !crate::ast::is_published(file.store) {
        PARSED_UNPUBLISHED.with(|parsed| parsed.borrow_mut().insert(file.store, file.clone()));
    }
}

/// `publish_parsed_files` (program.rs).
pub(super) fn publish_parsed_files(cwd: &str) {
    let parsed = FxHashMap::default();
    let files = go_files_of_unpublished_stores(&parsed, cwd, case_sensitivity());
    publish_file_stores(files);
}

/// Go `parseJSDocForNode` for a lazy JSDoc read of `node` (ast/ast.go:2614
/// `resolveJSDoc`). The result is cached in `LAZY_JSDOC`.
fn parse_lazy_js_doc(input: &LazyJsDocInput, node: Node) -> &'static [Node] {
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

/// Go ast/ast.go:2614 `(*SourceFile).resolveJSDoc` (slow path) for a file
/// of an alias resolver program. Such a file is in no program
/// (`OUTSIDE_PARSE_INPUTS`) or in a program version loaded on this thread.
/// None when this thread has no parser inputs for `file`.
pub(super) fn resolve_js_doc_outside_program(file: Node, node: Node) -> Option<&'static [Node]> {
    if let Some(jsdocs) = LAZY_JSDOC.with(|cache| cache.borrow().get(&node).copied()) {
        return Some(jsdocs);
    }
    let store = file.file_index();
    let input = OUTSIDE_PARSE_INPUTS
        .with(|inputs| inputs.borrow().get(&store).cloned())
        .or_else(|| {
            let path = GoPath(source_file_info(file).path.clone());
            let programs: Vec<&'static NewProgram> = FRONTENDS.with(|frontends| {
                frontends
                    .borrow()
                    .values()
                    .map(|frontend| frontend.program)
                    .collect()
            });
            programs.into_iter().find_map(|program| {
                let parsed = program
                    .get_source_file_by_path(&path)
                    .filter(|parsed| parsed.store == store)?;
                Some(Arc::new(LazyJsDocInput {
                    parse_options: parsed.parse_options.clone(),
                    text: parsed.text,
                    script_kind: parsed.script_kind,
                }))
            })
        })?;
    Some(parse_lazy_js_doc(&input, node))
}

/// The case sensitivity of the OS file system.
fn case_sensitivity() -> CaseSensitivity {
    if osvfs_fs().use_case_sensitive_file_names() {
        CaseSensitivity::Sensitive
    } else {
        CaseSensitivity::Insensitive
    }
}

/// The Go files of this thread's unpublished stores, in store id order
/// (`publish_file_stores`). `parsed` holds the program files by store id.
/// A store that is not a program file is a file that the language server
/// parsed outside a program load (`PARSED_UNPUBLISHED`), or a config file.
fn go_files_of_unpublished_stores(
    parsed: &FxHashMap<usize, Rc<ParsedSourceFile>>,
    cwd: &str,
    case_sensitivity: CaseSensitivity,
) -> Vec<GoFile> {
    let outside = PARSED_UNPUBLISHED.with(|outside| std::mem::take(&mut *outside.borrow_mut()));
    // `files[i]` is the GoFile of store `unpublished_file_ids().start + i`.
    let mut files = Vec::new();
    for store in unpublished_file_ids() {
        if !parsed.contains_key(&store)
            && let Some(file) = outside.get(&store)
        {
            let input = Arc::new(LazyJsDocInput {
                parse_options: file.parse_options.clone(),
                text: file.text,
                script_kind: file.script_kind,
            });
            OUTSIDE_PARSE_INPUTS.with(|inputs| inputs.borrow_mut().insert(store, input));
        }
        let file = parsed.get(&store).or_else(|| outside.get(&store));
        let info = match file {
            Some(file) => program_file_info(store, file),
            None => other_store_info(store, cwd, case_sensitivity),
        };
        // PORT: a store that is not a parsed source file (a config file) is
        // never bound or checked, so its root is not read.
        let root = file.map_or(Node::NIL, |file| file.root);
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
    files
}

/// The process current directory, normalized.
fn current_directory() -> Result<String, String> {
    let cwd = crate::frontend::vfs::os_current_dir().map_err(|e| e.to_string())?;
    Ok(ts_path::normalize_path(&cwd.replace('\\', "/")))
}

/// Go tsc config parsing and compiler host (tsc.go:213 and :293): the
/// program options of a load. It records the config time in `times`.
fn load_config(
    config_path: &str,
    edit_options: impl FnOnce(&mut CompilerOptions),
    times: &mut CompileTimes,
) -> Result<ProgramOptions, String> {
    let cwd = current_directory()?;
    // Go: sys.FS() is bundled.WrapFS(osvfs.FS()).
    let fs = bundled::wrap_fs(osvfs_fs());
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
    let config_start = std::time::Instant::now();
    let (config, errors) = get_parsed_command_line_of_config_file(
        &config_abs,
        Some(&command_line_options),
        None,
        &sys,
        None,
    );
    times.config_time = config_start.elapsed();
    if !errors.is_empty() {
        // Go reports these unrecoverable errors and exits.
        let messages: Vec<String> = errors
            .iter()
            .map(|d| {
                format!(
                    "error TS{}: {}",
                    d.code,
                    d.localize(&crate::locale::DEFAULT)
                )
            })
            .collect();
        return Err(messages.join("\n"));
    }
    let config = config.ok_or_else(|| format!("cannot parse {config_abs}"))?;

    // Go: tsc.go:293 NewCachedFSCompilerHost, tsc.go:301 NewProgram.
    let host =
        new_cached_fs_compiler_host(&cwd, fs, &bundled::lib_path(), None, Some(trace_from_sys()));
    Ok(ProgramOptions {
        host,
        config: Rc::new(config),
        use_source_of_project_reference: false,
        single_threaded: Tristate::Unknown,
        typings_location: String::new(),
        project_name: String::new(),
    })
}

/// Go `compiler.NewProgram` for a config that is already parsed. It builds
/// the Go files and installs the program for the process. Call it once.
pub(super) fn install_new_program(opts: ProgramOptions) -> Result<&'static GoProgram, String> {
    let cwd = current_directory()?;
    let new_program: &'static NewProgram = Box::leak(Box::new(new_program(opts)));
    Ok(build_program(new_program, Entry::Only, cwd, None))
}

/// How `build_program` makes a program known.
enum Entry {
    /// The program of a one-program process (`core::set_prog`).
    Only,
    /// A program version of a multi-program process
    /// (`core::register_program_version`). The caller parses and builds it
    /// inside `core::enter_program(None)`.
    Version,
}

/// Builds the Go files of the stores that `np` parsed, publishes them and
/// makes the `GoProgram` of `np` with its state. Program files that an
/// earlier version published keep their `GoFile`. `cwd` is the current
/// directory of the process. `previous` is the version that `np` was
/// updated from, if it is still loaded; the new state shares its copies of
/// unchanged frontend data (`GoSharedState::new`).
fn build_program(
    np: &'static NewProgram,
    entry: Entry,
    cwd: String,
    previous: Option<&'static GoProgram>,
) -> &'static GoProgram {
    let legacy_fs = ts_vfs::OsFileSystem::default();
    let case_sensitivity = case_sensitivity();
    let options = np.options().clone();

    let mut parsed = FxHashMap::default();
    let mut source_file_order = Vec::new();
    for file in np.source_files() {
        source_file_order.push(file.store);
        parsed.insert(file.store, file.clone());
    }

    let files = go_files_of_unpublished_stores(&parsed, &cwd, case_sensitivity);

    // Program files in ascending store id, the insert order of the first
    // load, then the Go program fields of each.
    let mut stores: Vec<usize> = parsed.keys().copied().collect();
    stores.sort_unstable();
    let mut file_by_path = FxHashMap::default();
    let mut file_meta = FxHashMap::default();
    for store in stores {
        let path = parsed[&store].path();
        file_by_path.insert(path.0.clone(), store);
        let meta = FileProgramMeta {
            meta_data: np.get_source_file_meta_data(path),
            is_default_library: np.is_source_file_default_library(path),
        };
        file_meta.insert(store, meta);
    }
    // Go: filesparser.go:425 `filesByPath[task.path] = packageIdFile`. A
    // package dedup redirect path maps to the first file with the same
    // package id, so `GetSourceFileByPath` finds that file.
    for (path, file) in np.files_by_path() {
        file_by_path.entry(path.0.clone()).or_insert(file.store);
    }

    let id = next_program_id();
    let frontend: &'static GoFrontendState = Box::leak(Box::new(GoFrontendState { program: np }));
    FRONTENDS.with(|frontends| {
        assert!(
            frontends.borrow_mut().insert(id, frontend).is_none(),
            "program {id} already loaded"
        );
    });
    // The stores become read-only here, before the program is installed.
    publish_file_stores(files);
    let program: &'static GoProgram = Box::leak(Box::new(GoProgram {
        id,
        program: None,
        source_file_order,
        options,
        bound_symbols: OnceLock::new(),
        state: OnceLock::new(),
    }));
    let _scope = match entry {
        Entry::Only => {
            set_prog(program);
            None
        }
        Entry::Version => {
            register_program_version(program);
            Some(crate::core::enter_program(Some(program)))
        }
    };
    // With the program current, like the lazy Go reads it replaces.
    let previous = previous.and_then(|old| {
        let old_np = FRONTENDS.with(|frontends| frontends.borrow().get(&old.id).copied())?;
        let old_shared = old.state.get()?.go.as_ref()?;
        Some((old_np.program, old_shared))
    });
    let shared = GoSharedState::new(np, &parsed, previous);
    let program_state: &'static ProgramState = Box::leak(Box::new(ProgramState {
        cwd,
        case_sensitivity,
        fs: legacy_fs,
        file_by_path,
        file_meta,
        config_diagnostics: Vec::new(),
        program_diagnostics: Vec::new(),
        external_locations: Vec::new(),
        resolved_modules: OnceLock::new(),
        common_source_directory: OnceLock::new(),
        file_associations: OnceLock::new(),
        declaration_diagnostic_cache: Mutex::new(FxHashMap::default()),
        go: Some(shared),
        alias_resolver: false,
    }));
    assert!(program.state.set(program_state).is_ok());
    program
}

/// Go `getTraceFromSys` (tsc.go:280) with no testing hooks:
/// `tsc.GetTraceWithWriterFromSys` (tsc/emit.go:20) writes each localized
/// trace message and a newline to `sys.Writer()`, which is stdout.
fn trace_from_sys() -> TraceFn {
    Rc::new(|msg: &'static Message, args: Vec<String>| {
        let text = format_message(msg, &args);
        // PORT: `text` is in the port form (see
        // `scanner_util::GO_STRING_MARKER`); stdout gets its Go bytes.
        let _ = crate::execute::tsc::write_go_output(
            &mut std::io::stdout().lock(),
            format!("{text}\n").as_bytes(),
        );
    })
}

/// `SourceFileInfo` of a program file, from the Go parser fields. The Go
/// program fields are in `ProgramState::file_meta`.
fn program_file_info(store: usize, file: &ParsedSourceFile) -> SourceFileInfo {
    let info = SourceFileInfo {
        file_name: file.file_name().to_string(),
        path: file.path().0.clone(),
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
    /// Copies what the checker reads from the frontend program. `previous`
    /// is the frontend program and shared state of the version that `p` was
    /// updated from. Its copies are shared where `p` shares the frontend
    /// data they were copied from, so a new version copies only what
    /// changed. A version is never freed, so each copy would leak once per
    /// edit.
    fn new(
        p: &NewProgram,
        parsed: &FxHashMap<usize, Rc<ParsedSourceFile>>,
        previous: Option<(&NewProgram, &GoSharedState)>,
    ) -> Self {
        let files = &p.processed_files;
        // Go `UpdateProgram` shares the resolutions and the project
        // references with the old program and keeps every file path, so
        // equal pointers mean equal copies.
        let same_resolutions = previous.filter(|(old, _)| {
            Rc::ptr_eq(
                &files.resolved_modules,
                &old.processed_files.resolved_modules,
            ) && match (
                &files.project_reference_file_mapper,
                &old.processed_files.project_reference_file_mapper,
            ) {
                (Some(mapper), Some(old_mapper)) => Rc::ptr_eq(mapper, old_mapper),
                (mapper, old_mapper) => mapper.is_none() && old_mapper.is_none(),
            }
        });
        let resolved_modules = match same_resolutions {
            Some((_, old)) => Arc::clone(&old.resolved_modules),
            None => Arc::new(
                files
                    .resolved_modules
                    .iter()
                    .map(|(path, cache)| {
                        let cache = cache
                            .iter()
                            .map(|(key, resolved)| (key.clone(), (**resolved).clone()))
                            .collect();
                        (path.0.clone(), cache)
                    })
                    .collect(),
            ),
        };
        let jsx_runtime_import_specifiers = files
            .jsx_runtime_import_specifiers
            .iter()
            .flat_map(|map| map.iter())
            .map(|(path, s)| (path.0.clone(), (s.module_reference.clone(), s.specifier)))
            .collect();
        let import_helpers_import_specifiers = files
            .import_helpers_import_specifiers
            .iter()
            .flat_map(|map| map.iter())
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
                let shared = previous.and_then(|(_, old)| old.parse_inputs.get(&store));
                let input = shared.map_or_else(
                    || {
                        Arc::new(LazyJsDocInput {
                            parse_options: file.parse_options.clone(),
                            text: file.text,
                            script_kind: file.script_kind,
                        })
                    },
                    Arc::clone,
                );
                (store, input)
            })
            .collect();
        // Go reads these lazily from the program. The only file names the
        // checker asks about are resolved module names.
        let parse_file_redirects = match same_resolutions {
            Some((_, old)) => Arc::clone(&old.parse_file_redirects),
            None => Arc::new(
                files
                    .resolved_modules
                    .values()
                    .flat_map(|cache| cache.values())
                    .map(|resolved| &resolved.resolved_file_name)
                    .filter(|name| !name.is_empty() && p.get_source_file(name).is_none())
                    .filter_map(|name| {
                        let redirect = p.get_parse_file_redirect(name);
                        (!redirect.is_empty()).then(|| (name.clone(), redirect))
                    })
                    .collect(),
            ),
        };
        let redirect_targets = files
            .redirect_targets_map
            .iter()
            .flat_map(|map| map.iter())
            .map(|(path, targets)| (path.0.clone(), targets.clone()))
            .collect();
        // Go: the declaration transformer asks only for preserved references
        // (transformers/declarations/transform.go:469).
        let references = parsed
            .iter()
            .flat_map(|(&store, file)| {
                file.referenced_files
                    .iter()
                    .filter(|r| r.preserve)
                    .map(move |r| {
                        let target = p
                            .get_source_file_from_reference(file, r)
                            .map_or(Node::NIL, |target| target.root);
                        ((store, r.file_name.clone()), target)
                    })
            })
            .collect();
        // Go: compiler/program.go:1562 CommonSourceDirectory.
        // PORT: Go computes it on first use, and `checkSourceFilesBelongToPath`
        // then adds include diagnostics. Go uses it first either in
        // `verifyCompilerOptions`, which the frontend program has already run,
        // or during emit, after the program diagnostics are reported. So the
        // value is computed here without the check, which adds nothing.
        let common_source_directory = crate::frontend::outputpaths::get_common_source_directory(
            p.options(),
            || {
                files
                    .files
                    .iter()
                    .filter(|file| {
                        p.source_file_may_be_emitted(file, false) && !file.is_declaration_file
                    })
                    .map(|file| file.file_name().to_string())
                    .collect()
            },
            &p.get_current_directory(),
            p.use_case_sensitive_file_names(),
            None,
        );
        let output_file_to_project_reference_source = files
            .output_file_to_project_reference_source
            .iter()
            .flat_map(|map| map.iter())
            .map(|(path, source)| (path.0.clone(), source.clone()))
            .collect();
        let mut project_references = ProjectReferenceCopies::default();
        let mapper = p.mapper();
        let mut copy_map = |map: &FxHashMap<GoPath, Rc<FrontendSourceOutput>>| {
            map.iter()
                .map(|(path, entry)| (path.0.clone(), project_references.entry(entry)))
                .collect::<FxHashMap<_, _>>()
        };
        let source_to_project_reference = copy_map(&mapper.source_to_project_reference);
        let output_dts_to_project_reference = copy_map(&mapper.output_dts_to_project_reference);
        let can_use_project_reference_source = mapper.opts.can_use_project_reference_source();
        drop(mapper);
        // Go asks for the redirect of checker files only, which are program files.
        let redirects_for_resolution = parsed
            .iter()
            .filter_map(|(&store, file)| {
                let redirect = p.get_redirect_for_resolution(&**file)?;
                Some((store, project_references.resolved(&redirect)))
            })
            .collect();
        let resolved_project_references = p
            .get_resolved_project_references()
            .iter()
            .map(|r| r.as_ref().map(|r| project_references.resolved(r)))
            .collect();
        // PORT: Go builds the symlink cache on first use. It reads only the
        // loaded program, so building it here gives the same value.
        let symlinks = p.get_symlink_cache();
        let known_symlinks = match previous {
            Some((old_p, old)) if Rc::ptr_eq(&symlinks, &old_p.get_symlink_cache()) => {
                Arc::clone(&old.known_symlinks)
            }
            _ => Arc::new((*symlinks).clone()),
        };
        let source_files_found_searching_node_modules = match previous {
            Some((old_p, old))
                if Rc::ptr_eq(
                    &files.source_files_found_searching_node_modules,
                    &old_p
                        .processed_files
                        .source_files_found_searching_node_modules,
                ) =>
            {
                Arc::clone(&old.source_files_found_searching_node_modules)
            }
            _ => Arc::new(
                files
                    .source_files_found_searching_node_modules
                    .iter()
                    .map(|path| path.0.clone())
                    .collect(),
            ),
        };
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
            parse_file_redirects,
            redirect_targets,
            references,
            common_source_directory,
            output_file_to_project_reference_source,
            source_to_project_reference,
            output_dts_to_project_reference,
            can_use_project_reference_source,
            redirects_for_resolution,
            resolved_project_references,
            known_symlinks,
            source_files_found_searching_node_modules,
        }
    }

    // Go: compiler/program.go:165 GetSourceOfProjectReferenceIfOutputIncluded
    // (the map lookup; the caller falls back to the file name)
    pub(super) fn get_source_of_project_reference_if_output_included(
        &self,
        path: &str,
    ) -> Option<&str> {
        self.output_file_to_project_reference_source
            .get(path)
            .map(String::as_str)
    }

    // Go: compiler/projectreferencefilemapper.go:64 getProjectReferenceFromSource
    pub(super) fn get_project_reference_from_source(
        &self,
        path: &str,
    ) -> Option<&SourceOutputAndProjectReference> {
        self.source_to_project_reference.get(path)
    }

    // Go: compiler/projectreferencefilemapper.go:68 getProjectReferenceFromOutputDts
    pub(super) fn get_project_reference_from_output_dts(
        &self,
        path: &str,
    ) -> Option<&SourceOutputAndProjectReference> {
        self.output_dts_to_project_reference.get(path)
    }

    // Go: compiler/projectreferencefilemapper.go:72 isSourceFromProjectReference
    pub(super) fn is_source_from_project_reference(&self, path: &str) -> bool {
        self.can_use_project_reference_source
            && self.get_project_reference_from_source(path).is_some()
    }

    // Go: compiler/program.go:190 GetRedirectForResolution (for program files)
    pub(super) fn get_redirect_for_resolution(
        &self,
        file: Node,
    ) -> Option<&ResolvedProjectReference> {
        self.redirects_for_resolution
            .get(&file.file_index())
            .map(|r| &**r)
    }

    // Go: compiler/program.go:199 GetResolvedProjectReferences
    pub(super) fn get_resolved_project_references(&self) -> Vec<Option<&ResolvedProjectReference>> {
        self.resolved_project_references
            .iter()
            .map(|r| r.as_deref())
            .collect()
    }

    // Go: compiler/program.go:1562 CommonSourceDirectory
    pub(super) fn common_source_directory(&self) -> &str {
        &self.common_source_directory
    }

    // Go: compiler/program.go:2017 GetSymlinkCache
    pub(crate) fn known_symlinks(&self) -> &crate::modulespecifiers::symlinks::KnownSymlinks {
        &self.known_symlinks
    }

    // Go: compiler/program.go:195 GetParseFileRedirect (for resolved module
    // file names)
    pub(super) fn get_parse_file_redirect(&self, file_name: &str) -> Option<&str> {
        self.parse_file_redirects.get(file_name).map(String::as_str)
    }

    // Go: compiler/program.go:157 GetRedirectTargets
    pub(super) fn get_redirect_targets(&self, path: &str) -> Vec<String> {
        self.redirect_targets.get(path).cloned().unwrap_or_default()
    }

    // Go: compiler/program.go:226 GetSourceFileFromReference (for the
    // preserved references of a program file)
    pub(super) fn get_source_file_from_reference(&self, origin: Node, r: &FileReference) -> Node {
        self.references
            .get(&(origin.file_index(), r.file_name.clone()))
            .copied()
            .expect("not a preserved reference of a program file")
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
        parse_lazy_js_doc(input, node)
    }

    // Go: compiler/program.go:122 FileExists
    // PORT: the loading thread asks the program host (with its cache). A
    // checker worker asks its own uncached copy of the same file system.
    pub(super) fn file_exists(&self, path: &str) -> bool {
        let id = prog().id;
        if let Some(go) = FRONTENDS.with(|frontends| frontends.borrow().get(&id).copied()) {
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

    // Go: compiler/program.go:1922 GetImportHelpersImportSpecifier
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
