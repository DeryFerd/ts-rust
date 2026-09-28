//! Go `compiler` package (Program, checker pool, diagnostics pipeline) plus
//! the parser-side `ast.SourceFile` fields that the checker reads.
//!
//! The graph (files, parse trees, module resolution) comes from
//! `ts_compiler::Program::load_config_graph_unchecked`. This file adds the
//! Go `SourceFile` fields the Rust parser does not produce (pragmas, external
//! module indicator, imports, module augmentations, metadata), the Go
//! `Program` methods as free functions, the Go checker pool and the tsc
//! diagnostics pipeline and non-pretty formatter.
//!
//! Use: `let program = load(config_path); bind_all();` then the diagnostics
//! functions below. `load` installs the program for the process; the
//! loading thread also keeps the frontend program and the checker pool.
//!
//! A multi-program process (watch, language server, tests) loads program
//! versions with `try_load_version` and `update_program_version`, reads one
//! inside `core::enter_program`, and frees its checker pool with
//! `release_program`. The loading thread keeps the frontend program and the
//! checker pool of each version, by program id.

use crate::execute::tsc::compile::CompileTimes;
use crate::gostd::{Context, context};
use crate::prelude::*;
use std::borrow::Cow;
use std::ops::Deref;
use std::sync::{Arc, Mutex, OnceLock, PoisonError};
use ts_path::CaseSensitivity;
use ts_vfs::FileSystem;

mod go_frontend;
pub mod ls_program;
mod verify_options;

// ---------------------------------------------------------------------------
// Types
// ---------------------------------------------------------------------------

/// Go `ast.PragmaArgument`.
#[derive(Clone, Debug, Default)]
pub struct PragmaArgument {
    pub name: String,
    pub value: String,
    pub range: TextRange,
}

/// Go `ast.Pragma`. `kind` is the comment kind (Go `CommentRange.Kind`).
#[derive(Clone, Debug)]
pub struct Pragma {
    pub name: String,
    pub args: IndexMap<String, PragmaArgument>,
    pub range: TextRange,
    pub kind: SyntaxKind,
}

/// Go `ast.CheckJsDirective`.
#[derive(Clone, Copy, Debug, Default)]
pub struct CheckJsDirective {
    pub enabled: bool,
    pub range: TextRange,
}

/// Go `ast.FileReference`.
#[derive(Clone, Debug, Default)]
pub struct FileReference {
    pub range: TextRange,
    pub file_name: String,
    pub resolution_mode: ResolutionMode,
    pub preserve: bool,
}

/// Go `ast.CommentDirective`.
#[derive(Clone, Copy, Debug, Default)]
pub struct CommentDirective {
    pub loc: TextRange,
    pub kind: CommentDirectiveKind,
}

/// Go `ast.SourceFileMetaData`.
#[derive(Clone, Debug, Default, PartialEq)]
pub struct SourceFileMetaData {
    pub package_json_type: String,
    pub package_json_directory: String,
    pub implied_node_format: ModuleKind,
}

/// Go `module.PackageId`.
#[derive(Clone, Debug, Default, PartialEq, Eq, Hash)]
pub struct PackageId {
    pub name: String,
    pub sub_module_name: String,
    pub version: String,
    pub peer_dependencies: String,
}

/// Go `module.ResolvedModule`.
#[derive(Clone, Default)]
pub struct ResolvedModule {
    pub resolved_file_name: String,
    pub original_path: String,
    pub extension: String,
    pub resolved_using_ts_extension: bool,
    pub package_id: PackageId,
    pub is_external_library_import: bool,
    pub alternate_result: String,
    pub resolution_diagnostics: Vec<Diagnostic>,
}

impl ResolvedModule {
    // Go: module/types.go IsResolved
    #[must_use]
    pub fn is_resolved(&self) -> bool {
        !self.resolved_file_name.is_empty()
    }
}

/// Go `*tsoptions.ParsedCommandLine` for a resolved project reference.
#[derive(Clone)]
pub struct ResolvedProjectReference {
    compiler_options: CompilerOptions,
    common_source_directory: String,
}

impl ResolvedProjectReference {
    /// A copy of the parts of a referenced project's command line that the
    /// checker reads.
    pub(crate) fn new(compiler_options: CompilerOptions, common_source_directory: String) -> Self {
        ResolvedProjectReference {
            compiler_options,
            common_source_directory,
        }
    }

    // Go: tsoptions/parsedcommandline.go CompilerOptions
    #[must_use]
    pub fn compiler_options(&self) -> &CompilerOptions {
        &self.compiler_options
    }

    // Go: tsoptions/parsedcommandline.go CommonSourceDirectory
    #[must_use]
    pub fn common_source_directory(&self) -> &str {
        &self.common_source_directory
    }
}

/// Go `tsoptions.SourceOutputAndProjectReference`.
#[derive(Clone)]
pub struct SourceOutputAndProjectReference {
    pub source: String,
    pub output_dts: String,
    /// PORT: Go shares one `*ParsedCommandLine` between the entries of a
    /// referenced project, so this is an `Arc`.
    pub resolved: Arc<ResolvedProjectReference>,
}

/// Go `ast.SourceFile` fields set by the parser and the program.
///
/// The fields here are computed from the source text before the program is
/// installed. The fields that walk the tree (external module indicator,
/// imports, ...) are in `LateSourceFileInfo`, reached through `Deref`, and
/// are set by `install`.
// PORT: the program sets Go `SourceFile.Metadata` and the default library
// flag, and program versions that share a file version can differ in them,
// so they are in `ProgramState::file_meta`.
pub struct SourceFileInfo {
    pub file_name: String,
    pub path: String,
    pub is_declaration_file: bool,
    pub language_variant: LanguageVariant,
    pub script_kind: ScriptKind,
    pub pragmas: Vec<Pragma>,
    pub check_js_directive: Option<CheckJsDirective>,
    pub referenced_files: Vec<FileReference>,
    pub type_reference_directives: Vec<FileReference>,
    pub lib_reference_directives: Vec<FileReference>,
    pub comment_directives: Vec<CommentDirective>,
    // PERF: the diagnostic lists borrow the leaked parsed file of the Go
    // frontend instead of copying it. The legacy path leaks its own lists.
    pub diagnostics: &'static [Diagnostic],
    pub js_diagnostics: &'static [Diagnostic],
    pub jsdoc_diagnostics: &'static [Diagnostic],
    /// True when a JSDoc cache miss means "not parsed" (Go parses lazily).
    pub has_lazy_js_doc: bool,
    /// Go `SourceFile.ContainsNonASCII`: the scanner decoded a non-ASCII
    /// rune. `ast::source_file_get_position_map` reads it.
    pub contains_non_ascii: bool,
    /// Trivia runs of the text. They map the Rust token-start ranges to Go
    /// full-start ranges (see `ast::go_view`).
    pub trivia: crate::ast::go_view::TriviaRuns,
    late: OnceLock<LateSourceFileInfo>,
}

impl Deref for SourceFileInfo {
    type Target = LateSourceFileInfo;

    fn deref(&self) -> &LateSourceFileInfo {
        self.late
            .get()
            .expect("SourceFileInfo tree fields read before program::install")
    }
}

/// Go `ast.SourceFile` fields that need the installed tree.
pub struct LateSourceFileInfo {
    pub file_index: usize,
    pub external_module_indicator: Node,
    // PERF: like the diagnostic lists, `reparsed_clones` and `jsdoc_cache`
    // borrow leaked data. The JSDoc cache has one list per host node, so a
    // copy costs one allocation per entry.
    pub reparsed_clones: &'static [Node],
    pub imports: Vec<Node>,
    pub module_augmentations: Vec<Node>,
    pub ambient_module_names: Vec<String>,
    pub uses_uri_style_node_core_modules: Tristate,
    /// Go `SourceFile.jsdocCache`: parsed JSDoc nodes by host node.
    pub jsdoc_cache: &'static FxHashMap<Node, Vec<Node>>,
    post_bind: OnceLock<PostBindInfo>,
}

/// The JSDoc cache of a file with no eager entries.
static EMPTY_JSDOC_CACHE: FxHashMap<Node, Vec<Node>> =
    FxHashMap::with_hasher(rustc_hash::FxBuildHasher);

/// Go `ast.SourceFile` fields that the binder sets but that live on the
/// SourceFile in Go.
pub struct PostBindInfo {
    pub common_js_module_indicator: Node,
}

static NOT_BOUND: PostBindInfo = PostBindInfo {
    common_js_module_indicator: Node::NIL,
};

impl Deref for LateSourceFileInfo {
    type Target = PostBindInfo;

    // PORT: Go `SourceFile.CommonJSModuleIndicator` is set by the binder
    // (binder.go:924-943). The Rust binder stores it in `FileBindData`.
    // Before the file is bound the value is nil and not cached.
    fn deref(&self) -> &PostBindInfo {
        if let Some(info) = self.post_bind.get() {
            return info;
        }
        let file = crate::ast::go_file(self.file_index);
        let Some(file_bind) = file.file_bind.get() else {
            return &NOT_BOUND;
        };
        self.post_bind.get_or_init(|| PostBindInfo {
            common_js_module_indicator: file_bind.common_js_module_indicator,
        })
    }
}

/// Go `checkerPool` (compiler pool). Checkers are created on first use.
/// Each checker lives on its own worker thread; the pool holds the job
/// queue of each worker. Only the loading thread has pools, one for each
/// program version (`POOLS`).
struct CheckerPool {
    workers: Vec<std::sync::mpsc::Sender<Job>>,
    threads: Vec<std::thread::JoinHandle<()>>,
}

impl CheckerPool {
    /// Stops the workers: each drops its checker and frees its synthetic
    /// nodes, then it closes their job queues and waits for each thread to
    /// end, so the checkers and the nodes they made are freed on return.
    fn shut_down(self) {
        for thread in self.stop() {
            // A job panic stays in its job result, so a worker ends normally.
            let _ = thread.join();
        }
    }

    /// `shut_down` without the wait: the workers drop their checkers, free
    /// their synthetic nodes and end while the caller goes on. Nothing waits
    /// for them; at process exit a worker that is still freeing just stops.
    fn shut_down_in_background(self) {
        drop(self.stop());
    }

    /// Sends each worker the job that drops its checker and frees its
    /// synthetic nodes, closes the job queues and returns the worker
    /// threads.
    fn stop(self) -> Vec<std::thread::JoinHandle<()>> {
        // A pool that only ends with the process forgets its checkers and
        // synthetic nodes (see `create_checkers`); a released program frees
        // them here.
        for worker in &self.workers {
            let _ = worker.send(Box::new(|| {
                drop(WORKER_CHECKER.with(|slot| slot.borrow_mut().take()));
                free_synthetic_nodes();
                WORKER_RELEASED.with(|released| released.set(true));
            }));
        }
        drop(self.workers);
        self.threads
    }
}

/// Work for one checker worker. It runs on the worker thread, where
/// `with_checker_at` reaches that worker's checker.
type Job = Box<dyn FnOnce() + Send>;

/// The result of a job, or the payload of its panic.
type JobResult<R> = std::thread::Result<R>;

/// A located diagnostic whose file is not a program source file (for example
/// the tsconfig). Go keeps a SourceFile for it; we keep the printed location.
struct ExternalLocation {
    code: i32,
    pos: i32,
    end: i32,
    args: Vec<String>,
    file_name: String,
    line: i32,
    character: i32,
}

/// Program-level state that `GoProgram` does not hold. One per program
/// version, in `GoProgram::state`; read it with `state()`.
pub(crate) struct ProgramState {
    cwd: String,
    case_sensitivity: CaseSensitivity,
    fs: ts_vfs::OsFileSystem,
    file_by_path: FxHashMap<String, usize>,
    /// The Go `SourceFile` fields that the program sets, by file id, for
    /// each program file.
    file_meta: FxHashMap<usize, FileProgramMeta>,
    config_diagnostics: Vec<Diagnostic>,
    program_diagnostics: Vec<Diagnostic>,
    external_locations: Vec<ExternalLocation>,
    resolved_modules:
        OnceLock<IndexMap<String, IndexMap<(String, ResolutionMode), ResolvedModule>>>,
    common_source_directory: OnceLock<String>,
    /// Checker index for each file index (Go `fileAssociations`). Set when
    /// the checker pool is made.
    file_associations: OnceLock<Vec<usize>>,
    /// Go `Program.declarationDiagnosticCache`.
    declaration_diagnostic_cache: Mutex<FxHashMap<Node, Vec<Diagnostic>>>,
    /// The thread-safe copy of the Go frontend data that the checker reads
    /// (`GOPORT_FRONTEND=go`). None on the legacy path. The frontend program
    /// itself is in `FRONTENDS`, on the loading thread only.
    go: Option<go_frontend::GoSharedState>,
    /// True for the program of an autoimport alias resolver
    /// (`new_alias_resolver_program`). Its resolver is in `ALIAS_RESOLVERS`.
    alias_resolver: bool,
}

/// Go `SourceFile.IsDefaultLibrary` (read through the program) and
/// `SourceFile.Metadata` of one program file.
struct FileProgramMeta {
    meta_data: SourceFileMetaData,
    is_default_library: bool,
}

thread_local! {
    /// The Go frontend program of each program version, by `GoProgram::id`.
    /// Only the thread that loaded a program has it: the frontend data is
    /// not thread-safe.
    static FRONTENDS: RefCell<FxHashMap<u32, &'static go_frontend::GoFrontendState>> =
        RefCell::new(FxHashMap::default());
}

/// The state of the current program (`prog()`).
fn state() -> &'static ProgramState {
    prog().state.get().copied().expect("program not loaded")
}

/// The Go frontend program, or None on the legacy path. Panics on a checker
/// worker thread, which must use the copies in `ProgramState::go`.
fn go_frontend() -> Option<&'static go_frontend::GoFrontendState> {
    state().go.as_ref()?;
    let id = prog().id;
    Some(FRONTENDS.with(|frontends| {
        *frontends
            .borrow()
            .get(&id)
            .expect("the Go frontend program is read on the loading thread only")
    }))
}

// ---------------------------------------------------------------------------
// Alias resolver programs (Go ls/autoimport/aliasresolver.go)
// ---------------------------------------------------------------------------

/// The Go `checker.Program` methods of the autoimport alias resolver
/// (`ls/autoimport/aliasresolver.go`) that read the files and module
/// resolutions it adds while its checker runs. Go gives the other methods a
/// constant or panics, and the `program.rs` functions do the same for an
/// alias resolver program.
pub trait AliasResolverProgram {
    /// Go `GetSourceFile`.
    fn source_file(&self, file_name: &str) -> Node;
    /// Go `GetSourceFileForResolvedModule`.
    fn source_file_for_resolved_module(&self, file_name: &str) -> Node;
    /// Go `GetResolvedModule`.
    fn resolved_module(
        &self,
        file: Node,
        module_reference: &str,
        mode: ResolutionMode,
    ) -> ResolvedModule;
}

thread_local! {
    /// The resolver of each alias resolver program of this thread, by
    /// `GoProgram::id`, while its `AliasResolverProgramScope` lives.
    static ALIAS_RESOLVERS: RefCell<FxHashMap<u32, Rc<dyn AliasResolverProgram>>> =
        RefCell::new(FxHashMap::default());
}

/// The resolver of the current program when it is an alias resolver program.
fn alias_resolver() -> Option<Rc<dyn AliasResolverProgram>> {
    if !state().alias_resolver {
        return None;
    }
    let id = prog().id;
    let resolver = ALIAS_RESOLVERS.with(|resolvers| resolvers.borrow().get(&id).cloned());
    Some(resolver.expect("an alias resolver program is read on its thread while its scope lives"))
}

/// Go `panic("unimplemented")`: the alias resolver's `checker.Program`
/// methods that Go does not implement (aliasresolver.go:141-230).
#[track_caller]
fn alias_resolver_unimplemented() {
    if state().alias_resolver {
        go_panic("unimplemented".to_string());
    }
}

/// From `new_alias_resolver_program`. The program is current on this thread
/// while the scope lives (an `ls_program::ProgramGuard`). On drop the
/// program forgets its resolver; do not use its checker after that.
pub struct AliasResolverProgramScope {
    program: &'static GoProgram,
    _guard: ls_program::ProgramGuard,
}

impl AliasResolverProgramScope {
    /// The alias resolver program.
    #[must_use]
    pub fn program(&self) -> &'static GoProgram {
        self.program
    }
}

impl Drop for AliasResolverProgramScope {
    fn drop(&mut self) {
        let id = self.program.id;
        let resolver = ALIAS_RESOLVERS.with(|resolvers| resolvers.borrow_mut().remove(&id));
        drop(resolver);
    }
}

/// Go `checker.NewChecker(aliasResolver, nil)` (ls/autoimport): makes the
/// program that the checker reads and makes it current until the scope
/// drops. `root_files` are Go `aliasResolver.SourceFiles()`. `files` are
/// every file that the checker can read (the root files too); they must be
/// published, and they are bound here if they are not yet. `options` are Go
/// `aliasResolver.Options()`, `current_directory` and
/// `use_case_sensitive_file_names` come from the resolver's host, and
/// `resolver` answers the lazy methods (`AliasResolverProgram`).
// PORT: Go needs no program: the resolver is the `checker.Program`. A
// checker here reads its program version (`prog()`), and it copies the
// binder lineage when it is made (`SymbolArena::for_checker`). So the
// program copies the lineage after `files` are bound, and a file bound
// later is not in its checkers' arenas. Go `GetResolvedModules` is nil, so
// the program has no resolved modules. The program shell stays leaked like
// other program versions (multi-program M2, M3).
pub fn new_alias_resolver_program(
    options: CompilerOptions,
    root_files: &[Node],
    files: &[Node],
    current_directory: &str,
    use_case_sensitive_file_names: bool,
    resolver: Rc<dyn AliasResolverProgram>,
) -> AliasResolverProgramScope {
    let case_sensitivity = if use_case_sensitive_file_names {
        CaseSensitivity::Sensitive
    } else {
        CaseSensitivity::Insensitive
    };
    let file_by_path = files
        .iter()
        .map(|&file| (source_file_info(file).path.clone(), file.file_index()))
        .collect();
    let program: &'static GoProgram = Box::leak(Box::new(GoProgram {
        id: next_program_id(),
        program: None,
        source_file_order: root_files.iter().map(|file| file.file_index()).collect(),
        options,
        bound_symbols: OnceLock::new(),
        state: OnceLock::new(),
    }));
    let program_state: &'static ProgramState = Box::leak(Box::new(ProgramState {
        cwd: current_directory.to_string(),
        case_sensitivity,
        fs: ts_vfs::OsFileSystem::default(),
        file_by_path,
        file_meta: FxHashMap::default(),
        config_diagnostics: Vec::new(),
        program_diagnostics: Vec::new(),
        external_locations: Vec::new(),
        resolved_modules: OnceLock::from(IndexMap::new()),
        common_source_directory: OnceLock::new(),
        file_associations: OnceLock::new(),
        declaration_diagnostic_cache: Mutex::new(FxHashMap::default()),
        go: None,
        alias_resolver: true,
    }));
    assert!(program.state.set(program_state).is_ok());
    register_program_version(program);
    let bound_symbols = {
        let mut lineage = LINEAGE.lock().unwrap_or_else(PoisonError::into_inner);
        let symbols = lineage.get_or_insert_with(SymbolArena::new);
        for &file in files {
            bind_source_file(file, symbols);
        }
        symbols.clone()
    };
    assert!(program.bound_symbols.set(bound_symbols).is_ok());
    ALIAS_RESOLVERS.with(|resolvers| resolvers.borrow_mut().insert(program.id, resolver));
    AliasResolverProgramScope {
        program,
        _guard: ls_program::enter_version(program),
    }
}

// ---------------------------------------------------------------------------
// Loading
// ---------------------------------------------------------------------------

/// Loads the config graph at `config_path`, builds the Go files and
/// installs the program for the process. Panics on a load error.
pub fn load(config_path: &str) -> &'static GoProgram {
    match try_load(config_path) {
        Ok(program) => program,
        Err(message) => panic!("cannot load program {config_path}: {message}"),
    }
}

/// `load` with the error returned. The program is leaked: it lives for the
/// rest of the process, like the Go program in `tsc`.
pub fn try_load(config_path: &str) -> Result<&'static GoProgram, String> {
    try_load_with(config_path, |_| {})
}

/// `try_load` with a hook that edits the compiler options before the files
/// are built. Use it for command line overrides, for example `--noEmit`.
pub fn try_load_with(
    config_path: &str,
    edit_options: impl FnOnce(&mut CompilerOptions),
) -> Result<&'static GoProgram, String> {
    try_load_timed(config_path, edit_options, &mut CompileTimes::default())
}

/// `try_load_with` that also records the Go `CompileTimes.ConfigTime` and
/// `ParseTime` (execute/tsc.go:214 and :306) in `times`.
// PORT: the legacy loader reads the config graph and parses the files in
// one call, so all of its time is parse time.
pub fn try_load_timed(
    config_path: &str,
    edit_options: impl FnOnce(&mut CompilerOptions),
    times: &mut CompileTimes,
) -> Result<&'static GoProgram, String> {
    if go_frontend::enabled() {
        return go_frontend::try_load_with(config_path, edit_options, times);
    }
    let parse_start = std::time::Instant::now();
    let result = try_load_legacy(config_path, edit_options);
    times.parse_time = parse_start.elapsed();
    result
}

/// `try_load_with` for the legacy ts_compiler loader.
fn try_load_legacy(
    config_path: &str,
    edit_options: impl FnOnce(&mut CompilerOptions),
) -> Result<&'static GoProgram, String> {
    let fs = ts_vfs::OsFileSystem::default();
    let cwd = std::env::current_dir().map_err(|e| e.to_string())?;
    let cwd = ts_path::normalize_path(&cwd.to_string_lossy().replace('\\', "/"));
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
    let compiler_program = ts_compiler::Program::load_config_graph_unchecked(&fs, &config_abs)
        .map_err(|e| e.to_string())?;
    let compiler_program: &'static ts_compiler::Program = Box::leak(Box::new(compiler_program));

    let mut options = from_ts_options(compiler_program.options());
    options.config_file_path = compiler_program
        .config_file_path()
        .map_or_else(|| config_abs.clone(), str::to_string);
    edit_options(&mut options);

    let mut files = Vec::new();
    let mut file_by_path = FxHashMap::default();
    let mut file_meta = FxHashMap::default();
    for (index, id) in compiler_program
        .semantic_source_order()
        .into_iter()
        .enumerate()
    {
        let source = compiler_program
            .source_file_by_id(id)
            .ok_or_else(|| format!("missing source file for {id:?}"))?;
        let parser_flags = compute_parser_flags(index, source);
        let root = Node::new(index, source.parse.source_file);
        let (info, meta) = build_early_info(
            index,
            source,
            &parser_flags,
            &options,
            &cwd,
            case_sensitivity,
            &fs,
        );
        file_by_path.insert(info.path.clone(), index);
        file_meta.insert(index, meta);
        files.push(GoFile {
            source: Some(source),
            root,
            parser_flags,
            info,
            node_bind: OnceLock::new(),
            file_bind: OnceLock::new(),
            flow_nodes: OnceLock::new(),
        });
    }

    let mut config_diagnostics = Vec::new();
    let mut program_diagnostics = Vec::new();
    let mut external_locations = Vec::new();
    convert_program_diagnostics(
        compiler_program,
        &files,
        &file_by_path,
        &options,
        &cwd,
        case_sensitivity,
        &mut config_diagnostics,
        &mut program_diagnostics,
        &mut external_locations,
    );

    // The legacy files have no node stores; they become the first publish.
    let file_count = files.len();
    crate::ast::publish_file_stores(files);
    let source_file_order = (0..file_count).collect();
    let program: &'static GoProgram = Box::leak(Box::new(GoProgram {
        id: next_program_id(),
        program: Some(compiler_program),
        source_file_order,
        options,
        bound_symbols: OnceLock::new(),
        state: OnceLock::new(),
    }));
    let program_state: &'static ProgramState = Box::leak(Box::new(ProgramState {
        cwd,
        case_sensitivity,
        fs,
        file_by_path,
        file_meta,
        config_diagnostics,
        program_diagnostics,
        external_locations,
        resolved_modules: OnceLock::new(),
        common_source_directory: OnceLock::new(),
        file_associations: OnceLock::new(),
        declaration_diagnostic_cache: Mutex::new(FxHashMap::default()),
        go: None,
        alias_resolver: false,
    }));
    assert!(program.state.set(program_state).is_ok());
    install(program);
    record_legacy_import_helpers_import_specifiers();
    Ok(program)
}

/// Installs `program` for the process (`core::set_prog`) and computes the
/// Go SourceFile fields that need the tree: Go `finishSourceFile`
/// (reparsed clones, external module indicator) and
/// `collectExternalModuleReferences`. The files of `program` must be
/// published (`crate::ast::publish_file_stores`) and its state set first.
pub fn install(program: &'static GoProgram) {
    set_prog(program);
    for &index in &program.source_file_order {
        let file = crate::ast::go_file(index);
        let late = build_late_info(index, file);
        assert!(
            file.info.late.set(late).is_ok(),
            "SourceFileInfo installed twice"
        );
    }
}

/// The symbol arena of every file version bound so far, in any program
/// version. It only grows, so the symbol ids of a file version stay valid
/// in every program that shares the file (Go `SourceFile.BindOnce`).
static LINEAGE: Mutex<Option<SymbolArena>> = Mutex::new(None);

// Go: compiler/program.go:445 BindSourceFiles
// PORT: Go binds files in parallel into per-file symbol tables. Here every
// file binds into the shared `LINEAGE` arena, and `prog().bound_symbols` is
// a copy of it after the program files are bound. `Checker::new` uses the
// same initializer, so the first of the two to run binds. Files bind in
// parallel, each into its own arena (`bind_files_parallel`), and join the
// lineage in file order with the ids a serial bind gives. With
// `--singleThreaded` they bind last-queued-first
// (`bind_files_last_queued_first`). A file that an earlier program version
// bound is not bound again.
pub fn bind_all() {
    let program = prog();
    program.bound_symbols.get_or_init(|| {
        let mut lineage = LINEAGE.lock().unwrap_or_else(PoisonError::into_inner);
        let symbols = lineage.get_or_insert_with(SymbolArena::new);
        let mark = symbols.mark();
        if single_threaded() {
            bind_files_last_queued_first(symbols);
        } else {
            bind_files_parallel(symbols);
        }
        for file in program.source_files() {
            // Go: program.go:450 traces the files that are not bound yet.
            let _trace = if file.file_bind.get().is_none() {
                trace_bind_source_file(file.root)
            } else {
                None
            };
            bind_source_file(file.root, symbols);
        }
        // Checkers clone the copy; share what this program added.
        symbols.share_since(mark);
        symbols.clone()
    });
}

/// Go program.go:445 with `--singleThreaded`: `core.singleThreadedWorkGroup`
/// runs the queued binds last-queued-first (core/workgroup.go:67), so the
/// files that are not bound yet bind, and trace, in reverse file order. Each
/// file binds into its own arena, and the arenas join the lineage arena in
/// file order, so the ids are those of a serial bind in file order (see
/// `bind_files_parallel`). This thread keeps the state that binding makes.
fn bind_files_last_queued_first(symbols: &mut SymbolArena) {
    let queued: Vec<Node> = prog()
        .source_files()
        .filter(|file| file.file_bind.get().is_none())
        .map(|file| file.root)
        .collect();
    let mut bound: Vec<(BoundFile, SymbolArena)> = queued
        .into_iter()
        .rev()
        .map(|file| {
            let _trace = trace_bind_source_file(file);
            let mut file_symbols = SymbolArena::new();
            let bound = bind_source_file_detached(file, &mut file_symbols);
            (bound, file_symbols)
        })
        .collect();
    bound.reverse();
    for (mut file, file_symbols) in bound {
        file.remap(symbols.append_file_arena(file_symbols));
        file.install();
    }
}

/// Go program.go:450: the "bindSourceFile" event of one file, when tracing.
/// PORT: a file whose parallel bind is dropped (see `bind_files_parallel`)
/// is bound again serially and gets a second event.
fn trace_bind_source_file(file: Node) -> Option<crate::tracing::Pop> {
    crate::tracing::get().map(|tr| {
        tr.push(
            crate::tracing::Phase::Bind,
            "bindSourceFile",
            vec![("path", source_file_info(file).path.clone().into())],
            true,
        )
    })
}

/// The state of this thread that binding must not change: synthetic nodes,
/// ids and lazy JSDoc. A bind thread starts from a copy of the loading
/// thread's state, so anything it adds would be lost.
fn bind_thread_fingerprint() -> (usize, (u64, u64), usize) {
    (
        synthetic_slot_count(),
        next_ids(),
        go_frontend::lazy_jsdoc_count(),
    )
}

/// Number of bind threads: `ThreadBudget::bind_threads` of the last
/// program load on this thread (`note_program_load`).
/// `GOPORT_BIND_THREADS` sets it (below 2 binds serially).
fn bind_thread_count() -> usize {
    if let Some(count) = std::env::var("GOPORT_BIND_THREADS")
        .ok()
        .and_then(|value| value.parse().ok())
    {
        return count;
    }
    ThreadBudget::current().bind_threads(LARGE_LOAD.get())
}

/// A program load with at least this many root tasks (root files, `lib`
/// entries and the automatic type directive task) is large.
// PERF (perf9 round 3, effect R3-E1): root tasks are query 27, hono 190,
// elysia 241, zod 324 and effect 459. At 16 threads, 7 parse workers
// parsed effect 12 ms and zod 9 ms faster than 4, and hono in the same
// time. Query gains nothing from more parse threads (lib.dom bounds its
// parse), and its peak RSS is near the 1.15x rule.
const LARGE_LOAD_ROOT_TASKS: usize = 128;

thread_local! {
    /// Whether the last program load on this thread was large
    /// (`note_program_load`). The bind of that program reads it.
    static LARGE_LOAD: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

/// Records whether a program load on this thread with `root_tasks` root
/// tasks is large, and returns it. A large load gets more parse threads
/// (`ThreadBudget::parse_threads`) and bind threads
/// (`ThreadBudget::bind_threads`). Call it when the load starts.
pub(crate) fn note_program_load(root_tasks: usize) -> bool {
    let large = root_tasks >= LARGE_LOAD_ROOT_TASKS;
    LARGE_LOAD.set(large);
    large
}

/// The cores that this process may run on, read once: each read asks the
/// kernel and the cgroup files, and a program load asks several times.
pub fn available_cores() -> usize {
    static CORES: OnceLock<usize> = OnceLock::new();
    *CORES.get_or_init(|| std::thread::available_parallelism().map_or(1, std::num::NonZero::get))
}

/// The most parse threads (the loading thread included) and bind threads
/// of a program load, and the glibc malloc arenas of the process, in one
/// budget. A large program load (`note_program_load`) has its own limits.
///
/// glibc gives each thread that mallocs its own arena until `arena_max`
/// arenas exist. A new thread first takes the arena of a thread that
/// ended, if there is one. When `arena_max` arenas exist, a later thread
/// shares the arena of another thread, and when both malloc at once they
/// wait on its lock. Each arena in use also adds peak RSS, because freed
/// per-file data stays in it. The parse mallocs most (a quarter of the
/// parse thread cycles), so the parse threads must fit the arenas: with 7
/// arenas at 16 cores, the 7 parse workers of effect made 3,763 futex waits
/// (19 at 4 cores). The bind threads malloc little (about 5% of their
/// cycles), so they can share arenas: 8 bind threads bind effect in the
/// same time with 7 arenas as with 16. In the check, the checkers and the
/// loading thread malloc. Main, and in `tsgo` the signal and text hash
/// threads, hold an arena too.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ThreadBudget {
    /// The most parse threads, the loading thread included.
    pub parse: usize,
    /// The most parse threads of a large program load.
    pub parse_large: usize,
    /// The most bind threads of a large program load.
    pub bind: usize,
    /// The most bind threads of other program loads.
    pub bind_small: usize,
    /// `glibc.malloc.arena_max`.
    pub arena_max: usize,
}

static THREAD_BUDGET: OnceLock<ThreadBudget> = OnceLock::new();

/// Go's default checker count (`checker_count`).
const DEFAULT_CHECKERS: usize = 4;

impl ThreadBudget {
    /// A process that loads several programs at once (`goport_build`: about
    /// 20 threads per program), and the counts of a process that installs
    /// no budget.
    pub const WIDE: ThreadBudget = ThreadBudget {
        parse: 8,
        parse_large: 8,
        bind: 8,
        bind_small: 8,
        arena_max: 16,
    };

    /// The budget of a one-program process (`tsgo`, `goport`) on the cores
    /// of this process. `arena_max` gives one arena to each thread alive
    /// while the checkers run (the checkers, main, the loading thread and
    /// `extra`; `tsgo` has 1 extra, its signal thread), and one to each
    /// parse worker that only a large load adds (the spare arenas).
    /// - A load that is not large parses on as many threads as the check (4
    ///   workers and the loading thread), which fit the check arenas.
    /// - A large load adds up to 3 parse workers, which use the spare
    ///   arenas, and binds on 8 threads.
    /// - With spare arenas, a load that is not large binds on as many
    ///   threads as it had parse workers. The bind threads then take the
    ///   arenas of the parse workers, which ended, and make no new ones.
    // PERF (perf9 round 2, env-only runs on cup2 and zbook): with 8 parse
    // threads at 8 and 16 cores, the parse threads shared arena locks. With
    // 5, the query parse on cup2 took 21 ms instead of 29 (wall 8% to 12%
    // less) and query peak RSS was 135 MB instead of 136 to 137 (Go 119).
    // 7 parse threads with 10 arenas were faster on effect, but query then
    // needs 143 MB, over the 1.15x RSS rule. 4 bind threads cost zod 13 ms
    // and effect 18 ms of bind.
    // PERF (perf9 round 3, effect R3-E1): so only a large program starts
    // more parse workers (7 workers with 12 arenas at 16 threads: effect
    // parse -12 ms, zod -9 ms; 9 or 11 workers gave no more). tsgo query
    // at 16 threads on zbook, env runs: `arena_max` 7 with 8 bind threads
    // (round 2) makes 7 arenas and 131 MB peak RSS; `arena_max` 10 with 8
    // bind threads makes 10 arenas and 135 MB, with 4 bind threads 7 arenas
    // and 129 MB (5 bind threads: 8 arenas). At 4 cores nothing changes:
    // the counts are the core count there, so there are no spare arenas.
    pub fn one_program(extra: usize) -> Self {
        let cores = available_cores();
        let parse = DEFAULT_CHECKERS + 1;
        let parse_large = parse + 3;
        let spare = cores.min(parse_large) - cores.min(parse);
        ThreadBudget {
            parse,
            parse_large,
            bind: 8,
            bind_small: if spare > 0 { parse - 1 } else { 8 },
            arena_max: DEFAULT_CHECKERS + 2 + extra + spare,
        }
    }

    /// Parse threads of a program load, the loading thread included: one
    /// per core, up to `parse_large` for a large load and `parse` for others.
    pub fn parse_threads(&self, large: bool) -> usize {
        available_cores().min(if large { self.parse_large } else { self.parse })
    }

    /// Bind threads of a program: one per core, up to `bind` for a large
    /// load and `bind_small` for others.
    pub fn bind_threads(&self, large: bool) -> usize {
        available_cores().min(if large { self.bind } else { self.bind_small })
    }

    /// Makes this the budget of the program loads of this process. The
    /// first install wins.
    pub fn install(self) {
        let _ = THREAD_BUDGET.set(self);
    }

    /// The installed budget, or `WIDE`.
    pub fn current() -> Self {
        THREAD_BUDGET.get().copied().unwrap_or(Self::WIDE)
    }

    /// The `GLIBC_TUNABLES` value of this budget (see `bin/goport.rs`
    /// `set_malloc_tunables`).
    pub fn glibc_tunables(&self) -> String {
        format!(
            "glibc.malloc.hugetlb=1:glibc.malloc.arena_max={}:glibc.malloc.top_pad=67108864",
            self.arena_max
        )
    }
}

/// One file bound on a bind thread, with its ids already moved to program
/// ids, or None when binding it made thread-local state or panicked.
type ParallelBind = (usize, Option<(BoundFile, PreparedFileArena)>);

/// The work queue of the bind threads (`bind_files_parallel`).
struct BindQueue {
    state: Mutex<BindQueueState>,
    /// Signals new known offsets, a finished bind and `stop`.
    changed: std::sync::Condvar,
}

struct BindQueueState {
    /// The next file to bind, as an index into the bind order.
    next: usize,
    /// The number of files being bound.
    binding: usize,
    /// Set by the loading thread when it stops at a failed file.
    stop: bool,
    /// The arena counts of each bound file, by file index.
    counts: Vec<Option<ArenaMark>>,
    /// The id offsets of file `i` at index `i`. They are known when every
    /// earlier file is bound: each file adds its counts to the offsets of the
    /// file before it.
    offsets: Vec<ArenaOffsets>,
    /// Bound files that wait for their offsets, by file index.
    waiting: std::collections::BTreeMap<usize, (BoundFile, SymbolArena)>,
}

impl BindQueue {
    fn new(file_count: usize, first: ArenaOffsets) -> Self {
        BindQueue {
            state: Mutex::new(BindQueueState {
                next: 0,
                binding: 0,
                stop: false,
                counts: vec![None; file_count],
                offsets: vec![first],
                waiting: std::collections::BTreeMap::new(),
            }),
            changed: std::sync::Condvar::new(),
        }
    }

    fn lock(&self) -> std::sync::MutexGuard<'_, BindQueueState> {
        self.state
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
    }

    /// Stops the bind threads.
    fn stop(&self) {
        self.lock().stop = true;
        self.changed.notify_all();
    }
}

impl BindQueueState {
    /// Records the arena counts of bound file `i`. Returns true when that
    /// made the offsets of more files known.
    fn record(&mut self, i: usize, counts: ArenaMark) -> bool {
        self.counts[i] = Some(counts);
        let known = self.offsets.len();
        while let Some(&Some(file_counts)) = self.counts.get(self.offsets.len() - 1) {
            let last = *self.offsets.last().expect("first offsets");
            self.offsets.push(last.after(file_counts));
        }
        self.offsets.len() > known
    }

    /// The waiting file with the lowest index, when its offsets are known.
    fn take_ready(&mut self) -> Option<(usize, BoundFile, SymbolArena, ArenaOffsets)> {
        let (&i, _) = self.waiting.first_key_value()?;
        let offsets = *self.offsets.get(i)?;
        let (_, (bound, file_symbols)) = self.waiting.pop_first()?;
        Some((i, bound, file_symbols, offsets))
    }
}

/// Binds the program files that are not bound yet on several threads, each
/// file into its own arena, and joins the arenas into `symbols` in file
/// order. It stops at the first file that made thread-local state while
/// binding (for example a lazy JSDoc parse) or panicked; `bind_all` binds
/// that file and the rest serially, which gives the same result as a serial
/// bind of every file.
// PERF: a file's ids move to their program values on a bind thread, as soon
// as every earlier file is bound, because its offsets are the sums of the
// earlier file counts. The threads stay while files wait for offsets, so
// when the last large file (lib.dom) is bound they move the waiting files in
// parallel. The loading thread only appends chunks, in file order. The ids
// are the ones that a join on the loading thread gives.
fn bind_files_parallel(symbols: &mut SymbolArena) {
    let files: Vec<Node> = prog()
        .source_files()
        .filter(|file| file.file_bind.get().is_none())
        .map(|file| file.root)
        .collect();
    let threads = bind_thread_count().min(files.len());
    if single_threaded() || threads < 2 {
        return;
    }
    let unported = unported_report();
    // PERF: the threads take the largest files first (by node count), so the
    // largest file (lib.dom) starts at once and the small files fill the other
    // threads while it binds. The join order stays the file order.
    let mut order: Vec<usize> = (0..files.len()).collect();
    order.sort_by_key(|&i| std::cmp::Reverse(files[i].go_file().parser_flags.len()));
    let queue = BindQueue::new(files.len(), symbols.next_file_offsets());
    let (sender, receiver) = std::sync::mpsc::channel::<ParallelBind>();
    let complete = std::thread::scope(|scope| {
        for _ in 0..threads {
            let seed = WorkerSeed::take();
            let (files, order, queue, sender) = (&files, &order, &queue, sender.clone());
            std::thread::Builder::new()
                .stack_size(CHECKER_STACK_SIZE)
                .spawn_scoped(scope, move || {
                    seed.install();
                    let mut state = queue.lock();
                    loop {
                        if state.stop {
                            break;
                        }
                        // Moving ids first: the loading thread waits for it.
                        if let Some((i, mut bound, file_symbols, offsets)) = state.take_ready() {
                            drop(state);
                            bound.remap(offsets);
                            let prepared = file_symbols.prepare_file_arena(offsets);
                            let _ = sender.send((i, Some((bound, prepared))));
                            state = queue.lock();
                            continue;
                        }
                        if let Some(&i) = order.get(state.next) {
                            let file = files[i];
                            state.next += 1;
                            state.binding += 1;
                            drop(state);
                            let before = bind_thread_fingerprint();
                            let result = std::panic::catch_unwind(|| {
                                let _trace = trace_bind_source_file(file);
                                let mut file_symbols = SymbolArena::new();
                                let bound = bind_source_file_detached(file, &mut file_symbols);
                                (bound, file_symbols)
                            })
                            .ok()
                            .filter(|_| bind_thread_fingerprint() == before);
                            state = queue.lock();
                            state.binding -= 1;
                            let Some((bound, file_symbols)) = result else {
                                drop(state);
                                // Later files never get offsets now; waiting
                                // threads check whether to stay.
                                queue.changed.notify_all();
                                let _ = sender.send((i, None));
                                break;
                            };
                            let more = state.record(i, file_symbols.mark());
                            state.waiting.insert(i, (bound, file_symbols));
                            if more || state.binding == 0 {
                                queue.changed.notify_all();
                            }
                            continue;
                        }
                        // Nothing to bind. Stay while a waiting file can
                        // still get its offsets from a bind in progress.
                        if state.waiting.is_empty() || state.binding == 0 {
                            break;
                        }
                        state = queue
                            .changed
                            .wait(state)
                            .unwrap_or_else(std::sync::PoisonError::into_inner);
                    }
                })
                .expect("cannot start a bind thread");
        }
        drop(sender);
        // Join the files in order as they arrive.
        let mut pending = FxHashMap::default();
        let mut joined = 0;
        for (i, result) in &receiver {
            pending.insert(i, result);
            while let Some(result) = pending.remove(&joined) {
                let Some((bound, prepared)) = result else {
                    queue.stop();
                    return false;
                };
                symbols.append_prepared_file_arena(prepared);
                bound.install();
                joined += 1;
            }
        }
        true
    });
    if !complete {
        // The serial bind counts the hits of the file that stopped here.
        restore_unported(&unported);
    }
}

// Go: parser/parser.go finishSourceFile (text part) and
// compiler/fileloader.go parseSourceFile / loadSourceFileMetaData.
// The metadata and the default library flag come back beside the info.
fn build_early_info(
    index: usize,
    source: &'static ts_compiler::SourceFile,
    parser_flags: &[NodeFlags],
    options: &CompilerOptions,
    cwd: &str,
    case_sensitivity: CaseSensitivity,
    fs: &ts_vfs::OsFileSystem,
) -> (SourceFileInfo, FileProgramMeta) {
    let file_name = source.file_name.clone();
    let path = ts_path::canonicalize(&file_name, cwd, case_sensitivity);
    let text = source.source_text.as_str();
    let file_node = Node::new(index, source.parse.source_file);

    // Go: parser/parser.go ensureScriptKind
    let script_kind = match ts_path::script_kind_from_path(&file_name) {
        ts_path::ScriptKind::Js => ScriptKind::JS,
        ts_path::ScriptKind::Jsx => ScriptKind::JSX,
        ts_path::ScriptKind::Ts => ScriptKind::TS,
        ts_path::ScriptKind::Tsx => ScriptKind::TSX,
        ts_path::ScriptKind::External => ScriptKind::EXTERNAL,
        ts_path::ScriptKind::Json => ScriptKind::JSON,
        ts_path::ScriptKind::Deferred => ScriptKind::DEFERRED,
        ts_path::ScriptKind::Unknown => ScriptKind::TS,
    };
    let language_variant = get_language_variant(script_kind);
    let is_declaration_file = ts_path::is_declaration_file(&file_name);

    let comment_directives = source
        .parse
        .comment_directives
        .iter()
        .map(|d| CommentDirective {
            loc: TextRange::new(d.range.start.get() as i32, d.range.end.get() as i32),
            kind: if d.expect_error {
                CommentDirectiveKind::EXPECT_ERROR
            } else {
                CommentDirectiveKind::IGNORE
            },
        })
        .collect();

    let mut diagnostics: Vec<Diagnostic> = source
        .parse
        .diagnostics
        .iter()
        .map(|d| {
            convert_text_diagnostic(
                file_node,
                d.range.start.get() as i32,
                d.range.end.get() as i32,
                d.code,
                convert_category(d.category),
                &d.message,
            )
        })
        .collect();

    let mut fields = PragmaFields::default();
    let pragmas = get_comment_pragmas(text);
    let mut pragma_diagnostics = Vec::new();
    process_pragmas_into_fields(file_node, &pragmas, &mut fields, &mut pragma_diagnostics);
    // PORT: the Rust parser may already report some pragma errors; add ours
    // only when no parse diagnostic has the same code and position.
    for d in pragma_diagnostics {
        if !diagnostics
            .iter()
            .any(|p| p.code == d.code && p.pos == d.pos)
        {
            diagnostics.push(d);
        }
    }

    let meta = FileProgramMeta {
        meta_data: load_source_file_meta_data(&file_name, options, fs),
        is_default_library: source.is_default_library,
    };
    let _ = parser_flags;

    let info = SourceFileInfo {
        file_name,
        path,
        is_declaration_file,
        language_variant,
        script_kind,
        pragmas,
        check_js_directive: fields.check_js_directive,
        referenced_files: fields.referenced_files,
        type_reference_directives: fields.type_reference_directives,
        lib_reference_directives: fields.lib_reference_directives,
        comment_directives,
        diagnostics: diagnostics.leak(),
        // PORT: the Rust parser does not report Go `JSDiagnostics` or
        // `JSDocDiagnostics` separately; they stay empty.
        js_diagnostics: &[],
        jsdoc_diagnostics: &[],
        has_lazy_js_doc: script_kind == ScriptKind::JS || script_kind == ScriptKind::JSX,
        // PORT: the legacy parser has no Go scanner flag. A string literal
        // with no escape or newline does not set the Go flag, so this can be
        // true where Go is false.
        contains_non_ascii: !text.is_ascii(),
        trivia: crate::ast::go_view::TriviaRuns::compute(&source.parse.arena, text),
        late: OnceLock::new(),
    };
    (info, meta)
}

// Go: parser/parser.go finishSourceFile (tree part) and
// parser/references.go collectExternalModuleReferences
fn build_late_info(index: usize, file: &'static GoFile) -> LateSourceFileInfo {
    let root = file.root;
    let info = &file.info;

    // Go: parser/parser.go finishSourceFile reparsedClones (sorted)
    // PORT: the Rust parser has no clone list; nodes with the REPARSED flag
    // stand in for Go's reparsed clones.
    let mut reparsed_clones: Vec<Node> = file
        .parser_flags
        .iter()
        .enumerate()
        .filter(|(_, flags)| flags.intersects(NodeFlags::REPARSED))
        .map(|(i, _)| Node::new(index, ts_ast::NodeId::new(i as u32)))
        .collect();
    reparsed_clones.sort_by(|a, b| compare_node_positions(*a, *b).cmp(&0));

    let missing = SourceFileMetaData::default();
    let meta_data = state()
        .file_meta
        .get(&index)
        .map_or(&missing, |meta| &meta.meta_data);
    let external_module_indicator =
        get_external_module_indicator(root, info, meta_data, &prog().options);

    let mut refs = ModuleReferences {
        imports: Vec::new(),
        module_augmentations: Vec::new(),
        ambient_module_names: Vec::new(),
        uses_uri_style_node_core_modules: Tristate::Unknown,
    };
    collect_external_module_references(root, info, external_module_indicator, &mut refs);

    LateSourceFileInfo {
        file_index: index,
        external_module_indicator,
        reparsed_clones: reparsed_clones.leak(),
        imports: refs.imports,
        module_augmentations: refs.module_augmentations,
        ambient_module_names: refs.ambient_module_names,
        uses_uri_style_node_core_modules: refs.uses_uri_style_node_core_modules,
        // PORT: JS files treat a cache miss as an unported lazy parse; TS
        // files get the eager Go entries.
        jsdoc_cache: if info.has_lazy_js_doc {
            &EMPTY_JSDOC_CACHE
        } else {
            &*Box::leak(Box::new(crate::ast::build_jsdoc_cache(root)))
        },
        post_bind: OnceLock::new(),
    }
}

// Go: parser/parser.go getLanguageVariant
fn get_language_variant(script_kind: ScriptKind) -> LanguageVariant {
    match script_kind {
        ScriptKind::TSX | ScriptKind::JSX | ScriptKind::JS | ScriptKind::JSON => {
            LanguageVariant::JSX
        }
        _ => LanguageVariant::STANDARD,
    }
}

fn convert_category(category: ts_core::DiagnosticCategory) -> ts_diagnostics::Category {
    match category {
        ts_core::DiagnosticCategory::Warning => ts_diagnostics::Category::Warning,
        ts_core::DiagnosticCategory::Error => ts_diagnostics::Category::Error,
        ts_core::DiagnosticCategory::Suggestion => ts_diagnostics::Category::Suggestion,
        ts_core::DiagnosticCategory::Message => ts_diagnostics::Category::Message,
    }
}

// PORT: Rust parser and program diagnostics carry the formatted text, not
// the message and args. When the catalog message for the code has exactly
// that text, use it. Otherwise make a message whose text is the formatted
// text (one `{0}` argument), so printing and comparison still work.
fn convert_text_diagnostic(
    file: Node,
    pos: i32,
    end: i32,
    code: Option<u32>,
    category: ts_diagnostics::Category,
    text: &str,
) -> Diagnostic {
    if let Some(message) = code.and_then(ts_diagnostics::message_by_code) {
        if message.text() == text {
            let mut d = new_diagnostic(file, TextRange::new(pos, end), message, Vec::new());
            d.category = category;
            return d;
        }
    }
    let code_value = code.unwrap_or(0);
    let message: &'static ts_diagnostics::Message = Box::leak(Box::new(
        ts_diagnostics::Message::new(code_value, category, "", "{0}", false, false, false),
    ));
    new_diagnostic(
        file,
        TextRange::new(pos, end),
        message,
        vec![text.to_string()],
    )
}

// Splits `ts_compiler` program diagnostics into Go config-file diagnostics and
// Go program diagnostics.
// PORT: Go builds these from the tsconfig parse and `verifyCompilerOptions`.
// The Rust graph loader reports one list. Diagnostics located in the config
// file become config diagnostics; the rest become program diagnostics.
// Records the checker or parser reports itself are dropped: parse errors
// already in a file's parse diagnostics, unresolved-import codes 2307 and
// 2882 (the checker reports them) and emit-overwrite codes 5055 and 5056
// (Go only reports them when emitting).
#[allow(clippy::too_many_arguments)]
fn convert_program_diagnostics(
    compiler_program: &'static ts_compiler::Program,
    files: &[GoFile],
    file_by_path: &FxHashMap<String, usize>,
    options: &CompilerOptions,
    cwd: &str,
    case_sensitivity: CaseSensitivity,
    config_diagnostics: &mut Vec<Diagnostic>,
    program_diagnostics: &mut Vec<Diagnostic>,
    external_locations: &mut Vec<ExternalLocation>,
) {
    const DROPPED_CODES: [u32; 4] = [2307, 2882, 5055, 5056];
    let config_path = ts_path::canonicalize(&options.config_file_path, cwd, case_sensitivity);
    for record in compiler_program.diagnostics() {
        if record
            .code
            .is_some_and(|code| DROPPED_CODES.contains(&code))
        {
            continue;
        }
        let path = record
            .file_name
            .as_deref()
            .map(|name| ts_path::canonicalize(name, cwd, case_sensitivity));
        if let (Some(path), Some(range)) = (&path, record.range) {
            if let Some(&index) = file_by_path.get(path) {
                let pos = range.start.get() as i32;
                let code = record.code.map_or(0, |c| c as i32);
                if files[index]
                    .info
                    .diagnostics
                    .iter()
                    .any(|d| d.pos == pos && d.code == code)
                {
                    continue;
                }
            }
        }
        let diagnostic = convert_program_diagnostic(
            compiler_program,
            record,
            files,
            file_by_path,
            cwd,
            case_sensitivity,
            external_locations,
        );
        if path.as_deref() == Some(config_path.as_str()) {
            config_diagnostics.push(diagnostic);
        } else {
            program_diagnostics.push(diagnostic);
        }
    }
}

fn convert_program_diagnostic(
    compiler_program: &'static ts_compiler::Program,
    record: &ts_compiler::ProgramDiagnostic,
    files: &[GoFile],
    file_by_path: &FxHashMap<String, usize>,
    cwd: &str,
    case_sensitivity: CaseSensitivity,
    external_locations: &mut Vec<ExternalLocation>,
) -> Diagnostic {
    let (pos, end) = record
        .range
        .map_or((0, 0), |r| (r.start.get() as i32, r.end.get() as i32));
    let mut file = Node::NIL;
    let mut external_name = None;
    if let Some(name) = &record.file_name {
        let path = ts_path::canonicalize(name, cwd, case_sensitivity);
        if let Some(&index) = file_by_path.get(&path) {
            file = files[index].root;
        }
        if file.is_nil() && record.range.is_some() {
            external_name = Some(name.clone());
        }
    }
    let mut diagnostic = convert_text_diagnostic(
        file,
        pos,
        end,
        record.code,
        record.category,
        &record.message,
    );
    if let Some(name) = external_name {
        let text = compiler_program.diagnostic_source_text(&name).unwrap_or("");
        let starts = compute_ecma_line_starts(text);
        let clamped = (pos.max(0) as usize).min(text.len());
        let line = compute_line_of_position(&starts, clamped as i32);
        let line_start = starts[line as usize] as usize;
        let character = text.get(line_start..clamped).map_or(0, utf16_len);
        external_locations.push(ExternalLocation {
            code: diagnostic.code,
            pos,
            end,
            args: diagnostic.message_args.clone(),
            file_name: name,
            line,
            character,
        });
    }
    let related = record
        .related_information
        .iter()
        .map(|r| {
            convert_program_diagnostic(
                compiler_program,
                r,
                files,
                file_by_path,
                cwd,
                case_sensitivity,
                external_locations,
            )
        })
        .collect();
    diagnostic.set_related_info(related);
    diagnostic
}

// ---------------------------------------------------------------------------
// Pragmas (Go parser/parser.go)
// ---------------------------------------------------------------------------

#[derive(Default)]
struct PragmaFields {
    check_js_directive: Option<CheckJsDirective>,
    referenced_files: Vec<FileReference>,
    type_reference_directives: Vec<FileReference>,
    lib_reference_directives: Vec<FileReference>,
}

// Go: scanner/scanner.go GetLeadingCommentRanges (pos 0)
// Returns (pos, end, kind) for each leading comment of the file.
fn get_leading_comment_ranges_at_start(text: &str) -> Vec<(i32, i32, SyntaxKind)> {
    let bytes = text.as_bytes();
    let mut ranges = Vec::new();
    let mut pos = get_shebang(text).len();
    // PORT: Go iterates runes; ASCII cases are matched on bytes.
    while pos < bytes.len() {
        let ch = bytes[pos];
        match ch {
            b'\r' | b'\n' | b'\t' | 0x0b | 0x0c | b' ' => {
                pos += 1;
            }
            b'/' => {
                let next = bytes.get(pos + 1).copied();
                if next != Some(b'/') && next != Some(b'*') {
                    break;
                }
                let start = pos;
                pos += 2;
                let kind = if next == Some(b'/') {
                    while pos < bytes.len() {
                        let c = text[pos..].chars().next().unwrap_or('\0');
                        if is_line_break(c) {
                            break;
                        }
                        pos += c.len_utf8();
                    }
                    SyntaxKind::SingleLineCommentTrivia
                } else {
                    while pos < bytes.len() {
                        if bytes[pos] == b'*' && bytes.get(pos + 1) == Some(&b'/') {
                            pos += 2;
                            break;
                        }
                        pos += 1;
                    }
                    SyntaxKind::MultiLineCommentTrivia
                };
                ranges.push((start as i32, pos as i32, kind));
            }
            _ => {
                let c = text[pos..].chars().next().unwrap_or('\0');
                if (c as u32) > 0x7f && is_white_space_like(c) {
                    pos += c.len_utf8();
                } else {
                    break;
                }
            }
        }
    }
    ranges
}

// Go: parser/parser.go:6427 getCommentPragmas
fn get_comment_pragmas(source_text: &str) -> Vec<Pragma> {
    let mut pragmas = Vec::new();
    for (pos, end, kind) in get_leading_comment_ranges_at_start(source_text) {
        let comment = &source_text[pos as usize..end as usize];
        pragmas.extend(extract_pragmas(TextRange::new(pos, end), kind, comment));
    }
    pragmas
}

// Go: parser/parser.go:6435 extractPragmas
fn extract_pragmas(comment_range: TextRange, kind: SyntaxKind, text: &str) -> Vec<Pragma> {
    if kind == SyntaxKind::SingleLineCommentTrivia {
        let mut pos = 2;
        let triple_slash = pragma_match(text, pos, "/");
        if triple_slash {
            pos += 1;
        }
        pos = skip_blanks(text, pos);
        if triple_slash && pragma_match(text, pos, "<") {
            let tag_name = extract_name(text, pos + 1);
            if tag_name != "reference" {
                return Vec::new();
            }
            pos += 10;
            let mut args = IndexMap::new();
            loop {
                pos = skip_blanks(text, pos);
                if pragma_match(text, pos, "/>") {
                    break;
                }
                let arg_name = extract_name(text, pos);
                if arg_name.is_empty() {
                    break;
                }
                pos = skip_blanks(text, pos + arg_name.len());
                if !pragma_match(text, pos, "=") {
                    break;
                }
                pos = skip_blanks(text, pos + 1);
                let Some(value) = extract_quoted_string(text, pos) else {
                    break;
                };
                let start = comment_range.pos() + pos as i32 + 1;
                args.insert(
                    arg_name.clone(),
                    PragmaArgument {
                        name: arg_name,
                        value: value.to_string(),
                        range: TextRange::new(start, start + value.len() as i32),
                    },
                );
                pos += value.len() + 2;
            }
            return vec![Pragma {
                name: "reference".to_string(),
                args,
                range: comment_range,
                kind,
            }];
        }
        if pragma_match(text, pos, "@") {
            pos += 1;
            let pragma_name = extract_name(text, pos);
            if !(pragma_name == "ts-check" || pragma_name == "ts-nocheck") {
                return Vec::new();
            }
            return vec![Pragma {
                name: pragma_name,
                args: IndexMap::new(),
                range: comment_range,
                kind,
            }];
        }
    }
    if kind == SyntaxKind::MultiLineCommentTrivia {
        let text = text.strip_suffix("*/").unwrap_or(text);
        let mut pos = 2;
        let mut pragmas = Vec::new();
        loop {
            let Some(at) = skip_to(text, pos, "@") else {
                break;
            };
            pos = at;
            let name_pos = pos + 1;
            let name_end = skip_non_blanks(text, name_pos);
            if name_end == name_pos {
                pos += 1;
                continue;
            }
            let line_end = line_end_pos(text, pos);
            let pragma_name = text[name_pos..name_end].to_lowercase();
            if matches!(
                pragma_name.as_str(),
                "jsx" | "jsxfrag" | "jsximportsource" | "jsxruntime"
            ) {
                let start = skip_blanks(text, name_end);
                let arg_end = skip_non_blanks(text, start);
                if arg_end != start {
                    let mut args = IndexMap::new();
                    args.insert(
                        "factory".to_string(),
                        PragmaArgument {
                            name: "factory".to_string(),
                            value: text[start..arg_end].to_string(),
                            range: TextRange::new(
                                comment_range.pos() + start as i32,
                                comment_range.pos() + arg_end as i32,
                            ),
                        },
                    );
                    pragmas.push(Pragma {
                        name: pragma_name,
                        args,
                        range: comment_range,
                        kind,
                    });
                }
            }
            pos = line_end;
        }
        return pragmas;
    }
    Vec::new()
}

// Go: parser/parser.go match
fn pragma_match(text: &str, pos: usize, s: &str) -> bool {
    text.as_bytes()
        .get(pos..)
        .is_some_and(|rest| rest.starts_with(s.as_bytes()))
}

// Go: parser/parser.go skipBlanks
fn skip_blanks(text: &str, mut pos: usize) -> usize {
    let bytes = text.as_bytes();
    while pos < bytes.len() && (bytes[pos] == b' ' || bytes[pos] == b'\t') {
        pos += 1;
    }
    pos
}

// Go: parser/parser.go skipNonBlanks
fn skip_non_blanks(text: &str, mut pos: usize) -> usize {
    let bytes = text.as_bytes();
    while pos < bytes.len() && !matches!(bytes[pos], b' ' | b'\t' | b'\r' | b'\n') {
        pos += 1;
    }
    pos
}

// Go: parser/parser.go skipTo
fn skip_to(text: &str, pos: usize, s: &str) -> Option<usize> {
    if pos >= text.len() {
        return None;
    }
    let bytes = text.as_bytes();
    let needle = s.as_bytes();
    bytes[pos..]
        .windows(needle.len())
        .position(|w| w == needle)
        .map(|i| pos + i)
}

// Go: parser/parser.go lineEndPos
fn line_end_pos(text: &str, mut pos: usize) -> usize {
    while pos < text.len() {
        // PORT: Go decodes a rune at a byte offset; a non-boundary offset
        // decodes as a one-byte error rune.
        let Some(ch) = text.get(pos..).and_then(|rest| rest.chars().next()) else {
            pos += 1;
            continue;
        };
        if is_line_break(ch) {
            return pos;
        }
        pos += ch.len_utf8();
    }
    text.len()
}

// Go: parser/parser.go extractName
fn extract_name(text: &str, pos: usize) -> String {
    let bytes = text.as_bytes();
    let start = pos.min(bytes.len());
    let mut end = start;
    while end < bytes.len() && (bytes[end].is_ascii_alphabetic() || bytes[end] == b'-') {
        end += 1;
    }
    text[start..end].to_lowercase()
}

// Go: parser/parser.go extractQuotedString
fn extract_quoted_string(text: &str, pos: usize) -> Option<&str> {
    let bytes = text.as_bytes();
    if pos >= bytes.len() {
        return None;
    }
    let quote = bytes[pos];
    if quote != b'\'' && quote != b'"' {
        return None;
    }
    let start = pos + 1;
    let mut end = start;
    while end < bytes.len() && bytes[end] != quote {
        end += 1;
    }
    if end >= bytes.len() {
        return None;
    }
    Some(&text[start..end])
}

// Go: parser/parser.go processPragmasIntoFields
fn process_pragmas_into_fields(
    file: Node,
    pragmas: &[Pragma],
    fields: &mut PragmaFields,
    diagnostics: &mut Vec<Diagnostic>,
) {
    for pragma in pragmas {
        match pragma.name.as_str() {
            "reference" => {
                let types = pragma.args.get("types");
                let lib = pragma.args.get("lib");
                let path = pragma.args.get("path");
                let resolution_mode = pragma.args.get("resolution-mode");
                let preserve = pragma
                    .args
                    .get("preserve")
                    .is_some_and(|p| p.value == "true");
                let no_default_lib = pragma.args.get("no-default-lib");
                if no_default_lib.is_some_and(|n| n.value == "true") {
                    // Ignored.
                } else if let Some(types) = types {
                    let parsed = resolution_mode.map_or(RESOLUTION_MODE_NONE, |mode| {
                        parse_resolution_mode(file, &mode.value, mode.range, diagnostics)
                    });
                    fields.type_reference_directives.push(FileReference {
                        range: types.range,
                        file_name: types.value.clone(),
                        resolution_mode: parsed,
                        preserve,
                    });
                } else if let Some(lib) = lib {
                    fields.lib_reference_directives.push(FileReference {
                        range: lib.range,
                        file_name: lib.value.clone(),
                        resolution_mode: RESOLUTION_MODE_NONE,
                        preserve,
                    });
                } else if let Some(path) = path {
                    fields.referenced_files.push(FileReference {
                        range: path.range,
                        file_name: path.value.clone(),
                        resolution_mode: RESOLUTION_MODE_NONE,
                        preserve,
                    });
                } else {
                    diagnostics.push(new_diagnostic(
                        file,
                        pragma.range,
                        diag::Invalid_reference_directive_syntax,
                        Vec::new(),
                    ));
                }
            }
            "ts-check" | "ts-nocheck" => {
                // _last_ of either nocheck or check in a file is the "winner"
                if fields
                    .check_js_directive
                    .is_none_or(|d| pragma.range.pos() > d.range.pos())
                {
                    fields.check_js_directive = Some(CheckJsDirective {
                        enabled: pragma.name == "ts-check",
                        range: pragma.range,
                    });
                }
            }
            "jsx" | "jsxfrag" | "jsximportsource" | "jsxruntime" => {
                // Nothing to do here
            }
            other => panic!("Unhandled pragma kind: {other}"),
        }
    }
}

// Go: parser/parser.go parseResolutionMode
fn parse_resolution_mode(
    file: Node,
    mode: &str,
    range: TextRange,
    diagnostics: &mut Vec<Diagnostic>,
) -> ResolutionMode {
    if mode == "import" {
        return ModuleKind::ES_NEXT;
    }
    if mode == "require" {
        return ModuleKind::COMMON_JS;
    }
    diagnostics.push(new_diagnostic(
        file,
        range,
        diag::X_resolution_mode_should_be_either_require_or_import,
        Vec::new(),
    ));
    RESOLUTION_MODE_NONE
}

// ---------------------------------------------------------------------------
// External module indicator (Go ast/parseoptions.go)
// ---------------------------------------------------------------------------

// Go: ast/parseoptions.go:60 getExternalModuleIndicator
// PORT: Go computes `ExternalModuleIndicatorOptions` first
// (GetExternalModuleIndicatorOptions); it is inlined here as `jsx`/`force`.
// `meta_data` is the file metadata from `ProgramState::file_meta`.
fn get_external_module_indicator(
    file: Node,
    info: &SourceFileInfo,
    meta_data: &SourceFileMetaData,
    options: &CompilerOptions,
) -> Node {
    if info.script_kind == ScriptKind::JSON {
        return Node::NIL;
    }
    let node = is_file_probably_external_module(file);
    if node.is_some() {
        return node;
    }
    if info.is_declaration_file {
        return Node::NIL;
    }
    let (jsx, force) = get_external_module_indicator_options(&info.file_name, options, meta_data);
    if jsx {
        let node = walk_tree_for_jsx_tags(file);
        if node.is_some() {
            return node;
        }
    }
    if force {
        return file;
    }
    Node::NIL
}

// Go: ast/parseoptions.go:19 GetExternalModuleIndicatorOptions
// Returns (JSX, Force).
fn get_external_module_indicator_options(
    file_name: &str,
    options: &CompilerOptions,
    metadata: &SourceFileMetaData,
) -> (bool, bool) {
    if ts_path::is_declaration_file(file_name) {
        return (false, false);
    }
    let kind = options.get_emit_module_detection_kind();
    if kind == ModuleDetectionKind::FORCE {
        (false, true)
    } else if kind == ModuleDetectionKind::AUTO {
        (
            options.jsx == JsxEmit::REACT_JSX || options.jsx == JsxEmit::REACT_JSX_DEV,
            is_file_forced_to_be_module_by_format(file_name, options, metadata),
        )
    } else {
        (false, false)
    }
}

// Go: ast/parseoptions.go:46 isFileForcedToBeModuleByFormat
fn is_file_forced_to_be_module_by_format(
    file_name: &str,
    options: &CompilerOptions,
    metadata: &SourceFileMetaData,
) -> bool {
    get_implied_node_format_for_emit_worker(file_name, options.get_emit_module_kind(), metadata)
        == ModuleKind::ES_NEXT
        || file_extension_is_one_of(file_name, &[".cjs", ".cts", ".mjs", ".mts"])
}

// Go: tspath FileExtensionIsOneOf
fn file_extension_is_one_of(path: &str, extensions: &[&str]) -> bool {
    extensions.iter().any(|ext| path.ends_with(ext))
}

// Go: ast/parseoptions.go:86 isFileProbablyExternalModule
fn is_file_probably_external_module(file: Node) -> Node {
    for statement in file.statements().iter() {
        if is_an_external_module_indicator_node(statement) {
            return statement;
        }
    }
    get_import_meta_if_necessary(file)
}

// Go: ast/parseoptions.go:95 isAnExternalModuleIndicatorNode
fn is_an_external_module_indicator_node(node: Node) -> bool {
    has_syntactic_modifier(node, ModifierFlags::EXPORT)
        || is_import_equals_declaration(node)
            && is_external_module_reference(node.module_reference())
        || is_import_declaration(node)
        || is_export_assignment(node)
        || is_export_declaration(node)
}

// Go: ast/parseoptions.go:101 getImportMetaIfNecessary
fn get_import_meta_if_necessary(file: Node) -> Node {
    if file
        .flags()
        .intersects(NodeFlags::POSSIBLY_CONTAINS_IMPORT_META)
    {
        return find_child_node(file, is_import_meta);
    }
    Node::NIL
}

// Go: ast/parseoptions.go:108 findChildNode
fn find_child_node(root: Node, check: fn(Node) -> bool) -> Node {
    fn visit(node: Node, check: fn(Node) -> bool, result: &mut Node) -> bool {
        if check(node) {
            *result = node;
            return true;
        }
        node.for_each_child(|child| visit(child, check, result))
    }
    let mut result = Node::NIL;
    visit(root, check, &mut result);
    result
}

// Go: ast/parseoptions.go:129 walkTreeForJSXTags
fn walk_tree_for_jsx_tags(node: Node) -> Node {
    fn visitor(node: Node, found: &mut Node) -> bool {
        if found.is_some() {
            return true;
        }
        if !node
            .subtree_facts()
            .intersects(SubtreeFacts::SUBTREE_CONTAINS_JSX)
        {
            return false;
        }
        if is_jsx_opening_like_element(node) || is_jsx_fragment(node) {
            *found = node;
            return true;
        }
        node.for_each_child(|child| visitor(child, found))
    }
    let mut found = Node::NIL;
    visitor(node, &mut found);
    found
}

// ---------------------------------------------------------------------------
// Module references (Go parser/references.go)
// ---------------------------------------------------------------------------

struct ModuleReferences {
    imports: Vec<Node>,
    module_augmentations: Vec<Node>,
    ambient_module_names: Vec<String>,
    uses_uri_style_node_core_modules: Tristate,
}

// Go: core/nodemodules.go UnprefixedNodeCoreModules
const UNPREFIXED_NODE_CORE_MODULES: [&str; 54] = [
    "assert",
    "assert/strict",
    "async_hooks",
    "buffer",
    "child_process",
    "cluster",
    "console",
    "constants",
    "crypto",
    "dgram",
    "diagnostics_channel",
    "dns",
    "dns/promises",
    "domain",
    "events",
    "fs",
    "fs/promises",
    "http",
    "http2",
    "https",
    "inspector",
    "inspector/promises",
    "module",
    "net",
    "os",
    "path",
    "path/posix",
    "path/win32",
    "perf_hooks",
    "process",
    "punycode",
    "querystring",
    "readline",
    "readline/promises",
    "repl",
    "stream",
    "stream/consumers",
    "stream/promises",
    "stream/web",
    "string_decoder",
    "sys",
    "timers",
    "timers/promises",
    "tls",
    "trace_events",
    "tty",
    "url",
    "util",
    "util/types",
    "v8",
    "vm",
    "wasi",
    "worker_threads",
    "zlib",
];

// Go: core/nodemodules.go ExclusivelyPrefixedNodeCoreModules
const EXCLUSIVELY_PREFIXED_NODE_CORE_MODULES: [&str; 5] = [
    "node:quic",
    "node:sea",
    "node:sqlite",
    "node:test",
    "node:test/reporters",
];

// Go: tspath IsExternalModuleNameRelative
fn is_external_module_name_relative(module_name: &str) -> bool {
    path_is_relative(module_name) || ts_path::is_rooted_disk_path(module_name)
}

// Go: tspath PathIsRelative
fn path_is_relative(path: &str) -> bool {
    path == "."
        || path == ".."
        || ["./", "../", ".\\", "..\\"]
            .iter()
            .any(|prefix| path.starts_with(prefix))
}

// Go: parser/references.go:11 collectExternalModuleReferences
// PORT: `is_external` is the file's own indicator result; Go reads
// `ast.IsExternalModule(file)`, which is not readable until install ends.
fn collect_external_module_references(
    file: Node,
    info: &SourceFileInfo,
    indicator: Node,
    refs: &mut ModuleReferences,
) {
    let is_external = indicator.is_some();
    for node in file.statements().iter() {
        collect_module_references(info, node, false, is_external, refs);
    }
    if file
        .flags()
        .intersects(NodeFlags::POSSIBLY_CONTAINS_DYNAMIC_IMPORT)
        || is_in_js_file(file)
    {
        for_each_dynamic_import_or_require_call(
            file,
            true,
            true,
            &mut |_node, module_specifier| {
                refs.imports.push(module_specifier);
                false
            },
        );
    }
}

// Go: parser/references.go:24 collectModuleReferences
fn collect_module_references(
    info: &SourceFileInfo,
    node: Node,
    in_ambient_module: bool,
    is_external: bool,
    refs: &mut ModuleReferences,
) {
    if is_any_import_or_re_export(node) {
        let module_name_expr = get_external_module_name(node);
        // TypeScript 1.0 spec (April 2014): 12.1.6
        // An ExternalImportDeclaration in an AmbientExternalModuleDeclaration may reference other external modules
        // only through top - level external module names. Relative external module names are not permitted.
        if module_name_expr.is_some() && is_string_literal(module_name_expr) {
            let module_name = module_name_expr.text();
            if !module_name.is_empty()
                && (!in_ambient_module || !is_external_module_name_relative(module_name))
            {
                refs.imports.push(module_name_expr);
                if refs.uses_uri_style_node_core_modules != Tristate::True
                    && !info.is_declaration_file
                {
                    if module_name.starts_with("node:")
                        && !EXCLUSIVELY_PREFIXED_NODE_CORE_MODULES.contains(&module_name)
                    {
                        // Presence of `node:` prefix takes precedence over unprefixed node core modules
                        refs.uses_uri_style_node_core_modules = Tristate::True;
                    } else if refs.uses_uri_style_node_core_modules == Tristate::Unknown
                        && UNPREFIXED_NODE_CORE_MODULES.contains(&module_name)
                    {
                        refs.uses_uri_style_node_core_modules = Tristate::False;
                    }
                }
            }
        }
        return;
    }
    if is_module_declaration(node)
        && is_ambient_module(node)
        && (in_ambient_module
            || has_syntactic_modifier(node, ModifierFlags::AMBIENT)
            || info.is_declaration_file)
    {
        let name_text = node.name().text();
        // Ambient module declarations can be interpreted as augmentations for some existing external modules.
        // This will happen in two cases:
        // - if current file is external module then module augmentation is a ambient module declaration defined in the top level scope
        // - if current file is not external module then module augmentation is an ambient module declaration with non-relative module name
        //   immediately nested in top level ambient module declaration .
        if is_external || (in_ambient_module && !is_external_module_name_relative(name_text)) {
            refs.module_augmentations.push(node.name());
        } else if !in_ambient_module {
            refs.ambient_module_names.push(name_text.to_string());
            // NOTE: body of ambient module is always a module block, if it exists
            let body = node.body();
            if body.is_some() {
                for statement in body.statements().iter() {
                    collect_module_references(info, statement, true, is_external, refs);
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Source file metadata (Go compiler/fileloader.go)
// ---------------------------------------------------------------------------

// Go: compiler/fileloader.go:341 loadSourceFileMetaData
// PORT: Go asks the module resolver for the package scope (cached
// package.json lookups). This walks up from the file's directory to the
// nearest package.json and reads its "type" field.
fn load_source_file_meta_data(
    file_name: &str,
    options: &CompilerOptions,
    fs: &ts_vfs::OsFileSystem,
) -> SourceFileMetaData {
    let module_resolution_kind = options.get_module_resolution_kind();
    let mut package_json_type = String::new();
    let mut package_json_directory = String::new();
    let mut directory = ts_path::directory_path(file_name);
    loop {
        let candidate = ts_path::combine_paths(&directory, &["package.json"]);
        if fs.file_exists(&candidate) {
            package_json_directory = directory.clone();
            let package_type = fs
                .read_file(&candidate)
                .ok()
                .and_then(|text| ts_module::parse_package_json(&text).ok())
                .and_then(|package| package.package_type);
            if let Some(value) = package_type {
                if !file_extension_is_one_of(file_name, &[".mts", ".cts", ".mjs", ".cjs"])
                    && ModuleResolutionKind::NODE16 <= module_resolution_kind
                    && module_resolution_kind <= ModuleResolutionKind::NODE_NEXT
                    || file_name.contains("/node_modules/")
                {
                    package_json_type = value;
                }
            }
            break;
        }
        let parent = ts_path::directory_path(&directory);
        if parent == directory || parent.is_empty() {
            break;
        }
        directory = parent;
    }
    let implied_node_format = get_implied_node_format_for_file(file_name, &package_json_type);
    SourceFileMetaData {
        package_json_type,
        package_json_directory,
        implied_node_format,
    }
}

// ---------------------------------------------------------------------------
// Resolution modes (Go compiler/fileloader.go)
// ---------------------------------------------------------------------------

// Go: compiler/fileloader.go:718 getDefaultResolutionModeForFile
fn get_default_resolution_mode_for_file_worker(
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

// Go: compiler/fileloader.go:726 getModeForUsageLocation
fn get_mode_for_usage_location_worker(
    file_name: &str,
    meta: &SourceFileMetaData,
    usage: Node,
    options: &CompilerOptions,
) -> ResolutionMode {
    let parent = usage.parent();
    if is_import_declaration(parent)
        || parent.kind() == SyntaxKind::JsImportDeclaration
        || is_export_declaration(parent)
        || parent.kind() == SyntaxKind::JsDocImportTag
    {
        let is_type_only = is_exclusively_type_only_import_or_export(parent);
        if is_type_only {
            let (override_, ok) = parent.attributes().get_resolution_mode_override();
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
    if import_syntax_affects_module_resolution(options) {
        return get_emit_syntax_for_usage_location_worker(file_name, meta, usage, options);
    }
    RESOLUTION_MODE_NONE
}

// Go: compiler/fileloader.go:758 importSyntaxAffectsModuleResolution
fn import_syntax_affects_module_resolution(options: &CompilerOptions) -> bool {
    let module_resolution = options.get_module_resolution_kind();
    ModuleResolutionKind::NODE16 <= module_resolution
        && module_resolution <= ModuleResolutionKind::NODE_NEXT
        || options.get_resolve_package_json_exports()
        || options.get_resolve_package_json_imports()
}

// Go: compiler/fileloader.go:764 getEmitSyntaxForUsageLocationWorker
fn get_emit_syntax_for_usage_location_worker(
    file_name: &str,
    meta: &SourceFileMetaData,
    usage: Node,
    options: &CompilerOptions,
) -> ResolutionMode {
    let parent = usage.parent();
    if is_require_call(parent, false)
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
    }
    if file_emit_mode.is_non_node_esm() || file_emit_mode == ModuleKind::PRESERVE {
        return ModuleKind::ES_NEXT;
    }
    ModuleKind::NONE
}

// ---------------------------------------------------------------------------
// Program methods (Go compiler/program.go). The program is the current
// `prog()`; these are free functions.
// PORT: Go `projectReferenceFileMapper.getCompilerOptionsForFile` returns the
// program options when there are no project references, which is always the
// case here.
// ---------------------------------------------------------------------------

fn file_info_by_path(path: &str) -> Option<&'static SourceFileInfo> {
    state()
        .file_by_path
        .get(path)
        .map(|&index| &crate::ast::go_file(index).info)
}

/// The program-set fields of the file at `path`, or None when `path` is not
/// a program file.
fn file_meta_by_path(path: &str) -> Option<&'static FileProgramMeta> {
    let state = state();
    state
        .file_by_path
        .get(path)
        .and_then(|index| state.file_meta.get(index))
}

/// Lazy JSDoc of `node` in `file` on the Go frontend path (Go
/// `SourceFile.resolveJSDoc`). None on the legacy path, where lazy JSDoc
/// parsing is not ported.
// PORT: the files of an alias resolver program are in no program, or in
// another program version; `go_frontend` keeps their parser inputs.
pub fn resolve_lazy_js_doc(file: Node, node: Node) -> Option<&'static [Node]> {
    let state = state();
    if state.alias_resolver {
        return go_frontend::resolve_js_doc_outside_program(file, node);
    }
    state.go.as_ref().map(|go| go.resolve_js_doc(file, node))
}

// Go: compiler/program.go:122 FileExists
// Go: ls/autoimport/aliasresolver.go:158 FileExists (unimplemented)
pub fn file_exists(path: &str) -> bool {
    alias_resolver_unimplemented();
    if let Some(go) = &state().go {
        return go.file_exists(path);
    }
    state().fs.file_exists(path)
}

// Go: compiler/program.go:127 GetCurrentDirectory
pub fn get_current_directory() -> &'static str {
    &state().cwd
}

// Go: compiler/program.go:215 UseCaseSensitiveFileNames
pub fn use_case_sensitive_file_names() -> bool {
    state().case_sensitivity == CaseSensitivity::Sensitive
}

// Go: compiler/program.go:219 UsesUriStyleNodeCoreModules
// Go never assigns the program field (only UpdateProgram copies it), so the
// value is always unknown.
pub fn uses_uri_style_node_core_modules() -> Tristate {
    Tristate::Unknown
}

// Go: compiler/program.go:173 GetProjectReferenceFromSource
// PORT: the Go frontend program has the port. The legacy loader does not
// load project references, so there is never a reference.
pub fn get_project_reference_from_source(
    path: &str,
) -> Option<&'static SourceOutputAndProjectReference> {
    // Go: ls/autoimport/aliasresolver.go:193 (unimplemented)
    alias_resolver_unimplemented();
    state().go.as_ref()?.get_project_reference_from_source(path)
}

// Go: compiler/program.go:178 IsSourceFromProjectReference
pub fn is_source_from_project_reference(path: &str) -> bool {
    // Go: ls/autoimport/aliasresolver.go:223 (unimplemented)
    alias_resolver_unimplemented();
    state()
        .go
        .as_ref()
        .is_some_and(|go| go.is_source_from_project_reference(path))
}

// Go: compiler/program.go:182 GetProjectReferenceFromOutputDts
// PORT: see `get_project_reference_from_source`.
pub fn get_project_reference_from_output_dts(
    path: &str,
) -> Option<&'static SourceOutputAndProjectReference> {
    // Go: ls/autoimport/aliasresolver.go:188 (unimplemented)
    alias_resolver_unimplemented();
    state()
        .go
        .as_ref()?
        .get_project_reference_from_output_dts(path)
}

// Go: compiler/program.go:190 GetRedirectForResolution
// PORT: see `get_project_reference_from_source`.
pub fn get_redirect_for_resolution(file: Node) -> Option<&'static ResolvedProjectReference> {
    // Go: ls/autoimport/aliasresolver.go:198 (unimplemented)
    alias_resolver_unimplemented();
    state().go.as_ref()?.get_redirect_for_resolution(file)
}

// Go: compiler/projectreferencefilemapper.go:76 getCompilerOptionsForFile
// Go: module/resolver.go:145 GetCompilerOptionsWithRedirect
// The options of the project reference that owns the file, else the root
// options. The per-file checker queries below use it.
fn compiler_options_for_file(file: Node) -> &'static CompilerOptions {
    get_redirect_for_resolution(file)
        .map_or(&prog().options, ResolvedProjectReference::compiler_options)
}

// Go: compiler/program.go:199 GetResolvedProjectReferences
// PORT: see `get_project_reference_from_source`. A reference that did not
// load is None (Go nil).
pub fn get_resolved_project_references() -> Vec<Option<&'static ResolvedProjectReference>> {
    state()
        .go
        .as_ref()
        .map(go_frontend::GoSharedState::get_resolved_project_references)
        .unwrap_or_default()
}

// Go: compiler/program.go:2017 GetSymlinkCache
// PORT: the Go frontend program has the port, and this is its value. None
// on the legacy loader, where `modulespecifiers::host` builds its own.
pub fn get_go_symlink_cache() -> Option<&'static crate::modulespecifiers::symlinks::KnownSymlinks> {
    // Go: ls/autoimport/aliasresolver.go:143 (unimplemented)
    alias_resolver_unimplemented();
    state()
        .go
        .as_ref()
        .map(go_frontend::GoSharedState::known_symlinks)
}

// Go: compiler/program.go:165 GetSourceOfProjectReferenceIfOutputIncluded
pub fn get_source_of_project_reference_if_output_included(file: Node) -> String {
    // Go: ls/autoimport/aliasresolver.go:213 (unimplemented)
    alias_resolver_unimplemented();
    let info = source_file_info(file);
    state()
        .go
        .as_ref()
        .and_then(|go| go.get_source_of_project_reference_if_output_included(&info.path))
        .map_or_else(|| info.file_name.clone(), str::to_string)
}

/// Go `compiler.NewProgram` for a config that is already parsed, in a
/// one-program process (`tsc`, `goport`). It installs the program for the
/// process, so call it once. `opts.host` carries the trace writer.
pub fn install_new_program(
    opts: crate::frontend::compiler::ProgramOptions,
) -> Result<&'static GoProgram, String> {
    go_frontend::install_new_program(opts)
}

/// Go `compiler.NewProgram` for a multi-program process (watch, language
/// server, tests), with the Go frontend. It loads a new program version and
/// does not make it current: read it inside `core::enter_program`. Call it
/// on the loading thread, which keeps the frontend and the checker pool of
/// the version. `edit_options` is as in `try_load_with`. The version is
/// leaked; `release_program` frees its checker pool.
pub fn try_load_version(
    config_path: &str,
    edit_options: impl FnOnce(&mut CompilerOptions),
) -> Result<&'static GoProgram, String> {
    go_frontend::try_load_version(config_path, edit_options)
}

/// Go `Program.UpdateProgram`: a new version of `old` after an edit of
/// `changed_file` (a file name, relative to the current directory or
/// absolute). It reads `changed_file` from disk again. When the edit keeps
/// the imports and references, the new version shares every other file
/// version with `old` and the second value is true. Else every file is
/// parsed again. `old` stays usable. Loading thread only.
pub fn update_program_version(
    old: &'static GoProgram,
    changed_file: &str,
) -> (&'static GoProgram, bool) {
    go_frontend::update_program_version(old, changed_file)
}

/// Go `compiler.NewProgram` and `Program.UpdateProgram` for a
/// multi-program process whose caller builds the frontend program `np`
/// itself (the language server, watch mode). It builds the Go files of the
/// stores that `np` parsed, publishes them and makes the program version of
/// `np`. It does not make it current: read it inside `core::enter_program`.
/// `previous` is the version that `np` was updated from, if it is still
/// loaded; the new version shares its copies of unchanged frontend data.
/// Call it on the loading thread, after `np` is built with no current
/// program.
pub fn new_program_version(
    np: &'static crate::frontend::compiler::NewProgram,
    previous: Option<&'static GoProgram>,
) -> &'static GoProgram {
    go_frontend::new_program_version(np, previous)
}

/// Records a source file that this thread parsed outside a program load
/// (the language server parse cache). When a program version publishes
/// the file's store but does not include the file, the store still gets
/// the file's Go file (parser fields), so a later version can share it.
pub fn note_parsed_source_file(file: &Rc<crate::frontend::parser::ParsedSourceFile>) {
    go_frontend::note_parsed_source_file(file);
}

/// Publishes this thread's unpublished stores with no program: the files
/// that `note_parsed_source_file` recorded get their Go files, and other
/// stores (config files) the name only. Then their nodes can be bound
/// (`bind_file_outside_program`). `cwd` is the current directory of the
/// caller's host.
pub fn publish_parsed_files(cwd: &str) {
    go_frontend::publish_parsed_files(cwd);
}

/// Go `binder.BindSourceFile` for a published file that no program
/// includes (Go `BindOnce`: a program that includes it later does not bind
/// it again). The file joins the binder lineage of the process.
pub fn bind_file_outside_program(file: Node) {
    let mut lineage = LINEAGE.lock().unwrap_or_else(PoisonError::into_inner);
    bind_source_file(file, lineage.get_or_insert_with(SymbolArena::new));
}

/// Frees what the loading thread keeps for `program`: it stops the checker
/// pool (and waits for its workers, which free their checkers and synthetic
/// nodes), removes the frontend program from this thread and empties the
/// declaration diagnostic cache. Do not use `program` after this. Its
/// `GoProgram`, frontend program and file versions stay leaked. Panics when
/// `program` is current on this thread.
pub fn release_program(program: &'static GoProgram) {
    release_program_with(program, CheckerPool::shut_down);
}

/// `release_program` that does not wait for the checker workers: they free
/// their checkers and synthetic nodes on their own threads while the caller
/// goes on (Go frees a program in the background GC). `tsc -b` uses it, so
/// the next project does not wait for the free.
pub fn release_program_in_background(program: &'static GoProgram) {
    release_program_with(program, CheckerPool::shut_down_in_background);
}

/// `release_program` with the pool stop that `shut_down` names.
fn release_program_with(program: &'static GoProgram, shut_down: fn(CheckerPool)) {
    assert!(
        !try_prog().is_some_and(|current| std::ptr::eq(current, program)),
        "program {} is released while it is current",
        program.id
    );
    let pool = POOLS.with(|pools| pools.borrow_mut().remove(&program.id));
    if let Some(pool) = pool {
        shut_down(pool);
    }
    FRONTENDS.with(|frontends| frontends.borrow_mut().remove(&program.id));
    if let Some(state) = program.state.get() {
        drop(std::mem::take(
            &mut *state
                .declaration_diagnostic_cache
                .lock()
                .unwrap_or_else(PoisonError::into_inner),
        ));
    }
}

/// The Go frontend program, or None on the legacy path. Loading thread only.
pub fn go_frontend_program() -> Option<&'static crate::frontend::compiler::NewProgram> {
    go_frontend().map(|go| go.program)
}

// Go: compiler/program.go:1841 ExplainFiles
// PORT: the legacy path has no Go frontend program and writes nothing.
pub fn explain_files(w: &mut String, locale: &crate::locale::Locale) {
    if let Some(go) = go_frontend() {
        go.program.explain_files(w, locale);
    }
}

// Go: compiler/program.go:397 SourceFiles
pub fn source_files() -> Vec<Node> {
    prog().source_files().map(|file| file.root).collect()
}

// Go: compiler/program.go:399 Options
pub fn options() -> &'static CompilerOptions {
    &prog().options
}

// Go: compiler/program.go:403 GetConfigFileParsingDiagnostics
// PORT: `ts_compiler` records of the option checks in `verify_options` are
// removed. Go reports those as program diagnostics.
pub fn get_config_file_parsing_diagnostics() -> Vec<Diagnostic> {
    if let Some(go) = go_frontend() {
        return go.program.get_config_file_parsing_diagnostics();
    }
    verify_options::without_reverified_option_diagnostics(&state().config_diagnostics)
}

// Go: compiler/program.go:441 SingleThreaded
pub fn single_threaded() -> bool {
    prog().options.single_threaded.is_true()
}

// Go: compiler/program.go:494 GetResolvedModule
// PORT: resolutions come from the `ts_compiler` graph loader, which keeps
// only the loaded target file per (file, specifier, mode). The Go
// `ResolvedModule` is rebuilt from that target. When the exact mode has no
// entry, the other modes are tried, because the Rust loader may key an
// import by a different mode than the Go mode computation. A miss (Go: a
// failed resolution) returns None.
// PERF: the Go frontend path borrows the stored resolution. Only the legacy
// path, which builds a new one, returns it owned.
pub fn get_resolved_module(
    file: Node,
    module_reference: &str,
    mode: ResolutionMode,
) -> Option<Cow<'static, ResolvedModule>> {
    // Go: ls/autoimport/aliasresolver.go:116 GetResolvedModule (never nil)
    if let Some(resolver) = alias_resolver() {
        return Some(Cow::Owned(resolver.resolved_module(
            file,
            module_reference,
            mode,
        )));
    }
    if let Some(go) = &state().go {
        return go
            .get_resolved_module(file, module_reference, mode)
            .map(Cow::Borrowed);
    }
    let program = prog();
    let go_file = crate::ast::go_file(file.file_index());
    let formats = [
        None,
        Some(ts_module::ModuleFormat::CommonJs),
        Some(ts_module::ModuleFormat::Esm),
    ];
    let wanted = if mode == ModuleKind::COMMON_JS {
        Some(ts_module::ModuleFormat::CommonJs)
    } else if mode == ModuleKind::ES_NEXT {
        Some(ts_module::ModuleFormat::Esm)
    } else {
        None
    };
    let target = std::iter::once(wanted)
        .chain(formats.into_iter().filter(|f| *f != wanted))
        .find_map(|format| {
            program
                .program
                .expect("legacy program")
                .resolved_module_file(go_file.legacy_source().id, module_reference, format)
        })?;
    Some(Cow::Owned(build_resolved_module(
        module_reference,
        &target.file_name,
    )))
}

fn build_resolved_module(module_reference: &str, resolved_file_name: &str) -> ResolvedModule {
    let extension =
        ts_path::extension_from_path(resolved_file_name).map_or("", ts_path::FileExtension::as_str);
    let is_external_library_import = resolved_file_name.contains("/node_modules/");
    let mut package_id = PackageId::default();
    if let Some(index) = resolved_file_name.rfind("/node_modules/") {
        let rest = &resolved_file_name[index + "/node_modules/".len()..];
        let mut parts = rest.split('/');
        let first = parts.next().unwrap_or("");
        let name = if first.starts_with('@') {
            format!("{first}/{}", parts.next().unwrap_or(""))
        } else {
            first.to_string()
        };
        let sub_module_name = rest[name.len().min(rest.len())..]
            .trim_start_matches('/')
            .to_string();
        package_id = PackageId {
            name,
            sub_module_name,
            ..PackageId::default()
        };
    }
    ResolvedModule {
        resolved_file_name: resolved_file_name.to_string(),
        original_path: String::new(),
        extension: extension.to_string(),
        resolved_using_ts_extension: ts_path::has_typescript_extension(module_reference)
            && !ts_path::is_declaration_file(module_reference),
        package_id,
        is_external_library_import,
        alternate_result: String::new(),
        resolution_diagnostics: Vec::new(),
    }
}

// Go: compiler/program.go:503 GetResolvedModuleFromModuleSpecifier
pub fn get_resolved_module_from_module_specifier(
    file: Node,
    module_specifier: Node,
) -> Option<ResolvedModule> {
    // Go: ls/autoimport/aliasresolver.go:208 (unimplemented)
    alias_resolver_unimplemented();
    if !is_string_literal_like(module_specifier) {
        panic!("moduleSpecifier must be a StringLiteralLike");
    }
    let mode = get_mode_for_usage_location(file, module_specifier);
    get_resolved_module(file, module_specifier.text(), mode).map(Cow::into_owned)
}

// Go: compiler/program.go:511 GetResolvedModules
// Go: compiler/fileloader.go:528 resolveImportsAndModuleAugmentations (the
// module names of each file's map)
// PORT: Go returns the map the file loader filled. It is rebuilt here on
// first use, keyed by file path, then (name, mode), from the same module
// names in the same order: the import helpers and JSX runtime synthetic
// imports, then the imports, then the string literal module augmentations.
// Only the Go frontend records the synthetic imports, so the legacy loader
// skips them. Go also keeps the `libReplacement` lib resolutions, keyed by
// the path they resolve from (filesparser.go:505). They are not in this map,
// because the checker copy of the Go frontend data looks up resolutions by
// program file only.
pub fn get_resolved_modules()
-> &'static IndexMap<String, IndexMap<(String, ResolutionMode), ResolvedModule>> {
    state().resolved_modules.get_or_init(|| {
        let mut result = IndexMap::new();
        for file in prog().source_files() {
            let mut in_file = IndexMap::new();
            let mut synthetic_imports = Vec::new();
            if state().go.is_some() {
                synthetic_imports.push(get_import_helpers_import_specifier(&file.info.path));
                synthetic_imports.push(get_jsx_runtime_import_specifier(&file.info.path).1);
            }
            let synthetic_imports = synthetic_imports.into_iter().filter(|n| n.is_some());
            let augmentations = file
                .info
                .module_augmentations
                .iter()
                .copied()
                .filter(|n| is_string_literal(*n));
            for specifier in synthetic_imports
                .chain(file.info.imports.iter().copied())
                .chain(augmentations)
            {
                let name = specifier.text().to_string();
                let mode = get_mode_for_usage_location(file.root, specifier);
                if in_file.contains_key(&(name.clone(), mode)) {
                    continue;
                }
                if let Some(resolved) = get_resolved_module(file.root, &name, mode) {
                    in_file.insert((name, mode), resolved.into_owned());
                }
            }
            result.insert(file.info.path.clone(), in_file);
        }
        result
    })
}

// Go: compiler/program.go:1519 GetSourceFileMetaData
pub fn get_source_file_meta_data(path: &str) -> SourceFileMetaData {
    // Go: ls/autoimport/aliasresolver.go:148 (unimplemented)
    alias_resolver_unimplemented();
    file_meta_by_path(path)
        .map(|meta| meta.meta_data.clone())
        .unwrap_or_default()
}

// Borrowed form of `get_source_file_meta_data` for the mode functions
// below, which run for each import and so do not clone the metadata
// strings. A path with no file gets the default metadata, as there.
fn source_file_meta_data_ref(path: &str) -> &'static SourceFileMetaData {
    static MISSING: std::sync::LazyLock<SourceFileMetaData> =
        std::sync::LazyLock::new(SourceFileMetaData::default);
    match file_meta_by_path(path) {
        Some(meta) => &meta.meta_data,
        None => &MISSING,
    }
}

// Go: compiler/program.go:1523 GetEmitModuleFormatOfFile
pub fn get_emit_module_format_of_file(source_file: Node) -> ModuleKind {
    // Go: ls/autoimport/aliasresolver.go:96 GetEmitModuleFormatOfFile
    if state().alias_resolver {
        return ModuleKind::ES_NEXT;
    }
    let info = source_file_info(source_file);
    get_emit_module_format_of_file_worker(
        &info.file_name,
        compiler_options_for_file(source_file),
        source_file_meta_data_ref(&info.path),
    )
}

// Go: compiler/program.go:1527 GetEmitSyntaxForUsageLocation
pub fn get_emit_syntax_for_usage_location(source_file: Node, location: Node) -> ResolutionMode {
    // Go: ls/autoimport/aliasresolver.go:101 GetEmitSyntaxForUsageLocation
    if state().alias_resolver {
        return ModuleKind::ES_NEXT;
    }
    let info = source_file_info(source_file);
    get_emit_syntax_for_usage_location_worker(
        &info.file_name,
        source_file_meta_data_ref(&info.path),
        location,
        compiler_options_for_file(source_file),
    )
}

// Go: compiler/program.go:1531 GetImpliedNodeFormatForEmit
pub fn get_implied_node_format_for_emit(source_file: Node) -> ResolutionMode {
    // Go: ls/autoimport/aliasresolver.go:106 GetImpliedNodeFormatForEmit
    if state().alias_resolver {
        return ModuleKind::ES_NEXT;
    }
    let info = source_file_info(source_file);
    get_implied_node_format_for_emit_worker(
        &info.file_name,
        compiler_options_for_file(source_file).get_emit_module_kind(),
        source_file_meta_data_ref(&info.path),
    )
}

// Go: compiler/program.go:1535 GetModeForUsageLocation
pub fn get_mode_for_usage_location(source_file: Node, location: Node) -> ResolutionMode {
    // Go: ls/autoimport/aliasresolver.go:111 GetModeForUsageLocation
    if state().alias_resolver {
        return ModuleKind::ES_NEXT;
    }
    let info = source_file_info(source_file);
    get_mode_for_usage_location_worker(
        &info.file_name,
        source_file_meta_data_ref(&info.path),
        location,
        compiler_options_for_file(source_file),
    )
}

// Go: compiler/program.go:1539 GetDefaultResolutionModeForFile
pub fn get_default_resolution_mode_for_file(source_file: Node) -> ResolutionMode {
    // Go: ls/autoimport/aliasresolver.go:91 GetDefaultResolutionModeForFile
    if state().alias_resolver {
        return ModuleKind::ES_NEXT;
    }
    let info = source_file_info(source_file);
    get_default_resolution_mode_for_file_worker(
        &info.file_name,
        source_file_meta_data_ref(&info.path),
        compiler_options_for_file(source_file),
    )
}

// Go: compiler/program.go:1543 IsSourceFileDefaultLibrary
pub fn is_source_file_default_library(path: &str) -> bool {
    file_meta_by_path(path).is_some_and(|meta| meta.is_default_library)
}

// Go: compiler/program.go:1562 CommonSourceDirectory
// PORT: the Go frontend program computes it once (see `GoSharedState`). The
// legacy loader computes it here.
pub fn common_source_directory() -> &'static str {
    // Go: ls/autoimport/aliasresolver.go:153 (unimplemented)
    alias_resolver_unimplemented();
    if let Some(go) = &state().go {
        return go.common_source_directory();
    }
    state().common_source_directory.get_or_init(|| {
        let files = || {
            prog()
                .source_files()
                .filter(|file| {
                    source_file_may_be_emitted(file.root, false) && !file.info.is_declaration_file
                })
                .map(|file| file.info.file_name.clone())
                .collect::<Vec<_>>()
        };
        get_common_source_directory(
            &prog().options,
            files,
            get_current_directory(),
            state().case_sensitivity,
        )
    })
}

// Go: outputpaths/commonsourcedirectory.go:59 GetCommonSourceDirectory
// PORT: Go `checkSourceFilesBelongToPath` reports TS6059 (file not under
// rootDir) as include processor diagnostics. It is not run, and the Rust
// graph loader does not report TS6059 either.
fn get_common_source_directory(
    options: &CompilerOptions,
    files: impl FnOnce() -> Vec<String>,
    current_directory: &str,
    case_sensitivity: CaseSensitivity,
) -> String {
    let common_source_directory = if !options.root_dir.is_empty() {
        // If a rootDir is specified use it as the commonSourceDirectory
        options.root_dir.clone()
    } else if !options.config_file_path.is_empty() {
        // If the rootDir is not specified, then the common source directory is the directory of the config file.
        ts_path::directory_path(&options.config_file_path)
    } else {
        compute_common_source_directory_of_filenames(&files(), current_directory, case_sensitivity)
    };
    if common_source_directory.is_empty() {
        return common_source_directory;
    }
    // Make sure directory path ends with directory separator so this string can directly
    // used to replace with "" to get the relative path of the source file and the relative path doesn't
    // start with / making it rooted path
    ts_path::ensure_trailing_directory_separator(&common_source_directory)
}

// Go: tspath GetNormalizedPathComponents (root first, then the parts)
fn get_normalized_path_components(path: &str, current_directory: &str) -> Vec<String> {
    let absolute = ts_path::resolve_path(current_directory, &[path]);
    let root_len = if absolute.starts_with('/') {
        1
    } else if absolute.as_bytes().get(1) == Some(&b':') {
        if absolute.as_bytes().get(2) == Some(&b'/') {
            3
        } else {
            2
        }
    } else {
        0
    };
    let mut components = vec![absolute[..root_len].to_string()];
    components.extend(
        absolute[root_len..]
            .split('/')
            .filter(|part| !part.is_empty())
            .map(str::to_string),
    );
    components
}

// Go: tspath GetPathFromPathComponents
fn get_path_from_path_components(components: &[String]) -> String {
    let Some((root, rest)) = components.split_first() else {
        return String::new();
    };
    let root = if root.is_empty() {
        String::new()
    } else {
        ts_path::ensure_trailing_directory_separator(root)
    };
    format!("{root}{}", rest.join("/"))
}

// Go: outputpaths/commonsourcedirectory.go:8 computeCommonSourceDirectoryOfFilenames
fn compute_common_source_directory_of_filenames(
    file_names: &[String],
    current_directory: &str,
    case_sensitivity: CaseSensitivity,
) -> String {
    let mut common_path_components: Option<Vec<String>> = None;
    for source_file in file_names {
        // Each file contributes into common source file path
        let mut source_path_components =
            get_normalized_path_components(source_file, current_directory);
        // The base file name is not part of the common directory path
        source_path_components.pop();
        let Some(common) = common_path_components.as_mut() else {
            // first file
            common_path_components = Some(source_path_components);
            continue;
        };
        let n = common.len().min(source_path_components.len());
        for i in 0..n {
            if ts_path::canonical_file_name(&common[i], case_sensitivity)
                != ts_path::canonical_file_name(&source_path_components[i], case_sensitivity)
            {
                if i == 0 {
                    // Failed to find any common path component
                    return String::new();
                }
                // New common path found that is 0 -> i-1
                common.truncate(i);
                break;
            }
        }
        // If the sourcePathComponents was shorter than the commonPathComponents, truncate to the sourcePathComponents
        if source_path_components.len() < common.len() {
            common.truncate(source_path_components.len());
        }
    }
    match common_path_components {
        Some(common) if !common.is_empty() => get_path_from_path_components(&common),
        // Can happen when all input files are .d.ts files
        _ => current_directory.to_string(),
    }
}

// Go: compiler/program.go:1912 IsSourceFileFromExternalLibrary
// PORT: the Go frontend loader records files found while searching
// node_modules. The legacy loader does not; a path inside node_modules
// stands in for it there.
pub fn is_source_file_from_external_library(file: Node) -> bool {
    let path = &source_file_info(file).path;
    if let Some(go) = &state().go {
        return go.is_source_file_from_external_library(path);
    }
    path.contains("/node_modules/")
}

// Go: compiler/program.go:1225 IsEmitBlocked
// PORT: the legacy loader does not verify output paths, so nothing is
// blocked there.
pub fn is_emit_blocked(emit_file_name: &str) -> bool {
    state()
        .go
        .as_ref()
        .is_some_and(|go| go.is_emit_blocked(emit_file_name))
}

// Go: compiler/program.go:1927 SourceFileMayBeEmitted
pub fn source_file_may_be_emitted(source_file: Node, force_dts_emit: bool) -> bool {
    // Go: ls/autoimport/aliasresolver.go:228 (unimplemented)
    alias_resolver_unimplemented();
    source_file_may_be_emitted_worker(source_file, force_dts_emit)
}

// Go: compiler/emitter.go:451 sourceFileMayBeEmitted
fn source_file_may_be_emitted_worker(source_file: Node, force_dts_emit: bool) -> bool {
    let options = &prog().options;
    let info = source_file_info(source_file);
    // Js files are emitted only if option is enabled
    if options.no_emit_for_js_files.is_true() && is_source_file_js(source_file) {
        return false;
    }
    // Declaration files are not emitted
    if info.is_declaration_file {
        return false;
    }
    // Source file from node_modules are not emitted
    if is_source_file_from_external_library(source_file) {
        return false;
    }
    // forcing dts emit => file needs to be emitted
    if force_dts_emit {
        return true;
    }
    // Source files from referenced projects are not emitted
    if get_project_reference_from_source(&info.path).is_some() {
        return false;
    }
    // Any non json file should be emitted
    if !is_json_source_file(source_file) {
        return true;
    }
    // Json file is not emitted if outDir is not specified
    if options.out_dir.is_empty() {
        return false;
    }
    // Otherwise, if rootDir is specified or a config file exists, we know the common source directory and can check if the file would be emitted in the same location
    if !options.root_dir.is_empty() || !options.config_file_path.is_empty() {
        let cwd = get_current_directory();
        let cs = state().case_sensitivity;
        let common_dir = ts_path::resolve_path(
            cwd,
            &[&get_common_source_directory(options, Vec::new, cwd, cs)],
        );
        let output_path = get_source_file_path_in_new_dir_worker(
            &info.file_name,
            &options.out_dir,
            cwd,
            &common_dir,
            cs,
        );
        if ts_path::canonicalize(&info.file_name, cwd, cs)
            == ts_path::canonicalize(&output_path, cwd, cs)
        {
            return false;
        }
    }
    true
}

// Go: outputpaths/outputpaths.go GetSourceFilePathInNewDirWorker
fn get_source_file_path_in_new_dir_worker(
    file_name: &str,
    new_dir_path: &str,
    current_directory: &str,
    common_source_directory: &str,
    case_sensitivity: CaseSensitivity,
) -> String {
    let mut source_file_path = ts_path::resolve_path(current_directory, &[file_name]);
    let common = ts_path::ensure_trailing_directory_separator(common_source_directory);
    let is_in_common = ts_path::canonical_file_name(&source_file_path, case_sensitivity)
        .starts_with(&ts_path::canonical_file_name(&common, case_sensitivity));
    if is_in_common {
        source_file_path = source_file_path[common.len().min(source_file_path.len())..].to_string();
    }
    ts_path::combine_paths(new_dir_path, &[&source_file_path])
}

// Go: compiler/program.go:1792 GetSourceFile
pub fn get_source_file(file_name: &str) -> Node {
    // Go: ls/autoimport/aliasresolver.go:80 GetSourceFile
    if let Some(resolver) = alias_resolver() {
        return resolver.source_file(file_name);
    }
    let path = ts_path::canonicalize(file_name, get_current_directory(), state().case_sensitivity);
    get_source_file_by_path(&path)
}

// Go: compiler/program.go:1812 GetSourceFileByPath
pub fn get_source_file_by_path(path: &str) -> Node {
    state()
        .file_by_path
        .get(path)
        .map_or(Node::NIL, |&index| crate::ast::go_file(index).root)
}

/// A memo of `get_source_file_for_resolved_module` by file name, for the
/// program with id `program`.
struct ResolvedModuleFiles {
    program: u32,
    files: FxHashMap<String, Node>,
}

thread_local! {
    /// Memo of `get_source_file_for_resolved_module` for the current program
    /// of this thread. Program ids start at 1, so 0 is no program.
    static RESOLVED_MODULE_FILES: RefCell<ResolvedModuleFiles> = const {
        RefCell::new(ResolvedModuleFiles {
            program: 0,
            files: FxHashMap::with_hasher(rustc_hash::FxBuildHasher),
        })
    };
}

// Go: compiler/program.go:1797 GetSourceFileForResolvedModule
// PORT: the legacy loader has no parse-file redirects, so only the Go
// frontend program has the redirect fallback.
// PORT: the answer is memoized per thread and program. The files, their
// paths and the redirects of a program do not change after load, so a name
// always gives the same file. The checker asks again on each alias and
// default-import check, and each lookup canonicalizes the path. Another
// program version can give another file (an edited file has a new id), so
// the memo is emptied when the current program changes.
pub fn get_source_file_for_resolved_module(file_name: &str) -> Node {
    // Go: ls/autoimport/aliasresolver.go:130 GetSourceFileForResolvedModule
    if let Some(resolver) = alias_resolver() {
        return resolver.source_file_for_resolved_module(file_name);
    }
    let program = prog().id;
    let hit = RESOLVED_MODULE_FILES.with_borrow_mut(|memo| {
        if memo.program != program {
            memo.program = program;
            memo.files.clear();
            return None;
        }
        memo.files.get(file_name).copied()
    });
    if let Some(file) = hit {
        return file;
    }
    let mut file = get_source_file(file_name);
    if file.is_nil()
        && let Some(redirect) = state()
            .go
            .as_ref()
            .and_then(|go| go.get_parse_file_redirect(file_name))
    {
        file = get_source_file(redirect);
    }
    RESOLVED_MODULE_FILES.with_borrow_mut(|memo| memo.files.insert(file_name.to_string(), file));
    file
}

// Go: compiler/program.go:157 GetRedirectTargets
// PORT: the legacy loader does not deduplicate packages, so it has no
// redirect targets.
pub fn get_redirect_targets(path: &crate::frontend::tspath::Path) -> Vec<String> {
    // Go: ls/autoimport/aliasresolver.go:203 (unimplemented)
    alias_resolver_unimplemented();
    state()
        .go
        .as_ref()
        .map(|go| go.get_redirect_targets(&path.0))
        .unwrap_or_default()
}

// Go: compiler/program.go:226 GetSourceFileFromReference
// PORT: the Go frontend program has the port, and its answers for the
// preserved references are copied. The legacy loader runs the Go function
// on its own files.
pub fn get_source_file_from_reference(origin: Node, r: &FileReference) -> Node {
    if let Some(go) = &state().go {
        return go.get_source_file_from_reference(origin, r);
    }
    get_source_file_from_reference_legacy(origin, r)
}

// Go: compiler/program.go:226 GetSourceFileFromReference (the body)
fn get_source_file_from_reference_legacy(origin: Node, r#ref: &FileReference) -> Node {
    use crate::frontend::tspath::{
        file_extension_is_one_of, get_canonical_file_name, get_directory_path, has_extension,
        resolve_path,
    };
    // TODO: The module loader in corsa is fairly different than strada, it should probably be able to expose this functionality at some point,
    // rather than redoing the logic approximately here, since most of the related logic now lives in module.Resolver
    // Still, without the failed lookup reporting that only the loader does, this isn't terribly complicated

    let file_name = resolve_path(
        &get_directory_path(source_file_file_name(origin)),
        &[&r#ref.file_name],
    );
    let supported_extensions_base =
        crate::frontend::tsoptions::get_supported_extensions(options(), &[]);
    let supported_extensions =
        crate::frontend::tsoptions::get_supported_extensions_with_json_if_resolve_json_module(
            Some(options()),
            supported_extensions_base,
        );
    let allow_non_ts_extensions = options().allow_non_ts_extensions.is_true();
    if has_extension(&file_name) {
        if !allow_non_ts_extensions {
            let canonical_file_name =
                get_canonical_file_name(&file_name, use_case_sensitive_file_names());
            let supported = supported_extensions.iter().any(|group| {
                let group: Vec<&str> = group.iter().map(String::as_str).collect();
                file_extension_is_one_of(&canonical_file_name, &group)
            });
            if !supported {
                return Node::NIL; // unsupported extensions are forced to fail
            }
        }

        return get_source_file_for_resolved_module(&file_name);
    }
    if allow_non_ts_extensions {
        let extensionless = get_source_file_for_resolved_module(&file_name);
        if extensionless.is_some() {
            return extensionless;
        }
    }

    // Only try adding extensions from the first supported group (which should be .ts/.tsx/.d.ts)
    for ext in &supported_extensions[0] {
        let result = get_source_file_for_resolved_module(&format!("{file_name}{ext}"));
        if result.is_some() {
            return result;
        }
    }
    Node::NIL
}

// Go: outputpaths/outputpaths.go:42 GetOutputPathsFor, called by
// compiler/emitHost.go:94 emitHost.GetOutputPathsFor with the program options.
// PORT: Go reads two fields of the source file. It is named for the emit
// host method so it does not clash with the frontend `get_output_paths_for`
// in the frontend prelude.
pub fn get_output_paths_for_source_file(
    file: Node,
    host: &dyn crate::frontend::outputpaths::OutputPathsHost,
    force_dts_paths: bool,
) -> crate::frontend::outputpaths::OutputPaths {
    let info = source_file_info(file);
    crate::frontend::outputpaths::get_output_paths_for_file(
        &info.file_name,
        info.script_kind,
        options(),
        host,
        force_dts_paths,
    )
}

// Go: compiler/program.go:1916 GetJSXRuntimeImportSpecifier
// Go: compiler/fileloader.go:550 (the value the loader records)
// PORT: on the Go frontend the loader records the value and its synthetic
// import (Go `createSyntheticImport`). On the legacy path the specifier is
// nil and callers fall back to their own location node.
pub fn get_jsx_runtime_import_specifier(path: &str) -> (String, Node) {
    // Go: ls/autoimport/aliasresolver.go:173 (unimplemented)
    alias_resolver_unimplemented();
    if let Some(go) = &state().go {
        return go.get_jsx_runtime_import_specifier(path);
    }
    let Some(info) = file_info_by_path(path) else {
        return (String::new(), Node::NIL);
    };
    if info.script_kind != ScriptKind::JSX && info.script_kind != ScriptKind::TSX {
        return (String::new(), Node::NIL);
    }
    let options = &prog().options;
    let file = crate::ast::go_file(info.file_index).root;
    let jsx_import = get_jsx_runtime_import(&get_jsx_implicit_import_base(options, file), options);
    if jsx_import.is_empty() {
        return (String::new(), Node::NIL);
    }
    (jsx_import, Node::NIL)
}

// Go: compiler/program.go:1923 GetImportHelpersImportSpecifier
// PORT: the Go frontend loader records the synthetic imports. On the legacy
// path `record_legacy_import_helpers_import_specifiers` records them.
pub fn get_import_helpers_import_specifier(path: &str) -> Node {
    // Go: ls/autoimport/aliasresolver.go:168 (unimplemented)
    alias_resolver_unimplemented();
    if let Some(go) = &state().go {
        return go.get_import_helpers_import_specifier(path);
    }
    LEGACY_IMPORT_HELPERS_IMPORT_SPECIFIERS
        .get()
        .and_then(|specifiers| specifiers.get(path).copied())
        .unwrap_or(Node::NIL)
}

/// Go `processedFiles.importHelpersImportSpecifiers` on the legacy path, by
/// file path.
static LEGACY_IMPORT_HELPERS_IMPORT_SPECIFIERS: OnceLock<FxHashMap<String, Node>> = OnceLock::new();

// Go: compiler/fileloader.go:541 (the import helpers part of
// resolveImportsAndModuleAugmentations)
// PORT: the legacy ts_compiler loader resolves `tslib` but makes no node for
// it. This makes the Go synthetic import of each file that needs one. It runs
// on the loading thread before binding, so the checker workers get the nodes
// with the synthetic seed. The legacy path has no project reference
// redirects, so the Go `optionsForFile` are the program options, and the
// condition is `needsImportHelpersImportSpecifier`.
fn record_legacy_import_helpers_import_specifiers() {
    let factory = NodeFactory::new();
    let mut specifiers = FxHashMap::default();
    for file in prog().source_files() {
        if needs_import_helpers_import_specifier(file.root) {
            let specifier =
                create_synthetic_import(&factory, EXTERNAL_HELPERS_MODULE_NAME_TEXT, file.root);
            specifiers.insert(file.info.path.clone(), specifier);
        }
    }
    assert!(
        LEGACY_IMPORT_HELPERS_IMPORT_SPECIFIERS
            .set(specifiers)
            .is_ok(),
        "legacy import helpers specifiers recorded twice"
    );
}

// Go: compiler/fileloader.go:634 (*fileLoader).createSyntheticImport
// PORT: the legacy path has no fileLoader, so the factory is a parameter.
fn create_synthetic_import(factory: &NodeFactory, text: &str, file: Node) -> Node {
    let external_helpers_module_reference = factory.new_string_literal(text, TokenFlags::NONE);
    let import_decl = factory.new_import_declaration(
        ModifierList::NIL,
        Node::NIL,
        external_helpers_module_reference,
        Node::NIL,
    );
    set_node_parent(external_helpers_module_reference, import_decl);
    set_node_parent(import_decl, file);
    external_helpers_module_reference
}

// Go: compiler/program.go:367 needsImportHelpersImportSpecifier
fn needs_import_helpers_import_specifier(file: Node) -> bool {
    let options = &prog().options;
    if !options.import_helpers.is_true() {
        return false;
    }
    let is_java_script_file = is_source_file_js(file);
    let is_external_module_file = is_external_module(file);
    if !is_java_script_file
        && (source_file_info(file).is_declaration_file
            || (!options.get_isolated_modules() && !is_external_module_file))
    {
        return false;
    }
    true
}

// Go: compiler/program.go:517 GetPackagesMap
pub fn get_packages_map() -> FxHashMap<String, bool> {
    let mut packages_map: FxHashMap<String, bool> = FxHashMap::default();
    for resolved_modules_in_file in get_resolved_modules().values() {
        for module in resolved_modules_in_file.values() {
            if !module.package_id.name.is_empty() {
                let previous = packages_map
                    .get(&module.package_id.name)
                    .copied()
                    .unwrap_or(false);
                packages_map.insert(
                    module.package_id.name.clone(),
                    previous || module.extension == ".d.ts",
                );
            }
        }
    }
    packages_map
}

// ---------------------------------------------------------------------------
// Checker pool (Go compiler/checkerpool.go)
// PORT: Go runs one goroutine task per checker on a work group. A Rust
// checker is not Send (it holds Rc and thread-local state), so each checker
// is made on its own worker thread and stays there. The loading thread
// sends jobs to the workers and waits for the results, which it merges in
// file order. Each checker sees only its own files, in file order, so the
// results match the Go grouping and do not depend on thread timing.
// ---------------------------------------------------------------------------

/// Stack size of a checker worker thread. The checker recurses deeply on
/// large projects.
const CHECKER_STACK_SIZE: usize = 1 << 30;

thread_local! {
    /// The checker pools of the loading thread, by `GoProgram::id`.
    static POOLS: RefCell<FxHashMap<u32, CheckerPool>> = RefCell::new(FxHashMap::default());
    /// The checker of a worker thread.
    static WORKER_CHECKER: RefCell<Option<Checker>> = const { RefCell::new(None) };
    /// The pool index of the checker of a worker thread.
    static WORKER_INDEX: std::cell::Cell<Option<usize>> = const { std::cell::Cell::new(None) };
    /// Set on a worker thread when `CheckerPool::stop` freed its checker and
    /// synthetic nodes.
    static WORKER_RELEASED: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

/// The thread-local state that a checker worker starts from: the current
/// program, and the synthetic nodes, ids and lazy JSDoc of the loading
/// thread when the pool is made. The language server's cross-project search
/// threads start from it too (`ls/search_thread.rs`).
pub(crate) struct WorkerSeed {
    program: &'static GoProgram,
    synthetic: SyntheticSeed,
    ids: IdSeed,
    lazy_jsdoc: FxHashMap<Node, &'static [Node]>,
}

impl WorkerSeed {
    pub(crate) fn take() -> Self {
        Self {
            program: prog(),
            synthetic: synthetic_seed(),
            ids: id_seed(),
            lazy_jsdoc: go_frontend::lazy_jsdoc_seed(),
        }
    }

    pub(crate) fn install(self) {
        crate::core::set_thread_program(Some(self.program));
        install_synthetic_seed(self.synthetic);
        install_id_seed(self.ids);
        go_frontend::install_lazy_jsdoc_seed(self.lazy_jsdoc);
    }
}

// Go: compiler/checkerpool.go:40 newCheckerPoolWithTracing (the count)
fn checker_count() -> usize {
    let program = prog();
    let mut checker_count: i64 = 4;
    if single_threaded() {
        checker_count = 1;
    } else if let Some(count) = program.options.checkers {
        checker_count = i64::from(count);
    }
    checker_count
        .min(program.source_file_order.len() as i64)
        .min(256)
        .max(1) as usize
}

// Go: compiler/checkerpool.go:98 createCheckers
// PORT: binding runs first on this thread, so no worker binds and every
// worker starts from the same bound program and thread-local state.
fn create_checkers() -> CheckerPool {
    bind_all();
    let count = checker_count();
    let program = prog();
    // One entry per file id up to the last program file.
    let len = program
        .source_file_order
        .iter()
        .max()
        .map_or(0, |&last| last + 1);
    let mut file_associations = vec![0; len];
    for (i, &file_index) in program.source_file_order.iter().enumerate() {
        file_associations[file_index] = i % count;
    }
    assert!(
        state().file_associations.set(file_associations).is_ok(),
        "checker pool made twice"
    );
    let (workers, threads): (Vec<_>, Vec<_>) = (0..count)
        .map(|index| {
            let (sender, receiver) = std::sync::mpsc::channel::<Job>();
            let seed = WorkerSeed::take();
            let thread = std::thread::Builder::new()
                .name(format!("checker-{index}"))
                .stack_size(CHECKER_STACK_SIZE)
                .spawn(move || {
                    seed.install();
                    let checker = Checker::new(index);
                    WORKER_CHECKER.with(|slot| *slot.borrow_mut() = Some(checker));
                    WORKER_INDEX.with(|slot| slot.set(Some(index)));
                    for job in receiver {
                        job();
                    }
                    // In a one-program process the queue closes only when
                    // the loading thread ends, after every job sent its
                    // result, so this runs once per checker, at the end of
                    // the process. Like Go, which never frees a checker, the
                    // checker and the synthetic nodes are not dropped:
                    // freeing the checker arenas at thread exit cost 0.83%
                    // of query CPU. `release_program` frees both first
                    // (`CheckerPool::stop`), so a released program does not
                    // leak them.
                    if !WORKER_RELEASED.with(std::cell::Cell::get) {
                        std::mem::forget(WORKER_CHECKER.with(|slot| slot.borrow_mut().take()));
                        forget_synthetic_nodes();
                    }
                })
                .expect("cannot start a checker thread");
            (sender, thread)
        })
        .unzip();
    CheckerPool { workers, threads }
}

/// Starts `f` with checker `index` on its thread and returns where the
/// result arrives. Jobs for one checker run in the order they are sent.
fn send_job<R: Send + 'static>(
    index: usize,
    f: impl FnOnce(&mut Checker) -> R + Send + 'static,
) -> std::sync::mpsc::Receiver<JobResult<R>> {
    send_thread_job(index, move || with_checker_at(index, f))
}

/// `send_job` for work that borrows the checker itself (`with_checker_at`)
/// when it needs it.
fn send_thread_job<R: Send + 'static>(
    index: usize,
    f: impl FnOnce() -> R + Send + 'static,
) -> std::sync::mpsc::Receiver<JobResult<R>> {
    let (sender, receiver) = std::sync::mpsc::channel();
    let job: Job = Box::new(move || {
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(f));
        let _ = sender.send(result);
    });
    let id = prog().id;
    POOLS.with(|pools| {
        let mut pools = pools.borrow_mut();
        let pool = pools.entry(id).or_insert_with(create_checkers);
        pool.workers[index]
            .send(job)
            .expect("checker thread stopped");
    });
    receiver
}

/// Waits for a job result. A panic in the job continues on this thread.
fn wait_job<R>(receiver: &std::sync::mpsc::Receiver<JobResult<R>>) -> R {
    match receiver.recv().expect("checker thread stopped") {
        Ok(value) => value,
        Err(payload) => std::panic::resume_unwind(payload),
    }
}

/// Waits for every job, then returns the results in order. The first
/// panic, in job order, continues on this thread after all jobs end.
fn wait_jobs<R>(receivers: Vec<std::sync::mpsc::Receiver<JobResult<R>>>) -> Vec<R> {
    let results: Vec<JobResult<R>> = receivers
        .iter()
        .map(|receiver| receiver.recv().expect("checker thread stopped"))
        .collect();
    results
        .into_iter()
        .map(|result| result.unwrap_or_else(|payload| std::panic::resume_unwind(payload)))
        .collect()
}

/// True once the checker pool of the current program exists.
/// `crate::tracing` dumps the checkers' types only then, so that stopping a
/// trace does not make the pool.
pub fn checker_pool_created() -> bool {
    crate::core::try_prog()
        .and_then(|program| program.state.get())
        .is_some_and(|program_state| program_state.file_associations.get().is_some())
}

/// The pool index of this thread's checker, or None off the worker threads.
fn worker_index() -> Option<usize> {
    WORKER_INDEX.with(std::cell::Cell::get)
}

/// The checker index of `file` (Go `fileAssociations[file]`).
fn checker_index_for_file(file: Node) -> usize {
    if state().file_associations.get().is_none() {
        let id = prog().id;
        POOLS.with(|pools| {
            pools.borrow_mut().entry(id).or_insert_with(create_checkers);
        });
    }
    state()
        .file_associations
        .get()
        .expect("checker pool not made")[file.file_index()]
}

// Go: compiler/checkerpool.go:77 getCheckerForFileNonExclusive
// PORT: Go returns the checker and a release function. Here the checker is
// lent to `f` for the call, on the checker's own thread.
pub fn with_type_checker_for_file<R: Send + 'static>(
    file: Node,
    f: impl FnOnce(&mut Checker) -> R + Send + 'static,
) -> R {
    let index = checker_index_for_file(file);
    if worker_index().is_some() {
        return with_checker_at(index, f);
    }
    wait_job(&send_job(index, f))
}

/// A job sent to the checker thread of a file by `send_type_checker_job_for_file`.
/// `CheckerJob::Inline` holds the result when the caller is itself a checker
/// thread, where the job ran at once.
pub enum CheckerJob<R> {
    Sent(std::sync::mpsc::Receiver<JobResult<R>>),
    Inline(R),
}

impl<R> CheckerJob<R> {
    /// Waits for the result. A panic in the job continues on this thread.
    pub fn wait(self) -> R {
        match self {
            CheckerJob::Sent(receiver) => wait_job(&receiver),
            CheckerJob::Inline(value) => value,
        }
    }
}

/// `with_type_checker_for_file` without the wait: jobs for several files can
/// run on their checker threads at the same time (Go runs such loops in a
/// `WorkGroup`). Jobs for one checker still run in the order they are sent.
pub fn send_type_checker_job_for_file<R: Send + 'static>(
    file: Node,
    f: impl FnOnce(&mut Checker) -> R + Send + 'static,
) -> CheckerJob<R> {
    let index = checker_index_for_file(file);
    if worker_index().is_some() {
        return CheckerJob::Inline(with_checker_at(index, f));
    }
    CheckerJob::Sent(send_job(index, f))
}

// PORT: replaces EmitResolver.checkerMu. Lends checker `index` to `f`. Only
// the worker thread of that checker can do this; the checker is borrowed
// for the call, so `f` must not ask for it again.
pub fn with_checker_at<R>(index: usize, f: impl FnOnce(&mut Checker) -> R) -> R {
    let Some(worker) = worker_index() else {
        panic!("checker {index} used off its worker thread");
    };
    assert!(
        worker == index,
        "checker {index} used on the thread of checker {worker}"
    );
    WORKER_CHECKER.with(|slot| f(slot.borrow_mut().as_mut().expect("worker checker")))
}

// Go: compiler/checkerpool.go:123 forEachCheckerParallel
pub fn for_each_checker_parallel<R: Send + 'static>(cb: fn(usize, &mut Checker) -> R) -> Vec<R> {
    let count = checker_count();
    let receivers = (0..count)
        .map(|index| send_job(index, move |checker| cb(index, checker)))
        .collect();
    wait_jobs(receivers)
}

// Go: compiler/checkerpool.go:136 GetGlobalDiagnostics
fn pool_get_global_diagnostics() -> Vec<Diagnostic> {
    let global_diagnostics =
        for_each_checker_parallel(|_, checker| checker.get_global_diagnostics());
    sort_and_deduplicate_diagnostics(global_diagnostics.into_iter().flatten().collect())
}

// Go: compiler/checkerpool.go:148 forEachCheckerGroupDo
// PORT: returns the results of `cb` by file position instead of passing the
// position to `cb`. A file with no result keeps an empty list.
fn for_each_checker_group_do(
    files: &[Node],
    cb: fn(&mut Checker, Node) -> Vec<Diagnostic>,
) -> Vec<Vec<Diagnostic>> {
    start_checker_group_do(files, cb).wait()
}

/// `for_each_checker_group_do` whose jobs are sent and not waited for yet.
// PORT: not in Go. A Go caller that does not wait runs the group on its
// own goroutine. Here the loading thread sends the jobs and reads the
// results later. Jobs for one checker run in the order they are sent, so
// the results are the same as with an immediate wait.
struct PendingCheckerGroup {
    files: Arc<Vec<Node>>,
    receivers: Vec<std::sync::mpsc::Receiver<JobResult<Vec<(usize, Vec<Diagnostic>)>>>>,
}

impl PendingCheckerGroup {
    /// Waits for every checker and returns the results of `cb` by file
    /// position (see `for_each_checker_group_do`).
    fn wait(self) -> Vec<Vec<Diagnostic>> {
        let mut diagnostics = vec![Vec::new(); self.files.len()];
        for (i, result) in wait_jobs(self.receivers).into_iter().flatten() {
            diagnostics[i] = result;
        }
        diagnostics
    }
}

/// The first half of `for_each_checker_group_do`: sends one job to each
/// checker of the current program and returns without waiting.
fn start_checker_group_do(
    files: &[Node],
    cb: fn(&mut Checker, Node) -> Vec<Diagnostic>,
) -> PendingCheckerGroup {
    let count = checker_count();
    let files: Arc<Vec<Node>> = Arc::new(files.to_vec());
    let receivers = (0..count)
        .map(|checker_index| {
            let files = Arc::clone(&files);
            send_job(checker_index, move |checker| {
                let associations = state()
                    .file_associations
                    .get()
                    .expect("checker pool not made");
                let mut results = Vec::new();
                for (i, &file) in files.iter().enumerate() {
                    if associations[file.file_index()] == checker_index {
                        results.push((i, cb(checker, file)));
                    }
                }
                results
            })
        })
        .collect();
    PendingCheckerGroup { files, receivers }
}

// ---------------------------------------------------------------------------
// Diagnostics (Go compiler/program.go)
// ---------------------------------------------------------------------------

// Go: compiler/program.go:534 collectDiagnostics
// PORT: the per-file work runs serially (see the checker pool note).
fn collect_diagnostics(
    file: Node,
    collect: &mut dyn FnMut(Node) -> Vec<Diagnostic>,
) -> Vec<Diagnostic> {
    let result = if file.is_some() {
        collect(file)
    } else {
        prog()
            .source_files()
            .flat_map(|f| collect(f.root))
            .collect()
    };
    sort_and_deduplicate_diagnostics(result)
}

// Go: compiler/program.go:562 collectCheckerDiagnostics
/// Collects diagnostics for one file (or all files when `file` is nil) with
/// the checker that owns each file. The bin uses this to guard each file.
pub fn collect_checker_diagnostics_with(
    file: Node,
    collect: fn(&mut Checker, Node) -> Vec<Diagnostic>,
) -> Vec<Diagnostic> {
    if file.is_some() {
        if skip_type_checking(file, false) {
            return Vec::new();
        }
        let result = with_type_checker_for_file(file, move |c| collect(c, file));
        return sort_and_deduplicate_diagnostics(result);
    }
    let files = source_files();
    let diagnostics = collect_checker_diagnostics_from_files(&files, collect);
    sort_and_deduplicate_diagnostics(diagnostics.into_iter().flatten().collect())
}

// Go: compiler/program.go:576 collectCheckerDiagnosticsFromFiles
fn collect_checker_diagnostics_from_files(
    source_files: &[Node],
    collect: fn(&mut Checker, Node) -> Vec<Diagnostic>,
) -> Vec<Vec<Diagnostic>> {
    for_each_checker_group_do(source_files, collect)
}

// Go: compiler/program.go:599 GetSyntacticDiagnostics
pub fn get_syntactic_diagnostics(source_file: Node) -> Vec<Diagnostic> {
    let options = &prog().options;
    collect_diagnostics(source_file, &mut |file| {
        let info = source_file_info(file);
        let mut diags: Vec<Diagnostic> = info
            .diagnostics
            .iter()
            .chain(info.js_diagnostics)
            .cloned()
            .collect();
        // For JS files that won't be checked by the checker (no checkJs/ts-check), we need
        // program-level syntactic checks that require compiler options. This mirrors Strada's
        // getJSSyntacticDiagnosticsForFile in program.ts.
        if is_source_file_js(file) && !is_check_js_enabled_for_file(file, options) {
            diags.extend(get_additional_js_syntactic_diagnostics(file, options));
        }
        diags
    })
}

// Go: compiler/program.go:618 getAdditionalJSSyntacticDiagnostics
fn get_additional_js_syntactic_diagnostics(
    file: Node,
    options: &CompilerOptions,
) -> Vec<Diagnostic> {
    if options.experimental_decorators.is_true() {
        return Vec::new();
    }
    let mut diags = Vec::new();
    // Parameter decorators are only valid with experimentalDecorators. Without it,
    // the checker would report this, but the checker doesn't run on unchecked JS files.
    fn walk(node: Node, file: Node, diags: &mut Vec<Diagnostic>) -> bool {
        if !node
            .subtree_facts()
            .intersects(SubtreeFacts::SUBTREE_CONTAINS_DECORATORS)
        {
            return false;
        }
        if node.kind() == SyntaxKind::Parameter && has_decorators(node) {
            if let Some(decorator) = node.modifier_nodes().into_iter().find(|n| is_decorator(*n)) {
                diags.push(new_diagnostic(
                    file,
                    decorator.loc(),
                    diag::Decorators_are_not_valid_here,
                    Vec::new(),
                ));
            }
        }
        node.for_each_child(|child| walk(child, file, diags));
        false
    }
    file.for_each_child(|child| walk(child, file, &mut diags));
    diags
}

// Go: compiler/program.go:643 GetBindDiagnostics
// PORT: Go binds one file when given one. The Rust binder binds every file
// into one shared arena, so this always binds all files.
pub fn get_bind_diagnostics(source_file: Node) -> Vec<Diagnostic> {
    bind_all();
    collect_diagnostics(source_file, &mut |file| {
        file_bind_data(file).bind_diagnostics.clone()
    })
}

// Go: compiler/program.go:654 GetSemanticDiagnostics
// PORT: the compile path has no context; Go tsc passes context.Background()
// (execute/tsc/emit.go:75). The same holds for the two functions below.
pub fn get_semantic_diagnostics(source_file: Node) -> Vec<Diagnostic> {
    collect_checker_diagnostics_with(source_file, |c, f| {
        get_semantic_diagnostics_with_checker(&context::background(), c, f)
    })
}

// Go: compiler/program.go:658 GetSemanticDiagnosticsWithoutNoEmitFiltering
pub fn get_semantic_diagnostics_without_no_emit_filtering(
    source_files: &[Node],
) -> FxHashMap<Node, Vec<Diagnostic>> {
    start_semantic_diagnostics_without_no_emit_filtering(source_files).wait()
}

/// A `get_semantic_diagnostics_without_no_emit_filtering` check that runs
/// on the checker threads while the caller goes on.
pub struct PendingSemanticDiagnostics(PendingCheckerGroup);

impl PendingSemanticDiagnostics {
    /// The files that are checked, in the order they were given.
    #[must_use]
    pub fn files(&self) -> &[Node] {
        &self.0.files
    }

    /// Waits for the check. Same result as
    /// `get_semantic_diagnostics_without_no_emit_filtering`.
    #[must_use]
    pub fn wait(self) -> FxHashMap<Node, Vec<Diagnostic>> {
        let files = Arc::clone(&self.0.files);
        files
            .iter()
            .zip(self.0.wait())
            .map(|(&file, diags)| (file, sort_and_deduplicate_diagnostics(diags)))
            .collect()
    }
}

/// Sends the `get_semantic_diagnostics_without_no_emit_filtering` check of
/// `source_files` to the checkers of the current program and returns
/// without waiting (Go `collectCheckerDiagnosticsFromFiles` with
/// `getBindAndCheckDiagnosticsForFile`).
pub fn start_semantic_diagnostics_without_no_emit_filtering(
    source_files: &[Node],
) -> PendingSemanticDiagnostics {
    PendingSemanticDiagnostics(start_checker_group_do(source_files, |c, f| {
        get_bind_and_check_diagnostics_with_checker(&context::background(), c, f)
    }))
}

// Go: compiler/program.go:667 GetSuggestionDiagnostics
pub fn get_suggestion_diagnostics(source_file: Node) -> Vec<Diagnostic> {
    collect_checker_diagnostics_with(source_file, |c, f| {
        get_suggestion_diagnostics_with_checker(&context::background(), c, f)
    })
}

// Go: compiler/program.go:671 GetProgramDiagnostics
// PORT: the include processor diagnostics are part of the converted
// `ts_compiler` program diagnostics.
pub fn get_program_diagnostics() -> Vec<Diagnostic> {
    if let Some(go) = go_frontend() {
        let mut diagnostics = go.program.program_diagnostics.clone();
        diagnostics.extend(
            go.program
                .include_processor
                .get_diagnostics(go.program)
                .borrow_mut()
                .get_global_diagnostics(),
        );
        return sort_and_deduplicate_diagnostics(diagnostics);
    }
    let mut diagnostics =
        verify_options::without_reverified_option_diagnostics(&state().program_diagnostics);
    diagnostics.extend(verify_options::verify_compiler_options());
    sort_and_deduplicate_diagnostics(diagnostics)
}

// Go: compiler/program.go:678 GetIncludeProcessorDiagnostics
// PORT: the Rust loader reports no per-file include diagnostics; its
// diagnostics go to the program diagnostics.
pub fn get_include_processor_diagnostics(source_file: Node) -> Vec<Diagnostic> {
    if skip_type_checking(source_file, false) {
        return Vec::new();
    }
    let diagnostics = match &state().go {
        Some(go) => go.get_include_processor_diagnostics(source_file),
        None => Vec::new(),
    };
    let (filtered, _) = get_diagnostics_with_preceding_directives(source_file, diagnostics);
    filtered
}

// Go: compiler/program.go:686 SkipTypeChecking
pub fn skip_type_checking(source_file: Node, ignore_no_check: bool) -> bool {
    let options = &prog().options;
    let info = source_file_info(source_file);
    (!ignore_no_check && options.no_check.is_true())
        || options.skip_lib_check.is_true() && info.is_declaration_file
        || options.skip_default_lib_check.is_true() && is_source_file_default_library(&info.path)
        || is_source_from_project_reference(&info.path)
        || !can_include_bind_and_check_diagnostics(source_file)
}

// Go: compiler/program.go:694 canIncludeBindAndCheckDiagnostics
fn can_include_bind_and_check_diagnostics(source_file: Node) -> bool {
    let options = &prog().options;
    let info = source_file_info(source_file);
    if info.check_js_directive.is_some_and(|d| !d.enabled) {
        return false;
    }
    if info.script_kind == ScriptKind::TS
        || info.script_kind == ScriptKind::TSX
        || info.script_kind == ScriptKind::EXTERNAL
    {
        return true;
    }
    let is_js = info.script_kind == ScriptKind::JS || info.script_kind == ScriptKind::JSX;
    let is_check_js = is_js && is_check_js_enabled_for_file(source_file, options);
    let is_plain_js = is_plain_js_file(source_file, options.check_js);
    // By default, only type-check .ts, .tsx, Deferred, plain JS, checked JS and External
    // - plain JS: .js files with no // ts-check and checkJs: undefined
    // - check JS: .js files with either // ts-check or checkJs: true
    // - external: files that are added by plugins
    is_plain_js || is_check_js || info.script_kind == ScriptKind::DEFERRED
}

// Go: compiler/program.go:1290 GetGlobalDiagnostics
pub fn get_global_diagnostics() -> Vec<Diagnostic> {
    if prog().source_file_order.is_empty() {
        return Vec::new();
    }
    pool_get_global_diagnostics()
}

// Go: compiler/program.go:1302 GetDeclarationDiagnostics
// PORT: each file's work runs on the thread of the file's checker, where its
// emit resolver can reach that checker. Files of different checkers run in
// parallel; the results merge in file order.
pub fn get_declaration_diagnostics(source_file: Node) -> Vec<Diagnostic> {
    let files = if source_file.is_some() {
        vec![source_file]
    } else {
        source_files()
    };
    if worker_index().is_some() {
        let result = files
            .into_iter()
            .flat_map(get_declaration_diagnostics_for_file)
            .collect();
        return sort_and_deduplicate_diagnostics(result);
    }
    let receivers = files
        .into_iter()
        .map(|file| {
            send_thread_job(checker_index_for_file(file), move || {
                get_declaration_diagnostics_for_file(file)
            })
        })
        .collect();
    sort_and_deduplicate_diagnostics(wait_jobs(receivers).into_iter().flatten().collect())
}

/// `get_declaration_diagnostics` for one file without the wait: the job runs
/// on the file's checker thread while the caller sends more (see
/// `CheckerJob`). `CheckerJob::wait` gives the diagnostics before
/// `sort_and_deduplicate_diagnostics`.
pub fn send_declaration_diagnostics_job(source_file: Node) -> CheckerJob<Vec<Diagnostic>> {
    if worker_index().is_some() {
        return CheckerJob::Inline(get_declaration_diagnostics_for_file(source_file));
    }
    CheckerJob::Sent(send_thread_job(
        checker_index_for_file(source_file),
        move || get_declaration_diagnostics_for_file(source_file),
    ))
}

// Go: compiler/program.go:1394 getDeclarationDiagnosticsForFile
fn get_declaration_diagnostics_for_file(source_file: Node) -> Vec<Diagnostic> {
    if source_file_info(source_file).is_declaration_file {
        return Vec::new();
    }

    if let Some(cached) = declaration_diagnostic_cache().get(&source_file) {
        return cached.clone();
    }

    let host = new_emit_host(source_file);
    let diagnostics = get_declaration_diagnostics_worker(host, source_file);
    // Go `LoadOrStore`: keep the first stored value.
    declaration_diagnostic_cache()
        .entry(source_file)
        .or_insert(diagnostics)
        .clone()
}

/// Go `Program.declarationDiagnosticCache`, locked.
fn declaration_diagnostic_cache() -> std::sync::MutexGuard<'static, FxHashMap<Node, Vec<Diagnostic>>>
{
    state()
        .declaration_diagnostic_cache
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner)
}

// Go: compiler/emitter.go:506 getSourceFilesToEmit
// PORT: Go takes a `SourceFileMayBeEmittedHost`; the program functions are that host.
pub(crate) fn get_source_files_to_emit(
    target_source_file: Node,
    force_dts_emit: bool,
) -> Vec<Node> {
    let source_files = if target_source_file.is_some() {
        vec![target_source_file]
    } else {
        source_files()
    };
    source_files
        .into_iter()
        .filter(|&source_file| source_file_may_be_emitted(source_file, force_dts_emit))
        .collect()
}

// Go: compiler/emitter.go:518 isSourceFileNotJson
fn is_source_file_not_json(file: Node) -> bool {
    !is_json_source_file(file)
}

// Go: compiler/emitter.go:522 getDeclarationDiagnostics
// PORT: renamed from Go `getDeclarationDiagnostics`, because the exported
// `GetDeclarationDiagnostics` above already has the snake name.
fn get_declaration_diagnostics_worker(host: Rc<EmitHost>, file: Node) -> Vec<Diagnostic> {
    // TODO: use p.getSourceFilesToEmit cache
    let full_files: Vec<Node> = get_source_files_to_emit(file, false)
        .into_iter()
        .filter(|&f| is_source_file_not_json(f))
        .collect();
    if !full_files.iter().any(|&f| f == file) {
        return Vec::new();
    }
    // PORT: Go calls host.Options(), which returns host.program.Options()
    // (emitHost.go:107). The trait method borrows `host`, but the transformer
    // needs `&'static`, so read the program options directly.
    let options = options();
    let mut transform =
        crate::declarations::new_declaration_transformer(host.clone(), None, options, "", "");
    transform.transform_source_file_root(file);
    transform.get_diagnostics()
}

// Go: compiler/emitHost.go:33 emitHost
// NOTE: emitHost operations must be thread-safe
pub struct EmitHost {
    emit_resolver: Rc<dyn crate::printer::EmitResolver>,
    /// Pool index of the checker that owns the file being emitted.
    pub checker_index: usize,
}

// Go: compiler/emitHost.go:38 newEmitHost
// PORT: Go gets the file's checker and a `done` func that releases it. The
// checker is lent only for the `GetEmitResolver` call here; the resolver
// must reach its checker itself. Call it on the thread of the file's checker.
pub fn new_emit_host(file: Node) -> Rc<EmitHost> {
    let checker_index = checker_index_for_file(file);
    let emit_resolver: Rc<dyn crate::printer::EmitResolver> =
        with_checker_at(checker_index, Checker::get_emit_resolver);
    Rc::new(EmitHost {
        emit_resolver,
        checker_index,
    })
}

impl EmitHost {
    /// Go `host.GetEmitResolver()` without the trait object.
    #[must_use]
    pub fn emit_resolver(&self) -> Rc<dyn crate::printer::EmitResolver> {
        self.emit_resolver.clone()
    }
}

impl crate::frontend::outputpaths::OutputPathsHost for EmitHost {
    // Go: compiler/emitHost.go:110 emitHost.CommonSourceDirectory
    fn common_source_directory(&self) -> String {
        common_source_directory().to_string()
    }

    // Go: compiler/emitHost.go:109 emitHost.GetCurrentDirectory
    fn get_current_directory(&self) -> String {
        get_current_directory().to_string()
    }

    // Go: compiler/emitHost.go:112 emitHost.UseCaseSensitiveFileNames
    fn use_case_sensitive_file_names(&self) -> bool {
        use_case_sensitive_file_names()
    }
}

// PORT: Go `emitHost` also implements `modulespecifiers.ModuleSpecifierGenerationHost`
// (GetModeForUsageLocation, GetResolvedModuleFromModuleSpecifier,
// GetDefaultResolutionModeForFile, FileExists, GetGlobalTypingsCacheLocation,
// GetNearestAncestorDirectoryWithPackageJson, GetPackageJsonInfo,
// GetSourceOfProjectReferenceIfOutputIncluded, GetProjectReferenceFromSource,
// GetRedirectTargets, GetSymlinkCache, ResolveModuleName). That interface is
// not ported, so those methods are left out until it is.
impl crate::declarations::DeclarationEmitHost for EmitHost {
    // Go: compiler/emitHost.go:109 emitHost.GetCurrentDirectory
    fn get_current_directory(&self) -> String {
        get_current_directory().to_string()
    }

    // Go: compiler/emitHost.go:112 emitHost.UseCaseSensitiveFileNames
    fn use_case_sensitive_file_names(&self) -> bool {
        use_case_sensitive_file_names()
    }

    // Go: compiler/emitHost.go:103 emitHost.GetSourceFileFromReference
    fn get_source_file_from_reference(&self, origin: Node, r#ref: &FileReference) -> Node {
        get_source_file_from_reference(origin, r#ref)
    }

    // Go: compiler/emitHost.go:94 emitHost.GetOutputPathsFor
    fn get_output_paths_for(
        &self,
        file: Node,
        force_dts_paths: bool,
    ) -> Box<dyn crate::declarations::OutputPaths> {
        // TODO: cache
        Box::new(get_output_paths_for_source_file(
            file,
            self,
            force_dts_paths,
        ))
    }

    // Go: compiler/emitHost.go:99 emitHost.GetResolutionModeOverride
    fn get_resolution_mode_override(&self, node: Node) -> ResolutionMode {
        self.emit_resolver.get_resolution_mode_override(node)
    }

    // Go: compiler/emitHost.go:90 emitHost.GetEffectiveDeclarationFlags
    fn get_effective_declaration_flags(&self, node: Node, flags: ModifierFlags) -> ModifierFlags {
        self.emit_resolver
            .get_effective_declaration_flags(node, flags)
    }

    // Go: compiler/emitHost.go:124 emitHost.GetEmitResolver
    fn get_emit_resolver(&self) -> Rc<dyn crate::printer::EmitResolver> {
        self.emit_resolver.clone()
    }
}

impl crate::printer::EmitHost for EmitHost {
    // Go: compiler/emitHost.go:107 emitHost.Options
    fn options(&self) -> &CompilerOptions {
        options()
    }

    // Go: compiler/emitHost.go:108 emitHost.SourceFiles
    fn source_files(&self) -> Vec<Node> {
        source_files()
    }

    // Go: compiler/emitHost.go:112 emitHost.UseCaseSensitiveFileNames
    fn use_case_sensitive_file_names(&self) -> bool {
        use_case_sensitive_file_names()
    }

    // Go: compiler/emitHost.go:109 emitHost.GetCurrentDirectory
    fn get_current_directory(&self) -> String {
        get_current_directory().to_string()
    }

    // Go: compiler/emitHost.go:110 emitHost.CommonSourceDirectory
    fn common_source_directory(&self) -> String {
        common_source_directory().to_string()
    }

    // Go: compiler/emitHost.go:116 emitHost.IsEmitBlocked
    fn is_emit_blocked(&self, file: &str) -> bool {
        is_emit_blocked(file)
    }

    // Go: compiler/emitHost.go:120 emitHost.WriteFile
    // PORT: Go writes through the program host file system. Here the emit
    // caller always passes `EmitOptions.write_file`; without one the
    // write fails instead of touching the disk.
    fn write_file(&self, file_name: &str, _text: &str) -> Result<(), String> {
        Err(format!("no WriteFile callback for {file_name}"))
    }

    // Go: compiler/emitHost.go:58 emitHost.GetEmitModuleFormatOfFile
    fn get_emit_module_format_of_file(&self, file: Node) -> ModuleKind {
        get_emit_module_format_of_file(crate::emitter::emitter::parsed_source_file(file))
    }

    // Go: compiler/emitHost.go:124 emitHost.GetEmitResolver
    fn get_emit_resolver(&self) -> Rc<dyn crate::printer::EmitResolver> {
        self.emit_resolver.clone()
    }

    // Go: compiler/emitHost.go:128 emitHost.IsSourceFileFromExternalLibrary
    fn is_source_file_from_external_library(&self, file: Node) -> bool {
        is_source_file_from_external_library(file)
    }
}

// Go: compiler/program.go:1306 FilterNoEmitSemanticDiagnostics
pub fn filter_no_emit_semantic_diagnostics(
    mut diagnostics: Vec<Diagnostic>,
    options: &CompilerOptions,
) -> Vec<Diagnostic> {
    if !options.no_emit.is_true() {
        return diagnostics;
    }
    diagnostics.retain(|d| !d.skipped_on_no_emit());
    diagnostics
}

// Go: compiler/program.go:1315 getSemanticDiagnosticsWithChecker
pub fn get_semantic_diagnostics_with_checker(
    ctx: &Context,
    c: &mut Checker,
    source_file: Node,
) -> Vec<Diagnostic> {
    let mut diags = filter_no_emit_semantic_diagnostics(
        get_bind_and_check_diagnostics_with_checker(ctx, c, source_file),
        &prog().options,
    );
    diags.extend(get_include_processor_diagnostics(source_file));
    diags
}

// Go: compiler/program.go:1325 getBindAndCheckDiagnosticsWithChecker
pub fn get_bind_and_check_diagnostics_with_checker(
    ctx: &Context,
    file_checker: &mut Checker,
    source_file: Node,
) -> Vec<Diagnostic> {
    let compiler_options = &prog().options;
    if skip_type_checking(source_file, false) {
        return Vec::new();
    }
    // Checker creation forces binding, so bind diagnostics will be populated.
    bind_all();
    let mut diags = file_bind_data(source_file).bind_diagnostics.clone();
    diags.extend(file_checker.get_diagnostics_exported(ctx, source_file));

    let is_plain_js = is_plain_js_file(source_file, compiler_options.check_js);
    if is_plain_js {
        diags.retain(|d| is_plain_js_error(d.code));
        return diags;
    }

    let info = source_file_info(source_file);
    let is_js = info.script_kind == ScriptKind::JS || info.script_kind == ScriptKind::JSX;
    let is_check_js = is_js && is_check_js_enabled_for_file(source_file, compiler_options);
    if is_check_js {
        diags.extend(info.jsdoc_diagnostics.iter().cloned());
    }

    let (mut filtered, directives_by_line) =
        get_diagnostics_with_preceding_directives(source_file, diags);
    for directive in directives_by_line.values() {
        // Above we changed all used directive kinds to @ts-ignore, so any @ts-expect-error directives that
        // remain are unused and thus errors.
        if directive.kind == CommentDirectiveKind::EXPECT_ERROR {
            filtered.push(new_diagnostic(
                source_file,
                directive.loc,
                diag::Unused_ts_expect_error_directive,
                Vec::new(),
            ));
        }
    }
    filtered
}

// Go: compiler/program.go:1359 getDiagnosticsWithPrecedingDirectives
// PORT: Go returns a map by line; its iteration order is random and the
// caller sorts the result later. A BTreeMap gives a fixed order.
fn get_diagnostics_with_preceding_directives(
    source_file: Node,
    diags: Vec<Diagnostic>,
) -> (
    Vec<Diagnostic>,
    std::collections::BTreeMap<i32, CommentDirective>,
) {
    let mut directives_by_line = std::collections::BTreeMap::new();
    let info = source_file_info(source_file);
    if info.comment_directives.is_empty() {
        return (diags, directives_by_line);
    }
    // Build map of directives by line number
    for directive in &info.comment_directives {
        let line = get_ecma_line_of_position(source_file, directive.loc.pos());
        directives_by_line.insert(line, *directive);
    }
    let line_starts = get_ecma_line_starts(source_file);
    let text = source_file_text(source_file);
    let mut filtered = Vec::with_capacity(diags.len());
    for diagnostic in diags {
        let mut ignore_diagnostic = false;
        let mut line = compute_line_of_position(line_starts, diagnostic.pos) - 1;
        while line >= 0 {
            // If line contains a @ts-ignore or @ts-expect-error directive, ignore this diagnostic and change
            // the directive kind to @ts-ignore to indicate it was used.
            if let Some(directive) = directives_by_line.get_mut(&line) {
                ignore_diagnostic = true;
                directive.kind = CommentDirectiveKind::IGNORE;
                break;
            }
            // Stop searching backwards when we encounter a line that isn't blank or a comment.
            if !is_comment_or_blank_line(text, line_starts[line as usize] as usize) {
                break;
            }
            line -= 1;
        }
        if !ignore_diagnostic {
            filtered.push(diagnostic);
        }
    }
    (filtered, directives_by_line)
}

// Go: compiler/program.go:1410 getSuggestionDiagnosticsWithChecker
fn get_suggestion_diagnostics_with_checker(
    ctx: &Context,
    file_checker: &mut Checker,
    source_file: Node,
) -> Vec<Diagnostic> {
    if skip_type_checking(source_file, false) {
        return Vec::new();
    }
    // Checker creation forces binding, so bind suggestion diagnostics will be populated.
    bind_all();
    let mut diags = file_bind_data(source_file)
        .bind_suggestion_diagnostics
        .clone();
    diags.extend(file_checker.get_suggestion_diagnostics(ctx, source_file));
    diags
}

// Go: compiler/program.go:1422 isCommentOrBlankLine
fn is_comment_or_blank_line(text: &str, mut pos: usize) -> bool {
    let text = text.as_bytes();
    while pos < text.len() && (text[pos] == b' ' || text[pos] == b'\t') {
        pos += 1;
    }
    pos == text.len()
        || pos < text.len() && (text[pos] == b'\r' || text[pos] == b'\n')
        || pos + 1 < text.len() && text[pos] == b'/' && text[pos + 1] == b'/'
}

// Go: compiler/program.go:1431 SortAndDeduplicateDiagnostics
pub fn sort_and_deduplicate_diagnostics(mut diagnostics: Vec<Diagnostic>) -> Vec<Diagnostic> {
    diagnostics.sort_by(|a, b| compare_diagnostics(a, b).cmp(&0));
    compact_and_merge_related_infos(diagnostics)
}

// Go: compiler/program.go:1439 compactAndMergeRelatedInfos
// Remove duplicate diagnostics and, for sequences of diagnostics that differ only by related information,
// create a single diagnostic with sorted and deduplicated related information.
fn compact_and_merge_related_infos(diagnostics: Vec<Diagnostic>) -> Vec<Diagnostic> {
    if diagnostics.len() < 2 {
        return diagnostics;
    }
    let mut result = Vec::with_capacity(diagnostics.len());
    let mut i = 0;
    while i < diagnostics.len() {
        let d = &diagnostics[i];
        let mut n = 1;
        while i + n < diagnostics.len() && equal_diagnostics_no_related_info(d, &diagnostics[i + n])
        {
            n += 1;
        }
        let mut merged = d.clone();
        if n > 1 {
            let mut related_infos: Vec<Diagnostic> = diagnostics[i..i + n]
                .iter()
                .flat_map(|x| x.related_information.iter().cloned())
                .collect();
            // PORT: Go tests `relatedInfos != nil`; appending empty slices
            // keeps it nil, so an empty list means "leave d alone".
            if !related_infos.is_empty() {
                related_infos.sort_by(|a, b| compare_diagnostics(a, b).cmp(&0));
                related_infos.dedup_by(|b, a| equal_diagnostics(a, b));
                merged.set_related_info(related_infos);
            }
        }
        result.push(merged);
        i += n;
    }
    result
}

// Go: compiler/program.go:1470 LineCount
pub fn line_count() -> i32 {
    let mut count = 0;
    for file in prog().source_files() {
        count += get_ecma_line_starts(file.root).len() as i32;
    }
    count
}

// Go: compiler/program.go:1478 IdentifierCount
// PORT: the legacy loader does not count identifiers.
pub fn identifier_count() -> i32 {
    let Some(go) = go_frontend() else {
        unported!("IdentifierCount");
    };
    let mut count = 0;
    for file in go.program.source_files() {
        count += file.identifier_count;
    }
    count
}

// Go: compiler/program.go:1486 SymbolCount
// PORT: an unbound file (the program had syntactic errors) has the Go zero
// value.
pub fn symbol_count() -> i32 {
    let mut count: u32 = 0;
    for file in prog().source_files() {
        count += file
            .file_bind
            .get()
            .map_or(0, |data| data.symbol_count as u32);
    }
    for value in for_each_checker_parallel(|_, c| c.symbol_count) {
        count = count.wrapping_add(value);
    }
    count as i32
}

// Go: compiler/program.go:1499 TypeCount
pub fn type_count() -> i32 {
    let mut val: u32 = 0;
    for value in for_each_checker_parallel(|_, c| c.type_count) {
        val = val.wrapping_add(value);
    }
    val as i32
}

// Go: compiler/program.go:1507 InstantiationCount
pub fn instantiation_count() -> i32 {
    let mut val: u32 = 0;
    for value in for_each_checker_parallel(|_, c| c.total_instantiation_count) {
        val = val.wrapping_add(value);
    }
    val as i32
}

// Go: compiler/program.go:1750 GetDiagnosticsOfAnyProgram
// PORT: Go calls `program.GetGlobalDiagnostics` and
// `program.GetDeclarationDiagnostics` directly. They are callbacks here so a
// caller can guard them the same way as the bind and semantic callbacks.
pub fn get_diagnostics_of_any_program(
    file: Node,
    skip_no_emit_check_for_dts_diagnostics: bool,
    get_bind_diagnostics: &mut dyn FnMut(Node) -> Vec<Diagnostic>,
    get_semantic_diagnostics: &mut dyn FnMut(Node) -> Vec<Diagnostic>,
    get_global_diagnostics: &mut dyn FnMut() -> Vec<Diagnostic>,
    get_declaration_diagnostics: &mut dyn FnMut(Node) -> Vec<Diagnostic>,
) -> Vec<Diagnostic> {
    let options = &prog().options;
    let mut all_diagnostics = get_config_file_parsing_diagnostics();
    let config_file_parsing_diagnostics_length = all_diagnostics.len();

    all_diagnostics.extend(get_syntactic_diagnostics(file));

    // If we didn't have any syntactic errors, then also try getting the program (options),
    // global and semantic errors.
    if all_diagnostics.len() == config_file_parsing_diagnostics_length {
        all_diagnostics.extend(get_program_diagnostics());

        // Do binding early so we can track the time.
        get_bind_diagnostics(file);

        if options.list_files_only.is_false_or_unknown() {
            all_diagnostics.extend(get_global_diagnostics());

            if all_diagnostics.len() == config_file_parsing_diagnostics_length {
                all_diagnostics.extend(get_semantic_diagnostics(file));
                // Ask for the global diagnostics again (they were empty above); we may have found new during checking, e.g. missing globals.
                all_diagnostics.extend(get_global_diagnostics());
            }

            if (skip_no_emit_check_for_dts_diagnostics || options.no_emit.is_true())
                && options.get_emit_declarations()
                && all_diagnostics.len() == config_file_parsing_diagnostics_length
            {
                all_diagnostics.extend(get_declaration_diagnostics(file));
            }
        }
    }
    all_diagnostics
}

// Go: compiler/program.go plainJSErrors
// PORT: built on each call from the generated message statics (a static set
// cannot read them at compile time). It is only used for plain JS files.
fn is_plain_js_error(code: i32) -> bool {
    let messages: [&'static ts_diagnostics::Message; 91] = [
        // binder errors
        diag::Cannot_redeclare_block_scoped_variable_0,
        diag::A_module_cannot_have_multiple_default_exports,
        diag::Another_export_default_is_here,
        diag::The_first_export_default_is_here,
        diag::Identifier_expected_0_is_a_reserved_word_at_the_top_level_of_a_module,
        diag::Identifier_expected_0_is_a_reserved_word_in_strict_mode_Modules_are_automatically_in_strict_mode,
        diag::Identifier_expected_0_is_a_reserved_word_that_cannot_be_used_here,
        diag::X_constructor_is_a_reserved_word,
        diag::X_delete_cannot_be_called_on_an_identifier_in_strict_mode,
        diag::Code_contained_in_a_class_is_evaluated_in_JavaScript_s_strict_mode_which_does_not_allow_this_use_of_0_For_more_information_see_https_Colon_Slash_Slashdeveloper_mozilla_org_Slashen_US_Slashdocs_SlashWeb_SlashJavaScript_SlashReference_SlashStrict_mode,
        diag::Invalid_use_of_0_Modules_are_automatically_in_strict_mode,
        diag::Invalid_use_of_0_in_strict_mode,
        diag::A_label_is_not_allowed_here,
        diag::X_with_statements_are_not_allowed_in_strict_mode,
        // grammar errors
        diag::A_break_statement_can_only_be_used_within_an_enclosing_iteration_or_switch_statement,
        diag::A_break_statement_can_only_jump_to_a_label_of_an_enclosing_statement,
        diag::A_class_declaration_without_the_default_modifier_must_have_a_name,
        diag::A_class_member_cannot_have_the_0_keyword,
        diag::A_comma_expression_is_not_allowed_in_a_computed_property_name,
        diag::A_continue_statement_can_only_be_used_within_an_enclosing_iteration_statement,
        diag::A_continue_statement_can_only_jump_to_a_label_of_an_enclosing_iteration_statement,
        diag::A_default_clause_cannot_appear_more_than_once_in_a_switch_statement,
        diag::A_default_export_must_be_at_the_top_level_of_a_file_or_module_declaration,
        diag::A_definite_assignment_assertion_is_not_permitted_in_this_context,
        diag::A_destructuring_declaration_must_have_an_initializer,
        diag::A_get_accessor_cannot_have_parameters,
        diag::A_rest_element_cannot_contain_a_binding_pattern,
        diag::A_rest_element_cannot_have_a_property_name,
        diag::A_rest_element_cannot_have_an_initializer,
        diag::A_rest_element_must_be_last_in_a_destructuring_pattern,
        diag::A_rest_parameter_cannot_have_an_initializer,
        diag::A_rest_parameter_must_be_last_in_a_parameter_list,
        diag::A_rest_parameter_or_binding_pattern_may_not_have_a_trailing_comma,
        diag::A_return_statement_cannot_be_used_inside_a_class_static_block,
        diag::A_set_accessor_cannot_have_rest_parameter,
        diag::A_set_accessor_must_have_exactly_one_parameter,
        diag::An_export_declaration_can_only_be_used_at_the_top_level_of_a_module,
        diag::An_export_declaration_cannot_have_modifiers,
        diag::An_import_declaration_can_only_be_used_at_the_top_level_of_a_module,
        diag::An_import_declaration_cannot_have_modifiers,
        diag::An_object_member_cannot_be_declared_optional,
        diag::Argument_of_dynamic_import_cannot_be_spread_element,
        diag::Cannot_assign_to_private_method_0_Private_methods_are_not_writable,
        diag::Cannot_redeclare_identifier_0_in_catch_clause,
        diag::Catch_clause_variable_cannot_have_an_initializer,
        diag::Class_decorators_can_t_be_used_with_static_private_identifier_Consider_removing_the_experimental_decorator,
        diag::Classes_can_only_extend_a_single_class,
        diag::Classes_may_not_have_a_field_named_constructor,
        diag::Did_you_mean_to_use_a_Colon_An_can_only_follow_a_property_name_when_the_containing_object_literal_is_part_of_a_destructuring_pattern,
        diag::Duplicate_label_0,
        diag::Dynamic_imports_can_only_accept_a_module_specifier_and_an_optional_set_of_attributes_as_arguments,
        diag::X_for_await_loops_cannot_be_used_inside_a_class_static_block,
        diag::JSX_attributes_must_only_be_assigned_a_non_empty_expression,
        diag::JSX_elements_cannot_have_multiple_attributes_with_the_same_name,
        diag::JSX_expressions_may_not_use_the_comma_operator_Did_you_mean_to_write_an_array,
        diag::JSX_property_access_expressions_cannot_include_JSX_namespace_names,
        diag::Jump_target_cannot_cross_function_boundary,
        diag::Line_terminator_not_permitted_before_arrow,
        diag::Modifiers_cannot_appear_here,
        diag::Only_a_single_variable_declaration_is_allowed_in_a_for_in_statement,
        diag::Only_a_single_variable_declaration_is_allowed_in_a_for_of_statement,
        diag::Private_identifiers_are_not_allowed_outside_class_bodies,
        diag::Private_identifiers_are_only_allowed_in_class_bodies_and_may_only_be_used_as_part_of_a_class_member_declaration_property_access_or_on_the_left_hand_side_of_an_in_expression,
        diag::Property_0_is_not_accessible_outside_class_1_because_it_has_a_private_identifier,
        diag::Tagged_template_expressions_are_not_permitted_in_an_optional_chain,
        diag::The_left_hand_side_of_a_for_of_statement_may_not_be_async,
        diag::The_variable_declaration_of_a_for_in_statement_cannot_have_an_initializer,
        diag::The_variable_declaration_of_a_for_of_statement_cannot_have_an_initializer,
        diag::Trailing_comma_not_allowed,
        diag::Variable_declaration_list_cannot_be_empty,
        diag::X_0_and_1_operations_cannot_be_mixed_without_parentheses,
        diag::X_0_expected,
        diag::X_0_is_not_a_valid_meta_property_for_keyword_1_Did_you_mean_2,
        diag::X_0_list_cannot_be_empty,
        diag::X_0_modifier_already_seen,
        diag::X_0_modifier_cannot_appear_on_a_constructor_declaration,
        diag::X_0_modifier_cannot_appear_on_a_module_or_namespace_element,
        diag::X_0_modifier_cannot_appear_on_a_parameter,
        diag::X_0_modifier_cannot_appear_on_class_elements_of_this_kind,
        diag::X_0_modifier_cannot_be_used_here,
        diag::X_0_modifier_must_precede_1_modifier,
        diag::X_0_declarations_can_only_be_declared_inside_a_block,
        diag::X_0_declarations_must_be_initialized,
        diag::X_extends_clause_already_seen,
        diag::X_let_is_not_allowed_to_be_used_as_a_name_in_let_or_const_declarations,
        diag::Class_constructor_may_not_be_a_generator,
        diag::Class_constructor_may_not_be_an_accessor,
        diag::X_await_expressions_are_only_allowed_within_async_functions_and_at_the_top_levels_of_modules,
        diag::X_await_using_statements_are_only_allowed_within_async_functions_and_at_the_top_levels_of_modules,
        diag::Private_field_0_must_be_declared_in_an_enclosing_class,
        // Type errors
        diag::This_condition_will_always_return_0_since_JavaScript_compares_objects_by_reference_not_value,
    ];
    messages.iter().any(|m| m.code() as i32 == code)
}

// ---------------------------------------------------------------------------
// Output (Go diagnosticwriter/diagnosticwriter.go, non-pretty)
// ---------------------------------------------------------------------------

// Go: tspath ConvertToRelativePath
fn convert_to_relative_path(file_name: &str) -> String {
    if !ts_path::is_rooted_disk_path(file_name) {
        return file_name.to_string();
    }
    ts_path::relative_path_from_directory(
        get_current_directory(),
        file_name,
        state().case_sensitivity,
    )
}

// Go: diagnosticwriter/diagnosticwriter.go:467 WriteFormatDiagnostic
// PORT: Go writes to an io.Writer; this returns the text. A diagnostic whose
// file is not a program source file (the tsconfig) has a nil file here, so
// its location comes from the side table built at load time.
pub fn format_diagnostic(diagnostic: &Diagnostic) -> String {
    let mut output = String::new();
    if diagnostic.file.is_some() {
        let (line, character) =
            get_ecma_line_and_utf16_character_of_position(diagnostic.file, diagnostic.pos);
        let file_name = &source_file_info(diagnostic.file).file_name;
        output.push_str(&format!(
            "{}({},{}): ",
            convert_to_relative_path(file_name),
            line + 1,
            character + 1
        ));
    } else if let Some(location) = state().external_locations.iter().find(|l| {
        l.code == diagnostic.code
            && l.pos == diagnostic.pos
            && l.end == diagnostic.end
            && l.args == diagnostic.message_args
    }) {
        output.push_str(&format!(
            "{}({},{}): ",
            convert_to_relative_path(&location.file_name),
            location.line + 1,
            location.character + 1
        ));
    }
    output.push_str(&format!(
        "{} TS{}: ",
        diagnostic.category.name(),
        diagnostic.code
    ));
    write_flattened_diagnostic_message(&mut output, diagnostic, "\n");
    output.push('\n');
    output
}

// Go: diagnosticwriter/diagnosticwriter.go:461 WriteFormatDiagnostics
pub fn write_format_diagnostics(output: &mut String, diagnostics: &[Diagnostic]) {
    for diagnostic in diagnostics {
        output.push_str(&format_diagnostic(diagnostic));
    }
}

// Go: diagnosticwriter/diagnosticwriter.go:263 WriteFlattenedDiagnosticMessage
// PORT: this legacy writer has no Go `FormattingOptions`, so the locale is
// Go `locale.Default` and the text is English (see execute/tsc/diagnostics.rs
// `write_format_diagnostic`).
fn write_flattened_diagnostic_message(writer: &mut String, diagnostic: &Diagnostic, newline: &str) {
    writer.push_str(&diagnostic.localize(&crate::locale::DEFAULT));
    for chain in &diagnostic.message_chain {
        flatten_diagnostic_message_chain(writer, chain, newline, 1);
    }
}

// Go: diagnosticwriter/diagnosticwriter.go:271 flattenDiagnosticMessageChain
fn flatten_diagnostic_message_chain(
    writer: &mut String,
    chain: &Diagnostic,
    new_line: &str,
    level: usize,
) {
    writer.push_str(new_line);
    for _ in 0..level {
        writer.push_str("  ");
    }
    writer.push_str(&chain.localize(&crate::locale::DEFAULT));
    for child in &chain.message_chain {
        flatten_diagnostic_message_chain(writer, child, new_line, level + 1);
    }
}

// Emit support: run work on a file's checker thread without holding the checker.

/// Runs `f(file)` for each file on the thread of the file's checker, with
/// no checker borrowed, and returns the results in file order. The emit
/// resolver borrows its checker itself (`with_checker_at`), so emit runs
/// through this instead of `with_type_checker_for_file`.
pub fn run_on_checker_threads_for_files<R: Send + 'static>(
    files: &[Node],
    f: impl Fn(Node) -> R + Send + Sync + 'static,
) -> Vec<R> {
    if worker_index().is_some() {
        return files.iter().map(|&file| f(file)).collect();
    }
    let f = Arc::new(f);
    let receivers = files
        .iter()
        .map(|&file| {
            let f = Arc::clone(&f);
            send_thread_job(checker_index_for_file(file), move || f(file))
        })
        .collect();
    wait_jobs(receivers)
}

/// The pool index of the checker for `file` (Go `fileAssociations[file]`).
pub fn checker_index_of_file(file: Node) -> usize {
    checker_index_for_file(file)
}
