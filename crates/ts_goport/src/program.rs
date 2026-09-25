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

use crate::prelude::*;
use std::cell::OnceCell;
use std::ops::Deref;
use std::sync::{Arc, Mutex, OnceLock};
use ts_path::CaseSensitivity;
use ts_vfs::FileSystem;

mod go_frontend;
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
    pub resolved: ResolvedProjectReference,
}

/// Go `ast.SourceFile` fields set by the parser and the program.
///
/// The fields here are computed from the source text before the program is
/// installed. The fields that walk the tree (external module indicator,
/// imports, ...) are in `LateSourceFileInfo`, reached through `Deref`, and
/// are set by `install`.
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
    pub diagnostics: Vec<Diagnostic>,
    pub js_diagnostics: Vec<Diagnostic>,
    pub jsdoc_diagnostics: Vec<Diagnostic>,
    /// True when a JSDoc cache miss means "not parsed" (Go parses lazily).
    pub has_lazy_js_doc: bool,
    pub is_default_library: bool,
    pub meta_data: SourceFileMetaData,
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
    pub reparsed_clones: Vec<Node>,
    pub imports: Vec<Node>,
    pub module_augmentations: Vec<Node>,
    pub ambient_module_names: Vec<String>,
    pub uses_uri_style_node_core_modules: Tristate,
    /// Go `SourceFile.jsdocCache`: parsed JSDoc nodes by host node.
    pub jsdoc_cache: FxHashMap<Node, Vec<Node>>,
    post_bind: OnceLock<PostBindInfo>,
}

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
        let file = &prog().files[self.file_index];
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
/// queue of each worker. Only the loading thread has a pool.
struct CheckerPool {
    workers: Vec<std::sync::mpsc::Sender<Job>>,
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

/// Program-level state that `GoProgram` does not hold.
struct ProgramState {
    cwd: String,
    case_sensitivity: CaseSensitivity,
    fs: ts_vfs::OsFileSystem,
    file_by_path: FxHashMap<String, usize>,
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
    /// itself is in `GO_FRONTEND`, on the loading thread only.
    go: Option<go_frontend::GoSharedState>,
}

/// The program state of the process. Every thread reads it.
static STATE: OnceLock<&'static ProgramState> = OnceLock::new();

thread_local! {
    /// The Go frontend program. Only the thread that loaded the program has
    /// it: the frontend data is not thread-safe.
    static GO_FRONTEND: OnceCell<&'static go_frontend::GoFrontendState> = const { OnceCell::new() };
}

fn state() -> &'static ProgramState {
    STATE.get().copied().expect("program not loaded")
}

fn set_state(program_state: &'static ProgramState) {
    assert!(STATE.set(program_state).is_ok(), "program already loaded");
}

/// The Go frontend program, or None on the legacy path. Panics on a checker
/// worker thread, which must use the copies in `ProgramState::go`.
fn go_frontend() -> Option<&'static go_frontend::GoFrontendState> {
    state().go.as_ref()?;
    Some(GO_FRONTEND.with(|cell| {
        *cell
            .get()
            .expect("the Go frontend program is read on the loading thread only")
    }))
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
    if go_frontend::enabled() {
        return go_frontend::try_load_with(config_path, edit_options);
    }
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
        let info = build_early_info(
            index,
            source,
            &parser_flags,
            &options,
            &cwd,
            case_sensitivity,
            &fs,
        );
        file_by_path.insert(info.path.clone(), index);
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

    let source_file_order = (0..files.len()).collect();
    let program: &'static GoProgram = Box::leak(Box::new(GoProgram {
        program: Some(compiler_program),
        files,
        source_file_order,
        options,
        bound_symbols: OnceLock::new(),
    }));
    let program_state: &'static ProgramState = Box::leak(Box::new(ProgramState {
        cwd,
        case_sensitivity,
        fs,
        file_by_path,
        config_diagnostics,
        program_diagnostics,
        external_locations,
        resolved_modules: OnceLock::new(),
        common_source_directory: OnceLock::new(),
        file_associations: OnceLock::new(),
        declaration_diagnostic_cache: Mutex::new(FxHashMap::default()),
        go: None,
    }));
    set_state(program_state);
    install(program);
    Ok(program)
}

/// Installs `program` for the process (`core::set_prog`) and computes the
/// Go SourceFile fields that need the tree: Go `finishSourceFile`
/// (reparsed clones, external module indicator) and
/// `collectExternalModuleReferences`.
pub fn install(program: &'static GoProgram) {
    set_prog(program);
    for (index, file) in program.files.iter().enumerate() {
        let late = build_late_info(index, file);
        assert!(
            file.info.late.set(late).is_ok(),
            "SourceFileInfo installed twice"
        );
    }
}

// Go: compiler/program.go:445 BindSourceFiles
// PORT: Go binds files in parallel into per-file symbol tables. Here every
// file binds into the shared `prog().bound_symbols` arena, with the same
// initializer that `Checker::new` uses, so the first of the two to run binds.
// Files bind in parallel, each into its own arena (`bind_files_parallel`),
// and join the program arena in file order with the ids a serial bind gives.
pub fn bind_all() {
    let program = prog();
    program.bound_symbols.get_or_init(|| {
        let mut symbols = SymbolArena::new();
        bind_files_parallel(&mut symbols);
        for file in program.source_files() {
            bind_source_file(file.root, &mut symbols);
        }
        symbols
    });
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

/// One file bound on a bind thread, or None when binding it made
/// thread-local state or panicked.
type ParallelBind = (usize, Option<(BoundFile, SymbolArena)>);

/// Binds the program files on several threads, each file into its own
/// arena, and joins the arenas into `symbols` in file order. It stops at the
/// first file that made thread-local state while binding (for example a
/// lazy JSDoc parse) or panicked; `bind_all` binds that file and the rest
/// serially, which gives the same result as a serial bind of every file.
fn bind_files_parallel(symbols: &mut SymbolArena) {
    let files: Vec<Node> = prog().source_files().map(|file| file.root).collect();
    let threads = std::thread::available_parallelism()
        .map_or(1, std::num::NonZero::get)
        .min(files.len());
    if single_threaded()
        || threads < 2
        || prog()
            .source_files()
            .any(|file| file.file_bind.get().is_some())
    {
        return;
    }
    let unported = unported_report();
    let next = std::sync::atomic::AtomicUsize::new(0);
    let stop = std::sync::atomic::AtomicBool::new(false);
    let (sender, receiver) = std::sync::mpsc::channel::<ParallelBind>();
    let complete = std::thread::scope(|scope| {
        for _ in 0..threads {
            let seed = WorkerSeed::take();
            let (files, next, stop, sender) = (&files, &next, &stop, sender.clone());
            std::thread::Builder::new()
                .stack_size(CHECKER_STACK_SIZE)
                .spawn_scoped(scope, move || {
                    seed.install();
                    while !stop.load(std::sync::atomic::Ordering::Relaxed) {
                        let i = next.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                        let Some(&file) = files.get(i) else { break };
                        let before = bind_thread_fingerprint();
                        let result = std::panic::catch_unwind(|| {
                            let mut file_symbols = SymbolArena::new();
                            let bound = bind_source_file_detached(file, &mut file_symbols);
                            (bound, file_symbols)
                        })
                        .ok()
                        .filter(|_| bind_thread_fingerprint() == before);
                        let failed = result.is_none();
                        let _ = sender.send((i, result));
                        if failed {
                            break;
                        }
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
                let Some((mut bound, file_symbols)) = result else {
                    stop.store(true, std::sync::atomic::Ordering::Relaxed);
                    return false;
                };
                bound.remap(symbols.append_file_arena(file_symbols));
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
fn build_early_info(
    index: usize,
    source: &'static ts_compiler::SourceFile,
    parser_flags: &[NodeFlags],
    options: &CompilerOptions,
    cwd: &str,
    case_sensitivity: CaseSensitivity,
    fs: &ts_vfs::OsFileSystem,
) -> SourceFileInfo {
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

    let meta_data = load_source_file_meta_data(&file_name, options, fs);
    let _ = parser_flags;

    SourceFileInfo {
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
        diagnostics,
        // PORT: the Rust parser does not report Go `JSDiagnostics` or
        // `JSDocDiagnostics` separately; they stay empty.
        js_diagnostics: Vec::new(),
        jsdoc_diagnostics: Vec::new(),
        has_lazy_js_doc: script_kind == ScriptKind::JS || script_kind == ScriptKind::JSX,
        is_default_library: source.is_default_library,
        meta_data,
        trivia: crate::ast::go_view::TriviaRuns::compute(&source.parse.arena, text),
        late: OnceLock::new(),
    }
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

    let external_module_indicator = get_external_module_indicator(root, info, &prog().options);

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
        reparsed_clones,
        imports: refs.imports,
        module_augmentations: refs.module_augmentations,
        ambient_module_names: refs.ambient_module_names,
        uses_uri_style_node_core_modules: refs.uses_uri_style_node_core_modules,
        // PORT: JS files treat a cache miss as an unported lazy parse; TS
        // files get the eager Go entries.
        jsdoc_cache: if info.has_lazy_js_doc {
            FxHashMap::default()
        } else {
            crate::ast::build_jsdoc_cache(root)
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
fn get_external_module_indicator(
    file: Node,
    info: &SourceFileInfo,
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
    let (jsx, force) =
        get_external_module_indicator_options(&info.file_name, options, &info.meta_data);
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
// Program methods (Go compiler/program.go). The program is the installed
// `prog()`; these are free functions.
// PORT: Go `projectReferenceFileMapper.getCompilerOptionsForFile` returns the
// program options when there are no project references, which is always the
// case here.
// ---------------------------------------------------------------------------

fn file_info_by_path(path: &str) -> Option<&'static SourceFileInfo> {
    state()
        .file_by_path
        .get(path)
        .map(|&index| &prog().files[index].info)
}

/// Lazy JSDoc of `node` in `file` on the Go frontend path (Go
/// `SourceFile.resolveJSDoc`). None on the legacy path, where lazy JSDoc
/// parsing is not ported.
pub fn resolve_lazy_js_doc(file: Node, node: Node) -> Option<&'static [Node]> {
    state().go.as_ref().map(|go| go.resolve_js_doc(file, node))
}

// Go: compiler/program.go:122 FileExists
pub fn file_exists(path: &str) -> bool {
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
// PORT: project references are not loaded; there is never a reference.
pub fn get_project_reference_from_source(
    path: &str,
) -> Option<&'static SourceOutputAndProjectReference> {
    let _ = path;
    None
}

// Go: compiler/program.go:178 IsSourceFromProjectReference
pub fn is_source_from_project_reference(path: &str) -> bool {
    get_project_reference_from_source(path).is_some()
}

// Go: compiler/program.go:182 GetProjectReferenceFromOutputDts
// PORT: project references are not loaded; there is never a reference.
pub fn get_project_reference_from_output_dts(
    path: &str,
) -> Option<&'static SourceOutputAndProjectReference> {
    let _ = path;
    None
}

// Go: compiler/program.go:190 GetRedirectForResolution
// PORT: project references are not loaded; there is never a redirect.
pub fn get_redirect_for_resolution(file: Node) -> Option<&'static ResolvedProjectReference> {
    let _ = file;
    None
}

// Go: compiler/program.go:199 GetResolvedProjectReferences
pub fn get_resolved_project_references() -> Vec<&'static ResolvedProjectReference> {
    Vec::new()
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
pub fn get_resolved_module(
    file: Node,
    module_reference: &str,
    mode: ResolutionMode,
) -> Option<ResolvedModule> {
    if let Some(go) = &state().go {
        return go.get_resolved_module(file, module_reference, mode);
    }
    let program = prog();
    let go_file = &program.files[file.file_index()];
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
    Some(build_resolved_module(module_reference, &target.file_name))
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
    if !is_string_literal_like(module_specifier) {
        panic!("moduleSpecifier must be a StringLiteralLike");
    }
    let mode = get_mode_for_usage_location(file, module_specifier);
    get_resolved_module(file, module_specifier.text(), mode)
}

// Go: compiler/program.go:511 GetResolvedModules
// PORT: built on first use from each file's imports and module
// augmentations, keyed by file path, then (name, mode).
pub fn get_resolved_modules()
-> &'static IndexMap<String, IndexMap<(String, ResolutionMode), ResolvedModule>> {
    state().resolved_modules.get_or_init(|| {
        let mut result = IndexMap::new();
        for file in prog().source_files() {
            let mut in_file = IndexMap::new();
            let augmentations = file
                .info
                .module_augmentations
                .iter()
                .copied()
                .filter(|n| is_string_literal(*n));
            for specifier in file.info.imports.iter().copied().chain(augmentations) {
                let name = specifier.text().to_string();
                let mode = get_mode_for_usage_location(file.root, specifier);
                if in_file.contains_key(&(name.clone(), mode)) {
                    continue;
                }
                if let Some(resolved) = get_resolved_module(file.root, &name, mode) {
                    in_file.insert((name, mode), resolved);
                }
            }
            result.insert(file.info.path.clone(), in_file);
        }
        result
    })
}

// Go: compiler/program.go:1519 GetSourceFileMetaData
pub fn get_source_file_meta_data(path: &str) -> SourceFileMetaData {
    file_info_by_path(path)
        .map(|info| info.meta_data.clone())
        .unwrap_or_default()
}

// Go: compiler/program.go:1523 GetEmitModuleFormatOfFile
pub fn get_emit_module_format_of_file(source_file: Node) -> ModuleKind {
    let info = source_file_info(source_file);
    get_emit_module_format_of_file_worker(
        &info.file_name,
        &prog().options,
        &get_source_file_meta_data(&info.path),
    )
}

// Go: compiler/program.go:1527 GetEmitSyntaxForUsageLocation
pub fn get_emit_syntax_for_usage_location(source_file: Node, location: Node) -> ResolutionMode {
    let info = source_file_info(source_file);
    get_emit_syntax_for_usage_location_worker(
        &info.file_name,
        &get_source_file_meta_data(&info.path),
        location,
        &prog().options,
    )
}

// Go: compiler/program.go:1531 GetImpliedNodeFormatForEmit
pub fn get_implied_node_format_for_emit(source_file: Node) -> ResolutionMode {
    let info = source_file_info(source_file);
    get_implied_node_format_for_emit_worker(
        &info.file_name,
        prog().options.get_emit_module_kind(),
        &get_source_file_meta_data(&info.path),
    )
}

// Go: compiler/program.go:1535 GetModeForUsageLocation
pub fn get_mode_for_usage_location(source_file: Node, location: Node) -> ResolutionMode {
    let info = source_file_info(source_file);
    get_mode_for_usage_location_worker(
        &info.file_name,
        &get_source_file_meta_data(&info.path),
        location,
        &prog().options,
    )
}

// Go: compiler/program.go:1539 GetDefaultResolutionModeForFile
pub fn get_default_resolution_mode_for_file(source_file: Node) -> ResolutionMode {
    let info = source_file_info(source_file);
    get_default_resolution_mode_for_file_worker(
        &info.file_name,
        &get_source_file_meta_data(&info.path),
        &prog().options,
    )
}

// Go: compiler/program.go:1543 IsSourceFileDefaultLibrary
pub fn is_source_file_default_library(path: &str) -> bool {
    file_info_by_path(path).is_some_and(|info| info.is_default_library)
}

// Go: compiler/program.go:1562 CommonSourceDirectory
pub fn common_source_directory() -> &'static str {
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
// PORT: Go records files found while searching node_modules. The Rust
// loader does not; a path inside node_modules stands in for it.
pub fn is_source_file_from_external_library(file: Node) -> bool {
    source_file_info(file).path.contains("/node_modules/")
}

// Go: compiler/program.go:1927 SourceFileMayBeEmitted
pub fn source_file_may_be_emitted(source_file: Node, force_dts_emit: bool) -> bool {
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
    let path = ts_path::canonicalize(file_name, get_current_directory(), state().case_sensitivity);
    get_source_file_by_path(&path)
}

// Go: compiler/program.go:1812 GetSourceFileByPath
pub fn get_source_file_by_path(path: &str) -> Node {
    state()
        .file_by_path
        .get(path)
        .map_or(Node::NIL, |&index| prog().files[index].root)
}

// Go: compiler/program.go:1797 GetSourceFileForResolvedModule
// PORT: the legacy loader has no parse-file redirects, so only the Go
// frontend program has the redirect fallback.
pub fn get_source_file_for_resolved_module(file_name: &str) -> Node {
    let file = get_source_file(file_name);
    if file.is_nil()
        && let Some(redirect) = state()
            .go
            .as_ref()
            .and_then(|go| go.get_parse_file_redirect(file_name))
    {
        return get_source_file(redirect);
    }
    file
}

// Go: compiler/program.go:157 GetRedirectTargets
// PORT: the legacy loader does not deduplicate packages, so it has no
// redirect targets.
pub fn get_redirect_targets(path: &crate::frontend::tspath::Path) -> Vec<String> {
    state()
        .go
        .as_ref()
        .map(|go| go.get_redirect_targets(&path.0))
        .unwrap_or_default()
}

// Go: compiler/program.go:226 GetSourceFileFromReference
// PORT: the Go frontend program has the port. The legacy loader has none.
pub fn get_source_file_from_reference(origin: Node, r: &FileReference) -> Node {
    let Some(go) = &state().go else {
        unported!("Program.GetSourceFileFromReference")
    };
    go.get_source_file_from_reference(origin, r)
}

// Go: outputpaths/outputpaths.go:42 GetOutputPathsFor, called by
// compiler/emitHost.go:94 emitHost.GetOutputPathsFor with the program options.
// PORT: Go passes the emit host as the `OutputPathsHost`. Its methods forward
// to the program, so the shared copy of the Go frontend program data is the
// host here. The legacy loader has no common source directory copy. It is
// private so it does not clash with the frontend `get_output_paths_for` in
// the frontend prelude.
fn get_output_paths_for(
    file: Node,
    force_dts_paths: bool,
) -> crate::frontend::outputpaths::OutputPaths {
    let Some(go) = &state().go else {
        unported!("outputpaths.GetOutputPathsFor")
    };
    let info = source_file_info(file);
    crate::frontend::outputpaths::get_output_paths_for_file(
        &info.file_name,
        info.script_kind,
        options(),
        go,
        force_dts_paths,
    )
}

// Go: compiler/program.go:1916 GetJSXRuntimeImportSpecifier
// Go: compiler/fileloader.go:550 (the value the loader records)
// PORT: on the Go frontend the loader records the value and its synthetic
// import (Go `createSyntheticImport`). On the legacy path the specifier is
// nil and callers fall back to their own location node.
pub fn get_jsx_runtime_import_specifier(path: &str) -> (String, Node) {
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
    let file = prog().files[info.file_index].root;
    let jsx_import = get_jsx_runtime_import(&get_jsx_implicit_import_base(options, file), options);
    if jsx_import.is_empty() {
        return (String::new(), Node::NIL);
    }
    (jsx_import, Node::NIL)
}

// Go: compiler/program.go:1923 GetImportHelpersImportSpecifier
// Go: compiler/fileloader.go:541 (the value the loader records)
// PORT: the Go frontend loader records the synthetic import. On the legacy
// path `createSyntheticImport` is not ported.
pub fn get_import_helpers_import_specifier(path: &str) -> Node {
    if let Some(go) = &state().go {
        return go.get_import_helpers_import_specifier(path);
    }
    let Some(info) = file_info_by_path(path) else {
        return Node::NIL;
    };
    let file = prog().files[info.file_index].root;
    if needs_import_helpers_import_specifier(file) {
        unported!("createSyntheticImport")
    }
    Node::NIL
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
    /// The checker pool of the loading thread.
    static POOL: RefCell<Option<CheckerPool>> = const { RefCell::new(None) };
    /// The checker of a worker thread.
    static WORKER_CHECKER: RefCell<Option<Checker>> = const { RefCell::new(None) };
    /// The pool index of the checker of a worker thread.
    static WORKER_INDEX: std::cell::Cell<Option<usize>> = const { std::cell::Cell::new(None) };
}

/// The thread-local state that a checker worker starts from: the synthetic
/// nodes, ids and lazy JSDoc of the loading thread when the pool is made.
struct WorkerSeed {
    synthetic: SyntheticSeed,
    ids: IdSeed,
    lazy_jsdoc: FxHashMap<Node, &'static [Node]>,
}

impl WorkerSeed {
    fn take() -> Self {
        Self {
            synthetic: synthetic_seed(),
            ids: id_seed(),
            lazy_jsdoc: go_frontend::lazy_jsdoc_seed(),
        }
    }

    fn install(self) {
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
    let mut file_associations = vec![0; program.files.len()];
    for (i, &file_index) in program.source_file_order.iter().enumerate() {
        file_associations[file_index] = i % count;
    }
    assert!(
        state().file_associations.set(file_associations).is_ok(),
        "checker pool made twice"
    );
    let workers = (0..count)
        .map(|index| {
            let (sender, receiver) = std::sync::mpsc::channel::<Job>();
            let seed = WorkerSeed::take();
            std::thread::Builder::new()
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
                })
                .expect("cannot start a checker thread");
            sender
        })
        .collect();
    CheckerPool { workers }
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
    POOL.with(|pool| {
        let mut pool = pool.borrow_mut();
        let pool = pool.get_or_insert_with(create_checkers);
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

/// The pool index of this thread's checker, or None off the worker threads.
fn worker_index() -> Option<usize> {
    WORKER_INDEX.with(std::cell::Cell::get)
}

/// The checker index of `file` (Go `fileAssociations[file]`).
fn checker_index_for_file(file: Node) -> usize {
    if state().file_associations.get().is_none() {
        POOL.with(|pool| {
            pool.borrow_mut().get_or_insert_with(create_checkers);
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
    let mut diagnostics = vec![Vec::new(); files.len()];
    for (i, result) in wait_jobs(receivers).into_iter().flatten() {
        diagnostics[i] = result;
    }
    diagnostics
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
            .chain(&info.js_diagnostics)
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
pub fn get_semantic_diagnostics(source_file: Node) -> Vec<Diagnostic> {
    collect_checker_diagnostics_with(source_file, get_semantic_diagnostics_with_checker)
}

// Go: compiler/program.go:658 GetSemanticDiagnosticsWithoutNoEmitFiltering
pub fn get_semantic_diagnostics_without_no_emit_filtering(
    source_files: &[Node],
) -> FxHashMap<Node, Vec<Diagnostic>> {
    let all_diags = collect_checker_diagnostics_from_files(
        source_files,
        get_bind_and_check_diagnostics_with_checker,
    );
    source_files
        .iter()
        .zip(all_diags)
        .map(|(&file, diags)| (file, sort_and_deduplicate_diagnostics(diags)))
        .collect()
}

// Go: compiler/program.go:667 GetSuggestionDiagnostics
pub fn get_suggestion_diagnostics(source_file: Node) -> Vec<Diagnostic> {
    collect_checker_diagnostics_with(source_file, get_suggestion_diagnostics_with_checker)
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
fn get_source_files_to_emit(target_source_file: Node, force_dts_emit: bool) -> Vec<Node> {
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
}

// Go: compiler/emitHost.go:38 newEmitHost
// PORT: Go gets the file's checker and a `done` func that releases it. The
// checker is lent only for the `GetEmitResolver` call here; the resolver
// must reach its checker itself.
fn new_emit_host(file: Node) -> Rc<EmitHost> {
    let emit_resolver: Rc<dyn crate::printer::EmitResolver> =
        with_checker_at(checker_index_for_file(file), Checker::get_emit_resolver);
    Rc::new(EmitHost { emit_resolver })
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
        Box::new(get_output_paths_for(file, force_dts_paths))
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
    fn is_emit_blocked(&self, _file: &str) -> bool {
        unported!("Program.IsEmitBlocked")
    }

    // Go: compiler/emitHost.go:120 emitHost.WriteFile
    fn write_file(&self, _file_name: &str, _text: &str) -> Result<(), String> {
        unported!("emitHost.WriteFile")
    }

    // Go: compiler/emitHost.go:58 emitHost.GetEmitModuleFormatOfFile
    fn get_emit_module_format_of_file(&self, file: Node) -> ModuleKind {
        get_emit_module_format_of_file(file)
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

// Go: compiler/program.go:1615 EmitResult
// PORT: `EmittedFiles` and `SourceMaps` are left out. Writing outputs is not
// ported, so they would always be empty.
#[derive(Clone, Debug, Default)]
pub struct EmitResult {
    pub emit_skipped: bool,
    /// Contains declaration emit diagnostics
    pub diagnostics: Vec<Diagnostic>,
}

// Go: compiler/program.go:1628 Emit
// PORT: of Go `EmitOptions`, only `TargetSourceFile` is a parameter.
// `EmitOnly` is always `EmitAll`, and `WriteFile` is not used, because
// writing outputs is not ported (see `Emitter::emit_js_file`). Go queues one
// emitter per file on a work group. Here `emit_file` runs for each file on
// the thread of the file's checker, where the emit resolver can reach that
// checker, so a caller can guard each file there. Pass `emit_source_file`
// for the Go behavior. Call it off the checker threads, like the other
// program-wide functions.
pub fn emit(target_source_file: Node, emit_file: fn(Node) -> EmitResult) -> EmitResult {
    // PORT: `options.EmitOnly != EmitOnlyForcedDts` is always true.
    if let Some(result) = handle_no_emit_on_error(target_source_file) {
        return result;
    }

    let source_files = get_source_files_to_emit(target_source_file, false);
    let receivers = source_files
        .into_iter()
        .map(|file| send_thread_job(checker_index_for_file(file), move || emit_file(file)))
        .collect();
    let results = wait_jobs(receivers);

    // collect results from emit, preserving input order
    combine_emit_results(results)
}

// Go: compiler/program.go:1663 (the work that Program.Emit queues for each file)
pub fn emit_source_file(source_file: Node) -> EmitResult {
    let host = new_emit_host(source_file);
    let paths = get_output_paths_for(source_file, false);
    let mut emitter = Emitter {
        host,
        source_file,
        emit_result: EmitResult::default(),
        emitter_diagnostics: DiagnosticsCollection::default(),
    };
    emitter.emit(&paths);
    emitter.emit_result
}

// Go: compiler/program.go:1692 CombineEmitResults
pub fn combine_emit_results(results: Vec<EmitResult>) -> EmitResult {
    let mut result = EmitResult::default();
    for emit_result in results {
        if emit_result.emit_skipped {
            result.emit_skipped = true;
        }
        result.diagnostics.extend(emit_result.diagnostics);
    }
    result
}

// Go: compiler/program.go:1728 HandleNoEmitOnError
// PORT: Go takes the program; the program functions are that program.
pub fn handle_no_emit_on_error(file: Node) -> Option<EmitResult> {
    if !options().no_emit_on_error.is_true() {
        return None; // No emit on error is not set, so we can proceed with emitting
    }

    let diagnostics = get_diagnostics_of_any_program(
        file,
        true,
        &mut get_bind_diagnostics,
        &mut get_semantic_diagnostics,
        &mut get_global_diagnostics,
        &mut get_declaration_diagnostics,
    );
    if diagnostics.is_empty() {
        return None; // No diagnostics, so we can proceed with emitting
    }
    Some(EmitResult {
        diagnostics,
        emit_skipped: true,
    })
}

// Go: compiler/emitter.go:33 emitter
// PORT: `writer`, `paths` and `tr` are left out. The printer and output
// writing are not ported, and the paths are passed to `emit`. `emitOnly` is
// always `EmitAll`.
struct Emitter {
    host: Rc<EmitHost>,
    source_file: Node,
    emit_result: EmitResult,
    emitter_diagnostics: DiagnosticsCollection,
}

impl Emitter {
    // Go: compiler/emitter.go:45 emitter.emit
    fn emit(&mut self, paths: &crate::frontend::outputpaths::OutputPaths) {
        self.emit_js_file(
            self.source_file,
            paths.js_file_path(),
            paths.source_map_file_path(),
        );
        self.emit_declaration_file(
            self.source_file,
            paths.declaration_file_path(),
            paths.declaration_map_path(),
        );
        self.emit_result.diagnostics = self.emitter_diagnostics.get_diagnostics();
    }

    // Go: compiler/emitter.go:69 emitter.runDeclarationTransformers
    // PORT: Go returns the transformed file too. Only the printer reads it,
    // and the printer is not ported, so only the diagnostics are returned.
    fn run_declaration_transformers(
        &self,
        emit_context: Rc<crate::printer::EmitContext>,
        source_file: Node,
        declaration_file_path: &str,
        declaration_map_path: &str,
    ) -> Vec<Diagnostic> {
        // Go: compiler/emitter.go:54 getDeclarationTransformers (one transformer)
        let mut transform = crate::declarations::new_declaration_transformer(
            self.host.clone(),
            Some(emit_context),
            options(),
            declaration_file_path,
            declaration_map_path,
        );
        transform.transform_source_file_root(source_file);
        transform.get_diagnostics()
    }

    // Go: compiler/emitter.go:173 emitter.emitJSFile
    fn emit_js_file(&mut self, source_file: Node, js_file_path: &str, _source_map_file_path: &str) {
        let options = options();

        // PORT: `emitOnly` is always `EmitAll`.
        if source_file.is_nil() || js_file_path.is_empty() {
            return;
        }

        if options.no_emit == Tristate::True
            || crate::printer::EmitHost::is_emit_blocked(&*self.host, js_file_path)
        {
            self.emit_result.emit_skipped = true;
            return;
        }

        // PORT: the script transformers and the printer are not ported.
        unported!("emitter.emitJSFile")
    }

    // Go: compiler/emitter.go:213 emitter.emitDeclarationFile
    fn emit_declaration_file(
        &mut self,
        source_file: Node,
        declaration_file_path: &str,
        declaration_map_path: &str,
    ) {
        let options = options();

        // PORT: `emitOnly` is always `EmitAll`, never `EmitOnlyJs`.
        if source_file.is_nil() || declaration_file_path.is_empty() {
            return;
        }

        // Go: printer.GetEmitContext takes a clean context from a pool.
        let emit_context = crate::printer::new_emit_context();
        let diags = self.run_declaration_transformers(
            emit_context,
            source_file,
            declaration_file_path,
            declaration_map_path,
        );
        let decl_blocked = !diags.is_empty();

        for elem in diags {
            // Add declaration transform diagnostics to emit diagnostics
            self.emitter_diagnostics.add(elem);
        }

        // PORT: `emitOnly` is never `EmitOnlyForcedDts`.
        if options.no_emit == Tristate::True
            || crate::printer::EmitHost::is_emit_blocked(&*self.host, declaration_file_path)
        {
            self.emit_result.emit_skipped = true;
            return;
        }

        if decl_blocked {
            self.emit_result.emit_skipped = true;
            return;
        }

        // PORT: the declaration printer and output writing are not ported.
        unported!("emitter.emitDeclarationFile")
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
    c: &mut Checker,
    source_file: Node,
) -> Vec<Diagnostic> {
    let mut diags = filter_no_emit_semantic_diagnostics(
        get_bind_and_check_diagnostics_with_checker(c, source_file),
        &prog().options,
    );
    diags.extend(get_include_processor_diagnostics(source_file));
    diags
}

// Go: compiler/program.go:1325 getBindAndCheckDiagnosticsWithChecker
pub fn get_bind_and_check_diagnostics_with_checker(
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
    diags.extend(file_checker.get_diagnostics_exported(source_file));

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
        let mut line = compute_line_of_position(&line_starts, diagnostic.pos) - 1;
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
    diags.extend(file_checker.get_suggestion_diagnostics(source_file));
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
fn write_flattened_diagnostic_message(writer: &mut String, diagnostic: &Diagnostic, newline: &str) {
    writer.push_str(&diagnostic.localize());
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
    writer.push_str(&chain.localize());
    for child in &chain.message_chain {
        flatten_diagnostic_message_chain(writer, child, new_line, level + 1);
    }
}
