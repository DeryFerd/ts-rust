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
use crate::frontend::parser::ParsedSourceFile;
use crate::frontend::tsoptions::{ParseConfigHost, get_parsed_command_line_of_config_file};
use crate::frontend::tspath::Path as GoPath;
use crate::frontend::vfs::{Fs, osvfs_fs};
use std::rc::Rc;

/// Go frontend data that the program functions dispatch to.
pub(super) struct GoFrontendState {
    pub(super) program: &'static NewProgram,
    /// Parsed program files by file index (store id).
    pub(super) parsed: FxHashMap<usize, Rc<ParsedSourceFile>>,
    /// Go `SourceFile.jsdocCache` entries added by lazy JSDoc parses.
    /// PORT: the parsed file is shared and read only, so the lazy entries
    /// live here. The slices are leaked to give `NodeSlice` a static borrow.
    pub(super) lazy_jsdoc: RefCell<FxHashMap<Node, &'static [Node]>>,
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
            node_bind: OnceCell::new(),
            file_bind: OnceCell::new(),
            flow_nodes: OnceCell::new(),
        });
    }

    let program: &'static GoProgram = Box::leak(Box::new(GoProgram {
        program: None,
        files,
        source_file_order,
        options,
        bound_symbols: OnceCell::new(),
    }));
    let program_state: &'static ProgramState = Box::leak(Box::new(ProgramState {
        cwd,
        case_sensitivity,
        fs: legacy_fs,
        file_by_path,
        config_diagnostics: Vec::new(),
        program_diagnostics: Vec::new(),
        external_locations: Vec::new(),
        resolved_modules: OnceCell::new(),
        common_source_directory: OnceCell::new(),
        pool: RefCell::new(None),
        declaration_diagnostic_cache: RefCell::new(FxHashMap::default()),
        go: Some(GoFrontendState {
            program: new_program,
            parsed,
            lazy_jsdoc: RefCell::new(FxHashMap::default()),
        }),
    }));
    STATE.with(|cell| {
        assert!(cell.set(program_state).is_ok(), "program already loaded");
    });
    set_prog(program);
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
        late: OnceCell::new(),
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
        post_bind: OnceCell::new(),
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
        late: OnceCell::new(),
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
        post_bind: OnceCell::new(),
    };
    assert!(info.late.set(late).is_ok());
    info
}

impl GoFrontendState {
    // Go: ast/ast.go:2614 (*SourceFile).resolveJSDoc (slow path; the caller
    // has checked the parser cache).
    pub(super) fn resolve_js_doc(&self, file: Node, node: Node) -> &'static [Node] {
        if let Some(jsdocs) = self.lazy_jsdoc.borrow().get(&node) {
            return jsdocs;
        }
        let parsed = self.parsed_file(file);
        let jsdocs: &'static [Node] = Box::leak(
            crate::frontend::parser::parse_js_doc_for_node(
                &parsed.parse_options,
                parsed.text,
                parsed.script_kind,
                node,
            )
            .into_boxed_slice(),
        );
        self.lazy_jsdoc.borrow_mut().insert(node, jsdocs);
        jsdocs
    }

    /// The parsed program file of `file`.
    pub(super) fn parsed_file(&self, file: Node) -> &Rc<ParsedSourceFile> {
        self.parsed
            .get(&file.file_index())
            .expect("not a Go frontend program file")
    }
}
