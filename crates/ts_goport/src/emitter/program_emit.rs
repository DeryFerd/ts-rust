//! Port of the emit parts of Go `compiler/program.go` (`Emit`,
//! `CombineEmitResults`, `HandleNoEmitOnError`, the emit option and result
//! types), the emit host of `compiler/emitHost.go`, and
//! `outputpaths.GetOutputPathsFor` for a program source file.

use crate::prelude::*;

use std::sync::Arc;

use super::emitter::{EmitOnly, Emitter};
use crate::frontend::outputpaths::{
    OutputPathsHost, get_declaration_emit_output_file_path, get_output_extension,
    get_source_file_path_in_new_dir, get_source_map_file_path,
};
use crate::frontend::tspath::{
    ComparePathsOptions, compare_paths, file_extension_is_one_of, get_canonical_file_name,
    get_directory_path, has_extension, remove_file_extension, resolve_path,
};
use crate::sourcemap::generator::RawSourceMap;

// Go: compiler/program.go:1600 WriteFileData
// PORT: Go `BuildInfo any` is left out: `.tsbuildinfo` is not emitted.
#[derive(Clone, Debug, Default)]
pub struct WriteFileData {
    pub source_map_url_pos: i32,
    pub diagnostics: Vec<Diagnostic>,
    pub skipped_dts_write: bool,
}

// Go: compiler/program.go:1607 WriteFile
// PORT: Go `error` is `Result<(), String>`. Emit runs on the checker
// threads, so the callback is shared and thread safe. The callback may set
// `skipped_dts_write`.
pub type WriteFile =
    Arc<dyn Fn(&str, &str, &mut WriteFileData) -> Result<(), String> + Send + Sync>;

// Go: compiler/program.go:1609 EmitOptions
#[derive(Clone, Default)]
pub struct EmitOptions {
    /// Single file to emit. If nil, emits all files
    pub target_source_file: Node,
    pub emit_only: EmitOnly,
    pub write_file: Option<WriteFile>,
}

// Go: compiler/program.go:1615 EmitResult
#[derive(Clone, Debug, Default)]
pub struct EmitResult {
    pub emit_skipped: bool,
    /// Contains declaration emit diagnostics
    pub diagnostics: Vec<Diagnostic>,
    /// Array of files the compiler wrote to disk
    pub emitted_files: Vec<String>,
    /// Array of sourceMapData if compiler emitted sourcemaps
    pub source_maps: Vec<SourceMapEmitResult>,
}

// Go: compiler/program.go:1622 SourceMapEmitResult
#[derive(Clone, Debug, Default)]
pub struct SourceMapEmitResult {
    /// Input source file (which one can use on program to get the file), 1:1 mapping with the sourceMap.sources list
    pub input_source_file_names: Vec<String>,
    pub source_map: RawSourceMap,
    pub generated_file: String,
}

// Go: compiler/program.go:1628 Program.Emit
// PORT: Go queues one emit per file on a work group and takes a writer from
// a pool. Each file's emit runs on the thread of its checker (the emit
// resolver reaches that checker there), and the results combine in file
// order. Each emit makes its own text writer.
pub fn emit(options: EmitOptions) -> EmitResult {
    if options.emit_only != EmitOnly::ForcedDts {
        if let Some(result) = handle_no_emit_on_error(options.target_source_file) {
            return result;
        }
    }

    let source_files = get_source_files_to_emit_for(
        options.target_source_file,
        options.emit_only == EmitOnly::ForcedDts,
    );
    let emit_only = options.emit_only;
    let write_file = options.write_file.clone();
    let results = run_on_checker_threads(&source_files, move |source_file| {
        emit_source_file(source_file, emit_only, write_file.clone())
    });

    // collect results from emit, preserving input order
    combine_emit_results(results)
}

/// The body of the Go `wg.Queue` closure in `Program.Emit`.
fn emit_source_file(
    source_file: Node,
    emit_only: EmitOnly,
    write_file: Option<WriteFile>,
) -> EmitResult {
    let host = new_emit_host(source_file);
    let new_line = options().new_line.get_new_line_character();
    let writer: Rc<RefCell<dyn EmitTextWriter>> =
        Rc::new(RefCell::new(new_text_writer(new_line, 0)));
    writer.borrow_mut().clear();
    let paths = get_output_paths_for(
        source_file,
        options(),
        host.as_ref(),
        emit_only == EmitOnly::ForcedDts,
    );
    let mut emitter = Emitter {
        host,
        emit_only,
        emitter_diagnostics: DiagnosticsCollection::default(),
        writer: Some(writer),
        paths,
        source_file,
        emit_result: EmitResult::default(),
        write_file,
    };
    emitter.emit();
    emitter.writer = None;
    emitter.emit_result
}

/// Runs `f` for each file on the thread of the file's checker and returns
/// the results in file order.
// PORT: Go `core.NewWorkGroup` plus `newEmitHost(ctx, p, sourceFile)`, which
// borrows the file's checker. The checker pool lives in program.rs, and
// program.rs has no public way to run a job on a checker thread without
// holding that checker. See the crossFile note for the needed function.
fn run_on_checker_threads<R: Send + 'static>(
    files: &[Node],
    f: impl Fn(Node) -> R + Send + Sync + 'static,
) -> Vec<R> {
    crate::program::run_on_checker_threads_for_files(files, f)
}

/// The pool index of the checker for `file` (Go `fileAssociations[file]`).
fn checker_index_of_file(file: Node) -> usize {
    crate::program::checker_index_of_file(file)
}

// Go: compiler/program.go:1690 CombineEmitResults
pub fn combine_emit_results(results: Vec<EmitResult>) -> EmitResult {
    let mut result = EmitResult::default();
    for emit_result in results {
        if emit_result.emit_skipped {
            result.emit_skipped = true;
        }
        result.diagnostics.extend(emit_result.diagnostics);
        result.emitted_files.extend(emit_result.emitted_files);
        result.source_maps.extend(emit_result.source_maps);
    }
    result
}

// Go: compiler/program.go:1728 HandleNoEmitOnError
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
        ..EmitResult::default()
    })
}

// Go: compiler/program.go getSourceFilesToEmit (compiler/emitter.go:506 getSourceFilesToEmit)
fn get_source_files_to_emit_for(target_source_file: Node, force_dts_emit: bool) -> Vec<Node> {
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

// Go: compiler/program.go:226 Program.GetSourceFileFromReference
pub fn get_source_file_from_reference(origin: Node, r#ref: &FileReference) -> Node {
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

// ---------------------------------------------------------------------------
// Go compiler/emitHost.go
// ---------------------------------------------------------------------------

// Go: compiler/emitHost.go:33 emitHost
// NOTE: emitHost operations must be thread-safe
// PORT: `program.rs` has an `EmitHost` that only the declaration
// diagnostics use; its output paths and `WriteFile` are unported. This is
// the full host for emit.
pub struct ProgramEmitHost {
    emit_resolver: Rc<dyn crate::printer::EmitResolver>,
    /// Pool index of the checker that owns the file being emitted.
    pub checker_index: usize,
}

// Go: compiler/emitHost.go:38 newEmitHost
// PORT: must run on the thread of the file's checker (see `emit`).
pub fn new_emit_host(file: Node) -> Rc<ProgramEmitHost> {
    let checker_index = checker_index_of_file(file);
    let emit_resolver: Rc<crate::checker::emit_resolver_p1::EmitResolver> =
        with_checker_at(checker_index, Checker::get_emit_resolver);
    Rc::new(ProgramEmitHost {
        emit_resolver,
        checker_index,
    })
}

impl ProgramEmitHost {
    /// Go `host.GetEmitResolver()` without the trait object.
    #[must_use]
    pub fn emit_resolver(&self) -> Rc<dyn crate::printer::EmitResolver> {
        self.emit_resolver.clone()
    }
}

impl OutputPathsHost for ProgramEmitHost {
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

impl crate::declarations::DeclarationEmitHost for ProgramEmitHost {
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
        Box::new(get_output_paths_for(file, options(), self, force_dts_paths))
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

impl crate::printer::EmitHost for ProgramEmitHost {
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
        crate::program::is_emit_blocked(file)
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
        get_emit_module_format_of_file(super::emitter::parsed_source_file(file))
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

// ---------------------------------------------------------------------------
// Go outputpaths/outputpaths.go
// ---------------------------------------------------------------------------

// Go: outputpaths/outputpaths.go:17 OutputPaths
// PORT: `frontend::outputpaths::OutputPaths` works on frontend parsed files
// and has private fields. This is the same struct for program source files.
#[derive(Clone, Debug, Default)]
pub struct OutputPaths {
    js_file_path: String,
    source_map_file_path: String,
    declaration_file_path: String,
    declaration_map_path: String,
}

impl OutputPaths {
    // Go: outputpaths/outputpaths.go:25 (*OutputPaths).DeclarationFilePath
    #[must_use]
    pub fn declaration_file_path(&self) -> &str {
        &self.declaration_file_path
    }

    // Go: outputpaths/outputpaths.go:30 (*OutputPaths).JsFilePath
    #[must_use]
    pub fn js_file_path(&self) -> &str {
        &self.js_file_path
    }

    // Go: outputpaths/outputpaths.go:34 (*OutputPaths).SourceMapFilePath
    #[must_use]
    pub fn source_map_file_path(&self) -> &str {
        &self.source_map_file_path
    }

    // Go: outputpaths/outputpaths.go:38 (*OutputPaths).DeclarationMapPath
    #[must_use]
    pub fn declaration_map_path(&self) -> &str {
        &self.declaration_map_path
    }
}

impl crate::declarations::OutputPaths for OutputPaths {
    fn declaration_file_path(&self) -> String {
        self.declaration_file_path.clone()
    }

    fn js_file_path(&self) -> String {
        self.js_file_path.clone()
    }
}

// Go: outputpaths/outputpaths.go:42 GetOutputPathsFor
pub fn get_output_paths_for(
    source_file: Node,
    options: &CompilerOptions,
    host: &dyn OutputPathsHost,
    force_dts_emit: bool,
) -> OutputPaths {
    let file_name = source_file_file_name(source_file);
    let own_output_file_path = get_own_emit_output_file_path(
        file_name,
        options,
        host,
        get_output_extension(file_name, options.jsx),
    );
    let is_json_file = is_json_source_file(source_file);
    // If json file emits to the same location skip writing it, if emitDeclarationOnly skip writing it
    let is_json_emitted_to_same_location = is_json_file
        && compare_paths(
            file_name,
            &own_output_file_path,
            &ComparePathsOptions {
                current_directory: host.get_current_directory(),
                use_case_sensitive_file_names: host.use_case_sensitive_file_names(),
            },
        ) == 0;
    let mut paths = OutputPaths::default();
    if options.emit_declaration_only != Tristate::True && !is_json_emitted_to_same_location {
        paths.js_file_path = own_output_file_path;
        if !is_json_file {
            paths.source_map_file_path = get_source_map_file_path(&paths.js_file_path, options);
        }
    }
    if force_dts_emit || options.get_emit_declarations() && !is_json_file {
        paths.declaration_file_path =
            get_declaration_emit_output_file_path(file_name, options, host);
        if options.get_are_declaration_maps_enabled() {
            paths.declaration_map_path = format!("{}.map", paths.declaration_file_path);
        }
    }
    paths
}

// Go: outputpaths/outputpaths.go:177 getOwnEmitOutputFilePath
fn get_own_emit_output_file_path(
    file_name: &str,
    options: &CompilerOptions,
    host: &dyn OutputPathsHost,
    extension: &str,
) -> String {
    let emit_output_file_path_without_extension = if !options.out_dir.is_empty() {
        let current_directory = host.get_current_directory();
        remove_file_extension(&get_source_file_path_in_new_dir(
            file_name,
            &options.out_dir,
            &current_directory,
            &host.common_source_directory(),
            host.use_case_sensitive_file_names(),
        ))
        .to_string()
    } else {
        remove_file_extension(file_name).to_string()
    };
    emit_output_file_path_without_extension + extension
}
