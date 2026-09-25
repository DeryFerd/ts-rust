//! Port of Go `compiler/emitter.go`: the per-file emitter, the script
//! transformer pipeline and the source map path helpers.
//!
//! `sourceFileMayBeEmitted`, `getSourceFilesToEmit`, `isSourceFileNotJson`
//! and `getDeclarationDiagnostics` are ported in `program.rs`.

use crate::prelude::*;

use super::program_emit::{EmitResult, SourceMapEmitResult, WriteFile, WriteFileData};
use crate::binder::reference_resolver::ReferenceResolverHooks;
use crate::declarations::DeclarationTransformer;
use crate::frontend::outputpaths::OutputPaths;
use crate::frontend::outputpaths::get_source_file_path_in_new_dir;
use crate::frontend::tspath::{
    ComparePathsOptions, combine_paths, ensure_trailing_directory_separator, file_extension_is,
    get_base_file_name, get_directory_path, get_relative_path_to_directory_or_url, get_root_length,
    normalize_path, normalize_slashes,
};
use crate::printer::EmitResolver;
use crate::sourcemap::generator::{Generator, new_generator};
use crate::transformers::reference_resolver::new_binder_reference_resolver;
use crate::transformers::transformer::{
    EmitResolverReferenceResolver, TransformOptions, TransformReferenceResolver, TransformerBox,
};

// Go: compiler/emitter.go:24 EmitOnly
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum EmitOnly {
    #[default]
    All,
    Js,
    Dts,
    ForcedDts,
}

// Go: compiler/emitter.go:33 emitter
// PORT: Go `tr *tracing.Tracing` is left out (tracing is skipped).
pub struct Emitter {
    pub host: Rc<crate::program::EmitHost>,
    pub emit_only: EmitOnly,
    pub emitter_diagnostics: DiagnosticsCollection,
    pub writer: Option<Rc<RefCell<dyn EmitTextWriter>>>,
    pub paths: OutputPaths,
    pub source_file: Node,
    pub emit_result: EmitResult,
    pub write_file: Option<WriteFile>,
}

impl Emitter {
    fn writer(&self) -> std::cell::RefMut<'_, dyn EmitTextWriter> {
        self.writer.as_ref().expect("nil writer").borrow_mut()
    }

    // Go: compiler/emitter.go:45 emitter.emit
    pub fn emit(&mut self) {
        let js_file_path = self.paths.js_file_path().to_string();
        let source_map_file_path = self.paths.source_map_file_path().to_string();
        let declaration_file_path = self.paths.declaration_file_path().to_string();
        let declaration_map_path = self.paths.declaration_map_path().to_string();
        self.emit_js_file(self.source_file, &js_file_path, &source_map_file_path);
        self.emit_declaration_file(
            self.source_file,
            &declaration_file_path,
            &declaration_map_path,
        );
        self.emit_result.diagnostics = self.emitter_diagnostics.get_diagnostics();
    }

    // Go: compiler/emitter.go:54 emitter.getDeclarationTransformers
    fn get_declaration_transformers(
        &self,
        emit_context: &Rc<EmitContext>,
        declaration_file_path: &str,
        declaration_map_path: &str,
    ) -> Vec<DeclarationTransformer> {
        let transform = crate::declarations::new_declaration_transformer(
            self.host.clone(),
            Some(emit_context.clone()),
            options(),
            declaration_file_path,
            declaration_map_path,
        );
        vec![transform]
    }

    // Go: compiler/emitter.go:59 emitter.runScriptTransformers
    fn run_script_transformers(
        &self,
        emit_context: &Rc<EmitContext>,
        mut source_file: Node,
    ) -> Node {
        for mut transformer in get_script_transformers(emit_context, &self.host, source_file) {
            source_file = transformer.transform_source_file(source_file);
        }
        source_file
    }

    // Go: compiler/emitter.go:69 emitter.runDeclarationTransformers
    fn run_declaration_transformers(
        &self,
        emit_context: &Rc<EmitContext>,
        mut source_file: Node,
        declaration_file_path: &str,
        declaration_map_path: &str,
    ) -> (Node, Vec<Diagnostic>) {
        let mut diags = Vec::new();
        for mut transformer in self.get_declaration_transformers(
            emit_context,
            declaration_file_path,
            declaration_map_path,
        ) {
            source_file = transformer.transform_source_file_root(source_file);
            diags.extend(transformer.get_diagnostics());
        }
        (source_file, diags)
    }

    // Go: compiler/emitter.go:181 emitter.emitJSFile
    fn emit_js_file(&mut self, source_file: Node, js_file_path: &str, source_map_file_path: &str) {
        let options = options();

        if source_file.is_nil()
            || self.emit_only != EmitOnly::All && self.emit_only != EmitOnly::Js
            || js_file_path.is_empty()
        {
            return;
        }

        if options.no_emit == Tristate::True
            || crate::printer::EmitHost::is_emit_blocked(self.host.as_ref(), js_file_path)
        {
            self.emit_result.emit_skipped = true;
            return;
        }

        let (emit_context, put_emit_context) = get_emit_context();

        let source_file = self.run_script_transformers(&emit_context, source_file);

        let printer_options = PrinterOptions {
            remove_comments: options.remove_comments.is_true(),
            new_line: options.new_line,
            no_emit_helpers: options.no_emit_helpers.is_true(),
            source_map: options.source_map.is_true(),
            inline_source_map: options.inline_source_map.is_true(),
            inline_sources: options.inline_sources.is_true(),
            target: options.target,
            // !!!
            ..PrinterOptions::default()
        };

        // create a printer to print the nodes
        let mut printer = new_printer(
            printer_options,
            PrintHandlers {
                // !!!
                ..PrintHandlers::default()
            },
            Some(emit_context.clone()),
        );

        let should_emit_source_maps = should_emit_source_maps(options, source_file);
        self.print_source_file(
            js_file_path,
            source_map_file_path,
            source_file,
            &mut printer,
            options,
            should_emit_source_maps,
        );
        put_emit_context();
    }

    // Go: compiler/emitter.go:223 emitter.emitDeclarationFile
    fn emit_declaration_file(
        &mut self,
        source_file: Node,
        declaration_file_path: &str,
        declaration_map_path: &str,
    ) {
        let options = options();

        if source_file.is_nil()
            || self.emit_only == EmitOnly::Js
            || declaration_file_path.is_empty()
        {
            return;
        }

        let (emit_context, put_emit_context) = get_emit_context();
        let (source_file, diags) = self.run_declaration_transformers(
            &emit_context,
            source_file,
            declaration_file_path,
            declaration_map_path,
        );

        for elem in &diags {
            // Add declaration transform diagnostics to emit diagnostics
            self.emitter_diagnostics.add(elem.clone());
        }

        if self.emit_only != EmitOnly::ForcedDts
            && (options.no_emit == Tristate::True
                || crate::printer::EmitHost::is_emit_blocked(
                    self.host.as_ref(),
                    declaration_file_path,
                ))
        {
            self.emit_result.emit_skipped = true;
            put_emit_context();
            return;
        }

        let decl_blocked = !diags.is_empty() && self.emit_only != EmitOnly::ForcedDts;
        if decl_blocked {
            self.emit_result.emit_skipped = true;
            put_emit_context();
            return;
        }

        let printer_options = PrinterOptions {
            remove_comments: options.remove_comments.is_true(),
            new_line: options.new_line,
            no_emit_helpers: true,
            // Module: 			   options.Module, // NYI
            // ModuleResolution:   options.ModuleResolution, // NYI
            target: options.get_emit_script_target(),
            source_map: self.emit_only != EmitOnly::ForcedDts && options.declaration_map.is_true(),
            inline_source_map: options.inline_source_map.is_true(),
            // InlineSources:       options.InlineSources.IsTrue(), // ignored, per strada
            // ExtendedDiagnostics: options.ExtendedDiagnostics.IsTrue(), // NYI
            only_print_js_doc_style: true,
            omit_brace_source_map_positions: true,
            ..PrinterOptions::default()
        };

        // create a printer to print the nodes
        let mut printer = new_printer(
            printer_options,
            PrintHandlers {
                // !!!
                ..PrintHandlers::default()
            },
            Some(emit_context.clone()),
        );

        let declaration_map_options = CompilerOptions {
            source_map: if self.emit_only != EmitOnly::ForcedDts
                && options.declaration_map.is_true()
            {
                Tristate::True
            } else {
                Tristate::False
            },
            source_root: options.source_root.clone(),
            map_root: options.map_root.clone(),
            // Explicitly do not pass through either inline option.
            ..CompilerOptions::default()
        };
        let should_emit_source_maps =
            should_emit_source_maps(&declaration_map_options, source_file);
        self.print_source_file(
            declaration_file_path,
            declaration_map_path,
            source_file,
            &mut printer,
            &declaration_map_options,
            should_emit_source_maps,
        );
        put_emit_context();
    }

    // Go: compiler/emitter.go:289 emitter.printSourceFile
    fn print_source_file(
        &mut self,
        js_file_path: &str,
        source_map_file_path: &str,
        source_file: Node,
        printer: &mut Printer,
        map_options: &CompilerOptions,
        should_emit_source_maps: bool,
    ) {
        // !!! sourceMapGenerator
        let options = options();
        let mut source_map_generator: Option<Rc<RefCell<Generator>>> = None;
        if should_emit_source_maps {
            source_map_generator = Some(Rc::new(RefCell::new(new_generator(
                &get_base_file_name(&normalize_slashes(js_file_path)),
                &get_source_root(map_options),
                &self.get_source_map_directory(map_options, js_file_path, source_file),
                ComparePathsOptions {
                    use_case_sensitive_file_names: use_case_sensitive_file_names(),
                    current_directory: get_current_directory().to_string(),
                },
            ))));
        }

        let writer = self.writer.clone().expect("nil writer");
        printer.write_exported(
            source_file,
            source_file,
            writer,
            source_map_generator.clone(),
        );

        let mut source_map_url_pos = -1;
        if let Some(generator) = &source_map_generator {
            if map_options.source_map.is_true() || map_options.inline_source_map.is_true() {
                let mut generator = generator.borrow_mut();
                let input_source_file_names = generator.sources();
                let source_map = generator.raw_source_map();
                self.emit_result.source_maps.push(SourceMapEmitResult {
                    input_source_file_names,
                    source_map,
                    generated_file: js_file_path.to_string(),
                });
            }

            let source_mapping_url = self.get_source_mapping_url(
                map_options,
                &mut generator.borrow_mut(),
                js_file_path,
                source_map_file_path,
                source_file,
            );

            if !source_mapping_url.is_empty() {
                let mut writer = self.writer();
                if !writer.is_at_start_of_line() {
                    writer.raw_write(if options.new_line == NewLineKind::CRLF {
                        "\r\n"
                    } else {
                        "\n"
                    });
                }
                source_map_url_pos = writer.get_text_pos();
                writer.write_comment("//# sourceMappingURL=");
                writer.write_comment(&source_mapping_url);
            }

            // Write the source map
            if !source_map_file_path.is_empty() {
                let source_map = generator.borrow_mut().string();
                let result = self.write_text(source_map_file_path, &source_map, None);
                match result {
                    Err(err) => self.emitter_diagnostics.add(new_compiler_diagnostic(
                        diag::Could_not_write_file_0_Colon_1,
                        args![js_file_path, err],
                    )),
                    Ok(()) => self
                        .emit_result
                        .emitted_files
                        .push(source_map_file_path.to_string()),
                }
            }
        } else {
            self.writer().write_line();
        }

        // Write the output file
        let mut text = self.writer().string();
        if options.emit_bom.is_true() {
            text = add_utf8_byte_order_mark(text);
        }
        let mut data = WriteFileData {
            source_map_url_pos,
            diagnostics: self.emitter_diagnostics.get_diagnostics(),
            skipped_dts_write: false,
        };
        let result = self.write_text(js_file_path, &text, Some(&mut data));
        let skipped_dts_write = data.skipped_dts_write;
        match result {
            Err(err) => self.emitter_diagnostics.add(new_compiler_diagnostic(
                diag::Could_not_write_file_0_Colon_1,
                args![js_file_path, err],
            )),
            Ok(()) => {
                if !skipped_dts_write {
                    self.emit_result
                        .emitted_files
                        .push(js_file_path.to_string());
                }
            }
        }

        // Reset state
        self.writer().clear();
    }

    // Go: compiler/emitter.go:374 emitter.writeText
    // PORT: Go passes a nil `*WriteFileData` for source maps; the callback
    // gets a default one then.
    fn write_text(
        &self,
        file_name: &str,
        text: &str,
        data: Option<&mut WriteFileData>,
    ) -> Result<(), String> {
        if let Some(write_file) = &self.write_file {
            let mut default_data = WriteFileData::default();
            let data = data.unwrap_or(&mut default_data);
            return write_file(file_name, text, data);
        }
        crate::printer::EmitHost::write_file(self.host.as_ref(), file_name, text)
    }

    // Go: compiler/emitter.go:397 emitter.getSourceMapDirectory
    fn get_source_map_directory(
        &self,
        map_options: &CompilerOptions,
        file_path: &str,
        source_file: Node,
    ) -> String {
        if !map_options.source_root.is_empty() {
            return common_source_directory().to_string();
        }
        if !map_options.map_root.is_empty() {
            let mut source_map_dir = normalize_slashes(&map_options.map_root);
            if source_file.is_some() {
                // For modules or multiple emit files the mapRoot will have directory structure like the sources
                // So if src\a.ts and src\lib\b.ts are compiled together user would be moving the maps into mapRoot\a.js.map and mapRoot\lib\b.js.map
                source_map_dir = get_directory_path(&get_source_file_path_in_new_dir(
                    source_file_file_name(source_file),
                    &source_map_dir,
                    get_current_directory(),
                    common_source_directory(),
                    use_case_sensitive_file_names(),
                ));
            }
            if get_root_length(&source_map_dir) == 0 {
                // The relative paths are relative to the common directory
                source_map_dir = combine_paths(common_source_directory(), &[&source_map_dir]);
            }
            return source_map_dir;
        }
        get_directory_path(&normalize_path(file_path))
    }

    // Go: compiler/emitter.go:422 emitter.getSourceMappingURL
    fn get_source_mapping_url(
        &self,
        map_options: &CompilerOptions,
        source_map_generator: &mut Generator,
        file_path: &str,
        source_map_file_path: &str,
        source_file: Node,
    ) -> String {
        if map_options.inline_source_map.is_true() {
            // Encode the sourceMap into the sourceMap url
            return source_map_generator.base64_data_url();
        }

        let source_map_file = get_base_file_name(&normalize_slashes(source_map_file_path));
        if !map_options.map_root.is_empty() {
            let mut source_map_dir = normalize_slashes(&map_options.map_root);
            if source_file.is_some() {
                // For modules or multiple emit files the mapRoot will have directory structure like the sources
                // So if src\a.ts and src\lib\b.ts are compiled together user would be moving the maps into mapRoot\a.js.map and mapRoot\lib\b.js.map
                source_map_dir = get_directory_path(&get_source_file_path_in_new_dir(
                    source_file_file_name(source_file),
                    &source_map_dir,
                    get_current_directory(),
                    common_source_directory(),
                    use_case_sensitive_file_names(),
                ));
            }
            if get_root_length(&source_map_dir) == 0 {
                // The relative paths are relative to the common directory
                source_map_dir = combine_paths(common_source_directory(), &[&source_map_dir]);
                return encode_uri(&get_relative_path_to_directory_or_url(
                    &get_directory_path(&normalize_path(file_path)), // get the relative sourceMapDir path based on jsFilePath
                    &combine_paths(&source_map_dir, &[&source_map_file]), // this is where user expects to see sourceMap
                    /*isAbsolutePathAnUrl*/ true,
                    &ComparePathsOptions {
                        use_case_sensitive_file_names: use_case_sensitive_file_names(),
                        current_directory: get_current_directory().to_string(),
                    },
                ));
            } else {
                return encode_uri(&combine_paths(&source_map_dir, &[&source_map_file]));
            }
        }
        encode_uri(&source_map_file)
    }
}

// Go: compiler/emitter.go:84 getModuleTransformer
fn get_module_transformer(opts: &TransformOptions) -> Option<TransformerBox> {
    use crate::transformers::moduletransforms;
    match opts.compiler_options.get_emit_module_kind() {
        ModuleKind::PRESERVE => {
            // `ESModuleTransformer` contains logic for preserving CJS input syntax in `--module preserve`
            into_transformer(moduletransforms::new_es_module_transformer(opts))
        }

        ModuleKind::ES_NEXT
        | ModuleKind::ES2022
        | ModuleKind::ES2020
        | ModuleKind::ES2015
        | ModuleKind::NODE20
        | ModuleKind::NODE18
        | ModuleKind::NODE16
        | ModuleKind::NODE_NEXT
        | ModuleKind::COMMON_JS => {
            into_transformer(moduletransforms::new_implied_module_transformer(opts))
        }

        _ => into_transformer(moduletransforms::new_commonjs_module_transformer(opts)),
    }
}

/// Go appends each constructor result to `tx`. Constructors that never
/// return nil return a plain `TransformerBox`; the others return an
/// `Option`. This takes either.
// PORT: Go would panic later on a nil transformer; a `None` is skipped.
trait IntoTransformer {
    fn into_transformer(self) -> Option<TransformerBox>;
}

impl IntoTransformer for TransformerBox {
    fn into_transformer(self) -> Option<TransformerBox> {
        Some(self)
    }
}

impl IntoTransformer for Option<TransformerBox> {
    fn into_transformer(self) -> Option<TransformerBox> {
        self
    }
}

fn into_transformer(t: impl IntoTransformer) -> Option<TransformerBox> {
    t.into_transformer()
}

// Go: compiler/emitter.go:107 getScriptTransformers
pub fn get_script_transformers(
    emit_context: &Rc<EmitContext>,
    host: &Rc<crate::program::EmitHost>,
    source_file: Node,
) -> Vec<TransformerBox> {
    use crate::transformers::{estransforms, inliners, jsxtransforms, tstransforms};

    let mut tx: Vec<TransformerBox> = Vec::new();
    let options = options();

    // JS files don't use reference calculations as they don't do import elision, no need to calculate it
    let import_elision_enabled =
        !options.verbatim_module_syntax.is_true() && !is_in_js_file(source_file);
    let jsx_transform_enabled = options.get_jsx_transform_enabled()
        && source_file_info(source_file).language_variant == LanguageVariant::JSX;

    let emit_resolver: Rc<dyn EmitResolver> = host.emit_resolver();

    let reference_resolver: Rc<dyn TransformReferenceResolver> = if import_elision_enabled
        || jsx_transform_enabled
        || !options.get_isolated_modules()
        || options.emit_decorator_metadata.is_true()
    {
        emit_resolver.mark_linked_references_recursively(source_file);
        Rc::new(EmitResolverReferenceResolver(emit_resolver.clone()))
    } else {
        Rc::new(new_binder_reference_resolver(
            options,
            ReferenceResolverHooks::default(),
            host.checker_index,
        ))
    };

    let opts = TransformOptions {
        context: emit_context.clone(),
        compiler_options: options,
        resolver: reference_resolver,
        emit_resolver,
        get_emit_module_format_of_file: Rc::new(|file| {
            get_emit_module_format_of_file(parsed_source_file(file))
        }),
    };

    let mut push = |t: Option<TransformerBox>| {
        if let Some(t) = t {
            tx.push(t);
        }
    };

    // transform TypeScript syntax
    {
        // use type nodes to add metadata decorators
        if options.emit_decorator_metadata.is_true() {
            push(into_transformer(tstransforms::new_metadata_transformer(
                &opts,
            )));
        }

        // erase types
        push(into_transformer(tstransforms::new_type_eraser_transformer(
            &opts,
        )));

        // elide imports
        if import_elision_enabled {
            push(into_transformer(
                tstransforms::new_import_elision_transformer(&opts),
            ));
        }

        // transform `enum`, `namespace`, and parameter properties
        push(into_transformer(
            tstransforms::new_runtime_syntax_transformer(&opts),
        ));

        if options.experimental_decorators.is_true() {
            push(into_transformer(
                tstransforms::new_legacy_decorators_transformer(&opts),
            ));
        }
    }

    if jsx_transform_enabled {
        push(into_transformer(jsxtransforms::new_jsx_transformer(&opts)));
    }

    let downleveler = into_transformer(estransforms::get_es_transformer(&opts));
    if downleveler.is_some() {
        push(downleveler);
    }

    push(into_transformer(estransforms::new_use_strict_transformer(
        &opts,
    )));

    // transform module syntax
    push(get_module_transformer(&opts));

    // inlining (formerly done via substitutions)
    if !options.get_isolated_modules() {
        push(into_transformer(
            inliners::new_const_enum_inlining_transformer(&opts),
        ));
    }
    tx
}

/// The parsed SourceFile for Go `ast.HasFileName` callbacks.
// PORT: Go `GetEmitModuleFormatOfFile(file ast.HasFileName)` reads only the
// file name and path, which a transformed (factory) SourceFile copies from
// its original. The program functions read parsed files only, so a factory
// SourceFile maps to the parsed file with the same path.
pub fn parsed_source_file(file: Node) -> Node {
    if is_synthetic_node(file) {
        let path = with_synthetic_source_file(file, |d| d.path.clone());
        return get_source_file_by_path(&path);
    }
    file
}

// Go: compiler/emitter.go:380 shouldEmitSourceMaps
fn should_emit_source_maps(map_options: &CompilerOptions, source_file: Node) -> bool {
    (map_options.source_map.is_true() || map_options.inline_source_map.is_true())
        && !file_extension_is(source_file_file_name(source_file), ".json")
}

// Go: compiler/emitter.go:385 getSourceRoot
fn get_source_root(map_options: &CompilerOptions) -> String {
    // Normalize source root and make sure it has trailing "/" so that it can be used to combine paths with the
    // relative paths of the sources list in the sourcemap
    let mut source_root = normalize_slashes(&map_options.source_root);
    if !source_root.is_empty() {
        source_root = ensure_trailing_directory_separator(&source_root);
    }
    source_root
}

// Go: stringutil/util.go:144 EncodeURI
pub fn encode_uri(s: &str) -> String {
    const UPPERHEX: &[u8; 16] = b"0123456789ABCDEF";
    let mut builder = String::with_capacity(s.len());
    for &b in s.as_bytes() {
        if !should_escape_for_encode_uri(b) {
            builder.push(b as char);
            continue;
        }
        builder.push('%');
        builder.push(UPPERHEX[(b >> 4) as usize] as char);
        builder.push(UPPERHEX[(b & 0x0f) as usize] as char);
    }
    builder
}

// Go: stringutil/util.go:164 shouldEscapeForEncodeURI
fn should_escape_for_encode_uri(b: u8) -> bool {
    if b.is_ascii_alphanumeric() {
        return false;
    }
    !matches!(
        b,
        b';' | b'/'
            | b'?'
            | b':'
            | b'@'
            | b'&'
            | b'='
            | b'+'
            | b'$'
            | b','
            | b'#'
            | b'-'
            | b'_'
            | b'.'
            | b'!'
            | b'~'
            | b'*'
            | b'\''
            | b'('
            | b')'
    )
}

// Go: stringutil/util.go:215 AddUTF8ByteOrderMark
// PORT: a Rust `String` is UTF-8, so only the UTF-8 mark can be present.
pub fn add_utf8_byte_order_mark(text: String) -> String {
    if text.starts_with('\u{FEFF}') {
        return text;
    }
    format!("\u{FEFF}{text}")
}
