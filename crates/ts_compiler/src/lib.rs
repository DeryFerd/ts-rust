//! Compiler Program and source-file graph foundations.

use std::{
    collections::{BTreeMap, BTreeSet, HashSet},
    path::Path,
};

use ts_ast::{NodeData, NodeId};
use ts_binder::{BindResult, bind_source_file};
use ts_checker::{
    CheckDiagnostic, CheckResult, CheckerOptions, EnumConstantValue as CheckerConstantValue,
    ProgramSource, TypeId, TypeKind, check_program_with_paths, empty_check_result,
};
use ts_config::{ConfigDiagnostic, resolve_config_file};
use ts_core::{TextPos, TextRange};
use ts_diagnostics::{Diagnostic, message_by_code};
use ts_glob::{DiscoveryOptions, discover_files};
use ts_module::{ResolutionOptions, Resolver, automatic_type_directive_names, parse_package_json};
use ts_options::{CompilerOptions, ModuleKind, PrinterSettings, parse_project_options};
use ts_parser::{ParseResult, parse_jsx_source_file, parse_source_file};
use ts_path::{
    CaseSensitivity, canonicalize, change_extension, declaration_emit_extension, directory_path,
    is_absolute, resolve_path,
};
use ts_printer::{
    AmdDependency as PrinterAmdDependency, BUNDLE_EXTENDS_HELPER, EmitConstantValue, EmitContext,
    emit_declaration_file_with_semantics, emit_source_file_with_context, runtime_identifier_uses,
    source_needs_extends_helper,
};
use ts_sourcemap::{SourceMap, SourceMapBuilder};
use ts_vfs::FileSystem;

/// One parsed source file owned by a Program.
#[derive(Debug)]
pub struct SourceFile {
    pub file_name: String,
    pub source_text: String,
    pub parse: ParseResult,
    pub binding: BindResult,
    pub checking: CheckResult,
    pub is_default_library: bool,
    implied_node_format: ModuleKind,
}

/// A diagnostic produced while constructing or parsing a Program.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ProgramDiagnostic {
    pub file_name: Option<String>,
    pub range: Option<TextRange>,
    pub code: Option<u32>,
    pub message: String,
}

/// Command-line overrides applied after loading a project configuration.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct ProgramOptionsOverride {
    pub no_check: Option<bool>,
    pub no_emit: Option<bool>,
    pub no_lib: Option<bool>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct OutputFile {
    pub file_name: String,
    pub text: String,
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct EmitOutput {
    pub files: Vec<OutputFile>,
    pub diagnostics: Vec<ProgramDiagnostic>,
}

fn prepend_emit_bom(files: &mut [OutputFile]) {
    for file in files {
        let lower = file.file_name.to_ascii_lowercase();
        if [".js", ".jsx", ".mjs", ".cjs", ".d.ts", ".d.mts", ".d.cts"]
            .iter()
            .any(|extension| lower.ends_with(extension))
            && !file.text.starts_with('\u{feff}')
        {
            file.text.insert(0, '\u{feff}');
        }
    }
}

fn source_shebang(source: &SourceFile) -> Option<&str> {
    let text = source
        .source_text
        .strip_prefix('\u{feff}')
        .unwrap_or(&source.source_text);
    text.lines()
        .find(|line| line.starts_with("#!"))
        .map(|line| line.trim_end_matches('\r'))
}

fn source_prologue_directives(source: &SourceFile) -> Vec<&str> {
    let Some(NodeData::SourceFile(file)) = source
        .parse
        .arena
        .get(source.parse.source_file)
        .map(|node| &node.data)
    else {
        return Vec::new();
    };
    file.statements
        .nodes
        .iter()
        .map_while(|statement| {
            let NodeData::ExpressionStatement(statement) =
                &source.parse.arena.get(*statement)?.data
            else {
                return None;
            };
            let NodeData::StringLiteral(literal) =
                &source.parse.arena.get(statement.expression)?.data
            else {
                return None;
            };
            Some(literal.text.as_str())
        })
        .collect()
}

fn push_bundle_prologue(code: &mut String, directive: &str) {
    code.push('"');
    for character in directive.chars() {
        match character {
            '"' => code.push_str("\\\""),
            '\\' => code.push_str("\\\\"),
            '\n' => code.push_str("\\n"),
            '\r' => code.push_str("\\r"),
            '\t' => code.push_str("\\t"),
            character => code.push(character),
        }
    }
    code.push_str("\";\n");
}

fn bundle_detached_comment(source: &SourceFile) -> Option<(String, u32)> {
    let Some(NodeData::SourceFile(file)) = source
        .parse
        .arena
        .get(source.parse.source_file)
        .map(|node| &node.data)
    else {
        return None;
    };
    let first_statement = file.statements.nodes.first()?;
    let end = usize::try_from(source.parse.arena.get(*first_statement)?.range.start.get()).ok()?;
    let prefix = source.source_text.get(..end)?;
    let separators = ["\r\n\r\n", "\n\n", "\r\r"];
    let (separator_start, separator_len) = separators
        .iter()
        .filter_map(|separator| prefix.find(separator).map(|start| (start, separator.len())))
        .min_by_key(|(start, _)| *start)?;
    let comment = prefix[..separator_start].trim();
    if !comment.starts_with("//") && !comment.starts_with("/*") {
        return None;
    }
    let excluded_end = u32::try_from(separator_start + separator_len).ok()?;
    Some((format!("{comment}\n"), excluded_end))
}

/// A compilation's parsed source-file graph.
#[derive(Debug, Default)]
pub struct Program {
    source_files: Vec<SourceFile>,
    file_index: BTreeMap<String, usize>,
    root_file_names: BTreeSet<String>,
    resolved_modules: BTreeMap<(String, String), String>,
    diagnostics: Vec<ProgramDiagnostic>,
    current_directory: String,
    case_sensitivity: CaseSensitivity,
    options: CompilerOptions,
}

impl Program {
    /// Creates a Program from explicit root file names.
    #[must_use]
    pub fn new(
        file_system: &dyn FileSystem,
        current_directory: &str,
        root_names: &[String],
    ) -> Self {
        let mut program = Self::new_unchecked(file_system, current_directory, root_names);
        program.check_program();
        program
    }

    fn new_unchecked(
        file_system: &dyn FileSystem,
        current_directory: &str,
        root_names: &[String],
    ) -> Self {
        let case_sensitivity = if file_system.use_case_sensitive_file_names() {
            CaseSensitivity::Sensitive
        } else {
            CaseSensitivity::Insensitive
        };
        let current_directory = ts_path::normalize_path(current_directory);
        let mut program = Self {
            current_directory: current_directory.clone(),
            case_sensitivity,
            ..Self::default()
        };
        for root_name in root_names {
            let file_name = if is_absolute(root_name) {
                ts_path::normalize_path(root_name)
            } else {
                resolve_path(&current_directory, &[root_name])
            };
            program.root_file_names.insert(canonicalize(
                &file_name,
                &program.current_directory,
                program.case_sensitivity,
            ));
            program.load_file(file_system, &file_name, true);
        }
        program
    }

    /// Creates a Program and follows import/export module specifiers using the
    /// foundational Node resolver.
    #[must_use]
    pub fn new_with_module_resolution(
        file_system: &dyn FileSystem,
        current_directory: &str,
        root_names: &[String],
        resolution_options: ResolutionOptions,
    ) -> Self {
        let mut program = Self::new_unchecked(file_system, current_directory, root_names);
        program.load_module_graph(file_system, resolution_options);
        program.check_program();
        program
    }

    fn load_module_graph(
        &mut self,
        file_system: &dyn FileSystem,
        resolution_options: ResolutionOptions,
    ) {
        let resolver = Resolver::new(file_system, resolution_options);
        let mut ambient_modules = BTreeMap::new();
        for source_file in &self.source_files {
            register_ambient_external_modules(
                source_file,
                &self.current_directory,
                self.case_sensitivity,
                &mut ambient_modules,
            );
        }
        let mut file_index = 0;
        while file_index < self.source_files.len() {
            if self.source_files[file_index].is_default_library {
                file_index += 1;
                continue;
            }
            register_ambient_external_modules(
                &self.source_files[file_index],
                &self.current_directory,
                self.case_sensitivity,
                &mut ambient_modules,
            );
            let containing_file = self.source_files[file_index].file_name.clone();
            let specifiers = module_specifiers(&self.source_files[file_index].parse);
            for (specifier, range, can_resolve_ambient) in specifiers {
                let result = resolver.resolve(&specifier, &containing_file);
                if let Some(resolved) = result.resolved {
                    let containing = canonicalize(
                        &containing_file,
                        &self.current_directory,
                        self.case_sensitivity,
                    );
                    let target = canonicalize(
                        &resolved.resolved_file_name,
                        &self.current_directory,
                        self.case_sensitivity,
                    );
                    self.resolved_modules
                        .insert((containing, specifier.clone()), target);
                    self.load_file(file_system, &resolved.resolved_file_name, false);
                } else if can_resolve_ambient
                    && !module_name_is_relative(&specifier)
                    && let Some(target) = ambient_modules.get(&specifier)
                {
                    let containing = canonicalize(
                        &containing_file,
                        &self.current_directory,
                        self.case_sensitivity,
                    );
                    self.resolved_modules
                        .insert((containing, specifier.clone()), target.clone());
                } else if !self.options.no_check {
                    self.diagnostics.push(module_not_found_diagnostic(
                        &containing_file,
                        range,
                        &specifier,
                    ));
                }
            }
            file_index += 1;
        }
    }

    /// Creates a Program using fully normalized compiler options, including
    /// module resolution and bundled default-library selection.
    #[must_use]
    pub fn new_with_options(
        file_system: &dyn FileSystem,
        current_directory: &str,
        root_names: &[String],
        options: CompilerOptions,
    ) -> Self {
        let mut program = Self::new_unchecked(file_system, current_directory, root_names);
        program.options = options;
        if program.options.emit_declaration_only
            && !program.options.declaration
            && !program.options.composite
        {
            program.diagnostics.push(emit_declaration_only_diagnostic());
        }
        if program
            .source_files
            .iter()
            .any(|source| has_no_default_lib_directive(&source.source_text))
        {
            program.options.no_lib = true;
        }
        program.load_default_libraries();
        let resolution_options = program.options.module_resolution_options();
        program.load_reference_directives(file_system, &resolution_options);
        program.load_automatic_type_directives(file_system, &resolution_options);
        program.load_module_graph(file_system, resolution_options);
        program.check_program();
        program
    }

    /// Creates a Program from the explicit `files` list in a tsconfig.
    /// Include/exclude glob expansion is added by the file-loader layer.
    #[must_use]
    pub fn from_config(file_system: &dyn FileSystem, config_path: &str) -> Self {
        Self::from_config_with_options(file_system, config_path, ProgramOptionsOverride::default())
    }

    /// Creates a Program from a tsconfig and applies command-line overrides.
    #[must_use]
    pub fn from_config_with_options(
        file_system: &dyn FileSystem,
        config_path: &str,
        overrides: ProgramOptionsOverride,
    ) -> Self {
        Self::from_config_with_overrides(file_system, config_path, overrides, None)
    }

    #[must_use]
    pub fn from_config_with_command_line_options(
        file_system: &dyn FileSystem,
        config_path: &str,
        overrides: ProgramOptionsOverride,
        command_line_options: &CompilerOptions,
        specified_options: &BTreeSet<String>,
    ) -> Self {
        Self::from_config_with_overrides(
            file_system,
            config_path,
            overrides,
            Some((command_line_options, specified_options)),
        )
    }

    fn from_config_with_overrides(
        file_system: &dyn FileSystem,
        config_path: &str,
        overrides: ProgramOptionsOverride,
        command_line: Option<(&CompilerOptions, &BTreeSet<String>)>,
    ) -> Self {
        let parsed = resolve_config_file(file_system, config_path);
        let mut config_diagnostics: Vec<_> =
            parsed.diagnostics.iter().map(config_diagnostic).collect();
        let Some(config) = parsed.value else {
            return Self {
                diagnostics: config_diagnostics,
                ..Self::default()
            };
        };
        let config_directory = config
            .path
            .rsplit_once('/')
            .map_or(".", |(directory, _)| directory);
        let mut options_result = parse_project_options(&config);
        config_diagnostics.extend(options_result.diagnostics.iter().map(|diagnostic| {
            ProgramDiagnostic {
                file_name: Some(config.path.clone()),
                range: None,
                code: Some(diagnostic.code()),
                message: diagnostic
                    .render()
                    .unwrap_or_else(|error| error.to_string()),
            }
        }));
        if let Some(value) = overrides.no_check {
            options_result.options.no_check = value;
        }
        if let Some(value) = overrides.no_emit {
            options_result.options.no_emit = value;
        }
        if let Some(value) = overrides.no_lib {
            options_result.options.no_lib = value;
            if value {
                options_result.options.lib = None;
            }
        }
        if let Some((command_line_options, specified_options)) = command_line {
            options_result
                .options
                .apply_overrides(command_line_options, specified_options);
        }
        let mut discovery = DiscoveryOptions::new(config_directory);
        discovery.files = config.files.unwrap_or_default();
        discovery.include = config.include.unwrap_or_else(|| {
            if discovery.files.is_empty() {
                vec!["**/*".to_owned()]
            } else {
                Vec::new()
            }
        });
        discovery.exclude = config.exclude.unwrap_or_default();
        let roots = discover_files(file_system, &discovery).unwrap_or_else(|error| {
            config_diagnostics.push(ProgramDiagnostic {
                file_name: Some(config.path.clone()),
                range: None,
                code: None,
                message: error.to_string(),
            });
            discovery.files.clone()
        });
        let mut program = Self::new_with_options(
            file_system,
            config_directory,
            &roots,
            options_result.options,
        );
        config_diagnostics.append(&mut program.diagnostics);
        program.diagnostics = config_diagnostics;
        program
    }

    #[must_use]
    pub fn source_files(&self) -> &[SourceFile] {
        &self.source_files
    }

    #[must_use]
    pub fn diagnostics(&self) -> &[ProgramDiagnostic] {
        &self.diagnostics
    }

    #[must_use]
    pub const fn options(&self) -> &CompilerOptions {
        &self.options
    }

    #[must_use]
    pub fn source_file(&self, file_name: &str) -> Option<&SourceFile> {
        let canonical = canonicalize(file_name, &self.current_directory, self.case_sensitivity);
        self.file_index
            .get(&canonical)
            .and_then(|index| self.source_files.get(*index))
    }

    /// Emits modern JavaScript for all implementation source files currently
    /// supported by the printer.
    #[must_use]
    #[allow(clippy::too_many_lines)]
    pub fn emit(&self) -> EmitOutput {
        let mut output = EmitOutput::default();
        if self.options.no_emit_on_error && !self.diagnostics.is_empty() {
            return output;
        }
        let settings = self.options.printer_settings();
        if !settings.emit_javascript && !settings.emit_declarations {
            return output;
        }
        if self.options.out_file.is_some()
            && settings.emit_javascript
            && !matches!(
                self.options.module,
                ModuleKind::None | ModuleKind::Amd | ModuleKind::System
            )
        {
            return output;
        }
        if self.options.out_file.is_some() {
            return self.emit_bundle(settings);
        }
        let source_names = self
            .source_files
            .iter()
            .filter(|source_file| {
                !source_file.is_default_library
                    && self.source_should_emit(source_file)
                    && (!ts_path::is_declaration_file(&source_file.file_name)
                        || self.root_file_names.contains(&canonicalize(
                            &source_file.file_name,
                            &self.current_directory,
                            self.case_sensitivity,
                        )))
            })
            .map(|source_file| source_file.file_name.clone())
            .collect::<Vec<_>>();
        let common_source_directory = ts_outputpaths::common_source_directory(
            &source_names,
            &self.current_directory,
            self.case_sensitivity,
        );
        for (source_index, source_file) in self.source_files.iter().enumerate() {
            if source_file.is_default_library
                || ts_path::is_declaration_file(&source_file.file_name)
                || !self.source_should_emit(source_file)
            {
                continue;
            }
            let paths = ts_outputpaths::output_paths(
                &source_file.file_name,
                &self.options,
                &self.current_directory,
                &common_source_directory,
                self.case_sensitivity,
            );
            let enum_member_values = enum_values_for_emit(&source_file.checking.enum_member_values);
            let enum_access_values = enum_values_for_emit(&source_file.checking.enum_access_values);
            if settings.emit_javascript {
                let mut source_settings = settings;
                let lower_file_name = source_file.file_name.to_ascii_lowercase();
                let fixed_es_module = [".mts", ".mjs"]
                    .iter()
                    .any(|extension| lower_file_name.ends_with(extension));
                let fixed_module_format = fixed_es_module
                    || [".cts", ".cjs"]
                        .iter()
                        .any(|extension| lower_file_name.ends_with(extension));
                if fixed_module_format
                    || matches!(
                        source_settings.module,
                        ModuleKind::Node16
                            | ModuleKind::Node18
                            | ModuleKind::Node20
                            | ModuleKind::NodeNext
                    )
                {
                    source_settings.module = source_file.implied_node_format;
                }
                let amd_dependencies = source_file
                    .parse
                    .amd_dependencies
                    .iter()
                    .map(|dependency| PrinterAmdDependency {
                        path: &dependency.path,
                        name: dependency.name.as_deref(),
                        comment_start: dependency.range.start.get(),
                        comment_end: dependency.range.end.get(),
                    })
                    .collect::<Vec<_>>();
                let preserve_const_enums = self.options.preserve_const_enums
                    || self.options.isolated_modules
                    || self.options.verbatim_module_syntax;
                let import_runtime_meanings = import_runtime_meanings_for_emit(
                    source_file,
                    preserve_const_enums,
                    source_settings.module == ModuleKind::Amd,
                    &later_top_level_script_variable_names(
                        self.source_files.iter().skip(source_index + 1),
                    ),
                );
                let preserve_top_of_file_reference_directive =
                    reference_directives(&source_file.source_text)
                        .into_iter()
                        .filter(|directive| matches!(directive.kind, ReferenceKind::Path))
                        .any(|directive| {
                            let referenced = resolve_path(
                                &directory_path(&source_file.file_name),
                                &[directive.value.as_str()],
                            );
                            let canonical = canonicalize(
                                &referenced,
                                &self.current_directory,
                                self.case_sensitivity,
                            );
                            self.file_index.contains_key(&canonical)
                        });
                let emit_context = EmitContext {
                    bindings: &source_file.binding,
                    amd_module_name: source_file.parse.amd_module_name.as_deref(),
                    amd_bundle: false,
                    preemitted_source_prologues: false,
                    preemitted_shebang: false,
                    suppress_extends_helper: false,
                    preemitted_comment_end: None,
                    preserve_top_of_file_reference_directive,
                    amd_dependencies: &amd_dependencies,
                    amd_module_specifier_rewrites: &BTreeMap::new(),
                    amd_generated_name_offsets: &BTreeMap::new(),
                    enum_member_values: &enum_member_values,
                    enum_access_values: &enum_access_values,
                    import_runtime_meanings: &import_runtime_meanings,
                    preserve_const_enums,
                    inline_const_enums: !self.options.isolated_modules
                        && !self.options.verbatim_module_syntax,
                    emit_decorator_metadata: self.options.emit_decorator_metadata,
                    preserve_dynamic_import: matches!(
                        settings.module,
                        ModuleKind::Node16
                            | ModuleKind::Node18
                            | ModuleKind::Node20
                            | ModuleKind::NodeNext
                    ),
                    isolated_modules: self.options.isolated_modules,
                    strict_null_checks: self.options.strict_null_checks,
                    force_use_strict: fixed_es_module && settings.module == ModuleKind::CommonJs,
                    jsx_factory: self.options.jsx_factory.as_deref(),
                    downlevel_iteration: self.options.downlevel_iteration,
                    module_detection: self.options.module_detection,
                };
                match emit_source_file_with_context(
                    &source_file.parse.arena,
                    source_file.parse.source_file,
                    &source_file.file_name,
                    &source_file.source_text,
                    source_settings,
                    &emit_context,
                ) {
                    Ok(mut emitted) => {
                        let Some(file_name) = paths.javascript.clone() else {
                            continue;
                        };
                        if let Some(mut source_map) = emitted.source_map {
                            source_map.file = file_name.rsplit('/').next().map(str::to_owned);
                            make_source_map_sources_relative(
                                &mut source_map,
                                &common_source_directory,
                            );
                            let serialized = serialize_source_map(
                                &source_map,
                                self.options.source_root.as_deref(),
                            );
                            if settings.inline_source_map {
                                emitted
                                    .code
                                    .push_str("//# sourceMappingURL=data:application/json;base64,");
                                emitted.code.push_str(&base64_encode(serialized.as_bytes()));
                                emitted.code.push('\n');
                            } else if let Some(map_file_name) = paths.source_map.clone() {
                                emitted.code.push_str("//# sourceMappingURL=");
                                emitted
                                    .code
                                    .push_str(&self.source_map_url(&file_name, &map_file_name));
                                emitted.code.push('\n');
                                output.files.push(OutputFile {
                                    file_name: map_file_name,
                                    text: serialized,
                                });
                            }
                        }
                        output.files.push(OutputFile {
                            file_name,
                            text: emitted.code,
                        });
                    }
                    Err(error) => output
                        .diagnostics
                        .push(emit_diagnostic(source_file, &error)),
                }
            }
            if settings.emit_declarations {
                let Some(declaration_file_name) = paths.declaration.as_deref() else {
                    continue;
                };
                if self.output_overwrites_input(declaration_file_name) {
                    output
                        .diagnostics
                        .push(output_overwrites_input_diagnostic(declaration_file_name));
                    continue;
                }
                if (self.options.isolated_declarations
                    && has_unserializable_isolated_declaration_name(source_file))
                    || has_private_export_type_query(source_file)
                    || has_unserializable_exported_anonymous_class(source_file)
                    || has_unserializable_exported_class_property_type(source_file)
                    || source_file.checking.diagnostics.iter().any(|diagnostic| {
                        matches!(
                            diagnostic.diagnostic.code(),
                            2527 | 2883 | 4023 | 4025 | 4032 | 4081 | 4094 | 4118 | 5088 | 9010
                        )
                    })
                {
                    continue;
                }
                let declaration_node_types =
                    declaration_node_types_for_emit(source_file, self.options.strict_null_checks);
                match emit_declaration_file_with_semantics(
                    &source_file.parse.arena,
                    source_file.parse.source_file,
                    &source_file.file_name,
                    &source_file.source_text,
                    self.options.declaration_map,
                    Some(&source_file.checking.declaration_reachability),
                    Some(&enum_member_values),
                    Some(&source_file.checking.types),
                    Some(&declaration_node_types),
                    Some(&source_file.checking.import_type_references),
                    Some(&source_file.checking.named_type_references),
                    settings.remove_comments,
                    self.options.rewrite_relative_import_extensions,
                ) {
                    Ok(mut emitted) => {
                        let file_name = declaration_file_name.to_owned();
                        let reference_directives =
                            preserved_reference_directives(source_file, &file_name);
                        if !reference_directives.is_empty() {
                            emitted.code.insert_str(0, &reference_directives);
                        }
                        if let Some(mut source_map) = emitted.source_map {
                            source_map.file = file_name.rsplit('/').next().map(str::to_owned);
                            if let Some(map_file_name) = paths.declaration_map.clone() {
                                emitted.code.push_str("//# sourceMappingURL=");
                                emitted.code.push_str(
                                    map_file_name.rsplit('/').next().unwrap_or(&map_file_name),
                                );
                                emitted.code.push('\n');
                                output.files.push(OutputFile {
                                    file_name: map_file_name,
                                    text: serialize_source_map(
                                        &source_map,
                                        self.options.source_root.as_deref(),
                                    ),
                                });
                            }
                        }
                        output.files.push(OutputFile {
                            file_name,
                            text: emitted.code,
                        });
                    }
                    Err(error) => output
                        .diagnostics
                        .push(emit_diagnostic(source_file, &error)),
                }
            }
        }
        suppress_output_path_collisions(
            &mut output,
            &self.current_directory,
            self.case_sensitivity,
        );
        if self.options.emit_bom {
            prepend_emit_bom(&mut output.files);
        }
        if self.options.no_emit_on_error && !output.diagnostics.is_empty() {
            output.files.clear();
        }
        output
    }

    #[allow(clippy::too_many_lines)]
    fn emit_bundle(&self, settings: PrinterSettings) -> EmitOutput {
        let mut output = EmitOutput::default();
        let paths = ts_outputpaths::bundle_output_paths(&self.options, &self.current_directory)
            .expect("outFile was checked before bundle emission");
        let sources = self.bundle_sources();
        let bundle_source_names = sources
            .iter()
            .map(|source| source.file_name.clone())
            .collect::<Vec<_>>();
        let bundle_root = ts_outputpaths::common_source_directory(
            &bundle_source_names,
            &self.current_directory,
            self.case_sensitivity,
        );

        if settings.emit_javascript {
            let mut code = String::new();
            let mut map_builder = settings.source_map.then(SourceMapBuilder::new);
            let mut map_sources = Vec::new();
            let mut amd_generated_name_offsets = BTreeMap::new();
            if let Some(shebang) = sources.iter().find_map(|source| source_shebang(source)) {
                code.push_str(shebang);
                code.push('\n');
            }
            let mut prologues = Vec::new();
            let mut seen_prologues = HashSet::new();
            let has_script_sources = sources
                .iter()
                .any(|source| !source_is_external_module(source));
            for source in sources
                .iter()
                .filter(|source| !source_is_external_module(source))
            {
                for directive in source_prologue_directives(source) {
                    if seen_prologues.insert(directive.to_owned()) {
                        prologues.push(directive.to_owned());
                    }
                }
            }
            if has_script_sources
                && settings.always_strict
                && seen_prologues.insert("use strict".to_owned())
            {
                prologues.insert(0, "use strict".to_owned());
            }
            for directive in &prologues {
                push_bundle_prologue(&mut code, directive);
            }
            let bundle_needs_extends_helper = settings.target < ts_options::ScriptTarget::Es2015
                && !settings.no_emit_helpers
                && sources
                    .iter()
                    .any(|source| source_needs_extends_helper(&source.parse.arena));
            if bundle_needs_extends_helper {
                code.push_str(BUNDLE_EXTENDS_HELPER);
            }
            for (source_index, source) in sources.iter().enumerate() {
                let detached_comment = (settings.module == ModuleKind::Amd
                    && source_is_external_module(source))
                .then(|| bundle_detached_comment(source))
                .flatten();
                if let Some((comment, _)) = &detached_comment {
                    code.push_str(comment);
                }
                let generated_line =
                    u32::try_from(code.bytes().filter(|byte| *byte == b'\n').count())
                        .unwrap_or(u32::MAX);
                let mut source_settings = settings;
                source_settings.source_map = false;
                source_settings.inline_source_map = false;
                source_settings.always_strict = false;
                let enum_member_values = enum_values_for_emit(&source.checking.enum_member_values);
                let enum_access_values = enum_values_for_emit(&source.checking.enum_access_values);
                let amd_dependencies = source
                    .parse
                    .amd_dependencies
                    .iter()
                    .map(|dependency| PrinterAmdDependency {
                        path: &dependency.path,
                        name: dependency.name.as_deref(),
                        comment_start: dependency.range.start.get(),
                        comment_end: dependency.range.end.get(),
                    })
                    .collect::<Vec<_>>();
                let amd_module_name =
                    (matches!(settings.module, ModuleKind::Amd | ModuleKind::System)
                        && source_is_external_module(source))
                    .then(|| {
                        if settings.module == ModuleKind::Amd {
                            amd_bundle_module_name(source, &bundle_root)
                        } else {
                            bundle_declaration_module_name(source, &bundle_root, settings.module)
                        }
                    });
                let amd_module_specifier_rewrites =
                    self.amd_bundle_specifier_rewrites(source, &bundle_root);
                let preserve_const_enums = self.options.preserve_const_enums
                    || self.options.isolated_modules
                    || self.options.verbatim_module_syntax;
                let import_runtime_meanings = import_runtime_meanings_for_emit(
                    source,
                    preserve_const_enums,
                    settings.module == ModuleKind::Amd,
                    &later_top_level_script_variable_names(
                        sources.iter().skip(source_index + 1).copied(),
                    ),
                );
                let emit_context = EmitContext {
                    bindings: &source.binding,
                    amd_module_name: amd_module_name.as_deref(),
                    amd_bundle: true,
                    preemitted_source_prologues: !source_is_external_module(source),
                    preemitted_shebang: source_shebang(source).is_some(),
                    suppress_extends_helper: bundle_needs_extends_helper,
                    preemitted_comment_end: detached_comment.as_ref().map(|(_, end)| *end),
                    preserve_top_of_file_reference_directive: false,
                    amd_dependencies: &amd_dependencies,
                    amd_module_specifier_rewrites: &amd_module_specifier_rewrites,
                    amd_generated_name_offsets: &amd_generated_name_offsets,
                    enum_member_values: &enum_member_values,
                    enum_access_values: &enum_access_values,
                    import_runtime_meanings: &import_runtime_meanings,
                    preserve_const_enums,
                    inline_const_enums: !self.options.isolated_modules
                        && !self.options.verbatim_module_syntax,
                    emit_decorator_metadata: self.options.emit_decorator_metadata,
                    preserve_dynamic_import: matches!(
                        settings.module,
                        ModuleKind::Node16
                            | ModuleKind::Node18
                            | ModuleKind::Node20
                            | ModuleKind::NodeNext
                    ),
                    isolated_modules: self.options.isolated_modules,
                    strict_null_checks: self.options.strict_null_checks,
                    force_use_strict: false,
                    jsx_factory: self.options.jsx_factory.as_deref(),
                    downlevel_iteration: self.options.downlevel_iteration,
                    module_detection: self.options.module_detection,
                };
                match emit_source_file_with_context(
                    &source.parse.arena,
                    source.parse.source_file,
                    &source.file_name,
                    &source.source_text,
                    source_settings,
                    &emit_context,
                ) {
                    Ok(emitted) => {
                        if !emitted.code.is_empty() {
                            if let Some(builder) = &mut map_builder {
                                let source_index =
                                    u32::try_from(map_sources.len()).unwrap_or(u32::MAX);
                                let _ = builder.add_mapping(generated_line, 0, source_index, 0, 0);
                            }
                            map_sources.push(source.file_name.clone());
                            code.push_str(&emitted.code);
                        }
                    }
                    Err(error) => output.diagnostics.push(emit_diagnostic(source, &error)),
                }
                for base in amd_generated_dependency_bases(source) {
                    *amd_generated_name_offsets.entry(base).or_default() += 1;
                }
            }
            if let Some(mut map) = map_builder.map(|builder| builder.finish(None, map_sources)) {
                let Some(file_name) = paths.javascript.as_ref() else {
                    return output;
                };
                map.file = file_name.rsplit('/').next().map(str::to_owned);
                let serialized = serialize_source_map(&map, self.options.source_root.as_deref());
                if settings.inline_source_map {
                    code.push_str("//# sourceMappingURL=data:application/json;base64,");
                    code.push_str(&base64_encode(serialized.as_bytes()));
                    code.push('\n');
                } else if let Some(map_file_name) = paths.source_map.clone() {
                    code.push_str("//# sourceMappingURL=");
                    code.push_str(&self.source_map_url(file_name, &map_file_name));
                    code.push('\n');
                    output.files.push(OutputFile {
                        file_name: map_file_name,
                        text: serialized,
                    });
                }
            }
            if let Some(file_name) = paths.javascript.clone() {
                output.files.push(OutputFile {
                    file_name,
                    text: code,
                });
            }
        }

        if settings.emit_declarations {
            if let Some(declaration_file_name) = paths.declaration.as_deref()
                && self.output_overwrites_input(declaration_file_name)
            {
                output
                    .diagnostics
                    .push(output_overwrites_input_diagnostic(declaration_file_name));
                if self.options.no_emit_on_error {
                    output.files.clear();
                }
                return output;
            }
            let mut code = String::new();
            let mut preserved_references = BTreeSet::new();
            if let Some(declaration_file) = paths.declaration.as_deref() {
                for source in &sources {
                    let lower = source.file_name.to_ascii_lowercase();
                    if lower.ends_with(".d.ts")
                        || lower.ends_with(".d.mts")
                        || lower.ends_with(".d.cts")
                    {
                        continue;
                    }
                    for directive in
                        preserved_reference_directives(source, declaration_file).lines()
                    {
                        if preserved_references.insert(directive.to_owned()) {
                            code.push_str(directive);
                            code.push('\n');
                        }
                    }
                }
            }
            let mut map_builder = self.options.declaration_map.then(SourceMapBuilder::new);
            let mut map_sources = Vec::new();
            for source in &sources {
                let lower = source.file_name.to_ascii_lowercase();
                if lower.ends_with(".d.ts")
                    || lower.ends_with(".d.mts")
                    || lower.ends_with(".d.cts")
                {
                    continue;
                }
                if (self.options.isolated_declarations
                    && has_unserializable_isolated_declaration_name(source))
                    || has_private_export_type_query(source)
                    || has_unserializable_exported_anonymous_class(source)
                    || has_unserializable_exported_class_property_type(source)
                    || source.checking.diagnostics.iter().any(|diagnostic| {
                        matches!(
                            diagnostic.diagnostic.code(),
                            2527 | 2883 | 4023 | 4025 | 4032 | 4081 | 4094 | 5088 | 9010
                        )
                    })
                {
                    continue;
                }
                let generated_line =
                    u32::try_from(code.bytes().filter(|byte| *byte == b'\n').count())
                        .unwrap_or(u32::MAX);
                let enum_member_values = enum_values_for_emit(&source.checking.enum_member_values);
                let declaration_node_types =
                    declaration_node_types_for_emit(source, self.options.strict_null_checks);
                match emit_declaration_file_with_semantics(
                    &source.parse.arena,
                    source.parse.source_file,
                    &source.file_name,
                    &source.source_text,
                    false,
                    Some(&source.checking.declaration_reachability),
                    Some(&enum_member_values),
                    Some(&source.checking.types),
                    Some(&declaration_node_types),
                    Some(&source.checking.import_type_references),
                    Some(&source.checking.named_type_references),
                    settings.remove_comments,
                    self.options.rewrite_relative_import_extensions,
                ) {
                    Ok(mut emitted) => {
                        if !emitted.code.is_empty() {
                            if let Some(builder) = &mut map_builder {
                                let source_index =
                                    u32::try_from(map_sources.len()).unwrap_or(u32::MAX);
                                let _ = builder.add_mapping(generated_line, 0, source_index, 0, 0);
                            }
                            map_sources.push(source.file_name.clone());
                            if source_is_external_module(source) {
                                emitted.code = self.rewrite_bundle_declaration_specifiers(
                                    source,
                                    &emitted.code,
                                    &bundle_root,
                                    settings.module,
                                );
                                emitted.code = self.prefer_bundle_declaration_imports(
                                    source,
                                    &emitted.code,
                                    &bundle_root,
                                    settings.module,
                                );
                                emitted.code = self.rewrite_late_bundle_export_references(
                                    source,
                                    &emitted.code,
                                    &bundle_root,
                                    settings.module,
                                );
                                emitted.code =
                                    remove_unused_named_declaration_imports(&emitted.code);
                                emitted.code = defer_export_only_bundle_imports(&emitted.code);
                                append_bundle_declaration_module(
                                    &mut code,
                                    source,
                                    &emitted.code,
                                    &bundle_declaration_module_name(
                                        source,
                                        &bundle_root,
                                        settings.module,
                                    ),
                                    settings.module == ModuleKind::Amd,
                                );
                            } else {
                                code.push_str(&emitted.code);
                            }
                        }
                    }
                    Err(error) => output.diagnostics.push(emit_diagnostic(source, &error)),
                }
            }
            if let Some(mut map) = map_builder.map(|builder| builder.finish(None, map_sources)) {
                let Some(file_name) = paths.declaration.as_ref() else {
                    return output;
                };
                map.file = file_name.rsplit('/').next().map(str::to_owned);
                if let Some(map_file_name) = paths.declaration_map.clone() {
                    code.push_str("//# sourceMappingURL=");
                    code.push_str(map_file_name.rsplit('/').next().unwrap_or(&map_file_name));
                    code.push('\n');
                    output.files.push(OutputFile {
                        file_name: map_file_name,
                        text: serialize_source_map(&map, self.options.source_root.as_deref()),
                    });
                }
            }
            if let Some(file_name) = paths.declaration.clone() {
                output.files.push(OutputFile {
                    file_name,
                    text: code,
                });
            }
        }

        if self.options.emit_bom {
            prepend_emit_bom(&mut output.files);
        }
        if self.options.no_emit_on_error && !output.diagnostics.is_empty() {
            output.files.clear();
        }
        output
    }

    fn bundle_sources(&self) -> Vec<&SourceFile> {
        fn visit(
            program: &Program,
            index: usize,
            visited: &mut BTreeSet<usize>,
            ordered: &mut Vec<usize>,
        ) {
            if !visited.insert(index) {
                return;
            }
            let source = &program.source_files[index];
            let canonical = canonicalize(
                &source.file_name,
                &program.current_directory,
                program.case_sensitivity,
            );
            for ((containing, _), target) in &program.resolved_modules {
                if containing != &canonical {
                    continue;
                }
                if let Some(target) = program.file_index.get(target) {
                    visit(program, *target, visited, ordered);
                }
            }
            if !source.is_default_library
                && !ts_path::is_declaration_file(&source.file_name)
                && program.source_should_emit(source)
            {
                ordered.push(index);
            }
        }

        let mut visited = BTreeSet::new();
        let mut ordered = Vec::new();
        for index in 0..self.source_files.len() {
            visit(self, index, &mut visited, &mut ordered);
        }
        ordered
            .into_iter()
            .map(|index| &self.source_files[index])
            .collect()
    }

    fn source_should_emit(&self, source: &SourceFile) -> bool {
        let canonical = canonicalize(
            &source.file_name,
            &self.current_directory,
            self.case_sensitivity,
        );
        self.root_file_names.contains(&canonical)
            || !canonical
                .split('/')
                .any(|component| component.eq_ignore_ascii_case("node_modules"))
    }

    fn output_overwrites_input(&self, file_name: &str) -> bool {
        let canonical = canonicalize(file_name, &self.current_directory, self.case_sensitivity);
        self.file_index.contains_key(&canonical)
    }

    fn amd_bundle_specifier_rewrites(
        &self,
        source: &SourceFile,
        bundle_root: &str,
    ) -> BTreeMap<String, String> {
        let containing = canonicalize(
            &source.file_name,
            &self.current_directory,
            self.case_sensitivity,
        );
        self.resolved_modules
            .iter()
            .filter(|((source, _), _)| source == &containing)
            .filter_map(|((_, specifier), target)| {
                let target = self
                    .file_index
                    .get(target)
                    .and_then(|index| self.source_files.get(*index))?;
                Some((
                    specifier.clone(),
                    amd_bundle_module_name(target, bundle_root),
                ))
            })
            .collect()
    }

    fn source_map_url(&self, generated_file: &str, map_file: &str) -> String {
        let Some(map_root) = self.options.map_root.as_deref() else {
            return map_file.rsplit('/').next().unwrap_or(map_file).to_owned();
        };
        let map_root = if is_absolute(map_root) {
            ts_path::normalize_path(map_root)
        } else {
            resolve_path(&self.current_directory, &[map_root])
        };
        let relative_map = self
            .options
            .out_dir
            .as_deref()
            .and_then(|out_dir| strip_directory_prefix(map_file, out_dir))
            .unwrap_or_else(|| map_file.rsplit('/').next().unwrap_or(map_file).to_owned());
        let logical_map = resolve_path(&map_root, &[&relative_map]);
        relative_path(&directory_path(generated_file), &logical_map)
    }

    fn rewrite_bundle_declaration_specifiers(
        &self,
        source: &SourceFile,
        declaration: &str,
        bundle_root: &str,
        module: ModuleKind,
    ) -> String {
        let containing = canonicalize(
            &source.file_name,
            &self.current_directory,
            self.case_sensitivity,
        );
        self.resolved_modules
            .iter()
            .filter(|((source, _), _)| source == &containing)
            .filter_map(|((_, specifier), target)| {
                let target = self
                    .file_index
                    .get(target)
                    .and_then(|index| self.source_files.get(*index))?;
                if !self.source_should_emit(target) {
                    return None;
                }
                Some((
                    specifier,
                    bundle_declaration_module_name(target, bundle_root, module),
                ))
            })
            .fold(
                declaration.to_owned(),
                |declaration, (specifier, target)| {
                    declaration
                        .replace(&format!("\"{specifier}\""), &format!("\"{target}\""))
                        .replace(&format!("'{specifier}'"), &format!("\"{target}\""))
                },
            )
    }

    fn prefer_bundle_declaration_imports(
        &self,
        source: &SourceFile,
        declaration: &str,
        bundle_root: &str,
        module: ModuleKind,
    ) -> String {
        let Some(NodeData::SourceFile(file)) = source
            .parse
            .arena
            .get(source.parse.source_file)
            .map(|node| &node.data)
        else {
            return declaration.to_owned();
        };
        let containing = canonicalize(
            &source.file_name,
            &self.current_directory,
            self.case_sensitivity,
        );
        let mut declaration = declaration.to_owned();
        let mut imports = Vec::new();
        for statement in &file.statements.nodes {
            let Some(NodeData::ImportDeclaration(import)) =
                source.parse.arena.get(*statement).map(|node| &node.data)
            else {
                continue;
            };
            let Some((specifier, _)) = string_literal(&source.parse.arena, import.module_specifier)
            else {
                continue;
            };
            let Some(target) = self
                .resolved_modules
                .get(&(containing.clone(), specifier))
                .and_then(|target| self.file_index.get(target))
                .and_then(|index| self.source_files.get(*index))
            else {
                continue;
            };
            let target = bundle_declaration_module_name(target, bundle_root, module);
            let Some(NodeData::ImportClause(clause)) = import
                .import_clause
                .and_then(|clause| source.parse.arena.get(clause))
                .map(|node| &node.data)
            else {
                continue;
            };
            if let Some(local) = clause
                .name
                .and_then(|name| identifier_text(&source.parse.arena, name))
                && replace_import_type_reference(&mut declaration, &target, "default", local)
            {
                imports.push(format!("import {local} from \"{target}\";"));
            }
            let Some(NodeData::NamedImports(named)) = clause
                .named_bindings
                .and_then(|bindings| source.parse.arena.get(bindings))
                .map(|node| &node.data)
            else {
                continue;
            };
            let mut retained = Vec::new();
            for element in &named.elements.nodes {
                let Some(NodeData::ImportSpecifier(import)) =
                    source.parse.arena.get(*element).map(|node| &node.data)
                else {
                    continue;
                };
                let Some(local) = identifier_text(&source.parse.arena, import.name) else {
                    continue;
                };
                let imported = import
                    .property_name
                    .and_then(|name| identifier_text(&source.parse.arena, name))
                    .unwrap_or(local);
                if replace_import_type_reference(&mut declaration, &target, imported, local) {
                    retained.push(if imported == local {
                        local.to_owned()
                    } else {
                        format!("{imported} as {local}")
                    });
                }
            }
            if !retained.is_empty() {
                imports.push(format!(
                    "import {{ {} }} from \"{target}\";",
                    retained.join(", ")
                ));
            }
        }
        if imports.is_empty() {
            declaration
        } else {
            imports.sort();
            imports.dedup();
            format!("{}\n{declaration}", imports.join("\n"))
        }
    }

    fn rewrite_late_bundle_export_references(
        &self,
        source: &SourceFile,
        declaration: &str,
        bundle_root: &str,
        module: ModuleKind,
    ) -> String {
        let source_module = bundle_declaration_module_name(source, bundle_root, module);
        let source_directory = source_module
            .rsplit_once('/')
            .map_or("", |(directory, _)| directory);
        source
            .checking
            .import_type_references
            .values()
            .filter(|reference| module_name_is_relative(&reference.module_specifier))
            .fold(declaration.to_owned(), |declaration, reference| {
                let resolved = resolve_path(
                    "/",
                    &[source_directory, reference.module_specifier.as_str()],
                );
                let resolved = resolved.trim_start_matches('/');
                let Some(target) = self.source_files.iter().find(|candidate| {
                    bundle_declaration_module_name(candidate, bundle_root, module) == resolved
                        && candidate
                            .binding
                            .exports
                            .get(&reference.qualifier)
                            .is_some()
                }) else {
                    return declaration;
                };
                let target_canonical = canonicalize(
                    &target.file_name,
                    &self.current_directory,
                    self.case_sensitivity,
                );
                let target_directory = directory_path(&target.file_name);
                let Some(barrel) = self.source_files.iter().find(|candidate| {
                    directory_path(&candidate.file_name) == target_directory
                        && ts_path::base_file_name(ts_path::remove_file_extension(
                            &candidate.file_name,
                        )) == "index"
                        && self.source_reexports_target(candidate, &target_canonical)
                }) else {
                    return declaration;
                };
                let barrel = bundle_declaration_module_name(barrel, bundle_root, module);
                let preferred = barrel.strip_suffix("/index").unwrap_or(&barrel);
                if preferred.is_empty() {
                    return declaration;
                }
                declaration.replace(
                    &format!(
                        "import(\"{}\").{}",
                        reference.module_specifier, reference.qualifier
                    ),
                    &format!("import(\"{preferred}\").{}", reference.qualifier),
                )
            })
    }

    fn source_reexports_target(&self, source: &SourceFile, target: &str) -> bool {
        let containing = canonicalize(
            &source.file_name,
            &self.current_directory,
            self.case_sensitivity,
        );
        self.resolved_modules
            .iter()
            .any(|((owner, specifier), resolved)| {
                owner == &containing
                    && resolved == target
                    && source.parse.arena.iter().any(|(_, node)| {
                        matches!(
                            &node.data,
                            NodeData::ExportDeclaration(export)
                                if export.export_clause.is_none()
                                    && export.module_specifier.is_some_and(|module| {
                                        string_literal(&source.parse.arena, module)
                                            .is_some_and(|(text, _)| &text == specifier)
                                    })
                        )
                    })
            })
    }

    fn check_program(&mut self) {
        let module_maps = self
            .source_files
            .iter()
            .map(|source_file| {
                let containing = canonicalize(
                    &source_file.file_name,
                    &self.current_directory,
                    self.case_sensitivity,
                );
                self.resolved_modules
                    .iter()
                    .filter_map(|((source, specifier), target)| {
                        (source == &containing).then(|| {
                            self.file_index
                                .get(target)
                                .map(|index| (specifier.clone(), *index))
                        })?
                    })
                    .collect::<BTreeMap<_, _>>()
            })
            .collect::<Vec<_>>();
        let checked = {
            let source_paths = self
                .source_files
                .iter()
                .map(|source_file| source_file.file_name.clone())
                .collect::<Vec<_>>();
            let inputs = self
                .source_files
                .iter()
                .zip(&module_maps)
                .map(|(source_file, resolved_modules)| ProgramSource {
                    arena: &source_file.parse.arena,
                    source_file: source_file.parse.source_file,
                    bindings: &source_file.binding,
                    resolved_modules,
                    is_default_library: source_file.is_default_library,
                    skip_diagnostics: self.options.no_check
                        || (self.options.skip_lib_check
                            && ts_path::is_declaration_file(&source_file.file_name)),
                    checker_options: CheckerOptions {
                        allow_unreachable_code: self.options.allow_unreachable_code,
                        exact_optional_property_types: self.options.exact_optional_property_types,
                        is_declaration_file: ts_path::is_declaration_file(&source_file.file_name),
                        is_javascript_file: matches!(
                            ts_path::script_kind_from_path(&source_file.file_name),
                            ts_path::ScriptKind::Js | ts_path::ScriptKind::Jsx
                        ),
                        no_fallthrough_cases_in_switch: self.options.no_fallthrough_cases_in_switch,
                        strict_null_checks: self.options.strict_null_checks,
                        no_implicit_any: self.options.no_implicit_any,
                        no_implicit_returns: self.options.no_implicit_returns,
                        no_unused_locals: self.options.no_unused_locals,
                        no_unused_parameters: self.options.no_unused_parameters,
                        use_unknown_in_catch_variables: self.options.use_unknown_in_catch_variables,
                    },
                })
                .collect::<Vec<_>>();
            check_program_with_paths(&inputs, &source_paths)
        };
        let check_declaration_portability = self.options.declaration && !self.options.no_check;
        let portability_diagnostics = if check_declaration_portability {
            self.declaration_portability_diagnostics()
        } else {
            vec![Vec::new(); self.source_files.len()]
        };
        for (index, (source_file, mut checking)) in
            self.source_files.iter_mut().zip(checked.files).enumerate()
        {
            if check_declaration_portability {
                add_nonportable_inferred_type_diagnostics(source_file, &mut checking);
            }
            checking
                .diagnostics
                .extend(portability_diagnostics[index].iter().cloned());
            if self.options.no_check {
                checking.diagnostics.clear();
            }
            for diagnostic in &checking.diagnostics {
                let range = source_file
                    .parse
                    .arena
                    .get(diagnostic.node)
                    .map(|node| node.range);
                self.diagnostics.push(ProgramDiagnostic {
                    file_name: Some(source_file.file_name.clone()),
                    range,
                    code: Some(diagnostic.diagnostic.code()),
                    message: diagnostic
                        .diagnostic
                        .render()
                        .unwrap_or_else(|error| error.to_string()),
                });
            }
            source_file.checking = checking;
        }
    }

    fn declaration_portability_diagnostics(&self) -> Vec<Vec<CheckDiagnostic>> {
        let mut diagnostics = self.nonportable_nested_package_diagnostics();
        for (target, additional) in diagnostics
            .iter_mut()
            .zip(self.unserializable_mapped_import_diagnostics())
        {
            target.extend(additional);
        }
        diagnostics
    }

    #[allow(clippy::too_many_lines)]
    fn nonportable_nested_package_diagnostics(&self) -> Vec<Vec<CheckDiagnostic>> {
        let mut diagnostics = vec![Vec::new(); self.source_files.len()];
        for (source_index, source) in self.source_files.iter().enumerate() {
            let containing = canonicalize(
                &source.file_name,
                &self.current_directory,
                self.case_sensitivity,
            );
            let imports = source_import_bindings(source);
            let Some(NodeData::SourceFile(file)) = source
                .parse
                .arena
                .get(source.parse.source_file)
                .map(|node| &node.data)
            else {
                continue;
            };
            for statement in &file.statements.nodes {
                if let Some(diagnostic) = self.nonportable_default_export_assignment_diagnostic(
                    source,
                    &containing,
                    &imports,
                    *statement,
                ) {
                    diagnostics[source_index].push(diagnostic);
                    continue;
                }
                let Some(NodeData::VariableStatement(variable)) =
                    source.parse.arena.get(*statement).map(|node| &node.data)
                else {
                    continue;
                };
                if !node_has_modifier(
                    &source.parse.arena,
                    variable.modifiers.as_ref(),
                    ts_ast::SyntaxKind::ExportKeyword,
                ) {
                    continue;
                }
                let Some(NodeData::VariableDeclarationList(list)) = source
                    .parse
                    .arena
                    .get(variable.declaration_list)
                    .map(|node| &node.data)
                else {
                    continue;
                };
                for declaration_id in &list.declarations.nodes {
                    let Some(NodeData::VariableDeclaration(declaration)) = source
                        .parse
                        .arena
                        .get(*declaration_id)
                        .map(|node| &node.data)
                    else {
                        continue;
                    };
                    if declaration.type_.is_some() {
                        continue;
                    }
                    let Some(NodeData::CallExpression(call)) = declaration
                        .initializer
                        .and_then(|initializer| source.parse.arena.get(initializer))
                        .map(|node| &node.data)
                    else {
                        continue;
                    };
                    let Some(callee) = identifier_text(&source.parse.arena, call.expression) else {
                        continue;
                    };
                    let Some((_, imported_name, specifier)) =
                        imports.iter().find(|(local, _, _)| local == callee)
                    else {
                        continue;
                    };
                    let Some(target_name) = self
                        .resolved_modules
                        .get(&(containing.clone(), specifier.clone()))
                    else {
                        continue;
                    };
                    let Some(target) = self
                        .file_index
                        .get(target_name)
                        .and_then(|index| self.source_files.get(*index))
                    else {
                        continue;
                    };
                    let Some((qualifier, module)) =
                        nonportable_return_import(self, target, imported_name)
                    else {
                        continue;
                    };
                    let Some(name) = identifier_text(&source.parse.arena, declaration.name) else {
                        continue;
                    };
                    let message =
                        message_by_code(2883).expect("TS2883 must be in the diagnostic catalog");
                    diagnostics[source_index].push(CheckDiagnostic {
                        node: declaration.name,
                        diagnostic: Diagnostic::with_arguments(
                            message,
                            [name.to_owned(), qualifier, module],
                        ),
                    });
                }
            }
        }
        diagnostics
    }

    fn nonportable_default_export_assignment_diagnostic(
        &self,
        source: &SourceFile,
        containing: &str,
        imports: &[(String, String, String)],
        statement: NodeId,
    ) -> Option<CheckDiagnostic> {
        let NodeData::ExportAssignment(export) = &source.parse.arena.get(statement)?.data else {
            return None;
        };
        if export.is_export_equals || !export_assignment_is_object_assign(source, export.expression)
        {
            return None;
        }
        let (_, _, specifier) = imports
            .iter()
            .find(|(_, imported, _)| imported == "default")?;
        let target_name = self
            .resolved_modules
            .get(&(containing.to_owned(), specifier.clone()))?;
        let target = self
            .file_index
            .get(target_name)
            .and_then(|index| self.source_files.get(*index))?;
        let (qualifier, module) = nested_namespace_import_reference(self, target)?;
        let message = message_by_code(2883).expect("TS2883 must be in the diagnostic catalog");
        Some(CheckDiagnostic {
            node: statement,
            diagnostic: Diagnostic::with_arguments(message, ["default".into(), qualifier, module]),
        })
    }

    fn unserializable_mapped_import_diagnostics(&self) -> Vec<Vec<CheckDiagnostic>> {
        let mut diagnostics = vec![Vec::new(); self.source_files.len()];
        for (source_index, source) in self.source_files.iter().enumerate() {
            let containing = canonicalize(
                &source.file_name,
                &self.current_directory,
                self.case_sensitivity,
            );
            let imports = source_import_bindings(source);
            let Some(NodeData::SourceFile(file)) = source
                .parse
                .arena
                .get(source.parse.source_file)
                .map(|node| &node.data)
            else {
                continue;
            };
            for statement in &file.statements.nodes {
                let Some(NodeData::VariableStatement(variable)) =
                    source.parse.arena.get(*statement).map(|node| &node.data)
                else {
                    continue;
                };
                if !node_has_modifier(
                    &source.parse.arena,
                    variable.modifiers.as_ref(),
                    ts_ast::SyntaxKind::ExportKeyword,
                ) {
                    continue;
                }
                let Some(NodeData::VariableDeclarationList(list)) = source
                    .parse
                    .arena
                    .get(variable.declaration_list)
                    .map(|node| &node.data)
                else {
                    continue;
                };
                for declaration_id in &list.declarations.nodes {
                    let Some(NodeData::VariableDeclaration(declaration)) = source
                        .parse
                        .arena
                        .get(*declaration_id)
                        .map(|node| &node.data)
                    else {
                        continue;
                    };
                    if declaration.type_.is_some() {
                        continue;
                    }
                    let Some((local, member)) = declaration
                        .initializer
                        .and_then(|initializer| imported_call_target(source, initializer))
                    else {
                        continue;
                    };
                    let Some((_, imported, specifier)) =
                        imports.iter().find(|(candidate, _, _)| candidate == &local)
                    else {
                        continue;
                    };
                    let imported = if imported == "*" {
                        let Some(member) = member.as_deref() else {
                            continue;
                        };
                        member
                    } else {
                        imported
                    };
                    let Some(target_name) = self
                        .resolved_modules
                        .get(&(containing.clone(), specifier.clone()))
                    else {
                        continue;
                    };
                    let Some(target) = self
                        .file_index
                        .get(target_name)
                        .and_then(|index| self.source_files.get(*index))
                    else {
                        continue;
                    };
                    let Some(property) = imported_function_mapped_symbol_property(target, imported)
                    else {
                        continue;
                    };
                    let message =
                        message_by_code(4118).expect("TS4118 must be in the diagnostic catalog");
                    diagnostics[source_index].push(CheckDiagnostic {
                        node: declaration.name,
                        diagnostic: Diagnostic::with_arguments(message, [format!("[{property}]")]),
                    });
                }
            }
        }
        diagnostics
    }

    fn load_file(&mut self, file_system: &dyn FileSystem, file_name: &str, report_missing: bool) {
        let canonical = canonicalize(file_name, &self.current_directory, self.case_sensitivity);
        if self.file_index.contains_key(&canonical) {
            return;
        }
        let Ok(source_text) = file_system.read_file(file_name) else {
            if report_missing {
                self.diagnostics.push(missing_file_diagnostic(file_name));
            }
            return;
        };
        let is_jsx = Path::new(file_name).extension().is_some_and(|extension| {
            extension.eq_ignore_ascii_case("tsx") || extension.eq_ignore_ascii_case("jsx")
        });
        let parse = if is_jsx {
            parse_jsx_source_file(&source_text)
        } else {
            parse_source_file(&source_text)
        };
        for diagnostic in &parse.diagnostics {
            self.diagnostics.push(ProgramDiagnostic {
                file_name: Some(file_name.to_owned()),
                range: Some(diagnostic.range),
                code: diagnostic.code,
                message: diagnostic.message.clone(),
            });
        }
        let binding = bind_source_file(&parse.arena, parse.source_file);
        for diagnostic in &binding.diagnostics {
            let range = parse.arena.get(diagnostic.node).map(|node| node.range);
            self.diagnostics.push(ProgramDiagnostic {
                file_name: Some(file_name.to_owned()),
                range,
                code: Some(diagnostic.diagnostic.code()),
                message: diagnostic
                    .diagnostic
                    .render()
                    .unwrap_or_else(|error| error.to_string()),
            });
        }
        let checking = empty_check_result();
        let index = self.source_files.len();
        self.file_index.insert(canonical, index);
        self.source_files.push(SourceFile {
            file_name: file_name.to_owned(),
            source_text,
            parse,
            binding,
            checking,
            is_default_library: false,
            implied_node_format: implied_node_format(file_system, file_name),
        });
    }

    fn load_default_libraries(&mut self) {
        if self.options.no_lib {
            return;
        }
        let roots = match &self.options.lib {
            None => vec![ts_bundled::default_library_name(self.options.target).to_owned()],
            Some(libraries) => libraries
                .iter()
                .map(|name| bundled_library_name(name))
                .collect(),
        };
        for root in roots {
            for library_name in ts_bundled::library_closure(&root) {
                self.load_bundled_library(library_name);
            }
        }
    }

    fn load_automatic_type_directives(
        &mut self,
        file_system: &dyn FileSystem,
        resolution_options: &ResolutionOptions,
    ) {
        let names = automatic_type_directive_names(
            file_system,
            resolution_options,
            &self.current_directory,
        );
        if names.is_empty() {
            return;
        }
        let resolver = Resolver::new(file_system, resolution_options.clone());
        let containing_file =
            resolve_path(&self.current_directory, &["__inferred type names__.ts"]);
        for name in names {
            if let Some(resolved) = resolver
                .resolve_type_reference(&name, &containing_file)
                .resolved
            {
                self.load_file(file_system, &resolved.resolved_file_name, false);
            } else if resolution_options
                .types
                .as_ref()
                .is_some_and(|types| types.iter().any(|entry| entry == &name))
            {
                self.diagnostics.push(type_definition_not_found(&name));
            }
        }
    }

    fn load_reference_directives(
        &mut self,
        file_system: &dyn FileSystem,
        resolution_options: &ResolutionOptions,
    ) {
        let resolver = Resolver::new(file_system, resolution_options.clone());
        let mut file_index = 0;
        while file_index < self.source_files.len() {
            if self.source_files[file_index].is_default_library {
                file_index += 1;
                continue;
            }
            let containing_file = self.source_files[file_index].file_name.clone();
            let directives = reference_directives(&self.source_files[file_index].source_text);
            for directive in directives {
                match directive.kind {
                    ReferenceKind::Path => {
                        let file_name = resolve_path(
                            &directory_path(&containing_file),
                            &[directive.value.as_str()],
                        );
                        self.load_file(file_system, &file_name, true);
                    }
                    ReferenceKind::Types => {
                        if let Some(resolved) = resolver
                            .resolve_type_reference(&directive.value, &containing_file)
                            .resolved
                        {
                            self.load_file(file_system, &resolved.resolved_file_name, false);
                        } else {
                            self.diagnostics
                                .push(type_definition_not_found(&directive.value));
                        }
                    }
                    ReferenceKind::Lib => {
                        let library_name = bundled_library_name(&directive.value);
                        for dependency in ts_bundled::library_closure(&library_name) {
                            self.load_bundled_library(dependency);
                        }
                    }
                }
            }
            file_index += 1;
        }
    }

    fn load_bundled_library(&mut self, library_name: &str) {
        let file_name = format!("/__typescript/lib/{library_name}");
        let canonical = canonicalize(&file_name, &self.current_directory, self.case_sensitivity);
        if self.file_index.contains_key(&canonical) {
            return;
        }
        let Some(source) = ts_bundled::library(library_name) else {
            return;
        };
        let source_text = source.to_owned();
        let parse = parse_source_file(&source_text);
        let binding = bind_source_file(&parse.arena, parse.source_file);
        let checking = empty_check_result();
        let index = self.source_files.len();
        self.file_index.insert(canonical, index);
        self.source_files.push(SourceFile {
            file_name,
            source_text,
            parse,
            binding,
            checking,
            is_default_library: true,
            implied_node_format: ModuleKind::CommonJs,
        });
    }
}

fn implied_node_format(file_system: &dyn FileSystem, file_name: &str) -> ModuleKind {
    let extension = Path::new(file_name)
        .extension()
        .and_then(|value| value.to_str());
    if extension.is_some_and(|extension| {
        extension.eq_ignore_ascii_case("mts") || extension.eq_ignore_ascii_case("mjs")
    }) {
        return ModuleKind::EsNext;
    }
    if extension.is_some_and(|extension| {
        extension.eq_ignore_ascii_case("cts") || extension.eq_ignore_ascii_case("cjs")
    }) {
        return ModuleKind::CommonJs;
    }
    let mut directory = directory_path(file_name);
    loop {
        let package_json = resolve_path(&directory, &["package.json"]);
        if file_system.file_exists(&package_json) {
            return file_system
                .read_file(&package_json)
                .ok()
                .and_then(|contents| parse_package_json(&contents).ok())
                .and_then(|package| package.package_type)
                .filter(|package_type| package_type == "module")
                .map_or(ModuleKind::CommonJs, |_| ModuleKind::EsNext);
        }
        let parent = directory_path(&directory);
        if parent == directory {
            break;
        }
        directory = parent;
    }
    ModuleKind::CommonJs
}

#[derive(Clone, Copy)]
enum ReferenceKind {
    Path,
    Types,
    Lib,
}

struct ReferenceDirective {
    kind: ReferenceKind,
    value: String,
}

fn reference_directives(source: &str) -> Vec<ReferenceDirective> {
    source
        .lines()
        .filter_map(|line| {
            let reference = line
                .trim_start()
                .strip_prefix("///")?
                .trim_start()
                .strip_prefix("<reference")?;
            [
                (ReferenceKind::Types, "types"),
                (ReferenceKind::Lib, "lib"),
                (ReferenceKind::Path, "path"),
            ]
            .into_iter()
            .find_map(|(kind, name)| {
                reference_attribute(reference, name).map(|value| ReferenceDirective { kind, value })
            })
        })
        .collect()
}

fn has_no_default_lib_directive(source: &str) -> bool {
    source.lines().any(|line| {
        line.trim_start()
            .strip_prefix("///")
            .and_then(|line| line.trim_start().strip_prefix("<reference"))
            .and_then(|reference| reference_attribute(reference, "no-default-lib"))
            .is_some_and(|value| value.eq_ignore_ascii_case("true"))
    })
}

fn reference_attribute(reference: &str, name: &str) -> Option<String> {
    let mut rest = reference;
    while let Some(index) = rest.find(name) {
        let candidate = &rest[index + name.len()..];
        let candidate = candidate.trim_start();
        if let Some(candidate) = candidate.strip_prefix('=') {
            let candidate = candidate.trim_start();
            let quote = candidate.chars().next()?;
            if matches!(quote, '\'' | '"') {
                let value = &candidate[quote.len_utf8()..];
                return value.find(quote).map(|end| value[..end].to_owned());
            }
        }
        rest = &candidate[candidate
            .char_indices()
            .nth(1)
            .map_or(candidate.len(), |(i, _)| i)..];
    }
    None
}

fn bundled_library_name(name: &str) -> String {
    let name = name.to_ascii_lowercase();
    if name.starts_with("lib.") && name.ends_with(".d.ts") {
        name
    } else {
        format!("lib.{name}.d.ts")
    }
}

fn serialize_source_map(source_map: &SourceMap, source_root: Option<&str>) -> String {
    #[derive(serde::Serialize)]
    #[serde(rename_all = "camelCase")]
    struct SerializedSourceMap<'a> {
        version: u8,
        file: &'a Option<String>,
        source_root: &'a str,
        sources: &'a [String],
        names: &'a [String],
        mappings: &'a str,
    }

    let source_root = source_root.map_or_else(String::new, |source_root| {
        if source_root.is_empty() || source_root.ends_with('/') {
            source_root.to_owned()
        } else {
            format!("{source_root}/")
        }
    });
    serde_json::to_string(&SerializedSourceMap {
        version: source_map.version,
        file: &source_map.file,
        source_root: &source_root,
        sources: &source_map.sources,
        names: &source_map.names,
        mappings: &source_map.mappings,
    })
    .expect("source map fields are JSON-serializable")
}

fn make_source_map_sources_relative(source_map: &mut SourceMap, source_directory: &str) {
    for source in &mut source_map.sources {
        *source =
            strip_directory_prefix(source, source_directory).unwrap_or_else(|| source.clone());
    }
}

fn strip_directory_prefix(path: &str, directory: &str) -> Option<String> {
    let path = ts_path::normalize_path(path);
    let directory = ts_path::normalize_path(directory);
    let remainder = path.strip_prefix(&directory)?;
    if remainder.is_empty() {
        Some(String::new())
    } else {
        remainder.strip_prefix('/').map(str::to_owned)
    }
}

fn relative_path(from_directory: &str, target: &str) -> String {
    let from = ts_path::normalize_path(from_directory);
    let target = ts_path::normalize_path(target);
    let from_parts = from.trim_start_matches('/').split('/').collect::<Vec<_>>();
    let target_parts = target
        .trim_start_matches('/')
        .split('/')
        .collect::<Vec<_>>();
    let common = from_parts
        .iter()
        .zip(&target_parts)
        .take_while(|(left, right)| left == right)
        .count();
    let mut parts = vec![".."; from_parts.len().saturating_sub(common)];
    parts.extend(target_parts[common..].iter().copied());
    if parts.is_empty() {
        ".".to_owned()
    } else {
        parts.join("/")
    }
}

fn preserved_reference_directives(source: &SourceFile, declaration_file: &str) -> String {
    let source_directory = directory_path(&source.file_name);
    let declaration_directory = directory_path(declaration_file);
    let mut output = String::new();
    for line in source.source_text.lines() {
        let trimmed = line.trim_start();
        if !trimmed.starts_with("///")
            || !trimmed.contains("<reference")
            || !(trimmed.contains("preserve=\"true\"") || trimmed.contains("preserve='true'"))
        {
            continue;
        }
        if let Some(reference) = preserved_reference_value(trimmed, "types") {
            output.push_str("/// <reference types=\"");
            output.push_str(reference);
            output.push('"');
            if let Some(mode) = preserved_reference_value(trimmed, "resolution-mode") {
                output.push_str(" resolution-mode=\"");
                output.push_str(mode);
                output.push('"');
            }
            output.push_str(" preserve=\"true\" />\n");
            continue;
        }
        if let Some(reference) = preserved_reference_value(trimmed, "lib") {
            output.push_str("/// <reference lib=\"");
            output.push_str(reference);
            output.push_str("\" preserve=\"true\" />\n");
            continue;
        }
        let Some(reference) = preserved_reference_value(trimmed, "path") else {
            continue;
        };
        let target = resolve_path(&source_directory, &[reference]);
        let target = change_extension(&target, declaration_emit_extension(&target));
        let rewritten = relative_path(&declaration_directory, &target);
        output.push_str("/// <reference path=\"");
        output.push_str(&rewritten);
        output.push_str("\" preserve=\"true\" />\n");
    }
    output
}

fn preserved_reference_value<'a>(directive: &'a str, attribute: &str) -> Option<&'a str> {
    let start = directive.find(&format!("{attribute}="))? + attribute.len() + 1;
    let quote = directive.as_bytes().get(start).copied().map(char::from)?;
    if !matches!(quote, '\'' | '"') {
        return None;
    }
    let value_start = start + 1;
    let value_end = directive[value_start..].find(quote)? + value_start;
    Some(&directive[value_start..value_end])
}

fn has_unserializable_isolated_declaration_name(source: &SourceFile) -> bool {
    source.parse.arena.iter().any(|(_, node)| {
        let NodeData::ComputedPropertyName(name) = &node.data else {
            return false;
        };
        let Some(expression) = source.parse.arena.get(name.expression) else {
            return true;
        };
        match &expression.data {
            NodeData::NumericLiteral(_)
            | NodeData::StringLiteral(_)
            | NodeData::NoSubstitutionTemplateLiteral(_) => false,
            NodeData::PrefixUnaryExpression(prefix) => !matches!(
                source
                    .parse
                    .arena
                    .get(prefix.operand)
                    .map(|operand| &operand.data),
                Some(NodeData::NumericLiteral(_))
            ),
            _ => true,
        }
    }) || source.parse.arena.iter().any(|(_, node)| {
        let NodeData::VariableStatement(statement) = &node.data else {
            return false;
        };
        if !node_has_modifier(
            &source.parse.arena,
            statement.modifiers.as_ref(),
            ts_ast::SyntaxKind::ExportKeyword,
        ) {
            return false;
        }
        let Some(NodeData::VariableDeclarationList(list)) = source
            .parse
            .arena
            .get(statement.declaration_list)
            .map(|node| &node.data)
        else {
            return false;
        };
        list.declarations.nodes.iter().any(|declaration| {
            matches!(
                source.parse.arena.get(*declaration).map(|node| &node.data),
                Some(NodeData::VariableDeclaration(variable))
                    if variable.type_.is_none()
                        && variable.initializer.is_some_and(|initializer| matches!(
                            source.parse.arena.get(initializer).map(|node| &node.data),
                            Some(NodeData::PropertyAccessExpression(_)
                                | NodeData::ElementAccessExpression(_)
                                | NodeData::CallExpression(_)
                                | NodeData::NewExpression(_))
                        ))
            )
        })
    })
}

fn has_private_export_type_query(source: &SourceFile) -> bool {
    source.parse.arena.iter().any(|(query_id, node)| {
        let NodeData::TypeQueryNode(query) = &node.data else {
            return false;
        };
        let mut ancestor = source
            .parse
            .arena
            .get(query_id)
            .and_then(|node| node.parent);
        let mut exported_alias = false;
        while let Some(id) = ancestor {
            let Some(node) = source.parse.arena.get(id) else {
                break;
            };
            if let NodeData::TypeAliasDeclaration(alias) = &node.data {
                exported_alias = node_has_modifier(
                    &source.parse.arena,
                    alias.modifiers.as_ref(),
                    ts_ast::SyntaxKind::ExportKeyword,
                );
                break;
            }
            ancestor = node.parent;
        }
        if !exported_alias {
            return false;
        }
        let Some((identifier, name)) =
            leftmost_entity_identifier(&source.parse.arena, query.expr_name)
        else {
            return false;
        };
        let Some(symbol) = source.binding.resolve_name_at(identifier, name) else {
            return false;
        };
        let Some(symbol) = source.binding.symbols.get(symbol) else {
            return false;
        };
        !symbol.declarations.is_empty()
            && symbol.declarations.iter().all(|declaration| {
                declaration_is_nested_in_runtime_block(
                    &source.parse.arena,
                    *declaration,
                    source.parse.source_file,
                )
            })
    })
}

fn has_unserializable_exported_anonymous_class(source: &SourceFile) -> bool {
    let private_mixins = source
        .parse
        .arena
        .iter()
        .filter_map(|(_, node)| {
            let NodeData::VariableDeclaration(variable) = &node.data else {
                return None;
            };
            let NodeData::ClassExpression(class) =
                &source.parse.arena.get(variable.initializer?)?.data
            else {
                return None;
            };
            class
                .members
                .nodes
                .iter()
                .any(|member| {
                    let modifiers = match &source.parse.arena.get(*member).map(|node| &node.data) {
                        Some(NodeData::PropertyDeclaration(member)) => member.modifiers.as_ref(),
                        Some(NodeData::MethodDeclaration(member)) => member.modifiers.as_ref(),
                        Some(NodeData::GetAccessorDeclaration(member)) => member.modifiers.as_ref(),
                        Some(NodeData::SetAccessorDeclaration(member)) => member.modifiers.as_ref(),
                        _ => None,
                    };
                    modifiers.is_some_and(|modifiers| {
                        modifiers.list.nodes.iter().any(|modifier| {
                            source.parse.arena.get(*modifier).is_some_and(|modifier| {
                                matches!(
                                    modifier.kind,
                                    ts_ast::SyntaxKind::PrivateKeyword
                                        | ts_ast::SyntaxKind::ProtectedKeyword
                                )
                            })
                        })
                    })
                })
                .then(|| identifier_text(&source.parse.arena, variable.name).map(str::to_owned))
                .flatten()
        })
        .collect::<BTreeSet<_>>();
    if private_mixins.is_empty() {
        return false;
    }
    let Some(NodeData::SourceFile(file)) = source
        .parse
        .arena
        .get(source.parse.source_file)
        .map(|node| &node.data)
    else {
        return false;
    };
    file.statements.nodes.iter().any(|statement_id| {
        let Some(statement) = source.parse.arena.get(*statement_id) else {
            return false;
        };
        let exported = matches!(&statement.data, NodeData::ExportAssignment(_))
            || match &statement.data {
                NodeData::ClassDeclaration(class) => node_has_modifier(
                    &source.parse.arena,
                    class.modifiers.as_ref(),
                    ts_ast::SyntaxKind::ExportKeyword,
                ),
                NodeData::VariableStatement(variable) => node_has_modifier(
                    &source.parse.arena,
                    variable.modifiers.as_ref(),
                    ts_ast::SyntaxKind::ExportKeyword,
                ),
                _ => false,
            };
        exported
            && source.parse.arena.iter().any(|(_, node)| {
                statement.range.start <= node.range.start
                    && node.range.end <= statement.range.end
                    && matches!(
                        &node.data,
                        NodeData::Identifier(identifier)
                            if private_mixins.contains(&identifier.text)
                    )
            })
    })
}

fn has_unserializable_exported_class_property_type(source: &SourceFile) -> bool {
    source.parse.arena.iter().any(|(_, node)| {
        let NodeData::ClassDeclaration(class) = &node.data else {
            return false;
        };
        if !node_has_modifier(
            &source.parse.arena,
            class.modifiers.as_ref(),
            ts_ast::SyntaxKind::ExportKeyword,
        ) {
            return false;
        }
        class.members.nodes.iter().any(|member| {
            let Some(NodeData::PropertyDeclaration(property)) =
                source.parse.arena.get(*member).map(|node| &node.data)
            else {
                return false;
            };
            if property.type_.is_some()
                || node_has_modifier(
                    &source.parse.arena,
                    property.modifiers.as_ref(),
                    ts_ast::SyntaxKind::PrivateKeyword,
                )
                || node_has_modifier(
                    &source.parse.arena,
                    property.modifiers.as_ref(),
                    ts_ast::SyntaxKind::ProtectedKeyword,
                )
            {
                return false;
            }
            let Some(type_id) = source.checking.type_of_node(*member).or_else(|| {
                property
                    .initializer
                    .and_then(|id| source.checking.type_of_node(id))
            }) else {
                return false;
            };
            let inaccessible =
                inaccessible_named_type_reference(&source.checking, type_id, &mut BTreeSet::new())
                    .or_else(|| {
                        cyclic_alias_type_name(&source.checking, type_id, &mut BTreeSet::new())
                    });
            inaccessible.is_some_and(|name| !source_declares_type_name(source, &name))
        })
    })
}

fn source_declares_type_name(source: &SourceFile, expected: &str) -> bool {
    source.parse.arena.iter().any(|(_, node)| {
        let name = match &node.data {
            NodeData::TypeAliasDeclaration(declaration) => Some(declaration.name),
            NodeData::InterfaceDeclaration(declaration) => Some(declaration.name),
            NodeData::ClassDeclaration(declaration) => declaration.name,
            NodeData::EnumDeclaration(declaration) => Some(declaration.name),
            _ => None,
        };
        name.and_then(|name| identifier_text(&source.parse.arena, name)) == Some(expected)
    })
}

fn leftmost_entity_identifier(arena: &ts_ast::NodeArena, entity: NodeId) -> Option<(NodeId, &str)> {
    match &arena.get(entity)?.data {
        NodeData::Identifier(identifier) => Some((entity, &identifier.text)),
        NodeData::QualifiedName(name) => leftmost_entity_identifier(arena, name.left),
        NodeData::PropertyAccessExpression(access) => {
            leftmost_entity_identifier(arena, access.expression)
        }
        _ => None,
    }
}

fn declaration_is_nested_in_runtime_block(
    arena: &ts_ast::NodeArena,
    declaration: NodeId,
    source_file: NodeId,
) -> bool {
    let mut current = declaration;
    while let Some(parent) = arena.get(current).and_then(|node| node.parent) {
        if parent == source_file {
            return false;
        }
        if matches!(
            arena.get(parent).map(|node| &node.data),
            Some(NodeData::Block(_))
        ) {
            return true;
        }
        current = parent;
    }
    false
}

fn private_type_query_name(source: &SourceFile, root: NodeId) -> Option<String> {
    let root = source.parse.arena.get(root)?;
    source.parse.arena.iter().find_map(|(_, node)| {
        if node.range.start < root.range.start || node.range.end > root.range.end {
            return None;
        }
        let NodeData::TypeQueryNode(query) = &node.data else {
            return None;
        };
        let (identifier, name) = leftmost_entity_identifier(&source.parse.arena, query.expr_name)?;
        let symbol = source.binding.resolve_name_at(identifier, name)?;
        let symbol = source.binding.symbols.get(symbol)?;
        (!symbol.declarations.is_empty()
            && symbol.declarations.iter().all(|declaration| {
                declaration_is_nested_in_runtime_block(
                    &source.parse.arena,
                    *declaration,
                    source.parse.source_file,
                )
            }))
        .then(|| name.to_owned())
    })
}

fn emit_diagnostic(source_file: &SourceFile, error: &ts_printer::EmitError) -> ProgramDiagnostic {
    ProgramDiagnostic {
        file_name: Some(source_file.file_name.clone()),
        range: source_file
            .parse
            .arena
            .get(error.node)
            .map(|node| node.range),
        code: None,
        message: error.to_string(),
    }
}

#[allow(clippy::too_many_lines)]
fn add_nonportable_inferred_type_diagnostics(source: &SourceFile, checking: &mut CheckResult) {
    let imports = source_import_bindings(source);
    let Some(NodeData::SourceFile(file)) = source
        .parse
        .arena
        .get(source.parse.source_file)
        .map(|node| &node.data)
    else {
        return;
    };
    for statement in &file.statements.nodes {
        let Some(NodeData::VariableStatement(variable)) =
            source.parse.arena.get(*statement).map(|node| &node.data)
        else {
            continue;
        };
        if !node_has_modifier(
            &source.parse.arena,
            variable.modifiers.as_ref(),
            ts_ast::SyntaxKind::ExportKeyword,
        ) {
            continue;
        }
        let Some(NodeData::VariableDeclarationList(list)) = source
            .parse
            .arena
            .get(variable.declaration_list)
            .map(|node| &node.data)
        else {
            continue;
        };
        for declaration_id in &list.declarations.nodes {
            let Some(NodeData::VariableDeclaration(declaration)) = source
                .parse
                .arena
                .get(*declaration_id)
                .map(|node| &node.data)
            else {
                continue;
            };
            if let Some(annotation) = declaration.type_
                && let Some(private_name) = private_type_query_name(source, annotation)
                && let Some(name) = identifier_text(&source.parse.arena, declaration.name)
            {
                let message =
                    message_by_code(4025).expect("TS4025 must be in the diagnostic catalog");
                checking.diagnostics.push(CheckDiagnostic {
                    node: declaration.name,
                    diagnostic: Diagnostic::with_arguments(
                        message,
                        [name.to_owned(), private_name],
                    ),
                });
                continue;
            }
            if declaration.type_.is_some() {
                continue;
            }
            let Some(type_id) = checking.type_of_node(*declaration_id).or_else(|| {
                declaration
                    .initializer
                    .and_then(|node| checking.type_of_node(node))
            }) else {
                continue;
            };
            let imported_computed_name_is_accessible =
                inaccessible_computed_symbol_name(checking, type_id, &mut BTreeSet::new())
                    .is_some_and(|qualifier| {
                        imports.iter().any(|(local, _, _)| local == &qualifier)
                    });
            if ((inaccessible_imported_unique_symbol(checking, type_id)
                && !imported_computed_name_is_accessible)
                || inferred_empty_object_from_imported_call(
                    source,
                    checking,
                    declaration.initializer,
                    type_id,
                ))
                && let Some(name) = identifier_text(&source.parse.arena, declaration.name)
            {
                let message =
                    message_by_code(2527).expect("TS2527 must be in the diagnostic catalog");
                checking.diagnostics.push(CheckDiagnostic {
                    node: declaration.name,
                    diagnostic: Diagnostic::with_arguments(
                        message,
                        [name.to_owned(), "unique symbol".into()],
                    ),
                });
                continue;
            }
            if let Some(qualifier) =
                inaccessible_computed_symbol_name(checking, type_id, &mut BTreeSet::new())
                && !imports.iter().any(|(local, _, _)| local == &qualifier)
                && let Some((_, _, module)) = imports.first()
                && let Some(name) = identifier_text(&source.parse.arena, declaration.name)
            {
                let message =
                    message_by_code(4023).expect("TS4023 must be in the diagnostic catalog");
                checking.diagnostics.push(CheckDiagnostic {
                    node: declaration.name,
                    diagnostic: Diagnostic::with_arguments(
                        message,
                        [
                            name.to_owned(),
                            qualifier,
                            format!("\"{}\"", module.trim_start_matches("./")),
                        ],
                    ),
                });
                continue;
            }
            let Some((qualifier, module)) =
                nonportable_import_type_reference(checking, type_id, &mut BTreeSet::new())
            else {
                continue;
            };
            let Some(name) = identifier_text(&source.parse.arena, declaration.name) else {
                continue;
            };
            let message = message_by_code(2883).expect("TS2883 must be in the diagnostic catalog");
            checking.diagnostics.push(CheckDiagnostic {
                node: declaration.name,
                diagnostic: Diagnostic::with_arguments(
                    message,
                    [name.to_owned(), qualifier, module],
                ),
            });
        }
    }

    let exported_functions = file
        .statements
        .nodes
        .iter()
        .filter_map(|statement| {
            let node = source.parse.arena.get(*statement)?;
            let NodeData::FunctionDeclaration(function) = &node.data else {
                return None;
            };
            node_has_modifier(
                &source.parse.arena,
                function.modifiers.as_ref(),
                ts_ast::SyntaxKind::ExportKeyword,
            )
            .then(|| {
                function
                    .name
                    .and_then(|name| identifier_text(&source.parse.arena, name))
            })
            .flatten()
        })
        .collect::<BTreeSet<_>>();
    for statement in &file.statements.nodes {
        let Some(NodeData::ExpressionStatement(statement)) =
            source.parse.arena.get(*statement).map(|node| &node.data)
        else {
            continue;
        };
        let Some(NodeData::BinaryExpression(assignment)) = source
            .parse
            .arena
            .get(statement.expression)
            .map(|node| &node.data)
        else {
            continue;
        };
        if source
            .parse
            .arena
            .get(assignment.operator_token)
            .is_none_or(|operator| operator.kind != ts_ast::SyntaxKind::EqualsToken)
        {
            continue;
        }
        let Some(NodeData::PropertyAccessExpression(access)) = source
            .parse
            .arena
            .get(assignment.left)
            .map(|node| &node.data)
        else {
            continue;
        };
        let Some(receiver) = identifier_text(&source.parse.arena, access.expression) else {
            continue;
        };
        if !exported_functions.contains(receiver) {
            continue;
        }
        let Some(NodeData::CallExpression(call)) = source
            .parse
            .arena
            .get(assignment.right)
            .map(|node| &node.data)
        else {
            continue;
        };
        let Some(callee) = identifier_text(&source.parse.arena, call.expression) else {
            continue;
        };
        let Some((_, _, module)) = imports.iter().find(|(local, _, _)| local == callee) else {
            continue;
        };
        let Some(type_id) = checking.type_of_node(assignment.right) else {
            continue;
        };
        let Some(private_name) =
            inaccessible_named_type_reference(checking, type_id, &mut BTreeSet::new())
        else {
            continue;
        };
        let Some(property) = identifier_text(&source.parse.arena, access.name) else {
            continue;
        };
        let message = message_by_code(4032).expect("TS4032 must be in the diagnostic catalog");
        checking.diagnostics.push(CheckDiagnostic {
            node: assignment.left,
            diagnostic: Diagnostic::with_arguments(
                message,
                [
                    property.to_owned(),
                    private_name,
                    format!("\"{}\"", module.trim_start_matches("./")),
                ],
            ),
        });
    }
}

fn inferred_empty_object_from_imported_call(
    source: &SourceFile,
    checking: &CheckResult,
    initializer: Option<NodeId>,
    type_id: TypeId,
) -> bool {
    if checking.import_type_references.contains_key(&type_id)
        || checking.named_type_references.contains_key(&type_id)
    {
        return false;
    }
    let Some(TypeKind::Object(object)) = checking.types.get(type_id).map(|type_| &type_.kind)
    else {
        return false;
    };
    if !object.properties.is_empty()
        || object.string_index_type.is_some()
        || object.number_index_type.is_some()
        || !object.call_signatures.is_empty()
        || !object.construct_signatures.is_empty()
    {
        return false;
    }
    let Some(NodeData::CallExpression(call)) = initializer
        .and_then(|initializer| source.parse.arena.get(initializer))
        .map(|node| &node.data)
    else {
        return false;
    };
    let Some(callee_type) = checking.type_of_node(call.expression) else {
        return false;
    };
    if nonportable_import_type_reference(checking, callee_type, &mut BTreeSet::new()).is_some() {
        return true;
    }
    let mut root = call.expression;
    while let Some(NodeData::PropertyAccessExpression(access)) =
        source.parse.arena.get(root).map(|node| &node.data)
    {
        root = access.expression;
    }
    let Some(root_name) = identifier_text(&source.parse.arena, root) else {
        return false;
    };
    source_import_bindings(source)
        .iter()
        .any(|(local, _, _)| local == root_name)
}

fn inaccessible_imported_unique_symbol(checking: &CheckResult, type_id: TypeId) -> bool {
    fn visit(
        checking: &CheckResult,
        type_id: TypeId,
        imported: bool,
        visited: &mut BTreeSet<TypeId>,
    ) -> bool {
        if !visited.insert(type_id) {
            return false;
        }
        let imported = imported
            || checking.import_type_references.contains_key(&type_id)
            || checking
                .named_type_references
                .get(&type_id)
                .is_some_and(|reference| reference.name.starts_with("import("));
        let Some(kind) = checking.types.get(type_id).map(|type_| &type_.kind) else {
            return false;
        };
        match kind {
            TypeKind::Object(object) => {
                if imported
                    && (object.properties.keys().any(|name| name.starts_with("[#"))
                        || object.readonly_properties.iter().any(|name| {
                            object.properties.get(name).is_some_and(|property| {
                                matches!(
                                    checking.types.get(*property).map(|type_| &type_.kind),
                                    Some(TypeKind::Unknown)
                                )
                            })
                        }))
                {
                    return true;
                }
                object
                    .properties
                    .values()
                    .copied()
                    .chain(object.string_index_type)
                    .chain(object.number_index_type)
                    .any(|part| visit(checking, part, imported, visited))
            }
            TypeKind::Array(element) => visit(checking, *element, imported, visited),
            TypeKind::Tuple(elements)
            | TypeKind::ReadonlyTuple(elements)
            | TypeKind::Union(elements)
            | TypeKind::Intersection(elements) => elements
                .iter()
                .any(|part| visit(checking, *part, imported, visited)),
            TypeKind::Function(signature) | TypeKind::Constructor(signature) => signature
                .parameters
                .iter()
                .copied()
                .chain(signature.rest_parameter)
                .chain(std::iter::once(signature.return_type))
                .any(|part| visit(checking, part, imported, visited)),
            TypeKind::Overload(signatures) => signatures.iter().any(|signature| {
                signature
                    .parameters
                    .iter()
                    .copied()
                    .chain(signature.rest_parameter)
                    .chain(std::iter::once(signature.return_type))
                    .any(|part| visit(checking, part, imported, visited))
            }),
            _ => false,
        }
    }

    visit(checking, type_id, false, &mut BTreeSet::new())
}

fn source_import_bindings(source: &SourceFile) -> Vec<(String, String, String)> {
    let Some(NodeData::SourceFile(file)) = source
        .parse
        .arena
        .get(source.parse.source_file)
        .map(|node| &node.data)
    else {
        return Vec::new();
    };
    let mut imports = Vec::new();
    for statement in &file.statements.nodes {
        let Some(NodeData::ImportDeclaration(import)) =
            source.parse.arena.get(*statement).map(|node| &node.data)
        else {
            continue;
        };
        let Some((specifier, _)) = string_literal(&source.parse.arena, import.module_specifier)
        else {
            continue;
        };
        let Some(NodeData::ImportClause(clause)) = import
            .import_clause
            .and_then(|clause| source.parse.arena.get(clause))
            .map(|node| &node.data)
        else {
            continue;
        };
        if let Some(local) = clause
            .name
            .and_then(|name| identifier_text(&source.parse.arena, name))
        {
            imports.push((local.to_owned(), "default".into(), specifier.clone()));
        }
        if let Some(NodeData::NamespaceImport(namespace)) = clause
            .named_bindings
            .and_then(|bindings| source.parse.arena.get(bindings))
            .map(|node| &node.data)
            && let Some(local) = identifier_text(&source.parse.arena, namespace.name)
        {
            imports.push((local.to_owned(), "*".into(), specifier.clone()));
        }
        let Some(NodeData::NamedImports(named)) = clause
            .named_bindings
            .and_then(|bindings| source.parse.arena.get(bindings))
            .map(|node| &node.data)
        else {
            continue;
        };
        for element in &named.elements.nodes {
            let Some(NodeData::ImportSpecifier(imported)) =
                source.parse.arena.get(*element).map(|node| &node.data)
            else {
                continue;
            };
            let Some(local) = identifier_text(&source.parse.arena, imported.name) else {
                continue;
            };
            let imported_name = imported
                .property_name
                .and_then(|name| identifier_text(&source.parse.arena, name))
                .unwrap_or(local);
            imports.push((
                local.to_owned(),
                imported_name.to_owned(),
                specifier.clone(),
            ));
        }
    }
    imports
}

fn imported_call_target(
    source: &SourceFile,
    initializer: NodeId,
) -> Option<(String, Option<String>)> {
    let NodeData::CallExpression(call) = &source.parse.arena.get(initializer)?.data else {
        return None;
    };
    match &source.parse.arena.get(call.expression)?.data {
        NodeData::Identifier(identifier) => Some((identifier.text.clone(), None)),
        NodeData::PropertyAccessExpression(access) => Some((
            identifier_text(&source.parse.arena, access.expression)?.to_owned(),
            Some(identifier_text(&source.parse.arena, access.name)?.to_owned()),
        )),
        _ => None,
    }
}

fn imported_function_mapped_symbol_property(
    source: &SourceFile,
    function_name: &str,
) -> Option<String> {
    let return_name = source.parse.arena.iter().find_map(|(_, node)| {
        let NodeData::FunctionDeclaration(function) = &node.data else {
            return None;
        };
        (function
            .name
            .and_then(|name| identifier_text(&source.parse.arena, name))
            == Some(function_name))
        .then(|| {
            let NodeData::TypeQueryNode(query) = &source.parse.arena.get(function.type_?)?.data
            else {
                return None;
            };
            identifier_text(&source.parse.arena, query.expr_name).map(str::to_owned)
        })
        .flatten()
    })?;
    source.parse.arena.iter().find_map(|(_, node)| {
        let NodeData::VariableDeclaration(variable) = &node.data else {
            return None;
        };
        if identifier_text(&source.parse.arena, variable.name) != Some(&return_name) {
            return None;
        }
        let NodeData::MappedTypeNode(mapped) = &source.parse.arena.get(variable.type_?)?.data
        else {
            return None;
        };
        let NodeData::TypeParameterDeclaration(parameter) =
            &source.parse.arena.get(mapped.type_parameter)?.data
        else {
            return None;
        };
        let NodeData::TypeQueryNode(query) = &source.parse.arena.get(parameter.constraint?)?.data
        else {
            return None;
        };
        identifier_text(&source.parse.arena, query.expr_name).map(str::to_owned)
    })
}

fn export_assignment_is_object_assign(source: &SourceFile, expression: NodeId) -> bool {
    let Some(NodeData::CallExpression(call)) =
        source.parse.arena.get(expression).map(|node| &node.data)
    else {
        return false;
    };
    matches!(
        source.parse.arena.get(call.expression).map(|node| &node.data),
        Some(NodeData::PropertyAccessExpression(access))
            if identifier_text(&source.parse.arena, access.expression) == Some("Object")
                && identifier_text(&source.parse.arena, access.name) == Some("assign")
    )
}

fn nested_namespace_import_reference(
    program: &Program,
    target: &SourceFile,
) -> Option<(String, String)> {
    let containing = canonicalize(
        &target.file_name,
        &program.current_directory,
        program.case_sensitivity,
    );
    source_import_bindings(target)
        .into_iter()
        .filter(|(_, imported, _)| imported == "*")
        .find_map(|(local, _, specifier)| {
            let resolved = program
                .resolved_modules
                .get(&(containing.clone(), specifier))?;
            if resolved.match_indices("/node_modules/").count() < 2 {
                return None;
            }
            let qualifier = target.parse.arena.iter().find_map(|(_, node)| {
                let NodeData::QualifiedName(name) = &node.data else {
                    return None;
                };
                (identifier_text(&target.parse.arena, name.left) == Some(&local))
                    .then(|| identifier_text(&target.parse.arena, name.right).map(str::to_owned))
                    .flatten()
            })?;
            let relative = resolved.split_once("/node_modules/")?.1;
            let module = ts_path::remove_file_extension(relative)
                .trim_end_matches("/index")
                .to_owned();
            Some((qualifier, module))
        })
}

fn nonportable_return_import(
    program: &Program,
    target: &SourceFile,
    function_name: &str,
) -> Option<(String, String)> {
    let containing = canonicalize(
        &target.file_name,
        &program.current_directory,
        program.case_sensitivity,
    );
    let nested_imports = source_import_bindings(target)
        .into_iter()
        .filter_map(|(local, imported, specifier)| {
            let resolved = program
                .resolved_modules
                .get(&(containing.clone(), specifier))?;
            (resolved.match_indices("/node_modules/").count() >= 2).then(|| {
                let relative = resolved.split_once("/node_modules/").unwrap().1;
                let module = ts_path::remove_file_extension(relative)
                    .trim_end_matches("/index")
                    .to_owned();
                (local, imported, module)
            })
        })
        .collect::<Vec<_>>();
    if nested_imports.is_empty() {
        return None;
    }
    let Some(NodeData::SourceFile(file)) = target
        .parse
        .arena
        .get(target.parse.source_file)
        .map(|node| &node.data)
    else {
        return None;
    };
    for statement in &file.statements.nodes {
        let Some(NodeData::FunctionDeclaration(function)) =
            target.parse.arena.get(*statement).map(|node| &node.data)
        else {
            continue;
        };
        if function
            .name
            .and_then(|name| identifier_text(&target.parse.arena, name))
            != Some(function_name)
        {
            continue;
        }
        let type_node = target.parse.arena.get(function.type_?)?;
        return nested_imports.iter().find_map(|(local, imported, module)| {
            target.parse.arena.iter().find_map(|(_, node)| {
                (type_node.range.start <= node.range.start
                    && node.range.end <= type_node.range.end
                    && matches!(
                        &node.data,
                        NodeData::Identifier(identifier) if identifier.text == *local
                    ))
                .then(|| (imported.clone(), module.clone()))
            })
        });
    }
    None
}

fn nonportable_import_type_reference(
    checking: &CheckResult,
    type_id: TypeId,
    visited: &mut BTreeSet<TypeId>,
) -> Option<(String, String)> {
    if !visited.insert(type_id) {
        return None;
    }
    if let Some(reference) = checking.import_type_references.get(&type_id)
        && reference.module_specifier.contains("/node_modules/")
    {
        return Some((
            reference.qualifier.clone(),
            reference.module_specifier.clone(),
        ));
    }
    if let Some(reference) = checking.named_type_references.get(&type_id)
        && let Some(nonportable) = reference
            .type_arguments
            .iter()
            .find_map(|argument| nonportable_import_type_reference(checking, *argument, visited))
    {
        return Some(nonportable);
    }
    let kind = &checking.types.get(type_id)?.kind;
    let mut children = Vec::new();
    match kind {
        TypeKind::TypeParameter { constraint, .. } => children.extend(constraint),
        TypeKind::Array(element) => children.push(*element),
        TypeKind::Tuple(elements)
        | TypeKind::ReadonlyTuple(elements)
        | TypeKind::Union(elements)
        | TypeKind::Intersection(elements) => children.extend(elements),
        TypeKind::Object(object) => {
            children.extend(object.properties.values());
            children.extend(object.string_index_type);
            children.extend(object.number_index_type);
            for signature in object
                .call_signatures
                .iter()
                .chain(&object.construct_signatures)
            {
                children.extend(&signature.parameters);
                children.extend(signature.rest_parameter);
                children.push(signature.return_type);
            }
        }
        TypeKind::Function(signature) | TypeKind::Constructor(signature) => {
            children.extend(&signature.parameters);
            children.extend(signature.rest_parameter);
            children.push(signature.return_type);
        }
        TypeKind::Overload(signatures) => {
            for signature in signatures {
                children.extend(&signature.parameters);
                children.extend(signature.rest_parameter);
                children.push(signature.return_type);
            }
        }
        _ => {}
    }
    children
        .into_iter()
        .find_map(|child| nonportable_import_type_reference(checking, child, visited))
}

fn inaccessible_computed_symbol_name(
    checking: &CheckResult,
    type_id: TypeId,
    visited: &mut BTreeSet<TypeId>,
) -> Option<String> {
    if !visited.insert(type_id) {
        return None;
    }
    let kind = &checking.types.get(type_id)?.kind;
    let mut children = Vec::new();
    match kind {
        TypeKind::TypeParameter { constraint, .. } => children.extend(constraint),
        TypeKind::Array(element) => children.push(*element),
        TypeKind::Tuple(elements)
        | TypeKind::ReadonlyTuple(elements)
        | TypeKind::Union(elements)
        | TypeKind::Intersection(elements) => children.extend(elements),
        TypeKind::Object(object) => {
            if let Some(name) = object.properties.keys().find_map(|name| {
                name.strip_prefix("[#")
                    .and_then(|name| name.strip_suffix(']'))
                    .and_then(|name| name.split('.').next())
                    .map(str::to_owned)
            }) {
                return Some(name);
            }
            children.extend(object.properties.values());
            children.extend(object.string_index_type);
            children.extend(object.number_index_type);
        }
        TypeKind::Function(signature) | TypeKind::Constructor(signature) => {
            children.extend(&signature.parameters);
            children.extend(signature.rest_parameter);
            children.push(signature.return_type);
        }
        TypeKind::Overload(signatures) => {
            for signature in signatures {
                children.extend(&signature.parameters);
                children.extend(signature.rest_parameter);
                children.push(signature.return_type);
            }
        }
        _ => {}
    }
    children
        .into_iter()
        .find_map(|child| inaccessible_computed_symbol_name(checking, child, visited))
}

fn inaccessible_named_type_reference(
    checking: &CheckResult,
    type_id: TypeId,
    visited: &mut BTreeSet<TypeId>,
) -> Option<String> {
    if !visited.insert(type_id) || checking.import_type_references.contains_key(&type_id) {
        return None;
    }
    if let Some(reference) = checking.named_type_references.get(&type_id)
        && !is_global_library_type_name(&reference.name)
    {
        return Some(reference.name.clone());
    }
    let kind = &checking.types.get(type_id)?.kind;
    let mut children = Vec::new();
    match kind {
        TypeKind::TypeParameter { constraint, .. } => children.extend(constraint),
        TypeKind::Array(element) => children.push(*element),
        TypeKind::Tuple(elements)
        | TypeKind::ReadonlyTuple(elements)
        | TypeKind::Union(elements)
        | TypeKind::Intersection(elements) => children.extend(elements),
        TypeKind::Object(object) => {
            children.extend(object.properties.values());
            children.extend(object.string_index_type);
            children.extend(object.number_index_type);
        }
        TypeKind::Function(signature) | TypeKind::Constructor(signature) => {
            children.extend(&signature.parameters);
            children.extend(signature.rest_parameter);
            children.push(signature.return_type);
        }
        TypeKind::Overload(signatures) => {
            for signature in signatures {
                children.extend(&signature.parameters);
                children.extend(signature.rest_parameter);
                children.push(signature.return_type);
            }
        }
        _ => {}
    }
    children
        .into_iter()
        .find_map(|child| inaccessible_named_type_reference(checking, child, visited))
}

fn is_global_library_type_name(name: &str) -> bool {
    matches!(
        name,
        "Array"
            | "ReadonlyArray"
            | "Promise"
            | "PromiseLike"
            | "PromiseConstructor"
            | "String"
            | "StringConstructor"
            | "Number"
            | "Boolean"
            | "Object"
            | "Function"
            | "CallableFunction"
            | "NewableFunction"
            | "IArguments"
            | "Record"
            | "Omit"
            | "Pick"
            | "Partial"
            | "Required"
            | "Readonly"
            | "Exclude"
            | "Extract"
            | "NonNullable"
            | "Parameters"
            | "ConstructorParameters"
            | "ReturnType"
            | "InstanceType"
    )
}

fn cyclic_alias_type_name(
    checking: &CheckResult,
    type_id: TypeId,
    visited: &mut BTreeSet<TypeId>,
) -> Option<String> {
    if !visited.insert(type_id) {
        return None;
    }
    let kind = &checking.types.get(type_id)?.kind;
    if let TypeKind::TypeParameter { name, .. } = kind
        && let Some(name) = name.strip_prefix("__cyclic_alias__")
    {
        return Some(name.to_owned());
    }
    let mut children = Vec::new();
    match kind {
        TypeKind::TypeParameter { constraint, .. } => children.extend(constraint),
        TypeKind::Array(element) => children.push(*element),
        TypeKind::Tuple(elements)
        | TypeKind::ReadonlyTuple(elements)
        | TypeKind::Union(elements)
        | TypeKind::Intersection(elements) => children.extend(elements),
        TypeKind::Object(object) => {
            children.extend(object.properties.values());
            children.extend(object.string_index_type);
            children.extend(object.number_index_type);
            for signature in object
                .call_signatures
                .iter()
                .chain(&object.construct_signatures)
            {
                children.extend(&signature.parameters);
                children.extend(signature.rest_parameter);
                children.push(signature.return_type);
            }
        }
        TypeKind::Function(signature) | TypeKind::Constructor(signature) => {
            children.extend(&signature.parameters);
            children.extend(signature.rest_parameter);
            children.push(signature.return_type);
        }
        TypeKind::Overload(signatures) => {
            for signature in signatures {
                children.extend(&signature.parameters);
                children.extend(signature.rest_parameter);
                children.push(signature.return_type);
            }
        }
        _ => {}
    }
    children
        .into_iter()
        .find_map(|child| cyclic_alias_type_name(checking, child, visited))
}

fn enum_values_for_emit(
    values: &BTreeMap<NodeId, CheckerConstantValue>,
) -> BTreeMap<NodeId, EmitConstantValue> {
    values
        .iter()
        .map(|(node, value)| {
            let value = match value {
                CheckerConstantValue::Number(value) => EmitConstantValue::Number(*value),
                CheckerConstantValue::String(value) => EmitConstantValue::String(value.clone()),
            };
            (*node, value)
        })
        .collect()
}

fn declaration_node_types_for_emit(
    source: &SourceFile,
    strict_null_checks: bool,
) -> BTreeMap<NodeId, ts_checker::TypeId> {
    let mut node_types = source.checking.node_types.clone();
    for (id, node) in source.parse.arena.iter() {
        if !strict_null_checks
            && let NodeData::ParameterDeclaration(parameter) = &node.data
            && parameter.type_.is_none()
            && let Some(initializer) = parameter.initializer
            && source
                .parse
                .arena
                .get(initializer)
                .is_some_and(|initializer| initializer.kind == ts_ast::SyntaxKind::NullKeyword)
        {
            node_types.insert(initializer, source.checking.types.any());
        }
        if let NodeData::Identifier(identifier) = &node.data
            && !node_types.contains_key(&id)
            && let Some(type_id) = source
                .binding
                .resolve_name_at(id, &identifier.text)
                .and_then(|symbol| source.checking.type_of_symbol(symbol))
        {
            node_types.insert(id, type_id);
        }
        if let NodeData::MethodDeclaration(method) = &node.data
            && !node_types.contains_key(&id)
            && let Some(name) = identifier_text(&source.parse.arena, method.name)
            && let Some(class_symbol) = node
                .parent
                .and_then(|class| source.binding.node_symbols.get(&class).copied())
            && let Some(class_type) = source.checking.type_of_symbol(class_symbol)
            && let Some(type_id) =
                source
                    .checking
                    .types
                    .get(class_type)
                    .and_then(|type_| match &type_.kind {
                        ts_checker::TypeKind::Object(object) => {
                            object.properties.get(name).copied()
                        }
                        _ => None,
                    })
        {
            node_types.insert(id, type_id);
        }
        if !matches!(node.data, NodeData::FunctionDeclaration(_)) || node_types.contains_key(&id) {
            continue;
        }
        let Some(type_id) = source
            .binding
            .node_symbols
            .get(&id)
            .and_then(|symbol| source.checking.type_of_symbol(*symbol))
        else {
            continue;
        };
        node_types.insert(id, type_id);
    }
    node_types
}

fn source_is_external_module(source: &SourceFile) -> bool {
    if !source.binding.exports.is_empty() {
        return true;
    }
    let Some(NodeData::SourceFile(file)) = source
        .parse
        .arena
        .get(source.parse.source_file)
        .map(|node| &node.data)
    else {
        return false;
    };
    file.statements.nodes.iter().any(|statement| {
        match source.parse.arena.get(*statement).map(|node| &node.data) {
            Some(
                NodeData::ImportDeclaration(_)
                | NodeData::ExportDeclaration(_)
                | NodeData::ExportAssignment(_),
            ) => true,
            Some(NodeData::ImportEqualsDeclaration(import)) => matches!(
                source
                    .parse
                    .arena
                    .get(import.module_reference)
                    .map(|node| &node.data),
                Some(NodeData::ExternalModuleReference(_))
            ),
            _ => false,
        }
    })
}

fn import_binding_is_const_enum(source: &SourceFile, binding: NodeId) -> bool {
    source
        .binding
        .node_symbols
        .get(&binding)
        .and_then(|symbol| source.checking.symbol_types.get(symbol))
        .is_some_and(|type_id| source.checking.const_enum_types.contains(type_id))
}

fn import_declaration_binds_const_enum(
    source: &SourceFile,
    import: &ts_ast::ImportDeclarationData,
) -> bool {
    import
        .import_clause
        .and_then(|clause| source.parse.arena.get(clause))
        .and_then(|node| match &node.data {
            NodeData::ImportClause(clause) => Some(clause),
            _ => None,
        })
        .is_some_and(|clause| {
            clause
                .name
                .is_some_and(|name| import_binding_is_const_enum(source, name))
                || clause.named_bindings.is_some_and(|bindings| {
                    match source.parse.arena.get(bindings).map(|node| &node.data) {
                        Some(NodeData::NamedImports(imports)) => {
                            imports.elements.nodes.iter().any(|specifier| {
                                matches!(
                                    source.parse.arena.get(*specifier).map(|node| &node.data),
                                    Some(NodeData::ImportSpecifier(specifier))
                                        if import_binding_is_const_enum(source, specifier.name)
                                )
                            })
                        }
                        _ => false,
                    }
                })
        })
}

fn import_equals_name<'a>(
    source: &'a SourceFile,
    import: &ts_ast::ImportEqualsDeclarationData,
) -> Option<&'a str> {
    match &source.parse.arena.get(import.name)?.data {
        NodeData::Identifier(identifier) => Some(&identifier.text),
        _ => None,
    }
}

fn import_equals_has_inlined_const_enum_access(source: &SourceFile, import_name: &str) -> bool {
    source.checking.enum_access_values.keys().any(|access| {
        let mut current = *access;
        loop {
            match source.parse.arena.get(current).map(|node| &node.data) {
                Some(NodeData::PropertyAccessExpression(access)) => current = access.expression,
                Some(NodeData::ElementAccessExpression(access)) => current = access.expression,
                Some(NodeData::Identifier(identifier)) => break identifier.text == import_name,
                _ => break false,
            }
        }
    })
}

fn import_runtime_meanings_for_emit(
    source: &SourceFile,
    preserve_const_enums: bool,
    amd: bool,
    later_script_variable_names: &HashSet<String>,
) -> BTreeMap<NodeId, bool> {
    let mut meanings = source.checking.import_runtime_meanings.clone();
    let Some(NodeData::SourceFile(file)) = source
        .parse
        .arena
        .get(source.parse.source_file)
        .map(|node| &node.data)
    else {
        return meanings;
    };
    let runtime_identifier_uses =
        amd.then(|| runtime_identifier_uses(&source.parse.arena, source.parse.source_file));
    for statement in &file.statements.nodes {
        if let Some(NodeData::ImportDeclaration(import)) =
            source.parse.arena.get(*statement).map(|node| &node.data)
        {
            if preserve_const_enums && import_declaration_binds_const_enum(source, import) {
                meanings.insert(*statement, true);
            }
            continue;
        }
        if !amd {
            if let Some(NodeData::ImportEqualsDeclaration(import)) =
                source.parse.arena.get(*statement).map(|node| &node.data)
                && !import.is_type_only
                && !matches!(
                    source
                        .parse
                        .arena
                        .get(import.module_reference)
                        .map(|node| &node.data),
                    Some(NodeData::ExternalModuleReference(_))
                )
                && import_equals_name(source, import)
                    .is_some_and(|name| later_script_variable_names.contains(name))
            {
                meanings.insert(*statement, true);
            }
            continue;
        }
        let Some(NodeData::ImportEqualsDeclaration(import)) =
            source.parse.arena.get(*statement).map(|node| &node.data)
        else {
            continue;
        };
        if import.is_type_only {
            continue;
        }
        let Some(import_name) = import_equals_name(source, import) else {
            continue;
        };
        let runtime_uses = runtime_identifier_uses
            .as_ref()
            .expect("AMD uses were collected");
        let has_runtime_use = runtime_uses.contains(import_name);
        if meanings.get(statement) == Some(&false)
            && (!has_runtime_use
                || import_equals_has_inlined_const_enum_access(source, import_name))
        {
            continue;
        }
        // Ambient modules have no implementation initializer, so semantic shape alone cannot
        // distinguish their runtime aliases. Preserve only aliases with binding-resolved uses.
        meanings.insert(*statement, true);
    }
    meanings
}

fn later_top_level_script_variable_names<'a>(
    sources: impl IntoIterator<Item = &'a SourceFile>,
) -> HashSet<String> {
    sources
        .into_iter()
        .filter(|source| {
            !source.is_default_library
                && !ts_path::is_declaration_file(&source.file_name)
                && !source_is_external_module(source)
        })
        .flat_map(|source| {
            let statements = match source
                .parse
                .arena
                .get(source.parse.source_file)
                .map(|node| &node.data)
            {
                Some(NodeData::SourceFile(file)) => file.statements.nodes.as_slice(),
                _ => &[],
            };
            statements
                .iter()
                .filter_map(|statement| {
                    let NodeData::VariableStatement(variable) =
                        &source.parse.arena.get(*statement)?.data
                    else {
                        return None;
                    };
                    let NodeData::VariableDeclarationList(list) =
                        &source.parse.arena.get(variable.declaration_list)?.data
                    else {
                        return None;
                    };
                    Some(list.declarations.nodes.iter().filter_map(|declaration| {
                        let NodeData::VariableDeclaration(variable) =
                            &source.parse.arena.get(*declaration)?.data
                        else {
                            return None;
                        };
                        match source.parse.arena.get(variable.name).map(|node| &node.data) {
                            Some(NodeData::Identifier(identifier)) => Some(identifier.text.clone()),
                            _ => None,
                        }
                    }))
                })
                .flatten()
                .collect::<Vec<_>>()
        })
        .collect()
}

fn append_bundle_declaration_module(
    code: &mut String,
    source: &SourceFile,
    declaration: &str,
    module_name: &str,
    preserve_amd_pragma: bool,
) {
    if preserve_amd_pragma && let Some(pragma) = source.parse.amd_module_names.last() {
        let start = usize::try_from(pragma.range.start.get()).unwrap_or(usize::MAX);
        let end = usize::try_from(pragma.range.end.get()).unwrap_or(usize::MAX);
        if let Some(comment) = source.source_text.get(start..end) {
            code.push_str(comment.trim_end_matches(['\r', '\n']));
            code.push('\n');
        }
    }
    code.push_str("declare module \"");
    code.push_str(&module_name.replace('"', "\\\""));
    code.push_str("\" {\n");
    for line in declaration.lines() {
        if preserve_amd_pragma {
            let trimmed = line.trim_start();
            if trimmed.starts_with("///") && trimmed.contains("<amd-module") {
                continue;
            }
        }
        let line = line.strip_prefix("export declare ").map_or_else(
            || line.strip_prefix("declare ").unwrap_or(line).to_owned(),
            |line| format!("export {line}"),
        );
        if !line.is_empty() {
            code.push_str("    ");
            code.push_str(&line);
        }
        code.push('\n');
    }
    code.push_str("}\n");
}

fn defer_export_only_bundle_imports(declaration: &str) -> String {
    let lines = declaration.lines().collect::<Vec<_>>();
    let mut deferred = BTreeMap::<usize, Vec<usize>>::new();
    for (import_index, line) in lines.iter().enumerate() {
        let names = declaration_import_local_names(line);
        if names.is_empty() {
            continue;
        }
        let mut last_export = None;
        let mut used_elsewhere = false;
        for (index, candidate) in lines.iter().enumerate() {
            if index == import_index
                || !names
                    .iter()
                    .any(|name| text_contains_identifier(candidate, name))
            {
                continue;
            }
            if candidate.trim_start().starts_with("export {") {
                last_export = Some(index);
            } else {
                used_elsewhere = true;
                break;
            }
        }
        if !used_elsewhere && let Some(export_index) = last_export {
            deferred.entry(export_index).or_default().push(import_index);
        }
    }
    if deferred.is_empty() {
        return declaration.to_owned();
    }
    let deferred_indices = deferred
        .values()
        .flatten()
        .copied()
        .collect::<BTreeSet<_>>();
    let mut output = String::new();
    for (index, line) in lines.iter().enumerate() {
        if !deferred_indices.contains(&index) {
            output.push_str(line);
            output.push('\n');
        }
        if let Some(imports) = deferred.get(&index) {
            for import in imports {
                output.push_str(lines[*import]);
                output.push('\n');
            }
        }
    }
    output
}

fn declaration_import_local_names(line: &str) -> Vec<String> {
    let line = line.trim();
    let Some(clause) = line.strip_prefix("import ") else {
        return Vec::new();
    };
    let Some((clause, _)) = clause.rsplit_once(" from ") else {
        return Vec::new();
    };
    if let Some(namespace) = clause.strip_prefix("* as ") {
        return vec![namespace.trim().to_owned()];
    }
    if let Some(named) = clause
        .strip_prefix('{')
        .and_then(|value| value.strip_suffix('}'))
    {
        return named
            .split(',')
            .filter_map(|specifier| {
                let specifier = specifier
                    .trim()
                    .strip_prefix("type ")
                    .unwrap_or(specifier.trim());
                specifier
                    .split_once(" as ")
                    .map_or(specifier, |(_, local)| local)
                    .split_whitespace()
                    .next()
                    .map(str::to_owned)
            })
            .collect();
    }
    clause
        .split_once(',')
        .map_or(clause, |(default, _)| default)
        .split_whitespace()
        .next()
        .map(str::to_owned)
        .into_iter()
        .collect()
}

fn bundle_declaration_module_name(
    source: &SourceFile,
    bundle_root: &str,
    module: ModuleKind,
) -> String {
    if module == ModuleKind::Amd {
        return amd_bundle_module_name(source, bundle_root);
    }
    let relative = source
        .file_name
        .strip_prefix(bundle_root)
        .unwrap_or(&source.file_name)
        .trim_start_matches('/');
    ts_path::remove_file_extension(relative).to_owned()
}

fn identifier_text(arena: &ts_ast::NodeArena, node: NodeId) -> Option<&str> {
    let NodeData::Identifier(identifier) = &arena.get(node)?.data else {
        return None;
    };
    Some(&identifier.text)
}

fn replace_import_type_reference(
    declaration: &mut String,
    module: &str,
    imported: &str,
    local: &str,
) -> bool {
    let reference = format!("import(\"{module}\").{imported}");
    if !declaration.contains(&reference) {
        return false;
    }
    *declaration = declaration.replace(&reference, local);
    true
}

fn remove_unused_named_declaration_imports(declaration: &str) -> String {
    let body = declaration
        .lines()
        .filter(|line| !line.trim_start().starts_with("import "))
        .collect::<Vec<_>>()
        .join("\n");
    let mut output = declaration
        .lines()
        .filter(|line| {
            let trimmed = line.trim();
            let Some(imports) = trimmed
                .strip_prefix("import { ")
                .and_then(|import| import.split_once(" } from "))
                .map(|(imports, _)| imports)
            else {
                return true;
            };
            imports.split(',').map(str::trim).any(|import| {
                let local = import.split_once(" as ").map_or(import, |(_, local)| local);
                text_contains_identifier(&body, local)
            })
        })
        .collect::<Vec<_>>()
        .join("\n");
    if declaration.ends_with('\n') {
        output.push('\n');
    }
    output
}

fn text_contains_identifier(text: &str, identifier: &str) -> bool {
    text.match_indices(identifier).any(|(start, _)| {
        let before = text[..start].chars().next_back();
        let end = start + identifier.len();
        let after = text[end..].chars().next();
        before.is_none_or(|character| !is_identifier_character(character))
            && after.is_none_or(|character| !is_identifier_character(character))
    })
}

fn is_identifier_character(character: char) -> bool {
    character == '_' || character == '$' || character.is_alphanumeric()
}

fn amd_bundle_module_name(source: &SourceFile, bundle_root: &str) -> String {
    source.parse.amd_module_name.clone().unwrap_or_else(|| {
        let relative = source
            .file_name
            .strip_prefix(bundle_root)
            .unwrap_or(&source.file_name)
            .trim_start_matches('/');
        ts_path::remove_file_extension(relative).to_owned()
    })
}

fn base64_encode(bytes: &[u8]) -> String {
    const ALPHABET: &[u8; 64] = b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";
    let mut encoded = String::with_capacity(bytes.len().div_ceil(3) * 4);
    for chunk in bytes.chunks(3) {
        let first = chunk[0];
        let second = chunk.get(1).copied().unwrap_or(0);
        let third = chunk.get(2).copied().unwrap_or(0);
        encoded.push(char::from(ALPHABET[usize::from(first >> 2)]));
        encoded.push(char::from(
            ALPHABET[usize::from(((first & 0x03) << 4) | (second >> 4))],
        ));
        encoded.push(if chunk.len() > 1 {
            char::from(ALPHABET[usize::from(((second & 0x0f) << 2) | (third >> 6))])
        } else {
            '='
        });
        encoded.push(if chunk.len() > 2 {
            char::from(ALPHABET[usize::from(third & 0x3f)])
        } else {
            '='
        });
    }
    encoded
}

fn module_specifiers(parse: &ParseResult) -> Vec<(String, TextRange, bool)> {
    let mut specifiers = parse
        .arena
        .iter()
        .filter_map(|(_, node)| match &node.data {
            NodeData::ImportDeclaration(data) => {
                string_literal(&parse.arena, data.module_specifier)
                    .map(|(specifier, range)| (specifier, range, true))
            }
            NodeData::ImportEqualsDeclaration(data) => parse
                .arena
                .get(data.module_reference)
                .and_then(|reference| match &reference.data {
                    NodeData::ExternalModuleReference(reference) => {
                        string_literal(&parse.arena, reference.expression)
                    }
                    _ => None,
                })
                .map(|(specifier, range)| (specifier, range, true)),
            NodeData::ExportDeclaration(data) => data
                .module_specifier
                .and_then(|specifier| string_literal(&parse.arena, specifier))
                .map(|(specifier, range)| (specifier, range, true)),
            NodeData::ImportTypeNode(data) => {
                let argument = match parse.arena.get(data.argument).map(|node| &node.data) {
                    Some(NodeData::LiteralTypeNode(literal)) => literal.literal,
                    _ => data.argument,
                };
                string_literal(&parse.arena, argument)
                    .map(|(specifier, range)| (specifier, range, true))
            }
            NodeData::CallExpression(data)
                if matches!(
                    parse.arena.get(data.expression).map(|node| &node.data),
                    Some(NodeData::Identifier(identifier)) if identifier.text == "import"
                ) =>
            {
                data.arguments
                    .nodes
                    .first()
                    .and_then(|argument| string_literal(&parse.arena, *argument))
                    .map(|(specifier, range)| (specifier, range, true))
            }
            _ => None,
        })
        .collect::<Vec<_>>();
    if let Some(source) = parse.arena.source_text() {
        specifiers.extend(jsdoc_import_specifiers(source));
    }
    specifiers
}

fn jsdoc_import_specifiers(source: &str) -> Vec<(String, TextRange, bool)> {
    let mut specifiers = Vec::new();
    let mut search_start = 0;
    while let Some(relative_start) = source[search_start..].find("/**") {
        let comment_start = search_start + relative_start;
        let body_start = comment_start + 3;
        let Some(relative_end) = source[body_start..].find("*/") else {
            break;
        };
        let comment_end = body_start + relative_end;
        let comment = &source[body_start..comment_end];
        let mut import_search = 0;
        while let Some(relative_import) = comment[import_search..].find("import(") {
            let import_start = body_start + import_search + relative_import;
            let argument_start = import_start + "import(".len();
            let argument = &source[argument_start..comment_end];
            let whitespace = argument.len() - argument.trim_start().len();
            let quote_start = argument_start + whitespace;
            let Some(quote @ ('\'' | '"')) = source[quote_start..].chars().next() else {
                import_search += relative_import + "import(".len();
                continue;
            };
            let value_start = quote_start + quote.len_utf8();
            let Some(value_end_relative) = source[value_start..comment_end].find(quote) else {
                import_search += relative_import + "import(".len();
                continue;
            };
            let value_end = value_start + value_end_relative;
            let after_quote = &source[value_end + quote.len_utf8()..comment_end];
            if !after_quote.trim_start().starts_with(')') {
                import_search += relative_import + "import(".len();
                continue;
            }
            specifiers.push((
                source[value_start..value_end].to_owned(),
                TextRange::new(
                    TextPos::new(u32::try_from(value_start).unwrap_or(u32::MAX)),
                    TextPos::new(u32::try_from(value_end).unwrap_or(u32::MAX)),
                ),
                true,
            ));
            import_search = value_end.saturating_sub(body_start);
        }
        search_start = comment_end + 2;
    }
    specifiers
}

fn register_ambient_external_modules(
    source_file: &SourceFile,
    current_directory: &str,
    case_sensitivity: CaseSensitivity,
    modules: &mut BTreeMap<String, String>,
) {
    if source_file.is_default_library || source_file_is_external_module(&source_file.parse) {
        return;
    }
    let Some(NodeData::SourceFile(source)) = source_file
        .parse
        .arena
        .get(source_file.parse.source_file)
        .map(|node| &node.data)
    else {
        return;
    };
    let target = canonicalize(&source_file.file_name, current_directory, case_sensitivity);
    for statement in &source.statements.nodes {
        let Some(node) = source_file.parse.arena.get(*statement) else {
            continue;
        };
        let NodeData::ModuleDeclaration(module) = &node.data else {
            continue;
        };
        if !node_has_modifier(
            &source_file.parse.arena,
            module.modifiers.as_ref(),
            ts_ast::SyntaxKind::DeclareKeyword,
        ) {
            continue;
        }
        let Some((name, _)) = string_literal(&source_file.parse.arena, module.name) else {
            continue;
        };
        if !module_name_is_relative(&name) {
            modules.entry(name).or_insert_with(|| target.clone());
        }
    }
}

fn source_file_is_external_module(parse: &ParseResult) -> bool {
    let Some(NodeData::SourceFile(source)) =
        parse.arena.get(parse.source_file).map(|node| &node.data)
    else {
        return false;
    };
    source.statements.nodes.iter().any(|statement| {
        let Some(node) = parse.arena.get(*statement) else {
            return false;
        };
        matches!(
            node.data,
            NodeData::ImportDeclaration(_)
                | NodeData::ImportEqualsDeclaration(_)
                | NodeData::ExportDeclaration(_)
                | NodeData::ExportAssignment(_)
        ) || declaration_modifiers(node).is_some_and(|modifiers| {
            node_has_modifier(
                &parse.arena,
                Some(modifiers),
                ts_ast::SyntaxKind::ExportKeyword,
            )
        })
    })
}

fn amd_generated_dependency_bases(source: &SourceFile) -> Vec<String> {
    let Some(NodeData::SourceFile(file)) = source
        .parse
        .arena
        .get(source.parse.source_file)
        .map(|node| &node.data)
    else {
        return Vec::new();
    };
    file.statements
        .nodes
        .iter()
        .filter_map(|statement| {
            if source.checking.import_runtime_meanings.get(statement) == Some(&false) {
                return None;
            }
            let Some(NodeData::ImportDeclaration(import)) =
                source.parse.arena.get(*statement).map(|node| &node.data)
            else {
                return None;
            };
            import.import_clause?;
            let (specifier, _) = string_literal(&source.parse.arena, import.module_specifier)?;
            Some(module_temp_base(&specifier))
        })
        .collect()
}

fn module_temp_base(specifier: &str) -> String {
    let segment = specifier
        .rsplit('/')
        .find(|segment| !segment.is_empty())
        .unwrap_or("module");
    let stem = segment.split('.').next().unwrap_or(segment);
    let mut base = String::new();
    for (index, character) in stem.chars().enumerate() {
        if character == '_' || character == '$' || character.is_ascii_alphanumeric() {
            if index == 0 && character.is_ascii_digit() {
                base.push('_');
            }
            base.push(character);
        } else if !base.ends_with('_') {
            base.push('_');
        }
    }
    if base.is_empty() {
        "module".to_owned()
    } else {
        base
    }
}

fn declaration_modifiers(node: &ts_ast::Node) -> Option<&ts_ast::ModifierList> {
    match &node.data {
        NodeData::VariableStatement(data) => data.modifiers.as_ref(),
        NodeData::FunctionDeclaration(data) => data.modifiers.as_ref(),
        NodeData::ClassDeclaration(data) => data.modifiers.as_ref(),
        NodeData::InterfaceDeclaration(data) => data.modifiers.as_ref(),
        NodeData::TypeAliasDeclaration(data) => data.modifiers.as_ref(),
        NodeData::EnumDeclaration(data) => data.modifiers.as_ref(),
        NodeData::ModuleDeclaration(data) => data.modifiers.as_ref(),
        NodeData::ImportDeclaration(data) => data.modifiers.as_ref(),
        NodeData::ImportEqualsDeclaration(data) => data.modifiers.as_ref(),
        _ => None,
    }
}

fn node_has_modifier(
    arena: &ts_ast::NodeArena,
    modifiers: Option<&ts_ast::ModifierList>,
    kind: ts_ast::SyntaxKind,
) -> bool {
    modifiers.is_some_and(|modifiers| {
        modifiers
            .list
            .nodes
            .iter()
            .any(|modifier| arena.get(*modifier).is_some_and(|node| node.kind == kind))
    })
}

fn module_name_is_relative(name: &str) -> bool {
    name.starts_with("./")
        || name.starts_with("../")
        || name.starts_with(".\\")
        || name.starts_with("..\\")
}

fn string_literal(arena: &ts_ast::NodeArena, id: NodeId) -> Option<(String, TextRange)> {
    let node = arena.get(id)?;
    let NodeData::StringLiteral(data) = &node.data else {
        return None;
    };
    Some((data.text.clone(), node.range))
}

fn missing_file_diagnostic(file_name: &str) -> ProgramDiagnostic {
    let message = message_by_code(6053).expect("TS6053 must be in the generated catalog");
    ProgramDiagnostic {
        file_name: None,
        range: None,
        code: Some(message.code()),
        message: message
            .format(&[file_name.to_owned()])
            .expect("TS6053 has one formatting argument"),
    }
}

fn output_overwrites_input_diagnostic(file_name: &str) -> ProgramDiagnostic {
    let message = message_by_code(5055).expect("TS5055 must be in the generated catalog");
    ProgramDiagnostic {
        file_name: None,
        range: None,
        code: Some(message.code()),
        message: message
            .format(&[file_name.to_owned()])
            .expect("TS5055 has one formatting argument"),
    }
}

fn output_collision_diagnostic(file_name: &str) -> ProgramDiagnostic {
    let message = message_by_code(5056).expect("TS5056 must be in the generated catalog");
    ProgramDiagnostic {
        file_name: None,
        range: None,
        code: Some(message.code()),
        message: message
            .format(&[file_name.to_owned()])
            .expect("TS5056 has one formatting argument"),
    }
}

fn suppress_output_path_collisions(
    output: &mut EmitOutput,
    current_directory: &str,
    case_sensitivity: CaseSensitivity,
) {
    let mut paths = BTreeMap::<String, (String, usize)>::new();
    for file in &output.files {
        let canonical = canonicalize(&file.file_name, current_directory, case_sensitivity);
        let entry = paths
            .entry(canonical)
            .or_insert_with(|| (file.file_name.clone(), 0));
        entry.1 += 1;
    }
    let collisions = paths
        .into_iter()
        .filter_map(|(canonical, (file_name, count))| (count > 1).then_some((canonical, file_name)))
        .collect::<BTreeMap<_, _>>();
    if collisions.is_empty() {
        return;
    }
    output.files.retain(|file| {
        let canonical = canonicalize(&file.file_name, current_directory, case_sensitivity);
        !collisions.contains_key(&canonical)
    });
    output.diagnostics.extend(
        collisions
            .into_values()
            .map(|file_name| output_collision_diagnostic(&file_name)),
    );
}

fn emit_declaration_only_diagnostic() -> ProgramDiagnostic {
    let message = message_by_code(5069).expect("TS5069 must be in the generated catalog");
    ProgramDiagnostic {
        file_name: None,
        range: None,
        code: Some(message.code()),
        message: message
            .format(&[
                "emitDeclarationOnly".to_owned(),
                "declaration".to_owned(),
                "composite".to_owned(),
            ])
            .expect("TS5069 has three formatting arguments"),
    }
}

fn module_not_found_diagnostic(
    file_name: &str,
    range: TextRange,
    specifier: &str,
) -> ProgramDiagnostic {
    let message = message_by_code(2307).expect("TS2307 must be in the generated catalog");
    ProgramDiagnostic {
        file_name: Some(file_name.to_owned()),
        range: Some(range),
        code: Some(message.code()),
        message: message
            .format(&[specifier.to_owned()])
            .expect("TS2307 has one formatting argument"),
    }
}

fn type_definition_not_found(name: &str) -> ProgramDiagnostic {
    let message = message_by_code(2688).expect("TS2688 must be in the generated catalog");
    ProgramDiagnostic {
        file_name: None,
        range: None,
        code: Some(message.code()),
        message: message
            .format(&[name.to_owned()])
            .expect("TS2688 has one formatting argument"),
    }
}

fn config_diagnostic(diagnostic: &ConfigDiagnostic) -> ProgramDiagnostic {
    ProgramDiagnostic {
        file_name: Some(diagnostic.file_name.clone()),
        range: None,
        code: Some(diagnostic.code()),
        message: diagnostic.render(),
    }
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;
    use std::time::{Duration, Instant};

    use ts_options::{CompilerOptions, ModuleKind, ScriptTarget};
    use ts_vfs::{FileSystem, MemoryFileSystem};

    use super::{Program, defer_export_only_bundle_imports};

    #[test]
    fn parses_and_indexes_explicit_roots() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file("/project/main.ts", "const answer: number = 40 + 2;")
            .unwrap();
        let program = Program::new(&fs, "/project", &["main.ts".to_owned()]);
        assert!(
            program.diagnostics().is_empty(),
            "{:?}",
            program.diagnostics()
        );
        assert_eq!(program.source_files().len(), 1);
        assert!(program.source_file("/project/main.ts").is_some());
    }

    #[test]
    fn reports_missing_files_and_deduplicates_canonical_names() {
        let fs = MemoryFileSystem::new(false);
        fs.write_file("/project/Main.ts", "const value = 1;")
            .unwrap();
        let program = Program::new(
            &fs,
            "/project",
            &[
                "Main.ts".to_owned(),
                "main.ts".to_owned(),
                "missing.ts".to_owned(),
            ],
        );
        assert_eq!(program.source_files().len(), 1);
        assert_eq!(program.diagnostics().len(), 1);
        assert_eq!(program.diagnostics()[0].code, Some(6053));
    }

    #[test]
    fn propagates_parser_diagnostic_codes() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file("/project/main.ts", "function () { const value = ;")
            .unwrap();
        let program = Program::new(&fs, "/project", &["main.ts".to_owned()]);
        for code in [1003, 1109, 1005] {
            assert!(
                program
                    .diagnostics()
                    .iter()
                    .any(|diagnostic| diagnostic.code == Some(code)),
                "missing TS{code}: {:?}",
                program.diagnostics()
            );
        }
    }

    #[test]
    fn suppresses_declaration_with_private_imported_expando_property_type() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/a.ts",
            "interface I {} export function f(): I { return null as I; }",
        )
        .unwrap();
        fs.write_file(
            "/project/b.ts",
            concat!(
                "import { f } from './a';\n",
                "export function q() {}\n",
                "q.val = f();",
            ),
        )
        .unwrap();
        let program = Program::new_with_options(
            &fs,
            "/project",
            &["a.ts".to_owned(), "b.ts".to_owned()],
            CompilerOptions {
                declaration: true,
                module: ModuleKind::CommonJs,
                no_lib: true,
                ..CompilerOptions::default()
            },
        );
        assert!(
            program
                .diagnostics()
                .iter()
                .any(|diagnostic| diagnostic.code == Some(4032)),
            "{:?}",
            program.diagnostics()
        );
        let emitted = program.emit();
        assert!(
            emitted
                .files
                .iter()
                .any(|file| file.file_name.ends_with("a.d.ts")),
            "{:?}",
            emitted.files
        );
        assert!(
            !emitted
                .files
                .iter()
                .any(|file| file.file_name.ends_with("b.d.ts")),
            "{:?}",
            emitted.files
        );
    }

    #[test]
    fn constructs_roots_from_config_files() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/tsconfig.json",
            "{ \"files\": [\"src/a.ts\", \"src/b.ts\"], \"compilerOptions\": { \"noLib\": true } }",
        )
        .unwrap();
        fs.write_file("/project/src/a.ts", "let a = 1;").unwrap();
        fs.write_file("/project/src/b.ts", "let b = 2;").unwrap();
        let program = Program::from_config(&fs, "/project/tsconfig.json");
        assert_eq!(
            program
                .source_files()
                .iter()
                .filter(|file| !file.is_default_library)
                .count(),
            2
        );
        assert!(program.diagnostics().is_empty());
    }

    #[test]
    fn loads_explicit_and_automatic_type_directives() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file("/project/main.ts", "ENV_GLOBAL; AUTO_GLOBAL;")
            .unwrap();
        fs.write_file(
            "/project/types/env/index.d.ts",
            "declare const ENV_GLOBAL: string;",
        )
        .unwrap();
        fs.write_file(
            "/project/node_modules/@types/auto/index.d.ts",
            "declare const AUTO_GLOBAL: number;",
        )
        .unwrap();
        fs.write_file(
            "/project/tsconfig.json",
            r#"{
                "files": ["main.ts"],
                "compilerOptions": {
                    "noLib": true,
                    "typeRoots": ["types", "node_modules/@types"],
                    "types": ["env", "auto", "missing"]
                }
            }"#,
        )
        .unwrap();
        let program = Program::from_config(&fs, "/project/tsconfig.json");
        assert!(
            program
                .source_file("/project/types/env/index.d.ts")
                .is_some()
        );
        assert!(
            program
                .source_file("/project/node_modules/@types/auto/index.d.ts")
                .is_some()
        );
        assert_eq!(
            program
                .diagnostics()
                .iter()
                .filter_map(|diagnostic| diagnostic.code)
                .collect::<Vec<_>>(),
            [2688]
        );

        fs.write_file(
            "/project/automatic.json",
            r#"{"files":["main.ts"],"compilerOptions":{"noLib":true}}"#,
        )
        .unwrap();
        let automatic = Program::from_config(&fs, "/project/automatic.json");
        assert!(
            automatic
                .source_file("/project/node_modules/@types/auto/index.d.ts")
                .is_some()
        );
    }

    #[test]
    fn follows_triple_slash_path_type_and_lib_references() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/main.ts",
            concat!(
                "/// <reference path='./globals.d.ts' />\n",
                "/// <reference types=\"pkg\" />\n",
                "/// <reference lib='es2015.promise' />\n",
                "GLOBAL; NESTED; PACKAGE_GLOBAL; Promise;\n",
            ),
        )
        .unwrap();
        fs.write_file(
            "/project/globals.d.ts",
            "/// <reference path='./nested.d.ts' />\ndeclare const GLOBAL: string;",
        )
        .unwrap();
        fs.write_file("/project/nested.d.ts", "declare const NESTED: number;")
            .unwrap();
        fs.write_file(
            "/project/node_modules/@types/pkg/index.d.ts",
            "declare const PACKAGE_GLOBAL: boolean;",
        )
        .unwrap();
        let program = Program::new_with_options(
            &fs,
            "/project",
            &["main.ts".to_owned()],
            CompilerOptions {
                no_lib: true,
                ..CompilerOptions::default()
            },
        );
        assert!(
            program.diagnostics().is_empty(),
            "{:?}",
            program.diagnostics()
        );
        for file in [
            "/project/globals.d.ts",
            "/project/nested.d.ts",
            "/project/node_modules/@types/pkg/index.d.ts",
            "/__typescript/lib/lib.es2015.promise.d.ts",
        ] {
            assert!(program.source_file(file).is_some(), "missing {file}");
        }

        fs.write_file(
            "/project/no-default.ts",
            "/// <reference no-default-lib='true' />\nArray;",
        )
        .unwrap();
        let no_default = Program::new_with_options(
            &fs,
            "/project",
            &["no-default.ts".to_owned()],
            CompilerOptions::default(),
        );
        assert!(no_default.options().no_lib);
        assert!(
            no_default
                .diagnostics()
                .iter()
                .any(|diagnostic| diagnostic.code == Some(2304))
        );
    }

    #[test]
    fn preserved_declaration_references_are_canonical_and_target_declarations() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file("/project/dep.ts", "export interface Dep {}")
            .unwrap();
        fs.write_file(
            "/project/node_modules/@types/pkg/index.d.ts",
            "declare interface PackageType {}",
        )
        .unwrap();
        fs.write_file(
            "/project/main.ts",
            concat!(
                "///<reference path='dep.ts' preserve=\"true\" />\n",
                "///<reference types='pkg' preserve=\"true\" />\n",
                "export const value = 1;",
            ),
        )
        .unwrap();
        let program = Program::new_with_options(
            &fs,
            "/project",
            &["main.ts".to_owned()],
            CompilerOptions {
                declaration: true,
                no_lib: true,
                ..CompilerOptions::default()
            },
        );
        let emitted = program.emit();
        assert!(emitted.diagnostics.is_empty(), "{:?}", emitted.diagnostics);
        let declaration = emitted
            .files
            .iter()
            .find(|file| file.file_name == "/project/main.d.ts")
            .unwrap();
        assert!(
            declaration.text.starts_with(concat!(
                "/// <reference path=\"dep.d.ts\" preserve=\"true\" />\n",
                "/// <reference types=\"pkg\" preserve=\"true\" />\n",
            )),
            "{}",
            declaration.text
        );
    }

    #[test]
    fn declarations_use_named_classes_from_erroneous_ambient_inputs() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/declFile.d.ts",
            concat!(
                "declare namespace M {\n",
                "    declare var x;\n",
                "    declare function f();\n",
                "    declare namespace N {}\n",
                "    declare class C {}\n",
                "}\n",
            ),
        )
        .unwrap();
        fs.write_file(
            "/project/client.ts",
            concat!(
                "///<reference path=\"declFile.d.ts\" preserve=\"true\"/>\n",
                "var value = new M.C();\n",
            ),
        )
        .unwrap();
        let program = Program::new_with_options(
            &fs,
            "/project",
            &["client.ts".to_owned()],
            CompilerOptions {
                declaration: true,
                no_lib: true,
                target: ScriptTarget::Es2015,
                ..CompilerOptions::default()
            },
        );
        assert!(
            program
                .diagnostics()
                .iter()
                .any(|diagnostic| diagnostic.code == Some(1038)),
            "{:?}",
            program.diagnostics()
        );
        let emitted = program.emit();
        let declaration = emitted
            .files
            .iter()
            .find(|file| file.file_name == "/project/client.d.ts")
            .unwrap();
        assert!(
            declaration.text.contains("declare var value: M.C;"),
            "{}",
            declaration.text
        );
    }

    #[test]
    fn declaration_emit_recovers_inferred_class_method_signatures() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/input.ts",
            concat!(
                "interface Example {}\n",
                "class Example {\n",
                "    f() { return ''; }\n",
                "    h(x = 4, nullable = null, label = '') {}\n",
                "}\n",
            ),
        )
        .unwrap();
        let program = Program::new_with_options(
            &fs,
            "/project",
            &["input.ts".to_owned()],
            CompilerOptions {
                declaration: true,
                no_lib: true,
                strict: false,
                target: ScriptTarget::Es2015,
                ..CompilerOptions::default()
            },
        );
        let emitted = program.emit();
        assert!(emitted.diagnostics.is_empty(), "{:?}", emitted.diagnostics);
        let declaration = emitted
            .files
            .iter()
            .find(|file| file.file_name == "/project/input.d.ts")
            .unwrap();
        assert!(
            declaration.text.contains("f(): string;"),
            "{}",
            declaration.text
        );
        assert!(
            declaration
                .text
                .contains("h(x?: number, nullable?: any, label?: string): void;"),
            "{}",
            declaration.text
        );
    }

    #[test]
    fn bundled_declarations_preserve_deduplicated_references_without_declaration_inputs() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/declFile.d.ts",
            concat!(
                "declare namespace M {\n",
                "    declare var x;\n",
                "    declare function f();\n",
                "    declare namespace N {}\n",
                "    declare class C {}\n",
                "}\n",
            ),
        )
        .unwrap();
        for file in ["client.ts", "other.ts"] {
            fs.write_file(
                &format!("/project/{file}"),
                concat!(
                    "///<reference path=\"declFile.d.ts\" preserve=\"true\"/>\n",
                    "var value = new M.C();\n",
                ),
            )
            .unwrap();
        }
        let program = Program::new_with_options(
            &fs,
            "/project",
            &[
                "declFile.d.ts".to_owned(),
                "client.ts".to_owned(),
                "other.ts".to_owned(),
            ],
            CompilerOptions {
                declaration: true,
                out_file: Some("out.js".into()),
                no_lib: true,
                target: ScriptTarget::Es2015,
                ..CompilerOptions::default()
            },
        );
        assert!(
            program
                .diagnostics()
                .iter()
                .any(|diagnostic| diagnostic.code == Some(1038)),
            "{:?}",
            program.diagnostics()
        );
        let emitted = program.emit();
        let declaration = emitted
            .files
            .iter()
            .find(|file| file.file_name == "/project/out.d.ts")
            .unwrap();
        let directive = "/// <reference path=\"declFile.d.ts\" preserve=\"true\" />";
        assert_eq!(declaration.text.matches(directive).count(), 1);
        assert!(declaration.text.starts_with(directive));
        assert!(declaration.text.contains("declare var value: M.C;"));
        assert!(!declaration.text.contains("declare namespace M"));
    }

    #[test]
    fn discovers_config_include_patterns() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/tsconfig.json",
            "{ \"include\": [\"src/**/*.ts\"], \"exclude\": [\"src/generated\"], \"compilerOptions\": { \"noLib\": true } }",
        )
        .unwrap();
        fs.write_file("/project/src/a.ts", "let a = 1;").unwrap();
        fs.write_file("/project/src/nested/b.ts", "let b = 2;")
            .unwrap();
        fs.write_file("/project/src/generated/c.ts", "let c = 3;")
            .unwrap();
        let program = Program::from_config(&fs, "/project/tsconfig.json");
        assert_eq!(
            program
                .source_files()
                .iter()
                .filter(|file| !file.is_default_library)
                .count(),
            2
        );
        assert!(program.diagnostics().is_empty());
    }

    #[test]
    fn resolves_inherited_options_and_base_relative_globs() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/repo/base/tsconfig.json",
            r#"{
                "include": ["src/**/*.ts"],
                "exclude": ["src/generated"],
                "compilerOptions": { "target": "es2015", "noLib": true }
            }"#,
        )
        .unwrap();
        fs.write_file(
            "/repo/app/tsconfig.json",
            r#"{"extends":"../base/tsconfig.json"}"#,
        )
        .unwrap();
        fs.write_file("/repo/base/src/a.ts", "const a = 1;")
            .unwrap();
        fs.write_file("/repo/base/src/nested/b.ts", "const b = 2;")
            .unwrap();
        fs.write_file("/repo/base/src/generated/skip.ts", "const skip = 3;")
            .unwrap();
        fs.write_file("/repo/app/unrelated.ts", "const unrelated = 4;")
            .unwrap();

        let program = Program::from_config(&fs, "/repo/app/tsconfig.json");
        assert!(
            program.diagnostics().is_empty(),
            "{:?}",
            program.diagnostics()
        );
        assert_eq!(program.options().target, ts_options::ScriptTarget::Es2015);
        assert_eq!(
            program
                .source_files()
                .iter()
                .filter(|file| !file.is_default_library)
                .count(),
            2
        );
        assert!(program.source_file("/repo/base/src/a.ts").is_some());
        assert!(program.source_file("/repo/base/src/nested/b.ts").is_some());
        assert!(
            program
                .source_file("/repo/base/src/generated/skip.ts")
                .is_none()
        );
        assert!(program.source_file("/repo/app/unrelated.ts").is_none());
    }

    #[test]
    fn retains_parser_diagnostics_with_file_ranges() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file("/bad.ts", "const value: = ;").unwrap();
        let program = Program::new(&fs, "/", &["bad.ts".to_owned()]);
        assert!(!program.diagnostics().is_empty());
        assert_eq!(
            program.diagnostics()[0].file_name.as_deref(),
            Some("/bad.ts")
        );
        assert!(program.diagnostics()[0].range.is_some());
    }

    #[test]
    fn emits_recovered_class_statements_and_erases_keyword_named_interfaces() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/class.ts",
            "class C { public const var export foo = 10; var constructor() { } }",
        )
        .unwrap();
        fs.write_file("/interface.ts", "interface string {}")
            .unwrap();
        let options = CompilerOptions {
            no_lib: true,
            target: ScriptTarget::Es2015,
            ..CompilerOptions::default()
        };

        let class_program =
            Program::new_with_options(&fs, "/", &["class.ts".to_owned()], options.clone());
        let class_output = class_program.emit();
        assert!(
            class_output.diagnostics.is_empty(),
            "{:?}",
            class_output.diagnostics
        );
        assert_eq!(class_output.files.len(), 1);
        assert!(class_output.files[0].text.contains("var constructor;"));
        assert!(class_output.files[0].text.contains("() => { };"));

        let interface_program =
            Program::new_with_options(&fs, "/", &["interface.ts".to_owned()], options);
        let interface_output = interface_program.emit();
        assert!(
            interface_output.diagnostics.is_empty(),
            "{:?}",
            interface_output.diagnostics
        );
        assert_eq!(interface_output.files.len(), 1);
        assert_eq!(interface_output.files[0].text, "\"use strict\";\n");
        assert_eq!(
            interface_program
                .diagnostics()
                .iter()
                .filter_map(|diagnostic| diagnostic.code)
                .collect::<Vec<_>>(),
            [2427]
        );
    }

    #[test]
    fn reports_missing_function_implementations_without_rejecting_ambient_declarations() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/main.ts",
            r"
                namespace M { function foo(); }
                function valid(value: string): string;
                function valid(value: string): string { return value; }
            ",
        )
        .unwrap();
        fs.write_file(
            "/project/tsconfig.json",
            r#"{
                "files": ["main.ts"],
                "compilerOptions": {
                    "noLib": true,
                    "noEmit": true,
                    "noImplicitAny": true
                }
            }"#,
        )
        .unwrap();
        let program = Program::from_config(&fs, "/project/tsconfig.json");
        assert_eq!(
            program
                .diagnostics()
                .iter()
                .filter_map(|diagnostic| diagnostic.code)
                .collect::<Vec<_>>(),
            [2391, 7010]
        );

        fs.write_file(
            "/project/ambient.d.ts",
            "function fromDeclarationFile(); declare function explicitlyAmbient();",
        )
        .unwrap();
        let ambient = Program::new_with_options(
            &fs,
            "/project",
            &["ambient.d.ts".to_owned()],
            CompilerOptions {
                no_lib: true,
                no_emit: true,
                ..CompilerOptions::default()
            },
        );
        assert!(
            ambient.diagnostics().is_empty(),
            "{:?}",
            ambient.diagnostics()
        );
    }

    #[test]
    fn accepts_dotted_ambient_namespace_declarations() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/main.ts",
            "declare namespace Foo.Bar { export var foo; }; Foo.Bar.foo = 5;",
        )
        .unwrap();
        let program = Program::new_with_options(
            &fs,
            "/project",
            &["main.ts".to_owned()],
            CompilerOptions {
                no_lib: true,
                no_emit: true,
                target: ScriptTarget::Es2015,
                ..CompilerOptions::default()
            },
        );
        assert!(
            program.diagnostics().is_empty(),
            "{:?}",
            program.diagnostics()
        );
    }

    #[test]
    fn binds_files_and_reports_duplicate_block_declarations() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file("/duplicate.ts", "let value = 1; let value = 2;")
            .unwrap();
        let program = Program::new(&fs, "/", &["duplicate.ts".to_owned()]);
        assert_eq!(program.source_files()[0].binding.symbols.len(), 1);
        assert!(
            program
                .diagnostics()
                .iter()
                .any(|diagnostic| diagnostic.code == Some(2451))
        );
    }

    #[test]
    fn ambient_external_modules_do_not_conflict_with_global_block_variables() {
        for module in [ModuleKind::CommonJs, ModuleKind::Preserve] {
            let fs = MemoryFileSystem::new(true);
            fs.write_file(
                "/project/node.d.ts",
                r#"
                    declare function require(moduleName: string): any;
                    declare module "fs" {
                        export function readFileSync(path: string): string;
                    }
                "#,
            )
            .unwrap();
            fs.write_file(
                "/project/app.js",
                r#"const fs = require("fs"); fs.readFileSync("/a/b/c");"#,
            )
            .unwrap();
            let program = Program::new_with_options(
                &fs,
                "/project",
                &["node.d.ts".to_owned(), "app.js".to_owned()],
                CompilerOptions {
                    allow_js: true,
                    module,
                    no_lib: true,
                    ..CompilerOptions::default()
                },
            );
            assert!(
                !program
                    .diagnostics()
                    .iter()
                    .any(|diagnostic| diagnostic.code == Some(2451)),
                "{module:?}: {:?}",
                program.diagnostics()
            );
        }

        let fs = MemoryFileSystem::new(true);
        fs.write_file("/project/first.ts", "const collision = 1;")
            .unwrap();
        fs.write_file("/project/second.ts", "const collision = 2;")
            .unwrap();
        let program = Program::new_with_options(
            &fs,
            "/project",
            &["first.ts".to_owned(), "second.ts".to_owned()],
            CompilerOptions {
                no_lib: true,
                ..CompilerOptions::default()
            },
        );
        assert!(
            program
                .diagnostics()
                .iter()
                .any(|diagnostic| diagnostic.code == Some(2451)),
            "{:?}",
            program.diagnostics()
        );
    }

    #[test]
    fn follows_relative_imports_and_reports_unresolved_modules() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/main.ts",
            "import { value } from './dep.js'; import './missing'; value;",
        )
        .unwrap();
        fs.write_file("/project/dep.ts", "export const value = 1;")
            .unwrap();
        let program = Program::new_with_module_resolution(
            &fs,
            "/project",
            &["main.ts".to_owned()],
            ts_module::ResolutionOptions::default(),
        );
        assert_eq!(program.source_files().len(), 2);
        assert!(program.source_file("/project/dep.ts").is_some());
        assert!(
            program
                .diagnostics()
                .iter()
                .any(|diagnostic| diagnostic.code == Some(2307))
        );
    }

    #[test]
    fn resolves_external_import_equals_module_references() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/main.ts",
            concat!(
                "import present = require('./dep');\n",
                "import nested = present.value;\n",
                "import missing = require('./missing');\n",
                "present.value; nested; missing;\n",
            ),
        )
        .unwrap();
        fs.write_file("/project/dep.ts", "export const value = 1;")
            .unwrap();

        let program = Program::new_with_module_resolution(
            &fs,
            "/project",
            &["main.ts".to_owned()],
            ts_module::ResolutionOptions::default(),
        );
        assert!(program.source_file("/project/dep.ts").is_some());
        assert_eq!(
            program
                .diagnostics()
                .iter()
                .filter(|diagnostic| diagnostic.code == Some(2307))
                .count(),
            1
        );
    }

    #[test]
    fn resolves_import_equals_against_top_level_ambient_modules() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/ambient.ts",
            r#"declare module "M" { const value: number; }"#,
        )
        .unwrap();
        fs.write_file("/project/main.ts", r#"import M = require("M"); M.value;"#)
            .unwrap();

        let program = Program::new_with_module_resolution(
            &fs,
            "/project",
            &["main.ts".to_owned(), "ambient.ts".to_owned()],
            ts_module::ResolutionOptions::default(),
        );
        assert!(
            !program
                .diagnostics()
                .iter()
                .any(|diagnostic| diagnostic.code == Some(2307)),
            "{:?}",
            program.diagnostics()
        );
        assert_eq!(
            program
                .resolved_modules
                .get(&("/project/main.ts".to_owned(), "M".to_owned()))
                .map(String::as_str),
            Some("/project/ambient.ts")
        );
    }

    #[test]
    fn resolves_es_imports_against_top_level_ambient_modules() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/ambient.d.ts",
            r#"declare module "url" { export class Url {} export function parse(): Url; }"#,
        )
        .unwrap();
        fs.write_file(
            "/project/main.ts",
            r#"import { parse } from "url"; export const thing = parse();"#,
        )
        .unwrap();
        let program = Program::new_with_options(
            &fs,
            "/project",
            &["main.ts".to_owned(), "ambient.d.ts".to_owned()],
            CompilerOptions {
                declaration: true,
                emit_declaration_only: true,
                no_lib: true,
                ..CompilerOptions::default()
            },
        );
        assert!(
            !program
                .diagnostics()
                .iter()
                .any(|diagnostic| diagnostic.code == Some(2307)),
            "{:?}",
            program.diagnostics()
        );
        let declaration = program
            .emit()
            .files
            .into_iter()
            .find(|file| file.file_name == "/project/main.d.ts")
            .unwrap();
        assert_eq!(
            declaration.text,
            "export declare const thing: import(\"url\").Url;\n"
        );
    }

    #[test]
    fn elides_semantically_type_only_imports_from_merged_ambient_modules() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/ambient.ts",
            r#"
                declare module "foo" {
                    namespace B { export interface A {} }
                    interface B { bar(name: string): B.A; }
                    export = B;
                }
                declare module "runtime" {
                    class Runtime {}
                    export = Runtime;
                }
            "#,
        )
        .unwrap();
        fs.write_file(
            "/project/main.ts",
            concat!(
                "///<reference path='ambient.ts' />\n",
                "import foo = require(\"foo\");\n",
                "import Runtime = require(\"runtime\");\n",
                "import Missing = require(\"missing\");\n",
                "import \"foo\";\n",
                "declare var z: foo;\n",
                "z.bar(\"hello\");\n",
                "var x: foo.A = foo.bar(\"hello\");\n",
                "new Runtime();\n",
                "Missing.run();\n",
            ),
        )
        .unwrap();
        let program = Program::new_with_options(
            &fs,
            "/project",
            &["main.ts".to_owned(), "ambient.ts".to_owned()],
            CompilerOptions {
                module: ModuleKind::CommonJs,
                target: ScriptTarget::Es2015,
                no_lib: true,
                ..CompilerOptions::default()
            },
        );
        let emitted = program.emit();
        assert!(emitted.diagnostics.is_empty(), "{:?}", emitted.diagnostics);
        let javascript = emitted
            .files
            .iter()
            .find(|file| file.file_name == "/project/main.js")
            .unwrap();
        assert!(!javascript.text.contains("const foo = require(\"foo\")"));
        assert!(!javascript.text.contains("reference path"));
        assert!(
            javascript
                .text
                .contains("const Runtime = require(\"runtime\");")
        );
        assert!(
            javascript
                .text
                .contains("const Missing = require(\"missing\");")
        );
        assert!(javascript.text.contains("require(\"foo\");"));
        assert!(javascript.text.contains("foo.bar(\"hello\")"));
    }

    #[test]
    fn emits_amd_wrapper_for_ambient_import_equals_consumer() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/ambient.ts",
            r#"declare module "M" { const value: number; }"#,
        )
        .unwrap();
        fs.write_file(
            "/project/main.ts",
            concat!(
                "///<amd-module name='Consumer'/>\n",
                "///<amd-dependency path='side' name='side'/>\n",
                "import M = require(\"M\");\n",
                "M.value;\n",
            ),
        )
        .unwrap();

        let program = Program::new_with_options(
            &fs,
            "/project",
            &["main.ts".to_owned(), "ambient.ts".to_owned()],
            CompilerOptions {
                module: ModuleKind::Amd,
                target: ScriptTarget::Es2015,
                no_lib: true,
                ..CompilerOptions::default()
            },
        );
        assert!(
            program.diagnostics().is_empty(),
            "{:?}",
            program.diagnostics()
        );
        let emitted = program.emit();
        assert!(emitted.diagnostics.is_empty(), "{:?}", emitted.diagnostics);
        let javascript = emitted
            .files
            .iter()
            .find(|file| file.file_name == "/project/main.js")
            .unwrap();
        assert_eq!(
            javascript.text,
            concat!(
                "///<amd-dependency path='side' name='side'/>\n",
                "define(\"Consumer\", [\"require\", \"exports\", \"side\", \"M\"], function (require, exports, side, M) {\n",
                "    \"use strict\";\n",
                "    Object.defineProperty(exports, \"__esModule\", { value: true });\n",
                "    ///<amd-module name='Consumer'/>\n",
                "    M.value;\n",
                "});\n",
            )
        );
    }

    #[test]
    fn amd_elides_import_equals_used_only_in_erased_generic_types() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/types.ts",
            "interface Foo<T> { value: T; } export = Foo;",
        )
        .unwrap();
        fs.write_file(
            "/project/main.ts",
            "import Foo = require(\"./types\"); export let value: Foo<string>;",
        )
        .unwrap();

        let program = Program::new_with_options(
            &fs,
            "/project",
            &["main.ts".to_owned(), "types.ts".to_owned()],
            CompilerOptions {
                module: ModuleKind::Amd,
                target: ScriptTarget::Es2015,
                declaration: true,
                no_lib: true,
                ..CompilerOptions::default()
            },
        );
        let emitted = program.emit();
        assert!(emitted.diagnostics.is_empty(), "{:?}", emitted.diagnostics);
        let javascript = emitted
            .files
            .iter()
            .find(|file| file.file_name == "/project/main.js")
            .unwrap();
        assert!(
            javascript
                .text
                .starts_with("define([\"require\", \"exports\"], function (require, exports)"),
            "{}",
            javascript.text
        );
        assert!(!javascript.text.contains("./types"), "{}", javascript.text);
    }

    #[test]
    fn relative_ambient_module_names_do_not_satisfy_resolution() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/ambient.ts",
            r#"declare module "./M" { const value: number; }"#,
        )
        .unwrap();
        fs.write_file("/project/main.ts", r#"import M = require("./M"); M.value;"#)
            .unwrap();

        let program = Program::new_with_module_resolution(
            &fs,
            "/project",
            &["main.ts".to_owned(), "ambient.ts".to_owned()],
            ts_module::ResolutionOptions::default(),
        );
        assert!(
            program
                .diagnostics()
                .iter()
                .any(|diagnostic| diagnostic.code == Some(2307)),
            "{:?}",
            program.diagnostics()
        );
    }

    #[test]
    fn module_augmentations_do_not_satisfy_ambient_resolution() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/augmentation.ts",
            r#"export {}; declare module "M" { const value: number; }"#,
        )
        .unwrap();
        fs.write_file("/project/main.ts", r#"import M = require("M"); M.value;"#)
            .unwrap();

        let program = Program::new_with_module_resolution(
            &fs,
            "/project",
            &["main.ts".to_owned(), "augmentation.ts".to_owned()],
            ts_module::ResolutionOptions::default(),
        );
        assert!(
            program
                .diagnostics()
                .iter()
                .any(|diagnostic| diagnostic.code == Some(2307)),
            "{:?}",
            program.diagnostics()
        );
    }

    #[test]
    fn checks_named_default_and_type_imports_across_files() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/dep.ts",
            r"
                export const count: number = 1;
                const internal: number = 2;
                export { internal as value };
                export type Box<T> = Array<T>;
                export default function label(value: string): string { return value; }
            ",
        )
        .unwrap();
        fs.write_file(
            "/project/main.ts",
            r#"
                import label, { count, value, Box } from "./dep";
                const total: number = count + value;
                const wrong: string = count;
                const boxed: Box<number> = [1, "wrong"];
                label(1);
            "#,
        )
        .unwrap();
        let program = Program::new_with_module_resolution(
            &fs,
            "/project",
            &["main.ts".to_owned()],
            ts_module::ResolutionOptions::default(),
        );
        assert_eq!(program.source_files().len(), 2);
        assert_eq!(
            program
                .diagnostics()
                .iter()
                .filter_map(|diagnostic| diagnostic.code)
                .collect::<Vec<_>>(),
            [2322, 2322, 2345]
        );
    }

    #[test]
    fn declaration_files_contribute_globals_and_report_duplicates() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/globals.d.ts",
            "interface Shared { value: string; } declare const duplicate: number;",
        )
        .unwrap();
        fs.write_file("/project/other.d.ts", "declare const duplicate: string;")
            .unwrap();
        fs.write_file(
            "/project/main.ts",
            "const good: Shared = { value: 'ok' }; const bad: Shared = { value: 1 };",
        )
        .unwrap();
        let program = Program::new(
            &fs,
            "/project",
            &[
                "globals.d.ts".to_owned(),
                "other.d.ts".to_owned(),
                "main.ts".to_owned(),
            ],
        );
        assert!(
            program
                .diagnostics()
                .iter()
                .any(|diagnostic| diagnostic.code == Some(2451))
        );
        assert!(
            program
                .diagnostics()
                .iter()
                .any(|diagnostic| diagnostic.code == Some(2322))
        );
        assert!(
            !program
                .diagnostics()
                .iter()
                .any(|diagnostic| diagnostic.code == Some(2304))
        );
    }

    #[test]
    fn resolves_nested_ambient_namespace_members_across_files() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/functions.d.ts",
            r"
                declare namespace A {
                    namespace AA {
                        function func(): number;
                    }
                }
            ",
        )
        .unwrap();
        fs.write_file(
            "/project/values.d.ts",
            "declare namespace A { namespace AA { const value: string; } }",
        )
        .unwrap();
        fs.write_file(
            "/project/main.ts",
            "const count: number = A.AA.func(); const text: string = A.AA.value;",
        )
        .unwrap();
        let program = Program::new_with_options(
            &fs,
            "/project",
            &[
                "main.ts".to_owned(),
                "functions.d.ts".to_owned(),
                "values.d.ts".to_owned(),
            ],
            CompilerOptions {
                no_lib: true,
                ..CompilerOptions::default()
            },
        );
        assert!(
            program.diagnostics().is_empty(),
            "{:?}",
            program.diagnostics()
        );
    }

    #[test]
    fn resolves_exported_namespaces_through_namespace_imports() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/library.ts",
            "export namespace Tools { export function value(): number { return 1; } }",
        )
        .unwrap();
        fs.write_file(
            "/project/main.ts",
            "import * as Library from './library'; const value: number = Library.Tools.value();",
        )
        .unwrap();
        let program = Program::new_with_options(
            &fs,
            "/project",
            &["main.ts".to_owned()],
            CompilerOptions {
                module: ModuleKind::EsNext,
                target: ScriptTarget::Es2015,
                no_lib: true,
                ..CompilerOptions::default()
            },
        );
        assert!(
            program.diagnostics().is_empty(),
            "{:?}",
            program.diagnostics()
        );
    }

    #[test]
    fn emits_type_erased_modern_javascript() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/main.ts",
            "interface Point { x: number } const point: Point = { x: 1 };",
        )
        .unwrap();
        let program = Program::new(&fs, "/project", &["main.ts".to_owned()]);
        let emitted = program.emit();
        assert!(emitted.diagnostics.is_empty());
        assert_eq!(emitted.files[0].file_name, "/project/main.js");
        assert_eq!(
            emitted.files[0].text,
            "\"use strict\";\nvar point = { x: 1 };\n"
        );
    }

    #[test]
    fn emit_paths_follow_jsx_and_module_extension_rules() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file("/project/view.tsx", "const view = 1;")
            .unwrap();
        fs.write_file("/project/module.mts", "const value = 1;")
            .unwrap();
        let program = Program::new(
            &fs,
            "/project",
            &["view.tsx".to_owned(), "module.mts".to_owned()],
        );
        let emitted = program.emit();
        let paths: Vec<_> = emitted
            .files
            .iter()
            .map(|file| file.file_name.as_str())
            .collect();
        assert!(paths.contains(&"/project/view.js"));
        assert!(paths.contains(&"/project/module.mjs"));
    }

    #[test]
    fn cts_sources_use_commonjs_and_import_async_helpers() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/notmodule.cts",
            concat!("export async function foo() {\n", "  await 0;\n", "}",),
        )
        .unwrap();
        let program = Program::new_with_options(
            &fs,
            "/project",
            &["notmodule.cts".to_owned()],
            CompilerOptions {
                import_helpers: true,
                module: ModuleKind::EsNext,
                target: ScriptTarget::Es2015,
                no_lib: true,
                ..CompilerOptions::default()
            },
        );
        let emitted = program.emit();
        let javascript = emitted
            .files
            .iter()
            .find(|file| file.file_name == "/project/notmodule.cjs")
            .unwrap();
        assert_eq!(
            javascript.text,
            concat!(
                "\"use strict\";\n",
                "Object.defineProperty(exports, \"__esModule\", { value: true });\n",
                "exports.foo = foo;\n",
                "const tslib_1 = require(\"tslib\");\n",
                "function foo() {\n",
                "    return tslib_1.__awaiter(this, void 0, void 0, function* () {\n",
                "        yield 0;\n",
                "    });\n",
                "}\n",
            )
        );
    }

    #[test]
    fn parses_and_emits_tsx_roots() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file("/project/view.tsx", "const view = <Box label=\"ok\" />;")
            .unwrap();
        let program = Program::new_with_options(
            &fs,
            "/project",
            &["view.tsx".to_owned()],
            CompilerOptions {
                no_lib: true,
                ..CompilerOptions::default()
            },
        );
        assert!(
            program.diagnostics().is_empty(),
            "{:?}",
            program.diagnostics()
        );
        let emitted = program.emit();
        assert!(emitted.diagnostics.is_empty(), "{:?}", emitted.diagnostics);
        assert_eq!(emitted.files.len(), 1);
        assert_eq!(emitted.files[0].file_name, "/project/view.js");
        assert_eq!(
            emitted.files[0].text,
            "\"use strict\";\nvar view = <Box label=\"ok\" />;\n"
        );
    }

    #[test]
    fn checks_annotated_variable_assignability() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/type-error.ts",
            "import { missing } from './absent'; const value: string = 1;",
        )
        .unwrap();
        let program = Program::new(&fs, "/", &["type-error.ts".to_owned()]);
        assert!(
            program
                .diagnostics()
                .iter()
                .any(|diagnostic| diagnostic.code == Some(2322))
        );
    }

    #[test]
    fn reports_enum_and_advanced_type_operator_diagnostics() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/advanced-types.ts",
            r#"
                enum State { Ready, Running = 3, Finished }
                type Record = { id: number; label: string };
                type Keys = keyof Record;
                type Values = Record[Keys];
                type Element<T> = T extends readonly (infer U)[] ? U : never;
                type Labels<T> = {
                    [K in keyof T as K extends "id" ? never : K]: T[K]
                };
                const state: State = "Ready";
                const key: Keys = "missing";
                const value: Values = false;
                const element: Element<string[]> = 1;
                const labels: Labels<Record> = { label: "ok", id: 1 };
            "#,
        )
        .unwrap();
        let program = Program::new_with_options(
            &fs,
            "/",
            &["advanced-types.ts".to_owned()],
            CompilerOptions {
                no_lib: true,
                ..CompilerOptions::default()
            },
        );
        assert_eq!(
            program
                .diagnostics()
                .iter()
                .filter_map(|diagnostic| diagnostic.code)
                .collect::<Vec<_>>(),
            [2322, 2322, 2322, 2322, 2353]
        );
    }

    #[test]
    fn no_check_skips_semantic_diagnostics() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file("/type-error.ts", "const value: string = 1;")
            .unwrap();
        let program = Program::new_with_options(
            &fs,
            "/",
            &["type-error.ts".to_owned()],
            CompilerOptions {
                no_check: true,
                no_lib: true,
                ..CompilerOptions::default()
            },
        );
        assert!(
            !program
                .diagnostics()
                .iter()
                .any(|diagnostic| matches!(diagnostic.code, Some(2307 | 2322)))
        );
        assert_eq!(program.emit().files.len(), 1);
    }

    #[test]
    fn emits_const_enum_accesses_as_commented_constants() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/const-enum.ts",
            concat!(
                "const enum TestType { foo, bar }\n",
                "type TestTypeStr = keyof typeof TestType;\n",
                "function f1(f: TestType) { }\n",
                "function f2(f: TestTypeStr) { }\n",
                "f1(TestType.foo)\n",
                "f1(TestType.bar)\n",
                "f2('foo')\n",
                "f2('bar')\n",
            ),
        )
        .unwrap();
        let program = Program::new_with_options(
            &fs,
            "/",
            &["const-enum.ts".to_owned()],
            CompilerOptions {
                target: ScriptTarget::Es2015,
                no_lib: true,
                ..CompilerOptions::default()
            },
        );
        let emitted = program.emit();
        assert_eq!(
            emitted.files[0].text,
            concat!(
                "\"use strict\";\n",
                "function f1(f) { }\n",
                "function f2(f) { }\n",
                "f1(0 /* TestType.foo */);\n",
                "f1(1 /* TestType.bar */);\n",
                "f2('foo');\n",
                "f2('bar');\n",
            )
        );
    }

    #[test]
    fn const_enum_emit_respects_preserve_isolated_and_no_check() {
        let source = "const enum E { Value = 1, Value2 = Value } E.Value2;";
        for (options, expected_access) in [
            (
                CompilerOptions {
                    preserve_const_enums: true,
                    target: ScriptTarget::Es2015,
                    no_lib: true,
                    ..CompilerOptions::default()
                },
                "1 /* E.Value2 */;",
            ),
            (
                CompilerOptions {
                    isolated_modules: true,
                    target: ScriptTarget::Es2015,
                    no_lib: true,
                    ..CompilerOptions::default()
                },
                "E.Value2;",
            ),
            (
                CompilerOptions {
                    no_check: true,
                    target: ScriptTarget::Es2015,
                    no_lib: true,
                    ..CompilerOptions::default()
                },
                "1 /* E.Value2 */;",
            ),
        ] {
            let fs = MemoryFileSystem::new(true);
            fs.write_file("/mode.ts", source).unwrap();
            let program = Program::new_with_options(&fs, "/", &["mode.ts".to_owned()], options);
            assert!(
                program.diagnostics().is_empty(),
                "{:?}",
                program.diagnostics()
            );
            let javascript = &program.emit().files[0].text;
            if javascript.contains("var E;") {
                assert!(javascript.contains("E[E[\"Value2\"] = 1] = \"Value2\";"));
            }
            assert!(javascript.contains(expected_access), "{javascript}");
        }
    }

    #[test]
    fn const_enum_fallbacks_do_not_capture_same_named_non_const_enums() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/scoped-enums.ts",
            concat!(
                "function ordinary() { return E.A; enum E { A } }\n",
                "function constant() { return E.A; const enum E { A } }\n",
                "const config = { a: After.A };\n",
                "const enum After { A = 2 }\n",
            ),
        )
        .unwrap();
        let program = Program::new_with_options(
            &fs,
            "/",
            &["scoped-enums.ts".to_owned()],
            CompilerOptions {
                target: ScriptTarget::Es2015,
                no_lib: true,
                ..CompilerOptions::default()
            },
        );
        let javascript = &program.emit().files[0].text;
        assert!(javascript.contains("return E.A;"), "{javascript}");
        assert!(javascript.contains("return 0 /* E.A */;"), "{javascript}");
        assert!(javascript.contains("a: 2 /* After.A */"), "{javascript}");
    }

    #[test]
    fn const_enum_property_accesses_inline_in_computed_names() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/property.ts",
            concat!(
                "const enum G { A = 1, B = 2, C = A + B, D = A * 2 }\n",
                "var o: { [idx: number]: boolean } = { 1: true };\n",
                "var a = G.A; var a1 = G[\"A\"]; var g = o[G.A];\n",
                "class C { [G.A]() { } get [G.B]() { return true; } set [G.B](x: number) { } }\n",
            ),
        )
        .unwrap();
        let program = Program::new_with_options(
            &fs,
            "/",
            &["property.ts".to_owned()],
            CompilerOptions {
                target: ScriptTarget::Es2015,
                no_lib: true,
                ..CompilerOptions::default()
            },
        );
        let javascript = &program.emit().files[0].text;
        assert!(!javascript.contains("var G;"), "{javascript}");
        for expected in [
            "1 /* G.A */",
            "1 /* G[\"A\"] */",
            "o[1 /* G.A */]",
            "[1 /* G.A */]()",
            "get [2 /* G.B */]()",
            "set [2 /* G.B */](x)",
        ] {
            assert!(
                javascript.contains(expected),
                "missing {expected}: {javascript}"
            );
        }
    }

    #[test]
    fn erased_exported_const_enum_has_no_commonjs_export() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/exported.ts",
            "export const enum E { A = 1 } export const value = E.A;",
        )
        .unwrap();
        let program = Program::new_with_options(
            &fs,
            "/",
            &["exported.ts".to_owned()],
            CompilerOptions {
                module: ModuleKind::CommonJs,
                target: ScriptTarget::Es2015,
                no_lib: true,
                ..CompilerOptions::default()
            },
        );
        let javascript = &program.emit().files[0].text;
        assert!(!javascript.contains("exports.E"), "{javascript}");
        assert!(
            javascript.contains("exports.value = 1 /* E.A */;"),
            "{javascript}"
        );
    }

    #[test]
    fn type_only_import_expression_does_not_emit_commonjs_helpers() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/p1/index.ts",
            concat!(
                "export interface Ref<T> { current: T; }\n",
                "export function useRef<T>(current: T): Ref<T> { return { current }; }\n",
                "export const useParser = () => useRef<typeof import(\"csv-parse\")>(null);\n",
            ),
        )
        .unwrap();
        fs.write_file(
            "/p1/node_modules/csv-parse/lib/index.d.ts",
            "export function bar(): number;",
        )
        .unwrap();
        fs.write_file(
            "/p1/node_modules/csv-parse/package.json",
            r#"{"main":"./lib","types":["./lib/index.d.ts"]}"#,
        )
        .unwrap();
        let program = Program::new_with_options(
            &fs,
            "/p1",
            &["index.ts".to_owned()],
            CompilerOptions {
                declaration: true,
                module: ModuleKind::CommonJs,
                target: ScriptTarget::Es2015,
                no_lib: true,
                ..CompilerOptions::default()
            },
        );
        assert!(
            program
                .source_file("/p1/node_modules/csv-parse/lib/index.d.ts")
                .is_some(),
            "{:?}",
            program.diagnostics()
        );
        let emitted = program.emit();
        let javascript = emitted
            .files
            .iter()
            .find(|file| file.file_name == "/p1/index.js")
            .unwrap();
        assert!(
            !javascript.text.contains("__createBinding"),
            "{javascript:?}"
        );
        let declaration = emitted
            .files
            .iter()
            .find(|file| file.file_name == "/p1/index.d.ts")
            .unwrap();
        assert!(
            declaration.text.contains("typeof import(\"csv-parse\")"),
            "{declaration:?}"
        );
    }

    #[test]
    fn no_emit_on_error_suppresses_all_outputs() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file("/type-error.ts", "const value: string = 1;")
            .unwrap();
        let program = Program::new_with_options(
            &fs,
            "/",
            &["type-error.ts".to_owned()],
            CompilerOptions {
                no_emit_on_error: true,
                no_lib: true,
                ..CompilerOptions::default()
            },
        );
        assert!(
            program
                .diagnostics()
                .iter()
                .any(|diagnostic| diagnostic.code == Some(2322))
        );
        assert!(program.emit().files.is_empty());

        let ordinary = Program::new_with_options(
            &fs,
            "/",
            &["type-error.ts".to_owned()],
            CompilerOptions {
                no_lib: true,
                ..CompilerOptions::default()
            },
        );
        assert_eq!(ordinary.emit().files.len(), 1);
    }

    #[test]
    fn out_file_concatenates_sources_once_in_root_order() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file("/project/first.ts", "const first = 1;")
            .unwrap();
        fs.write_file("/project/second.ts", "const second = 2;")
            .unwrap();
        let program = Program::new_with_options(
            &fs,
            "/project",
            &["second.ts".to_owned(), "first.ts".to_owned()],
            CompilerOptions {
                out_file: Some("dist/out.js".into()),
                module: ModuleKind::Amd,
                target: ScriptTarget::Es2015,
                source_map: true,
                no_lib: true,
                ..CompilerOptions::default()
            },
        );
        let emitted = program.emit();
        assert!(emitted.diagnostics.is_empty(), "{:?}", emitted.diagnostics);
        assert_eq!(emitted.files.len(), 2);
        let javascript = emitted
            .files
            .iter()
            .find(|file| file.file_name == "/project/dist/out.js")
            .unwrap();
        assert_eq!(
            javascript.text,
            "\"use strict\";\nconst second = 2;\nconst first = 1;\n//# sourceMappingURL=out.js.map\n"
        );
        let map = emitted
            .files
            .iter()
            .find(|file| file.file_name == "/project/dist/out.js.map")
            .unwrap();
        assert!(
            map.text
                .contains("\"sources\":[\"/project/second.ts\",\"/project/first.ts\"]")
        );
    }

    #[test]
    fn amd_out_file_emits_dependency_ordered_named_declaration_modules() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/Class.ts",
            concat!(
                "import { Configurable } from './Configurable';\n",
                "export class HiddenClass {}\n",
                "export class ActualClass extends Configurable(HiddenClass) {}\n",
            ),
        )
        .unwrap();
        fs.write_file(
            "/project/Configurable.ts",
            concat!(
                "export type Constructor<T = {}> = new (...args: any[]) => T;\n",
                "export function Configurable<TBase extends Constructor>(Base: TBase) { return Base; }\n",
            ),
        )
        .unwrap();

        let program = Program::new_with_module_resolution(
            &fs,
            "/project",
            &["Class.ts".to_owned()],
            ts_module::ResolutionOptions::default(),
        );
        let emitted = Program {
            options: CompilerOptions {
                declaration: true,
                out_file: Some("dist.js".into()),
                module: ModuleKind::Amd,
                target: ScriptTarget::Es2015,
                no_lib: true,
                ..CompilerOptions::default()
            },
            ..program
        }
        .emit();
        assert!(emitted.diagnostics.is_empty(), "{:?}", emitted.diagnostics);
        let declaration = emitted
            .files
            .iter()
            .find(|file| file.file_name == "/project/dist.d.ts")
            .unwrap();
        assert_eq!(
            declaration.text,
            concat!(
                "declare module \"Configurable\" {\n",
                "    export type Constructor<T = {}> = new (...args: any[]) => T;\n",
                "    export function Configurable<TBase extends Constructor>(Base: TBase): TBase;\n",
                "}\n",
                "declare module \"Class\" {\n",
                "    export class HiddenClass {\n",
                "    }\n",
                "    const ActualClass_base: typeof HiddenClass;\n",
                "    export class ActualClass extends ActualClass_base {\n",
                "    }\n",
                "}\n",
            )
        );
        let javascript = emitted
            .files
            .iter()
            .find(|file| file.file_name == "/project/dist.js")
            .unwrap();
        assert!(javascript.text.starts_with("define(\"Configurable\""));
        assert!(
            javascript
                .text
                .contains("define(\"Class\", [\"require\", \"exports\", \"Configurable\"]")
        );
    }

    #[test]
    fn amd_out_file_preserves_each_module_pragma_once_in_declarations() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/a.ts",
            "/// <amd-module name=\"NamedA\" />\nexport class Foo {}\n",
        )
        .unwrap();
        fs.write_file(
            "/project/b.ts",
            "/// <amd-module name=\"NamedB\" />\nexport class Bar {}\n",
        )
        .unwrap();
        let program = Program::new_with_options(
            &fs,
            "/project",
            &["a.ts".to_owned(), "b.ts".to_owned()],
            CompilerOptions {
                declaration: true,
                out_file: Some("out.js".into()),
                module: ModuleKind::Amd,
                target: ScriptTarget::Es2015,
                no_lib: true,
                ..CompilerOptions::default()
            },
        );
        let emitted = program.emit();
        assert!(emitted.diagnostics.is_empty(), "{:?}", emitted.diagnostics);
        let declaration = emitted
            .files
            .iter()
            .find(|file| file.file_name == "/project/out.d.ts")
            .unwrap();
        assert_eq!(
            declaration.text,
            concat!(
                "/// <amd-module name=\"NamedA\" />\n",
                "declare module \"NamedA\" {\n",
                "    export class Foo {\n",
                "    }\n",
                "}\n",
                "/// <amd-module name=\"NamedB\" />\n",
                "declare module \"NamedB\" {\n",
                "    export class Bar {\n",
                "    }\n",
                "}\n",
            )
        );
    }

    #[test]
    fn commonjs_out_file_bundles_declarations_with_late_export_names() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file("/project/index.ts", "export * from './nested';")
            .unwrap();
        fs.write_file(
            "/project/nested/base.ts",
            "import { B } from './shared'; export function f() { return new B(); }",
        )
        .unwrap();
        fs.write_file(
            "/project/nested/derived.ts",
            "import { f } from './base'; export function g() { return f(); }",
        )
        .unwrap();
        fs.write_file(
            "/project/nested/index.ts",
            "export * from './base'; export * from './derived'; export * from './shared';",
        )
        .unwrap();
        fs.write_file("/project/nested/shared.ts", "export class B {}")
            .unwrap();
        let program = Program::new_with_options(
            &fs,
            "/project",
            &["index.ts".to_owned()],
            CompilerOptions {
                declaration: true,
                emit_declaration_only: true,
                out_file: Some("dist/out.d.ts".into()),
                module: ModuleKind::CommonJs,
                target: ScriptTarget::Es2015,
                no_lib: true,
                ..CompilerOptions::default()
            },
        );
        let emitted = program.emit();
        assert!(emitted.diagnostics.is_empty(), "{:?}", emitted.diagnostics);
        let declaration = emitted
            .files
            .iter()
            .find(|file| file.file_name == "/project/dist/out.d.ts")
            .unwrap();
        assert_eq!(
            declaration.text,
            concat!(
                "declare module \"nested/shared\" {\n",
                "    export class B {\n",
                "    }\n",
                "}\n",
                "declare module \"nested/base\" {\n",
                "    import { B } from \"nested/shared\";\n",
                "    export function f(): B;\n",
                "}\n",
                "declare module \"nested/derived\" {\n",
                "    export function g(): import(\"nested\").B;\n",
                "}\n",
                "declare module \"nested/index\" {\n",
                "    export * from \"nested/base\";\n",
                "    export * from \"nested/derived\";\n",
                "    export * from \"nested/shared\";\n",
                "}\n",
                "declare module \"index\" {\n",
                "    export * from \"nested/index\";\n",
                "}\n",
            )
        );
    }

    #[test]
    fn path_mapped_ambient_return_types_emit_as_import_types() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/repo/packages/a/index.d.ts",
            concat!(
                "declare module '@scope/a' {\n",
                "    export type Result = { value: string };\n",
                "    export function create(value: string): Result;\n",
                "}\n",
            ),
        )
        .unwrap();
        fs.write_file(
            "/repo/packages/b/src/index.ts",
            concat!(
                "import { create } from '@scope/a';\n",
                "export function read(value: string) { return create(value); }\n",
            ),
        )
        .unwrap();
        let program = Program::new_with_options(
            &fs,
            "/repo/packages/b",
            &["src/index.ts".to_owned()],
            CompilerOptions {
                declaration: true,
                emit_declaration_only: true,
                base_url: Some("/repo/packages/b".into()),
                paths: BTreeMap::from([("@scope/a".into(), vec!["../a".into()])]),
                no_lib: true,
                ..CompilerOptions::default()
            },
        );
        assert!(
            program.diagnostics().is_empty(),
            "{:?}",
            program.diagnostics()
        );
        let emitted = program.emit();
        let declaration = emitted
            .files
            .iter()
            .find(|file| file.file_name.ends_with("index.d.ts"))
            .unwrap();
        assert_eq!(
            declaration.text,
            "export declare function read(value: string): import(\"@scope/a\").Result;\n"
        );
    }

    #[test]
    fn path_mapped_factory_default_export_preserves_imported_type() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/repo/packages/core/src/SvgIcon.d.ts",
            concat!(
                "export interface SomeInterface { myProp: string; }\n",
                "declare const SvgIcon: SomeInterface;\n",
                "export default SvgIcon;\n",
            ),
        )
        .unwrap();
        fs.write_file(
            "/repo/packages/core/src/utils.d.ts",
            concat!(
                "import SvgIcon from './SvgIcon';\n",
                "export function createSvgIcon(path: string, name: string): typeof SvgIcon;\n",
            ),
        )
        .unwrap();
        fs.write_file(
            "/repo/packages/lab/src/index.ts",
            concat!(
                "import { createSvgIcon } from '@scope/core/utils';\n",
                "export default createSvgIcon('Hello', 'ArrowLeft');\n",
            ),
        )
        .unwrap();
        let program = Program::new_with_options(
            &fs,
            "/repo/packages/lab",
            &["src/index.ts".to_owned()],
            CompilerOptions {
                declaration: true,
                emit_declaration_only: true,
                base_url: Some("/repo/packages".into()),
                paths: BTreeMap::from([("@scope/core/*".into(), vec!["./core/src/*".into()])]),
                no_lib: true,
                ..CompilerOptions::default()
            },
        );
        assert!(
            program.diagnostics().is_empty(),
            "{:?}",
            program.diagnostics()
        );
        let emitted = program.emit();
        let declaration = emitted
            .files
            .iter()
            .find(|file| file.file_name.ends_with("index.d.ts"))
            .unwrap();
        assert_eq!(
            declaration.text,
            concat!(
                "declare const _default: import(\"@scope/core/SvgIcon\").SomeInterface;\n",
                "export default _default;\n",
            )
        );
    }

    #[test]
    fn anonymous_mixin_heritage_preserves_constructor_object_shape() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/wrappers.ts",
            concat!(
                "export type Constructor<T = {}> = new (...args: any[]) => T;\n",
                "export function Timestamped<TBase extends Constructor>(Base: TBase) {\n",
                "    return class extends Base { timestamp: number = 1; };\n",
                "}\n",
            ),
        )
        .unwrap();
        fs.write_file(
            "/project/index.ts",
            concat!(
                "import { Timestamped } from './wrappers';\n",
                "export class User { name = ''; }\n",
                "export class TimestampedUser extends Timestamped(User) {}\n",
            ),
        )
        .unwrap();
        let program = Program::new_with_options(
            &fs,
            "/project",
            &["index.ts".to_owned()],
            CompilerOptions {
                declaration: true,
                emit_declaration_only: true,
                module: ModuleKind::CommonJs,
                target: ScriptTarget::Es2015,
                no_lib: true,
                ..CompilerOptions::default()
            },
        );
        assert!(
            program.diagnostics().is_empty(),
            "{:?}",
            program.diagnostics()
        );
        let emitted = program.emit();
        let declaration = emitted
            .files
            .iter()
            .find(|file| file.file_name == "/project/index.d.ts")
            .unwrap();
        assert!(
            declaration.text.contains(concat!(
                "declare const TimestampedUser_base: {\n",
                "    new (...args: any[]): {\n",
                "        timestamp: number;\n",
                "    };\n",
                "} & typeof User;",
            )),
            "{}",
            declaration.text
        );
    }

    #[test]
    fn bundled_export_only_imports_follow_the_export_alias() {
        assert_eq!(
            defer_export_only_bundle_imports(concat!(
                "import versions from \"versions.static\";\n",
                "export { versions };\n",
            )),
            concat!(
                "export { versions };\n",
                "import versions from \"versions.static\";\n",
            )
        );
        assert_eq!(
            defer_export_only_bundle_imports(concat!(
                "import { B } from \"shared\";\n",
                "export function make(): B;\n",
            )),
            concat!(
                "import { B } from \"shared\";\n",
                "export function make(): B;\n",
            )
        );
    }

    #[test]
    fn config_options_control_emit_and_resolution() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/tsconfig.json",
            "{ \"files\": [\"main.ts\"], \"compilerOptions\": { \"noEmit\": true, \"module\": \"esnext\", \"noLib\": true } }",
        )
        .unwrap();
        fs.write_file("/project/main.ts", "const value = 1;")
            .unwrap();
        let program = Program::from_config(&fs, "/project/tsconfig.json");
        assert!(program.diagnostics().is_empty());
        assert!(program.options().no_emit);
        assert!(program.emit().files.is_empty());
    }

    #[test]
    fn config_without_module_preserves_ecmascript_exports() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/tsconfig.json",
            r#"{"files":["main.ts"],"compilerOptions":{"target":"es2015","noLib":true}}"#,
        )
        .unwrap();
        fs.write_file("/project/main.ts", "export class Model {}")
            .unwrap();

        let program = Program::from_config(&fs, "/project/tsconfig.json");
        assert_eq!(program.options().module, ModuleKind::None);
        let javascript = &program.emit().files[0].text;
        assert!(javascript.contains("export class Model"), "{javascript}");
        assert!(!javascript.contains("exports.Model"), "{javascript}");
    }

    #[test]
    fn config_options_control_target_module_and_source_maps() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/tsconfig.json",
            "{ \"files\": [\"main.ts\"], \"compilerOptions\": { \"target\": \"es2015\", \"module\": \"commonjs\", \"sourceMap\": true, \"noLib\": true } }",
        )
        .unwrap();
        fs.write_file(
            "/project/main.ts",
            "const value = (input: number) => input; export { value };",
        )
        .unwrap();
        let program = Program::from_config(&fs, "/project/tsconfig.json");
        assert!(
            program.diagnostics().is_empty(),
            "{:?}",
            program.diagnostics()
        );
        let emitted = program.emit();
        assert!(emitted.diagnostics.is_empty());
        assert_eq!(emitted.files.len(), 2);
        let map = emitted
            .files
            .iter()
            .find(|file| file.file_name.rsplit('/').next() == Some("main.js.map"))
            .unwrap();
        assert!(
            map.text
                .starts_with("{\"version\":3,\"file\":\"main.js\",\"sourceRoot\":\"\"")
        );
        let javascript = emitted
            .files
            .iter()
            .find(|file| file.file_name.rsplit('/').next() == Some("main.js"))
            .unwrap();
        assert!(javascript.text.contains("exports.value"));
        assert!(javascript.text.contains("sourceMappingURL=main.js.map"));
    }

    #[test]
    fn out_dir_and_root_dir_preserve_source_structure() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/tsconfig.json",
            r#"{
                "files": ["src/main.ts", "src/nested/other.ts"],
                "compilerOptions": {
                    "outDir": "build",
                    "rootDir": "src",
                    "sourceMap": true,
                    "noLib": true
                }
            }"#,
        )
        .unwrap();
        fs.write_file("/project/src/main.ts", "const main = 1;")
            .unwrap();
        fs.write_file("/project/src/nested/other.ts", "const other = 2;")
            .unwrap();
        let program = Program::from_config(&fs, "/project/tsconfig.json");
        let emitted = program.emit();
        let paths = emitted
            .files
            .iter()
            .map(|file| file.file_name.as_str())
            .collect::<Vec<_>>();
        assert!(paths.contains(&"/project/build/main.js"));
        assert!(paths.contains(&"/project/build/main.js.map"));
        assert!(paths.contains(&"/project/build/nested/other.js"));
        assert!(paths.contains(&"/project/build/nested/other.js.map"));
    }

    #[test]
    fn inline_source_maps_are_embedded_without_map_files() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/tsconfig.json",
            r#"{
                "files": ["src/main.ts"],
                "compilerOptions": { "outDir": "build", "inlineSourceMap": true, "noLib": true }
            }"#,
        )
        .unwrap();
        fs.write_file("/project/src/main.ts", "const main = 1;")
            .unwrap();
        let program = Program::from_config(&fs, "/project/tsconfig.json");
        let emitted = program.emit();
        assert_eq!(emitted.files.len(), 1);
        assert_eq!(emitted.files[0].file_name, "/project/build/main.js");
        assert!(
            emitted.files[0]
                .text
                .contains("sourceMappingURL=data:application/json;base64,")
        );
    }

    #[test]
    fn emits_declarations_and_declaration_maps_to_declaration_dir() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/tsconfig.json",
            r#"{
                "files": ["src/api.mts"],
                "compilerOptions": {
                    "outDir": "dist",
                    "rootDir": "src",
                    "declaration": true,
                    "declarationMap": true,
                    "declarationDir": "types",
                    "noLib": true
                }
            }"#,
        )
        .unwrap();
        fs.write_file(
            "/project/src/api.mts",
            r"
                export const version: number = 1;
                export function identity<T>(value: T): T { return value; }
                export interface Box<T> { value: T; }
                export type Maybe<T> = T | undefined;
                export enum Color { Red, Blue = 2 }
            ",
        )
        .unwrap();
        let program = Program::from_config(&fs, "/project/tsconfig.json");
        assert!(
            program.diagnostics().is_empty(),
            "{:?}",
            program.diagnostics()
        );
        let emitted = program.emit();
        assert!(emitted.diagnostics.is_empty(), "{:?}", emitted.diagnostics);
        let declaration = emitted
            .files
            .iter()
            .find(|file| file.file_name == "/project/types/api.d.mts")
            .unwrap();
        assert_eq!(
            declaration.text,
            "export declare const version: number;\nexport declare function identity<T>(value: T): T;\nexport interface Box<T> {\n    value: T;\n}\nexport type Maybe<T> = T | undefined;\nexport declare enum Color {\n    Red = 0,\n    Blue = 2\n}\n//# sourceMappingURL=api.d.mts.map\n"
        );
        assert!(
            emitted
                .files
                .iter()
                .any(|file| file.file_name == "/project/types/api.d.mts.map")
        );
        assert!(
            emitted
                .files
                .iter()
                .any(|file| file.file_name == "/project/dist/api.mjs")
        );
    }

    #[test]
    fn declaration_emit_consumes_reachable_private_declarations() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/main.ts",
            "type T = { x: number }; export interface I { f: T; }",
        )
        .unwrap();
        let program = Program::new_with_options(
            &fs,
            "/project",
            &["main.ts".to_owned()],
            CompilerOptions {
                declaration: true,
                module: ModuleKind::CommonJs,
                target: ScriptTarget::Es2015,
                no_emit_on_error: true,
                no_lib: true,
                ..CompilerOptions::default()
            },
        );
        let emitted = program.emit();
        assert!(emitted.diagnostics.is_empty(), "{:?}", emitted.diagnostics);
        let declaration = emitted
            .files
            .iter()
            .find(|file| file.file_name == "/project/main.d.ts")
            .unwrap();
        assert_eq!(
            declaration.text,
            concat!(
                "type T = {\n",
                "    x: number;\n",
                "};\n",
                "export interface I {\n",
                "    f: T;\n",
                "}\n",
                "export {};\n",
            )
        );

        for (source, expected) in [
            (
                "namespace M { namespace N {} export import X = N; }",
                concat!(
                    "declare namespace M {\n",
                    "    namespace N {\n",
                    "    }\n",
                    "    export import X = N;\n",
                    "    export {};\n",
                    "}\n",
                ),
            ),
            (
                "namespace M { namespace N { class C {} } import R = N; export import X = R; }",
                concat!(
                    "declare namespace M {\n",
                    "    namespace N {\n",
                    "    }\n",
                    "    import R = N;\n",
                    "    export import X = R;\n",
                    "    export {};\n",
                    "}\n",
                ),
            ),
            (
                "namespace M { class C {} export var value: C = new C(); }",
                concat!(
                    "declare namespace M {\n",
                    "    class C {\n",
                    "    }\n",
                    "    var value: C;\n",
                    "}\n",
                ),
            ),
        ] {
            let fs = MemoryFileSystem::new(true);
            fs.write_file("/project/alias.ts", source).unwrap();
            let program = Program::new_with_options(
                &fs,
                "/project",
                &["alias.ts".to_owned()],
                CompilerOptions {
                    declaration: true,
                    module: ModuleKind::None,
                    target: ScriptTarget::Es2015,
                    no_lib: true,
                    ..CompilerOptions::default()
                },
            );
            let emitted = program.emit();
            assert!(emitted.diagnostics.is_empty(), "{:?}", emitted.diagnostics);
            let declaration = emitted
                .files
                .iter()
                .find(|file| file.file_name == "/project/alias.d.ts")
                .unwrap();
            assert_eq!(declaration.text, expected);
        }
    }

    #[test]
    fn declaration_emit_spreads_imported_type_only_alias_shape() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/type.ts",
            "export type Type = { x?: { [Enum.A]: 0 } };",
        )
        .unwrap();
        fs.write_file(
            "/project/index.ts",
            "import { type Type } from './type'; export const foo = { ...({} as Type) };",
        )
        .unwrap();
        let program = Program::new_with_options(
            &fs,
            "/project",
            &["type.ts".to_owned(), "index.ts".to_owned()],
            CompilerOptions {
                declaration: true,
                emit_declaration_only: true,
                target: ScriptTarget::Es2015,
                no_lib: true,
                ..CompilerOptions::default()
            },
        );
        let index = program
            .source_files
            .iter()
            .find(|source| source.file_name == "/project/index.ts")
            .unwrap();
        let symbol = index
            .binding
            .root_scope()
            .unwrap()
            .symbols
            .get("foo")
            .unwrap();
        let type_id = index.checking.type_of_symbol(symbol).unwrap();
        assert_eq!(
            index
                .checking
                .type_of_node(index.binding.symbols.get(symbol).unwrap().declarations[0]),
            Some(type_id)
        );
        assert!(
            matches!(
                index.checking.types.get(type_id).map(|type_| &type_.kind),
                Some(ts_checker::TypeKind::Object(object)) if object.properties.contains_key("x")
            ),
            "{}",
            index.checking.types.display(type_id)
        );
        let emitted = program.emit();
        let declaration = emitted
            .files
            .iter()
            .find(|file| file.file_name == "/project/index.d.ts")
            .unwrap();
        assert!(declaration.text.contains("x?:"), "{}", declaration.text);
    }

    #[test]
    fn declaration_emit_preserves_cross_module_default_type_identity() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/color.ts",
            "interface Color { c: string; } export default Color;",
        )
        .unwrap();
        fs.write_file(
            "/project/file1.ts",
            "import Color from './color'; export declare function styled(): Color;",
        )
        .unwrap();
        fs.write_file(
            "/project/file2.ts",
            "import { styled } from './file1'; export const A = styled();",
        )
        .unwrap();
        let program = Program::new_with_options(
            &fs,
            "/project",
            &["color.ts".into(), "file1.ts".into(), "file2.ts".into()],
            CompilerOptions {
                declaration: true,
                module: ModuleKind::CommonJs,
                target: ScriptTarget::Es2015,
                no_lib: true,
                ..CompilerOptions::default()
            },
        );
        let emitted = program.emit();
        assert!(emitted.diagnostics.is_empty(), "{:?}", emitted.diagnostics);
        let declaration = emitted
            .files
            .iter()
            .find(|file| file.file_name == "/project/file2.d.ts")
            .unwrap();
        assert_eq!(
            declaration.text,
            "export declare const A: import(\"./color\").default;\n"
        );
    }

    #[test]
    fn namespace_alias_runtime_emit_tracks_instantiation_and_source_order() {
        for (source, expected) in [
            (
                "namespace M { namespace N {} export import X = N; }",
                "\"use strict\";\nvar M;\n(function (M) {\n})(M || (M = {}));\n",
            ),
            (
                "namespace M { namespace N { class C {} } import R = N; export import X = R; }",
                concat!(
                    "\"use strict\";\n",
                    "var M;\n",
                    "(function (M) {\n",
                    "    let N;\n",
                    "    (function (N) {\n",
                    "        class C {\n",
                    "        }\n",
                    "    })(N || (N = {}));\n",
                    "    var R = N;\n",
                    "    M.X = R;\n",
                    "})(M || (M = {}));\n",
                ),
            ),
        ] {
            let fs = MemoryFileSystem::new(true);
            fs.write_file("/project/alias.ts", source).unwrap();
            let program = Program::new_with_options(
                &fs,
                "/project",
                &["alias.ts".to_owned()],
                CompilerOptions {
                    module: ModuleKind::None,
                    target: ScriptTarget::Es2015,
                    no_lib: true,
                    ..CompilerOptions::default()
                },
            );
            let emitted = program.emit();
            assert!(emitted.diagnostics.is_empty(), "{:?}", emitted.diagnostics);
            let javascript = emitted
                .files
                .iter()
                .find(|file| file.file_name == "/project/alias.js")
                .unwrap();
            assert_eq!(javascript.text, expected);
        }
    }

    #[test]
    fn declaration_emit_uses_evaluated_const_enum_values() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/enum.ts",
            concat!(
                "const enum E {\n",
                "    a = 10, b = a, c = (a + 1), e, d = ~e,\n",
                "    f = a << 2 >> 1, g = a << 2 >>> 1, h = a | b\n",
                "}\n",
            ),
        )
        .unwrap();
        let program = Program::new_with_options(
            &fs,
            "/project",
            &["enum.ts".to_owned()],
            CompilerOptions {
                declaration: true,
                target: ScriptTarget::Es2015,
                no_lib: true,
                ..CompilerOptions::default()
            },
        );
        let emitted = program.emit();
        let javascript = emitted
            .files
            .iter()
            .find(|file| file.file_name == "/project/enum.js")
            .unwrap();
        assert_eq!(javascript.text, "\"use strict\";\n");
        let declaration = emitted
            .files
            .iter()
            .find(|file| file.file_name == "/project/enum.d.ts")
            .unwrap();
        assert_eq!(
            declaration.text,
            concat!(
                "declare const enum E {\n",
                "    a = 10,\n",
                "    b = 10,\n",
                "    c = 11,\n",
                "    e = 12,\n",
                "    d = -13,\n",
                "    f = 20,\n",
                "    g = 20,\n",
                "    h = 10\n",
                "}\n",
            )
        );
    }

    #[test]
    fn emit_declaration_only_suppresses_javascript() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/tsconfig.json",
            r#"{
                "files": ["src/index.ts"],
                "compilerOptions": { "outDir": "types", "declaration": true, "emitDeclarationOnly": true, "noLib": true }
            }"#,
        )
        .unwrap();
        fs.write_file(
            "/project/src/index.ts",
            "export const value: string = 'ok';",
        )
        .unwrap();
        let program = Program::from_config(&fs, "/project/tsconfig.json");
        let emitted = program.emit();
        assert_eq!(emitted.files.len(), 1);
        assert_eq!(emitted.files[0].file_name, "/project/types/index.d.ts");
        assert_eq!(
            emitted.files[0].text,
            "export declare const value: string;\n"
        );
    }

    #[test]
    fn emit_declaration_only_requires_declaration_or_composite() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file("/project/index.ts", "var hello = 'yo!';")
            .unwrap();
        let program = Program::new_with_options(
            &fs,
            "/project",
            &["index.ts".to_owned()],
            CompilerOptions {
                emit_declaration_only: true,
                no_lib: true,
                ..CompilerOptions::default()
            },
        );
        assert_eq!(
            program
                .diagnostics()
                .iter()
                .filter_map(|diagnostic| diagnostic.code)
                .collect::<Vec<_>>(),
            [5069]
        );
        assert!(program.emit().files.is_empty());
    }

    #[test]
    fn config_loads_target_default_libraries_without_emitting_them() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/tsconfig.json",
            r#"{
                "files": ["main.ts"],
                "compilerOptions": { "target": "es2015" }
            }"#,
        )
        .unwrap();
        fs.write_file("/project/main.ts", "Array; Promise;")
            .unwrap();
        let program = Program::from_config(&fs, "/project/tsconfig.json");
        assert!(
            !program
                .diagnostics()
                .iter()
                .any(|diagnostic| diagnostic.code == Some(2304))
        );
        assert!(
            program.source_files().iter().any(|file| {
                file.is_default_library && file.file_name.ends_with("/lib.es6.d.ts")
            })
        );
        let emitted = program.emit();
        assert!(
            emitted
                .files
                .iter()
                .all(|file| !file.file_name.contains("/__typescript/lib/"))
        );
    }

    #[test]
    fn no_lib_removes_default_library_globals() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/tsconfig.json",
            r#"{
                "files": ["main.ts"],
                "compilerOptions": { "noLib": true }
            }"#,
        )
        .unwrap();
        fs.write_file("/project/main.ts", "Array; Promise;")
            .unwrap();
        let program = Program::from_config(&fs, "/project/tsconfig.json");
        assert_eq!(
            program
                .diagnostics()
                .iter()
                .filter(|diagnostic| diagnostic.code == Some(2304))
                .count(),
            2
        );
        assert!(
            !program
                .source_files()
                .iter()
                .any(|file| file.is_default_library)
        );
    }

    #[test]
    fn explicit_lib_overrides_target_default_selection() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/tsconfig.json",
            r#"{
                "files": ["main.ts"],
                "compilerOptions": {
                    "target": "es5",
                    "lib": ["es5", "es2015.promise"]
                }
            }"#,
        )
        .unwrap();
        fs.write_file("/project/main.ts", "Array; Promise;")
            .unwrap();
        let program = Program::from_config(&fs, "/project/tsconfig.json");
        assert!(
            !program
                .diagnostics()
                .iter()
                .any(|diagnostic| diagnostic.code == Some(2304))
        );
        assert!(program.source_files().iter().any(|file| {
            file.is_default_library && file.file_name.ends_with("/lib.es2015.promise.d.ts")
        }));
        assert!(
            !program.source_files().iter().any(|file| {
                file.is_default_library && file.file_name.ends_with("/lib.dom.d.ts")
            })
        );
    }

    #[test]
    fn target_selects_distinct_default_library_roots() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file("/project/main.ts", "Array;").unwrap();
        let es5 = Program::new_with_options(
            &fs,
            "/project",
            &["main.ts".to_owned()],
            CompilerOptions {
                target: ts_options::ScriptTarget::Es5,
                ..CompilerOptions::default()
            },
        );
        let es2015 = Program::new_with_options(
            &fs,
            "/project",
            &["main.ts".to_owned()],
            CompilerOptions {
                target: ts_options::ScriptTarget::Es2015,
                ..CompilerOptions::default()
            },
        );
        assert!(
            es5.source_files()
                .iter()
                .any(|file| { file.is_default_library && file.file_name.ends_with("/lib.d.ts") })
        );
        assert!(
            es2015.source_files().iter().any(|file| {
                file.is_default_library && file.file_name.ends_with("/lib.es6.d.ts")
            })
        );
    }

    #[test]
    fn checks_core_default_library_array_and_promise_generics() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/tsconfig.json",
            r#"{
                "files": ["main.ts"],
                "compilerOptions": { "target": "es2015", "lib": ["es5"] }
            }"#,
        )
        .unwrap();
        fs.write_file(
            "/project/main.ts",
            r#"
                const values: Array<number> = [1, 2];
                const wrongElement: string = values[0];
                values.push("wrong");
                const wrongMap: Array<string> = values.map(value => value + 1);

                let promise: PromiseLike<number>;
                promise.then((value: string) => value);
            "#,
        )
        .unwrap();
        let program = Program::from_config(&fs, "/project/tsconfig.json");
        assert_eq!(
            program
                .diagnostics()
                .iter()
                .filter_map(|diagnostic| diagnostic.code)
                .collect::<Vec<_>>(),
            [2322, 2345, 2322, 2345]
        );
    }

    #[test]
    fn checks_core_default_library_within_debug_budget() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/tsconfig.json",
            r#"{
                "files": ["main.ts"],
                "compilerOptions": { "target": "es5", "lib": ["es5"] }
            }"#,
        )
        .unwrap();
        fs.write_file(
            "/project/main.ts",
            "const values: Array<number> = [1, 2, 3]; values.map(value => value + 1);",
        )
        .unwrap();
        let started = Instant::now();
        let program = Program::from_config(&fs, "/project/tsconfig.json");
        let elapsed = started.elapsed();
        assert!(
            program.diagnostics().is_empty(),
            "{:?}",
            program.diagnostics()
        );
        assert!(
            elapsed < Duration::from_secs(2),
            "cold debug default-library check took {elapsed:?}"
        );
    }

    #[test]
    fn enforces_strict_null_checks() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/tsconfig.json",
            r#"{
                "files": ["main.ts"],
                "compilerOptions": { "noLib": true, "strictNullChecks": true }
            }"#,
        )
        .unwrap();
        fs.write_file(
            "/project/main.ts",
            "const text: string = null; const count: number = null;",
        )
        .unwrap();
        let strict = Program::from_config(&fs, "/project/tsconfig.json");
        assert_eq!(
            strict
                .diagnostics()
                .iter()
                .filter_map(|diagnostic| diagnostic.code)
                .collect::<Vec<_>>(),
            [2322, 2322]
        );

        fs.write_file(
            "/project/tsconfig.json",
            r#"{
                "files": ["main.ts"],
                "compilerOptions": { "noLib": true, "strictNullChecks": false }
            }"#,
        )
        .unwrap();
        let loose = Program::from_config(&fs, "/project/tsconfig.json");
        assert!(loose.diagnostics().is_empty(), "{:?}", loose.diagnostics());
    }

    #[test]
    fn enforces_exact_optional_property_types_from_config() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/tsconfig.json",
            r#"{
                "files": ["main.ts"],
                "compilerOptions": {
                    "noLib": true,
                    "strictNullChecks": true,
                    "exactOptionalPropertyTypes": true
                }
            }"#,
        )
        .unwrap();
        fs.write_file(
            "/project/main.ts",
            "declare function take(value: { text?: string }): void; take({ text: undefined });",
        )
        .unwrap();
        let program = Program::from_config(&fs, "/project/tsconfig.json");
        assert_eq!(
            program
                .diagnostics()
                .iter()
                .filter_map(|diagnostic| diagnostic.code)
                .collect::<Vec<_>>(),
            [2379]
        );

        fs.write_file(
            "/project/tsconfig.json",
            r#"{
                "files": ["main.ts"],
                "compilerOptions": { "noLib": true, "exactOptionalPropertyTypes": true }
            }"#,
        )
        .unwrap();
        let invalid = Program::from_config(&fs, "/project/tsconfig.json");
        assert_eq!(
            invalid
                .diagnostics()
                .iter()
                .filter_map(|diagnostic| diagnostic.code)
                .collect::<Vec<_>>(),
            [5052]
        );
    }

    #[test]
    fn checks_delete_operands_with_exact_optional_property_types() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/main.ts",
            r"
                interface Model {
                    required: number;
                    includesUndefined: number | undefined;
                    optional?: number;
                }
                declare const model: Model;
                delete model.required;
                delete model.includesUndefined;
                delete model.optional;
            ",
        )
        .unwrap();
        fs.write_file(
            "/project/tsconfig.json",
            r#"{
                "files": ["main.ts"],
                "compilerOptions": {
                    "noLib": true,
                    "strictNullChecks": true,
                    "exactOptionalPropertyTypes": true
                }
            }"#,
        )
        .unwrap();
        let exact = Program::from_config(&fs, "/project/tsconfig.json");
        assert_eq!(
            exact
                .diagnostics()
                .iter()
                .filter_map(|diagnostic| diagnostic.code)
                .collect::<Vec<_>>(),
            [2790, 2790]
        );

        fs.write_file(
            "/project/tsconfig.json",
            r#"{
                "files": ["main.ts"],
                "compilerOptions": {
                    "noLib": true,
                    "strictNullChecks": true,
                    "exactOptionalPropertyTypes": false
                }
            }"#,
        )
        .unwrap();
        let legacy = Program::from_config(&fs, "/project/tsconfig.json");
        assert_eq!(
            legacy
                .diagnostics()
                .iter()
                .filter_map(|diagnostic| diagnostic.code)
                .collect::<Vec<_>>(),
            [2790]
        );
    }

    #[test]
    fn reports_contextual_exact_optional_diagnostic_codes() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/main.ts",
            r"
                interface Options { text?: string; }
                declare let options: Options;
                options.text = undefined;
                const initialized: Options = { text: undefined };
                declare function take(value: Options): void;
                take({ text: undefined });
            ",
        )
        .unwrap();
        fs.write_file(
            "/project/tsconfig.json",
            r#"{
                "files": ["main.ts"],
                "compilerOptions": {
                    "noLib": true,
                    "strictNullChecks": true,
                    "exactOptionalPropertyTypes": true
                }
            }"#,
        )
        .unwrap();
        let exact = Program::from_config(&fs, "/project/tsconfig.json");
        assert_eq!(
            exact
                .diagnostics()
                .iter()
                .filter_map(|diagnostic| diagnostic.code)
                .collect::<Vec<_>>(),
            [2412, 2375, 2379]
        );

        fs.write_file(
            "/project/tsconfig.json",
            r#"{
                "files": ["main.ts"],
                "compilerOptions": {
                    "noLib": true,
                    "strictNullChecks": true,
                    "exactOptionalPropertyTypes": false
                }
            }"#,
        )
        .unwrap();
        let legacy = Program::from_config(&fs, "/project/tsconfig.json");
        assert!(
            legacy.diagnostics().is_empty(),
            "{:?}",
            legacy.diagnostics()
        );
    }

    #[test]
    fn reports_implicit_any_and_unused_bindings() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/tsconfig.json",
            r#"{
                "files": ["main.ts"],
                "compilerOptions": {
                    "noLib": true,
                    "noImplicitAny": true,
                    "noUnusedLocals": true,
                    "noUnusedParameters": true
                }
            }"#,
        )
        .unwrap();
        fs.write_file(
            "/project/main.ts",
            r"
                function work(used, unused, _ignored) {
                    const local = 1;
                    const read = 2;
                    return used + read;
                }
            ",
        )
        .unwrap();
        let program = Program::from_config(&fs, "/project/tsconfig.json");
        assert_eq!(
            program
                .diagnostics()
                .iter()
                .filter_map(|diagnostic| diagnostic.code)
                .collect::<Vec<_>>(),
            [7006, 7006, 7006, 6133, 6133]
        );
    }

    #[test]
    fn skip_lib_check_suppresses_declaration_file_semantics() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file("/project/main.ts", "const value: Broken = { text: 'ok' };")
            .unwrap();
        fs.write_file(
            "/project/broken.d.ts",
            "interface Broken { text: string; } declare const invalid: string = 1;",
        )
        .unwrap();
        fs.write_file(
            "/project/tsconfig.json",
            r#"{
                "files": ["main.ts", "broken.d.ts"],
                "compilerOptions": { "noLib": true, "skipLibCheck": false }
            }"#,
        )
        .unwrap();
        let checked = Program::from_config(&fs, "/project/tsconfig.json");
        assert_eq!(
            checked
                .diagnostics()
                .iter()
                .filter_map(|diagnostic| diagnostic.code)
                .collect::<Vec<_>>(),
            [2322]
        );

        fs.write_file(
            "/project/tsconfig.json",
            r#"{
                "files": ["main.ts", "broken.d.ts"],
                "compilerOptions": { "noLib": true, "skipLibCheck": true }
            }"#,
        )
        .unwrap();
        let skipped = Program::from_config(&fs, "/project/tsconfig.json");
        assert!(
            skipped.diagnostics().is_empty(),
            "{:?}",
            skipped.diagnostics()
        );
    }

    #[test]
    fn reports_accidental_get_accessor_calls_across_files() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/model.ts",
            "export class Model { get value(): number { return 1; } set label(value: string) {} }",
        )
        .unwrap();
        fs.write_file(
            "/project/main.ts",
            r"
                import { Model } from './model';
                declare const model: Model;
                const value: number = model.value;
                const label: string = model.label;
                model.value();
            ",
        )
        .unwrap();
        fs.write_file(
            "/project/tsconfig.json",
            r#"{
                "files": ["main.ts"],
                "compilerOptions": { "noLib": true, "noEmit": true }
            }"#,
        )
        .unwrap();
        let program = Program::from_config(&fs, "/project/tsconfig.json");
        assert_eq!(
            program
                .diagnostics()
                .iter()
                .filter_map(|diagnostic| diagnostic.code)
                .collect::<Vec<_>>(),
            [6234]
        );
    }

    #[test]
    fn checks_structural_shapes_and_generic_argument_inference() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/tsconfig.json",
            r#"{
                "files": ["main.ts"],
                "compilerOptions": { "noLib": true, "strict": true }
            }"#,
        )
        .unwrap();
        fs.write_file(
            "/project/main.ts",
            r#"
                interface Base { readonly id: number; note?: string; }
                interface Entry extends Base { value: string; }
                const good: Entry = { id: 1, value: "ok" };
                const missing: Entry = { id: 1 };
                const excess: Entry = { id: 1, value: "ok", other: true };
                good.id = 2;
                function unwrap<T>(box: { value: T }): T { return box.value; }
                const inferred: number = unwrap({ value: 1 });
                const wrong: string = unwrap({ value: 1 });
            "#,
        )
        .unwrap();
        let program = Program::from_config(&fs, "/project/tsconfig.json");
        assert_eq!(
            program
                .diagnostics()
                .iter()
                .filter_map(|diagnostic| diagnostic.code)
                .collect::<Vec<_>>(),
            [2322, 2353, 2540, 2322]
        );
    }

    #[test]
    fn declaration_emit_uses_inferred_readonly_object_types() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/main.ts",
            "export var basePrototype = { get primaryPath() { return this.collection; } };",
        )
        .unwrap();
        let program = Program::new_with_options(
            &fs,
            "/project",
            &["main.ts".to_owned()],
            CompilerOptions {
                declaration: true,
                no_lib: true,
                module: ModuleKind::CommonJs,
                target: ScriptTarget::Es2015,
                ..CompilerOptions::default()
            },
        );
        let emitted = program.emit();
        let declaration = emitted
            .files
            .iter()
            .find(|file| file.file_name == "/project/main.d.ts")
            .unwrap();
        assert_eq!(
            declaration.text,
            "export declare var basePrototype: {\n    readonly primaryPath: any;\n};\n"
        );
    }

    #[test]
    fn declaration_emit_serializes_ambient_const_literals() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/main.ts",
            concat!(
                "function f<T>(x: T): T { return x; }\n",
                "enum E { A, B, C, \"non identifier\" }\n",
                "const c1 = \"abc\";\n",
                "const c2 = 123;\n",
                "const c3 = c1;\n",
                "const c4 = c2;\n",
                "const c5 = f(123);\n",
                "const c6 = f(-123);\n",
                "const c7 = true;\n",
                "const c8 = E.A;\n",
                "const c8b = E[\"non identifier\"];\n",
                "const c9 = { x: \"abc\" };\n",
                "const c10 = [123];\n",
                "const c11 = \"abc\" + \"def\";\n",
                "const c12 = 123 + 456;\n",
                "const c13 = Math.random() > 0.5 ? \"abc\" : \"def\";\n",
                "const c14 = Math.random() > 0.5 ? 123 : 456;\n",
            ),
        )
        .unwrap();
        let program = Program::new_with_options(
            &fs,
            "/project",
            &["main.ts".to_owned()],
            CompilerOptions {
                declaration: true,
                no_lib: true,
                target: ScriptTarget::Es2015,
                ..CompilerOptions::default()
            },
        );
        let emitted = program.emit();
        let declaration = emitted
            .files
            .iter()
            .find(|file| file.file_name == "/project/main.d.ts")
            .unwrap();
        assert_eq!(
            declaration.text,
            concat!(
                "declare function f<T>(x: T): T;\n",
                "declare enum E {\n",
                "    A = 0,\n",
                "    B = 1,\n",
                "    C = 2,\n",
                "    \"non identifier\" = 3\n",
                "}\n",
                "declare const c1 = \"abc\";\n",
                "declare const c2 = 123;\n",
                "declare const c3 = \"abc\";\n",
                "declare const c4 = 123;\n",
                "declare const c5 = 123;\n",
                "declare const c6 = -123;\n",
                "declare const c7 = true;\n",
                "declare const c8 = E.A;\n",
                "declare const c8b = E[\"non identifier\"];\n",
                "declare const c9: {\n",
                "    x: string;\n",
                "};\n",
                "declare const c10: number[];\n",
                "declare const c11: string;\n",
                "declare const c12: number;\n",
                "declare const c13: string;\n",
                "declare const c14: number;\n",
            )
        );
    }

    #[test]
    fn javascript_declaration_emit_synthesizes_accessor_namespaces() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/a.js",
            concat!(
                "export const t1 = { p: 'value', get getter() { return 'value'; } };\n",
                "export const t2 = { v: 'value', set setter(v) {} };\n",
                "export const t3 = { p: 'value', get value() { return 'value'; }, set value(v) {} };\n",
            ),
        )
        .unwrap();
        let program = Program::new_with_options(
            &fs,
            "/project",
            &["a.js".to_owned()],
            CompilerOptions {
                allow_js: true,
                check_js: true,
                declaration: true,
                emit_declaration_only: true,
                no_lib: true,
                target: ScriptTarget::Es2015,
                ..CompilerOptions::default()
            },
        );
        let emitted = program.emit();
        let declaration = emitted
            .files
            .iter()
            .find(|file| file.file_name == "/project/a.d.ts")
            .unwrap();
        assert_eq!(
            declaration.text,
            concat!(
                "export namespace t1 {\n    let p: string;\n    const getter: string;\n}\n",
                "export namespace t2 {\n    let v: string;\n    let setter: any;\n}\n",
                "export namespace t3 {\n    let p_1: string;\n    export { p_1 as p };\n    export let value: string;\n}\n",
            )
        );
    }

    #[test]
    fn javascript_declaration_emit_hoists_functions_before_object_namespaces() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/a.js",
            "const foo = { f1: (params) => { } };\nfunction f2(x) { foo.f1({ x }); }",
        )
        .unwrap();
        let program = Program::new_with_options(
            &fs,
            "/project",
            &["a.js".to_owned()],
            CompilerOptions {
                allow_js: true,
                check_js: true,
                declaration: true,
                emit_declaration_only: true,
                no_lib: true,
                target: ScriptTarget::Es2015,
                ..CompilerOptions::default()
            },
        );
        let declaration = program
            .emit()
            .files
            .into_iter()
            .find(|file| file.file_name == "/project/a.d.ts")
            .unwrap();
        assert_eq!(
            declaration.text,
            "declare function f2(x: any): void;\ndeclare namespace foo {\n    function f1(params: any): void;\n}\n"
        );
    }

    #[test]
    fn javascript_declaration_emit_preserves_inline_jsdoc_casts_and_typedefs() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/a.js",
            concat!(
                "/** @typedef {{ } & { name?: string }} P */\n",
                "const value = /** @type {*} */(null);\n",
                "export let cast = /** @type {P} */(value);\n",
                "export function use(input = /** @type {P} */(value)) {}\n",
                "export class C {\n",
                "  /** @readonly */ field = /** @type {P} */(value);\n",
                "  get current() { return /** @type {P} */(value); }\n",
                "  set current(next) {}\n",
                "}\n",
                "export default /** @type {P} */(value);\n",
            ),
        )
        .unwrap();
        let program = Program::new_with_options(
            &fs,
            "/project",
            &["a.js".to_owned()],
            CompilerOptions {
                allow_js: true,
                check_js: true,
                declaration: true,
                emit_declaration_only: true,
                no_lib: true,
                target: ScriptTarget::Es2015,
                ..CompilerOptions::default()
            },
        );
        let declaration = program
            .emit()
            .files
            .into_iter()
            .find(|file| file.file_name == "/project/a.d.ts")
            .unwrap()
            .text;
        assert!(declaration.starts_with("export function use(input?: P): void;\n"));
        assert!(declaration.contains("export let cast: P;"), "{declaration}");
        assert!(
            declaration.contains("/** @readonly */ readonly field: P;"),
            "{declaration}"
        );
        assert!(
            declaration.contains("set current(next: P);\n    get current(): P;"),
            "{declaration}"
        );
        assert!(
            declaration.contains("declare const _default: P;"),
            "{declaration}"
        );
        assert!(
            declaration.contains("export type P = {} & {"),
            "{declaration}"
        );
    }

    #[test]
    fn javascript_declaration_emit_synthesizes_amd_like_module_exports() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/typing.d.ts",
            "declare function define<T = unknown>(name: string, modules: string[], ready: (...modules: unknown[]) => T): void;",
        )
        .unwrap();
        fs.write_file(
            "/project/deps/BaseClass.d.ts",
            concat!(
                "declare module \"deps/BaseClass\" {\n",
                "    class BaseClass {\n",
                "        static extends<A>(a: A): new () => A & BaseClass;\n",
                "    }\n",
                "    export = BaseClass;\n",
                "}\n",
            ),
        )
        .unwrap();
        fs.write_file(
            "/project/ExtendedClass.js",
            concat!(
                "define(\"lib/ExtendedClass\", [\"deps/BaseClass\"],\n",
                "/** @param {typeof import(\"deps/BaseClass\")} BaseClass */\n",
                "(BaseClass) => {\n",
                "    const ExtendedClass = BaseClass.extends({\n",
                "        f: function() { return \"something\"; }\n",
                "    });\n",
                "    const module = {};\n",
                "    module.exports = ExtendedClass;\n",
                "    return module.exports;\n",
                "});\n",
            ),
        )
        .unwrap();
        let program = Program::new_with_options(
            &fs,
            "/project",
            &[
                "typing.d.ts".to_owned(),
                "deps/BaseClass.d.ts".to_owned(),
                "ExtendedClass.js".to_owned(),
            ],
            CompilerOptions {
                allow_js: true,
                check_js: true,
                declaration: true,
                emit_declaration_only: true,
                no_lib: true,
                target: ScriptTarget::Es2015,
                ..CompilerOptions::default()
            },
        );
        assert!(
            program.diagnostics().is_empty(),
            "{:?}",
            program.diagnostics()
        );
        let declaration = program
            .emit()
            .files
            .into_iter()
            .find(|file| file.file_name == "/project/ExtendedClass.d.ts")
            .unwrap();
        assert_eq!(
            declaration.text,
            concat!(
                "export = ExtendedClass;\n",
                "declare const ExtendedClass: new () => {\n",
                "    f: () => \"something\";\n",
                "} & import(\"deps/BaseClass\");\n",
            )
        );
    }

    #[test]
    fn javascript_declaration_emit_consumes_arguments_and_jsdoc_metadata() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/a.js",
            concat!(
                "function f(x) { arguments; }\n",
                "const bar = { arguments: {} };\n",
                "class A {\n",
                "    /** @param {object} [foo={}] */\n",
                "    constructor(foo = {}) {\n",
                "        /** @type object */\n",
                "        this.arguments = foo;\n",
                "    }\n",
                "    get info() { return { bar: {} }; }\n",
                "}\n",
                "class B {\n",
                "    m() {\n",
                "        /** @type object */\n",
                "        this.foo = arguments;\n",
                "    }\n",
                "}\n",
            ),
        )
        .unwrap();
        let program = Program::new_with_options(
            &fs,
            "/project",
            &["a.js".to_owned()],
            CompilerOptions {
                allow_js: true,
                check_js: true,
                declaration: true,
                emit_declaration_only: true,
                target: ScriptTarget::Es2015,
                ..CompilerOptions::default()
            },
        );
        let declaration = program
            .emit()
            .files
            .into_iter()
            .find(|file| file.file_name == "/project/a.d.ts")
            .unwrap();
        assert_eq!(
            declaration.text,
            concat!(
                "declare function f(x: any, ...args: any[]): void;\n",
                "declare namespace bar {\n    let arguments: {};\n}\n",
                "declare class A {\n",
                "    /** @param {object} [foo={}] */\n",
                "    constructor(foo?: object);\n",
                "    /** @type object */\n",
                "    arguments: object;\n",
                "    get info(): {\n        bar: {};\n    };\n",
                "}\n",
                "declare class B {\n",
                "    m(...args: any[]): void;\n",
                "    /** @type object */\n",
                "    foo: object | undefined;\n",
                "}\n",
            )
        );
    }

    #[test]
    fn cyclic_inferred_alias_diagnostic_suppresses_only_declaration_output() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/main.ts",
            concat!(
                "type Bad<Arr> = Arr extends infer Inner ? Bad<Inner> : Arr;\n",
                "declare function flat<A>(arr: A): Bad<A>[];\n",
                "function foo<T>(arr: T[]) { return flat(arr); }\n",
            ),
        )
        .unwrap();
        let program = Program::new_with_options(
            &fs,
            "/project",
            &["main.ts".to_owned()],
            CompilerOptions {
                declaration: true,
                no_lib: true,
                target: ScriptTarget::Es2015,
                ..CompilerOptions::default()
            },
        );
        assert!(
            program
                .diagnostics()
                .iter()
                .any(|diagnostic| diagnostic.code == Some(5088))
        );
        let emitted = program.emit();
        assert!(
            emitted
                .files
                .iter()
                .any(|file| file.file_name == "/project/main.js")
        );
        assert!(
            !emitted
                .files
                .iter()
                .any(|file| file.file_name == "/project/main.d.ts")
        );
    }

    #[test]
    fn private_name_export_diagnostic_suppresses_declaration_output() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/main.ts",
            "if (false) { export var hidden = 0; } export type Public = typeof hidden; }",
        )
        .unwrap();
        let program = Program::new_with_options(
            &fs,
            "/project",
            &["main.ts".to_owned()],
            CompilerOptions {
                declaration: true,
                no_lib: true,
                target: ScriptTarget::Es2015,
                ..CompilerOptions::default()
            },
        );
        assert!(
            !program
                .emit()
                .files
                .iter()
                .any(|file| file.file_name == "/project/main.d.ts")
        );
    }

    #[test]
    fn block_scoped_private_type_query_reports_exported_variable() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/main.ts",
            "{ var a = \"\"; } export let b: typeof a;",
        )
        .unwrap();
        let program = Program::new_with_options(
            &fs,
            "/project",
            &["main.ts".to_owned()],
            CompilerOptions {
                declaration: true,
                emit_declaration_only: true,
                no_lib: true,
                target: ScriptTarget::Es2015,
                ..CompilerOptions::default()
            },
        );

        assert!(
            program
                .diagnostics()
                .iter()
                .any(|diagnostic| diagnostic.code == Some(4025))
        );
        assert!(
            !program
                .emit()
                .files
                .iter()
                .any(|file| file.file_name == "/project/main.d.ts")
        );
    }

    #[test]
    fn isolated_declaration_annotation_diagnostic_suppresses_declaration_output() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/main.ts",
            "declare const internal: { value: number }; export const value = internal.value;",
        )
        .unwrap();
        let program = Program::new_with_options(
            &fs,
            "/project",
            &["main.ts".to_owned()],
            CompilerOptions {
                declaration: true,
                isolated_declarations: true,
                no_lib: true,
                target: ScriptTarget::Es2015,
                ..CompilerOptions::default()
            },
        );
        assert!(
            !program
                .emit()
                .files
                .iter()
                .any(|file| file.file_name == "/project/main.d.ts")
        );
    }

    #[test]
    fn private_anonymous_mixin_diagnostic_suppresses_declaration_output() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/main.ts",
            concat!(
                "declare function mix<T>(value: T): T;\n",
                "const Mixin = class { protected dispose() {} private assert() {} };\n",
                "export default class extends mix(Mixin) {}\n",
            ),
        )
        .unwrap();
        let program = Program::new_with_options(
            &fs,
            "/project",
            &["main.ts".to_owned()],
            CompilerOptions {
                declaration: true,
                module: ModuleKind::CommonJs,
                no_lib: true,
                target: ScriptTarget::Es2015,
                ..CompilerOptions::default()
            },
        );
        assert!(
            !program
                .emit()
                .files
                .iter()
                .any(|file| file.file_name == "/project/main.d.ts")
        );
    }

    #[test]
    fn nonportable_nested_package_inference_suppresses_declaration_output() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/node_modules/foo/node_modules/nested/index.d.ts",
            "export interface NestedProps {}",
        )
        .unwrap();
        fs.write_file(
            "/project/node_modules/foo/index.d.ts",
            concat!(
                "import { NestedProps } from 'nested';\n",
                "export function foo(): [NestedProps];\n",
            ),
        )
        .unwrap();
        fs.write_file(
            "/project/main.ts",
            "import { foo } from 'foo'; export const value = foo();",
        )
        .unwrap();
        let program = Program::new_with_options(
            &fs,
            "/project",
            &["main.ts".to_owned()],
            CompilerOptions {
                declaration: true,
                no_lib: true,
                module: ModuleKind::CommonJs,
                target: ScriptTarget::Es2015,
                ..CompilerOptions::default()
            },
        );
        let entry = program
            .source_files
            .iter()
            .find(|source| source.file_name == "/project/main.ts")
            .unwrap();
        assert!(
            program
                .diagnostics()
                .iter()
                .any(|diagnostic| diagnostic.code == Some(2883)),
            "refs={:?}, types={:?}",
            entry.checking.import_type_references,
            entry.checking.types
        );
        assert!(
            !program
                .emit()
                .files
                .iter()
                .any(|file| file.file_name == "/project/main.d.ts")
        );
    }

    #[test]
    fn nonportable_package_entry_alias_inference_suppresses_declaration_output() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/node_modules/some-dep/dist/inner.d.ts",
            concat!(
                "export type Other = { other: string };\n",
                "export type SomeType = { arg: Other };",
            ),
        )
        .unwrap();
        fs.write_file(
            "/project/node_modules/some-dep/dist/index.d.ts",
            concat!(
                "export type OtherType = import('./inner').Other;\n",
                "export type SomeType = import('./inner').SomeType;",
            ),
        )
        .unwrap();
        fs.write_file(
            "/project/node_modules/some-dep/package.json",
            r#"{"name":"some-dep","types":"./dist/index.d.ts","exports":{".":"./dist/index.js"}}"#,
        )
        .unwrap();
        fs.write_file(
            "/project/src/index.ts",
            concat!(
                "import { SomeType } from 'some-dep';\n",
                "export const foo = (thing: SomeType) => thing;\n",
                "export const bar = (thing: SomeType) => thing.arg;",
            ),
        )
        .unwrap();
        let program = Program::new_with_options(
            &fs,
            "/project",
            &["src/index.ts".to_owned()],
            CompilerOptions {
                declaration: true,
                no_lib: true,
                module: ModuleKind::NodeNext,
                target: ScriptTarget::Es2015,
                strict: true,
                ..CompilerOptions::default()
            },
        );
        let entry = program
            .source_files
            .iter()
            .find(|source| source.file_name == "/project/src/index.ts")
            .unwrap();

        assert_eq!(
            program
                .diagnostics()
                .iter()
                .filter(|diagnostic| diagnostic.code == Some(2883))
                .count(),
            2,
            "diagnostics={:?}, refs={:?}, named={:?}, types={:?}",
            program.diagnostics(),
            entry.checking.import_type_references,
            entry.checking.named_type_references,
            entry.checking.types,
        );
        assert!(
            !program
                .emit()
                .files
                .iter()
                .any(|file| file.file_name == "/project/src/index.d.ts")
        );
    }

    #[test]
    fn node_next_uses_the_nearest_package_type_for_javascript_emit() {
        for (package_json, common_js) in [
            ("{\"name\":\"pkg\"}", true),
            ("{\"name\":\"pkg\",\"type\":\"module\"}", false),
        ] {
            let fs = MemoryFileSystem::new(true);
            fs.write_file("/project/package.json", package_json)
                .unwrap();
            fs.write_file(
                "/project/index.ts",
                "import { Shape } from './types'; export type Public = Shape;",
            )
            .unwrap();
            fs.write_file("/project/types.ts", "export interface Shape {}")
                .unwrap();
            let program = Program::new_with_options(
                &fs,
                "/project",
                &["index.ts".to_owned()],
                CompilerOptions {
                    module: ModuleKind::NodeNext,
                    no_lib: true,
                    target: ScriptTarget::Es2015,
                    ..CompilerOptions::default()
                },
            );
            let javascript = program
                .emit()
                .files
                .into_iter()
                .find(|file| file.file_name == "/project/index.js")
                .unwrap();
            assert_eq!(javascript.text.contains("__esModule"), common_js);
            assert_eq!(javascript.text.contains("export {};"), !common_js);
        }
    }

    #[test]
    fn inferred_external_return_types_use_import_types_without_runtime_imports() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/node_modules/pkg/package.json",
            "{\"name\":\"pkg\",\"types\":\"index.d.ts\"}",
        )
        .unwrap();
        fs.write_file(
            "/project/node_modules/pkg/index.d.ts",
            "export declare function createPlugin(): PluginConfig; export declare class PluginConfig {}",
        )
        .unwrap();
        fs.write_file(
            "/project/index.ts",
            "import { createPlugin } from 'pkg'; export function plugins() { return [createPlugin()]; }",
        )
        .unwrap();
        let program = Program::new_with_options(
            &fs,
            "/project",
            &["index.ts".to_owned()],
            CompilerOptions {
                declaration: true,
                module: ModuleKind::NodeNext,
                no_lib: true,
                target: ScriptTarget::Es2015,
                ..CompilerOptions::default()
            },
        );
        let source = program.source_file("/project/index.ts").unwrap();
        let declaration = program
            .emit()
            .files
            .into_iter()
            .find(|file| file.file_name == "/project/index.d.ts")
            .unwrap();
        assert_eq!(
            declaration.text,
            "export declare function plugins(): import(\"pkg\").PluginConfig[];\n",
            "reachability={:?}, import refs={:?}",
            source.checking.declaration_reachability,
            source.checking.import_type_references,
        );
    }

    #[test]
    fn declaration_emit_preserves_ambient_auto_accessors() {
        let source = concat!(
            "declare class AmbientClass { accessor prop1: string; static accessor prop2: number; private accessor prop3: boolean; private static accessor prop4: symbol; }\n",
            "declare namespace AmbientNamespace { class C { accessor prop: string; } }\n",
            "declare module \"some-module\" { export class ExportedClass { accessor value: any; } }\n",
            "class RegularClass { accessor shouldError: string; }\n",
        );
        let expected = concat!(
            "declare class AmbientClass {\n    accessor prop1: string;\n    static accessor prop2: number;\n    private accessor prop3;\n    private static accessor prop4;\n}\n",
            "declare namespace AmbientNamespace {\n    class C {\n        accessor prop: string;\n    }\n}\n",
            "declare module \"some-module\" {\n    class ExportedClass {\n        accessor value: any;\n    }\n}\n",
            "declare class RegularClass {\n    accessor shouldError: string;\n}\n",
        );
        for target in [ScriptTarget::Es5, ScriptTarget::Es2015] {
            let fs = MemoryFileSystem::new(true);
            fs.write_file("/project/main.ts", source).unwrap();
            let program = Program::new_with_options(
                &fs,
                "/project",
                &["main.ts".to_owned()],
                CompilerOptions {
                    declaration: true,
                    no_lib: true,
                    module: ModuleKind::None,
                    target,
                    ..CompilerOptions::default()
                },
            );
            let emitted = program.emit();
            let declaration = emitted
                .files
                .iter()
                .find(|file| file.file_name == "/project/main.d.ts")
                .unwrap();
            assert_eq!(declaration.text, expected);
        }
    }

    #[test]
    fn declaration_emit_preserves_cross_file_alias_operator_provenance() {
        let fs = MemoryFileSystem::new(true);
        let body = concat!(
            "type O = { prop: string; prop2: string }; ",
            "type I = { prop: string }; ",
            "export const fn = (v: O['prop'], p: Omit<O, 'prop'>, key: keyof O, p2: Omit<O, keyof I>) => {};",
        );
        fs.write_file("/project/a.ts", body).unwrap();
        fs.write_file(
            "/project/aExp.ts",
            &body
                .replace("type O", "export type O")
                .replace("type I", "export type I"),
        )
        .unwrap();
        fs.write_file(
            "/project/b.ts",
            "import { fn } from './a'; import { fn as fnExp } from './aExp'; export const f = fn; export const fExp = fnExp;",
        )
        .unwrap();
        let program = Program::new_with_options(
            &fs,
            "/project",
            &["b.ts".to_owned()],
            CompilerOptions {
                declaration: true,
                module: ModuleKind::CommonJs,
                strict: true,
                ..CompilerOptions::default()
            },
        );
        let emitted = program.emit();
        assert!(emitted.diagnostics.is_empty(), "{:?}", emitted.diagnostics);
        let declaration = emitted
            .files
            .iter()
            .find(|file| file.file_name == "/project/b.d.ts")
            .unwrap();
        assert!(
            declaration
                .text
                .contains("p: Omit<{\n    prop: string;\n    prop2: string;\n}, \"prop\">")
                && declaration
                    .text
                    .contains("key: keyof {\n    prop: string;\n    prop2: string;\n}")
                && declaration
                    .text
                    .contains("v: import(\"./aExp\").O[\"prop\"]")
                && declaration
                    .text
                    .contains("p2: Omit<import(\"./aExp\").O, keyof import(\"./aExp\").I>"),
            "{}",
            declaration.text
        );
    }

    #[test]
    fn declaration_emit_preserves_cross_file_import_type_wrapper() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/box.d.ts",
            "export declare class Box<T> { value: T; }",
        )
        .unwrap();
        fs.write_file(
            "/project/boxed.d.ts",
            concat!(
                "export declare const boxed: import(\"./box\").Box<{\n",
                "    nested: import(\"./box\").Box<number>;\n",
                "}>;",
            ),
        )
        .unwrap();
        fs.write_file(
            "/project/main.ts",
            "import { boxed } from './boxed'; export const value = boxed;",
        )
        .unwrap();
        let program = Program::new_with_options(
            &fs,
            "/project",
            &["main.ts".to_owned()],
            CompilerOptions {
                declaration: true,
                no_lib: true,
                module: ModuleKind::CommonJs,
                strict: true,
                ..CompilerOptions::default()
            },
        );
        let emitted = program.emit();
        assert!(emitted.diagnostics.is_empty(), "{:?}", emitted.diagnostics);
        let declaration = emitted
            .files
            .iter()
            .find(|file| file.file_name == "/project/main.d.ts")
            .unwrap();
        assert!(
            declaration.text.contains(concat!(
                "export declare const value: import(\"./box\").Box<{\n",
                "    nested: import(\"./box\").Box<number>;\n",
                "}>;",
            )),
            "{}",
            declaration.text
        );
    }

    #[test]
    fn declaration_emit_preserves_nested_optional_alias_parameters_across_files() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/a.ts",
            concat!(
                "export type X = string; ",
                "export const fn = { o: (a?: (X | undefined)[]) => {} };",
            ),
        )
        .unwrap();
        fs.write_file(
            "/project/b.ts",
            "import { fn } from './a'; export const value = { fn };",
        )
        .unwrap();
        let program = Program::new_with_options(
            &fs,
            "/project",
            &["a.ts".to_owned(), "b.ts".to_owned()],
            CompilerOptions {
                declaration: true,
                no_lib: true,
                module: ModuleKind::CommonJs,
                ..CompilerOptions::default()
            },
        );
        let emitted = program.emit();
        assert!(emitted.diagnostics.is_empty(), "{:?}", emitted.diagnostics);
        let a = emitted
            .files
            .iter()
            .find(|file| file.file_name == "/project/a.d.ts")
            .unwrap();
        let b = emitted
            .files
            .iter()
            .find(|file| file.file_name == "/project/b.d.ts")
            .unwrap();
        assert!(
            a.text.contains("o: (a?: (X | undefined)[]) => void;"),
            "{}",
            a.text
        );
        assert!(
            b.text
                .contains("o: (a?: (import(\"./a\").X | undefined)[]) => void;"),
            "{}",
            b.text
        );
    }

    #[test]
    fn resolves_non_relative_imports_from_base_url() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file("/proj/defs/cc.ts", "export const enum CharCode { A, B }")
            .unwrap();
        fs.write_file(
            "/proj/component/file.ts",
            "import { CharCode } from 'defs/cc'; export const value = CharCode.A;",
        )
        .unwrap();
        let program = Program::new_with_options(
            &fs,
            "/proj",
            &["component/file.ts".to_owned()],
            CompilerOptions {
                base_url: Some("/proj".into()),
                no_lib: true,
                ..CompilerOptions::default()
            },
        );
        assert!(
            program
                .diagnostics()
                .iter()
                .all(|diagnostic| diagnostic.code != Some(2307)),
            "{:?}",
            program.diagnostics()
        );
        assert!(program.source_file("/proj/defs/cc.ts").is_some());
    }

    #[test]
    fn invalid_out_file_module_kind_does_not_emit() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file("/project/main.ts", "export const value = 1;")
            .unwrap();
        let program = Program::new_with_options(
            &fs,
            "/project",
            &["main.ts".to_owned()],
            CompilerOptions {
                module: ModuleKind::EsNext,
                out_file: Some("/project/bundle.js".into()),
                no_lib: true,
                ..CompilerOptions::default()
            },
        );
        assert!(program.emit().files.is_empty());
    }

    #[test]
    fn resolved_node_modules_sources_are_not_emit_roots() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file("/project/main.ts", "import { value } from 'pkg'; value;")
            .unwrap();
        fs.write_file(
            "/project/node_modules/pkg/index.ts",
            "export const value = 1;",
        )
        .unwrap();
        let program = Program::new_with_options(
            &fs,
            "/project",
            &["main.ts".to_owned()],
            CompilerOptions {
                no_lib: true,
                ..CompilerOptions::default()
            },
        );
        let emitted = program.emit();
        assert!(
            emitted
                .files
                .iter()
                .any(|file| file.file_name == "/project/main.js")
        );
        assert!(
            emitted
                .files
                .iter()
                .all(|file| !file.file_name.contains("node_modules"))
        );
    }

    #[test]
    fn isolated_declaration_errors_suppress_declaration_output() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/main.ts",
            "const key: 0 = 0; export const value = { [key]: 1 };",
        )
        .unwrap();
        let program = Program::new_with_options(
            &fs,
            "/project",
            &["main.ts".to_owned()],
            CompilerOptions {
                declaration: true,
                isolated_declarations: true,
                no_lib: true,
                ..CompilerOptions::default()
            },
        );
        let emitted = program.emit();
        assert!(
            emitted
                .files
                .iter()
                .any(|file| file.file_name == "/project/main.js")
        );
        assert!(
            emitted
                .files
                .iter()
                .all(|file| file.file_name != "/project/main.d.ts")
        );
    }
}
