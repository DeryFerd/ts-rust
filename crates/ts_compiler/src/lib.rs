//! Compiler Program and source-file graph foundations.

use std::{
    collections::{BTreeMap, BTreeSet},
    path::Path,
};

use ts_ast::{NodeData, NodeId};
use ts_binder::{BindResult, bind_source_file};
use ts_checker::{
    CheckResult, CheckerOptions, EnumConstantValue as CheckerConstantValue, ProgramSource,
    check_program, empty_check_result,
};
use ts_config::{ConfigDiagnostic, resolve_config_file};
use ts_core::TextRange;
use ts_diagnostics::message_by_code;
use ts_glob::{DiscoveryOptions, discover_files};
use ts_module::{ResolutionOptions, Resolver, automatic_type_directive_names};
use ts_options::{CompilerOptions, PrinterSettings, parse_project_options};
use ts_parser::{ParseResult, parse_jsx_source_file, parse_source_file};
use ts_path::{CaseSensitivity, canonicalize, directory_path, is_absolute, resolve_path};
use ts_printer::{
    AmdDependency as PrinterAmdDependency, EmitConstantValue, EmitContext,
    emit_declaration_file_with_reachability, emit_source_file_with_context,
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

/// A compilation's parsed source-file graph.
#[derive(Debug, Default)]
pub struct Program {
    source_files: Vec<SourceFile>,
    file_index: BTreeMap<String, usize>,
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
            for (specifier, range, is_import_equals) in specifiers {
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
                } else if is_import_equals
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
        if self.options.out_file.is_some() {
            return self.emit_bundle(settings);
        }
        let source_names = self
            .source_files
            .iter()
            .filter(|source_file| {
                !source_file.is_default_library
                    && !ts_path::is_declaration_file(&source_file.file_name)
            })
            .map(|source_file| source_file.file_name.clone())
            .collect::<Vec<_>>();
        let common_source_directory = ts_outputpaths::common_source_directory(
            &source_names,
            &self.current_directory,
            self.case_sensitivity,
        );
        for source_file in &self.source_files {
            if source_file.is_default_library
                || ts_path::is_declaration_file(&source_file.file_name)
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
                let emit_context = EmitContext {
                    bindings: &source_file.binding,
                    amd_module_name: source_file.parse.amd_module_name.as_deref(),
                    amd_dependencies: &amd_dependencies,
                    enum_member_values: &enum_member_values,
                    enum_access_values: &enum_access_values,
                    import_runtime_meanings: &source_file.checking.import_runtime_meanings,
                    preserve_const_enums: self.options.preserve_const_enums
                        || self.options.isolated_modules
                        || self.options.verbatim_module_syntax,
                    inline_const_enums: !self.options.isolated_modules,
                };
                match emit_source_file_with_context(
                    &source_file.parse.arena,
                    source_file.parse.source_file,
                    &source_file.file_name,
                    &source_file.source_text,
                    settings,
                    &emit_context,
                ) {
                    Ok(mut emitted) => {
                        let Some(file_name) = paths.javascript.clone() else {
                            continue;
                        };
                        if let Some(mut source_map) = emitted.source_map {
                            source_map.file = file_name.rsplit('/').next().map(str::to_owned);
                            let serialized = serialize_source_map(&source_map);
                            if settings.inline_source_map {
                                emitted
                                    .code
                                    .push_str("//# sourceMappingURL=data:application/json;base64,");
                                emitted.code.push_str(&base64_encode(serialized.as_bytes()));
                                emitted.code.push('\n');
                            } else if let Some(map_file_name) = paths.source_map.clone() {
                                emitted.code.push_str("//# sourceMappingURL=");
                                emitted.code.push_str(
                                    map_file_name.rsplit('/').next().unwrap_or(&map_file_name),
                                );
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
                match emit_declaration_file_with_reachability(
                    &source_file.parse.arena,
                    source_file.parse.source_file,
                    &source_file.file_name,
                    &source_file.source_text,
                    self.options.declaration_map,
                    Some(&source_file.checking.declaration_reachability),
                    Some(&enum_member_values),
                ) {
                    Ok(mut emitted) => {
                        let Some(file_name) = paths.declaration.clone() else {
                            continue;
                        };
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
                                    text: serialize_source_map(&source_map),
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
        let sources = self
            .source_files
            .iter()
            .filter(|source| {
                !source.is_default_library && !ts_path::is_declaration_file(&source.file_name)
            })
            .collect::<Vec<_>>();

        if settings.emit_javascript {
            let mut code = String::new();
            let mut map_builder = settings.source_map.then(SourceMapBuilder::new);
            let mut map_sources = Vec::new();
            for source in &sources {
                let generated_line =
                    u32::try_from(code.bytes().filter(|byte| *byte == b'\n').count())
                        .unwrap_or(u32::MAX);
                let mut source_settings = settings;
                source_settings.source_map = false;
                source_settings.inline_source_map = false;
                source_settings.always_strict = settings.always_strict && code.is_empty();
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
                let emit_context = EmitContext {
                    bindings: &source.binding,
                    amd_module_name: source.parse.amd_module_name.as_deref(),
                    amd_dependencies: &amd_dependencies,
                    enum_member_values: &enum_member_values,
                    enum_access_values: &enum_access_values,
                    import_runtime_meanings: &source.checking.import_runtime_meanings,
                    preserve_const_enums: self.options.preserve_const_enums
                        || self.options.isolated_modules
                        || self.options.verbatim_module_syntax,
                    inline_const_enums: !self.options.isolated_modules,
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
            }
            if let Some(mut map) = map_builder.map(|builder| builder.finish(None, map_sources)) {
                let Some(file_name) = paths.javascript.as_ref() else {
                    return output;
                };
                map.file = file_name.rsplit('/').next().map(str::to_owned);
                let serialized = serialize_source_map(&map);
                if settings.inline_source_map {
                    code.push_str("//# sourceMappingURL=data:application/json;base64,");
                    code.push_str(&base64_encode(serialized.as_bytes()));
                    code.push('\n');
                } else if let Some(map_file_name) = paths.source_map.clone() {
                    code.push_str("//# sourceMappingURL=");
                    code.push_str(map_file_name.rsplit('/').next().unwrap_or(&map_file_name));
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
            let mut code = String::new();
            let mut map_builder = self.options.declaration_map.then(SourceMapBuilder::new);
            let mut map_sources = Vec::new();
            for source in &sources {
                let generated_line =
                    u32::try_from(code.bytes().filter(|byte| *byte == b'\n').count())
                        .unwrap_or(u32::MAX);
                let enum_member_values = enum_values_for_emit(&source.checking.enum_member_values);
                match emit_declaration_file_with_reachability(
                    &source.parse.arena,
                    source.parse.source_file,
                    &source.file_name,
                    &source.source_text,
                    false,
                    Some(&source.checking.declaration_reachability),
                    Some(&enum_member_values),
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
                        text: serialize_source_map(&map),
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

        if self.options.no_emit_on_error && !output.diagnostics.is_empty() {
            output.files.clear();
        }
        output
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
            check_program(&inputs)
        };
        for (source_file, mut checking) in self.source_files.iter_mut().zip(checked.files) {
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
        });
    }
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

fn serialize_source_map(source_map: &SourceMap) -> String {
    #[derive(serde::Serialize)]
    #[serde(rename_all = "camelCase")]
    struct SerializedSourceMap<'a> {
        version: u8,
        file: &'a Option<String>,
        source_root: &'static str,
        sources: &'a [String],
        names: &'a [String],
        mappings: &'a str,
    }

    serde_json::to_string(&SerializedSourceMap {
        version: source_map.version,
        file: &source_map.file,
        source_root: "",
        sources: &source_map.sources,
        names: &source_map.names,
        mappings: &source_map.mappings,
    })
    .expect("source map fields are JSON-serializable")
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
    parse
        .arena
        .iter()
        .filter_map(|(_, node)| match &node.data {
            NodeData::ImportDeclaration(data) => {
                string_literal(&parse.arena, data.module_specifier)
                    .map(|(specifier, range)| (specifier, range, false))
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
                .map(|(specifier, range)| (specifier, range, false)),
            _ => None,
        })
        .collect()
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

fn declaration_modifiers(node: &ts_ast::Node) -> Option<&ts_ast::ModifierList> {
    match &node.data {
        NodeData::VariableStatement(data) => data.modifiers.as_ref(),
        NodeData::FunctionDeclaration(data) => data.modifiers.as_ref(),
        NodeData::ClassDeclaration(data) => data.modifiers.as_ref(),
        NodeData::InterfaceDeclaration(data) => data.modifiers.as_ref(),
        NodeData::TypeAliasDeclaration(data) => data.modifiers.as_ref(),
        NodeData::EnumDeclaration(data) => data.modifiers.as_ref(),
        NodeData::ModuleDeclaration(data) => data.modifiers.as_ref(),
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
    use std::time::{Duration, Instant};

    use ts_options::{CompilerOptions, ModuleKind, ScriptTarget};
    use ts_vfs::{FileSystem, MemoryFileSystem};

    use super::Program;

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
                "    ///<amd-module name='Consumer'/>\n",
                "    Object.defineProperty(exports, \"__esModule\", { value: true });\n",
                "    M.value;\n",
                "});\n",
            )
        );
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
        assert!(paths.contains(&"/project/view.jsx"));
        assert!(paths.contains(&"/project/module.mjs"));
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
        assert_eq!(emitted.files[0].file_name, "/project/view.jsx");
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
            javascript.contains("const value = 1 /* E.A */;"),
            "{javascript}"
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
            "export declare const version: number;\nexport declare function identity<T>(value: T): T;\nexport interface Box<T> {\n    value: T;\n}\nexport type Maybe<T> = T | undefined;\nexport declare enum Color {\n    Red,\n    Blue = 2,\n}\n//# sourceMappingURL=api.d.mts.map\n"
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
                "compilerOptions": { "outDir": "types", "emitDeclarationOnly": true, "noLib": true }
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
}
