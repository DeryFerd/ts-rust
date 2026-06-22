//! Compiler Program and source-file graph foundations.

use std::collections::BTreeMap;

use ts_ast::{NodeData, NodeId};
use ts_binder::{BindResult, bind_source_file};
use ts_checker::{CheckResult, check_source_file};
use ts_config::{ConfigDiagnostic, parse_config_file};
use ts_core::TextRange;
use ts_diagnostics::message_by_code;
use ts_glob::{DiscoveryOptions, discover_files};
use ts_module::{ResolutionOptions, Resolver};
use ts_options::{CompilerOptions, parse_project_options};
use ts_parser::{ParseResult, parse_source_file};
use ts_path::{CaseSensitivity, canonicalize, is_absolute, resolve_path};
use ts_printer::emit_source_file;
use ts_vfs::FileSystem;

/// One parsed source file owned by a Program.
#[derive(Debug)]
pub struct SourceFile {
    pub file_name: String,
    pub source_text: String,
    pub parse: ParseResult,
    pub binding: BindResult,
    pub checking: CheckResult,
}

/// A diagnostic produced while constructing or parsing a Program.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ProgramDiagnostic {
    pub file_name: Option<String>,
    pub range: Option<TextRange>,
    pub code: Option<u32>,
    pub message: String,
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
        let mut program = Self::new(file_system, current_directory, root_names);
        let resolver = Resolver::new(file_system, resolution_options);
        let mut file_index = 0;
        while file_index < program.source_files.len() {
            let containing_file = program.source_files[file_index].file_name.clone();
            let specifiers = module_specifiers(&program.source_files[file_index].parse);
            for (specifier, range) in specifiers {
                let result = resolver.resolve(&specifier, &containing_file);
                if let Some(resolved) = result.resolved {
                    program.load_file(file_system, &resolved.resolved_file_name, false);
                } else {
                    program.diagnostics.push(module_not_found_diagnostic(
                        &containing_file,
                        range,
                        &specifier,
                    ));
                }
            }
            file_index += 1;
        }
        program
    }

    /// Creates a Program from the explicit `files` list in a tsconfig.
    /// Include/exclude glob expansion is added by the file-loader layer.
    #[must_use]
    pub fn from_config(file_system: &dyn FileSystem, config_path: &str) -> Self {
        let parsed = parse_config_file(file_system, config_path);
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
        let options_result = parse_project_options(&config);
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
        let mut program = Self::new_with_module_resolution(
            file_system,
            config_directory,
            &roots,
            options_result.options.module_resolution_options(),
        );
        program.options = options_result.options;
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
    pub fn emit(&self) -> EmitOutput {
        let mut output = EmitOutput::default();
        if !self.options.printer_settings().emit_javascript {
            return output;
        }
        for source_file in &self.source_files {
            if ts_path::is_declaration_file(&source_file.file_name) {
                continue;
            }
            match emit_source_file(&source_file.parse.arena, source_file.parse.source_file) {
                Ok(emitted) => output.files.push(OutputFile {
                    file_name: javascript_output_path(&source_file.file_name),
                    text: emitted.code,
                }),
                Err(error) => output.diagnostics.push(ProgramDiagnostic {
                    file_name: Some(source_file.file_name.clone()),
                    range: source_file
                        .parse
                        .arena
                        .get(error.node)
                        .map(|node| node.range),
                    code: None,
                    message: error.to_string(),
                }),
            }
        }
        output
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
        let parse = parse_source_file(&source_text);
        for diagnostic in &parse.diagnostics {
            self.diagnostics.push(ProgramDiagnostic {
                file_name: Some(file_name.to_owned()),
                range: Some(diagnostic.range),
                code: None,
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
        let checking = check_source_file(&parse.arena, parse.source_file, &binding);
        for diagnostic in &checking.diagnostics {
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
        let index = self.source_files.len();
        self.file_index.insert(canonical, index);
        self.source_files.push(SourceFile {
            file_name: file_name.to_owned(),
            source_text,
            parse,
            binding,
            checking,
        });
    }
}

fn javascript_output_path(file_name: &str) -> String {
    for (source, output) in [
        (".mts", ".mjs"),
        (".cts", ".cjs"),
        (".tsx", ".js"),
        (".ts", ".js"),
    ] {
        if let Some(stem) = file_name.strip_suffix(source) {
            return format!("{stem}{output}");
        }
    }
    file_name.to_owned()
}

fn module_specifiers(parse: &ParseResult) -> Vec<(String, TextRange)> {
    parse
        .arena
        .iter()
        .filter_map(|(_, node)| match &node.data {
            NodeData::ImportDeclaration(data) => {
                string_literal(&parse.arena, data.module_specifier)
            }
            NodeData::ExportDeclaration(data) => data
                .module_specifier
                .and_then(|specifier| string_literal(&parse.arena, specifier)),
            _ => None,
        })
        .collect()
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
    use ts_vfs::{FileSystem, MemoryFileSystem};

    use super::Program;

    #[test]
    fn parses_and_indexes_explicit_roots() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file("/project/main.ts", "const answer: number = 40 + 2;")
            .unwrap();
        let program = Program::new(&fs, "/project", &["main.ts".to_owned()]);
        assert!(program.diagnostics().is_empty());
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
    fn constructs_roots_from_config_files() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/tsconfig.json",
            "{ \"files\": [\"src/a.ts\", \"src/b.ts\"] }",
        )
        .unwrap();
        fs.write_file("/project/src/a.ts", "let a = 1;").unwrap();
        fs.write_file("/project/src/b.ts", "let b = 2;").unwrap();
        let program = Program::from_config(&fs, "/project/tsconfig.json");
        assert_eq!(program.source_files().len(), 2);
        assert!(program.diagnostics().is_empty());
    }

    #[test]
    fn discovers_config_include_patterns() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/tsconfig.json",
            "{ \"include\": [\"src/**/*.ts\"], \"exclude\": [\"src/generated\"] }",
        )
        .unwrap();
        fs.write_file("/project/src/a.ts", "let a = 1;").unwrap();
        fs.write_file("/project/src/nested/b.ts", "let b = 2;")
            .unwrap();
        fs.write_file("/project/src/generated/c.ts", "let c = 3;")
            .unwrap();
        let program = Program::from_config(&fs, "/project/tsconfig.json");
        assert_eq!(program.source_files().len(), 2);
        assert!(program.diagnostics().is_empty());
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
        assert_eq!(emitted.files[0].text, "const point = { x: 1 };\n");
    }

    #[test]
    fn checks_annotated_variable_assignability() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file("/type-error.ts", "const value: string = 1;")
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
    fn config_options_control_emit_and_resolution() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/tsconfig.json",
            "{ \"files\": [\"main.ts\"], \"compilerOptions\": { \"noEmit\": true, \"module\": \"esnext\" } }",
        )
        .unwrap();
        fs.write_file("/project/main.ts", "const value = 1;")
            .unwrap();
        let program = Program::from_config(&fs, "/project/tsconfig.json");
        assert!(program.diagnostics().is_empty());
        assert!(program.options().no_emit);
        assert!(program.emit().files.is_empty());
    }
}
