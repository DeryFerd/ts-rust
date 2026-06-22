//! Compiler Program and source-file graph foundations.

use std::collections::BTreeMap;

use ts_ast::{NodeData, NodeId};
use ts_binder::{BindResult, bind_source_file};
use ts_checker::{CheckResult, ProgramSource, check_program, check_source_file};
use ts_config::{ConfigDiagnostic, resolve_config_file};
use ts_core::TextRange;
use ts_diagnostics::message_by_code;
use ts_glob::{DiscoveryOptions, discover_files};
use ts_module::{ResolutionOptions, Resolver};
use ts_options::{CompilerOptions, parse_project_options};
use ts_parser::{ParseResult, parse_source_file};
use ts_path::{CaseSensitivity, canonicalize, is_absolute, resolve_path};
use ts_printer::emit_source_file_with_settings;
use ts_sourcemap::SourceMap;
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
        let resolver = Resolver::new(file_system, resolution_options);
        let mut file_index = 0;
        while file_index < program.source_files.len() {
            let containing_file = program.source_files[file_index].file_name.clone();
            let specifiers = module_specifiers(&program.source_files[file_index].parse);
            for (specifier, range) in specifiers {
                let result = resolver.resolve(&specifier, &containing_file);
                if let Some(resolved) = result.resolved {
                    let containing = canonicalize(
                        &containing_file,
                        &program.current_directory,
                        program.case_sensitivity,
                    );
                    let target = canonicalize(
                        &resolved.resolved_file_name,
                        &program.current_directory,
                        program.case_sensitivity,
                    );
                    program
                        .resolved_modules
                        .insert((containing, specifier.clone()), target);
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
        program.check_program();
        program
    }

    /// Creates a Program from the explicit `files` list in a tsconfig.
    /// Include/exclude glob expansion is added by the file-loader layer.
    #[must_use]
    pub fn from_config(file_system: &dyn FileSystem, config_path: &str) -> Self {
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
        let settings = self.options.printer_settings();
        if !settings.emit_javascript {
            return output;
        }
        let source_names = self
            .source_files
            .iter()
            .filter(|source_file| !ts_path::is_declaration_file(&source_file.file_name))
            .map(|source_file| source_file.file_name.clone())
            .collect::<Vec<_>>();
        let common_source_directory = ts_outputpaths::common_source_directory(
            &source_names,
            &self.current_directory,
            self.case_sensitivity,
        );
        for source_file in &self.source_files {
            if ts_path::is_declaration_file(&source_file.file_name) {
                continue;
            }
            match emit_source_file_with_settings(
                &source_file.parse.arena,
                source_file.parse.source_file,
                &source_file.file_name,
                &source_file.source_text,
                settings,
            ) {
                Ok(mut emitted) => {
                    let paths = ts_outputpaths::output_paths(
                        &source_file.file_name,
                        &self.options,
                        &self.current_directory,
                        &common_source_directory,
                        self.case_sensitivity,
                    );
                    let Some(file_name) = paths.javascript else {
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
                        } else if let Some(map_file_name) = paths.source_map {
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
                })
                .collect::<Vec<_>>();
            check_program(&inputs)
        };
        for (source_file, checking) in self.source_files.iter_mut().zip(checked.files) {
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
    fn resolves_inherited_options_and_base_relative_globs() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/repo/base/tsconfig.json",
            r#"{
                "include": ["src/**/*.ts"],
                "exclude": ["src/generated"],
                "compilerOptions": { "target": "es2015" }
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
        assert_eq!(program.source_files().len(), 2);
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
        assert_eq!(emitted.files[0].text, "var point = { x: 1 };\n");
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

    #[test]
    fn config_options_control_target_module_and_source_maps() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/tsconfig.json",
            "{ \"files\": [\"main.ts\"], \"compilerOptions\": { \"target\": \"es2015\", \"module\": \"commonjs\", \"sourceMap\": true } }",
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
                    "sourceMap": true
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
                "compilerOptions": { "outDir": "build", "inlineSourceMap": true }
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
}
