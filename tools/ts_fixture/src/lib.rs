//! Parsing for TypeScript's directive-based compiler test fixtures.
//!
//! A fixture can describe one source file directly, or several virtual files
//! separated by `// @filename: path` directives. Other directives are retained
//! as name/value metadata for the compiler harness.

use std::{collections::BTreeMap, fmt, ops::Range, path::PathBuf};

use ts_core::SourceText;
use ts_vfs::{FileSystem, MemoryFileSystem};

/// A parsed compiler test case.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Case {
    /// Path of the fixture containing the test case.
    pub path: PathBuf,
    /// Exact, unmodified contents of the fixture.
    pub source_text: SourceText,
    /// Directives in source order, including `filename` directives.
    pub directives: Vec<Directive>,
    /// Source units in compilation order.
    pub units: Vec<Unit>,
}

impl Case {
    /// Parses one compiler test fixture.
    ///
    /// # Errors
    ///
    /// Returns an error when a `filename` directive has an empty value.
    pub fn parse(
        path: impl Into<PathBuf>,
        source_text: impl Into<SourceText>,
    ) -> Result<Self, ParseError> {
        let path = path.into();
        let source_text = source_text.into();
        let mut directives = Vec::new();
        let mut units = Vec::new();
        let mut current = UnitBuilder::new(path.clone(), 1, false);
        let mut byte_offset = 0;

        for (line_index, line_with_ending) in source_text
            .as_bytes()
            .split_inclusive(|byte| *byte == b'\n')
            .enumerate()
        {
            let line_number = line_index + 1;
            let line = strip_line_ending(line_with_ending);

            if let Some((line_text, name, value)) =
                std::str::from_utf8(line).ok().and_then(|text| {
                    parse_directive_line(text).map(|(name, value)| (text, name, value))
                })
            {
                let directive = Directive {
                    name: name.to_owned(),
                    value: value.to_owned(),
                    line: line_number,
                    byte_range: byte_offset..byte_offset + line.len(),
                    raw_text: line_text.to_owned(),
                };

                if directive.is_filename() {
                    if directive.value.is_empty() {
                        return Err(ParseError::EmptyFileName { line: line_number });
                    }

                    if current.explicit || current.has_source() {
                        units.push(current.finish());
                    }
                    current = UnitBuilder::new(
                        PathBuf::from(&directive.value),
                        line_number.saturating_add(1),
                        true,
                    );
                }
                directives.push(directive);
            } else {
                current.source_bytes.extend_from_slice(line_with_ending);
            }

            byte_offset += line_with_ending.len();
        }

        // `split_inclusive` yields no item for an empty source. It also handles a
        // final non-newline-terminated line, so no separate tail pass is needed.
        if current.explicit || current.has_source() || units.is_empty() {
            units.push(current.finish());
        }

        Ok(Self {
            path,
            source_text,
            directives,
            units,
        })
    }

    /// Returns all values of a directive, matching names case-insensitively.
    pub fn directive_values<'a>(&'a self, name: &'a str) -> impl Iterator<Item = &'a str> + 'a {
        self.directives
            .iter()
            .filter(move |directive| directive.name.eq_ignore_ascii_case(name))
            .map(|directive| directive.value.as_str())
    }
}

/// Deterministic result of compiling one directive-based fixture variant.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Compilation {
    pub diagnostics: Vec<CompilationDiagnostic>,
    pub outputs: BTreeMap<String, String>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CompilationDiagnostic {
    pub file_name: Option<String>,
    pub code: Option<u32>,
    pub message: String,
}

/// One deterministic combination of scalar compiler-option directives.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct OptionVariant {
    pub values: BTreeMap<String, String>,
}

/// Compilation and baseline comparison for one option variant.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct BaselineRun {
    pub variant: OptionVariant,
    pub compilation: Compilation,
    pub comparison: BaselineComparison,
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct BaselineComparison {
    pub differences: Vec<OutputDifference>,
}

impl BaselineComparison {
    #[must_use]
    pub fn is_match(&self) -> bool {
        self.differences.is_empty()
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct OutputDifference {
    pub section: String,
    pub kind: OutputDifferenceKind,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum OutputDifferenceKind {
    Missing { expected: String },
    Unexpected { actual: String },
    Content { expected: String, actual: String },
}

/// Parses TypeScript's `//// [file]` baseline sections, preserving section
/// contents exactly apart from the marker line itself.
#[must_use]
pub fn parse_baseline_sections(baseline: &str) -> BTreeMap<String, String> {
    let mut sections = BTreeMap::new();
    let mut current_name: Option<String> = None;
    let mut current_text = String::new();
    for line in baseline.split_inclusive('\n') {
        let marker = line.trim_end_matches(['\r', '\n']);
        if let Some(name) = marker
            .strip_prefix("//// [")
            .and_then(|marker| marker.split_once(']').map(|(name, _)| name))
        {
            if let Some(name) = current_name.replace(name.to_owned()) {
                sections.insert(name, std::mem::take(&mut current_text));
            }
        } else if current_name.is_some() {
            current_text.push_str(line);
        }
    }
    if let Some(name) = current_name {
        sections.insert(name, current_text);
    }
    sections
}

/// Expands comma-separated scalar option directives as a Cartesian product.
/// Option names are ordered canonically and values retain directive order.
#[must_use]
pub fn expand_option_matrix(case: &Case) -> Vec<OptionVariant> {
    let mut option_values = BTreeMap::<String, Vec<String>>::new();
    for &name in SCALAR_OPTION_NAMES {
        let Some(value) = case.directive_values(name).next() else {
            continue;
        };
        let values = value
            .split(',')
            .map(str::trim)
            .filter(|value| !value.is_empty())
            .map(str::to_owned)
            .collect::<Vec<_>>();
        option_values.insert(
            name.to_owned(),
            if values.is_empty() {
                vec![String::new()]
            } else {
                values
            },
        );
    }
    for &name in LIST_OPTION_NAMES {
        if let Some(value) = case.directive_values(name).next() {
            option_values.insert(name.to_owned(), vec![value.to_owned()]);
        }
    }

    let mut variants = vec![OptionVariant::default()];
    for (name, values) in option_values {
        let mut expanded = Vec::with_capacity(variants.len() * values.len());
        for variant in variants {
            for value in &values {
                let mut variant = variant.clone();
                variant.values.insert(name.clone(), value.clone());
                expanded.push(variant);
            }
        }
        variants = expanded;
    }
    variants
}

/// Compares compiler outputs with JavaScript and declaration baseline sections.
#[must_use]
pub fn compare_emitted_output_sections(
    outputs: &BTreeMap<String, String>,
    baseline: &str,
) -> BaselineComparison {
    let expected = parse_baseline_sections(baseline)
        .into_iter()
        .filter(|(name, _)| is_emitted_section(name))
        .map(|(name, text)| (normalize_section_name(&name), text))
        .collect::<BTreeMap<_, _>>();
    let actual = outputs
        .iter()
        .filter(|(name, _)| is_emitted_section(name))
        .map(|(name, text)| (normalize_section_name(name), text.clone()))
        .collect::<BTreeMap<_, _>>();
    let names = expected
        .keys()
        .chain(actual.keys())
        .cloned()
        .collect::<std::collections::BTreeSet<_>>();
    let differences = names
        .into_iter()
        .filter_map(|section| {
            let kind = match (expected.get(&section), actual.get(&section)) {
                (Some(expected), Some(actual)) if expected != actual => {
                    OutputDifferenceKind::Content {
                        expected: expected.clone(),
                        actual: actual.clone(),
                    }
                }
                (Some(expected), None) => OutputDifferenceKind::Missing {
                    expected: expected.clone(),
                },
                (None, Some(actual)) => OutputDifferenceKind::Unexpected {
                    actual: actual.clone(),
                },
                _ => return None,
            };
            Some(OutputDifference { section, kind })
        })
        .collect();
    BaselineComparison { differences }
}

/// Compiles a fixture using its first value for each compiler-option directive.
///
/// This deliberately represents one variant. Matrix expansion for directives
/// such as `@target: es5, esnext` belongs in the baseline runner.
///
/// # Errors
///
/// Returns an I/O error only if the in-memory fixture filesystem rejects a
/// virtual source path.
pub fn compile_case(case: &Case) -> std::io::Result<Compilation> {
    let variant = expand_option_matrix(case)
        .into_iter()
        .next()
        .unwrap_or_default();
    compile_case_variant(case, &variant)
}

/// Compiles every scalar compiler-option variant in deterministic order.
///
/// # Errors
///
/// Returns an I/O error if the fixture filesystem rejects a virtual source.
pub fn compile_case_matrix(case: &Case) -> std::io::Result<Vec<(OptionVariant, Compilation)>> {
    expand_option_matrix(case)
        .into_iter()
        .map(|variant| {
            compile_case_variant(case, &variant).map(|compilation| (variant, compilation))
        })
        .collect()
}

/// Compiles every option variant and compares it with an emit baseline.
///
/// # Errors
///
/// Returns an I/O error if the fixture filesystem rejects a virtual source.
pub fn run_case_against_baseline(case: &Case, baseline: &str) -> std::io::Result<Vec<BaselineRun>> {
    compile_case_matrix(case)?
        .into_iter()
        .map(|(variant, compilation)| {
            let comparison = compare_emitted_output_sections(&compilation.outputs, baseline);
            Ok(BaselineRun {
                variant,
                compilation,
                comparison,
            })
        })
        .collect()
}

fn compile_case_variant(case: &Case, variant: &OptionVariant) -> std::io::Result<Compilation> {
    let file_system = MemoryFileSystem::new(true);
    let mut roots = Vec::with_capacity(case.units.len());
    for (index, unit) in case.units.iter().enumerate() {
        let path = virtual_unit_path(case, unit, index);
        file_system.write_file(&path, unit.source_text.as_scannable_str())?;
        roots.push(path);
    }

    let mut compiler_options = fixture_compiler_options(variant);
    // Compiler baselines generally assume libraries. Keeping this enabled is
    // important for diagnostic fidelity even though syntax-only corpus tests
    // use the cheaper parser path directly.
    if case.directive_values("noLib").next().is_none() {
        compiler_options.no_lib = false;
    }
    let program =
        ts_compiler::Program::new_with_options(&file_system, "/case", &roots, compiler_options);
    let emit = program.emit();
    let diagnostics = program
        .diagnostics()
        .iter()
        .chain(&emit.diagnostics)
        .map(|diagnostic| CompilationDiagnostic {
            file_name: diagnostic.file_name.clone(),
            code: diagnostic.code,
            message: diagnostic.message.clone(),
        })
        .collect();
    let outputs = emit
        .files
        .into_iter()
        .map(|output| (output.file_name, output.text))
        .collect();
    Ok(Compilation {
        diagnostics,
        outputs,
    })
}

fn virtual_unit_path(case: &Case, unit: &Unit, index: usize) -> String {
    let path = unit.path.to_string_lossy().replace('\\', "/");
    if path.starts_with('/') {
        return ts_path::normalize_path(&path);
    }
    if unit.path == case.path {
        let base = unit
            .path
            .file_name()
            .and_then(|name| name.to_str())
            .map_or_else(|| format!("unit{index}.ts"), str::to_owned);
        return ts_path::resolve_path("/case", &[&base]);
    }
    ts_path::resolve_path("/case", &[&path])
}

fn fixture_compiler_options(variant: &OptionVariant) -> ts_options::CompilerOptions {
    let mut values = BTreeMap::new();
    for (name, value) in &variant.values {
        values.insert(name.to_owned(), directive_json_value(name, value));
    }
    ts_options::parse_compiler_options(&ts_config::JsonValue::Object(values)).options
}

fn directive_json_value(name: &str, value: &str) -> ts_config::JsonValue {
    if LIST_OPTION_NAMES
        .iter()
        .any(|option| name.eq_ignore_ascii_case(option))
    {
        return ts_config::JsonValue::Array(
            value
                .split(',')
                .map(str::trim)
                .filter(|part| !part.is_empty())
                .map(|part| ts_config::JsonValue::String(part.to_owned()))
                .collect(),
        );
    }
    match value {
        value if value.eq_ignore_ascii_case("true") => ts_config::JsonValue::Bool(true),
        value if value.eq_ignore_ascii_case("false") => ts_config::JsonValue::Bool(false),
        value => ts_config::JsonValue::String(
            value
                .split_once(',')
                .map_or(value, |(first, _)| first)
                .trim()
                .to_owned(),
        ),
    }
}

const SCALAR_OPTION_NAMES: &[&str] = &[
    "allowJs",
    "allowSyntheticDefaultImports",
    "checkJs",
    "composite",
    "declaration",
    "declarationMap",
    "declarationDir",
    "emitDeclarationOnly",
    "esModuleInterop",
    "forceConsistentCasingInFileNames",
    "incremental",
    "inlineSourceMap",
    "isolatedModules",
    "jsx",
    "module",
    "moduleDetection",
    "moduleResolution",
    "noCheck",
    "noEmit",
    "noImplicitAny",
    "noLib",
    "noUnusedLocals",
    "noUnusedParameters",
    "outDir",
    "resolveJsonModule",
    "rootDir",
    "skipLibCheck",
    "sourceMap",
    "strict",
    "strictNullChecks",
    "target",
    "tsBuildInfoFile",
    "verbatimModuleSyntax",
];

const LIST_OPTION_NAMES: &[&str] = &["lib", "rootDirs", "typeRoots", "types"];

fn is_emitted_section(name: &str) -> bool {
    let name = name.to_ascii_lowercase();
    [".js", ".jsx", ".mjs", ".cjs", ".d.ts", ".d.mts", ".d.cts"]
        .iter()
        .any(|extension| name.ends_with(extension))
}

fn normalize_section_name(name: &str) -> String {
    let name = name.replace('\\', "/");
    name.strip_prefix("/case/")
        .or_else(|| name.strip_prefix("./"))
        .unwrap_or(name.trim_start_matches('/'))
        .to_owned()
}

/// One virtual source file declared by a fixture.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Unit {
    /// Virtual path used by the compiler harness.
    pub path: PathBuf,
    /// Source text with harness directive lines removed. Line endings and all
    /// other bytes are preserved.
    pub source_text: SourceText,
    /// One-based fixture line at which this unit's source begins.
    pub start_line: usize,
}

/// One `// @name: value` compiler test directive.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Directive {
    /// Directive name as written, without `@`.
    pub name: String,
    /// Trimmed directive value.
    pub value: String,
    /// One-based line number in the fixture.
    pub line: usize,
    /// Half-open byte range of the directive line, excluding its line ending.
    pub byte_range: Range<usize>,
    /// Exact directive line, excluding its line ending.
    pub raw_text: String,
}

impl Directive {
    /// Whether this directive starts a new virtual source file.
    #[must_use]
    pub fn is_filename(&self) -> bool {
        self.name.eq_ignore_ascii_case("filename")
    }
}

/// A malformed fixture directive.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ParseError {
    /// A `filename` directive did not specify a virtual path.
    EmptyFileName { line: usize },
}

impl fmt::Display for ParseError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::EmptyFileName { line } => {
                write!(formatter, "empty @filename directive on line {line}")
            }
        }
    }
}

impl std::error::Error for ParseError {}

struct UnitBuilder {
    path: PathBuf,
    source_bytes: Vec<u8>,
    start_line: usize,
    explicit: bool,
}

impl UnitBuilder {
    fn new(path: PathBuf, start_line: usize, explicit: bool) -> Self {
        Self {
            path,
            source_bytes: Vec::new(),
            start_line,
            explicit,
        }
    }

    fn has_source(&self) -> bool {
        !SourceText::from_bytes(self.source_bytes.clone())
            .as_scannable_str()
            .trim()
            .is_empty()
    }

    fn finish(self) -> Unit {
        Unit {
            path: self.path,
            source_text: SourceText::from_bytes(self.source_bytes),
            start_line: self.start_line,
        }
    }
}

fn strip_line_ending(line: &[u8]) -> &[u8] {
    let line = line.strip_suffix(b"\n").unwrap_or(line);
    line.strip_suffix(b"\r").unwrap_or(line)
}

fn parse_directive_line(line: &str) -> Option<(&str, &str)> {
    let comment = line.trim_start().strip_prefix("//")?.trim_start();
    let directive = comment.strip_prefix('@')?;
    let (name, value) = directive.split_once(':')?;
    let name = name.trim();
    if name.is_empty() || !name.chars().all(is_directive_name_character) {
        return None;
    }
    Some((name, value.trim()))
}

fn is_directive_name_character(character: char) -> bool {
    character.is_ascii_alphanumeric() || matches!(character, '_' | '-')
}

#[cfg(test)]
mod tests {
    use std::{collections::BTreeMap, path::Path};

    use super::{
        Case, OutputDifferenceKind, ParseError, compare_emitted_output_sections, compile_case,
        compile_case_matrix, expand_option_matrix, parse_baseline_sections,
        run_case_against_baseline,
    };

    #[test]
    fn parses_single_file_and_preserves_original_source() {
        let source = "// @target: esnext\r\n// @strict: true\r\n\r\nconst answer = 42;\r\n";
        let case = Case::parse("tests/cases/compiler/simple.ts", source).unwrap();

        assert_eq!(case.path, Path::new("tests/cases/compiler/simple.ts"));
        assert_eq!(case.source_text, source);
        assert_eq!(case.units.len(), 1);
        assert_eq!(case.units[0].path, case.path);
        assert_eq!(case.units[0].source_text, "\r\nconst answer = 42;\r\n");
        assert_eq!(
            case.directive_values("TARGET").collect::<Vec<_>>(),
            ["esnext"]
        );
        assert_eq!(case.directives[1].line, 2);
        assert_eq!(case.directives[1].raw_text, "// @strict: true");
    }

    #[test]
    fn parses_multiple_virtual_files_and_options() {
        let source = concat!(
            "// @target: esnext\n",
            "// @module: preserve, commonjs\n",
            "\n",
            "// @filename: /src/fileA.ts\n",
            "export interface Person { name: string }\n",
            "// @Filename: ./fileB.js\n",
            "/** @param {import('./fileA').Person} person */\n",
            "export function greet(person) {}\n",
        );
        let case = Case::parse("multiFile.ts", source).unwrap();

        assert_eq!(case.units.len(), 2);
        assert_eq!(case.units[0].path, Path::new("/src/fileA.ts"));
        assert_eq!(
            case.units[0].source_text,
            "export interface Person { name: string }\n"
        );
        assert_eq!(case.units[0].start_line, 5);
        assert_eq!(case.units[1].path, Path::new("./fileB.js"));
        assert_eq!(
            case.units[1].source_text,
            "/** @param {import('./fileA').Person} person */\nexport function greet(person) {}\n"
        );
        assert_eq!(case.units[1].start_line, 7);
        assert_eq!(case.directives.len(), 4);
        assert!(case.directives[2].is_filename());
    }

    #[test]
    fn retains_substantive_implicit_unit_before_named_units() {
        let source = "const implicit = 1;\n// @filename: named.ts\nconst named = 2;";
        let case = Case::parse("mixed.ts", source).unwrap();

        assert_eq!(case.units.len(), 2);
        assert_eq!(case.units[0].path, Path::new("mixed.ts"));
        assert_eq!(case.units[0].source_text, "const implicit = 1;\n");
        assert_eq!(case.units[1].path, Path::new("named.ts"));
        assert_eq!(case.units[1].source_text, "const named = 2;");
    }

    #[test]
    fn ignores_comment_text_that_is_not_a_directive() {
        let source = "// @not a directive\n// ordinary comment\nconst value = 1;";
        let case = Case::parse("comments.ts", source).unwrap();

        assert!(case.directives.is_empty());
        assert_eq!(case.units[0].source_text, source);
    }

    #[test]
    fn rejects_an_empty_virtual_filename() {
        let error = Case::parse("bad.ts", "// @filename:   \nconst value = 1;").unwrap_err();

        assert_eq!(error, ParseError::EmptyFileName { line: 1 });
        assert_eq!(error.to_string(), "empty @filename directive on line 1");
    }

    #[test]
    fn represents_an_empty_case_as_one_empty_unit() {
        let case = Case::parse("empty.ts", "").unwrap();

        assert_eq!(case.units.len(), 1);
        assert_eq!(case.units[0].path, Path::new("empty.ts"));
        assert!(case.units[0].source_text.is_empty());
    }

    #[test]
    fn preserves_invalid_utf8_in_cases_and_units() {
        let bytes = b"// @target: esnext\n/\x80/u\n".to_vec();
        let case = Case::parse("invalid.ts", bytes.clone()).unwrap();

        assert_eq!(case.source_text.as_bytes(), bytes);
        assert!(!case.source_text.is_valid_utf8());
        assert_eq!(case.units[0].source_text.as_bytes(), b"/\x80/u\n");
        assert_eq!(
            case.directive_values("target").collect::<Vec<_>>(),
            ["esnext"]
        );
    }

    #[test]
    fn compiles_virtual_units_with_fixture_options() {
        let case = Case::parse(
            "fixture.ts",
            concat!(
                "// @target: esnext\n",
                "// @module: esnext\n",
                "// @noLib: true\n",
                "// @filename: a.ts\n",
                "export const value: number = 1;\n",
                "// @filename: b.ts\n",
                "import { value } from './a';\n",
                "export const result = value + 1;\n",
            ),
        )
        .unwrap();
        let compilation = compile_case(&case).unwrap();
        assert!(
            compilation.diagnostics.is_empty(),
            "{:?}",
            compilation.diagnostics
        );
        assert_eq!(compilation.outputs.len(), 2);
        assert_eq!(
            compilation.outputs["/case/a.js"],
            "export const value = 1;\n"
        );
        assert!(compilation.outputs["/case/b.js"].contains("result = value + 1"));
    }

    #[test]
    fn parses_typescript_baseline_sections() {
        let sections = parse_baseline_sections(concat!(
            "preamble\n",
            "//// [input.ts] ////\n",
            "const value: number = 1;\n",
            "//// [input.js] ////\n",
            "const value = 1;\n",
        ));
        assert_eq!(sections.len(), 2);
        assert_eq!(sections["input.ts"], "const value: number = 1;\n");
        assert_eq!(sections["input.js"], "const value = 1;\n");
    }

    #[test]
    fn expands_scalar_options_as_a_deterministic_matrix() {
        let case = Case::parse(
            "matrix.ts",
            concat!(
                "// @target: es5, esnext\n",
                "// @module: commonjs, esnext\n",
                "// @lib: es5, dom\n",
                "const value = 1;\n",
            ),
        )
        .unwrap();
        let variants = expand_option_matrix(&case);
        assert_eq!(variants.len(), 4);
        let values = variants
            .iter()
            .map(|variant| {
                (
                    variant.values["module"].as_str(),
                    variant.values["target"].as_str(),
                    variant.values["lib"].as_str(),
                )
            })
            .collect::<Vec<_>>();
        assert_eq!(
            values,
            [
                ("commonjs", "es5", "es5, dom"),
                ("commonjs", "esnext", "es5, dom"),
                ("esnext", "es5", "es5, dom"),
                ("esnext", "esnext", "es5, dom"),
            ]
        );
        assert_eq!(compile_case_matrix(&case).unwrap().len(), 4);
    }

    #[test]
    fn compares_only_emitted_baseline_sections_with_actionable_differences() {
        let outputs = BTreeMap::from([
            ("/case/a.js".into(), "const a = 1;\n".into()),
            ("/case/a.d.ts".into(), "declare const a = 2;\n".into()),
            ("/case/a.js.map".into(), "ignored".into()),
            ("/case/c.js".into(), "const c = 1;\n".into()),
        ]);
        let comparison = compare_emitted_output_sections(
            &outputs,
            concat!(
                "//// [a.ts] ////\n",
                "const a: number = 1;\n",
                "//// [a.js] ////\n",
                "const a = 1;\n",
                "//// [a.d.ts] ////\n",
                "declare const a = 1;\n",
                "//// [b.js] ////\n",
                "const b = 1;\n",
            ),
        );
        assert!(!comparison.is_match());
        assert_eq!(
            comparison
                .differences
                .iter()
                .map(|difference| difference.section.as_str())
                .collect::<Vec<_>>(),
            ["a.d.ts", "b.js", "c.js"]
        );
        assert!(matches!(
            comparison.differences[0].kind,
            OutputDifferenceKind::Content { .. }
        ));
        assert!(matches!(
            comparison.differences[1].kind,
            OutputDifferenceKind::Missing { .. }
        ));
        assert!(matches!(
            comparison.differences[2].kind,
            OutputDifferenceKind::Unexpected { .. }
        ));
    }

    #[test]
    fn runs_a_case_against_an_emit_baseline() {
        let case = Case::parse(
            "simple.ts",
            "// @target: esnext\n// @noLib: true\nconst value: number = 1;\n",
        )
        .unwrap();
        let runs =
            run_case_against_baseline(&case, "//// [simple.js] ////\nconst value = 1;\n").unwrap();
        assert_eq!(runs.len(), 1);
        assert!(runs[0].comparison.is_match());
    }
}
