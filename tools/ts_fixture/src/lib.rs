//! Parsing for TypeScript's directive-based compiler test fixtures.
//!
//! A fixture can describe one source file directly, or several virtual files
//! separated by `// @filename: path` directives. Other directives are retained
//! as name/value metadata for the compiler harness.

use std::{
    collections::{BTreeMap, BTreeSet},
    fmt, fs,
    io::{self, Write},
    ops::Range,
    path::{Path, PathBuf},
};

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

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct RunnerOptions {
    pub filter: Option<String>,
    pub skip: usize,
    pub limit: Option<usize>,
}

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct RunnerSummary {
    pub matched: usize,
    pub mismatched: usize,
    pub missing: usize,
    pub content_differences: usize,
    pub missing_sections: usize,
    pub unexpected_sections: usize,
    pub diagnostic_failures: usize,
}

impl RunnerSummary {
    #[must_use]
    pub const fn is_success(self) -> bool {
        self.mismatched == 0 && self.missing == 0
    }
}

/// Discovers upstream cases/reference baselines and runs emitted-output comparisons.
///
/// # Errors
///
/// Returns an error when a case, baseline, or fixture compilation cannot be read.
pub fn run_upstream_baselines(
    repository: &Path,
    options: &RunnerOptions,
    writer: &mut impl Write,
) -> io::Result<RunnerSummary> {
    let layouts = upstream_layouts(repository);
    if layouts.is_empty() {
        return Err(io::Error::new(
            io::ErrorKind::NotFound,
            format!(
                "no TypeScript cases/reference baseline layout below {}",
                repository.display()
            ),
        ));
    }
    let mut cases = Vec::new();
    let mut baseline_sets = Vec::new();
    for (case_root, baseline_root) in &layouts {
        let baselines = collect_files(baseline_root, is_emit_baseline_file)?;
        let baseline_index = baseline_sets.len();
        baseline_sets.push(index_baselines(baselines));
        for case_path in collect_files(case_root, is_case_file)? {
            cases.push((case_path, baseline_index));
        }
    }
    cases.sort_by(|left, right| left.0.cmp(&right.0));
    cases.dedup_by(|left, right| left.0 == right.0);
    let filter = options.filter.as_deref().map(str::to_ascii_lowercase);
    let cases = cases
        .into_iter()
        .filter(|(path, _)| {
            filter
                .as_ref()
                .is_none_or(|filter| path.to_string_lossy().to_ascii_lowercase().contains(filter))
        })
        .skip(options.skip)
        .take(options.limit.unwrap_or(usize::MAX));

    let mut summary = RunnerSummary::default();
    for (case_path, baseline_index) in cases {
        let baseline_files = &baseline_sets[baseline_index];
        let source = fs::read(&case_path)?;
        let case = Case::parse(&case_path, source)
            .map_err(|error| io::Error::new(io::ErrorKind::InvalidData, error))?;
        let axes = matrix_axes(&case);
        let case_name = case_path
            .file_stem()
            .and_then(|name| name.to_str())
            .unwrap_or_default();
        let candidates = baseline_files
            .get(case_name)
            .map_or_else(Vec::new, |paths| paths.iter().collect::<Vec<_>>());
        for (variant, compilation) in compile_case_matrix(&case)? {
            let selected = select_variant_baselines(&candidates, case_name, &variant, &axes);
            let display_path = case_path
                .strip_prefix(repository)
                .unwrap_or(&case_path)
                .display();
            let label = variant_label(&variant, &axes);
            if selected.is_empty() {
                if compilation
                    .outputs
                    .keys()
                    .any(|name| is_emitted_section(name))
                {
                    summary.missing += 1;
                    writeln!(writer, "MISSING {display_path}{label}")?;
                } else {
                    summary.matched += 1;
                }
                continue;
            }
            let baseline = read_baseline_files(&selected)?;
            let comparison = compare_case_emitted_output_sections(
                &compilation.outputs,
                &baseline,
                &case,
                &variant,
            );
            if comparison.is_match() {
                summary.matched += 1;
            } else {
                summary.mismatched += 1;
                let description = record_mismatch(&mut summary, &comparison, &compilation);
                writeln!(writer, "MISMATCH {display_path}{label}: {description}")?;
            }
        }
    }
    writeln!(
        writer,
        "summary: matched={} mismatched={} missing={} content={} missing_sections={} unexpected_sections={} diagnostics={}",
        summary.matched,
        summary.mismatched,
        summary.missing,
        summary.content_differences,
        summary.missing_sections,
        summary.unexpected_sections,
        summary.diagnostic_failures,
    )?;
    Ok(summary)
}

fn read_baseline_files(paths: &[&PathBuf]) -> io::Result<String> {
    let mut baseline = String::new();
    for path in paths {
        let text = fs::read_to_string(path)?;
        if !baseline.is_empty() && !baseline.ends_with('\n') {
            baseline.push('\n');
        }
        baseline.push_str(&text);
    }
    Ok(baseline)
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
    compare_emitted_output_sections_excluding(outputs, baseline, &BTreeSet::new())
}

fn compare_case_emitted_output_sections(
    outputs: &BTreeMap<String, String>,
    baseline: &str,
    case: &Case,
    variant: &OptionVariant,
) -> BaselineComparison {
    let mut excluded_expected = case
        .units
        .iter()
        .filter_map(|unit| {
            let path = unit.path.to_string_lossy().replace('\\', "/");
            ts_path::is_declaration_file(&path).then(|| normalize_section_name(&path))
        })
        .collect::<BTreeSet<_>>();
    let emit_declaration_only = variant.values.iter().any(|(name, value)| {
        name.eq_ignore_ascii_case("emitDeclarationOnly") && value.eq_ignore_ascii_case("true")
    });
    if emit_declaration_only {
        excluded_expected.extend(
            parse_baseline_sections(baseline)
                .into_keys()
                .map(|name| normalize_section_name(&name))
                .filter(|name| is_javascript_output_section(name)),
        );
    }
    compare_emitted_output_sections_excluding(outputs, baseline, &excluded_expected)
}

fn compare_emitted_output_sections_excluding(
    outputs: &BTreeMap<String, String>,
    baseline: &str,
    excluded_expected: &BTreeSet<String>,
) -> BaselineComparison {
    let expected = parse_baseline_sections(baseline)
        .into_iter()
        .filter(|(name, _)| is_emitted_section(name))
        .map(|(name, text)| {
            (
                normalize_section_name(&name),
                normalize_emitted_section(&text),
            )
        })
        .filter(|(name, _)| !excluded_expected.contains(name))
        .collect::<BTreeMap<_, _>>();
    let actual_sections = outputs
        .iter()
        .filter(|(name, _)| is_emitted_section(name))
        .map(|(name, text)| {
            (
                normalize_section_name(name),
                normalize_emitted_section(text),
            )
        })
        .collect::<Vec<_>>();
    let basename_counts =
        actual_sections
            .iter()
            .fold(BTreeMap::<String, usize>::new(), |mut counts, (name, _)| {
                *counts.entry(section_basename(name).to_owned()).or_default() += 1;
                counts
            });
    let actual = actual_sections
        .into_iter()
        .map(|(name, text)| {
            let basename = section_basename(&name);
            let name = if !expected.contains_key(&name)
                && expected.contains_key(basename)
                && basename_counts.get(basename) == Some(&1)
            {
                basename.to_owned()
            } else {
                name
            };
            (name, text)
        })
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
            let comparison = compare_case_emitted_output_sections(
                &compilation.outputs,
                baseline,
                case,
                &variant,
            );
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
        if is_compilation_unit(&path) {
            roots.push(path);
        }
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
    let diagnostics = emit
        .diagnostics
        .iter()
        .chain(program.diagnostics())
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
    if unit.path == case.path {
        let base = unit
            .path
            .file_name()
            .and_then(|name| name.to_str())
            .map_or_else(|| format!("unit{index}.ts"), str::to_owned);
        return ts_path::resolve_path("/case", &[&base]);
    }
    if path.starts_with('/') {
        return ts_path::normalize_path(&path);
    }
    ts_path::resolve_path("/case", &[&path])
}

fn is_compilation_unit(path: &str) -> bool {
    let path = path.to_ascii_lowercase();
    [".ts", ".tsx", ".mts", ".cts", ".js", ".jsx", ".mjs", ".cjs"]
        .iter()
        .any(|extension| path.ends_with(extension))
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
    "alwaysStrict",
    "allowJs",
    "allowSyntheticDefaultImports",
    "baseUrl",
    "checkJs",
    "composite",
    "declaration",
    "declarationMap",
    "declarationDir",
    "emitDeclarationOnly",
    "esModuleInterop",
    "exactOptionalPropertyTypes",
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
    "noEmitOnError",
    "noImplicitAny",
    "noLib",
    "noUnusedLocals",
    "noUnusedParameters",
    "outFile",
    "outDir",
    "preserveConstEnums",
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

fn upstream_layouts(repository: &Path) -> Vec<(PathBuf, PathBuf)> {
    let candidates = [
        ("testdata/tests/cases", "testdata/tests/baselines/reference"),
        (
            "_submodules/TypeScript/tests/cases",
            "_submodules/TypeScript/tests/baselines/reference",
        ),
        ("tests/cases", "tests/baselines/reference"),
    ];
    candidates
        .into_iter()
        .map(|(cases, baselines)| (repository.join(cases), repository.join(baselines)))
        .find(|(cases, baselines)| cases.is_dir() && baselines.is_dir())
        .into_iter()
        .collect()
}

fn collect_files(root: &Path, include: fn(&Path) -> bool) -> io::Result<Vec<PathBuf>> {
    let mut files = Vec::new();
    if !root.is_dir() {
        return Ok(files);
    }
    let mut pending = vec![root.to_owned()];
    while let Some(directory) = pending.pop() {
        let mut entries = fs::read_dir(directory)?.collect::<Result<Vec<_>, _>>()?;
        entries.sort_by_key(std::fs::DirEntry::path);
        for entry in entries.into_iter().rev() {
            let path = entry.path();
            if path.is_dir() {
                pending.push(path);
            } else if include(&path) {
                files.push(path);
            }
        }
    }
    files.sort();
    Ok(files)
}

fn is_case_file(path: &Path) -> bool {
    matches!(
        path.extension().and_then(|extension| extension.to_str()),
        Some("ts" | "tsx" | "js" | "jsx")
    )
}

fn is_emit_baseline_file(path: &Path) -> bool {
    path.file_name()
        .and_then(|name| name.to_str())
        .is_some_and(is_emitted_section)
}

fn index_baselines(paths: Vec<PathBuf>) -> BTreeMap<String, Vec<PathBuf>> {
    let mut index = BTreeMap::<String, Vec<PathBuf>>::new();
    for path in paths {
        let Some(base) = path
            .file_name()
            .and_then(|name| name.to_str())
            .and_then(emitted_baseline_base)
        else {
            continue;
        };
        let case_name = base.split_once('(').map_or(base, |(name, _)| name);
        index.entry(case_name.to_owned()).or_default().push(path);
    }
    index
}

fn emitted_baseline_base(file_name: &str) -> Option<&str> {
    [".d.mts", ".d.cts", ".d.ts", ".jsx", ".mjs", ".cjs", ".js"]
        .into_iter()
        .find_map(|extension| file_name.strip_suffix(extension))
}

fn matrix_axes(case: &Case) -> Vec<String> {
    SCALAR_OPTION_NAMES
        .iter()
        .filter_map(|name| {
            case.directive_values(name)
                .next()
                .filter(|value| {
                    value
                        .split(',')
                        .filter(|part| !part.trim().is_empty())
                        .count()
                        > 1
                })
                .map(|_| (*name).to_owned())
        })
        .collect()
}

fn select_variant_baselines<'a>(
    candidates: &[&'a PathBuf],
    case_name: &str,
    variant: &OptionVariant,
    axes: &[String],
) -> Vec<&'a PathBuf> {
    if axes.is_empty() {
        return candidates.to_vec();
    }
    let tagged = candidates
        .iter()
        .copied()
        .filter(|path| {
            let name = path
                .file_name()
                .and_then(|name| name.to_str())
                .unwrap_or_default()
                .to_ascii_lowercase();
            axes.iter().all(|axis| {
                variant.values.get(axis).is_some_and(|value| {
                    name.contains(&format!(
                        "{}={}",
                        axis.to_ascii_lowercase(),
                        value.to_ascii_lowercase()
                    ))
                })
            })
        })
        .collect::<Vec<_>>();
    if tagged.is_empty() {
        candidates
            .iter()
            .copied()
            .filter(|path| {
                path.file_name()
                    .and_then(|name| name.to_str())
                    .and_then(emitted_baseline_base)
                    == Some(case_name)
            })
            .collect()
    } else {
        tagged
    }
}

fn variant_label(variant: &OptionVariant, axes: &[String]) -> String {
    if axes.is_empty() {
        return String::new();
    }
    let values = axes
        .iter()
        .filter_map(|axis| {
            variant
                .values
                .get(axis)
                .map(|value| format!("{axis}={value}"))
        })
        .collect::<Vec<_>>()
        .join(",");
    format!(" [{values}]")
}

fn describe_difference(difference: &OutputDifference) -> String {
    match &difference.kind {
        OutputDifferenceKind::Missing { .. } => format!("missing section {}", difference.section),
        OutputDifferenceKind::Unexpected { .. } => {
            format!("unexpected section {}", difference.section)
        }
        OutputDifferenceKind::Content { expected, actual } => {
            let (line, expected, actual) = first_different_line(expected, actual);
            format!(
                "section {} differs at line {line}; expected {expected:?}, actual {actual:?}",
                difference.section
            )
        }
    }
}

fn describe_compilation_diagnostic(diagnostic: &CompilationDiagnostic) -> String {
    let code = diagnostic
        .code
        .map_or_else(|| "no code".to_owned(), |code| format!("TS{code}"));
    let file = diagnostic.file_name.as_deref().unwrap_or("<global>");
    format!("diagnostic {code} {file}: {}", diagnostic.message)
}

fn record_mismatch(
    summary: &mut RunnerSummary,
    comparison: &BaselineComparison,
    compilation: &Compilation,
) -> String {
    let has_missing_section = comparison
        .differences
        .iter()
        .any(|difference| matches!(&difference.kind, OutputDifferenceKind::Missing { .. }));
    let diagnostic = has_missing_section
        .then(|| compilation.diagnostics.first())
        .flatten();
    if diagnostic.is_some() {
        summary.diagnostic_failures += 1;
    }
    for difference in &comparison.differences {
        match &difference.kind {
            OutputDifferenceKind::Content { .. } => summary.content_differences += 1,
            OutputDifferenceKind::Missing { .. } if diagnostic.is_none() => {
                summary.missing_sections += 1;
            }
            OutputDifferenceKind::Unexpected { .. } => summary.unexpected_sections += 1,
            OutputDifferenceKind::Missing { .. } => {}
        }
    }
    diagnostic.map_or_else(
        || describe_difference(&comparison.differences[0]),
        describe_compilation_diagnostic,
    )
}

fn first_different_line<'a>(expected: &'a str, actual: &'a str) -> (usize, &'a str, &'a str) {
    let mut expected_lines = expected.split('\n');
    let mut actual_lines = actual.split('\n');
    let mut line = 1;
    loop {
        match (expected_lines.next(), actual_lines.next()) {
            (Some(expected), Some(actual)) if expected == actual => line += 1,
            (Some(expected), Some(actual)) => return (line, expected, actual),
            (Some(expected), None) => return (line, expected, "<end of file>"),
            (None, Some(actual)) => return (line, "<end of file>", actual),
            (None, None) => return (line, "<no differing line>", "<no differing line>"),
        }
    }
}

fn is_emitted_section(name: &str) -> bool {
    let name = name.to_ascii_lowercase();
    [".js", ".jsx", ".mjs", ".cjs", ".d.ts", ".d.mts", ".d.cts"]
        .iter()
        .any(|extension| name.ends_with(extension))
}

fn is_javascript_output_section(name: &str) -> bool {
    let name = name.to_ascii_lowercase();
    [".js", ".jsx", ".mjs", ".cjs"]
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

fn section_basename(name: &str) -> &str {
    name.rsplit('/').next().unwrap_or(name)
}

fn normalize_newlines(text: &str) -> String {
    text.replace("\r\n", "\n").replace('\r', "\n")
}

fn normalize_emitted_section(text: &str) -> String {
    let mut normalized = normalize_newlines(text);
    while normalized.ends_with('\n') {
        normalized.pop();
    }
    if !normalized.is_empty() {
        normalized.push('\n');
    }
    normalized
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
    let comment = line
        .trim_start_matches('\u{feff}')
        .trim_start()
        .strip_prefix("//")?
        .trim_start();
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
        Case, OptionVariant, OutputDifferenceKind, ParseError,
        compare_case_emitted_output_sections, compare_emitted_output_sections, compile_case,
        compile_case_matrix, expand_option_matrix, first_different_line, parse_baseline_sections,
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
    fn parses_a_directive_after_a_utf8_bom() {
        let case = Case::parse("bom.ts", "\u{feff}// @target: es2015\nconst value = 1;").unwrap();
        assert_eq!(
            case.directive_values("target").collect::<Vec<_>>(),
            ["es2015"]
        );
        assert_eq!(
            case.units[0].source_text.as_scannable_str(),
            "const value = 1;"
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
    fn moduleless_fixtures_preserve_exports_and_commonjs_remains_explicit() {
        let preserved = Case::parse(
            "preserved.ts",
            "// @target: es2015\n// @noLib: true\nexport const value: number = 1;\n",
        )
        .unwrap();
        let preserved = compile_case(&preserved).unwrap();
        let javascript = &preserved.outputs["/case/preserved.js"];
        assert!(
            javascript.contains("export const value = 1;"),
            "{javascript}"
        );
        assert!(!javascript.contains("exports.value"), "{javascript}");

        let commonjs = Case::parse(
            "commonjs.ts",
            concat!(
                "// @target: es2015\n",
                "// @module: commonjs\n",
                "// @noLib: true\n",
                "export const value: number = 1;\n",
            ),
        )
        .unwrap();
        let commonjs = compile_case(&commonjs).unwrap();
        let javascript = &commonjs.outputs["/case/commonjs.js"];
        assert!(
            javascript.contains("exports.value = value;"),
            "{javascript}"
        );
        assert!(!javascript.contains("export const value"), "{javascript}");
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
    fn compiles_out_file_directives_to_one_output() {
        let case = Case::parse(
            "bundle.ts",
            concat!(
                "// @module: amd\n",
                "// @target: es2015\n",
                "// @outFile: out.js\n",
                "// @noLib: true\n",
                "// @filename: first.ts\n",
                "const first = 1;\n",
                "// @filename: types.d.ts\n",
                "declare const ambient: string;\n",
                "// @filename: second.ts\n",
                "const second = 2;\n",
            ),
        )
        .unwrap();
        let compilation = compile_case(&case).unwrap();
        assert!(
            compilation.diagnostics.is_empty(),
            "{:?}",
            compilation.diagnostics
        );
        assert_eq!(compilation.outputs.len(), 1);
        assert_eq!(
            compilation.outputs["/case/out.js"],
            "\"use strict\";\nconst first = 1;\nconst second = 2;\n"
        );
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
    fn applies_exact_optional_property_types_directives() {
        let case = Case::parse(
            "exactOptionalPropertyTypesArgumentError.ts",
            concat!(
                "// @strictNullChecks: true\n",
                "// @exactOptionalPropertyTypes: true\n",
                "// @noEmit: true\n",
                "declare function f(o: { y?: string }): void;\n",
                "f({ y: undefined });\n",
            ),
        )
        .unwrap();
        let variants = expand_option_matrix(&case);
        assert_eq!(variants.len(), 1);
        assert_eq!(variants[0].values["exactOptionalPropertyTypes"], "true");
        let compilation = compile_case(&case).unwrap();
        assert_eq!(
            compilation
                .diagnostics
                .iter()
                .filter_map(|diagnostic| diagnostic.code)
                .collect::<Vec<_>>(),
            [2379]
        );
    }

    #[test]
    fn applies_base_url_to_non_relative_virtual_module_imports() {
        let case = Case::parse(
            "baseUrl.ts",
            concat!(
                "// @baseUrl: /proj\n",
                "// @filename: /proj/defs/cc.ts\n",
                "export const enum CharCode { A }\n",
                "// @filename: /proj/component/file.ts\n",
                "import { CharCode } from 'defs/cc';\n",
                "export const value = CharCode.A;\n",
            ),
        )
        .unwrap();
        let variants = expand_option_matrix(&case);
        assert_eq!(variants[0].values["baseUrl"], "/proj");
        let compilation = compile_case(&case).unwrap();
        assert!(
            compilation
                .diagnostics
                .iter()
                .all(|diagnostic| diagnostic.code != Some(2307)),
            "{:?}",
            compilation.diagnostics
        );
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
    fn compares_emitted_sections_independent_of_line_endings() {
        let outputs = BTreeMap::from([(
            "/case/input.js".into(),
            "const value = 1;\nconsole.log(value);\n".into(),
        )]);
        let baseline = concat!(
            "//// [input.js] ////\r\n",
            "const value = 1;\r\n",
            "console.log(value);\r\n",
        );
        assert!(compare_emitted_output_sections(&outputs, baseline).is_match());
    }

    #[test]
    fn ignores_baseline_separator_blank_lines_between_emitted_sections() {
        let outputs = BTreeMap::from([
            ("/case/input.js".into(), "const value = 1;\n".into()),
            (
                "/case/input.d.ts".into(),
                "declare const value = 1;\n".into(),
            ),
        ]);
        let baseline = concat!(
            "//// [input.js] ////\n",
            "const value = 1;\n",
            "\n",
            "//// [input.d.ts] ////\n",
            "declare const value = 1;\n",
        );
        assert!(compare_emitted_output_sections(&outputs, baseline).is_match());
    }

    #[test]
    fn matches_unique_baseline_basenames_for_absolute_virtual_outputs() {
        let outputs = BTreeMap::from([(
            "/proj/defs/cc.js".into(),
            "export const value = 1;\n".into(),
        )]);
        let baseline = "//// [cc.js] ////\nexport const value = 1;\n";
        assert!(compare_emitted_output_sections(&outputs, baseline).is_match());
    }

    #[test]
    fn declaration_only_variants_do_not_expect_javascript_sections() {
        let case = Case::parse(
            "declarationOnly.ts",
            "// @emitDeclarationOnly: true\nexport const value = 1;\n",
        )
        .unwrap();
        let outputs = BTreeMap::from([(
            "/case/declarationOnly.d.ts".into(),
            "export declare const value = 1;\n".into(),
        )]);
        let baseline = concat!(
            "//// [declarationOnly.js] ////\n",
            "export const value = 1;\n",
            "//// [declarationOnly.d.ts] ////\n",
            "export declare const value = 1;\n",
        );
        let declaration_only = OptionVariant {
            values: BTreeMap::from([("emitDeclarationOnly".into(), "true".into())]),
        };
        assert!(
            compare_case_emitted_output_sections(&outputs, baseline, &case, &declaration_only,)
                .is_match()
        );

        assert!(
            !compare_case_emitted_output_sections(
                &outputs,
                baseline,
                &case,
                &OptionVariant::default(),
            )
            .is_match()
        );
    }

    #[test]
    fn reports_end_of_file_differences_explicitly() {
        assert_eq!(
            first_different_line("first\nsecond", "first"),
            (2, "second", "<end of file>")
        );
        assert_eq!(
            first_different_line("first", "first\nsecond"),
            (2, "<end of file>", "second")
        );
    }

    #[test]
    fn runs_a_case_against_an_emit_baseline() {
        let case = Case::parse(
            "simple.ts",
            "// @target: esnext\n// @noLib: true\nconst value: number = 1;\n",
        )
        .unwrap();
        let runs = run_case_against_baseline(
            &case,
            "//// [simple.js] ////\n\"use strict\";\nconst value = 1;\n",
        )
        .unwrap();
        assert_eq!(runs.len(), 1);
        assert!(runs[0].comparison.is_match());
    }
}
