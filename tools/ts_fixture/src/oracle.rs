use std::{
    collections::BTreeMap,
    fmt, fs,
    io::{self, Write},
    path::{Path, PathBuf},
};

/// Source of an upstream compiler fixture suite.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum UpstreamOrigin {
    /// Fixtures owned by the typescript-go repository.
    Go,
    /// Fixtures inherited from the pinned TypeScript submodule.
    TypeScriptSubmodule,
}

impl UpstreamOrigin {
    const fn as_str(self) -> &'static str {
        match self {
            Self::Go => "go",
            Self::TypeScriptSubmodule => "submodule",
        }
    }
}

/// Compiler fixture suite recognized by the typescript-go compiler runner.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum UpstreamSuite {
    Compiler,
    Conformance,
}

impl UpstreamSuite {
    const fn as_str(self) -> &'static str {
        match self {
            Self::Compiler => "compiler",
            Self::Conformance => "conformance",
        }
    }
}

/// Whether typescript-go executes a discovered case.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum UpstreamCaseDisposition {
    Runnable,
    SkippedByUpstream,
}

impl UpstreamCaseDisposition {
    const fn as_str(self) -> &'static str {
        match self {
            Self::Runnable => "runnable",
            Self::SkippedByUpstream => "upstream-skip",
        }
    }
}

/// One compiler/conformance fixture in deterministic upstream order.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct UpstreamCaseManifest {
    pub path: PathBuf,
    pub relative_path: PathBuf,
    pub disposition: UpstreamCaseDisposition,
}

/// Counts of semantic and emit oracle artifacts in one suite.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct OracleArtifactCounts {
    pub errors: usize,
    pub types: usize,
    pub symbols: usize,
    pub emit: usize,
}

impl OracleArtifactCounts {
    fn add_assign(&mut self, other: Self) {
        self.errors += other.errors;
        self.types += other.types;
        self.symbols += other.symbols;
        self.emit += other.emit;
    }
}

/// One exact corpus/oracle layout consumed by typescript-go's compiler runner.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct UpstreamSuiteManifest {
    pub origin: UpstreamOrigin,
    pub suite: UpstreamSuite,
    pub case_root: PathBuf,
    pub case_root_relative: PathBuf,
    pub oracle_root: PathBuf,
    pub oracle_root_relative: PathBuf,
    pub cases: Vec<UpstreamCaseManifest>,
    pub artifacts: OracleArtifactCounts,
}

impl UpstreamSuiteManifest {
    #[must_use]
    pub fn runnable_case_count(&self) -> usize {
        self.cases
            .iter()
            .filter(|case| case.disposition == UpstreamCaseDisposition::Runnable)
            .count()
    }

    #[must_use]
    pub fn skipped_case_count(&self) -> usize {
        self.cases.len() - self.runnable_case_count()
    }
}

/// Deterministic inventory of the four suites used as the typescript-go oracle.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct UpstreamManifest {
    pub suites: Vec<UpstreamSuiteManifest>,
}

impl UpstreamManifest {
    #[must_use]
    pub fn summary(&self) -> UpstreamManifestSummary {
        let mut summary = UpstreamManifestSummary {
            suites: self.suites.len(),
            ..UpstreamManifestSummary::default()
        };
        for suite in &self.suites {
            summary.discovered_cases += suite.cases.len();
            summary.runnable_cases += suite.runnable_case_count();
            summary.upstream_skipped_cases += suite.skipped_case_count();
            summary.artifacts.add_assign(suite.artifacts);
        }
        summary
    }

    /// Writes a stable, tab-delimited inventory suitable for diffing and sharding.
    ///
    /// # Errors
    ///
    /// Returns an error when the destination writer cannot accept the manifest.
    pub fn write_to(&self, writer: &mut impl Write) -> io::Result<()> {
        writeln!(writer, "oracle-manifest\t1")?;
        for suite in &self.suites {
            writeln!(
                writer,
                "suite\t{}\t{}\tcases={}\trunnable={}\tupstream_skipped={}\terrors={}\ttypes={}\tsymbols={}\temit={}\tcase_root={}\toracle_root={}",
                suite.origin.as_str(),
                suite.suite.as_str(),
                suite.cases.len(),
                suite.runnable_case_count(),
                suite.skipped_case_count(),
                suite.artifacts.errors,
                suite.artifacts.types,
                suite.artifacts.symbols,
                suite.artifacts.emit,
                manifest_path(&suite.case_root_relative),
                manifest_path(&suite.oracle_root_relative),
            )?;
            for case in &suite.cases {
                writeln!(
                    writer,
                    "case\t{}\t{}\t{}\t{}",
                    suite.origin.as_str(),
                    suite.suite.as_str(),
                    case.disposition.as_str(),
                    manifest_path(&case.relative_path),
                )?;
            }
        }
        writeln!(writer, "{}", self.summary())
    }
}

/// Stable aggregate for an [`UpstreamManifest`].
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct UpstreamManifestSummary {
    pub suites: usize,
    pub discovered_cases: usize,
    pub runnable_cases: usize,
    pub upstream_skipped_cases: usize,
    pub artifacts: OracleArtifactCounts,
}

impl fmt::Display for UpstreamManifestSummary {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            formatter,
            "manifest-summary: suites={} discovered_cases={} runnable_cases={} upstream_skipped_cases={} errors={} types={} symbols={} emit={}",
            self.suites,
            self.discovered_cases,
            self.runnable_cases,
            self.upstream_skipped_cases,
            self.artifacts.errors,
            self.artifacts.types,
            self.artifacts.symbols,
            self.artifacts.emit,
        )
    }
}

#[derive(Clone, Copy)]
struct LayoutSpec {
    origin: UpstreamOrigin,
    suite: UpstreamSuite,
    case_root: &'static str,
    oracle_root: &'static str,
}

const LAYOUTS: [LayoutSpec; 4] = [
    LayoutSpec {
        origin: UpstreamOrigin::Go,
        suite: UpstreamSuite::Compiler,
        case_root: "testdata/tests/cases/compiler",
        oracle_root: "testdata/baselines/reference/compiler",
    },
    LayoutSpec {
        origin: UpstreamOrigin::Go,
        suite: UpstreamSuite::Conformance,
        case_root: "testdata/tests/cases/conformance",
        oracle_root: "testdata/baselines/reference/conformance",
    },
    LayoutSpec {
        origin: UpstreamOrigin::TypeScriptSubmodule,
        suite: UpstreamSuite::Compiler,
        case_root: "_submodules/TypeScript/tests/cases/compiler",
        oracle_root: "testdata/baselines/reference/submodule/compiler",
    },
    LayoutSpec {
        origin: UpstreamOrigin::TypeScriptSubmodule,
        suite: UpstreamSuite::Conformance,
        case_root: "_submodules/TypeScript/tests/cases/conformance",
        oracle_root: "testdata/baselines/reference/submodule/conformance",
    },
];

/// Discovers the exact local and submodule compiler/conformance layouts used by
/// the pinned typescript-go compiler runner.
///
/// This deliberately fails when any of the four corpus or actual-oracle roots
/// is absent. An explicit parity run must not silently shrink to whichever
/// directories happen to be available.
///
/// # Errors
///
/// Returns an error for a missing suite root, unreadable directory, or duplicate
/// fixture basename within one upstream origin.
pub fn discover_upstream_manifest(repository: &Path) -> io::Result<UpstreamManifest> {
    let mut missing = Vec::new();
    for layout in LAYOUTS {
        let case_root = repository.join(layout.case_root);
        let oracle_root = repository.join(layout.oracle_root);
        if !case_root.is_dir() {
            missing.push(format!("corpus {}", case_root.display()));
        }
        if !oracle_root.is_dir() {
            missing.push(format!("oracle {}", oracle_root.display()));
        }
    }
    if !missing.is_empty() {
        return Err(io::Error::new(
            io::ErrorKind::NotFound,
            format!(
                "incomplete typescript-go compiler oracle below {}: missing {}",
                repository.display(),
                missing.join(", ")
            ),
        ));
    }

    let mut suites = Vec::with_capacity(LAYOUTS.len());
    for layout in LAYOUTS {
        let case_root_relative = PathBuf::from(layout.case_root);
        let oracle_root_relative = PathBuf::from(layout.oracle_root);
        let case_root = repository.join(&case_root_relative);
        let oracle_root = repository.join(&oracle_root_relative);
        let cases = collect_files(&case_root, is_go_compiler_case)?
            .into_iter()
            .map(|path| -> io::Result<_> {
                let relative_path = path
                    .strip_prefix(&case_root)
                    .map(|relative| case_root_relative.join(relative))
                    .map_err(|error| {
                        io::Error::new(
                            io::ErrorKind::InvalidData,
                            format!(
                                "case {} escaped corpus root {}: {error}",
                                path.display(),
                                case_root.display()
                            ),
                        )
                    })?;
                let disposition = if is_upstream_skipped(&path) {
                    UpstreamCaseDisposition::SkippedByUpstream
                } else {
                    UpstreamCaseDisposition::Runnable
                };
                Ok(UpstreamCaseManifest {
                    path,
                    relative_path,
                    disposition,
                })
            })
            .collect::<io::Result<Vec<_>>>()?;
        let artifacts = count_artifacts(&collect_files(&oracle_root, |_| true)?);
        suites.push(UpstreamSuiteManifest {
            origin: layout.origin,
            suite: layout.suite,
            case_root,
            case_root_relative,
            oracle_root,
            oracle_root_relative,
            cases,
            artifacts,
        });
    }
    reject_duplicate_basenames(&suites)?;
    Ok(UpstreamManifest { suites })
}

fn reject_duplicate_basenames(suites: &[UpstreamSuiteManifest]) -> io::Result<()> {
    for origin in [UpstreamOrigin::Go, UpstreamOrigin::TypeScriptSubmodule] {
        let mut seen = BTreeMap::<String, &Path>::new();
        for case in suites
            .iter()
            .filter(|suite| suite.origin == origin)
            .flat_map(|suite| &suite.cases)
        {
            let basename = case
                .path
                .file_name()
                .and_then(|name| name.to_str())
                .unwrap_or_default()
                .to_owned();
            if let Some(previous) = seen.insert(basename.clone(), &case.path) {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidData,
                    format!(
                        "duplicate {origin:?} compiler fixture basename {basename:?}: {} and {}",
                        previous.display(),
                        case.path.display()
                    ),
                ));
            }
        }
    }
    Ok(())
}

fn collect_files(root: &Path, include: impl Fn(&Path) -> bool + Copy) -> io::Result<Vec<PathBuf>> {
    let mut files = Vec::new();
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

fn is_go_compiler_case(path: &Path) -> bool {
    matches!(
        path.extension().and_then(|extension| extension.to_str()),
        Some("ts" | "tsx")
    )
}

fn count_artifacts(paths: &[PathBuf]) -> OracleArtifactCounts {
    let mut counts = OracleArtifactCounts::default();
    for path in paths {
        let name = path
            .file_name()
            .and_then(|name| name.to_str())
            .unwrap_or_default()
            .to_ascii_lowercase();
        if has_suffix(&name, ".errors.txt") {
            counts.errors += 1;
        } else if has_suffix(&name, ".types") {
            counts.types += 1;
        } else if has_suffix(&name, ".symbols") {
            counts.symbols += 1;
        } else if [".js", ".jsx", ".mjs", ".cjs", ".d.ts", ".d.mts", ".d.cts"]
            .iter()
            .any(|extension| has_suffix(&name, extension))
        {
            counts.emit += 1;
        }
    }
    counts
}

fn has_suffix(name: &str, suffix: &str) -> bool {
    name.ends_with(suffix)
}

fn manifest_path(path: &Path) -> String {
    path.components()
        .map(|component| escape_field(&component.as_os_str().to_string_lossy()))
        .collect::<Vec<_>>()
        .join("/")
}

fn escape_field(field: &str) -> String {
    field
        .replace('\\', "\\\\")
        .replace('\t', "\\t")
        .replace('\r', "\\r")
        .replace('\n', "\\n")
}

fn is_upstream_skipped(path: &Path) -> bool {
    let basename = path
        .file_name()
        .and_then(|name| name.to_str())
        .unwrap_or_default();
    SKIPPED_TESTS.contains(&basename)
}

// Pinned from internal/testrunner/compiler_runner.go at the UPSTREAM.md commit.
const SKIPPED_TESTS: [&str; 45] = [
    "APILibCheck.ts",
    "APISample_Watch.ts",
    "APISample_WatchWithDefaults.ts",
    "APISample_WatchWithOwnWatchHost.ts",
    "APISample_compile.ts",
    "APISample_jsdoc.ts",
    "APISample_linter.ts",
    "APISample_parseConfig.ts",
    "APISample_transform.ts",
    "APISample_watcher.ts",
    "preserveUnusedImports.ts",
    "noCrashWithVerbatimModuleSyntaxAndImportsNotUsedAsValues.ts",
    "verbatimModuleSyntaxCompat.ts",
    "verbatimModuleSyntaxCompat2.ts",
    "verbatimModuleSyntaxCompat3.ts",
    "verbatimModuleSyntaxCompat4.ts",
    "preserveValueImports.ts",
    "preserveValueImports_importsNotUsedAsValues.ts",
    "preserveValueImports_errors.ts",
    "preserveValueImports_mixedImports.ts",
    "preserveValueImports_module.ts",
    "importsNotUsedAsValues_error.ts",
    "alwaysStrictNoImplicitUseStrict.ts",
    "nonPrimitiveIndexingWithForInSupressError.ts",
    "parameterInitializerBeforeDestructuringEmit.ts",
    "mappedTypeUnionConstraintInferences.ts",
    "lateBoundConstraintTypeChecksCorrectly.ts",
    "keyofDoesntContainSymbols.ts",
    "isolatedModulesOut.ts",
    "noStrictGenericChecks.ts",
    "noImplicitUseStrict_umd.ts",
    "noImplicitUseStrict_system.ts",
    "noImplicitUseStrict_es6.ts",
    "noImplicitUseStrict_commonjs.ts",
    "noImplicitUseStrict_amd.ts",
    "noImplicitAnyIndexingSuppressed.ts",
    "excessPropertyErrorsSuppressed.ts",
    "moduleNoneDynamicImport.ts",
    "moduleNoneErrors.ts",
    "moduleNoneOutFile.ts",
    "noErrorUsingImportExportModuleAugmentationInDeclarationFile1.ts",
    "noErrorUsingImportExportModuleAugmentationInDeclarationFile2.ts",
    "noErrorUsingImportExportModuleAugmentationInDeclarationFile3.ts",
    "requireOfJsonFileWithModuleEmitNone.ts",
    "requireOfJsonFileWithModuleNodeResolutionEmitNone.ts",
];
