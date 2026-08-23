//! Parsing for TypeScript's directive-based compiler test fixtures.
//!
//! A fixture can describe one source file directly, or several virtual files
//! separated by `// @filename: path` directives. Other directives are retained
//! as name/value metadata for the compiler harness.

use std::{
    cmp::Ordering,
    collections::{BTreeMap, BTreeSet},
    fmt::{self, Write as _},
    fs,
    io::{self, Write},
    ops::Range,
    path::{Path, PathBuf},
    process::Command,
    sync::Arc,
};

use serde::{Deserialize, Deserializer, Serialize};
use ts_core::{SourceText, TextRange};
use ts_vfs::{FileSystem, MemoryFileSystem, decode_utf16_bom};
use xxhash_rust::xxh3::xxh3_128;

mod artifacts;
mod oracle;

use artifacts::{GeneratedSemanticArtifacts, SemanticArtifactKind};

pub use oracle::{
    OracleArtifactCounts, UpstreamCaseDisposition, UpstreamCaseManifest, UpstreamManifest,
    UpstreamManifestSummary, UpstreamOrigin, UpstreamSuite, UpstreamSuiteManifest,
    discover_upstream_manifest,
};

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
    /// Returns an error when a `filename` directive has an empty value or when
    /// substantive source precedes the first virtual filename. The latter is a
    /// panic in the pinned compiler harness; representing it as a parse error
    /// keeps the fixture runner fail-closed.
    pub fn parse(
        path: impl Into<PathBuf>,
        source_text: impl Into<SourceText>,
    ) -> Result<Self, ParseError> {
        let path = path.into();
        let source_text = source_text.into();
        let source_text =
            decode_utf16_bom(source_text.as_bytes()).map_or(source_text, SourceText::from);
        let mut directives = Vec::new();
        let mut units = Vec::new();
        let mut current = UnitBuilder::new(path.clone(), 1, false);
        let source_bytes = source_text.as_bytes();
        let mut byte_offset = 0;

        // Go's `lineDelimiter.Split(code, -1)` retains a final empty line,
        // normalizes CRLF to LF when units are rebuilt, and drops empty lines
        // while the current unit is still empty. Reproduce those semantics so
        // diagnostic locations are relative to the same virtual source text.
        for (line_index, raw_line) in source_bytes.split(|byte| *byte == b'\n').enumerate() {
            let line_number = line_index + 1;
            let has_line_ending = byte_offset + raw_line.len() < source_bytes.len();
            let line = if has_line_ending {
                raw_line.strip_suffix(b"\r").unwrap_or(raw_line)
            } else {
                raw_line
            };

            if line_index == 0
                && line
                    .strip_prefix(b"\xef\xbb\xbf")
                    .and_then(|line| std::str::from_utf8(line).ok())
                    .and_then(parse_directive_line)
                    .is_some_and(|(name, _)| is_compiler_option_directive(name))
            {
                byte_offset += raw_line.len() + usize::from(has_line_ending);
                continue;
            }

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

                    if !current.explicit && current.has_substantive_source() {
                        return Err(ParseError::ContentBeforeFirstFile { line: line_number });
                    }
                    if current.explicit {
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
                current.append_line(line);
            }

            byte_offset += raw_line.len() + usize::from(has_line_ending);
        }

        if current.explicit || units.is_empty() {
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
    /// Non-pretty diagnostic header text in the same form as TypeScript error baselines.
    pub diagnostic_text: String,
    pub outputs: BTreeMap<String, String>,
    semantic_artifacts: Option<GeneratedSemanticArtifacts>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CompilationDiagnostic {
    pub file_name: Option<String>,
    /// Source used to translate the diagnostic's UTF-8 byte range to a baseline location.
    pub source_text: Option<SourceText>,
    pub range: Option<TextRange>,
    pub code: Option<u32>,
    pub category: Option<CompilationDiagnosticCategory>,
    pub message: String,
    /// `None` means the checker did not expose whether related information exists.
    pub related_information: Option<Vec<CompilationRelatedInformation>>,
}

/// Related diagnostic detail retained when the checker exposes it.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CompilationRelatedInformation {
    pub file_name: Option<String>,
    pub source_text: Option<SourceText>,
    pub range: Option<TextRange>,
    pub code: Option<u32>,
    pub category: Option<CompilationDiagnosticCategory>,
    pub message: String,
}

/// Diagnostic category retained by the fixture compiler when its source exposes one.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum CompilationDiagnosticCategory {
    Error,
    Warning,
    Suggestion,
    Message,
}

/// One deterministic combination of scalar compiler-option directives.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct OptionVariant {
    pub values: BTreeMap<String, String>,
    /// Configuration details that the Rust compiler cannot faithfully apply.
    /// Such variants execute for visibility but can never count as exact.
    pub unsupported_details: Vec<String>,
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
#[allow(clippy::struct_excessive_bools)] // Keep each independent CLI mode directly addressable.
pub struct RunnerOptions {
    pub filter: Option<String>,
    pub skip: usize,
    pub limit: Option<usize>,
    /// Execute one checked-in diagnostic shard by stable expanded-variant key.
    pub variant_manifest: Option<PathBuf>,
    /// Compare compiler diagnostics with upstream `.errors.txt` baselines instead of emit.
    pub diagnostics: bool,
    /// Check through the experimental canonical diagnostics-only pipeline.
    ///
    /// This mode is intentionally unavailable to emitted-output and manifest
    /// runs. Unsupported canonical boundaries are retained on each option
    /// variant so a corpus run can continue without falling back to legacy.
    pub canonical_checker: bool,
    /// Account for configured `.types` and `.symbols` baselines without a
    /// legacy checker fallback or unsupported semantic matches.
    pub semantic_artifacts: bool,
    /// Print the discovered corpus/oracle manifest without compiling cases.
    pub manifest: bool,
    /// Write a deterministic machine-readable diagnostic scorecard to this path.
    pub scorecard_json: Option<PathBuf>,
    /// Exact process invocation recorded in scorecard provenance.
    ///
    /// Library callers may leave this empty. The CLI always fills it from
    /// [`std::env::args`].
    #[doc(hidden)]
    pub invocation: Vec<String>,
}

/// Fidelity boundary of one diagnostic comparison.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum DiagnosticComparisonScope {
    /// The complete, non-pretty `.errors.txt` artifact was compared byte for byte.
    FullArtifact,
}

/// Whole-checker pipeline used to produce a diagnostic scorecard.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum DiagnosticCheckerMode {
    Legacy,
    Canonical,
}

/// Deterministic outcome category for one diagnostic fixture variant.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum DiagnosticVariantStatus {
    ExactMatch,
    /// The pinned upstream harness skips this option variant before checking.
    UpstreamSkipped,
    /// The normalized headers match, but the complete artifacts do not.
    HeaderOnlyMatch,
    CodeMismatch,
    SpanMismatch,
    MessageMismatch,
    OrderMismatch,
    UnsupportedDetail,
    HeaderMismatch,
    ArtifactMismatch,
    FatalInvariant,
}

/// Structured reason why two complete diagnostic artifacts differ.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum DiagnosticArtifactMismatchKind {
    HeaderOnly,
    Code,
    Span,
    Message,
    Order,
    UnsupportedDetail,
    Header,
    Artifact,
    FatalInvariant,
}

/// High-level reason a scorecard variant did or did not compare exactly.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum DiagnosticVariantOutcomeClass {
    Exact,
    UpstreamSkipped,
    HarnessConfig,
    CheckerCapability,
    SupportedMismatch,
    FatalInvariant,
}

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct DiagnosticScorecardSummary {
    pub discovered_cases: usize,
    pub upstream_skipped_cases: usize,
    pub selected_cases: usize,
    pub executed_variants: usize,
    pub upstream_skipped_variants: usize,
    /// Byte-for-byte full diagnostic artifact matches.
    pub exact_matches: usize,
    pub header_only_matches: usize,
    pub code_mismatches: usize,
    pub span_mismatches: usize,
    pub message_mismatches: usize,
    pub order_mismatches: usize,
    pub unsupported_details: usize,
    pub header_mismatches: usize,
    pub artifact_mismatches: usize,
    pub fatal_invariants: usize,
    pub actual_diagnostics: usize,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct DiagnosticScorecardRange {
    pub start: u32,
    pub length: u32,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct DiagnosticScorecardDiagnostic {
    pub file_name: Option<String>,
    pub range: Option<DiagnosticScorecardRange>,
    pub code: Option<u32>,
    pub category: Option<CompilationDiagnosticCategory>,
    pub message: String,
    /// Related records remain nested beneath their primary and never count as
    /// top-level diagnostics.
    pub related_information: Vec<DiagnosticScorecardDiagnostic>,
}

impl From<&CompilationDiagnostic> for DiagnosticScorecardDiagnostic {
    fn from(diagnostic: &CompilationDiagnostic) -> Self {
        Self {
            file_name: diagnostic.file_name.clone(),
            range: diagnostic.range.map(|range| DiagnosticScorecardRange {
                start: range.start.get(),
                length: range.len(),
            }),
            code: diagnostic.code,
            category: diagnostic.category,
            message: diagnostic.message.clone(),
            related_information: diagnostic
                .related_information
                .as_deref()
                .unwrap_or_default()
                .iter()
                .map(DiagnosticScorecardDiagnostic::from)
                .collect(),
        }
    }
}

impl From<&CompilationRelatedInformation> for DiagnosticScorecardDiagnostic {
    fn from(diagnostic: &CompilationRelatedInformation) -> Self {
        Self {
            file_name: diagnostic.file_name.clone(),
            range: diagnostic.range.map(|range| DiagnosticScorecardRange {
                start: range.start.get(),
                length: range.len(),
            }),
            code: diagnostic.code,
            category: diagnostic.category,
            message: diagnostic.message.clone(),
            related_information: Vec::new(),
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct DiagnosticVariantResult {
    pub variant_key: String,
    pub case: String,
    pub options: BTreeMap<String, String>,
    pub expected_baseline: Option<String>,
    pub comparison_scope: DiagnosticComparisonScope,
    pub status: DiagnosticVariantStatus,
    pub outcome_class: DiagnosticVariantOutcomeClass,
    pub frontier_blocker: Option<DiagnosticFrontierBlocker>,
    pub expected_header: String,
    pub actual_header: String,
    pub mismatch_kinds: Vec<DiagnosticArtifactMismatchKind>,
    pub first_difference: Option<DiagnosticArtifactDifference>,
    pub unsupported_details: Vec<String>,
    pub diagnostics: Vec<DiagnosticScorecardDiagnostic>,
    /// Type and symbol artifact results when semantic accounting was requested.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub semantic_artifacts: Option<SemanticVariantArtifacts>,
}

/// Whether one upstream semantic artifact was proven, skipped, or unavailable.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum SemanticArtifactStatus {
    ExactMatch,
    Mismatch,
    Unsupported,
    NotReached,
    UpstreamSkipped,
}

/// Accounting for one configured upstream `.types` or `.symbols` baseline.
#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct SemanticArtifactResult {
    pub expected_baseline: Option<String>,
    pub status: SemanticArtifactStatus,
    pub visited_nodes: usize,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub unsupported_detail: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub first_difference: Option<DiagnosticArtifactDifference>,
}

/// Per-variant semantic baseline results in stable artifact order.
#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct SemanticVariantArtifacts {
    pub types: SemanticArtifactResult,
    pub symbols: SemanticArtifactResult,
}

/// Explicit denominator and result counts for one semantic artifact kind.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct SemanticArtifactSummary {
    pub expected_baselines: usize,
    pub missing_baselines: usize,
    pub exact_matches: usize,
    pub mismatches: usize,
    pub unsupported: usize,
    pub not_reached: usize,
    pub upstream_skipped: usize,
}

/// Semantic-artifact accounting independent of diagnostic-only scorecards.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct SemanticArtifactScorecard {
    pub types: SemanticArtifactSummary,
    pub symbols: SemanticArtifactSummary,
}

/// The first honest boundary reached by one scorecard variant.
#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct DiagnosticFrontierBlocker {
    pub outcome_class: DiagnosticVariantOutcomeClass,
    /// Checker capability codes are registry-backed and invariant codes use
    /// the reserved `INV.*` namespace. Harness and mismatch blockers have no
    /// capability code.
    pub code: Option<String>,
    pub detail: String,
}

/// First byte-significant line difference for a diagnostic artifact mismatch.
#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct DiagnosticArtifactDifference {
    pub line: usize,
    pub expected: String,
    pub actual: String,
}

/// Machine-readable results for a diagnostic baseline run.
#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct DiagnosticScorecard {
    pub schema_version: u32,
    pub provenance: DiagnosticScorecardProvenance,
    pub checker_mode: DiagnosticCheckerMode,
    pub comparison_scope: DiagnosticComparisonScope,
    pub full_artifact_comparison: bool,
    pub summary: DiagnosticScorecardSummary,
    pub variants: Vec<DiagnosticVariantResult>,
    /// Present only when both configured semantic artifacts were requested.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub semantic_artifacts: Option<SemanticArtifactScorecard>,
}

/// Git identity for one source tree used by a scorecard run.
#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct ScorecardRepositoryRevision {
    pub sha: Option<String>,
    pub dirty: Option<bool>,
}

/// Version and content identity of the capability registry compiled into the runner.
#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct ScorecardCapabilityRegistry {
    pub version: u32,
    pub digest: String,
}

/// Inputs needed to reproduce and attribute a scorecard run.
#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct DiagnosticScorecardProvenance {
    pub upstream: ScorecardRepositoryRevision,
    pub rust: ScorecardRepositoryRevision,
    /// Digest of the complete deterministic upstream oracle manifest.
    pub manifest_digest: String,
    pub digest_algorithm: String,
    /// Identity of the fixed subset used for this run, when present.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub fixed_shard: Option<ScorecardFixedShardProvenance>,
    pub invocation: Vec<String>,
    pub capability_registry: ScorecardCapabilityRegistry,
}

/// Independently versioned identity of a fixed diagnostic subset.
#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct ScorecardFixedShardProvenance {
    pub name: String,
    pub schema_version: u32,
    pub variant_key_version: u32,
    pub digest: String,
    pub digest_algorithm: String,
    pub variant_count: usize,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct FixedVariantManifest {
    schema_version: u32,
    name: String,
    upstream: FixedVariantManifestUpstream,
    variant_key_version: u32,
    selection_evidence: FixedVariantManifestSelectionEvidence,
    policy: FixedVariantManifestPolicy,
    coverage: FixedVariantManifestCoverage,
    digest: FixedVariantManifestDigest,
    variants: Vec<FixedVariantManifestEntry>,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct FixedVariantManifestUpstream {
    sha: String,
    oracle_manifest_digest: String,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct FixedVariantManifestSelectionEvidence {
    scorecard_schema_version: u32,
    rust_sha: String,
    selected_cases: usize,
    executed_variants: usize,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct FixedVariantManifestPolicy {
    families: Vec<String>,
    quota_per_family: usize,
    expected_diagnostics_per_family: FixedExpectedDiagnosticCounts,
}

#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct FixedExpectedDiagnosticCounts {
    clean: usize,
    error: usize,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct FixedVariantManifestCoverage {
    cases: usize,
    variants: usize,
    expected_clean: usize,
    expected_error: usize,
    single_file: usize,
    multi_file: usize,
    source_kind_membership: BTreeMap<String, usize>,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct FixedVariantManifestDigest {
    algorithm: String,
    canonicalization: String,
    value: String,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct FixedVariantManifestEntry {
    variant_key: String,
    family: String,
    case: String,
    options: BTreeMap<String, String>,
    #[serde(default)]
    expected_baseline: FixedExpectedBaseline,
    expected_diagnostics: FixedExpectedDiagnostics,
    file_shape: FixedFileShape,
    source_kinds: Vec<String>,
    tags: Vec<String>,
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
enum FixedExpectedBaseline {
    #[default]
    Missing,
    Present(Option<String>),
}

impl FixedExpectedBaseline {
    const fn is_missing(&self) -> bool {
        matches!(self, Self::Missing)
    }

    fn as_deref(&self) -> Option<&str> {
        match self {
            Self::Missing | Self::Present(None) => None,
            Self::Present(Some(value)) => Some(value),
        }
    }
}

impl<'de> Deserialize<'de> for FixedExpectedBaseline {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        Option::<String>::deserialize(deserializer).map(Self::Present)
    }
}

#[derive(Clone, Copy, Debug, Deserialize, Eq, Ord, PartialEq, PartialOrd)]
#[serde(rename_all = "snake_case")]
enum FixedExpectedDiagnostics {
    Clean,
    Error,
}

#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq)]
#[serde(rename_all = "snake_case")]
enum FixedFileShape {
    SingleFile,
    MultiFile,
}

const DIAGNOSTIC_SCORECARD_SCHEMA_VERSION: u32 = 5;
const CAPABILITY_REGISTRY_VERSION: u32 = 1;
const SCORECARD_DIGEST_ALGORITHM: &str = "xxh3-128";
const FIXED_VARIANT_MANIFEST_SCHEMA_VERSION: u32 = 1;
const DIAGNOSTIC_VARIANT_KEY_VERSION: u32 = 1;
const FIXED_MANIFEST_CANONICALIZATION: &str =
    "ordered variantKey values encoded as UTF-8, each followed by LF";
#[cfg(panic = "unwind")]
const CANONICAL_CHECKER_PANIC_INVARIANT: &str = "INV.CHECKER.PANIC";
const CAPABILITY_REGISTRY: &str = include_str!("../../../docs/typechecker-capabilities.tsv");
const TYPECHECKER_PORT_MAP: &str = include_str!("../../../docs/typechecker-port-map.tsv");

const TYPED_CHECKER_CAPABILITY_CODES: [&str; 20] = [
    "B02.DECLARATION_FAMILY",
    "B03.NAME_RESOLUTION",
    "C00.SOURCE_KIND",
    "E00.DERIVED_TYPE",
    "E00.ENUM_TYPE",
    "E00.SOURCE_SYNTAX",
    "M00.DECLARATION_FILE",
    "M00.EXTERNAL_MODULE_TARGET",
    "M00.FIXED_MODULE_FORMAT",
    "M00.NODE_MODULE_FACTS",
    "M00.PLAIN_ESM_MODE",
    "M00.SPECIFIER_RESOLUTION_MODE",
    "M03.IMPORT_META_MODULE_MODE",
    "R01.RELATION",
    "T04.GLOBAL_CONTEXT",
    "T05.DECLARED_TYPE",
    "T06.ARRAY_TYPE",
    "T06.LITERAL_UNION",
    "T06.TYPE_NODE",
    "T07.TYPE_DISPLAY",
];

fn stable_digest(bytes: &[u8]) -> String {
    format!("{:032x}", xxh3_128(bytes))
}

fn invalid_fixed_manifest(detail: impl Into<String>) -> io::Error {
    io::Error::new(
        io::ErrorKind::InvalidData,
        format!("invalid fixed variant manifest: {}", detail.into()),
    )
}

fn is_lower_hex(value: &str, length: usize) -> bool {
    value.len() == length
        && value
            .bytes()
            .all(|byte| byte.is_ascii_digit() || matches!(byte, b'a'..=b'f'))
}

fn is_manifest_identifier(value: &str) -> bool {
    !value.is_empty()
        && value.bytes().all(|byte| {
            byte.is_ascii_lowercase() || byte.is_ascii_digit() || matches!(byte, b'_' | b'-' | b'.')
        })
}

fn fixed_variant_manifest_digest(entries: &[FixedVariantManifestEntry]) -> String {
    let mut bytes = Vec::with_capacity(entries.len().saturating_mul(36));
    for entry in entries {
        bytes.extend_from_slice(entry.variant_key.as_bytes());
        bytes.push(b'\n');
    }
    stable_digest(&bytes)
}

#[allow(clippy::too_many_lines)] // One fail-closed audit surface for the versioned schema.
fn validate_fixed_variant_manifest_structure(manifest: &FixedVariantManifest) -> io::Result<()> {
    if manifest.schema_version != FIXED_VARIANT_MANIFEST_SCHEMA_VERSION {
        return Err(invalid_fixed_manifest(format!(
            "schemaVersion must be {FIXED_VARIANT_MANIFEST_SCHEMA_VERSION}, got {}",
            manifest.schema_version
        )));
    }
    if !is_manifest_identifier(&manifest.name) {
        return Err(invalid_fixed_manifest(format!(
            "name {:?} is not a stable manifest identifier",
            manifest.name
        )));
    }
    if manifest.variant_key_version != DIAGNOSTIC_VARIANT_KEY_VERSION {
        return Err(invalid_fixed_manifest(format!(
            "variantKeyVersion must be {DIAGNOSTIC_VARIANT_KEY_VERSION}, got {}",
            manifest.variant_key_version
        )));
    }
    if !is_lower_hex(&manifest.upstream.sha, 40) {
        return Err(invalid_fixed_manifest(
            "upstream.sha must be a 40-character lowercase Git SHA",
        ));
    }
    if !is_lower_hex(&manifest.upstream.oracle_manifest_digest, 32) {
        return Err(invalid_fixed_manifest(
            "upstream.oracleManifestDigest must be a 32-character lowercase digest",
        ));
    }
    let evidence = &manifest.selection_evidence;
    if evidence.scorecard_schema_version != DIAGNOSTIC_SCORECARD_SCHEMA_VERSION
        || !is_lower_hex(&evidence.rust_sha, 40)
        || evidence.selected_cases == 0
        || evidence.executed_variants < evidence.selected_cases
    {
        return Err(invalid_fixed_manifest(
            "selectionEvidence is malformed or does not identify a schema-5 scorecard",
        ));
    }

    let policy = &manifest.policy;
    if policy.families.is_empty() || policy.quota_per_family == 0 {
        return Err(invalid_fixed_manifest(
            "policy must contain at least one family and one variant per family",
        ));
    }
    let mut policy_families = BTreeSet::new();
    for family in &policy.families {
        if !is_manifest_identifier(family) || !policy_families.insert(family.as_str()) {
            return Err(invalid_fixed_manifest(format!(
                "policy repeats or malforms family {family:?}"
            )));
        }
    }
    let diagnostics_per_family = policy
        .expected_diagnostics_per_family
        .clean
        .checked_add(policy.expected_diagnostics_per_family.error)
        .ok_or_else(|| invalid_fixed_manifest("diagnostic quota overflows usize"))?;
    if diagnostics_per_family != policy.quota_per_family {
        return Err(invalid_fixed_manifest(format!(
            "clean/error quota {diagnostics_per_family} does not equal quotaPerFamily {}",
            policy.quota_per_family
        )));
    }
    let expected_variants = policy
        .families
        .len()
        .checked_mul(policy.quota_per_family)
        .ok_or_else(|| invalid_fixed_manifest("family quota overflows usize"))?;
    if manifest.variants.len() != expected_variants {
        return Err(invalid_fixed_manifest(format!(
            "policy requires {expected_variants} variants, found {}",
            manifest.variants.len()
        )));
    }

    let mut keys = BTreeSet::new();
    let mut cases = BTreeSet::new();
    let mut family_counts = BTreeMap::<&str, usize>::new();
    let mut family_diagnostics = BTreeMap::<(&str, FixedExpectedDiagnostics), usize>::new();
    let mut expected_clean = 0usize;
    let mut expected_error = 0usize;
    let mut single_file = 0usize;
    let mut multi_file = 0usize;
    let mut source_kind_membership = BTreeMap::<String, usize>::new();
    for entry in &manifest.variants {
        let Some(digest) = entry.variant_key.strip_prefix("v1:") else {
            return Err(invalid_fixed_manifest(format!(
                "variant key {:?} does not use the v1 identity",
                entry.variant_key
            )));
        };
        if !is_lower_hex(digest, 32) || !keys.insert(entry.variant_key.as_str()) {
            return Err(invalid_fixed_manifest(format!(
                "variant key {:?} is malformed or duplicated",
                entry.variant_key
            )));
        }
        if entry.expected_baseline.is_missing() {
            return Err(invalid_fixed_manifest(format!(
                "variant {} must explicitly include expectedBaseline",
                entry.variant_key
            )));
        }
        if !policy_families.contains(entry.family.as_str()) {
            return Err(invalid_fixed_manifest(format!(
                "variant {} uses unlisted family {:?}",
                entry.variant_key, entry.family
            )));
        }
        if entry.case.is_empty()
            || entry.case.starts_with('/')
            || entry.case.contains('\\')
            || entry.case.split('/').any(|component| component == "..")
        {
            return Err(invalid_fixed_manifest(format!(
                "variant {} has non-canonical case path {:?}",
                entry.variant_key, entry.case
            )));
        }
        if entry.source_kinds.is_empty() {
            return Err(invalid_fixed_manifest(format!(
                "variant {} has no source kinds",
                entry.variant_key
            )));
        }
        let mut source_kinds = BTreeSet::new();
        for kind in &entry.source_kinds {
            if !is_manifest_identifier(kind) || !source_kinds.insert(kind.as_str()) {
                return Err(invalid_fixed_manifest(format!(
                    "variant {} repeats or malforms source kind {kind:?}",
                    entry.variant_key
                )));
            }
            *source_kind_membership.entry(kind.clone()).or_default() += 1;
        }
        if entry.tags.is_empty() {
            return Err(invalid_fixed_manifest(format!(
                "variant {} has no semantic tags",
                entry.variant_key
            )));
        }
        let mut tags = BTreeSet::new();
        for tag in &entry.tags {
            if !is_manifest_identifier(tag) || !tags.insert(tag.as_str()) {
                return Err(invalid_fixed_manifest(format!(
                    "variant {} repeats or malforms tag {tag:?}",
                    entry.variant_key
                )));
            }
        }

        cases.insert(entry.case.as_str());
        *family_counts.entry(entry.family.as_str()).or_default() += 1;
        *family_diagnostics
            .entry((entry.family.as_str(), entry.expected_diagnostics))
            .or_default() += 1;
        match entry.expected_diagnostics {
            FixedExpectedDiagnostics::Clean => expected_clean += 1,
            FixedExpectedDiagnostics::Error => expected_error += 1,
        }
        match entry.file_shape {
            FixedFileShape::SingleFile => single_file += 1,
            FixedFileShape::MultiFile => multi_file += 1,
        }
    }
    for family in &policy.families {
        if family_counts.get(family.as_str()) != Some(&policy.quota_per_family)
            || family_diagnostics
                .get(&(family.as_str(), FixedExpectedDiagnostics::Clean))
                .copied()
                .unwrap_or_default()
                != policy.expected_diagnostics_per_family.clean
            || family_diagnostics
                .get(&(family.as_str(), FixedExpectedDiagnostics::Error))
                .copied()
                .unwrap_or_default()
                != policy.expected_diagnostics_per_family.error
        {
            return Err(invalid_fixed_manifest(format!(
                "family {family:?} does not satisfy its quota and clean/error policy"
            )));
        }
    }

    let coverage = &manifest.coverage;
    if coverage.cases != cases.len()
        || coverage.variants != manifest.variants.len()
        || coverage.expected_clean != expected_clean
        || coverage.expected_error != expected_error
        || coverage.single_file != single_file
        || coverage.multi_file != multi_file
        || coverage.source_kind_membership != source_kind_membership
        || evidence.selected_cases < coverage.cases
        || evidence.executed_variants < coverage.variants
    {
        return Err(invalid_fixed_manifest(
            "coverage counters do not match the selected variant metadata",
        ));
    }
    if manifest.digest.algorithm != SCORECARD_DIGEST_ALGORITHM
        || manifest.digest.canonicalization != FIXED_MANIFEST_CANONICALIZATION
        || !is_lower_hex(&manifest.digest.value, 32)
    {
        return Err(invalid_fixed_manifest(
            "digest algorithm, canonicalization, or value shape is invalid",
        ));
    }
    let actual_digest = fixed_variant_manifest_digest(&manifest.variants);
    if manifest.digest.value != actual_digest {
        return Err(invalid_fixed_manifest(format!(
            "ordered-key digest is {}, expected {actual_digest}",
            manifest.digest.value
        )));
    }
    Ok(())
}

fn read_fixed_variant_manifest(path: &Path) -> io::Result<FixedVariantManifest> {
    let bytes = fs::read(path)?;
    let manifest = serde_json::from_slice(&bytes)
        .map_err(|error| invalid_fixed_manifest(format!("{}: {error}", path.to_string_lossy())))?;
    validate_fixed_variant_manifest_structure(&manifest)?;
    Ok(manifest)
}

fn git_output(repository: &Path, arguments: &[&str]) -> Option<String> {
    let output = Command::new("git")
        .arg("-C")
        .arg(repository)
        .args(arguments)
        .env("GIT_OPTIONAL_LOCKS", "0")
        .output()
        .ok()?;
    if !output.status.success() {
        return None;
    }
    Some(
        String::from_utf8_lossy(&output.stdout)
            .trim_end()
            .to_owned(),
    )
}

fn repository_revision(repository: &Path) -> ScorecardRepositoryRevision {
    let sha = git_output(repository, &["rev-parse", "--verify", "HEAD"]);
    let dirty = sha.as_ref().and_then(|_| {
        git_output(
            repository,
            &["status", "--porcelain=v1", "--untracked-files=normal"],
        )
        .map(|status| !status.is_empty())
    });
    ScorecardRepositoryRevision { sha, dirty }
}

fn oracle_manifest_digest(manifest: &UpstreamManifest) -> io::Result<String> {
    let mut bytes = Vec::new();
    manifest.write_to(&mut bytes)?;
    Ok(stable_digest(&bytes))
}

fn validate_fixed_variant_manifest_upstream(
    manifest: &FixedVariantManifest,
    repository: &Path,
    oracle_digest: &str,
) -> io::Result<()> {
    let revision = repository_revision(repository);
    if revision.sha.as_deref() != Some(manifest.upstream.sha.as_str()) {
        return Err(invalid_fixed_manifest(format!(
            "upstream SHA is {:?}, expected {}",
            revision.sha, manifest.upstream.sha
        )));
    }
    if revision.dirty != Some(false) {
        return Err(invalid_fixed_manifest(
            "upstream checkout must be clean for fixed-shard execution",
        ));
    }
    if manifest.upstream.oracle_manifest_digest != oracle_digest {
        return Err(invalid_fixed_manifest(format!(
            "complete oracle manifest digest is {oracle_digest}, expected {}",
            manifest.upstream.oracle_manifest_digest,
        )));
    }
    Ok(())
}

#[allow(clippy::too_many_lines)] // Keeps the versioned registry contract in one audit surface.
fn capability_registry_metadata() -> io::Result<ScorecardCapabilityRegistry> {
    let mut lines = CAPABILITY_REGISTRY.lines();
    if lines.next() != Some("# schema_version\t1") {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "typechecker capability registry must declare schema version 1",
        ));
    }
    let expected_header =
        "code\tport_map_id\tdescription\towner_slice\tintroduced_version\tstatus\treplacement";
    if lines.next() != Some(expected_header) {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "typechecker capability registry has an invalid header",
        ));
    }
    let mut port_map_ids = BTreeSet::new();
    for line in TYPECHECKER_PORT_MAP.lines().skip(1) {
        let Some(port_map_id) = line.split('\t').next().filter(|id| !id.is_empty()) else {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "typechecker port map contains an empty row identity",
            ));
        };
        if !port_map_ids.insert(port_map_id) {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                format!("typechecker port map repeats row {port_map_id}"),
            ));
        }
    }
    let mut codes = BTreeSet::new();
    let mut retired_replacements = Vec::new();
    for (index, line) in lines.enumerate() {
        if line.is_empty() || line.starts_with('#') {
            continue;
        }
        let columns: [&str; 7] = match line.split('\t').collect::<Vec<_>>().try_into() {
            Ok(columns) => columns,
            Err(columns) => {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidData,
                    format!(
                        "typechecker capability registry line {} has {} columns, expected 7",
                        index + 3,
                        columns.len()
                    ),
                ));
            }
        };
        let [
            code,
            port_map_id,
            description,
            owner_slice,
            introduced_version,
            status,
            replacement,
        ] = columns;
        if code.starts_with("INV.") || !codes.insert(code) {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                format!("invalid or duplicate capability code {code:?}"),
            ));
        }
        if !port_map_ids.contains(port_map_id) {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                format!("capability {code} references unknown port-map row {port_map_id}"),
            ));
        }
        if code.split_once('.').map(|(prefix, _)| prefix) != Some(port_map_id) {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                format!("capability {code} does not use its port-map row as the code prefix"),
            ));
        }
        let lifecycle_is_valid = match status {
            "active" => replacement == "-",
            "retired" => {
                retired_replacements.push((code, replacement));
                !replacement.is_empty() && replacement != "-"
            }
            _ => false,
        };
        let introduced_version = introduced_version.parse::<u32>();
        if description.is_empty()
            || owner_slice.is_empty()
            || !matches!(introduced_version, Ok(1..=CAPABILITY_REGISTRY_VERSION))
            || !lifecycle_is_valid
        {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                format!("capability {code} has invalid lifecycle metadata"),
            ));
        }
    }
    for (code, replacement) in retired_replacements {
        if !codes.contains(replacement) {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                format!("retired capability {code} names unknown replacement {replacement}"),
            ));
        }
    }
    for capability_code in TYPED_CHECKER_CAPABILITY_CODES {
        if !codes.contains(capability_code) {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                format!("typed checker capability {capability_code} is absent from the registry"),
            ));
        }
    }
    Ok(ScorecardCapabilityRegistry {
        version: CAPABILITY_REGISTRY_VERSION,
        digest: stable_digest(CAPABILITY_REGISTRY.as_bytes()),
    })
}

fn scorecard_provenance(
    repository: &Path,
    options: &RunnerOptions,
    oracle_digest: &str,
    fixed_manifest: Option<&FixedVariantManifest>,
) -> io::Result<DiagnosticScorecardProvenance> {
    let capability_registry = capability_registry_metadata()?;
    let fixed_shard = fixed_manifest.map(|manifest| ScorecardFixedShardProvenance {
        name: manifest.name.clone(),
        schema_version: manifest.schema_version,
        variant_key_version: manifest.variant_key_version,
        digest: manifest.digest.value.clone(),
        digest_algorithm: manifest.digest.algorithm.clone(),
        variant_count: manifest.variants.len(),
    });
    if options.scorecard_json.is_none() {
        return Ok(DiagnosticScorecardProvenance {
            upstream: ScorecardRepositoryRevision {
                sha: None,
                dirty: None,
            },
            rust: ScorecardRepositoryRevision {
                sha: None,
                dirty: None,
            },
            manifest_digest: String::new(),
            digest_algorithm: SCORECARD_DIGEST_ALGORITHM.to_owned(),
            fixed_shard,
            invocation: options.invocation.clone(),
            capability_registry,
        });
    }
    let rust_repository = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    Ok(DiagnosticScorecardProvenance {
        upstream: repository_revision(repository),
        rust: repository_revision(&rust_repository),
        manifest_digest: oracle_digest.to_owned(),
        digest_algorithm: SCORECARD_DIGEST_ALGORITHM.to_owned(),
        fixed_shard,
        invocation: options.invocation.clone(),
        capability_registry,
    })
}

fn append_identity_field(identity: &mut Vec<u8>, name: &str, value: &str) {
    let name_length = u64::try_from(name.len()).expect("field name length must fit u64");
    let value_length = u64::try_from(value.len()).expect("field value length must fit u64");
    identity.extend_from_slice(&name_length.to_le_bytes());
    identity.extend_from_slice(name.as_bytes());
    identity.extend_from_slice(&value_length.to_le_bytes());
    identity.extend_from_slice(value.as_bytes());
}

fn diagnostic_variant_key(
    case: &str,
    variant: &OptionVariant,
    expected_baseline: Option<&str>,
    expected: &str,
) -> String {
    let mut identity = Vec::new();
    append_identity_field(&mut identity, "case", case);
    for (name, value) in &variant.values {
        let canonical_name = name.to_ascii_lowercase();
        let canonical_value =
            normalized_option_value(name, value).unwrap_or_else(|| value.trim().to_owned());
        append_identity_field(&mut identity, &canonical_name, &canonical_value);
    }
    append_identity_field(
        &mut identity,
        "expectedBaseline",
        expected_baseline.unwrap_or("<none>"),
    );
    append_identity_field(&mut identity, "expectedContent", expected);
    format!("v1:{}", stable_digest(&identity))
}

impl DiagnosticScorecard {
    fn write_json(&self, path: &Path) -> io::Result<()> {
        let mut file = fs::File::create(path)?;
        serde_json::to_writer_pretty(&mut file, self).map_err(io::Error::other)?;
        writeln!(file)
    }
}

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct RunnerSummary {
    pub discovered_cases: usize,
    pub upstream_skipped_cases: usize,
    pub selected_cases: usize,
    pub executed_variants: usize,
    pub upstream_skipped_variants: usize,
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

impl fmt::Display for RunnerSummary {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            formatter,
            "summary: discovered_cases={} upstream_skipped_cases={} selected_cases={} executed_variants={} matched={} mismatched={} missing={} content={} missing_sections={} unexpected_sections={} diagnostics={}",
            self.discovered_cases,
            self.upstream_skipped_cases,
            self.selected_cases,
            self.executed_variants,
            self.matched,
            self.mismatched,
            self.missing,
            self.content_differences,
            self.missing_sections,
            self.unexpected_sections,
            self.diagnostic_failures,
        )?;
        if self.upstream_skipped_variants != 0 {
            write!(
                formatter,
                " upstream_skipped_variants={}",
                self.upstream_skipped_variants
            )?;
        }
        Ok(())
    }
}

/// Discovers upstream cases/reference baselines and runs emitted-output comparisons.
///
/// # Errors
///
/// Returns an error when a case, baseline, or fixture compilation cannot be read.
#[allow(clippy::too_many_lines)] // Keep emitted-output selection and accounting visibly linear.
pub fn run_upstream_baselines(
    repository: &Path,
    options: &RunnerOptions,
    writer: &mut impl Write,
) -> io::Result<RunnerSummary> {
    if options.variant_manifest.is_some() {
        return Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            "--variant-manifest requires diagnostic mode",
        ));
    }
    if options.canonical_checker {
        return Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            "the canonical checker is diagnostics-only and cannot run emitted-output baselines",
        ));
    }
    let manifest = discover_upstream_manifest(repository)?;
    let manifest_summary = manifest.summary();
    let mut cases = Vec::new();
    let mut baseline_sets = Vec::new();
    for suite in &manifest.suites {
        let baselines = collect_files(&suite.oracle_root, is_emit_baseline_file)?;
        let baseline_index = baseline_sets.len();
        baseline_sets.push(index_baselines(baselines));
        for case in &suite.cases {
            if case.disposition == UpstreamCaseDisposition::Runnable {
                cases.push((case.path.clone(), baseline_index));
            }
        }
    }
    let filter = options.filter.as_deref().map(str::to_ascii_lowercase);
    let cases = cases
        .into_iter()
        .filter(|(path, _)| {
            filter
                .as_ref()
                .is_none_or(|filter| path.to_string_lossy().to_ascii_lowercase().contains(filter))
        })
        .skip(options.skip)
        .take(options.limit.unwrap_or(usize::MAX))
        .collect::<Vec<_>>();

    let mut summary = RunnerSummary {
        discovered_cases: manifest_summary.discovered_cases,
        upstream_skipped_cases: manifest_summary.upstream_skipped_cases,
        selected_cases: cases.len(),
        ..RunnerSummary::default()
    };
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
            summary.executed_variants += 1;
            let selected = select_variant_baselines(&candidates, case_name, &variant, &axes);
            let display_path = case_path
                .strip_prefix(repository)
                .unwrap_or(&case_path)
                .display();
            let label = variant_label(&variant, &axes);
            if !variant.unsupported_details.is_empty() {
                summary.mismatched += 1;
                writeln!(
                    writer,
                    "MISMATCH {display_path}{label}: unsupported configuration: {}",
                    variant.unsupported_details.join("; ")
                )?;
                continue;
            }
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
    writeln!(writer, "{summary}")?;
    Ok(summary)
}

struct DiagnosticVariantPlan {
    case: Arc<Case>,
    axes: Arc<[String]>,
    variant: OptionVariant,
    variant_key: String,
    scorecard_case: String,
    expected_baseline: Option<String>,
    expected: String,
    semantic_artifacts: Option<SemanticArtifactPlan>,
}

#[derive(Clone, Debug)]
struct SemanticArtifactPlan {
    types: Option<String>,
    symbols: Option<String>,
    upstream_skipped: bool,
}

#[derive(Clone, Debug, Default)]
struct SemanticBaselineSet {
    types: BTreeMap<String, Vec<PathBuf>>,
    symbols: BTreeMap<String, Vec<PathBuf>>,
}

impl SemanticBaselineSet {
    fn discover(root: &Path) -> io::Result<Self> {
        let baselines = collect_files(root, |path| {
            path.file_name()
                .and_then(|name| name.to_str())
                .is_some_and(|name| {
                    artifacts::types::baseline_base(name).is_some()
                        || artifacts::symbols::baseline_base(name).is_some()
                })
        })?;
        Ok(Self {
            types: index_baselines_with(baselines.clone(), artifacts::types::baseline_base),
            symbols: index_baselines_with(baselines, artifacts::symbols::baseline_base),
        })
    }

    fn artifact_baseline(
        &self,
        repository: &Path,
        case_path: &Path,
        case_name: &str,
        variant: &OptionVariant,
        axes: &[String],
        kind: SemanticArtifactKind,
    ) -> io::Result<Option<String>> {
        let index = match kind {
            SemanticArtifactKind::Types => &self.types,
            SemanticArtifactKind::Symbols => &self.symbols,
        };
        let candidates = index
            .get(case_name)
            .map_or_else(Vec::new, |paths| paths.iter().collect::<Vec<_>>());
        let configured_base = configured_baseline_base(case_name, variant, axes);
        let selected = candidates
            .into_iter()
            .filter(|path| {
                path.file_name()
                    .and_then(|name| name.to_str())
                    .and_then(|name| kind.baseline_base(name))
                    .is_some_and(|base| base == configured_base)
            })
            .collect::<Vec<_>>();
        if selected.len() > 1 {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                format!(
                    "multiple {} baselines match {}{}: {}",
                    kind.extension(),
                    case_path.display(),
                    variant_label(variant, axes),
                    selected
                        .iter()
                        .map(|path| path.display().to_string())
                        .collect::<Vec<_>>()
                        .join(", ")
                ),
            ));
        }
        Ok(selected
            .first()
            .map(|path| relative_scorecard_path(repository, path)))
    }
}

struct FixedDiagnosticCase {
    path: PathBuf,
    oracle_root: PathBuf,
    disposition: UpstreamCaseDisposition,
}

#[allow(clippy::too_many_lines)] // Keep variant expansion and oracle selection in one ordered pass.
fn prepare_diagnostic_case_variants(
    repository: &Path,
    case_path: &Path,
    baseline_files: &BTreeMap<String, Vec<PathBuf>>,
    semantic_baselines: Option<&SemanticBaselineSet>,
) -> io::Result<Vec<DiagnosticVariantPlan>> {
    let source = fs::read(case_path)?;
    let case = Arc::new(
        Case::parse(case_path, source)
            .map_err(|error| io::Error::new(io::ErrorKind::InvalidData, error))?,
    );
    let axes = Arc::<[String]>::from(matrix_axes(&case));
    let case_name = case_path
        .file_stem()
        .and_then(|name| name.to_str())
        .unwrap_or_default();
    let candidates = baseline_files
        .get(case_name)
        .map_or_else(Vec::new, |paths| paths.iter().collect::<Vec<_>>());
    let scorecard_case = relative_scorecard_path(repository, case_path);
    expand_option_matrix(&case)
        .into_iter()
        .map(|variant| {
            let selected = select_variant_baselines_with(
                &candidates,
                case_name,
                &variant,
                &axes,
                error_baseline_base,
            );
            if selected.len() > 1 {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidData,
                    format!(
                        "multiple error baselines match {}{}: {}",
                        case_path.display(),
                        variant_label(&variant, &axes),
                        selected
                            .iter()
                            .map(|path| path.display().to_string())
                            .collect::<Vec<_>>()
                            .join(", ")
                    ),
                ));
            }
            let expected_baseline = selected
                .first()
                .map(|path| relative_scorecard_path(repository, path));
            let expected = selected
                .first()
                .map(fs::read_to_string)
                .transpose()?
                .unwrap_or_default();
            let variant_key = diagnostic_variant_key(
                &scorecard_case,
                &variant,
                expected_baseline.as_deref(),
                &expected,
            );
            let semantic_artifacts = semantic_baselines
                .map(|baselines| -> io::Result<_> {
                    let types = baselines.artifact_baseline(
                        repository,
                        case_path,
                        case_name,
                        &variant,
                        &axes,
                        SemanticArtifactKind::Types,
                    )?;
                    let symbols = baselines.artifact_baseline(
                        repository,
                        case_path,
                        case_name,
                        &variant,
                        &axes,
                        SemanticArtifactKind::Symbols,
                    )?;
                    let upstream_skipped = case
                        .directive_values("noTypesAndSymbols")
                        .last()
                        .is_some_and(|value| value.eq_ignore_ascii_case("true"));
                    if upstream_skipped && (types.is_some() || symbols.is_some()) {
                        return Err(io::Error::new(
                            io::ErrorKind::InvalidData,
                            format!(
                                "@noTypesAndSymbols case {} unexpectedly has semantic baselines",
                                case_path.display()
                            ),
                        ));
                    }
                    Ok(SemanticArtifactPlan {
                        types,
                        symbols,
                        upstream_skipped,
                    })
                })
                .transpose()?;
            Ok(DiagnosticVariantPlan {
                case: Arc::clone(&case),
                axes: Arc::clone(&axes),
                variant,
                variant_key,
                scorecard_case: scorecard_case.clone(),
                expected_baseline,
                expected,
                semantic_artifacts,
            })
        })
        .collect()
}

fn fixed_source_kind(path: &Path) -> String {
    let path = path.to_string_lossy().to_ascii_lowercase();
    [
        ("d.mts", ".d.mts"),
        ("d.cts", ".d.cts"),
        ("d.ts", ".d.ts"),
        ("tsx", ".tsx"),
        ("jsx", ".jsx"),
        ("mts", ".mts"),
        ("cts", ".cts"),
        ("mjs", ".mjs"),
        ("cjs", ".cjs"),
        ("js", ".js"),
        ("json", ".json"),
        ("ts", ".ts"),
    ]
    .into_iter()
    .find_map(|(kind, suffix)| path.ends_with(suffix).then_some(kind))
    .unwrap_or("other")
    .to_owned()
}

fn fixed_case_source_kinds(case: &Case) -> Vec<String> {
    let mut kinds = Vec::new();
    for unit in &case.units {
        let kind = fixed_source_kind(&unit.path);
        if !kinds.contains(&kind) {
            kinds.push(kind);
        }
    }
    kinds
}

fn validate_fixed_variant_entry(
    entry: &FixedVariantManifestEntry,
    plan: &DiagnosticVariantPlan,
) -> io::Result<()> {
    let expected_diagnostics = if parse_error_baseline_header(&plan.expected).is_empty() {
        FixedExpectedDiagnostics::Clean
    } else {
        FixedExpectedDiagnostics::Error
    };
    let file_shape = if plan.case.units.len() > 1 {
        FixedFileShape::MultiFile
    } else {
        FixedFileShape::SingleFile
    };
    let source_kinds = fixed_case_source_kinds(&plan.case);
    if entry.case != plan.scorecard_case
        || entry.options != plan.variant.values
        || entry.expected_baseline.as_deref() != plan.expected_baseline.as_deref()
        || entry.expected_diagnostics != expected_diagnostics
        || entry.file_shape != file_shape
        || entry.source_kinds != source_kinds
    {
        return Err(invalid_fixed_manifest(format!(
            "variant {} metadata disagrees with discovered case/options/baseline/source facts",
            entry.variant_key
        )));
    }
    Ok(())
}

fn select_fixed_diagnostic_cases(
    oracle_manifest: &UpstreamManifest,
    manifest: &FixedVariantManifest,
) -> io::Result<Vec<FixedDiagnosticCase>> {
    let desired = manifest
        .variants
        .iter()
        .map(|entry| entry.case.as_str())
        .collect::<BTreeSet<_>>();
    let mut matches = BTreeMap::<String, Vec<FixedDiagnosticCase>>::new();
    for suite in &oracle_manifest.suites {
        for case in &suite.cases {
            let relative_path = case.relative_path.to_string_lossy().replace('\\', "/");
            if !desired.contains(relative_path.as_str()) {
                continue;
            }
            matches
                .entry(relative_path.clone())
                .or_default()
                .push(FixedDiagnosticCase {
                    path: case.path.clone(),
                    oracle_root: suite.oracle_root.clone(),
                    disposition: case.disposition,
                });
        }
    }

    let mut selected = Vec::with_capacity(desired.len());
    for case_name in desired {
        let mut case_matches = matches.remove(case_name).unwrap_or_default();
        if case_matches.is_empty() {
            return Err(invalid_fixed_manifest(format!(
                "case {case_name:?} does not exist in the complete oracle manifest"
            )));
        }
        if case_matches.len() != 1 {
            return Err(invalid_fixed_manifest(format!(
                "case {case_name:?} resolves {} times in the complete oracle manifest",
                case_matches.len()
            )));
        }
        let case_match = case_matches
            .pop()
            .expect("one fixed case match was established");
        if case_match.disposition != UpstreamCaseDisposition::Runnable {
            return Err(invalid_fixed_manifest(format!(
                "case {case_name:?} is not runnable in the complete oracle manifest"
            )));
        }
        selected.push(case_match);
    }
    Ok(selected)
}

fn resolve_fixed_variant_plans(
    repository: &Path,
    cases: &[(PathBuf, usize)],
    baseline_sets: &[BTreeMap<String, Vec<PathBuf>>],
    semantic_baseline_sets: &[Option<SemanticBaselineSet>],
    manifest: &FixedVariantManifest,
) -> io::Result<Vec<DiagnosticVariantPlan>> {
    let desired = manifest
        .variants
        .iter()
        .enumerate()
        .map(|(index, entry)| (entry.variant_key.as_str(), (index, entry)))
        .collect::<BTreeMap<_, _>>();
    let mut resolved = std::iter::repeat_with(|| None)
        .take(manifest.variants.len())
        .collect::<Vec<Option<DiagnosticVariantPlan>>>();
    for (case_path, baseline_index) in cases {
        for plan in prepare_diagnostic_case_variants(
            repository,
            case_path,
            &baseline_sets[*baseline_index],
            semantic_baseline_sets[*baseline_index].as_ref(),
        )? {
            let Some(&(index, entry)) = desired.get(plan.variant_key.as_str()) else {
                continue;
            };
            if resolved[index].is_some() {
                return Err(invalid_fixed_manifest(format!(
                    "variant key {} resolves more than once in the complete corpus",
                    plan.variant_key
                )));
            }
            validate_fixed_variant_entry(entry, &plan)?;
            resolved[index] = Some(plan);
        }
    }
    let missing = manifest
        .variants
        .iter()
        .zip(&resolved)
        .filter_map(|(entry, plan)| plan.is_none().then_some(entry.variant_key.as_str()))
        .collect::<Vec<_>>();
    if !missing.is_empty() {
        return Err(invalid_fixed_manifest(format!(
            "variant keys do not resolve in the complete corpus: {}",
            missing.join(", ")
        )));
    }
    Ok(resolved
        .into_iter()
        .map(|plan| plan.expect("missing fixed plans were rejected"))
        .collect())
}

fn semantic_artifact_result(
    kind: SemanticArtifactKind,
    expected_baseline: Option<&str>,
    upstream_skipped: bool,
    artifacts: Option<&GeneratedSemanticArtifacts>,
    repository: &Path,
) -> io::Result<SemanticArtifactResult> {
    if upstream_skipped {
        return Ok(SemanticArtifactResult {
            expected_baseline: None,
            status: SemanticArtifactStatus::UpstreamSkipped,
            visited_nodes: 0,
            unsupported_detail: None,
            first_difference: None,
        });
    }

    let Some(artifacts) = artifacts else {
        return Ok(SemanticArtifactResult {
            expected_baseline: expected_baseline.map(str::to_owned),
            status: SemanticArtifactStatus::NotReached,
            visited_nodes: 0,
            unsupported_detail: None,
            first_difference: None,
        });
    };

    let mut result = SemanticArtifactResult {
        expected_baseline: expected_baseline.map(str::to_owned),
        status: SemanticArtifactStatus::ExactMatch,
        visited_nodes: artifacts.visited_nodes(kind),
        unsupported_detail: None,
        first_difference: None,
    };
    let actual = match artifacts.result(kind) {
        Ok(actual) => actual,
        Err(detail) => {
            result.status = SemanticArtifactStatus::Unsupported;
            result.unsupported_detail = Some(detail.clone());
            return Ok(result);
        }
    };

    let Some(expected_baseline) = expected_baseline else {
        if actual != "<no content>" {
            result.status = SemanticArtifactStatus::Mismatch;
            result.first_difference = Some(DiagnosticArtifactDifference {
                line: 1,
                expected: "<missing baseline>".to_owned(),
                actual: actual.lines().next().unwrap_or_default().to_owned(),
            });
        }
        return Ok(result);
    };

    let expected = fs::read_to_string(repository.join(expected_baseline))?;
    if expected != *actual {
        let (line, expected, actual) = first_different_line(&expected, actual);
        result.status = SemanticArtifactStatus::Mismatch;
        result.first_difference = Some(DiagnosticArtifactDifference {
            line,
            expected: expected.to_owned(),
            actual: actual.to_owned(),
        });
    }
    Ok(result)
}

fn semantic_variant_results(
    plan: &SemanticArtifactPlan,
    artifacts: Option<&GeneratedSemanticArtifacts>,
    repository: &Path,
) -> io::Result<SemanticVariantArtifacts> {
    Ok(SemanticVariantArtifacts {
        types: semantic_artifact_result(
            SemanticArtifactKind::Types,
            plan.types.as_deref(),
            plan.upstream_skipped,
            artifacts,
            repository,
        )?,
        symbols: semantic_artifact_result(
            SemanticArtifactKind::Symbols,
            plan.symbols.as_deref(),
            plan.upstream_skipped,
            artifacts,
            repository,
        )?,
    })
}

fn record_semantic_artifact(
    summary: &mut SemanticArtifactSummary,
    result: &SemanticArtifactResult,
) {
    if result.status == SemanticArtifactStatus::UpstreamSkipped {
        summary.upstream_skipped += 1;
        return;
    }
    if result.expected_baseline.is_some() {
        summary.expected_baselines += 1;
    } else {
        summary.missing_baselines += 1;
    }
    match result.status {
        SemanticArtifactStatus::ExactMatch => summary.exact_matches += 1,
        SemanticArtifactStatus::Mismatch => summary.mismatches += 1,
        SemanticArtifactStatus::Unsupported => summary.unsupported += 1,
        SemanticArtifactStatus::NotReached => summary.not_reached += 1,
        SemanticArtifactStatus::UpstreamSkipped => unreachable!(),
    }
}

fn record_semantic_variant(
    scorecard: &mut DiagnosticScorecard,
    results: &SemanticVariantArtifacts,
) {
    let Some(summary) = scorecard.semantic_artifacts.as_mut() else {
        return;
    };
    record_semantic_artifact(&mut summary.types, &results.types);
    record_semantic_artifact(&mut summary.symbols, &results.symbols);
}

fn record_upstream_skipped_variant(
    plan: DiagnosticVariantPlan,
    reasons: Vec<String>,
    repository: &Path,
    summary: &mut RunnerSummary,
    scorecard: &mut DiagnosticScorecard,
    writer: &mut impl Write,
) -> io::Result<()> {
    summary.upstream_skipped_variants += 1;
    scorecard.summary.upstream_skipped_variants += 1;

    let detail = reasons.join("; ");
    writeln!(
        writer,
        "SKIP {}{}: {detail}",
        plan.scorecard_case,
        variant_label(&plan.variant, &plan.axes),
    )?;

    let semantic_artifacts = plan
        .semantic_artifacts
        .as_ref()
        .map(|_| {
            semantic_variant_results(
                &SemanticArtifactPlan {
                    types: None,
                    symbols: None,
                    upstream_skipped: true,
                },
                None,
                repository,
            )
        })
        .transpose()?;
    if let Some(artifacts) = semantic_artifacts.as_ref() {
        record_semantic_variant(scorecard, artifacts);
    }

    scorecard.variants.push(DiagnosticVariantResult {
        variant_key: plan.variant_key,
        case: plan.scorecard_case,
        options: plan.variant.values,
        expected_baseline: plan.expected_baseline,
        comparison_scope: DiagnosticComparisonScope::FullArtifact,
        status: DiagnosticVariantStatus::UpstreamSkipped,
        outcome_class: DiagnosticVariantOutcomeClass::UpstreamSkipped,
        frontier_blocker: Some(DiagnosticFrontierBlocker {
            outcome_class: DiagnosticVariantOutcomeClass::UpstreamSkipped,
            code: None,
            detail,
        }),
        expected_header: parse_error_baseline_header(&plan.expected),
        actual_header: String::new(),
        mismatch_kinds: Vec::new(),
        first_difference: None,
        unsupported_details: reasons,
        diagnostics: Vec::new(),
        semantic_artifacts,
    });
    Ok(())
}

#[allow(clippy::too_many_lines)] // One shared execution path keeps ordinary and fixed runs exact.
fn execute_diagnostic_variant(
    mut plan: DiagnosticVariantPlan,
    repository: &Path,
    checker: FixtureChecker,
    summary: &mut RunnerSummary,
    scorecard: &mut DiagnosticScorecard,
    writer: &mut impl Write,
) -> io::Result<()> {
    let upstream_skip_reasons = pinned_skip_unsupported_details(&plan.case, &plan.variant);
    if !upstream_skip_reasons.is_empty() {
        return record_upstream_skipped_variant(
            plan,
            upstream_skip_reasons,
            repository,
            summary,
            scorecard,
            writer,
        );
    }

    summary.executed_variants += 1;
    let case_path = &plan.case.path;
    let mut checker_frontier = None;
    let walk_semantic_artifacts = plan
        .semantic_artifacts
        .as_ref()
        .is_some_and(|artifacts| !artifacts.upstream_skipped);
    let compilation = match compile_case_variant(
        &plan.case,
        &mut plan.variant,
        checker,
        walk_semantic_artifacts,
    ) {
        Ok(compilation) => compilation,
        // A fixture filesystem failure makes scorecard persistence itself
        // suspect. Keep it as a fail-closed harness error (CLI exit 2), never
        // as a checker invariant or capability.
        Err(FixtureCompilationFailure::Io(error)) => return Err(error),
        Err(FixtureCompilationFailure::Canonical(error)) => {
            let detail = format!("experimental canonical checker: {error}");
            match error.failure_class() {
                ts_compiler::CanonicalProgramCheckFailureClass::Unsupported { capability_code } => {
                    if !capability_registry_contains(capability_code) {
                        return Err(io::Error::new(
                            io::ErrorKind::InvalidData,
                            format!(
                                "typed checker capability {capability_code} is absent from the registry"
                            ),
                        ));
                    }
                    checker_frontier = Some((capability_code.to_owned(), detail.clone()));
                    plan.variant.unsupported_details.push(detail);
                    plan.variant.unsupported_details.sort();
                    plan.variant.unsupported_details.dedup();
                    Compilation::default()
                }
                ts_compiler::CanonicalProgramCheckFailureClass::Fatal { invariant_code } => {
                    retain_fatal_variant(
                        summary,
                        scorecard,
                        writer,
                        FatalVariantRecord {
                            case_path,
                            repository,
                            variant: &plan.variant,
                            axes: &plan.axes,
                            variant_key: plan.variant_key,
                            scorecard_case: plan.scorecard_case,
                            expected_baseline: plan.expected_baseline,
                            expected: &plan.expected,
                            semantic_artifacts: plan.semantic_artifacts.as_ref(),
                            invariant_code,
                            detail,
                        },
                    )?;
                    return Ok(());
                }
            }
        }
        #[cfg(panic = "unwind")]
        Err(FixtureCompilationFailure::CanonicalPanic { detail }) => {
            retain_fatal_variant(
                summary,
                scorecard,
                writer,
                FatalVariantRecord {
                    case_path,
                    repository,
                    variant: &plan.variant,
                    axes: &plan.axes,
                    variant_key: plan.variant_key,
                    scorecard_case: plan.scorecard_case,
                    expected_baseline: plan.expected_baseline,
                    expected: &plan.expected,
                    semantic_artifacts: plan.semantic_artifacts.as_ref(),
                    invariant_code: CANONICAL_CHECKER_PANIC_INVARIANT,
                    detail,
                },
            )?;
            return Ok(());
        }
    };
    let mut actual = render_error_baseline(&plan.case, &compilation.diagnostics);
    actual
        .unsupported_details
        .extend(plan.variant.unsupported_details.iter().cloned());
    let mut comparison =
        compare_diagnostic_artifacts(&plan.expected, &actual, &compilation.diagnostics);
    let semantic_artifacts = plan
        .semantic_artifacts
        .as_ref()
        .map(|artifacts| {
            semantic_variant_results(
                artifacts,
                compilation.semantic_artifacts.as_ref(),
                repository,
            )
        })
        .transpose()?;
    if let Some(artifacts) = semantic_artifacts.as_ref() {
        record_semantic_variant(scorecard, artifacts);
        if comparison.is_exact() {
            actual.unsupported_details.extend(
                [&artifacts.types, &artifacts.symbols]
                    .into_iter()
                    .filter_map(|artifact| artifact.unsupported_detail.clone()),
            );
            comparison =
                compare_diagnostic_artifacts(&plan.expected, &actual, &compilation.diagnostics);
            if comparison.is_exact()
                && let Some(mismatch) = [&artifacts.types, &artifacts.symbols]
                    .into_iter()
                    .find(|artifact| artifact.status == SemanticArtifactStatus::Mismatch)
            {
                comparison
                    .mismatch_kinds
                    .push(DiagnosticArtifactMismatchKind::Artifact);
                comparison
                    .first_difference
                    .clone_from(&mismatch.first_difference);
            }
        }
    }
    let checker_blocked = checker_frontier.is_some();
    let status = if checker_blocked {
        DiagnosticVariantStatus::UnsupportedDetail
    } else {
        comparison.status()
    };
    let (outcome_class, frontier_blocker) =
        comparison_frontier(status, &comparison, checker_frontier);
    if comparison.is_exact() && !checker_blocked {
        summary.matched += 1;
        scorecard.summary.exact_matches += 1;
    } else {
        summary.mismatched += 1;
        summary.diagnostic_failures += 1;
        if parse_error_baseline_header(&plan.expected) != parse_error_baseline_header(&actual.text)
        {
            scorecard.summary.header_mismatches += 1;
        }
        match status {
            DiagnosticVariantStatus::ExactMatch
            | DiagnosticVariantStatus::UpstreamSkipped
            | DiagnosticVariantStatus::FatalInvariant => {
                unreachable!()
            }
            DiagnosticVariantStatus::HeaderOnlyMatch => {
                scorecard.summary.header_only_matches += 1;
            }
            DiagnosticVariantStatus::CodeMismatch => {
                scorecard.summary.code_mismatches += 1;
            }
            DiagnosticVariantStatus::SpanMismatch => {
                scorecard.summary.span_mismatches += 1;
            }
            DiagnosticVariantStatus::MessageMismatch => {
                scorecard.summary.message_mismatches += 1;
            }
            DiagnosticVariantStatus::OrderMismatch => {
                scorecard.summary.order_mismatches += 1;
            }
            DiagnosticVariantStatus::UnsupportedDetail => {
                scorecard.summary.unsupported_details += 1;
            }
            DiagnosticVariantStatus::HeaderMismatch => {}
            DiagnosticVariantStatus::ArtifactMismatch => {
                scorecard.summary.artifact_mismatches += 1;
            }
        }
        let label = variant_label(&plan.variant, &plan.axes);
        if let Some(difference) = comparison.first_difference.as_ref() {
            writeln!(
                writer,
                "MISMATCH {}{label}: {status:?} at artifact line {}; expected {:?}, actual {:?}",
                plan.scorecard_case, difference.line, difference.expected, difference.actual
            )?;
        } else {
            writeln!(
                writer,
                "MISMATCH {}{label}: {status:?}: {}",
                plan.scorecard_case,
                comparison.unsupported_details.join("; ")
            )?;
        }
    }
    scorecard.summary.executed_variants += 1;
    scorecard.summary.actual_diagnostics += compilation.diagnostics.len();
    scorecard.variants.push(DiagnosticVariantResult {
        variant_key: plan.variant_key,
        case: plan.scorecard_case,
        options: plan.variant.values,
        expected_baseline: plan.expected_baseline,
        comparison_scope: DiagnosticComparisonScope::FullArtifact,
        status,
        outcome_class,
        frontier_blocker,
        expected_header: parse_error_baseline_header(&plan.expected),
        actual_header: parse_error_baseline_header(&actual.text),
        mismatch_kinds: comparison.mismatch_kinds,
        first_difference: comparison.first_difference,
        unsupported_details: comparison.unsupported_details,
        diagnostics: compilation
            .diagnostics
            .iter()
            .map(DiagnosticScorecardDiagnostic::from)
            .collect(),
        semantic_artifacts,
    });
    Ok(())
}

#[allow(clippy::too_many_lines)] // Keep fixed manifest validation and execution order together.
fn run_fixed_variant_diagnostic_baselines(
    repository: &Path,
    options: &RunnerOptions,
    manifest_path: &Path,
    writer: &mut impl Write,
) -> io::Result<RunnerSummary> {
    if options.filter.is_some() || options.skip != 0 || options.limit.is_some() {
        return Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            "--variant-manifest cannot be combined with --filter, --skip, or --limit",
        ));
    }
    let oracle_manifest = discover_upstream_manifest(repository)?;
    let manifest_summary = oracle_manifest.summary();
    let oracle_digest = oracle_manifest_digest(&oracle_manifest)?;
    let fixed_manifest = read_fixed_variant_manifest(manifest_path)?;
    validate_fixed_variant_manifest_upstream(&fixed_manifest, repository, &oracle_digest)?;

    let selected_case_sources = select_fixed_diagnostic_cases(&oracle_manifest, &fixed_manifest)?;
    let mut cases = Vec::new();
    let mut baseline_sets = Vec::new();
    let mut semantic_baseline_sets = Vec::new();
    let mut baseline_indexes = BTreeMap::<PathBuf, usize>::new();
    for selected_case in selected_case_sources {
        let baseline_index = if let Some(index) = baseline_indexes.get(&selected_case.oracle_root) {
            *index
        } else {
            let baselines = collect_files(&selected_case.oracle_root, is_error_baseline_file)?;
            let index = baseline_sets.len();
            baseline_sets.push(index_baselines_with(baselines, error_baseline_base));
            semantic_baseline_sets.push(
                options
                    .semantic_artifacts
                    .then(|| SemanticBaselineSet::discover(&selected_case.oracle_root))
                    .transpose()?,
            );
            baseline_indexes.insert(selected_case.oracle_root, index);
            index
        };
        cases.push((selected_case.path, baseline_index));
    }
    let plans = resolve_fixed_variant_plans(
        repository,
        &cases,
        &baseline_sets,
        &semantic_baseline_sets,
        &fixed_manifest,
    )?;
    let selected_cases = plans
        .iter()
        .map(|plan| plan.scorecard_case.as_str())
        .collect::<BTreeSet<_>>()
        .len();
    let provenance =
        scorecard_provenance(repository, options, &oracle_digest, Some(&fixed_manifest))?;
    let checker = if options.canonical_checker {
        FixtureChecker::Canonical
    } else {
        FixtureChecker::Legacy
    };
    let mut summary = RunnerSummary {
        discovered_cases: manifest_summary.discovered_cases,
        upstream_skipped_cases: manifest_summary.upstream_skipped_cases,
        selected_cases,
        ..RunnerSummary::default()
    };
    let mut scorecard = DiagnosticScorecard {
        schema_version: DIAGNOSTIC_SCORECARD_SCHEMA_VERSION,
        provenance,
        checker_mode: match checker {
            FixtureChecker::Legacy => DiagnosticCheckerMode::Legacy,
            FixtureChecker::Canonical => DiagnosticCheckerMode::Canonical,
        },
        comparison_scope: DiagnosticComparisonScope::FullArtifact,
        full_artifact_comparison: true,
        summary: DiagnosticScorecardSummary {
            discovered_cases: summary.discovered_cases,
            upstream_skipped_cases: summary.upstream_skipped_cases,
            selected_cases: summary.selected_cases,
            ..DiagnosticScorecardSummary::default()
        },
        variants: Vec::with_capacity(plans.len()),
        semantic_artifacts: options
            .semantic_artifacts
            .then(SemanticArtifactScorecard::default),
    };
    for plan in plans {
        execute_diagnostic_variant(
            plan,
            repository,
            checker,
            &mut summary,
            &mut scorecard,
            writer,
        )?;
    }
    if let Some(path) = &options.scorecard_json {
        scorecard.write_json(path)?;
    }
    writeln!(
        writer,
        "{summary} diagnostic_comparison=full-artifact exact_matches={} header_only_matches={} code_mismatches={} span_mismatches={} message_mismatches={} order_mismatches={} unsupported_details={} header_mismatches={} artifact_mismatches={} fatal_invariants={}",
        scorecard.summary.exact_matches,
        scorecard.summary.header_only_matches,
        scorecard.summary.code_mismatches,
        scorecard.summary.span_mismatches,
        scorecard.summary.message_mismatches,
        scorecard.summary.order_mismatches,
        scorecard.summary.unsupported_details,
        scorecard.summary.header_mismatches,
        scorecard.summary.artifact_mismatches,
        scorecard.summary.fatal_invariants,
    )?;
    Ok(summary)
}

/// Discovers upstream cases/reference baselines and compares compiler diagnostics.
///
/// The comparison renders and compares the complete non-pretty TypeScript `.errors.txt`
/// artifact. A missing error baseline means that the variant is expected to produce no
/// diagnostics.
///
/// # Errors
///
/// Returns an error when a case or baseline cannot be read, or when more than one error
/// baseline matches the same case variant.
#[allow(clippy::too_many_lines)]
pub fn run_upstream_diagnostic_baselines(
    repository: &Path,
    options: &RunnerOptions,
    writer: &mut impl Write,
) -> io::Result<RunnerSummary> {
    #[cfg(not(panic = "unwind"))]
    if options.canonical_checker {
        return Err(canonical_checker_unwind_isolation_error());
    }
    if let Some(path) = options.variant_manifest.as_deref() {
        return run_fixed_variant_diagnostic_baselines(repository, options, path, writer);
    }
    let manifest = discover_upstream_manifest(repository)?;
    let manifest_summary = manifest.summary();
    let oracle_digest = oracle_manifest_digest(&manifest)?;
    let provenance = scorecard_provenance(repository, options, &oracle_digest, None)?;
    let mut cases = Vec::new();
    let mut baseline_sets = Vec::new();
    let mut semantic_baseline_sets = Vec::new();
    for suite in &manifest.suites {
        let baselines = collect_files(&suite.oracle_root, is_error_baseline_file)?;
        let baseline_index = baseline_sets.len();
        baseline_sets.push(index_baselines_with(baselines, error_baseline_base));
        semantic_baseline_sets.push(
            options
                .semantic_artifacts
                .then(|| SemanticBaselineSet::discover(&suite.oracle_root))
                .transpose()?,
        );
        for case in &suite.cases {
            if case.disposition == UpstreamCaseDisposition::Runnable {
                cases.push((case.path.clone(), baseline_index));
            }
        }
    }
    let filter = options.filter.as_deref().map(str::to_ascii_lowercase);
    let cases = cases
        .into_iter()
        .filter(|(path, _)| {
            filter
                .as_ref()
                .is_none_or(|filter| path.to_string_lossy().to_ascii_lowercase().contains(filter))
        })
        .skip(options.skip)
        .take(options.limit.unwrap_or(usize::MAX))
        .collect::<Vec<_>>();

    let mut summary = RunnerSummary {
        discovered_cases: manifest_summary.discovered_cases,
        upstream_skipped_cases: manifest_summary.upstream_skipped_cases,
        selected_cases: cases.len(),
        ..RunnerSummary::default()
    };
    let checker = if options.canonical_checker {
        FixtureChecker::Canonical
    } else {
        FixtureChecker::Legacy
    };
    let mut scorecard = DiagnosticScorecard {
        schema_version: DIAGNOSTIC_SCORECARD_SCHEMA_VERSION,
        provenance,
        checker_mode: match checker {
            FixtureChecker::Legacy => DiagnosticCheckerMode::Legacy,
            FixtureChecker::Canonical => DiagnosticCheckerMode::Canonical,
        },
        comparison_scope: DiagnosticComparisonScope::FullArtifact,
        full_artifact_comparison: true,
        summary: DiagnosticScorecardSummary {
            discovered_cases: summary.discovered_cases,
            upstream_skipped_cases: summary.upstream_skipped_cases,
            selected_cases: summary.selected_cases,
            ..DiagnosticScorecardSummary::default()
        },
        variants: Vec::new(),
        semantic_artifacts: options
            .semantic_artifacts
            .then(SemanticArtifactScorecard::default),
    };
    for (case_path, baseline_index) in cases {
        for plan in prepare_diagnostic_case_variants(
            repository,
            &case_path,
            &baseline_sets[baseline_index],
            semantic_baseline_sets[baseline_index].as_ref(),
        )? {
            execute_diagnostic_variant(
                plan,
                repository,
                checker,
                &mut summary,
                &mut scorecard,
                writer,
            )?;
        }
    }
    if let Some(path) = &options.scorecard_json {
        scorecard.write_json(path)?;
    }
    writeln!(
        writer,
        "{summary} diagnostic_comparison=full-artifact exact_matches={} header_only_matches={} code_mismatches={} span_mismatches={} message_mismatches={} order_mismatches={} unsupported_details={} header_mismatches={} artifact_mismatches={} fatal_invariants={}",
        scorecard.summary.exact_matches,
        scorecard.summary.header_only_matches,
        scorecard.summary.code_mismatches,
        scorecard.summary.span_mismatches,
        scorecard.summary.message_mismatches,
        scorecard.summary.order_mismatches,
        scorecard.summary.unsupported_details,
        scorecard.summary.header_mismatches,
        scorecard.summary.artifact_mismatches,
        scorecard.summary.fatal_invariants,
    )?;
    Ok(summary)
}

fn capability_registry_contains(code: &str) -> bool {
    CAPABILITY_REGISTRY
        .lines()
        .skip(2)
        .filter(|line| !line.is_empty() && !line.starts_with('#'))
        .any(|line| line.split('\t').next() == Some(code))
}

fn comparison_frontier(
    status: DiagnosticVariantStatus,
    comparison: &DiagnosticArtifactComparison,
    checker_frontier: Option<(String, String)>,
) -> (
    DiagnosticVariantOutcomeClass,
    Option<DiagnosticFrontierBlocker>,
) {
    if let Some((code, detail)) = checker_frontier {
        return (
            DiagnosticVariantOutcomeClass::CheckerCapability,
            Some(DiagnosticFrontierBlocker {
                outcome_class: DiagnosticVariantOutcomeClass::CheckerCapability,
                code: Some(code),
                detail,
            }),
        );
    }
    if comparison.is_exact() {
        return (DiagnosticVariantOutcomeClass::Exact, None);
    }
    if let Some(detail) = comparison.unsupported_details.first() {
        return (
            DiagnosticVariantOutcomeClass::HarnessConfig,
            Some(DiagnosticFrontierBlocker {
                outcome_class: DiagnosticVariantOutcomeClass::HarnessConfig,
                code: None,
                detail: detail.clone(),
            }),
        );
    }
    let detail = comparison.first_difference.as_ref().map_or_else(
        || format!("diagnostic comparison ended with {status:?}"),
        |difference| {
            format!(
                "artifact line {} differs: expected {:?}, actual {:?}",
                difference.line, difference.expected, difference.actual
            )
        },
    );
    (
        DiagnosticVariantOutcomeClass::SupportedMismatch,
        Some(DiagnosticFrontierBlocker {
            outcome_class: DiagnosticVariantOutcomeClass::SupportedMismatch,
            code: None,
            detail,
        }),
    )
}

struct FatalVariantRecord<'a> {
    case_path: &'a Path,
    repository: &'a Path,
    variant: &'a OptionVariant,
    axes: &'a [String],
    variant_key: String,
    scorecard_case: String,
    expected_baseline: Option<String>,
    expected: &'a str,
    semantic_artifacts: Option<&'a SemanticArtifactPlan>,
    invariant_code: &'a str,
    detail: String,
}

fn retain_fatal_variant(
    summary: &mut RunnerSummary,
    scorecard: &mut DiagnosticScorecard,
    writer: &mut impl Write,
    record: FatalVariantRecord<'_>,
) -> io::Result<()> {
    summary.mismatched += 1;
    summary.diagnostic_failures += 1;
    scorecard.summary.executed_variants += 1;
    scorecard.summary.fatal_invariants += 1;
    let display_path = record
        .case_path
        .strip_prefix(record.repository)
        .unwrap_or(record.case_path)
        .display();
    let label = variant_label(record.variant, record.axes);
    writeln!(
        writer,
        "FATAL {display_path}{label}: {}: {}",
        record.invariant_code, record.detail
    )?;
    let semantic_artifacts = record
        .semantic_artifacts
        .map(|artifacts| semantic_variant_results(artifacts, None, record.repository))
        .transpose()?;
    if let Some(artifacts) = semantic_artifacts.as_ref() {
        record_semantic_variant(scorecard, artifacts);
    }
    scorecard.variants.push(DiagnosticVariantResult {
        variant_key: record.variant_key,
        case: record.scorecard_case,
        options: record.variant.values.clone(),
        expected_baseline: record.expected_baseline,
        comparison_scope: DiagnosticComparisonScope::FullArtifact,
        status: DiagnosticVariantStatus::FatalInvariant,
        outcome_class: DiagnosticVariantOutcomeClass::FatalInvariant,
        frontier_blocker: Some(DiagnosticFrontierBlocker {
            outcome_class: DiagnosticVariantOutcomeClass::FatalInvariant,
            code: Some(record.invariant_code.to_owned()),
            detail: record.detail,
        }),
        expected_header: parse_error_baseline_header(record.expected),
        actual_header: String::new(),
        mismatch_kinds: vec![DiagnosticArtifactMismatchKind::FatalInvariant],
        first_difference: None,
        unsupported_details: record.variant.unsupported_details.clone(),
        diagnostics: Vec::new(),
        semantic_artifacts,
    });
    Ok(())
}

fn relative_scorecard_path(repository: &Path, path: &Path) -> String {
    path.strip_prefix(repository)
        .unwrap_or(path)
        .to_string_lossy()
        .replace('\\', "/")
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

/// Returns the canonical, non-pretty diagnostics at the start of a TypeScript
/// `.errors.txt` baseline. Annotated source and related-information sections are
/// deliberately outside this first-pass comparison.
#[must_use]
pub fn parse_error_baseline_header(baseline: &str) -> String {
    let normalized = baseline
        .trim_start_matches('\u{feff}')
        .replace("\r\n", "\n")
        .replace('\r', "\n");
    let header_end = normalized.find("\n\n").unwrap_or(normalized.len());
    normalized[..header_end].trim_end_matches('\n').to_owned()
}

const HARNESS_NEW_LINE: &str = "\r\n";

#[derive(Clone, Debug, Default, Eq, PartialEq)]
struct RenderedDiagnosticArtifact {
    text: String,
    unsupported_details: Vec<String>,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct ParsedDiagnosticHeader {
    location: Option<String>,
    category: String,
    code: Option<u32>,
    message: String,
}

fn render_error_baseline(
    case: &Case,
    diagnostics: &[CompilationDiagnostic],
) -> RenderedDiagnosticArtifact {
    if diagnostics.is_empty() {
        return RenderedDiagnosticArtifact::default();
    }

    let mut ordered = diagnostics.iter().collect::<Vec<_>>();
    ordered.sort_by(|left, right| compare_compilation_diagnostics(left, right));
    let mut artifact = RenderedDiagnosticArtifact::default();
    for (index, pair) in ordered.windows(2).enumerate() {
        if diagnostic_primary_order_key(pair[0]) == diagnostic_primary_order_key(pair[1])
            && (pair[0].message != pair[1].message
                || compare_compilation_related_information(
                    pair[0].related_information.as_deref(),
                    pair[1].related_information.as_deref(),
                ) == Ordering::Equal)
        {
            artifact.unsupported_details.push(format!(
                "diagnostics {index} and {} have the same path/range/code ordering key; the checker does not expose message arguments or message chains required by the pinned sort key",
                index + 1
            ));
        }
    }
    let (unit_order, unit_order_issues) = error_baseline_unit_order(case);
    artifact.unsupported_details.extend(unit_order_issues);
    artifact.text = render_diagnostic_header(case, &ordered, &mut artifact.unsupported_details);
    artifact.text.push_str(HARNESS_NEW_LINE);
    artifact.text.push_str(HARNESS_NEW_LINE);

    let mut annotations = String::new();
    let mut first_annotation_line = true;
    for (index, diagnostic) in ordered.iter().enumerate() {
        if diagnostic.file_name.is_none() {
            append_annotated_diagnostic(
                &mut annotations,
                &mut first_annotation_line,
                diagnostic,
                index,
                case,
                &mut artifact.unsupported_details,
            );
        }
    }

    for unit_index in unit_order {
        let unit = &case.units[unit_index];
        let file_diagnostics = ordered
            .iter()
            .enumerate()
            .filter(|(_, diagnostic)| diagnostic_belongs_to_unit(case, diagnostic, unit_index))
            .collect::<Vec<_>>();
        append_annotation_line(
            &mut annotations,
            &mut first_annotation_line,
            &format!(
                "==== {} ({} errors) ====",
                baseline_unit_name(case, unit, unit_index),
                file_diagnostics.len()
            ),
        );
        annotate_source_unit(
            case,
            unit,
            unit_index,
            &file_diagnostics,
            &mut annotations,
            &mut first_annotation_line,
            &mut artifact.unsupported_details,
        );
    }

    for (index, diagnostic) in ordered.iter().enumerate() {
        if let Some(file_name) = diagnostic.file_name.as_deref()
            && !case
                .units
                .iter()
                .enumerate()
                .any(|(unit_index, _)| diagnostic_belongs_to_unit(case, diagnostic, unit_index))
            && !is_default_library_file(file_name)
            && !is_tsconfig_file(file_name)
        {
            artifact.unsupported_details.push(format!(
                "diagnostic {index} refers to non-input file {file_name:?}; no annotated source section can be rendered"
            ));
        }
    }

    artifact.text.push_str(&annotations);
    artifact.unsupported_details.sort();
    artifact.unsupported_details.dedup();
    artifact
}

fn error_baseline_unit_order(case: &Case) -> (Vec<usize>, Vec<String>) {
    let config_indices = case
        .units
        .iter()
        .enumerate()
        .filter_map(|(index, unit)| {
            unit.path
                .file_name()
                .and_then(|name| name.to_str())
                .is_some_and(|name| {
                    name.eq_ignore_ascii_case("tsconfig.json")
                        || name.eq_ignore_ascii_case("jsconfig.json")
                })
                .then_some(index)
        })
        .collect::<Vec<_>>();
    if let Some(&config_index) = config_indices.first() {
        let mut issues = project_configuration_unsupported_details(case);
        let roots = pinned_project_config(case)
            .map(|config| {
                let variant = expand_option_matrix(case)
                    .into_iter()
                    .next()
                    .unwrap_or_default();
                let options = fixture_compiler_options(case, &variant);
                project_root_unit_indices(case, &config, &options)
            })
            .unwrap_or_default();
        if config_indices.len() > 1 {
            issues.push(
                "multiple project configuration units make upstream tsConfigFiles ordering ambiguous"
                    .to_owned(),
            );
        }
        let mut order = vec![config_index];
        order.extend(roots.iter().copied());
        let remaining = case
            .units
            .iter()
            .enumerate()
            .map(|(index, _)| index)
            .filter(|index| !order.contains(index) && !roots.contains(index))
            .collect::<Vec<_>>();
        order.extend(remaining);
        return (order, issues);
    }

    let mut order = (0..case.units.len()).collect::<Vec<_>>();
    let implicit_references = case
        .directive_values("noImplicitReferences")
        .last()
        .is_some_and(|value| !value.is_empty())
        || case.units.last().is_some_and(unit_uses_implicit_references);
    if implicit_references && let Some(last) = order.pop() {
        order.insert(0, last);
    }
    (order, Vec::new())
}

fn render_diagnostic_header(
    case: &Case,
    diagnostics: &[&CompilationDiagnostic],
    unsupported_details: &mut Vec<String>,
) -> String {
    let mut output = String::new();
    for (index, diagnostic) in diagnostics.iter().enumerate() {
        if let Some(file_name) = diagnostic.file_name.as_deref() {
            match (diagnostic.source_text.as_ref(), diagnostic.range) {
                (Some(source), Some(range)) => {
                    let position = range.start.get() as usize;
                    if position > source.len()
                        || !source.as_scannable_str().is_char_boundary(position.min(source.len()))
                    {
                        unsupported_details.push(format!(
                            "diagnostic {index} has an invalid source position {position} for {file_name:?}"
                        ));
                    } else {
                        let display_name = baseline_diagnostic_file_name(case, file_name);
                        if is_default_library_file(&display_name) {
                            let _ = write!(output, "{display_name}(--,--): ");
                        } else {
                            let (line, column) = line_and_utf16_column(
                                source.as_scannable_str(),
                                position,
                            );
                            let _ = write!(output, "{display_name}({line},{column}): ");
                        }
                    }
                }
                _ => unsupported_details.push(format!(
                    "diagnostic {index} for {file_name:?} lacks source text or a range required for its header location"
                )),
            }
        }
        output.push_str(diagnostic_category_name(
            diagnostic.category,
            index,
            unsupported_details,
        ));
        if let Some(code) = diagnostic.code {
            let _ = write!(output, " TS{code}: ");
        } else {
            output.push_str(": ");
            unsupported_details.push(format!(
                "diagnostic {index} lacks the code required by an error baseline"
            ));
        }
        output.push_str(&normalize_to_crlf(&remove_test_path_prefixes(
            &diagnostic.message,
        )));
        output.push_str(HARNESS_NEW_LINE);
    }
    output
}

#[allow(clippy::too_many_lines)]
fn annotate_source_unit(
    case: &Case,
    unit: &Unit,
    unit_index: usize,
    diagnostics: &[(usize, &&CompilationDiagnostic)],
    output: &mut String,
    first_line: &mut bool,
    unsupported_details: &mut Vec<String>,
) {
    let source = unit.source_text.as_scannable_str();
    let mut line_starts = vec![0];
    line_starts.extend(
        source
            .bytes()
            .enumerate()
            .filter_map(|(index, byte)| (byte == b'\n').then_some(index + 1)),
    );
    let lines = source.split('\n').collect::<Vec<_>>();
    let mut marked = vec![false; diagnostics.len()];

    for (line_index, raw_line) in lines.iter().enumerate() {
        let line = raw_line.strip_suffix('\r').unwrap_or(raw_line);
        append_annotation_line(output, first_line, &format!("    {line}"));
        let this_line_start = line_starts[line_index];
        let next_line_start = if line_index + 1 == lines.len() {
            source.len()
        } else {
            line_starts[line_index + 1]
        };

        for (file_diagnostic_index, (diagnostic_index, diagnostic)) in
            diagnostics.iter().enumerate()
        {
            let Some(range) = diagnostic.range else {
                unsupported_details.push(format!(
                    "diagnostic {diagnostic_index} for {} lacks a source range",
                    baseline_unit_name(case, unit, unit_index)
                ));
                continue;
            };
            let start = range.start.get() as usize;
            let end = range.end.get() as usize;
            if start > end || start > source.len() || end > source.len() {
                unsupported_details.push(format!(
                    "diagnostic {diagnostic_index} has range {start}..{end} outside {} ({} bytes)",
                    baseline_unit_name(case, unit, unit_index),
                    source.len()
                ));
                continue;
            }
            if end >= this_line_start && (start < next_line_start || line_index + 1 == lines.len())
            {
                let consumed_before_line = this_line_start.saturating_sub(start);
                let length = end
                    .saturating_sub(start)
                    .saturating_sub(consumed_before_line);
                let squiggle_start = start.saturating_sub(this_line_start);
                if squiggle_start > line.len()
                    || !line.is_char_boundary(squiggle_start.min(line.len()))
                {
                    unsupported_details.push(format!(
                        "diagnostic {diagnostic_index} starts at a non-renderable byte offset on line {} of {}",
                        line_index + 1,
                        baseline_unit_name(case, unit, unit_index)
                    ));
                    continue;
                }
                let squiggle_end = squiggle_start
                    .saturating_add(length)
                    .min(line.len())
                    .max(squiggle_start);
                if !line.is_char_boundary(squiggle_end) {
                    unsupported_details.push(format!(
                        "diagnostic {diagnostic_index} ends at a non-renderable byte offset on line {} of {}",
                        line_index + 1,
                        baseline_unit_name(case, unit, unit_index)
                    ));
                    continue;
                }
                let prefix = line[..squiggle_start]
                    .chars()
                    .map(|character| {
                        if matches!(character, ' ' | '\t' | '\u{000b}' | '\u{000c}') {
                            character
                        } else {
                            ' '
                        }
                    })
                    .collect::<String>();
                let squiggles = "~".repeat(line[squiggle_start..squiggle_end].chars().count());
                append_annotation_line(output, first_line, &format!("    {prefix}{squiggles}"));
                if line_index + 1 == lines.len() || next_line_start > end {
                    append_annotated_diagnostic(
                        output,
                        first_line,
                        diagnostic,
                        *diagnostic_index,
                        case,
                        unsupported_details,
                    );
                    marked[file_diagnostic_index] = true;
                }
            }
        }
    }

    for ((diagnostic_index, _), was_marked) in diagnostics.iter().zip(marked) {
        if !was_marked {
            unsupported_details.push(format!(
                "diagnostic {diagnostic_index} could not be annotated in {}",
                baseline_unit_name(case, unit, unit_index)
            ));
        }
    }
}

fn append_annotated_diagnostic(
    output: &mut String,
    first_line: &mut bool,
    diagnostic: &CompilationDiagnostic,
    diagnostic_index: usize,
    case: &Case,
    unsupported_details: &mut Vec<String>,
) {
    let category =
        diagnostic_category_name(diagnostic.category, diagnostic_index, unsupported_details);
    let code = diagnostic.code.map_or_else(
        || {
            unsupported_details.push(format!(
                "diagnostic {diagnostic_index} lacks the code required by an annotated error"
            ));
            String::new()
        },
        |code| format!(" TS{code}"),
    );
    for line in
        normalize_to_crlf(&remove_test_path_prefixes(&diagnostic.message)).split(HARNESS_NEW_LINE)
    {
        if !line.is_empty() {
            append_annotation_line(output, first_line, &format!("!!! {category}{code}: {line}"));
        }
    }

    if let Some(related_information) = diagnostic.related_information.as_ref() {
        for (related_index, related) in related_information.iter().enumerate() {
            let location = match (
                related.file_name.as_deref(),
                related.source_text.as_ref(),
                related.range,
            ) {
                (Some(file_name), Some(source), Some(range)) => {
                    let display_name = baseline_diagnostic_file_name(case, file_name);
                    if is_default_library_file(&display_name) {
                        format!(" {display_name}:--:--")
                    } else {
                        let position = range.start.get() as usize;
                        if position > source.len()
                            || !source
                                .as_scannable_str()
                                .is_char_boundary(position.min(source.len()))
                        {
                            unsupported_details.push(format!(
                                "related diagnostic {diagnostic_index}.{related_index} has an invalid source position"
                            ));
                            String::new()
                        } else {
                            let (line, column) =
                                line_and_utf16_column(source.as_scannable_str(), position);
                            format!(" {display_name}:{line}:{column}")
                        }
                    }
                }
                (None, _, _) => String::new(),
                _ => {
                    unsupported_details.push(format!(
                        "related diagnostic {diagnostic_index}.{related_index} lacks source text or a range for its location"
                    ));
                    String::new()
                }
            };
            let code = related.code.map_or_else(
                || {
                    unsupported_details.push(format!(
                        "related diagnostic {diagnostic_index}.{related_index} lacks a code"
                    ));
                    String::new()
                },
                |code| format!(" TS{code}"),
            );
            append_annotation_line(
                output,
                first_line,
                &format!(
                    "!!! related{code}{location}: {}",
                    normalize_to_crlf(&remove_test_path_prefixes(&related.message))
                ),
            );
        }
    }
}

fn append_annotation_line(output: &mut String, first_line: &mut bool, line: &str) {
    if *first_line {
        *first_line = false;
    } else {
        output.push_str(HARNESS_NEW_LINE);
    }
    output.push_str(line);
}

fn compare_compilation_diagnostics(
    left: &CompilationDiagnostic,
    right: &CompilationDiagnostic,
) -> Ordering {
    left.file_name
        .as_deref()
        .unwrap_or_default()
        .cmp(right.file_name.as_deref().unwrap_or_default())
        .then_with(|| {
            left.range
                .map(|range| range.start)
                .cmp(&right.range.map(|range| range.start))
        })
        .then_with(|| {
            left.range
                .map(|range| range.end)
                .cmp(&right.range.map(|range| range.end))
        })
        .then_with(|| left.code.cmp(&right.code))
        .then_with(|| left.message.cmp(&right.message))
        .then_with(|| {
            compare_compilation_related_information(
                left.related_information.as_deref(),
                right.related_information.as_deref(),
            )
        })
}

fn compare_compilation_related_information(
    left: Option<&[CompilationRelatedInformation]>,
    right: Option<&[CompilationRelatedInformation]>,
) -> Ordering {
    let left = left.unwrap_or_default();
    let right = right.unwrap_or_default();
    right.len().cmp(&left.len()).then_with(|| {
        left.iter()
            .zip(right)
            .map(|(left, right)| {
                left.file_name
                    .as_deref()
                    .unwrap_or_default()
                    .cmp(right.file_name.as_deref().unwrap_or_default())
                    .then_with(|| {
                        left.range
                            .map(|range| range.start)
                            .cmp(&right.range.map(|range| range.start))
                    })
                    .then_with(|| {
                        left.range
                            .map(|range| range.end)
                            .cmp(&right.range.map(|range| range.end))
                    })
                    .then_with(|| left.code.cmp(&right.code))
                    .then_with(|| left.message.cmp(&right.message))
            })
            .find(|ordering| *ordering != Ordering::Equal)
            .unwrap_or(Ordering::Equal)
    })
}

fn diagnostic_primary_order_key(
    diagnostic: &CompilationDiagnostic,
) -> (&str, Option<TextRange>, Option<u32>) {
    (
        diagnostic.file_name.as_deref().unwrap_or_default(),
        diagnostic.range,
        diagnostic.code,
    )
}

fn diagnostic_belongs_to_unit(
    case: &Case,
    diagnostic: &CompilationDiagnostic,
    unit_index: usize,
) -> bool {
    let Some(file_name) = diagnostic.file_name.as_deref() else {
        return false;
    };
    let unit = &case.units[unit_index];
    let virtual_path = virtual_unit_path(case, unit, unit_index);
    normalize_comparison_path(file_name)
        .eq_ignore_ascii_case(&normalize_comparison_path(&virtual_path))
        || baseline_diagnostic_file_name(case, file_name)
            .eq_ignore_ascii_case(&baseline_unit_name(case, unit, unit_index))
}

fn normalize_comparison_path(path: &str) -> String {
    ts_path::normalize_path(&path.replace('\\', "/"))
}

fn baseline_unit_name(case: &Case, unit: &Unit, unit_index: usize) -> String {
    let name = if unit.path == case.path {
        unit.path
            .file_name()
            .and_then(|name| name.to_str())
            .map_or_else(|| format!("unit{unit_index}.ts"), str::to_owned)
    } else {
        unit.path.to_string_lossy().replace('\\', "/")
    };
    remove_test_path_prefixes(&name)
}

fn baseline_diagnostic_file_name(case: &Case, file_name: &str) -> String {
    if let Some((unit_index, unit)) = case.units.iter().enumerate().find(|(unit_index, _)| {
        normalize_comparison_path(file_name).eq_ignore_ascii_case(&normalize_comparison_path(
            &virtual_unit_path(case, &case.units[*unit_index], *unit_index),
        ))
    }) {
        return baseline_unit_name(case, unit, unit_index);
    }
    let name = remove_test_path_prefixes(&file_name.replace('\\', "/"));
    name.strip_prefix("/case/").unwrap_or(&name).to_owned()
}

fn remove_test_path_prefixes(text: &str) -> String {
    [
        ("/.ts/", ""),
        ("/.lib/", ""),
        ("/.src/", ""),
        ("bundled:///libs/", ""),
        ("file:///./ts/", "file:///"),
        ("file:///./lib/", "file:///"),
        ("file:///./src/", "file:///"),
    ]
    .into_iter()
    .fold(text.to_owned(), |text, (prefix, replacement)| {
        text.replace(prefix, replacement)
    })
}

fn is_default_library_file(file_name: &str) -> bool {
    file_name
        .rsplit(['/', '\\'])
        .next()
        .is_some_and(|base| base.starts_with("lib.") && base.ends_with(".d.ts"))
}

fn is_tsconfig_file(file_name: &str) -> bool {
    let lower = file_name.to_ascii_lowercase();
    lower.contains("tsconfig") && lower.contains("json")
}

fn diagnostic_category_name(
    category: Option<CompilationDiagnosticCategory>,
    diagnostic_index: usize,
    unsupported_details: &mut Vec<String>,
) -> &'static str {
    match category {
        Some(CompilationDiagnosticCategory::Error) => "error",
        Some(CompilationDiagnosticCategory::Warning) => "warning",
        Some(CompilationDiagnosticCategory::Suggestion) => "suggestion",
        Some(CompilationDiagnosticCategory::Message) => "message",
        None => {
            unsupported_details.push(format!(
                "diagnostic {diagnostic_index} lacks a category required by an error baseline"
            ));
            "unknown"
        }
    }
}

fn line_and_utf16_column(source: &str, byte_position: usize) -> (usize, usize) {
    let position = byte_position.min(source.len());
    let prefix = &source[..position];
    let line = prefix.bytes().filter(|byte| *byte == b'\n').count() + 1;
    let line_start = prefix.rfind('\n').map_or(0, |index| index + 1);
    let column = prefix[line_start..].encode_utf16().count() + 1;
    (line, column)
}

fn normalize_to_crlf(text: &str) -> String {
    text.replace("\r\n", "\n")
        .replace('\r', "\n")
        .replace('\n', HARNESS_NEW_LINE)
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
struct DiagnosticArtifactComparison {
    mismatch_kinds: Vec<DiagnosticArtifactMismatchKind>,
    first_difference: Option<DiagnosticArtifactDifference>,
    unsupported_details: Vec<String>,
}

impl DiagnosticArtifactComparison {
    fn is_exact(&self) -> bool {
        self.mismatch_kinds.is_empty() && self.unsupported_details.is_empty()
    }

    fn status(&self) -> DiagnosticVariantStatus {
        if self.is_exact() {
            return DiagnosticVariantStatus::ExactMatch;
        }
        if !self.unsupported_details.is_empty()
            || self
                .mismatch_kinds
                .contains(&DiagnosticArtifactMismatchKind::UnsupportedDetail)
        {
            return DiagnosticVariantStatus::UnsupportedDetail;
        }
        for (kind, status) in [
            (
                DiagnosticArtifactMismatchKind::Order,
                DiagnosticVariantStatus::OrderMismatch,
            ),
            (
                DiagnosticArtifactMismatchKind::Code,
                DiagnosticVariantStatus::CodeMismatch,
            ),
            (
                DiagnosticArtifactMismatchKind::Span,
                DiagnosticVariantStatus::SpanMismatch,
            ),
            (
                DiagnosticArtifactMismatchKind::Message,
                DiagnosticVariantStatus::MessageMismatch,
            ),
            (
                DiagnosticArtifactMismatchKind::HeaderOnly,
                DiagnosticVariantStatus::HeaderOnlyMatch,
            ),
            (
                DiagnosticArtifactMismatchKind::Header,
                DiagnosticVariantStatus::HeaderMismatch,
            ),
        ] {
            if self.mismatch_kinds.contains(&kind) {
                return status;
            }
        }
        DiagnosticVariantStatus::ArtifactMismatch
    }
}

fn compare_diagnostic_artifacts(
    expected: &str,
    actual: &RenderedDiagnosticArtifact,
    diagnostics: &[CompilationDiagnostic],
) -> DiagnosticArtifactComparison {
    let mut comparison = DiagnosticArtifactComparison {
        unsupported_details: actual.unsupported_details.clone(),
        ..DiagnosticArtifactComparison::default()
    };
    if expected.contains("!!! related TS")
        && !actual.text.contains("!!! related TS")
        && diagnostics
            .iter()
            .any(|diagnostic| diagnostic.related_information.is_none())
    {
        comparison.unsupported_details.push(
            "the expected artifact contains related information, but the checker did not expose related diagnostics"
                .to_owned(),
        );
    }
    comparison.unsupported_details.sort();
    comparison.unsupported_details.dedup();

    if expected == actual.text && comparison.unsupported_details.is_empty() {
        return comparison;
    }
    if !comparison.unsupported_details.is_empty() {
        comparison
            .mismatch_kinds
            .push(DiagnosticArtifactMismatchKind::UnsupportedDetail);
    }
    if expected != actual.text {
        let (line, expected_line, actual_line) = first_different_line(expected, &actual.text);
        comparison.first_difference = Some(DiagnosticArtifactDifference {
            line,
            expected: expected_line.to_owned(),
            actual: actual_line.to_owned(),
        });
    }

    let expected_header = parse_error_baseline_header(expected);
    let actual_header = parse_error_baseline_header(&actual.text);
    if expected_header == actual_header {
        let expected_squiggles = annotated_squiggles(expected);
        let actual_squiggles = annotated_squiggles(&actual.text);
        if expected_squiggles == actual_squiggles {
            let expected_annotations = annotated_diagnostic_lines(expected);
            let actual_annotations = annotated_diagnostic_lines(&actual.text);
            if same_annotated_diagnostics_except(&expected_annotations, &actual_annotations, "code")
            {
                comparison
                    .mismatch_kinds
                    .push(DiagnosticArtifactMismatchKind::Code);
            } else if same_annotated_diagnostics_except(
                &expected_annotations,
                &actual_annotations,
                "message",
            ) {
                comparison
                    .mismatch_kinds
                    .push(DiagnosticArtifactMismatchKind::Message);
            } else {
                comparison
                    .mismatch_kinds
                    .push(DiagnosticArtifactMismatchKind::HeaderOnly);
            }
        } else {
            comparison
                .mismatch_kinds
                .push(DiagnosticArtifactMismatchKind::Span);
        }
    } else {
        let expected_records = parse_diagnostic_headers(&expected_header);
        let actual_records = parse_diagnostic_headers(&actual_header);
        if expected_records.len() == actual_records.len()
            && !expected_records.is_empty()
            && sorted_headers(&expected_records) == sorted_headers(&actual_records)
        {
            comparison
                .mismatch_kinds
                .push(DiagnosticArtifactMismatchKind::Order);
        } else if headers_equal_except(&expected_records, &actual_records, "code") {
            comparison
                .mismatch_kinds
                .push(DiagnosticArtifactMismatchKind::Code);
        } else if headers_equal_except(&expected_records, &actual_records, "location") {
            comparison
                .mismatch_kinds
                .push(DiagnosticArtifactMismatchKind::Span);
        } else if headers_equal_except(&expected_records, &actual_records, "message") {
            comparison
                .mismatch_kinds
                .push(DiagnosticArtifactMismatchKind::Message);
        } else {
            comparison
                .mismatch_kinds
                .push(DiagnosticArtifactMismatchKind::Header);
        }
    }
    if comparison.mismatch_kinds.is_empty() {
        comparison
            .mismatch_kinds
            .push(DiagnosticArtifactMismatchKind::Artifact);
    }
    comparison.mismatch_kinds.sort_by_key(|kind| *kind as u8);
    comparison.mismatch_kinds.dedup();
    comparison
}

fn parse_diagnostic_headers(header: &str) -> Vec<ParsedDiagnosticHeader> {
    let mut records = Vec::<ParsedDiagnosticHeader>::new();
    for line in header.lines() {
        if let Some(record) = parse_diagnostic_header_line(line) {
            records.push(record);
        } else if let Some(record) = records.last_mut() {
            record.message.push('\n');
            record.message.push_str(line);
        }
    }
    records
}

fn parse_diagnostic_header_line(line: &str) -> Option<ParsedDiagnosticHeader> {
    let code_marker = line.rfind(" TS")?;
    let after_marker = &line[code_marker + 3..];
    let (code, message) = after_marker.split_once(": ")?;
    let code = code.parse().ok()?;
    let prefix = &line[..code_marker];
    let (location, category) = prefix.rsplit_once(": ").map_or_else(
        || (None, prefix),
        |(location, category)| (Some(location.to_owned()), category),
    );
    Some(ParsedDiagnosticHeader {
        location,
        category: category.to_owned(),
        code: Some(code),
        message: message.to_owned(),
    })
}

fn sorted_headers(headers: &[ParsedDiagnosticHeader]) -> Vec<ParsedDiagnosticHeader> {
    let mut headers = headers.to_vec();
    headers.sort();
    headers
}

fn headers_equal_except(
    expected: &[ParsedDiagnosticHeader],
    actual: &[ParsedDiagnosticHeader],
    excluded: &str,
) -> bool {
    expected.len() == actual.len()
        && !expected.is_empty()
        && expected.iter().zip(actual).all(|(expected, actual)| {
            (excluded == "location" || expected.location == actual.location)
                && (excluded == "code" || expected.code == actual.code)
                && expected.category == actual.category
                && (excluded == "message" || expected.message == actual.message)
        })
        && expected != actual
}

fn annotated_squiggles(artifact: &str) -> Vec<String> {
    normalize_diagnostic_header_newlines(artifact)
        .lines()
        .filter(|line| {
            line.contains('~')
                && line
                    .chars()
                    .all(|character| matches!(character, ' ' | '\t' | '~'))
        })
        .map(str::to_owned)
        .collect()
}

fn annotated_diagnostic_lines(artifact: &str) -> Vec<String> {
    normalize_diagnostic_header_newlines(artifact)
        .lines()
        .filter(|line| line.starts_with("!!! "))
        .map(str::to_owned)
        .collect()
}

fn same_annotated_diagnostics_except(
    expected: &[String],
    actual: &[String],
    excluded: &str,
) -> bool {
    if expected.len() != actual.len() || expected.is_empty() || expected == actual {
        return false;
    }
    expected.iter().zip(actual).all(|(expected, actual)| {
        let expected = parse_annotated_diagnostic(expected);
        let actual = parse_annotated_diagnostic(actual);
        match (expected, actual) {
            (Some(expected), Some(actual)) => {
                expected.0 == actual.0
                    && (excluded == "code" || expected.1 == actual.1)
                    && (excluded == "message" || expected.2 == actual.2)
            }
            _ => false,
        }
    })
}

fn parse_annotated_diagnostic(line: &str) -> Option<(&str, Option<u32>, &str)> {
    let content = line.strip_prefix("!!! ")?;
    let code_marker = content.find(" TS")?;
    let label = &content[..code_marker];
    let (code_and_location, message) = content[code_marker + 3..].split_once(": ")?;
    let code = code_and_location
        .split([' ', ':'])
        .next()
        .and_then(|code| code.parse().ok());
    Some((label, code, message))
}

fn normalize_diagnostic_header_newlines(text: &str) -> String {
    text.replace("\r\n", "\n").replace('\r', "\n")
}

/// Parses TypeScript's `//// [file]` baseline sections, preserving section
/// contents exactly apart from the marker line itself.
#[must_use]
pub fn parse_baseline_sections(baseline: &str) -> BTreeMap<String, String> {
    parse_baseline_section_list(baseline).into_iter().collect()
}

fn parse_baseline_section_list(baseline: &str) -> Vec<(String, String)> {
    let mut normalized = String::with_capacity(baseline.len());
    let mut offset = 0;
    for (index, _) in baseline.match_indices("//// [") {
        normalized.push_str(&baseline[offset..index]);
        if index > 0 && !matches!(baseline.as_bytes()[index - 1], b'\n' | b'\r') {
            normalized.push('\n');
        }
        offset = index;
    }
    normalized.push_str(&baseline[offset..]);

    let mut sections = Vec::new();
    let mut current_name: Option<String> = None;
    let mut current_text = String::new();
    for line in normalized.split_inclusive('\n') {
        let marker = line.trim_end_matches(['\r', '\n']);
        if marker.starts_with("!!!! File ") && marker.contains("noCheck emit") {
            break;
        }
        if let Some(name) = marker
            .strip_prefix("//// [")
            .and_then(|marker| marker.rsplit_once(']').map(|(name, _)| name))
        {
            if let Some(name) = current_name.replace(name.to_owned()) {
                sections.push((name, std::mem::take(&mut current_text)));
            }
        } else if current_name.is_some() {
            current_text.push_str(line);
        }
    }
    if let Some(name) = current_name {
        sections.push((name, current_text));
    }
    sections
}

/// Expands frozen-pin compiler variation directives as a Cartesian product.
///
/// This mirrors `harnessutil.GetFileBasedTestConfigurations`: only boolean and
/// enum options in the pinned compiler's vary-by set expand, `*` uses the
/// pinned option declaration order, aliases deduplicate by semantic value, and
/// `-`/`!` exclusions remove normalized values. Variants that Rust cannot apply
/// remain visible with an explicit unsupported reason.
#[must_use]
pub fn expand_option_matrix(case: &Case) -> Vec<OptionVariant> {
    let (option_values, mut unsupported_details) = expanded_option_values(case);
    let variation_count = option_values
        .values()
        .map(Vec::len)
        .try_fold(1_usize, usize::checked_mul)
        .unwrap_or(usize::MAX);
    if variation_count > 25 {
        unsupported_details.push(format!(
            "pinned harness variation cap exceeded: {variation_count} configurations (maximum 25)"
        ));
        let mut variant = OptionVariant {
            values: option_values
                .into_iter()
                .filter_map(|(name, values)| values.into_iter().next().map(|value| (name, value)))
                .collect(),
            unsupported_details,
        };
        finalize_option_variant(case, &mut variant);
        return vec![variant];
    }

    let mut variants = vec![OptionVariant {
        values: BTreeMap::new(),
        unsupported_details,
    }];
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
    for variant in &mut variants {
        finalize_option_variant(case, variant);
    }
    variants
}

fn expanded_option_values(case: &Case) -> (BTreeMap<String, Vec<String>>, Vec<String>) {
    let mut option_values = BTreeMap::<String, Vec<String>>::new();
    let mut unsupported_details = pinned_directive_unsupported_details(case);
    for &name in COMPILER_OPTION_NAMES {
        let Some(raw_value) = case.directive_values(name).last().map(pinned_setting_value) else {
            continue;
        };
        let values = if is_varying_boolean_option(name) || enum_option_values(name).is_some() {
            if raw_value.is_empty() {
                continue;
            }
            match split_pinned_option_values(raw_value, name) {
                Ok(values) => values,
                Err(detail) => {
                    unsupported_details.push(detail);
                    vec![raw_value.to_owned()]
                }
            }
        } else {
            if is_non_varying_boolean_option(name)
                && !matches!(raw_value.to_ascii_lowercase().as_str(), "true" | "false")
            {
                unsupported_details.push(format!(
                    "invalid boolean value {raw_value:?} for pinned compiler option {name}"
                ));
            }
            vec![raw_value.to_owned()]
        };
        let suppressed_unused_labels = name.eq_ignore_ascii_case("allowUnusedLabels")
            && values
                .iter()
                .all(|value| value.eq_ignore_ascii_case("true"));
        if !rust_applies_compiler_option(name) && !suppressed_unused_labels {
            unsupported_details.push(format!(
                "compiler option {name} is configured as {raw_value:?}, but Rust does not apply it"
            ));
        }
        if name.eq_ignore_ascii_case("pretty") && raw_value.eq_ignore_ascii_case("true") {
            unsupported_details.push(
                "pretty diagnostic baselines are not implemented; non-pretty output cannot count as exact"
                    .to_owned(),
            );
        }
        option_values.insert(name.to_owned(), values);
    }
    for &name in LIST_OPTION_NAMES {
        if let Some(value) = case.directive_values(name).last().map(pinned_setting_value) {
            option_values.insert(name.to_owned(), vec![value.to_owned()]);
        }
    }
    unsupported_details.extend(project_configuration_unsupported_details(case));
    unsupported_details.sort();
    unsupported_details.dedup();
    (option_values, unsupported_details)
}

fn pinned_setting_value(value: &str) -> &str {
    value.strip_suffix(';').unwrap_or(value)
}

fn is_non_varying_boolean_option(name: &str) -> bool {
    ["incremental", "noCheck", "pretty"]
        .iter()
        .any(|option| name.eq_ignore_ascii_case(option))
}

fn pinned_directive_unsupported_details(case: &Case) -> Vec<String> {
    let mut details = Vec::new();
    let mut seen = BTreeSet::new();
    // The pinned harness applies the last setting with a given name.
    for directive in case.directives.iter().rev() {
        let lower = directive.name.to_ascii_lowercase();
        if !seen.insert(lower.clone())
            || COMPILER_OPTION_NAMES
                .iter()
                .chain(LIST_OPTION_NAMES)
                .any(|name| name.eq_ignore_ascii_case(&directive.name))
            || matches!(
                lower.as_str(),
                "filename"
                    | "currentdirectory"
                    | "fullemitpaths"
                    | "ignoredeprecations"
                    | "noimplicitreferences"
                    | "notypesandsymbols"
                    | "traceresolution"
                    | "reportdiagnostics"
            )
        {
            continue;
        }

        let reason = match lower.as_str() {
            "capturesuggestions" => {
                "the pinned harness adds suggestion diagnostics, which Rust does not collect"
            }
            "link" => {
                if directive
                    .value
                    .split_once("->")
                    .is_some_and(|(source, target)| {
                        !source.trim().is_empty() && !target.trim().is_empty()
                    })
                {
                    continue;
                }
                "the pinned harness requires a nonempty source -> target directory link"
            }
            "symlink" => {
                if directive
                    .value
                    .split(',')
                    .any(|alias| !alias.trim().is_empty())
                {
                    continue;
                }
                "the pinned harness requires a nonempty file symlink target"
            }
            "typescriptversion" => "version-specific harness semantics are not proven exact",
            "usecasesensitivefilenames" => {
                let value = pinned_setting_value(&directive.value);
                if value.eq_ignore_ascii_case("true") || value.eq_ignore_ascii_case("false") {
                    continue;
                }
                "the pinned harness requires a boolean useCaseSensitiveFileNames value"
            }
            _ => "the pinned compiler or harness setting is not modeled by Rust",
        };
        details.push(format!("@{}: {reason}", directive.name));
    }

    for name in [
        "noImplicitReferences",
        "fullEmitPaths",
        "noTypesAndSymbols",
        "traceResolution",
        "reportDiagnostics",
    ] {
        if let Some(value) = case.directive_values(name).last().map(pinned_setting_value)
            && !matches!(value.to_ascii_lowercase().as_str(), "true" | "false")
        {
            details.push(format!(
                "invalid boolean value {value:?} for pinned harness/compiler option {name}"
            ));
        }
    }
    details
}

fn finalize_option_variant(case: &Case, variant: &mut OptionVariant) {
    let skip_details = pinned_skip_unsupported_details(case, variant);
    variant.unsupported_details.extend(skip_details);
    variant.unsupported_details.sort();
    variant.unsupported_details.dedup();
}

fn pinned_skip_unsupported_details(case: &Case, variant: &OptionVariant) -> Vec<String> {
    let mut details = Vec::new();
    let value = |name: &str| effective_option_value(case, variant, name);

    if value("module").is_some_and(|module| {
        matches!(
            module.to_ascii_lowercase().as_str(),
            "amd" | "umd" | "system"
        )
    }) {
        details.push("pinned Go harness skips AMD, UMD, and System module variants".to_owned());
    }
    if value("moduleResolution").is_some_and(|resolution| {
        matches!(
            resolution.to_ascii_lowercase().as_str(),
            "node" | "node10" | "classic"
        )
    }) {
        details.push("pinned Go harness skips node10 and classic module resolution".to_owned());
    }
    for (name, label) in [
        ("esModuleInterop", "esModuleInterop=false"),
        (
            "allowSyntheticDefaultImports",
            "allowSyntheticDefaultImports=false",
        ),
        ("alwaysStrict", "alwaysStrict=false"),
    ] {
        if value(name).is_some_and(|configured| configured.eq_ignore_ascii_case("false")) {
            details.push(format!("pinned Go harness skips {label}"));
        }
    }
    for name in ["baseUrl", "outFile"] {
        if value(name).is_some_and(|configured| !configured.trim().is_empty()) {
            details.push(format!("pinned Go harness skips nonempty {name}"));
        }
    }
    if value("target").is_some_and(|target| target.eq_ignore_ascii_case("es5")) {
        details.push("pinned Go harness skips target ES5".to_owned());
    }
    details
}

fn effective_option_value(case: &Case, variant: &OptionVariant, name: &str) -> Option<String> {
    variant
        .values
        .iter()
        .find_map(|(configured_name, value)| {
            configured_name
                .eq_ignore_ascii_case(name)
                .then(|| value.clone())
        })
        .or_else(|| {
            pinned_project_config(case).and_then(|config| {
                config
                    .compiler_options
                    .into_iter()
                    .find(|(configured_name, _)| configured_name.eq_ignore_ascii_case(name))
                    .and_then(|(_, value)| match value {
                        ts_config::JsonValue::String(value) => Some(value),
                        ts_config::JsonValue::Bool(value) => Some(value.to_string()),
                        ts_config::JsonValue::Number(value) => Some(value.as_str().to_owned()),
                        _ => None,
                    })
            })
        })
}

fn split_pinned_option_values(raw_value: &str, option: &str) -> Result<Vec<String>, String> {
    let mut star = false;
    let mut includes = Vec::new();
    let mut excludes = Vec::new();
    for part in raw_value
        .split(',')
        .map(str::trim)
        .filter(|part| !part.is_empty())
    {
        if part == "*" {
            star = true;
        } else if let Some(excluded) = part.strip_prefix(['-', '!']) {
            excludes.push(excluded);
        } else {
            includes.push(part);
        }
    }

    let mut values = Vec::<(String, String)>::new();
    for include in includes {
        let Some(identity) = normalized_option_value(option, include) else {
            return Err(format!(
                "unknown value {include:?} for pinned compiler option {option}"
            ));
        };
        if !values.iter().any(|(existing, _)| *existing == identity) {
            values.push((identity, include.to_owned()));
        }
    }
    if star {
        let all_values = if is_varying_boolean_option(option) {
            BOOLEAN_OPTION_VALUES
        } else {
            enum_option_values(option).unwrap_or_default()
        };
        for &(spelling, identity) in all_values {
            if !values.iter().any(|(existing, _)| existing == identity) {
                values.push((identity.to_owned(), spelling.to_owned()));
            }
        }
    }
    for exclude in excludes {
        if let Some(identity) = normalized_option_value(option, exclude) {
            values.retain(|(existing, _)| *existing != identity);
        }
    }
    if values.is_empty() {
        return Err(format!(
            "variations in pinned compiler option @{option}: {raw_value} resulted in an empty set"
        ));
    }
    Ok(values.into_iter().map(|(_, spelling)| spelling).collect())
}

fn normalized_option_value(option: &str, value: &str) -> Option<String> {
    if is_varying_boolean_option(option) {
        return matches!(value.to_ascii_lowercase().as_str(), "true" | "false")
            .then(|| value.to_ascii_lowercase());
    }
    enum_option_values(option)?
        .iter()
        .find_map(|(spelling, identity)| {
            spelling
                .eq_ignore_ascii_case(value)
                .then(|| (*identity).to_owned())
        })
}

fn is_varying_boolean_option(name: &str) -> bool {
    VARYING_BOOLEAN_OPTION_NAMES
        .iter()
        .any(|option| name.eq_ignore_ascii_case(option))
}

fn enum_option_values(name: &str) -> Option<&'static [(&'static str, &'static str)]> {
    if name.eq_ignore_ascii_case("target") {
        Some(TARGET_OPTION_VALUES)
    } else if name.eq_ignore_ascii_case("module") {
        Some(MODULE_OPTION_VALUES)
    } else if name.eq_ignore_ascii_case("moduleResolution") {
        Some(MODULE_RESOLUTION_OPTION_VALUES)
    } else if name.eq_ignore_ascii_case("moduleDetection") {
        Some(MODULE_DETECTION_OPTION_VALUES)
    } else if name.eq_ignore_ascii_case("jsx") {
        Some(JSX_OPTION_VALUES)
    } else if name.eq_ignore_ascii_case("newLine") {
        Some(NEW_LINE_OPTION_VALUES)
    } else {
        None
    }
}

fn rust_applies_compiler_option(name: &str) -> bool {
    RUST_APPLIED_COMPILER_OPTION_NAMES
        .iter()
        .any(|option| name.eq_ignore_ascii_case(option))
}

/// Compares compiler outputs with JavaScript and declaration baseline sections.
#[must_use]
pub fn compare_emitted_output_sections(
    outputs: &BTreeMap<String, String>,
    baseline: &str,
) -> BaselineComparison {
    compare_emitted_output_sections_excluding(outputs, baseline, &BTreeSet::new(), &[], false)
}

fn compare_case_emitted_output_sections(
    outputs: &BTreeMap<String, String>,
    baseline: &str,
    case: &Case,
    variant: &OptionVariant,
) -> BaselineComparison {
    let baseline_sections = parse_baseline_sections(baseline)
        .into_iter()
        .map(|(name, text)| {
            (
                normalize_section_name(&name),
                normalize_emitted_section(&text),
            )
        })
        .collect::<BTreeMap<_, _>>();
    let declaration_unit_basename_counts = case
        .units
        .iter()
        .filter_map(|unit| {
            let path = unit.path.to_string_lossy().replace('\\', "/");
            ts_path::is_declaration_file(&path)
                .then(|| section_basename(&normalize_section_name(&path)).to_owned())
        })
        .fold(BTreeMap::<String, usize>::new(), |mut counts, name| {
            *counts.entry(name).or_default() += 1;
            counts
        });
    let mut excluded_expected = BTreeSet::new();
    for unit in &case.units {
        let path = unit.path.to_string_lossy().replace('\\', "/");
        if !ts_path::is_declaration_file(&path) {
            continue;
        }
        let name = normalize_section_name(&path);
        let basename = section_basename(&name);
        let source = normalize_input_section(unit.source_text.as_scannable_str());
        let candidates = [
            baseline_sections
                .contains_key(&name)
                .then_some(name.as_str()),
            (declaration_unit_basename_counts.get(basename) == Some(&1)
                && baseline_sections.contains_key(basename))
            .then_some(basename),
        ];
        for candidate in candidates.into_iter().flatten() {
            if baseline_sections.get(candidate) == Some(&source) {
                excluded_expected.insert(candidate.to_owned());
            }
        }
    }
    let emit_declaration_only = variant.values.iter().any(|(name, value)| {
        name.eq_ignore_ascii_case("emitDeclarationOnly") && value.eq_ignore_ascii_case("true")
    });
    if emit_declaration_only {
        excluded_expected.extend(
            baseline_sections
                .keys()
                .filter(|name| is_javascript_output_section(name))
                .cloned(),
        );
    }
    let legacy_bom_baseline_omits_javascript = case
        .directive_values("emitBOM")
        .any(|value| value.eq_ignore_ascii_case("true"))
        && !baseline_sections
            .keys()
            .any(|name| is_javascript_output_section(name));
    let filtered_outputs = legacy_bom_baseline_omits_javascript.then(|| {
        outputs
            .iter()
            .filter(|(name, _)| !is_javascript_output_section(name))
            .map(|(name, text)| (name.clone(), text.clone()))
            .collect::<BTreeMap<_, _>>()
    });
    let outputs = filtered_outputs.as_ref().unwrap_or(outputs);
    let input_echoes = case
        .units
        .iter()
        .map(|unit| {
            let path = unit.path.to_string_lossy().replace('\\', "/");
            (
                normalize_section_name(&path),
                normalize_input_section(unit.source_text.as_scannable_str()),
            )
        })
        .collect::<Vec<_>>();
    let require_full_paths = case
        .directive_values("fullEmitPaths")
        .last()
        .is_some_and(|value| value.eq_ignore_ascii_case("true"));
    compare_emitted_output_sections_excluding(
        outputs,
        baseline,
        &excluded_expected,
        &input_echoes,
        require_full_paths,
    )
}

fn compare_emitted_output_sections_excluding(
    outputs: &BTreeMap<String, String>,
    baseline: &str,
    excluded_expected: &BTreeSet<String>,
    input_echoes: &[(String, String)],
    require_full_paths: bool,
) -> BaselineComparison {
    let mut expected = parse_baseline_section_list(baseline)
        .into_iter()
        .filter(|(name, _)| is_emitted_section(name))
        .map(|(name, text)| {
            (
                normalize_section_name(&name),
                normalize_emitted_section(&text),
            )
        })
        .filter(|(name, _)| !excluded_expected.contains(name))
        .collect::<Vec<_>>();
    let actual = outputs
        .iter()
        .filter(|(name, _)| is_emitted_section(name))
        .map(|(name, text)| {
            (
                normalize_section_name(name),
                normalize_emitted_section(text),
            )
        })
        .collect::<Vec<_>>();
    exclude_input_echo_sections(&mut expected, &actual, input_echoes);
    let differences = compare_section_multisets(&expected, &actual, require_full_paths);
    BaselineComparison { differences }
}

fn exclude_input_echo_sections(
    expected: &mut Vec<(String, String)>,
    actual: &[(String, String)],
    input_echoes: &[(String, String)],
) {
    for (input_name, input_text) in input_echoes {
        let basename = section_basename(input_name);
        let expected_count = expected
            .iter()
            .filter(|(name, _)| section_basename(name) == basename)
            .count();
        let actual_count = actual
            .iter()
            .filter(|(name, _)| section_basename(name) == basename)
            .count();
        if expected_count <= actual_count {
            continue;
        }
        if let Some(index) = expected
            .iter()
            .position(|(name, text)| section_basename(name) == basename && text == input_text)
        {
            expected.remove(index);
        }
    }
}

fn compare_section_multisets(
    expected: &[(String, String)],
    actual: &[(String, String)],
    require_full_paths: bool,
) -> Vec<OutputDifference> {
    let mut expected_match = vec![None; expected.len()];
    let mut actual_matched = vec![false; actual.len()];

    for (expected_index, (expected_name, expected_text)) in expected.iter().enumerate() {
        if let Some(actual_index) = actual.iter().enumerate().find_map(|(index, (name, text))| {
            (!actual_matched[index] && name == expected_name && text == expected_text)
                .then_some(index)
        }) {
            expected_match[expected_index] = Some(actual_index);
            actual_matched[actual_index] = true;
        }
    }

    for (expected_index, (expected_name, expected_text)) in expected.iter().enumerate() {
        if require_full_paths || expected_match[expected_index].is_some() {
            continue;
        }
        let basename = section_basename(expected_name);
        if let Some(actual_index) = actual.iter().enumerate().find_map(|(index, (name, text))| {
            (!actual_matched[index] && section_basename(name) == basename && text == expected_text)
                .then_some(index)
        }) {
            expected_match[expected_index] = Some(actual_index);
            actual_matched[actual_index] = true;
        }
    }

    for (expected_index, (expected_name, _)) in expected.iter().enumerate() {
        if expected_match[expected_index].is_some() {
            continue;
        }
        if let Some(actual_index) = actual.iter().enumerate().find_map(|(index, (name, _))| {
            (!actual_matched[index] && name == expected_name).then_some(index)
        }) {
            expected_match[expected_index] = Some(actual_index);
            actual_matched[actual_index] = true;
            continue;
        }
        if !require_full_paths {
            let basename = section_basename(expected_name);
            if let Some(actual_index) = actual.iter().enumerate().find_map(|(index, (name, _))| {
                (!actual_matched[index] && section_basename(name) == basename).then_some(index)
            }) {
                expected_match[expected_index] = Some(actual_index);
                actual_matched[actual_index] = true;
            }
        }
    }

    let mut differences = Vec::new();
    for (expected_index, (section, expected_text)) in expected.iter().enumerate() {
        match expected_match[expected_index] {
            Some(actual_index) if expected_text != &actual[actual_index].1 => {
                differences.push(OutputDifference {
                    section: section.clone(),
                    kind: OutputDifferenceKind::Content {
                        expected: expected_text.clone(),
                        actual: actual[actual_index].1.clone(),
                    },
                });
            }
            Some(_) => {}
            None => differences.push(OutputDifference {
                section: section.clone(),
                kind: OutputDifferenceKind::Missing {
                    expected: expected_text.clone(),
                },
            }),
        }
    }
    differences.extend(
        actual
            .iter()
            .enumerate()
            .filter(|(index, _)| !actual_matched[*index])
            .map(|(_, (section, actual))| OutputDifference {
                section: section.clone(),
                kind: OutputDifferenceKind::Unexpected {
                    actual: actual.clone(),
                },
            }),
    );
    differences
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
    let mut variant = expand_option_matrix(case)
        .into_iter()
        .next()
        .unwrap_or_default();
    compile_case_variant(case, &mut variant, FixtureChecker::Legacy, false)
        .map_err(FixtureCompilationFailure::into_io_error)
}

/// Compiles every scalar compiler-option variant in deterministic order.
///
/// # Errors
///
/// Returns an I/O error if the fixture filesystem rejects a virtual source.
pub fn compile_case_matrix(case: &Case) -> std::io::Result<Vec<(OptionVariant, Compilation)>> {
    compile_case_matrix_with_checker(case, FixtureChecker::Legacy)
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum FixtureChecker {
    Legacy,
    Canonical,
}

#[derive(Debug)]
enum FixtureCompilationFailure {
    Io(io::Error),
    Canonical(ts_compiler::CanonicalProgramCheckError),
    #[cfg(panic = "unwind")]
    CanonicalPanic {
        detail: String,
    },
}

impl FixtureCompilationFailure {
    fn into_io_error(self) -> io::Error {
        match self {
            Self::Io(error) => error,
            Self::Canonical(error) => io::Error::new(io::ErrorKind::InvalidData, error),
            #[cfg(panic = "unwind")]
            Self::CanonicalPanic { detail } => io::Error::new(io::ErrorKind::InvalidData, detail),
        }
    }
}

impl From<io::Error> for FixtureCompilationFailure {
    fn from(error: io::Error) -> Self {
        Self::Io(error)
    }
}

#[cfg(not(panic = "unwind"))]
fn canonical_checker_unwind_isolation_error() -> io::Error {
    io::Error::new(
        io::ErrorKind::Unsupported,
        "canonical checker diagnostic runs require panic=\"unwind\" so each variant can retain checker panics and continue; this binary was built with panic=\"abort\"",
    )
}

#[cfg(panic = "unwind")]
fn canonical_checker_panic_detail(payload: &(dyn std::any::Any + Send)) -> String {
    let message = if let Some(message) = payload.downcast_ref::<&str>() {
        *message
    } else if let Some(message) = payload.downcast_ref::<String>() {
        message.as_str()
    } else {
        "<non-string panic payload>"
    };
    format!("canonical checker panicked: {message}")
}

#[cfg(panic = "unwind")]
fn catch_canonical_checker_unwind<T>(
    operation: impl FnOnce() -> Result<T, ts_compiler::CanonicalProgramCheckError>,
) -> Result<T, FixtureCompilationFailure> {
    // Every invocation owns its Program, options, and in-memory filesystem;
    // none of that state is reused after an unwind. The assertion applies to
    // this per-variant isolation boundary, not to arbitrary checker callbacks.
    match std::panic::catch_unwind(std::panic::AssertUnwindSafe(operation)) {
        Ok(result) => result.map_err(FixtureCompilationFailure::Canonical),
        Err(payload) => Err(FixtureCompilationFailure::CanonicalPanic {
            detail: canonical_checker_panic_detail(payload.as_ref()),
        }),
    }
}

#[cfg(not(panic = "unwind"))]
fn catch_canonical_checker_unwind<T>(
    _operation: impl FnOnce() -> Result<T, ts_compiler::CanonicalProgramCheckError>,
) -> Result<T, FixtureCompilationFailure> {
    Err(FixtureCompilationFailure::Io(
        canonical_checker_unwind_isolation_error(),
    ))
}

fn compile_case_matrix_with_checker(
    case: &Case,
    checker: FixtureChecker,
) -> std::io::Result<Vec<(OptionVariant, Compilation)>> {
    expand_option_matrix(case)
        .into_iter()
        .map(
            |mut variant| match compile_case_variant(case, &mut variant, checker, false) {
                Ok(compilation) => Ok((variant, compilation)),
                Err(FixtureCompilationFailure::Canonical(error))
                    if matches!(
                        error.failure_class(),
                        ts_compiler::CanonicalProgramCheckFailureClass::Unsupported { .. }
                    ) =>
                {
                    variant
                        .unsupported_details
                        .push(format!("experimental canonical checker: {error}"));
                    variant.unsupported_details.sort();
                    variant.unsupported_details.dedup();
                    Ok((variant, Compilation::default()))
                }
                Err(error) => Err(error.into_io_error()),
            },
        )
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

#[allow(clippy::too_many_lines)]
fn compile_case_variant(
    case: &Case,
    variant: &mut OptionVariant,
    checker: FixtureChecker,
    walk_semantic_artifacts: bool,
) -> Result<Compilation, FixtureCompilationFailure> {
    let file_system = MemoryFileSystem::new(fixture_case_sensitive(case));
    let project_config_path = project_config_unit(case).map(|(path, _)| path);
    let project_directory = project_config_path.as_deref().and_then(|path| {
        path.rsplit_once('/')
            .map(|(directory, _)| directory.to_owned())
    });
    let links = case
        .directive_values("link")
        .filter_map(|value| value.split_once("->"))
        .map(|(source, target)| {
            (
                virtual_harness_path(case, source.trim()),
                virtual_harness_path(case, target.trim()),
            )
        })
        .collect::<Vec<_>>();
    for (source, alias) in &links {
        file_system.add_directory_link(source, alias);
    }
    let mut roots = Vec::with_capacity(case.units.len());
    for (index, unit) in case.units.iter().enumerate() {
        let path = virtual_unit_path(case, unit, index);
        file_system.write_file(&path, unit.source_text.as_scannable_str())?;
        let next_unit_line = case
            .units
            .get(index + 1)
            .map_or(usize::MAX, |next| next.start_line);
        for alias in case
            .directives
            .iter()
            .filter(|directive| {
                directive.name.eq_ignore_ascii_case("symlink")
                    && directive.line >= unit.start_line
                    && directive.line < next_unit_line
            })
            .flat_map(|directive| directive.value.split(','))
            .map(str::trim)
            .filter(|alias| !alias.is_empty())
        {
            file_system.add_file_link(&path, &virtual_harness_path(case, alias));
        }
        if is_pinned_program_root(&path) {
            roots.push(path);
        }
    }
    let parsed_options = fixture_compiler_options_result(case, variant);
    let option_diagnostics = parsed_options.diagnostics;
    let mut compiler_options = parsed_options.options;
    if let Some(config) = pinned_project_config(case) {
        roots = project_root_unit_indices(case, &config, &compiler_options)
            .into_iter()
            .map(|index| virtual_unit_path(case, &case.units[index], index))
            .collect();
    } else {
        let last_unit_uses_implicit_references =
            case.units.last().is_some_and(unit_uses_implicit_references);
        if project_directory.is_none()
            && (case
                .directive_values("noImplicitReferences")
                .last()
                .is_some_and(|value| !value.is_empty())
                || last_unit_uses_implicit_references)
        {
            roots.clear();
            if let Some((index, last_unit)) = case.units.iter().enumerate().next_back() {
                let last_root = virtual_unit_path(case, last_unit, index);
                if is_pinned_program_root(&last_root) {
                    roots.push(last_root);
                }
            }
        }
    }

    if compiler_options.root_dir.is_none()
        && let Some(project_directory) = project_directory.as_ref()
        && !project_directory.is_empty()
    {
        compiler_options.root_dir = Some(project_directory.clone());
    }
    materialize_upstream_test_libraries(case, &file_system, &roots)?;
    // Compiler baselines generally assume libraries. Keeping this enabled is
    // important for diagnostic fidelity even though syntax-only corpus tests
    // use the cheaper parser path directly.
    if project_config_path.is_none() && case.directive_values("noLib").next().is_none() {
        compiler_options.no_lib = false;
    }
    let current_directory = virtual_unit_root(case);
    let (program, semantic_artifacts) = match checker {
        FixtureChecker::Legacy => (
            ts_compiler::Program::new_with_options(
                &file_system,
                &current_directory,
                &roots,
                compiler_options,
            ),
            None,
        ),
        FixtureChecker::Canonical if walk_semantic_artifacts => {
            let (program, rendered) = catch_canonical_checker_unwind(|| {
                ts_compiler::Program::try_new_with_canonical_checker_and_queries_with_config_path(
                    &file_system,
                    &current_directory,
                    &roots,
                    compiler_options,
                    project_config_path.as_deref(),
                    |program, queries| artifacts::render_program(case, program, queries),
                )
            })?;
            let rendered = rendered
                .transpose()
                .map_err(|error| io::Error::new(io::ErrorKind::InvalidData, error))?;
            let artifacts = match rendered {
                Some(rendered) => rendered,
                None => GeneratedSemanticArtifacts::unavailable(
                    artifacts::walk_program(case, &program)
                        .map_err(|error| io::Error::new(io::ErrorKind::InvalidData, error))?,
                    "semantic baselines require a canonical checker, but noCheck prevented checker construction",
                ),
            };
            (program, Some(artifacts))
        }
        FixtureChecker::Canonical => (
            catch_canonical_checker_unwind(|| {
                ts_compiler::Program::try_new_with_canonical_checker_with_config_path(
                    &file_system,
                    &current_directory,
                    &roots,
                    compiler_options,
                    project_config_path.as_deref(),
                )
            })?,
            None,
        ),
    };
    // The Go harness baselines pre-emit program/syntactic/semantic/global and
    // declaration diagnostics. Emit-result diagnostics are not part of that
    // stream, so use Program's aggregate as the closest available Rust API.
    let mut diagnostics = program
        .diagnostics()
        .iter()
        .map(|diagnostic| CompilationDiagnostic {
            file_name: diagnostic.file_name.clone(),
            source_text: diagnostic
                .file_name
                .as_deref()
                .and_then(|file_name| program.source_file(file_name))
                .map(|source_file| SourceText::from(source_file.source_text.clone())),
            range: diagnostic.range,
            code: diagnostic.code,
            category: Some(match diagnostic.category {
                ts_diagnostics::Category::Error => CompilationDiagnosticCategory::Error,
                ts_diagnostics::Category::Warning => CompilationDiagnosticCategory::Warning,
                ts_diagnostics::Category::Suggestion => CompilationDiagnosticCategory::Suggestion,
                ts_diagnostics::Category::Message => CompilationDiagnosticCategory::Message,
            }),
            message: pinned_program_diagnostic_message(&program, diagnostic),
            related_information: match checker {
                // Legacy Program diagnostics still do not expose whether
                // related records exist. Do not manufacture canonical detail
                // or use the legacy checker as a fallback for canonical mode.
                FixtureChecker::Legacy => None,
                FixtureChecker::Canonical => Some(
                    diagnostic
                        .related_information
                        .iter()
                        .map(|related| CompilationRelatedInformation {
                            file_name: related.file_name.clone(),
                            source_text: related
                                .file_name
                                .as_deref()
                                .and_then(|file_name| program.source_file(file_name))
                                .map(|source_file| {
                                    SourceText::from(source_file.source_text.clone())
                                }),
                            range: related.range,
                            code: related.code,
                            category: Some(match related.category {
                                ts_diagnostics::Category::Error => {
                                    CompilationDiagnosticCategory::Error
                                }
                                ts_diagnostics::Category::Warning => {
                                    CompilationDiagnosticCategory::Warning
                                }
                                ts_diagnostics::Category::Suggestion => {
                                    CompilationDiagnosticCategory::Suggestion
                                }
                                ts_diagnostics::Category::Message => {
                                    CompilationDiagnosticCategory::Message
                                }
                            }),
                            message: related.message.clone(),
                        })
                        .collect(),
                ),
            },
        })
        .collect::<Vec<_>>();
    for diagnostic in option_diagnostics {
        let message = diagnostic
            .render()
            .map_err(|error| io::Error::new(io::ErrorKind::InvalidData, error))?;
        let option_diagnostic = CompilationDiagnostic {
            file_name: None,
            source_text: None,
            range: None,
            code: Some(diagnostic.code()),
            category: Some(match diagnostic.category() {
                ts_diagnostics::Category::Error => CompilationDiagnosticCategory::Error,
                ts_diagnostics::Category::Warning => CompilationDiagnosticCategory::Warning,
                ts_diagnostics::Category::Suggestion => CompilationDiagnosticCategory::Suggestion,
                ts_diagnostics::Category::Message => CompilationDiagnosticCategory::Message,
            }),
            message,
            related_information: match checker {
                FixtureChecker::Legacy => None,
                FixtureChecker::Canonical => Some(Vec::new()),
            },
        };
        if !diagnostics.iter().any(|existing| {
            existing.file_name == option_diagnostic.file_name
                && existing.range == option_diagnostic.range
                && existing.code == option_diagnostic.code
                && existing.category == option_diagnostic.category
                && existing.message == option_diagnostic.message
        }) {
            diagnostics.push(option_diagnostic);
        }
    }
    diagnostics.sort_by(compare_compilation_diagnostics);
    let ordered = diagnostics.iter().collect::<Vec<_>>();
    let mut unsupported_details = Vec::new();
    let diagnostic_text = render_diagnostic_header(case, &ordered, &mut unsupported_details);
    let outputs = match checker {
        FixtureChecker::Legacy => program
            .emit()
            .files
            .into_iter()
            .map(|output| (output.file_name, output.text))
            .collect(),
        FixtureChecker::Canonical => BTreeMap::new(),
    };
    Ok(Compilation {
        diagnostics,
        diagnostic_text,
        outputs,
        semantic_artifacts,
    })
}

fn materialize_upstream_test_libraries(
    case: &Case,
    file_system: &MemoryFileSystem,
    roots: &[String],
) -> io::Result<()> {
    let case_sensitive = fixture_case_sensitive(case);
    let needs_test_libraries = case.units.iter().enumerate().any(|(index, unit)| {
        unit.source_text.as_scannable_str().contains("/.lib/")
            && roots.iter().any(|root| {
                project_paths_equal(root, &virtual_unit_path(case, unit, index), case_sensitive)
            })
    });
    if !needs_test_libraries {
        return Ok(());
    }

    let Some(library_root) = case.path.ancestors().find_map(|ancestor| {
        let candidate = ancestor.join("_submodules/TypeScript/tests/lib");
        candidate.is_dir().then_some(candidate)
    }) else {
        return Ok(());
    };

    for path in collect_files(&library_root, |_| true)? {
        let relative = path.strip_prefix(&library_root).map_err(|error| {
            io::Error::new(
                io::ErrorKind::InvalidData,
                format!("test library path is outside its root: {error}"),
            )
        })?;
        let virtual_path = format!("/.lib/{}", relative.to_string_lossy().replace('\\', "/"));
        let source = fs::read_to_string(path)?;
        file_system.write_file(&virtual_path, source.trim_start_matches('\u{feff}'))?;
    }
    Ok(())
}

fn virtual_harness_path(case: &Case, path: &str) -> String {
    if ts_path::is_absolute(path) {
        ts_path::normalize_path(path)
    } else {
        ts_path::resolve_path(&virtual_unit_root(case), &[path])
    }
}

fn virtual_unit_path(case: &Case, unit: &Unit, index: usize) -> String {
    let path = unit.path.to_string_lossy().replace('\\', "/");
    if unit.path == case.path {
        let base = unit
            .path
            .file_name()
            .and_then(|name| name.to_str())
            .map_or_else(|| format!("unit{index}.ts"), str::to_owned);
        return ts_path::resolve_path(&virtual_unit_root(case), &[&base]);
    }
    if ts_path::is_absolute(&path) {
        return ts_path::normalize_path(&path);
    }
    ts_path::resolve_path(&virtual_unit_root(case), &[&path])
}

fn virtual_unit_root(case: &Case) -> String {
    case.directive_values("currentDirectory")
        .last()
        .map(str::trim)
        .filter(|directory| !directory.is_empty())
        .map_or_else(
            || "/.src".to_owned(),
            |directory| ts_path::resolve_path("/.src", &[directory]),
        )
}

fn is_pinned_program_root(path: &str) -> bool {
    let path = path.to_ascii_lowercase();
    !matches!(path.rsplit_once('.'), Some((_, "json" | "tsbuildinfo")))
}

fn unit_uses_implicit_references(unit: &Unit) -> bool {
    let source = unit.source_text.as_scannable_str();
    source.contains("require(")
        || source.as_bytes().windows(14).any(|window| {
            window.starts_with(b"reference")
                && matches!(window[9], b' ' | b'\t' | b'\n' | b'\r' | 0x0c)
                && &window[10..] == b"path"
        })
}

fn pinned_program_diagnostic_message(
    program: &ts_compiler::Program,
    diagnostic: &ts_compiler::ProgramDiagnostic,
) -> String {
    if diagnostic.code != Some(2688) || diagnostic.file_name.is_some() {
        return diagnostic.message.clone();
    }

    let Some(missing_message) = ts_diagnostics::message_by_code(2688) else {
        return diagnostic.message.clone();
    };
    let matching = program
        .options()
        .types
        .as_deref()
        .unwrap_or_default()
        .iter()
        .filter(|name| {
            missing_message
                .format(&[(*name).clone()])
                .is_ok_and(|message| message == diagnostic.message)
        })
        .collect::<Vec<_>>();
    let [name] = matching.as_slice() else {
        return diagnostic.message.clone();
    };
    let Some(program_reason) = ts_diagnostics::message_by_code(1430) else {
        return diagnostic.message.clone();
    };
    let Some(type_reason) = ts_diagnostics::message_by_code(1417) else {
        return diagnostic.message.clone();
    };
    let Ok(type_reason) = type_reason.format(&[(*name).clone()]) else {
        return diagnostic.message.clone();
    };

    format!(
        "{}\n  {}\n    {type_reason}",
        diagnostic.message,
        program_reason.text(),
    )
}

fn fixture_compiler_options(case: &Case, variant: &OptionVariant) -> ts_options::CompilerOptions {
    fixture_compiler_options_result(case, variant).options
}

fn fixture_compiler_options_result(
    case: &Case,
    variant: &OptionVariant,
) -> ts_options::ParseOptionsResult {
    let project_config = pinned_project_config(case);
    let mut values = project_config
        .as_ref()
        .map_or_else(BTreeMap::new, |config| config.compiler_options.clone());
    if let Some((name, value)) = bom_prefixed_compiler_directive(case) {
        values.retain(|configured_name, _| !configured_name.eq_ignore_ascii_case(name));
        values.insert(
            name.to_owned(),
            directive_json_value(name, pinned_setting_value(value)),
        );
    }
    if let Some(value) = case.directive_values("ignoreDeprecations").last() {
        values.retain(|name, _| !name.eq_ignore_ascii_case("ignoreDeprecations"));
        values.insert(
            "ignoreDeprecations".to_owned(),
            ts_config::JsonValue::String(pinned_setting_value(value).trim().to_owned()),
        );
    }
    for (name, value) in &variant.values {
        if name.eq_ignore_ascii_case("pretty") {
            continue;
        }
        values.retain(|configured_name, _| !configured_name.eq_ignore_ascii_case(name));
        values.insert(name.to_owned(), directive_json_value(name, value));
    }
    let has_explicit_target = values
        .keys()
        .any(|name| name.eq_ignore_ascii_case("target"));
    let has_explicit_module = values
        .keys()
        .any(|name| name.eq_ignore_ascii_case("module"));
    let mut parsed = if let Some(mut config) = project_config {
        config.compiler_options = values;
        ts_options::parse_project_options(&config)
    } else {
        ts_options::parse_compiler_options(&ts_config::JsonValue::Object(values))
    };
    let options = &mut parsed.options;
    // The current ts-go compiler treats an omitted target as the latest
    // standard language version rather than the historical ES5 default.
    if !has_explicit_target {
        options.target = ts_options::ScriptTarget::Es2025;
    }
    if options.target == ts_options::ScriptTarget::Es3
        && case
            .directive_values("typeScriptVersion")
            .filter_map(|version| version.split('.').next())
            .filter_map(|major| major.parse::<u32>().ok())
            .any(|major| major >= 5)
    {
        options.target = ts_options::ScriptTarget::Es2025;
    }
    if !has_explicit_module
        && options.out_file.is_none()
        && options.target < ts_options::ScriptTarget::Es2015
    {
        options.module = ts_options::ModuleKind::CommonJs;
    }
    if case
        .directive_values("module")
        .any(|module| module.trim() == "*")
        && variant
            .values
            .get("module")
            .is_some_and(|module| module.eq_ignore_ascii_case("none"))
    {
        options.module = ts_options::ModuleKind::CommonJs;
    }
    parsed
}

fn bom_prefixed_compiler_directive(case: &Case) -> Option<(&str, &str)> {
    let source = case.source_text.as_str()?.strip_prefix('\u{feff}')?;
    let first_line = source.lines().next()?;
    let (name, value) = parse_directive_line(first_line)?;
    is_compiler_option_directive(name).then_some((name, value))
}

fn is_compiler_option_directive(name: &str) -> bool {
    name.eq_ignore_ascii_case("ignoreDeprecations")
        || COMPILER_OPTION_NAMES
            .iter()
            .chain(LIST_OPTION_NAMES)
            .any(|option| option.eq_ignore_ascii_case(name))
}

fn project_configuration_unsupported_details(case: &Case) -> Vec<String> {
    let Some((path, unit)) = project_config_unit(case) else {
        return Vec::new();
    };
    let config_count = case
        .units
        .iter()
        .filter(|unit| {
            unit.path
                .file_name()
                .and_then(|name| name.to_str())
                .is_some_and(|name| {
                    name.eq_ignore_ascii_case("tsconfig.json")
                        || name.eq_ignore_ascii_case("jsconfig.json")
                })
        })
        .count();
    let mut details = Vec::new();
    if config_count > 1 {
        details.push("multiple virtual project configurations are not modeled exactly".to_owned());
    }

    let parsed = ts_config::parse_config_text(&path, unit.source_text.as_scannable_str());
    let Some(config) = pinned_project_config(case) else {
        details.push("virtual project configuration has no recoverable object".to_owned());
        return details;
    };
    if parsed.value.is_some() && !parsed.diagnostics.is_empty() {
        details
            .push("virtual project configuration diagnostics are not modeled exactly".to_owned());
    }
    if !config.references.is_empty() {
        details.push("virtual project references are not modeled exactly".to_owned());
    }
    let directory = config
        .path
        .rsplit_once('/')
        .map_or("", |(directory, _)| directory);
    let case_sensitive = fixture_case_sensitive(case);
    for pattern in config.include.iter().chain(config.exclude.iter()).flatten() {
        if project_pattern_matches(directory, directory, pattern, case_sensitive).is_none() {
            details.push(format!(
                "virtual project include/exclude pattern {pattern:?} is not modeled exactly"
            ));
        }
    }
    if let Some(files) = config.files.as_ref() {
        for file in files {
            let expected = ts_path::resolve_path(directory, &[file]);
            if !case.units.iter().enumerate().any(|(index, unit)| {
                project_paths_equal(
                    &virtual_unit_path(case, unit, index),
                    &expected,
                    case_sensitive,
                )
            }) {
                details.push(format!(
                    "virtual project explicitly references unavailable input {file:?}"
                ));
            }
        }
    }
    details
}

fn pinned_project_config(case: &Case) -> Option<ts_config::ProjectConfig> {
    let (path, unit) = project_config_unit(case)?;
    let source = unit.source_text.as_scannable_str();
    if let Some(config) = ts_config::parse_config_text(&path, source).value {
        if config.extends.is_some() {
            let filesystem = MemoryFileSystem::new(fixture_case_sensitive(case));
            for (index, unit) in case.units.iter().enumerate() {
                filesystem
                    .write_file(
                        &virtual_unit_path(case, unit, index),
                        unit.source_text.as_scannable_str(),
                    )
                    .ok()?;
            }
            let resolved = ts_config::resolve_config_file(&filesystem, &path);
            return resolved.diagnostics.is_empty().then_some(resolved.value)?;
        }
        return Some(config);
    }

    let ts_config::JsonValue::Array(values) = ts_config::parse_jsonc(&path, source).value? else {
        return None;
    };
    let first_object = values
        .into_iter()
        .find(|value| matches!(value, ts_config::JsonValue::Object(_)))?;
    let recovered = serde_json::to_string(&project_json_value(&first_object)?).ok()?;
    ts_config::parse_config_text(&path, &recovered).value
}

fn project_json_value(value: &ts_config::JsonValue) -> Option<serde_json::Value> {
    match value {
        ts_config::JsonValue::Null => Some(serde_json::Value::Null),
        ts_config::JsonValue::Bool(value) => Some(serde_json::Value::Bool(*value)),
        ts_config::JsonValue::Number(value) => value
            .as_str()
            .parse::<serde_json::Number>()
            .ok()
            .map(serde_json::Value::Number),
        ts_config::JsonValue::String(value) => Some(serde_json::Value::String(value.clone())),
        ts_config::JsonValue::Array(values) => values
            .iter()
            .map(project_json_value)
            .collect::<Option<Vec<_>>>()
            .map(serde_json::Value::Array),
        ts_config::JsonValue::Object(values) => values
            .iter()
            .map(|(key, value)| project_json_value(value).map(|value| (key.clone(), value)))
            .collect::<Option<serde_json::Map<_, _>>>()
            .map(serde_json::Value::Object),
    }
}

fn project_root_unit_indices(
    case: &Case,
    config: &ts_config::ProjectConfig,
    options: &ts_options::CompilerOptions,
) -> Vec<usize> {
    let directory = config
        .path
        .rsplit_once('/')
        .map_or("", |(directory, _)| directory);
    let case_sensitive = fixture_case_sensitive(case);
    let explicit_files = config.files.as_ref().map(|files| {
        files
            .iter()
            .map(|file| {
                project_canonical_path(&ts_path::resolve_path(directory, &[file]), case_sensitive)
            })
            .collect::<BTreeSet<_>>()
    });
    case.units
        .iter()
        .enumerate()
        .filter_map(|(index, unit)| {
            let path = virtual_unit_path(case, unit, index);
            if !is_pinned_program_root(&path) {
                return None;
            }
            if explicit_files
                .as_ref()
                .is_some_and(|files| files.contains(&project_canonical_path(&path, case_sensitive)))
            {
                return Some(index);
            }

            let relative = project_relative_path(&path, directory, case_sensitive)?;
            if relative.split('/').any(|component| {
                component.starts_with('.')
                    || matches!(
                        component,
                        "node_modules" | "bower_components" | "jspm_packages"
                    )
            }) {
                return None;
            }
            match ts_path::script_kind_from_path(&path) {
                ts_path::ScriptKind::Ts | ts_path::ScriptKind::Tsx => Some(index),
                ts_path::ScriptKind::Js | ts_path::ScriptKind::Jsx if options.allow_js => {
                    Some(index)
                }
                _ => None,
            }?;

            let included = config.include.as_ref().map_or_else(
                || explicit_files.is_none(),
                |patterns| {
                    patterns.iter().any(|pattern| {
                        project_pattern_matches(directory, &path, pattern, case_sensitive)
                            == Some(true)
                    })
                },
            );
            if !included {
                return None;
            }
            if config.exclude.as_ref().is_some_and(|patterns| {
                patterns.iter().any(|pattern| {
                    project_pattern_matches(directory, &path, pattern, case_sensitive) == Some(true)
                })
            }) {
                return None;
            }
            Some(index)
        })
        .collect()
}

fn fixture_case_sensitive(case: &Case) -> bool {
    case.directive_values("useCaseSensitiveFileNames")
        .last()
        .map(pinned_setting_value)
        .is_none_or(|value| !value.eq_ignore_ascii_case("false"))
}

fn project_canonical_path(path: &str, case_sensitive: bool) -> String {
    ts_path::canonical_file_name(
        &ts_path::normalize_path(path),
        if case_sensitive {
            ts_path::CaseSensitivity::Sensitive
        } else {
            ts_path::CaseSensitivity::Insensitive
        },
    )
}

fn project_paths_equal(left: &str, right: &str, case_sensitive: bool) -> bool {
    project_canonical_path(left, case_sensitive) == project_canonical_path(right, case_sensitive)
}

fn project_relative_path<'path>(
    path: &'path str,
    directory: &str,
    case_sensitive: bool,
) -> Option<&'path str> {
    let directory = directory.trim_end_matches('/');
    if directory.is_empty() {
        return path.strip_prefix('/');
    }
    let prefix = path.get(..directory.len())?;
    if !project_paths_equal(prefix, directory, case_sensitive) {
        return None;
    }
    path.get(directory.len()..)?.strip_prefix('/')
}

fn project_pattern_matches(
    directory: &str,
    path: &str,
    pattern: &str,
    case_sensitive: bool,
) -> Option<bool> {
    let normalized = ts_path::resolve_path(directory, &[&pattern.replace('\\', "/")]);
    if normalized.contains(['?', '[', ']', '{', '}']) {
        return None;
    }

    if let Some((base, tail)) = normalized.split_once("/**/") {
        if tail.contains('/') || tail.contains('?') {
            return None;
        }
        let base = if base.is_empty() { "/" } else { base };
        let Some(relative) = project_relative_path(path, base, case_sensitive) else {
            return Some(false);
        };
        return project_pattern_leaf_matches(
            tail,
            relative.rsplit('/').next().unwrap_or(relative),
            case_sensitive,
        );
    }

    if normalized.contains("**") {
        return None;
    }
    if normalized.contains('*') {
        let (parent, leaf) = normalized.rsplit_once('/')?;
        let Some(relative) = project_relative_path(path, parent, case_sensitive) else {
            return Some(false);
        };
        if relative.contains('/') {
            return Some(false);
        }
        return project_pattern_leaf_matches(leaf, relative, case_sensitive);
    }

    Some(
        project_paths_equal(path, &normalized, case_sensitive)
            || project_relative_path(path, &normalized, case_sensitive).is_some(),
    )
}

fn project_pattern_leaf_matches(
    pattern: &str,
    file_name: &str,
    case_sensitive: bool,
) -> Option<bool> {
    if pattern == "*" {
        return Some(true);
    }
    let suffix = pattern.strip_prefix('*')?;
    if !suffix.starts_with('.') || suffix.contains('*') {
        return None;
    }
    let file_name = if case_sensitive {
        file_name.to_owned()
    } else {
        ts_path::canonical_file_name(file_name, ts_path::CaseSensitivity::Insensitive)
    };
    let suffix = if case_sensitive {
        suffix.to_owned()
    } else {
        ts_path::canonical_file_name(suffix, ts_path::CaseSensitivity::Insensitive)
    };
    Some(file_name.ends_with(&suffix))
}

fn project_config_unit(case: &Case) -> Option<(String, &Unit)> {
    case.units.iter().enumerate().find_map(|(index, unit)| {
        let path = virtual_unit_path(case, unit, index);
        let file_name = path.rsplit('/').next()?;
        (file_name.eq_ignore_ascii_case("tsconfig.json")
            || file_name.eq_ignore_ascii_case("jsconfig.json"))
        .then_some((path, unit))
    })
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
    if matches!(name.to_ascii_lowercase().as_str(), "outdir" | "outfile") {
        return ts_config::JsonValue::String(value.trim().to_owned());
    }
    match value {
        value if value.eq_ignore_ascii_case("true") => ts_config::JsonValue::Bool(true),
        value if value.eq_ignore_ascii_case("false") => ts_config::JsonValue::Bool(false),
        value => ts_config::JsonValue::String(value.trim().to_owned()),
    }
}

/// Frozen `compilerVaryBy` boolean options from the pinned Go runner.
const VARYING_BOOLEAN_OPTION_NAMES: &[&str] = &[
    "allowArbitraryExtensions",
    "allowImportingTsExtensions",
    "allowJs",
    "allowSyntheticDefaultImports",
    "allowUmdGlobalAccess",
    "allowUnreachableCode",
    "allowUnusedLabels",
    "alwaysStrict",
    "assumeChangesOnlyAffectDirectDependencies",
    "checkJs",
    "composite",
    "declaration",
    "declarationMap",
    "deduplicatePackages",
    "disableSizeLimit",
    "downlevelIteration",
    "emitBOM",
    "emitDeclarationOnly",
    "emitDecoratorMetadata",
    "erasableSyntaxOnly",
    "experimentalDecorators",
    "esModuleInterop",
    "exactOptionalPropertyTypes",
    "forceConsistentCasingInFileNames",
    "importHelpers",
    "inlineSourceMap",
    "inlineSources",
    "isolatedDeclarations",
    "isolatedModules",
    "libReplacement",
    "noEmit",
    "noEmitHelpers",
    "noEmitOnError",
    "noErrorTruncation",
    "noFallthroughCasesInSwitch",
    "noImplicitAny",
    "noImplicitOverride",
    "noImplicitReturns",
    "noImplicitThis",
    "noLib",
    "noPropertyAccessFromIndexSignature",
    "noResolve",
    "noUncheckedIndexedAccess",
    "noUncheckedSideEffectImports",
    "noUnusedLocals",
    "noUnusedParameters",
    "preserveConstEnums",
    "removeComments",
    "resolveJsonModule",
    "resolvePackageJsonExports",
    "resolvePackageJsonImports",
    "rewriteRelativeImportExtensions",
    "skipDefaultLibCheck",
    "skipLibCheck",
    "sourceMap",
    "stableTypeOrdering",
    "stripInternal",
    "strict",
    "strictBindCallApply",
    "strictBuiltinIteratorReturn",
    "strictFunctionTypes",
    "strictNullChecks",
    "strictPropertyInitialization",
    "useDefineForClassFields",
    "useUnknownInCatchVariables",
    "verbatimModuleSyntax",
];

/// Scalar compiler settings read by this fixture harness. Varying enum options
/// are included here alongside the frozen boolean set and non-varying strings.
const COMPILER_OPTION_NAMES: &[&str] = &[
    "allowArbitraryExtensions",
    "allowImportingTsExtensions",
    "allowJs",
    "allowSyntheticDefaultImports",
    "allowUmdGlobalAccess",
    "allowUnreachableCode",
    "allowUnusedLabels",
    "alwaysStrict",
    "assumeChangesOnlyAffectDirectDependencies",
    "baseUrl",
    "checkJs",
    "composite",
    "declaration",
    "declarationDir",
    "declarationMap",
    "deduplicatePackages",
    "disableSizeLimit",
    "downlevelIteration",
    "emitBOM",
    "emitDeclarationOnly",
    "emitDecoratorMetadata",
    "erasableSyntaxOnly",
    "esModuleInterop",
    "exactOptionalPropertyTypes",
    "experimentalDecorators",
    "forceConsistentCasingInFileNames",
    "importHelpers",
    "incremental",
    "inlineSourceMap",
    "inlineSources",
    "isolatedDeclarations",
    "isolatedModules",
    "jsx",
    "jsxFactory",
    "jsxFragmentFactory",
    "jsxImportSource",
    "libReplacement",
    "mapRoot",
    "module",
    "moduleDetection",
    "moduleResolution",
    "newLine",
    "noCheck",
    "noEmit",
    "noEmitHelpers",
    "noEmitOnError",
    "noErrorTruncation",
    "noFallthroughCasesInSwitch",
    "noImplicitAny",
    "noImplicitOverride",
    "noImplicitReturns",
    "noImplicitThis",
    "noLib",
    "noPropertyAccessFromIndexSignature",
    "noResolve",
    "noUncheckedIndexedAccess",
    "noUncheckedSideEffectImports",
    "noUnusedLocals",
    "noUnusedParameters",
    "outDir",
    "outFile",
    "preserveConstEnums",
    "pretty",
    "reactNamespace",
    "removeComments",
    "resolveJsonModule",
    "resolvePackageJsonExports",
    "resolvePackageJsonImports",
    "rewriteRelativeImportExtensions",
    "rootDir",
    "skipDefaultLibCheck",
    "skipLibCheck",
    "sourceMap",
    "sourceRoot",
    "stableTypeOrdering",
    "strict",
    "strictBindCallApply",
    "strictBuiltinIteratorReturn",
    "strictFunctionTypes",
    "strictNullChecks",
    "strictPropertyInitialization",
    "stripInternal",
    "target",
    "tsBuildInfoFile",
    "useDefineForClassFields",
    "useUnknownInCatchVariables",
    "verbatimModuleSyntax",
];

const LIST_OPTION_NAMES: &[&str] = &["lib", "rootDirs", "typeRoots", "types"];

const BOOLEAN_OPTION_VALUES: &[(&str, &str)] = &[("true", "true"), ("false", "false")];
const TARGET_OPTION_VALUES: &[(&str, &str)] = &[
    ("es5", "es5"),
    ("es6", "es2015"),
    ("es2015", "es2015"),
    ("es2016", "es2016"),
    ("es2017", "es2017"),
    ("es2018", "es2018"),
    ("es2019", "es2019"),
    ("es2020", "es2020"),
    ("es2021", "es2021"),
    ("es2022", "es2022"),
    ("es2023", "es2023"),
    ("es2024", "es2024"),
    ("es2025", "es2025"),
    ("esnext", "esnext"),
];
const MODULE_OPTION_VALUES: &[(&str, &str)] = &[
    ("commonjs", "commonjs"),
    ("amd", "amd"),
    ("system", "system"),
    ("umd", "umd"),
    ("es6", "es2015"),
    ("es2015", "es2015"),
    ("es2020", "es2020"),
    ("es2022", "es2022"),
    ("esnext", "esnext"),
    ("node16", "node16"),
    ("node18", "node18"),
    ("node20", "node20"),
    ("nodenext", "nodenext"),
    ("preserve", "preserve"),
];
const MODULE_RESOLUTION_OPTION_VALUES: &[(&str, &str)] = &[
    ("node16", "node16"),
    ("nodenext", "nodenext"),
    ("bundler", "bundler"),
    ("classic", "classic"),
    ("node", "node10"),
    ("node10", "node10"),
];
const MODULE_DETECTION_OPTION_VALUES: &[(&str, &str)] =
    &[("auto", "auto"), ("legacy", "legacy"), ("force", "force")];
const JSX_OPTION_VALUES: &[(&str, &str)] = &[
    ("preserve", "preserve"),
    ("react-native", "react-native"),
    ("react-jsx", "react-jsx"),
    ("react-jsxdev", "react-jsxdev"),
    ("react", "react"),
];
const NEW_LINE_OPTION_VALUES: &[(&str, &str)] = &[("crlf", "crlf"), ("lf", "lf")];

const RUST_APPLIED_COMPILER_OPTION_NAMES: &[&str] = &[
    "allowArbitraryExtensions",
    "allowJs",
    "allowSyntheticDefaultImports",
    "allowUnreachableCode",
    "alwaysStrict",
    "baseUrl",
    "checkJs",
    "composite",
    "declaration",
    "declarationDir",
    "declarationMap",
    "downlevelIteration",
    "emitBOM",
    "emitDeclarationOnly",
    "emitDecoratorMetadata",
    "esModuleInterop",
    "exactOptionalPropertyTypes",
    "experimentalDecorators",
    "forceConsistentCasingInFileNames",
    "importHelpers",
    "incremental",
    "inlineSourceMap",
    "inlineSources",
    "isolatedDeclarations",
    "isolatedModules",
    "jsx",
    "jsxFactory",
    "jsxFragmentFactory",
    "jsxImportSource",
    "mapRoot",
    "module",
    "moduleDetection",
    "moduleResolution",
    "noCheck",
    "noEmit",
    "noEmitHelpers",
    "noEmitOnError",
    "noErrorTruncation",
    "noFallthroughCasesInSwitch",
    "noImplicitAny",
    "noImplicitReturns",
    "noLib",
    "noUncheckedSideEffectImports",
    "noUnusedLocals",
    "noUnusedParameters",
    "outDir",
    "outFile",
    "preserveConstEnums",
    "pretty",
    "reactNamespace",
    "removeComments",
    "resolveJsonModule",
    "resolvePackageJsonExports",
    "resolvePackageJsonImports",
    "rewriteRelativeImportExtensions",
    "rootDir",
    "skipLibCheck",
    "sourceMap",
    "sourceRoot",
    "strict",
    "strictBuiltinIteratorReturn",
    "strictFunctionTypes",
    "strictNullChecks",
    "strictPropertyInitialization",
    "stripInternal",
    "target",
    "tsBuildInfoFile",
    "useDefineForClassFields",
    "useUnknownInCatchVariables",
    "verbatimModuleSyntax",
];

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

fn is_emit_baseline_file(path: &Path) -> bool {
    path.file_name()
        .and_then(|name| name.to_str())
        .is_some_and(is_emitted_section)
}

fn is_error_baseline_file(path: &Path) -> bool {
    path.file_name()
        .and_then(|name| name.to_str())
        .and_then(error_baseline_base)
        .is_some()
}

fn index_baselines(paths: Vec<PathBuf>) -> BTreeMap<String, Vec<PathBuf>> {
    index_baselines_with(paths, emitted_baseline_base)
}

fn index_baselines_with(
    paths: Vec<PathBuf>,
    baseline_base: fn(&str) -> Option<&str>,
) -> BTreeMap<String, Vec<PathBuf>> {
    let mut index = BTreeMap::<String, Vec<PathBuf>>::new();
    for path in paths {
        let Some(base) = path
            .file_name()
            .and_then(|name| name.to_str())
            .and_then(baseline_base)
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

fn error_baseline_base(file_name: &str) -> Option<&str> {
    file_name.strip_suffix(".errors.txt")
}

fn matrix_axes(case: &Case) -> Vec<String> {
    expanded_option_values(case)
        .0
        .into_iter()
        .filter_map(|(name, values)| (values.len() > 1).then_some(name))
        .collect()
}

fn select_variant_baselines<'a>(
    candidates: &[&'a PathBuf],
    case_name: &str,
    variant: &OptionVariant,
    axes: &[String],
) -> Vec<&'a PathBuf> {
    select_variant_baselines_with(candidates, case_name, variant, axes, emitted_baseline_base)
}

fn select_variant_baselines_with<'a>(
    candidates: &[&'a PathBuf],
    case_name: &str,
    variant: &OptionVariant,
    axes: &[String],
    baseline_base: fn(&str) -> Option<&str>,
) -> Vec<&'a PathBuf> {
    let configured_base = configured_baseline_base(case_name, variant, axes);
    candidates
        .iter()
        .copied()
        .filter(|path| {
            path.file_name()
                .and_then(|name| name.to_str())
                .and_then(baseline_base)
                .is_some_and(|base| base == configured_base)
        })
        .collect()
}

fn configured_baseline_base(case_name: &str, variant: &OptionVariant, axes: &[String]) -> String {
    if axes.is_empty() {
        return case_name.to_owned();
    }
    let description = axes
        .iter()
        .filter_map(|axis| {
            variant.values.get(axis).map(|value| {
                format!(
                    "{}={}",
                    axis.to_ascii_lowercase(),
                    value.to_ascii_lowercase()
                )
            })
        })
        .collect::<Vec<_>>()
        .join(",");
    format!("{case_name}({description})")
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
        .or_else(|| name.strip_prefix("/.src/"))
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
    if normalized.starts_with('\u{feff}') {
        normalized.replace_range(..'\u{feff}'.len_utf8(), "ï»¿");
    }
    while normalized.ends_with('\n') {
        normalized.pop();
    }
    if !normalized.is_empty() {
        normalized.push('\n');
    }
    normalized
}

fn normalize_input_section(text: &str) -> String {
    let normalized = normalize_emitted_section(text);
    normalized
        .strip_prefix('\n')
        .unwrap_or(&normalized)
        .to_owned()
}

/// One virtual source file declared by a fixture.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Unit {
    /// Virtual path used by the compiler harness.
    pub path: PathBuf,
    /// Source text reconstructed with pinned-harness newline and leading-blank
    /// semantics after directive lines are removed.
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
    /// The regular compiler harness rejects source before its first virtual file.
    ContentBeforeFirstFile { line: usize },
}

impl fmt::Display for ParseError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::EmptyFileName { line } => {
                write!(formatter, "empty @filename directive on line {line}")
            }
            Self::ContentBeforeFirstFile { line } => write!(
                formatter,
                "substantive source precedes the first @filename directive on line {line}"
            ),
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

    fn append_line(&mut self, line: &[u8]) {
        if !self.source_bytes.is_empty() {
            self.source_bytes.push(b'\n');
        }
        self.source_bytes.extend_from_slice(line);
    }

    fn has_substantive_source(&self) -> bool {
        let mut bytes = self.source_bytes.as_slice();
        loop {
            if let Some(rest) = bytes.strip_prefix(b"\xef\xbb\xbf") {
                bytes = rest;
            }
            bytes = bytes
                .iter()
                .position(|byte| !byte.is_ascii_whitespace())
                .map_or(&[], |start| &bytes[start..]);
            if bytes.is_empty() {
                return false;
            }
            if bytes.starts_with(b"//") {
                bytes = bytes
                    .iter()
                    .position(|byte| *byte == b'\n' || *byte == b'\r')
                    .map_or(&[], |end| &bytes[end..]);
                continue;
            }
            if bytes.starts_with(b"/*") {
                let comment = &bytes[2..];
                bytes = comment
                    .windows(2)
                    .position(|window| window == b"*/")
                    .map_or(&[], |end| &comment[end + 2..]);
                continue;
            }
            return true;
        }
    }

    fn finish(self) -> Unit {
        Unit {
            path: self.path,
            source_text: SourceText::from_bytes(self.source_bytes),
            start_line: self.start_line,
        }
    }
}

fn parse_directive_line(line: &str) -> Option<(&str, &str)> {
    // The pinned Go regexp begins `^//`: indented comments remain source, as do
    // hyphenated TypeScript pragmas because the harness name grammar is `\w+`.
    let comment = line
        .strip_prefix("//")?
        .trim_start_matches(is_pinned_regex_whitespace);
    let directive = comment.strip_prefix('@')?;
    let (name, value) = directive.split_once(':')?;
    let name = name.trim_matches(is_pinned_regex_whitespace);
    if name.is_empty() || !name.chars().all(is_directive_name_character) {
        return None;
    }
    if name.eq_ignore_ascii_case("ts-ignore") || name.eq_ignore_ascii_case("ts-expect-error") {
        return None;
    }
    Some((name, value.trim()))
}

fn is_pinned_regex_whitespace(character: char) -> bool {
    matches!(character, ' ' | '\t' | '\n' | '\r' | '\u{000c}')
}

fn is_directive_name_character(character: char) -> bool {
    character.is_ascii_alphanumeric() || character == '_'
}

#[cfg(test)]
mod tests {
    use std::{
        collections::BTreeMap,
        path::{Path, PathBuf},
    };

    use ts_core::{TextPos, TextRange};

    use super::{
        Case, CompilationDiagnostic, CompilationDiagnosticCategory, CompilationRelatedInformation,
        DiagnosticArtifactComparison, DiagnosticArtifactMismatchKind, DiagnosticCheckerMode,
        DiagnosticComparisonScope, DiagnosticScorecard, DiagnosticScorecardDiagnostic,
        DiagnosticScorecardProvenance, DiagnosticScorecardSummary, DiagnosticVariantOutcomeClass,
        DiagnosticVariantStatus, FatalVariantRecord, FixedVariantManifest, FixtureChecker,
        OptionVariant, OutputDifferenceKind, ParseError, RunnerOptions, RunnerSummary,
        ScorecardCapabilityRegistry, ScorecardRepositoryRevision, TYPED_CHECKER_CAPABILITY_CODES,
        capability_registry_contains, capability_registry_metadata,
        compare_case_emitted_output_sections, compare_diagnostic_artifacts,
        compare_emitted_output_sections, comparison_frontier, compile_case, compile_case_matrix,
        compile_case_matrix_with_checker, diagnostic_variant_key, error_baseline_unit_order,
        expand_option_matrix, first_different_line, fixed_variant_manifest_digest,
        fixture_compiler_options, matrix_axes, parse_baseline_sections,
        parse_error_baseline_header, render_error_baseline, retain_fatal_variant,
        run_case_against_baseline, run_upstream_baselines, select_variant_baselines,
        validate_fixed_variant_manifest_structure, virtual_unit_path,
    };

    #[test]
    fn checked_in_smoke_manifest_has_the_versioned_static_contract() {
        let manifest: FixedVariantManifest =
            serde_json::from_str(include_str!("../manifests/checker-smoke-v1.json")).unwrap();

        validate_fixed_variant_manifest_structure(&manifest).unwrap();
        assert_eq!(manifest.variants.len(), 96);
        assert_eq!(
            fixed_variant_manifest_digest(&manifest.variants),
            "60dbd52bce2c3f9f94971819ad0d9cda"
        );
    }

    #[test]
    fn checked_in_milestone_manifest_is_a_balanced_smoke_superset() {
        let smoke: FixedVariantManifest =
            serde_json::from_str(include_str!("../manifests/checker-smoke-v1.json")).unwrap();
        let milestone: FixedVariantManifest =
            serde_json::from_str(include_str!("../manifests/checker-milestone-v1.json")).unwrap();

        validate_fixed_variant_manifest_structure(&milestone).unwrap();
        assert_eq!(milestone.variants.len(), 512);
        assert_eq!(milestone.policy.quota_per_family, 64);
        assert_eq!(milestone.policy.expected_diagnostics_per_family.clean, 32);
        assert_eq!(milestone.policy.expected_diagnostics_per_family.error, 32);
        assert_eq!(
            fixed_variant_manifest_digest(&milestone.variants),
            "850c826e464cfb77a725af8b4fec7468"
        );
        assert!(smoke.variants.iter().all(|entry| {
            milestone
                .variants
                .iter()
                .any(|candidate| candidate.variant_key == entry.variant_key)
        }));
        assert!(milestone.variants.iter().any(|entry| {
            entry.case == "_submodules/TypeScript/tests/cases/compiler/asyncFunctionsAcrossFiles.ts"
                && entry.tags.iter().any(|tag| tag == "relative_import_cycle")
        }));
    }

    #[test]
    fn capability_registry_covers_every_typed_checker_code() {
        let metadata = capability_registry_metadata().unwrap();
        assert_eq!(metadata.version, 1);
        assert_eq!(metadata.digest.len(), 32);
        assert!(
            TYPED_CHECKER_CAPABILITY_CODES
                .iter()
                .all(|code| capability_registry_contains(code))
        );
        assert!(
            TYPED_CHECKER_CAPABILITY_CODES
                .iter()
                .all(|code| !code.starts_with("INV."))
        );
    }

    #[cfg(panic = "unwind")]
    #[test]
    fn canonical_checker_unwind_boundary_retains_the_panic_payload() {
        let failure = super::catch_canonical_checker_unwind(
            || -> Result<(), ts_compiler::CanonicalProgramCheckError> {
                panic!("deterministic checker panic payload")
            },
        )
        .unwrap_err();

        let detail = match failure {
            super::FixtureCompilationFailure::CanonicalPanic { detail } => detail,
            other => panic!("expected a retained canonical checker panic, got {other:?}"),
        };
        assert_eq!(
            detail,
            "canonical checker panicked: deterministic checker panic payload"
        );
    }

    #[test]
    fn typed_checker_frontier_dominates_empty_exact_artifacts() {
        let comparison = DiagnosticArtifactComparison::default();
        assert!(comparison.is_exact());

        let (outcome, blocker) = comparison_frontier(
            DiagnosticVariantStatus::UnsupportedDetail,
            &comparison,
            Some((
                "C00.SOURCE_KIND".to_owned(),
                "typed checker boundary".to_owned(),
            )),
        );

        assert_eq!(outcome, DiagnosticVariantOutcomeClass::CheckerCapability);
        assert_eq!(
            blocker.as_ref().and_then(|blocker| blocker.code.as_deref()),
            Some("C00.SOURCE_KIND")
        );
    }

    #[test]
    fn variant_keys_canonicalize_options_and_bind_expected_content() {
        let mut es6 = OptionVariant::default();
        es6.values.insert("target".to_owned(), "ES6".to_owned());
        let mut es2015 = OptionVariant::default();
        es2015
            .values
            .insert("TARGET".to_owned(), "es2015".to_owned());

        let first = diagnostic_variant_key(
            "tests/cases/compiler/input.ts",
            &es6,
            Some("tests/baselines/reference/compiler/input.errors.txt"),
            "expected\n",
        );
        let alias = diagnostic_variant_key(
            "tests/cases/compiler/input.ts",
            &es2015,
            Some("tests/baselines/reference/compiler/input.errors.txt"),
            "expected\n",
        );
        let changed_oracle = diagnostic_variant_key(
            "tests/cases/compiler/input.ts",
            &es2015,
            Some("tests/baselines/reference/compiler/input.errors.txt"),
            "changed\n",
        );

        assert_eq!(first, alias);
        assert_ne!(first, changed_oracle);
        assert_eq!(first.len(), 35);
        assert!(first.starts_with("v1:"));
    }

    #[test]
    fn fatal_variant_is_retained_as_an_invariant_outcome() {
        let mut summary = RunnerSummary {
            executed_variants: 1,
            ..RunnerSummary::default()
        };
        let mut scorecard = DiagnosticScorecard {
            schema_version: 5,
            provenance: DiagnosticScorecardProvenance {
                upstream: ScorecardRepositoryRevision {
                    sha: None,
                    dirty: None,
                },
                rust: ScorecardRepositoryRevision {
                    sha: None,
                    dirty: None,
                },
                manifest_digest: "0".repeat(32),
                digest_algorithm: "xxh3-128".to_owned(),
                fixed_shard: None,
                invocation: Vec::new(),
                capability_registry: ScorecardCapabilityRegistry {
                    version: 1,
                    digest: "0".repeat(32),
                },
            },
            checker_mode: DiagnosticCheckerMode::Canonical,
            comparison_scope: DiagnosticComparisonScope::FullArtifact,
            full_artifact_comparison: true,
            summary: DiagnosticScorecardSummary::default(),
            variants: Vec::new(),
            semantic_artifacts: None,
        };
        let variant = OptionVariant::default();
        let mut writer = Vec::new();

        retain_fatal_variant(
            &mut summary,
            &mut scorecard,
            &mut writer,
            FatalVariantRecord {
                case_path: Path::new("repo/input.ts"),
                repository: Path::new("repo"),
                variant: &variant,
                axes: &[],
                variant_key: "v1:00000000000000000000000000000000".to_owned(),
                scorecard_case: "input.ts".to_owned(),
                expected_baseline: None,
                expected: "",
                semantic_artifacts: None,
                invariant_code: "INV.PROGRAM.DIAGNOSTIC_FORMAT",
                detail: "typed fatal detail".to_owned(),
            },
        )
        .unwrap();

        assert_eq!(summary.executed_variants, 1);
        assert_eq!(summary.mismatched, 1);
        assert_eq!(summary.diagnostic_failures, 1);
        assert!(!summary.is_success());
        assert_eq!(scorecard.summary.executed_variants, 1);
        assert_eq!(scorecard.summary.fatal_invariants, 1);
        assert_eq!(scorecard.variants.len(), 1);
        assert_eq!(
            scorecard.variants[0].outcome_class,
            DiagnosticVariantOutcomeClass::FatalInvariant
        );
        assert_eq!(
            scorecard.variants[0]
                .frontier_blocker
                .as_ref()
                .and_then(|blocker| blocker.code.as_deref()),
            Some("INV.PROGRAM.DIAGNOSTIC_FORMAT")
        );
        assert_eq!(
            String::from_utf8(writer).unwrap(),
            "FATAL input.ts: INV.PROGRAM.DIAGNOSTIC_FORMAT: typed fatal detail\n"
        );
    }

    #[test]
    fn parses_single_file_with_pinned_unit_reconstruction() {
        let source = "// @target: esnext\r\n// @strict: true\r\n\r\nconst answer = 42;\r\n";
        let case = Case::parse("tests/cases/compiler/simple.ts", source).unwrap();

        assert_eq!(case.path, Path::new("tests/cases/compiler/simple.ts"));
        assert_eq!(case.source_text, source);
        assert_eq!(case.units.len(), 1);
        assert_eq!(case.units[0].path, case.path);
        assert_eq!(case.units[0].source_text, "const answer = 42;\n");
        assert_eq!(
            case.directive_values("TARGET").collect::<Vec<_>>(),
            ["esnext"]
        );
        assert_eq!(case.directives[1].line, 2);
        assert_eq!(case.directives[1].raw_text, "// @strict: true");
    }

    #[test]
    fn includes_explicit_node_modules_units_as_pinned_compilation_roots() {
        let case = Case::parse(
            "dependencyUnit.ts",
            concat!(
                "// @target: es2015\n",
                "// @filename: /main.ts\nexport const main = 1;\n",
                "// @filename: /node_modules/pkg/index.ts\nexport const dependency = 1;\n",
            ),
        )
        .unwrap();
        let compilation = compile_case(&case).unwrap();
        assert!(
            compilation
                .outputs
                .keys()
                .any(|path| path.ends_with("main.js"))
        );
        assert!(
            compilation
                .outputs
                .keys()
                .any(|path| path.ends_with("node_modules/pkg/index.js"))
        );
    }

    #[test]
    fn canonical_checker_matches_pinned_simple_multi_file_diagnostics_exactly() {
        // This is the pinned source verbatim: there is deliberately no `noLib`
        // or `lib` directive, so the fixture's default library closure (and its
        // foundational lib.es5 declarations) participates in canonical setup.
        let case = Case::parse(
            "testdata/tests/cases/compiler/simpleTestMultiFile.ts",
            concat!(
                "// @filename: /src/foo.ts\r\n",
                "const x: number = \"\";\r\n",
                "\r\n",
                "// @filename: /src/bar.ts\r\n",
                "const y: string = 1;",
            ),
        )
        .unwrap();
        let mut runs = compile_case_matrix_with_checker(&case, FixtureChecker::Canonical).unwrap();
        assert_eq!(runs.len(), 1);
        let (variant, compilation) = runs.remove(0);

        assert!(
            variant.unsupported_details.is_empty(),
            "{:?}",
            variant.unsupported_details
        );
        assert!(compilation.outputs.is_empty());
        assert_eq!(compilation.diagnostics.len(), 2);
        assert_eq!(
            compilation
                .diagnostics
                .iter()
                .map(|diagnostic| (
                    diagnostic.file_name.as_deref(),
                    diagnostic.range,
                    diagnostic.code,
                    diagnostic.message.as_str(),
                ))
                .collect::<Vec<_>>(),
            [
                (
                    Some("/src/bar.ts"),
                    Some(TextRange::new(TextPos::new(6), TextPos::new(7))),
                    Some(2322),
                    "Type 'number' is not assignable to type 'string'.",
                ),
                (
                    Some("/src/foo.ts"),
                    Some(TextRange::new(TextPos::new(6), TextPos::new(7))),
                    Some(2322),
                    "Type 'string' is not assignable to type 'number'.",
                ),
            ]
        );

        let artifact = render_error_baseline(&case, &compilation.diagnostics);
        assert!(
            artifact.unsupported_details.is_empty(),
            "{:?}",
            artifact.unsupported_details
        );
        assert_eq!(
            artifact.text,
            concat!(
                "/src/bar.ts(1,7): error TS2322: Type 'number' is not assignable to type 'string'.\r\n",
                "/src/foo.ts(1,7): error TS2322: Type 'string' is not assignable to type 'number'.\r\n",
                "\r\n",
                "\r\n",
                "==== /src/foo.ts (1 errors) ====\r\n",
                "    const x: number = \"\";\r\n",
                "          ~\r\n",
                "!!! error TS2322: Type 'string' is not assignable to type 'number'.\r\n",
                "    \r\n",
                "==== /src/bar.ts (1 errors) ====\r\n",
                "    const y: string = 1;\r\n",
                "          ~\r\n",
                "!!! error TS2322: Type 'number' is not assignable to type 'string'.",
            )
        );
    }

    #[test]
    fn canonical_javascript_overwrite_advice_respects_virtual_project_configuration() {
        let inferred = Case::parse(
            "inferredOverwrite.ts",
            concat!(
                "// @allowJs: true\n",
                "// @noCheck: true\n",
                "// @filename: input.js\n",
                "const value = 1;\n",
            ),
        )
        .unwrap();
        let configured = Case::parse(
            "configuredOverwrite.ts",
            concat!(
                "// @allowJs: true\n",
                "// @noCheck: true\n",
                "// @filename: tsconfig.json\n",
                "{}\n",
                "// @filename: input.js\n",
                "const value = 1;\n",
            ),
        )
        .unwrap();
        let advice = ts_diagnostics::message_by_code(5068).unwrap().text();

        for (case, expects_advice) in [(&inferred, true), (&configured, false)] {
            for walk_semantic_artifacts in [false, true] {
                let mut variant = expand_option_matrix(case).remove(0);
                let compilation = super::compile_case_variant(
                    case,
                    &mut variant,
                    FixtureChecker::Canonical,
                    walk_semantic_artifacts,
                )
                .unwrap();
                let diagnostic = compilation
                    .diagnostics
                    .iter()
                    .find(|diagnostic| diagnostic.code == Some(5055))
                    .unwrap();

                assert_eq!(diagnostic.message.contains(advice), expects_advice);
                assert_eq!(compilation.diagnostic_text.contains(advice), expects_advice);
                assert_eq!(
                    compilation.semantic_artifacts.is_some(),
                    walk_semantic_artifacts
                );
            }
        }
    }

    #[test]
    fn canonical_checked_javascript_overwrite_diagnostics_match_artifact_walk() {
        let advice = ts_diagnostics::message_by_code(5068).unwrap().text();
        let primary = ts_diagnostics::message_by_code(5055)
            .unwrap()
            .format(&["/workspace/app/input.js".to_owned()])
            .unwrap();

        for (name, configuration, expects_advice) in [
            ("inferredOverwrite.ts", "", true),
            (
                "configuredOverwrite.ts",
                "// @filename: tsconfig.json\n{}\n",
                false,
            ),
            (
                "javascriptProjectOverwrite.ts",
                concat!(
                    "// @filename: jsconfig.json\n",
                    "{\"compilerOptions\":{\"noEmit\":false}}\n",
                ),
                false,
            ),
        ] {
            let case = Case::parse(
                name,
                format!(
                    concat!(
                        "// @currentDirectory: /workspace/app\n",
                        "// @allowJs: true\n",
                        "// @checkJs: true\n",
                        "// @lib: es5\n",
                        "{}",
                        "// @filename: input.js\n",
                        "const value = 1;\n",
                    ),
                    configuration,
                ),
            )
            .unwrap();
            let mut diagnostic_variant = expand_option_matrix(&case).remove(0);
            let diagnostics_only = super::compile_case_variant(
                &case,
                &mut diagnostic_variant,
                FixtureChecker::Canonical,
                false,
            )
            .unwrap();
            let mut artifact_variant = expand_option_matrix(&case).remove(0);
            let with_artifacts = super::compile_case_variant(
                &case,
                &mut artifact_variant,
                FixtureChecker::Canonical,
                true,
            )
            .unwrap();

            assert_eq!(
                diagnostics_only.diagnostics, with_artifacts.diagnostics,
                "{name}"
            );
            assert_eq!(
                diagnostics_only.diagnostic_text, with_artifacts.diagnostic_text,
                "{name}"
            );

            let [diagnostic] = diagnostics_only.diagnostics.as_slice() else {
                panic!(
                    "expected one overwrite diagnostic for {name}: {:?}",
                    diagnostics_only.diagnostics
                );
            };
            assert_eq!(diagnostic.code, Some(5055), "{name}");
            let expected = if expects_advice {
                format!("{primary}\n  {advice}")
            } else {
                primary.clone()
            };
            assert_eq!(diagnostic.message, expected, "{name}");

            let artifacts = with_artifacts.semantic_artifacts.unwrap();
            assert!(artifacts.types.is_ok(), "{name}: {:?}", artifacts.types);
            assert!(artifacts.symbols.is_ok(), "{name}: {:?}", artifacts.symbols);
            assert!(!artifacts.walk.types.is_empty(), "{name}");
            assert!(!artifacts.walk.symbols.is_empty(), "{name}");
        }
    }

    #[test]
    fn canonical_checker_retains_typed_failures_as_variant_unsupported_details() {
        let case = Case::parse(
            "unsupported.ts",
            concat!(
                "// @module: esnext\n",
                "// @outDir: out\n",
                "// @filename: unsupported.ts\n",
                "const source = [1, 2];\n",
                "const value = [...source];\n",
            ),
        )
        .unwrap();
        let legacy = compile_case(&case).unwrap();
        assert!(legacy.diagnostics.is_empty(), "{:?}", legacy.diagnostics);
        assert!(!legacy.outputs.is_empty());

        let mut runs = compile_case_matrix_with_checker(&case, FixtureChecker::Canonical).unwrap();
        assert_eq!(runs.len(), 1);
        let (variant, compilation) = runs.remove(0);

        assert!(compilation.diagnostics.is_empty());
        assert!(compilation.outputs.is_empty());
        assert_eq!(variant.unsupported_details.len(), 1);
        assert!(
            variant.unsupported_details[0].contains("kind: SpreadElement, role: ArrayElement"),
            "{:?}",
            variant.unsupported_details
        );

        let mut artifact = render_error_baseline(&case, &compilation.diagnostics);
        artifact
            .unsupported_details
            .extend(variant.unsupported_details);
        let comparison = compare_diagnostic_artifacts("", &artifact, &compilation.diagnostics);
        assert_eq!(
            comparison.status(),
            DiagnosticVariantStatus::UnsupportedDetail
        );
    }

    #[test]
    fn canonical_checker_rejects_emitted_output_runner_api() {
        let mut output = Vec::new();
        let error = run_upstream_baselines(
            Path::new("does-not-need-to-exist"),
            &RunnerOptions {
                canonical_checker: true,
                ..RunnerOptions::default()
            },
            &mut output,
        )
        .unwrap_err();
        assert_eq!(error.kind(), std::io::ErrorKind::InvalidInput);
        assert!(error.to_string().contains("diagnostics-only"));
        assert!(output.is_empty());
    }

    #[test]
    fn full_emit_paths_promotes_explicit_node_modules_units() {
        let case = Case::parse(
            "dependencyUnit.ts",
            concat!(
                "// @target: es2015\n",
                "// @fullEmitPaths: true\n",
                "// @filename: /src/main.ts\nexport const main = 1;\n",
                "// @filename: /src/node_modules/pkg/index.ts\nexport const dependency = 1;\n",
            ),
        )
        .unwrap();
        let compilation = compile_case(&case).unwrap();
        assert!(
            compilation
                .outputs
                .keys()
                .any(|path| path.ends_with("node_modules/pkg/index.js")),
            "{:?}",
            compilation.outputs.keys().collect::<Vec<_>>()
        );
    }

    #[test]
    fn full_emit_paths_require_exact_output_paths_instead_of_basename_fallback() {
        let case = Case::parse(
            "fullPaths.ts",
            concat!(
                "// @fullEmitPaths: true\n",
                "// @filename: /src/first/index.ts\n",
                "const value = 1;\n",
            ),
        )
        .unwrap();
        let variant = expand_option_matrix(&case).remove(0);
        assert!(
            variant.unsupported_details.is_empty(),
            "{:?}",
            variant.unsupported_details
        );
        let outputs = BTreeMap::from([(
            "/src/first/index.js".to_owned(),
            "const value = 1;\n".to_owned(),
        )]);
        let matching = compare_case_emitted_output_sections(
            &outputs,
            "//// [/src/first/index.js] ////\nconst value = 1;\n",
            &case,
            &variant,
        );
        assert!(matching.is_match(), "{:?}", matching.differences);

        let wrong_directory = compare_case_emitted_output_sections(
            &outputs,
            "//// [/src/second/index.js] ////\nconst value = 1;\n",
            &case,
            &variant,
        );
        assert_eq!(wrong_directory.differences.len(), 2);
        assert!(matches!(
            wrong_directory.differences[0].kind,
            OutputDifferenceKind::Missing { .. }
        ));
        assert!(matches!(
            wrong_directory.differences[1].kind,
            OutputDifferenceKind::Unexpected { .. }
        ));
    }

    #[test]
    fn omitted_fixture_target_uses_the_current_upstream_default() {
        let case = Case::parse("defaultTarget.ts", "const answer = 42;\n").unwrap();
        let options = fixture_compiler_options(&case, &OptionVariant::default());
        assert_eq!(options.target, ts_options::ScriptTarget::Es2025);

        let case = Case::parse(
            "explicitTarget.ts",
            "// @target: es2015\nconst answer = 42;\n",
        )
        .unwrap();
        let variant = expand_option_matrix(&case).remove(0);
        let options = fixture_compiler_options(&case, &variant);
        assert_eq!(options.target, ts_options::ScriptTarget::Es2015);
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
            "export interface Person { name: string }"
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
    fn relative_units_share_an_explicit_upstream_src_root() {
        let case = Case::parse(
            "srcRoot.ts",
            concat!(
                "// @filename: /.src/node_modules/@types/pkg/index.d.ts\n",
                "declare module 'pkg' {}\n",
                "// @filename: usage.ts\n",
                "import 'pkg';\n",
            ),
        )
        .unwrap();
        assert_eq!(
            virtual_unit_path(&case, &case.units[1], 1),
            "/.src/usage.ts"
        );
    }

    #[test]
    fn normalizes_crlf_and_preserves_trailing_blank_lines_in_virtual_units() {
        let case = Case::parse("trailing.ts", "// @filename: a.js\r\nvalue;\r\n\r\n").unwrap();

        assert_eq!(case.units[0].source_text, "value;\n\n");
    }

    #[test]
    fn rejects_substantive_implicit_unit_before_named_units() {
        let source = "const implicit = 1;\n// @filename: named.ts\nconst named = 2;";
        let error = Case::parse("mixed.ts", source).unwrap_err();

        assert_eq!(error, ParseError::ContentBeforeFirstFile { line: 2 });
    }

    #[test]
    fn drops_comment_trivia_before_the_first_named_unit() {
        let source = concat!(
            "// ordinary comment\n",
            "/* block comment */\n",
            "// @filename: named.ts\n",
            "const named = 2;\n",
        );
        let case = Case::parse("comments.ts", source).unwrap();

        assert_eq!(case.units.len(), 1);
        assert_eq!(case.units[0].path, Path::new("named.ts"));
        assert_eq!(case.units[0].source_text, "const named = 2;\n");
    }

    #[test]
    fn ignores_comment_text_that_is_not_a_directive() {
        let source = "// @not a directive\n// ordinary comment\nconst value = 1;";
        let case = Case::parse("comments.ts", source).unwrap();

        assert!(case.directives.is_empty());
        assert_eq!(case.units[0].source_text, source);
    }

    #[test]
    fn preserves_typescript_error_directive_comments() {
        let source = concat!(
            "// @ts-ignore: explanation\n",
            "const first: number = 'nope';\n",
            "// @ts-expect-error: explanation\n",
            "const second: number = 'nope';\n",
            "// @ts-nocheck: source pragma\n",
            " // @todo: indented source comment\n",
        );
        let case = Case::parse("directives.ts", source).unwrap();

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
    fn removes_a_bom_prefixed_directive_without_changing_fixture_identity() {
        let case = Case::parse("bom.ts", "\u{feff}// @target: es2015\n\nconst value = 1;").unwrap();
        assert!(case.directives.is_empty());
        assert!(case.source_text.as_scannable_str().starts_with('\u{feff}'));
        assert_eq!(
            case.units[0].source_text.as_scannable_str(),
            "const value = 1;"
        );
    }

    #[test]
    fn applies_a_bom_prefixed_compiler_setting_without_changing_fixture_identity() {
        let case = Case::parse(
            "bomStrict.ts",
            concat!(
                "\u{feff}// @strict: false\n",
                "// @target: es2015\n",
                "function value(parameter) {}\n",
            ),
        )
        .unwrap();
        let variant = expand_option_matrix(&case).remove(0);
        assert_eq!(variant.values.len(), 1);
        assert_eq!(variant.values["target"], "es2015");
        assert_eq!(
            case.units[0].source_text.as_scannable_str(),
            "function value(parameter) {}\n"
        );
        let options = fixture_compiler_options(&case, &variant);
        assert!(!options.strict);
        assert!(!options.no_implicit_any);
        let compilation = compile_case(&case).unwrap();
        assert!(
            compilation.diagnostics.is_empty(),
            "{:?}",
            compilation.diagnostics
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
            compilation.outputs["/.src/a.js"],
            "export const value = 1;\n"
        );
        assert!(compilation.outputs["/.src/b.js"].contains("result = value + 1"));
    }

    #[test]
    fn no_implicit_references_and_links_model_the_upstream_harness() {
        let case = Case::parse(
            "linkedBundle.ts",
            concat!(
                "// @declaration: true\n",
                "// @emitDeclarationOnly: true\n",
                "// @outFile: dist/index.d.ts\n",
                "// @currentDirectory: /project\n",
                "// @noImplicitReferences: true\n",
                "// @noLib: true\n",
                "// @filename: /package/index.ts\n",
                "export class External {}\n",
                "// @filename: /project/index.ts\n",
                "import { External } from 'package';\n",
                "export default function value() { return new External(); }\n",
                "// @link: /package -> /project/node_modules/package\n",
            ),
        )
        .unwrap();
        let compilation = compile_case(&case).unwrap();
        assert!(
            compilation.diagnostics.is_empty(),
            "{:?}",
            compilation.diagnostics
        );
        let declaration = &compilation.outputs["/project/dist/index.d.ts"];
        assert_eq!(
            declaration,
            concat!(
                "declare module \"package/index\" {\n",
                "    export class External {\n",
                "    }\n",
                "}\n",
                "declare module \"project/index\" {\n",
                "    import { External } from \"package/index\";\n",
                "    export default function value(): External;\n",
                "}\n",
            )
        );
    }

    #[test]
    fn materializes_unit_symlink_directives_and_relative_links() {
        let symlink = Case::parse(
            "symlink.ts",
            concat!(
                "// @module: commonjs\n",
                "// @target: es2015\n",
                "// @noLib: true\n",
                "// @noImplicitReferences: true\n",
                "// @filename: /shared/index.ts\n",
                "// @symlink: /app/node_modules/pkg/index.ts\n",
                "export const value = 1;\n",
                "// @filename: /app/index.ts\n",
                "import { value } from 'pkg';\n",
                "export const result = value;\n",
            ),
        )
        .unwrap();
        assert!(
            expand_option_matrix(&symlink)[0]
                .unsupported_details
                .is_empty()
        );
        let compilation = compile_case(&symlink).unwrap();
        assert!(
            compilation.diagnostics.is_empty(),
            "{:?}",
            compilation.diagnostics
        );
        assert!(compilation.outputs.contains_key("/app/index.js"));

        let relative_link = Case::parse(
            "relativeLink.ts",
            concat!(
                "// @module: commonjs\n",
                "// @target: es2015\n",
                "// @noLib: true\n",
                "// @noImplicitReferences: true\n",
                "// @filename: packages/pkg/index.ts\n",
                "export const value = 1;\n",
                "// @filename: app/index.ts\n",
                "import { value } from 'pkg';\n",
                "export const result = value;\n",
                "// @link: packages/pkg -> app/node_modules/pkg\n",
            ),
        )
        .unwrap();
        assert!(
            expand_option_matrix(&relative_link)[0]
                .unsupported_details
                .is_empty()
        );
        let compilation = compile_case(&relative_link).unwrap();
        assert!(
            compilation.diagnostics.is_empty(),
            "{:?}",
            compilation.diagnostics
        );
        assert!(compilation.outputs.contains_key("/.src/app/index.js"));
    }

    #[test]
    fn chained_directory_links_resolve_packages_without_copying_virtual_files() {
        let case = Case::parse(
            "chainedLinks.ts",
            concat!(
                "// @module: commonjs\n",
                "// @target: es2015\n",
                "// @noLib: true\n",
                "// @noImplicitReferences: true\n",
                "// @filename: /packages/shared/index.ts\n",
                "export const shared: number = 1;\n",
                "// @filename: /app/index.ts\n",
                "import { shared } from 'shared';\n",
                "export const value: number = shared;\n",
                "// @link: /packages/shared -> /middle/shared\n",
                "// @link: /middle/shared -> /app/node_modules/shared\n",
            ),
        )
        .unwrap();
        let variant = expand_option_matrix(&case).remove(0);
        assert!(
            variant.unsupported_details.is_empty(),
            "{:?}",
            variant.unsupported_details
        );
        let compilation = compile_case(&case).unwrap();
        assert!(
            compilation.diagnostics.is_empty(),
            "{:?}",
            compilation.diagnostics
        );
        assert!(compilation.outputs.contains_key("/app/index.js"));
    }

    #[test]
    fn file_links_follow_case_insensitive_fixture_settings() {
        let case = Case::parse(
            "caseInsensitiveLink.ts",
            concat!(
                "// @module: commonjs\n",
                "// @target: es2015\n",
                "// @noLib: true\n",
                "// @noImplicitReferences: true\n",
                "// @useCaseSensitiveFileNames: false\n",
                "// @filename: /SHARED/Index.ts\n",
                "// @symlink: /APP/node_modules/PKG/index.ts\n",
                "export const shared: number = 1;\n",
                "// @filename: /app/main.ts\n",
                "import { shared } from 'pkg';\n",
                "export const value: number = shared;\n",
            ),
        )
        .unwrap();
        let variant = expand_option_matrix(&case).remove(0);
        assert!(
            variant.unsupported_details.is_empty(),
            "{:?}",
            variant.unsupported_details
        );
        let compilation = compile_case(&case).unwrap();
        assert!(
            compilation.diagnostics.is_empty(),
            "{:?}",
            compilation.diagnostics
        );
        assert!(compilation.outputs.contains_key("/app/main.js"));
    }

    #[test]
    fn custom_current_directory_controls_relative_sources_and_directory_links() {
        let case = Case::parse(
            "customDirectory.ts",
            concat!(
                "// @currentDirectory: /workspace/app\n",
                "// @module: commonjs\n",
                "// @target: es2015\n",
                "// @noLib: true\n",
                "// @noImplicitReferences: true\n",
                "// @filename: packages/pkg/index.ts\n",
                "export const shared: number = 1;\n",
                "// @filename: src/main.ts\n",
                "import { shared } from 'pkg';\n",
                "export const value: number = shared;\n",
                "// @link: packages/pkg -> src/node_modules/pkg\n",
            ),
        )
        .unwrap();
        let variant = expand_option_matrix(&case).remove(0);
        assert!(
            variant.unsupported_details.is_empty(),
            "{:?}",
            variant.unsupported_details
        );
        assert_eq!(
            virtual_unit_path(&case, &case.units[0], 0),
            "/workspace/app/packages/pkg/index.ts"
        );
        assert_eq!(
            virtual_unit_path(&case, &case.units[1], 1),
            "/workspace/app/src/main.ts"
        );
        let compilation = compile_case(&case).unwrap();
        assert!(
            compilation.diagnostics.is_empty(),
            "{:?}",
            compilation.diagnostics
        );
        assert!(
            compilation
                .outputs
                .contains_key("/workspace/app/src/main.js")
        );
    }

    #[test]
    fn relative_current_directory_is_normalized_against_the_upstream_source_root() {
        let case = Case::parse(
            "relativeDirectory.ts",
            concat!(
                "// @currentDirectory: workspace/../project\n",
                "// @filename: src/index.ts\n",
                "const value: number = 1;\n",
            ),
        )
        .unwrap();
        assert!(
            expand_option_matrix(&case)[0]
                .unsupported_details
                .is_empty()
        );
        assert_eq!(
            virtual_unit_path(&case, &case.units[0], 0),
            "/.src/project/src/index.ts"
        );
        assert!(
            compile_case(&case)
                .unwrap()
                .outputs
                .contains_key("/.src/project/src/index.js")
        );
    }

    #[test]
    fn honors_no_emit_from_the_nearest_virtual_project_config() {
        let case = Case::parse(
            "projectNoEmit.ts",
            concat!(
                "// @target: es2015\n",
                "// @filename: /packages/shared/value.ts\n",
                "export const shared = 1;\n",
                "// @filename: /packages/main/tsconfig.json\n",
                "{ \"compilerOptions\": { \"noEmit\": true, \"strict\": true } }\n",
                "// @filename: /packages/main/index.ts\n",
                "const value: number = 1;\n",
            ),
        )
        .unwrap();

        let compilation = compile_case(&case).unwrap();
        assert!(compilation.outputs.is_empty());
        assert!(
            compilation.diagnostics.is_empty(),
            "{:?}",
            compilation.diagnostics
        );
    }

    #[test]
    fn fixture_directives_override_virtual_project_options() {
        let case = Case::parse(
            "projectEmitOverride.ts",
            concat!(
                "// @noEmit: false\n",
                "// @noLib: true\n",
                "// @filename: /project/tsconfig.json\n",
                "{ \"compilerOptions\": { \"noEmit\": true } }\n",
                "// @filename: /project/index.ts\n",
                "const value: number = 1;\n",
            ),
        )
        .unwrap();

        let compilation = compile_case(&case).unwrap();
        assert_eq!(compilation.outputs.len(), 1);
        assert!(compilation.outputs.contains_key("/project/index.js"));
    }

    #[test]
    fn project_config_default_inputs_have_proven_root_and_baseline_order() {
        let case = Case::parse(
            "projectDefaults.ts",
            concat!(
                "// @filename: tsconfig.json\n",
                "{ \"compilerOptions\": { \"strictNullChecks\": true } }\n",
                "// @filename: selected.ts\n",
                "const value: string = undefined;\n",
            ),
        )
        .unwrap();
        let variant = expand_option_matrix(&case).remove(0);
        assert!(
            variant.unsupported_details.is_empty(),
            "{:?}",
            variant.unsupported_details
        );
        let (order, issues) = error_baseline_unit_order(&case);
        assert!(issues.is_empty(), "{issues:?}");
        assert_eq!(order, [0, 1]);
        assert_eq!(compile_case(&case).unwrap().diagnostics.len(), 1);
    }

    #[test]
    fn project_config_explicit_files_exclude_other_virtual_source_roots() {
        let case = Case::parse(
            "projectFiles.ts",
            concat!(
                "// @filename: tsconfig.json\n",
                "{ \"files\": [\"selected.ts\"] }\n",
                "// @filename: ignored.ts\n",
                "const ignored: string = 1;\n",
                "// @filename: selected.ts\n",
                "const selected: number = 1;\n",
            ),
        )
        .unwrap();
        let compilation = compile_case(&case).unwrap();
        assert!(
            compilation.diagnostics.is_empty(),
            "{:?}",
            compilation.diagnostics
        );
        assert!(compilation.outputs.contains_key("/.src/selected.js"));
        assert!(!compilation.outputs.contains_key("/.src/ignored.js"));
        let (order, issues) = error_baseline_unit_order(&case);
        assert!(issues.is_empty(), "{issues:?}");
        assert_eq!(order, [0, 2, 1]);
    }

    #[test]
    fn project_include_and_exclude_patterns_select_exact_virtual_inputs() {
        let case = Case::parse(
            "projectPatterns.ts",
            concat!(
                "// @filename: /app/tsconfig.json\n",
                "{ \"include\": [\"src/**/*.ts\"], \"exclude\": [\"src/generated\"] }\n",
                "// @filename: /app/src/main.ts\n",
                "const first: number = 1;\n",
                "// @filename: /app/src/nested/value.ts\n",
                "const second: number = 2;\n",
                "// @filename: /app/src/generated/ignored.ts\n",
                "const ignored: string = 1;\n",
                "// @filename: /app/outside.ts\n",
                "const outside: string = 1;\n",
            ),
        )
        .unwrap();
        let variant = expand_option_matrix(&case).remove(0);
        assert!(
            variant.unsupported_details.is_empty(),
            "{:?}",
            variant.unsupported_details
        );
        let compilation = compile_case(&case).unwrap();
        assert!(
            compilation.diagnostics.is_empty(),
            "{:?}",
            compilation.diagnostics
        );
        assert!(compilation.outputs.contains_key("/app/src/main.js"));
        assert!(compilation.outputs.contains_key("/app/src/nested/value.js"));
        assert!(
            !compilation
                .outputs
                .contains_key("/app/src/generated/ignored.js")
        );
        assert!(!compilation.outputs.contains_key("/app/outside.js"));
        let (order, issues) = error_baseline_unit_order(&case);
        assert!(issues.is_empty(), "{issues:?}");
        assert_eq!(order, [0, 1, 2, 3, 4]);
    }

    #[test]
    fn project_explicit_files_and_direct_globs_are_combined_in_fixture_order() {
        let case = Case::parse(
            "projectMixedInputs.ts",
            concat!(
                "// @filename: /app/tsconfig.json\n",
                "{ \"files\": [\"outside.ts\"], \"include\": [\"src/*.ts\"] }\n",
                "// @filename: /app/src/nested/ignored.ts\n",
                "const ignored: string = 1;\n",
                "// @filename: /app/outside.ts\n",
                "const outside: number = 1;\n",
                "// @filename: /app/src/main.ts\n",
                "const main: number = 1;\n",
            ),
        )
        .unwrap();
        let variant = expand_option_matrix(&case).remove(0);
        assert!(
            variant.unsupported_details.is_empty(),
            "{:?}",
            variant.unsupported_details
        );
        let compilation = compile_case(&case).unwrap();
        assert!(
            compilation.diagnostics.is_empty(),
            "{:?}",
            compilation.diagnostics
        );
        assert!(compilation.outputs.contains_key("/app/outside.js"));
        assert!(compilation.outputs.contains_key("/app/src/main.js"));
        assert!(
            !compilation
                .outputs
                .contains_key("/app/src/nested/ignored.js")
        );
        let (order, issues) = error_baseline_unit_order(&case);
        assert!(issues.is_empty(), "{issues:?}");
        assert_eq!(order, [0, 2, 3, 1]);
    }

    #[test]
    fn project_patterns_honor_case_insensitive_fixture_filesystems() {
        let case = Case::parse(
            "projectCaseInsensitive.ts",
            concat!(
                "// @useCaseSensitiveFileNames: false\n",
                "// @filename: /App/tsconfig.json\n",
                "{ \"include\": [\"SRC/**/*.TS\"] }\n",
                "// @filename: /app/src/nested/Main.ts\n",
                "const value: number = 1;\n",
            ),
        )
        .unwrap();
        assert!(
            expand_option_matrix(&case)[0]
                .unsupported_details
                .is_empty()
        );
        assert!(
            compile_case(&case)
                .unwrap()
                .outputs
                .contains_key("/app/src/nested/Main.js")
        );
    }

    #[test]
    fn project_extends_lists_apply_each_base_and_preserve_baseline_order() {
        let case = Case::parse(
            "projectExtends.ts",
            concat!(
                "// @filename: /base-one.json\n",
                "{ \"compilerOptions\": { \"strictNullChecks\": true } }\n",
                "// @filename: /base-two.json\n",
                "{ \"compilerOptions\": { \"noImplicitAny\": true } }\n",
                "// @filename: /tsconfig.json\n",
                "{ \"extends\": [\"./base-one.json\", \"./base-two.json\"] }\n",
                "// @filename: /index.ts\n",
                "const value: string = undefined;\n",
            ),
        )
        .unwrap();
        let variant = expand_option_matrix(&case).remove(0);
        assert!(
            variant.unsupported_details.is_empty(),
            "{:?}",
            variant.unsupported_details
        );
        let options = fixture_compiler_options(&case, &variant);
        assert!(options.strict_null_checks);
        assert!(options.no_implicit_any);
        let (order, issues) = error_baseline_unit_order(&case);
        assert!(issues.is_empty(), "{issues:?}");
        assert_eq!(order, [2, 3, 0, 1]);
        assert_eq!(compile_case(&case).unwrap().diagnostics.len(), 1);
    }

    #[test]
    fn project_config_array_recovers_its_first_configuration_object() {
        let case = Case::parse(
            "malformedProject.ts",
            concat!(
                "// @filename: tsconfig.json\n",
                "[{\"compilerOptions\": {\"types\": [\"nonexistent\"]}}]\n",
                "// @filename: index.ts\n",
                "export const value = 1;\n",
            ),
        )
        .unwrap();
        let variant = expand_option_matrix(&case).remove(0);
        assert!(
            variant.unsupported_details.is_empty(),
            "{:?}",
            variant.unsupported_details
        );
        let options = fixture_compiler_options(&case, &variant);
        assert_eq!(options.types, Some(vec!["nonexistent".to_owned()]));
        let compilation = compile_case(&case).unwrap();
        assert_eq!(compilation.diagnostics.len(), 1);
        assert_eq!(compilation.diagnostics[0].code, Some(2688));
        assert_eq!(
            compilation.diagnostics[0].message,
            concat!(
                "Cannot find type definition file for 'nonexistent'.\n",
                "  The file is in the program because:\n",
                "    Entry point of type library 'nonexistent' specified in compilerOptions",
            )
        );
    }

    #[test]
    fn no_implicit_references_selects_the_last_source_without_an_unsupported_detail() {
        let case = Case::parse(
            "explicitRoots.ts",
            concat!(
                "// @noImplicitReferences: true\n",
                "// @filename: ignored.ts\n",
                "const ignored: string = 1;\n",
                "// @filename: selected.ts\n",
                "const selected: number = 1;\n",
            ),
        )
        .unwrap();
        let variant = expand_option_matrix(&case).remove(0);
        assert!(
            variant.unsupported_details.is_empty(),
            "{:?}",
            variant.unsupported_details
        );
        let compilation = compile_case(&case).unwrap();
        assert!(
            compilation.diagnostics.is_empty(),
            "{:?}",
            compilation.diagnostics
        );
        assert!(compilation.outputs.contains_key("/.src/selected.js"));
        assert!(!compilation.outputs.contains_key("/.src/ignored.js"));
        let (order, issues) = error_baseline_unit_order(&case);
        assert!(issues.is_empty(), "{issues:?}");
        assert_eq!(order, [1, 0]);
    }

    #[test]
    fn fixture_compilation_retains_compiler_option_validation_diagnostics() {
        let case = Case::parse(
            "checkJsOptions.ts",
            concat!(
                "// @allowJs: false\n",
                "// @checkJs: true\n",
                "// @noEmit: true\n",
                "// @filename: a.js\n",
                "var value;\n",
            ),
        )
        .unwrap();
        let compilation = compile_case(&case).unwrap();
        let option_diagnostics = compilation
            .diagnostics
            .iter()
            .filter(|diagnostic| diagnostic.code == Some(5052))
            .collect::<Vec<_>>();
        assert_eq!(option_diagnostics.len(), 1, "{:?}", compilation.diagnostics);
        assert_eq!(
            option_diagnostics[0].message,
            "Option 'checkJs' cannot be specified without specifying option 'allowJs'."
        );
    }

    #[test]
    fn moduleless_fixtures_preserve_exports_and_commonjs_remains_explicit() {
        let preserved = Case::parse(
            "preserved.ts",
            "// @target: es2015\n// @noLib: true\nexport const value: number = 1;\n",
        )
        .unwrap();
        let preserved = compile_case(&preserved).unwrap();
        let javascript = &preserved.outputs["/.src/preserved.js"];
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
        let javascript = &commonjs.outputs["/.src/commonjs.js"];
        assert!(javascript.contains("exports.value = 1;"), "{javascript}");
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
    fn parses_multiline_error_baseline_header_and_normalizes_line_endings() {
        let baseline = concat!(
            "\u{feff}input.ts(3,6): error TS2322: Type 'string | number' is not assignable to type 'string'.\r\n",
            "  Type 'number' is not assignable to type 'string'.\r\n",
            "\r\n",
            "\r\n",
            "!!! error TS2318: An annotated global diagnostic outside the header.\r\n",
            "==== input.ts (1 errors) ====\r\n",
            "    const value = source;\r\n",
            "          ~~~~~\r\n",
            "!!! error TS2322: Type 'string | number' is not assignable to type 'string'.\r\n",
        );
        assert_eq!(
            parse_error_baseline_header(baseline),
            concat!(
                "input.ts(3,6): error TS2322: Type 'string | number' is not assignable to type 'string'.\n",
                "  Type 'number' is not assignable to type 'string'.",
            )
        );
    }

    #[test]
    fn renders_global_related_crlf_and_utf8_diagnostic_artifacts_exactly() {
        let case = Case::parse("global.ts", "const café = 1;\r\n").unwrap();
        let source = case.units[0].source_text.clone();
        let related_start = u32::try_from(source.as_scannable_str().find('=').unwrap()).unwrap();
        let diagnostic = CompilationDiagnostic {
            file_name: None,
            source_text: None,
            range: None,
            code: Some(2318),
            category: Some(CompilationDiagnosticCategory::Error),
            message: "Cannot find global type 'Array'.".to_owned(),
            related_information: Some(vec![CompilationRelatedInformation {
                file_name: Some("/case/global.ts".to_owned()),
                source_text: Some(source),
                range: Some(TextRange::new(
                    TextPos::new(related_start),
                    TextPos::new(related_start + 1),
                )),
                code: Some(2728),
                category: Some(CompilationDiagnosticCategory::Message),
                message: "The declaration is here.".to_owned(),
            }]),
        };

        let artifact = render_error_baseline(&case, &[diagnostic]);
        assert!(artifact.unsupported_details.is_empty());
        assert_eq!(
            artifact.text,
            concat!(
                "error TS2318: Cannot find global type 'Array'.\r\n",
                "\r\n",
                "\r\n",
                "!!! error TS2318: Cannot find global type 'Array'.\r\n",
                "!!! related TS2728 global.ts:1:12: The declaration is here.\r\n",
                "==== global.ts (0 errors) ====\r\n",
                "    const café = 1;\r\n",
                "    ",
            )
        );
    }

    #[test]
    fn renders_same_and_cross_file_related_records_in_owned_order() {
        let case = Case::parse(
            "related.ts",
            concat!(
                "// @filename: /src/a.ts\n",
                "const primary = 1; const same = 2;\n",
                "// @filename: /src/b.ts\n",
                "const cross = 3;",
            ),
        )
        .unwrap();
        let first_source = case.units[0].source_text.clone();
        let second_source = case.units[1].source_text.clone();
        let primary_start =
            u32::try_from(first_source.as_scannable_str().find("primary").unwrap()).unwrap();
        let same_start =
            u32::try_from(first_source.as_scannable_str().find("same").unwrap()).unwrap();
        let cross_start =
            u32::try_from(second_source.as_scannable_str().find("cross").unwrap()).unwrap();
        let diagnostic = CompilationDiagnostic {
            file_name: Some("/src/a.ts".to_owned()),
            source_text: Some(first_source.clone()),
            range: Some(TextRange::new(
                TextPos::new(primary_start),
                TextPos::new(primary_start + 7),
            )),
            code: Some(2451),
            category: Some(CompilationDiagnosticCategory::Error),
            message: "Cannot redeclare block-scoped variable 'primary'.".to_owned(),
            related_information: Some(vec![
                CompilationRelatedInformation {
                    file_name: Some("/src/a.ts".to_owned()),
                    source_text: Some(first_source),
                    range: Some(TextRange::new(
                        TextPos::new(same_start),
                        TextPos::new(same_start + 4),
                    )),
                    code: Some(6203),
                    category: Some(CompilationDiagnosticCategory::Message),
                    message: "'primary' was also declared here.".to_owned(),
                },
                CompilationRelatedInformation {
                    file_name: Some("/src/b.ts".to_owned()),
                    source_text: Some(second_source),
                    range: Some(TextRange::new(
                        TextPos::new(cross_start),
                        TextPos::new(cross_start + 5),
                    )),
                    code: Some(6204),
                    category: Some(CompilationDiagnosticCategory::Message),
                    message: "and here.".to_owned(),
                },
            ]),
        };

        let artifact = render_error_baseline(&case, std::slice::from_ref(&diagnostic));
        assert!(artifact.unsupported_details.is_empty());
        let same = artifact
            .text
            .find("!!! related TS6203 /src/a.ts:1:26: 'primary' was also declared here.")
            .unwrap();
        let cross = artifact
            .text
            .find("!!! related TS6204 /src/b.ts:1:7: and here.")
            .unwrap();
        assert!(same < cross, "{}", artifact.text);

        let scorecard = DiagnosticScorecardDiagnostic::from(&diagnostic);
        assert_eq!(scorecard.related_information.len(), 2);
        assert_eq!(
            scorecard
                .related_information
                .iter()
                .map(|related| (related.file_name.as_deref(), related.code))
                .collect::<Vec<_>>(),
            [
                (Some("/src/a.ts"), Some(6203)),
                (Some("/src/b.ts"), Some(6204)),
            ]
        );
    }

    #[test]
    fn renders_multifile_multiline_spans_and_messages_exactly() {
        let case = Case::parse(
            "multifile.ts",
            concat!(
                "// @filename: a.ts\r\n",
                "const first = 1;\r\n",
                "// @filename: b.ts\r\n",
                "const value:\r\n",
                "    string = 1;\r\n",
            ),
        )
        .unwrap();
        let source = case.units[1].source_text.clone();
        let start = u32::try_from(source.as_scannable_str().find("value").unwrap()).unwrap();
        let end = u32::try_from(source.as_scannable_str().find("string").unwrap() + "string".len())
            .unwrap();
        let diagnostic = CompilationDiagnostic {
            file_name: Some("/case/b.ts".to_owned()),
            source_text: Some(source),
            range: Some(TextRange::new(TextPos::new(start), TextPos::new(end))),
            code: Some(9999),
            category: Some(CompilationDiagnosticCategory::Error),
            message: "First line.\nSecond line.".to_owned(),
            related_information: None,
        };

        let artifact = render_error_baseline(&case, &[diagnostic]);
        assert!(artifact.unsupported_details.is_empty());
        assert_eq!(
            artifact.text,
            concat!(
                "b.ts(1,7): error TS9999: First line.\r\n",
                "Second line.\r\n",
                "\r\n",
                "\r\n",
                "==== a.ts (0 errors) ====\r\n",
                "    const first = 1;\r\n",
                "==== b.ts (1 errors) ====\r\n",
                "    const value:\r\n",
                "          ~~~~~~\r\n",
                "        string = 1;\r\n",
                "    ~~~~~~~~~~\r\n",
                "!!! error TS9999: First line.\r\n",
                "!!! error TS9999: Second line.\r\n",
                "    ",
            )
        );
    }

    #[test]
    fn diagnostic_artifact_diff_classifies_exact_header_code_span_message_and_order() {
        let case = Case::parse("input.ts", "const value = 1;\n").unwrap();
        let source = case.units[0].source_text.clone();
        let diagnostic = CompilationDiagnostic {
            file_name: Some("/case/input.ts".to_owned()),
            source_text: Some(source),
            range: Some(TextRange::new(TextPos::new(6), TextPos::new(11))),
            code: Some(1000),
            category: Some(CompilationDiagnosticCategory::Error),
            message: "Original message.".to_owned(),
            related_information: None,
        };
        let actual = render_error_baseline(&case, std::slice::from_ref(&diagnostic));
        assert!(
            compare_diagnostic_artifacts(&actual.text, &actual, std::slice::from_ref(&diagnostic))
                .is_exact()
        );

        let line_endings = actual.text.replace("\r\n", "\n");
        assert_eq!(
            compare_diagnostic_artifacts(&line_endings, &actual, std::slice::from_ref(&diagnostic))
                .mismatch_kinds,
            [DiagnosticArtifactMismatchKind::HeaderOnly]
        );
        let code = actual.text.replace("TS1000", "TS1001");
        assert_eq!(
            compare_diagnostic_artifacts(&code, &actual, std::slice::from_ref(&diagnostic))
                .mismatch_kinds,
            [DiagnosticArtifactMismatchKind::Code]
        );
        let span = actual.text.replacen("(1,7)", "(1,8)", 1);
        assert_eq!(
            compare_diagnostic_artifacts(&span, &actual, std::slice::from_ref(&diagnostic))
                .mismatch_kinds,
            [DiagnosticArtifactMismatchKind::Span]
        );
        let message = actual
            .text
            .replace("Original message.", "Different message.");
        assert_eq!(
            compare_diagnostic_artifacts(&message, &actual, std::slice::from_ref(&diagnostic))
                .mismatch_kinds,
            [DiagnosticArtifactMismatchKind::Message]
        );

        let globals = [
            CompilationDiagnostic {
                file_name: None,
                source_text: None,
                range: None,
                code: Some(1000),
                category: Some(CompilationDiagnosticCategory::Error),
                message: "First.".to_owned(),
                related_information: None,
            },
            CompilationDiagnostic {
                file_name: None,
                source_text: None,
                range: None,
                code: Some(2000),
                category: Some(CompilationDiagnosticCategory::Error),
                message: "Second.".to_owned(),
                related_information: None,
            },
        ];
        let actual = render_error_baseline(&case, &globals);
        let (header, body) = actual.text.split_once("\r\n\r\n\r\n").unwrap();
        let mut header_lines = header.split("\r\n").collect::<Vec<_>>();
        header_lines.reverse();
        let reordered = format!("{}\r\n\r\n\r\n{body}", header_lines.join("\r\n"));
        assert_eq!(
            compare_diagnostic_artifacts(&reordered, &actual, &globals).mismatch_kinds,
            [DiagnosticArtifactMismatchKind::Order]
        );
    }

    #[test]
    fn expected_related_information_is_unsupported_when_checker_does_not_expose_it() {
        let case = Case::parse("global.ts", "").unwrap();
        let diagnostic = CompilationDiagnostic {
            file_name: None,
            source_text: None,
            range: None,
            code: Some(2318),
            category: Some(CompilationDiagnosticCategory::Error),
            message: "Global error.".to_owned(),
            related_information: None,
        };
        let actual = render_error_baseline(&case, std::slice::from_ref(&diagnostic));
        let expected = actual.text.replacen(
            "\r\n====",
            "\r\n!!! related TS2728: Missing checker detail.\r\n====",
            1,
        );
        let comparison =
            compare_diagnostic_artifacts(&expected, &actual, std::slice::from_ref(&diagnostic));
        assert_eq!(
            comparison.status(),
            super::DiagnosticVariantStatus::UnsupportedDetail
        );
        assert!(
            comparison
                .mismatch_kinds
                .contains(&DiagnosticArtifactMismatchKind::UnsupportedDetail)
        );
        assert!(!comparison.unsupported_details.is_empty());
    }

    #[test]
    fn normalizes_upstream_prefixes_inside_messages_and_rejects_ambiguous_ordering() {
        let case = Case::parse("global.ts", "").unwrap();
        let diagnostics = [
            CompilationDiagnostic {
                file_name: None,
                source_text: None,
                range: None,
                code: Some(1000),
                category: Some(CompilationDiagnosticCategory::Error),
                message: "See /.src/first.ts.".to_owned(),
                related_information: None,
            },
            CompilationDiagnostic {
                file_name: None,
                source_text: None,
                range: None,
                code: Some(1000),
                category: Some(CompilationDiagnosticCategory::Error),
                message: "See bundled:///libs/second.d.ts.".to_owned(),
                related_information: None,
            },
        ];
        let artifact = render_error_baseline(&case, &diagnostics);
        assert!(artifact.text.contains("See first.ts."));
        assert!(artifact.text.contains("See second.d.ts."));
        assert!(!artifact.text.contains("/.src/"));
        assert!(!artifact.text.contains("bundled:///libs/"));
        assert!(!artifact.unsupported_details.is_empty());

        let comparison = compare_diagnostic_artifacts(&artifact.text, &artifact, &diagnostics);
        assert!(!comparison.is_exact());
        assert_eq!(
            comparison.status(),
            super::DiagnosticVariantStatus::UnsupportedDetail
        );
    }

    #[test]
    fn parses_baseline_section_names_containing_brackets() {
        let sections = parse_baseline_sections(concat!(
            "//// [input[one].ts] ////\n",
            "const value: number = 1;\n",
            "//// [input[one].js] ////\n",
            "const value = 1;\n",
        ));
        assert_eq!(sections["input[one].ts"], "const value: number = 1;\n");
        assert_eq!(sections["input[one].js"], "const value = 1;\n");
    }

    #[test]
    fn parses_section_marker_appended_to_source_map_url() {
        let sections = parse_baseline_sections(concat!(
            "//// [a.d.ts] ////\n",
            "declare const a: number;\n",
            "//# sourceMappingURL=a.d.ts.map",
            "//// [b.d.ts] ////\n",
            "declare const b: number;\n",
        ));
        assert_eq!(
            sections["a.d.ts"],
            "declare const a: number;\n//# sourceMappingURL=a.d.ts.map\n"
        );
        assert_eq!(sections["b.d.ts"], "declare const b: number;\n");
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
            compilation.outputs["/.src/out.js"],
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
    fn repeated_scalar_option_directives_use_the_last_value() {
        let case = Case::parse(
            "repeated.ts",
            concat!(
                "// @outFile: first.js\n",
                "// @outFile: second.js\n",
                "const value = 1;\n",
            ),
        )
        .unwrap();
        let variants = expand_option_matrix(&case);
        assert_eq!(variants.len(), 1);
        assert_eq!(
            variants[0].values.get("outFile").map(String::as_str),
            Some("second.js")
        );
    }

    #[test]
    fn ignore_deprecations_is_scalar_without_changing_variant_identity() {
        let ordinary = Case::parse(
            "deprecations.ts",
            concat!("// @target: es2015, esnext\n", "const value = 1;\n"),
        )
        .unwrap();
        let configured_case = Case::parse(
            "deprecations.ts",
            concat!(
                "// @ignoreDeprecations: 5.0\n",
                "// @IGNOREDEPRECATIONS: 6.0;\n",
                "// @target: es2015, esnext\n",
                "const value = 1;\n",
            ),
        )
        .unwrap();
        let ordinary_variants = expand_option_matrix(&ordinary);
        let configured_variants = expand_option_matrix(&configured_case);

        assert_eq!(matrix_axes(&ordinary), matrix_axes(&configured_case));
        assert_eq!(ordinary_variants.len(), configured_variants.len());
        for (ordinary_variant, configured_variant) in
            ordinary_variants.iter().zip(&configured_variants)
        {
            assert_eq!(ordinary_variant.values, configured_variant.values);
            assert!(configured_variant.unsupported_details.is_empty());
            assert_eq!(
                diagnostic_variant_key("deprecations.ts", ordinary_variant, None, "expected"),
                diagnostic_variant_key("deprecations.ts", configured_variant, None, "expected"),
            );
            assert_eq!(
                fixture_compiler_options(&configured_case, configured_variant)
                    .ignore_deprecations
                    .as_deref(),
                Some("6.0")
            );
        }
    }

    #[test]
    fn ignore_deprecations_overrides_projects_without_hiding_unknown_directives() {
        let case = Case::parse(
            "projectDeprecations.ts",
            concat!(
                "// @ignoreDeprecations: 6.0\n",
                "// @unknownAxis: enabled\n",
                "// @filename: /project/tsconfig.json\n",
                "{\"compilerOptions\":{\"ignoreDeprecations\":\"5.0\"}}\n",
                "// @filename: /project/main.ts\n",
                "const value = 1;\n",
            ),
        )
        .unwrap();
        let variants = expand_option_matrix(&case);

        assert_eq!(variants.len(), 1);
        assert!(!variants[0].values.contains_key("ignoreDeprecations"));
        assert!(
            variants[0]
                .unsupported_details
                .iter()
                .any(|detail| detail.contains("@unknownAxis"))
        );
        assert!(
            variants[0]
                .unsupported_details
                .iter()
                .all(|detail| !detail.contains("ignoreDeprecations"))
        );
        assert_eq!(
            fixture_compiler_options(&case, &variants[0])
                .ignore_deprecations
                .as_deref(),
            Some("6.0")
        );
    }

    #[test]
    fn applies_bom_prefixed_ignore_deprecations_without_a_variant_axis() {
        let case = Case::parse(
            "bomDeprecations.ts",
            "\u{feff}// @ignoreDeprecations: 6.0\nconst value = 1;\n",
        )
        .unwrap();
        let variants = expand_option_matrix(&case);

        assert!(case.directives.is_empty());
        assert_eq!(variants.len(), 1);
        assert!(variants[0].values.is_empty());
        assert!(variants[0].unsupported_details.is_empty());
        assert_eq!(
            fixture_compiler_options(&case, &variants[0])
                .ignore_deprecations
                .as_deref(),
            Some("6.0")
        );
    }

    #[test]
    fn repeated_target_directive_emits_each_requested_variant() {
        let case = Case::parse(
            "useStrictLikePrologueString01.ts",
            concat!(
                "//@target: commonjs\n",
                "//@target: es5, es2015\n\n",
                "\"hey!\"\n",
                "\" use strict \"\n",
                "export function f() {   \n}\n",
            ),
        )
        .unwrap();
        assert_eq!(matrix_axes(&case), ["target"]);
        let matrix = compile_case_matrix(&case).unwrap();
        assert_eq!(matrix.len(), 2);
        for (variant, compilation) in matrix {
            let output = compilation
                .outputs
                .get("/.src/useStrictLikePrologueString01.js")
                .unwrap();
            let expected = if variant.values["target"] == "es5" {
                concat!(
                    "\"use strict\";\n",
                    "\"hey!\";\n",
                    "\" use strict \";\n",
                    "Object.defineProperty(exports, \"__esModule\", { value: true });\n",
                    "exports.f = f;\n",
                    "function f() {\n}\n",
                )
            } else {
                "\"hey!\";\n\" use strict \";\nexport function f() {\n}\n"
            };
            assert_eq!(output, expected, "variant={variant:?}");
        }
    }

    #[test]
    fn selects_matrix_baselines_using_complete_axis_values() {
        let paths = [
            PathBuf::from("case(jsx=react,module=commonjs).js"),
            PathBuf::from("case(jsx=react-jsx,module=commonjs).js"),
            PathBuf::from("case(jsx=react-jsxdev,module=commonjs).js"),
        ];
        let candidates = paths.iter().collect::<Vec<_>>();
        let variant = OptionVariant {
            values: BTreeMap::from([
                ("jsx".to_owned(), "react".to_owned()),
                ("module".to_owned(), "commonjs".to_owned()),
            ]),
            ..OptionVariant::default()
        };
        let selected = select_variant_baselines(
            &candidates,
            "case",
            &variant,
            &["jsx".to_owned(), "module".to_owned()],
        );
        assert_eq!(selected, vec![&paths[0]]);
    }

    #[test]
    fn matrix_baseline_selection_has_no_untagged_or_partial_fallback() {
        let paths = [
            PathBuf::from("case.js"),
            PathBuf::from("case(module=commonjs).js"),
            PathBuf::from("case(module=commonjs,target=esnext,extra=true).js"),
        ];
        let candidates = paths.iter().collect::<Vec<_>>();
        let variant = OptionVariant {
            values: BTreeMap::from([
                ("module".to_owned(), "commonjs".to_owned()),
                ("target".to_owned(), "esnext".to_owned()),
            ]),
            ..OptionVariant::default()
        };

        assert!(
            select_variant_baselines(
                &candidates,
                "case",
                &variant,
                &["module".to_owned(), "target".to_owned()],
            )
            .is_empty()
        );
    }

    #[test]
    fn expands_boolean_wildcard_matrix_axes() {
        let case = Case::parse(
            "wildcards.ts",
            "// @isolatedDeclarations: *\n// @strictBuiltinIteratorReturn: *\nconst x = 1;\n",
        )
        .unwrap();
        let variants = expand_option_matrix(&case);
        assert_eq!(variants.len(), 4);
        assert_eq!(
            matrix_axes(&case),
            vec![
                "isolatedDeclarations".to_owned(),
                "strictBuiltinIteratorReturn".to_owned(),
            ]
        );
    }

    #[test]
    fn applies_strict_builtin_iterator_return_without_hiding_module_resolution_skips() {
        let case = Case::parse(
            "iteratorReturn.ts",
            concat!(
                "// @strict: true\n",
                "// @strictBuiltinIteratorReturn: *\n",
                "const value = 1;\n",
            ),
        )
        .unwrap();
        let variants = expand_option_matrix(&case);
        assert_eq!(variants.len(), 2);
        for (variant, expected) in variants.iter().zip([true, false]) {
            assert!(variant.unsupported_details.is_empty());
            let options = fixture_compiler_options(&case, variant);
            assert_eq!(options.strict_builtin_iterator_return, expected);
            assert!(options.strict_builtin_iterator_return_specified);
        }

        let classic = Case::parse(
            "settingsSimpleTest.ts",
            concat!(
                "// @strict: true\n",
                "// @strictBuiltinIteratorReturn: *, !true\n",
                "// @moduleResolution: classic\n",
                "const value = 1;\n",
            ),
        )
        .unwrap();
        let variants = expand_option_matrix(&classic);
        assert_eq!(variants.len(), 1);
        assert_eq!(variants[0].values["strictBuiltinIteratorReturn"], "false");
        assert_eq!(
            variants[0].unsupported_details,
            ["pinned Go harness skips node10 and classic module resolution"]
        );
        let options = fixture_compiler_options(&classic, &variants[0]);
        assert!(!options.strict_builtin_iterator_return);
        assert!(options.strict_builtin_iterator_return_specified);
    }

    #[test]
    fn applies_supported_function_variance_and_error_truncation_options() {
        let case = Case::parse(
            "supportedCheckerOptions.ts",
            concat!(
                "// @strict: false\n",
                "// @strictFunctionTypes: true\n",
                "// @noErrorTruncation: false\n",
                "const value = 1;\n",
            ),
        )
        .unwrap();
        let variant = expand_option_matrix(&case).remove(0);
        assert!(
            variant.unsupported_details.is_empty(),
            "{:?}",
            variant.unsupported_details
        );
        let options = fixture_compiler_options(&case, &variant);
        assert!(!options.strict);
        assert!(options.strict_function_types);
        assert!(options.strict_function_types_specified);
        assert!(!options.no_error_truncation);
    }

    #[test]
    fn only_applies_unused_label_suppression_to_enabled_variants() {
        for (setting, expected_values, supported) in [
            ("true", &["true"][..], true),
            ("false", &["false"][..], false),
            ("true, false", &["true", "false"][..], false),
        ] {
            let case = Case::parse(
                "unusedLabels.ts",
                format!(
                    "// @target: es2015\n// @allowUnusedLabels: {setting}\nouter:\ninner:\nwhile (true) {{ break outer; }}\n"
                ),
            )
            .unwrap();
            let variants = expand_option_matrix(&case);
            assert_eq!(variants.len(), expected_values.len(), "{setting}");

            for (variant, expected) in variants.iter().zip(expected_values) {
                assert_eq!(variant.values["allowUnusedLabels"], *expected, "{setting}");
                assert_eq!(
                    variant.unsupported_details.is_empty(),
                    supported,
                    "{setting}: {:?}",
                    variant.unsupported_details
                );
                if !supported {
                    assert_eq!(
                        variant.unsupported_details,
                        [format!(
                            "compiler option allowUnusedLabels is configured as {setting:?}, but Rust does not apply it"
                        )]
                    );
                }
                assert_eq!(
                    fixture_compiler_options(&case, variant).allow_unused_labels,
                    Some(*expected == "true")
                );
            }
        }
    }

    #[test]
    fn applies_package_json_exports_and_imports_option_variants() {
        let case = Case::parse(
            "packageResolution.ts",
            concat!(
                "// @moduleResolution: bundler\n",
                "// @resolvePackageJsonExports: *\n",
                "// @resolvePackageJsonImports: *\n",
                "const value = 1;\n",
            ),
        )
        .unwrap();
        let variants = expand_option_matrix(&case);
        assert_eq!(variants.len(), 4);
        for variant in variants {
            assert!(variant.unsupported_details.is_empty());
            let options = fixture_compiler_options(&case, &variant);
            assert_eq!(
                options.resolve_package_json_exports,
                variant.values["resolvePackageJsonExports"] == "true"
            );
            assert_eq!(
                options.resolve_package_json_imports,
                variant.values["resolvePackageJsonImports"] == "true"
            );
        }
    }

    #[test]
    fn expands_pinned_target_wildcard_exclusions_and_aliases() {
        let case = Case::parse(
            "callChainWithSuper.ts",
            concat!(
                "// @target: *,-es3\r\n",
                "// @strict: true\r\n",
                "// @noTypesAndSymbols: true\r\n",
                "\r\n",
                "// GH#34952\r\n",
                "class Base { method?() {} }\r\n",
                "class Derived extends Base {\r\n",
                "    method1() { return super.method?.(); }\r\n",
                "    method2() { return super[\"method\"]?.(); }\r\n",
                "}\r\n",
            ),
        )
        .unwrap();
        let variants = expand_option_matrix(&case);
        let targets = variants
            .iter()
            .map(|variant| variant.values["target"].as_str())
            .collect::<Vec<_>>();

        assert_eq!(
            targets,
            [
                "es5", "es6", "es2016", "es2017", "es2018", "es2019", "es2020", "es2021", "es2022",
                "es2023", "es2024", "es2025", "esnext",
            ]
        );
        assert_eq!(matrix_axes(&case), ["target"]);
        assert!(
            variants[0]
                .unsupported_details
                .iter()
                .any(|detail| detail.contains("target ES5"))
        );
        assert!(
            variants[1..]
                .iter()
                .all(|variant| variant.unsupported_details.is_empty())
        );
    }

    #[test]
    fn does_not_expand_non_varying_or_empty_pinned_options() {
        let case = Case::parse(
            "nonVarying.ts",
            concat!(
                "// @noCheck: true,false\n",
                "// @strict:\n",
                "const value = 1;\n",
            ),
        )
        .unwrap();
        let variants = expand_option_matrix(&case);

        assert_eq!(variants.len(), 1);
        assert_eq!(variants[0].values["noCheck"], "true,false");
        assert!(!variants[0].values.contains_key("strict"));
        assert!(matrix_axes(&case).is_empty());
        assert!(
            variants[0]
                .unsupported_details
                .iter()
                .any(|detail| detail.contains("invalid boolean value"))
        );
    }

    #[test]
    fn mirrors_pinned_go_unsupported_option_skips() {
        for (directive, expected) in [
            ("// @module: amd\n", "AMD, UMD, and System"),
            ("// @module: umd\n", "AMD, UMD, and System"),
            ("// @module: system\n", "AMD, UMD, and System"),
            ("// @moduleResolution: node10\n", "node10 and classic"),
            ("// @moduleResolution: classic\n", "node10 and classic"),
            ("// @esModuleInterop: false\n", "esModuleInterop=false"),
            (
                "// @allowSyntheticDefaultImports: false\n",
                "allowSyntheticDefaultImports=false",
            ),
            ("// @alwaysStrict: false\n", "alwaysStrict=false"),
            ("// @baseUrl: .\n", "nonempty baseUrl"),
            ("// @outFile: output.js\n", "nonempty outFile"),
            ("// @target: es5\n", "target ES5"),
        ] {
            let case =
                Case::parse("unsupported.ts", format!("{directive}const value = 1;\n")).unwrap();
            let variants = expand_option_matrix(&case);
            assert_eq!(variants.len(), 1, "{directive:?}");
            assert!(
                variants[0]
                    .unsupported_details
                    .iter()
                    .any(|detail| detail.contains(expected)),
                "{directive:?}: {:?}",
                variants[0].unsupported_details
            );
        }
    }

    #[test]
    fn refuses_exactness_for_unmodeled_harness_and_project_semantics() {
        for (source, expected) in [
            (
                "// @useCaseSensitiveFileNames: invalid\nconst value = 1;\n",
                "boolean useCaseSensitiveFileNames",
            ),
            (
                "// @fullEmitPaths: invalid\nconst value = 1;\n",
                "invalid boolean value",
            ),
            (
                concat!(
                    "// @filename: tsconfig.json\n",
                    "{\"include\":[\"src/**/generated/*.ts\"]}\n",
                    "// @filename: src/index.ts\n",
                    "const value = 1;\n",
                ),
                "include/exclude pattern",
            ),
            (
                "// @captureSuggestions: true\nconst value = 1;\n",
                "suggestion diagnostics",
            ),
            (
                "// @link: missing-target\nconst value = 1;\n",
                "source -> target directory link",
            ),
            ("// @symlink:   \nconst value = 1;\n", "file symlink target"),
        ] {
            let case = Case::parse("unsupported.ts", source).unwrap();
            let variant = expand_option_matrix(&case).remove(0);
            assert!(
                variant
                    .unsupported_details
                    .iter()
                    .any(|detail| detail.contains(expected)),
                "{source:?}: {:?}",
                variant.unsupported_details
            );
        }

        for setting in ["true", "false"] {
            let case = Case::parse(
                "supported.ts",
                format!("// @useCaseSensitiveFileNames: {setting}\nconst value = 1;\n"),
            )
            .unwrap();
            assert!(
                expand_option_matrix(&case)[0]
                    .unsupported_details
                    .is_empty(),
                "setting: {setting}"
            );
        }
    }

    #[test]
    fn enumerates_missing_pinned_boolean_axes_as_unsupported() {
        for option in [
            "allowImportingTsExtensions",
            "deduplicatePackages",
            "noImplicitOverride",
            "noPropertyAccessFromIndexSignature",
            "noUncheckedIndexedAccess",
        ] {
            let case = Case::parse(
                format!("{option}.ts"),
                format!("// @{option}: true, false\nconst value = 1;\n"),
            )
            .unwrap();
            let variants = expand_option_matrix(&case);
            assert_eq!(variants.len(), 2, "{option}");
            assert_eq!(matrix_axes(&case), [option], "{option}");
            assert_eq!(variants[0].values[option], "true", "{option}");
            assert_eq!(variants[1].values[option], "false", "{option}");
            assert!(
                variants
                    .iter()
                    .all(|variant| !variant.unsupported_details.is_empty()),
                "{option}"
            );
        }
    }

    #[test]
    fn enforces_pinned_twenty_five_variant_cap_without_a_false_exact_matrix() {
        let case = Case::parse(
            "tooMany.ts",
            concat!(
                "// @target: es5, es6, es2016, es2017, es2018, es2019\n",
                "// @moduleDetection: *\n",
                "// @strict: *\n",
                "const value = 1;\n",
            ),
        )
        .unwrap();
        let variants = expand_option_matrix(&case);
        assert_eq!(variants.len(), 1);
        assert!(
            variants[0]
                .unsupported_details
                .iter()
                .any(|detail| detail.contains("variation cap exceeded"))
        );
    }

    #[test]
    fn orders_error_baseline_inputs_as_roots_then_other_files() {
        let case = Case::parse(
            "deduplicatePackages.ts",
            concat!(
                "// @noImplicitReferences: true\n",
                "// @deduplicatePackages: true,false\n",
                "\n",
                "// @filename: /node_modules/a/index.d.ts\n",
                "import X from \"x\";\n",
                "export function a(x: X): void;\n",
                "\n",
                "// @filename: /node_modules/a/node_modules/x/index.d.ts\n",
                "export default class X {\n",
                "    private x: number;\n",
                "}\n",
                "\n",
                "// @filename: /node_modules/a/node_modules/x/package.json\n",
                "{ \"name\": \"x\", \"version\": \"1.2.3\" }\n",
                "\n",
                "// @filename: /node_modules/b/index.d.ts\n",
                "import X from \"x\";\n",
                "export const b: X;\n",
                "\n",
                "// @filename: /node_modules/b/node_modules/x/index.d.ts\n",
                "content not parsed\n",
                "\n",
                "// @filename: /node_modules/b/node_modules/x/package.json\n",
                "{ \"name\": \"x\", \"version\": \"1.2.3\" }\n",
                "\n",
                "// @filename: /node_modules/c/index.d.ts\n",
                "import X from \"x\";\n",
                "export const c: X;\n",
                "\n",
                "// @filename: /node_modules/c/node_modules/x/index.d.ts\n",
                "export default class X {\n",
                "    private x: number;\n",
                "}\n",
                "\n",
                "// @filename: /node_modules/c/node_modules/x/package.json\n",
                "{ \"name\": \"x\", \"version\": \"1.2.4\" }\n",
                "\n",
                "// @filename: /src/a.ts\n",
                "import { a } from \"a\";\n",
                "import { b } from \"b\";\n",
                "import { c } from \"c\";\n",
                "a(b); // Works\n",
                "a(c); // Error, these are from different versions of the library.\n",
            ),
        )
        .unwrap();
        let (order, issues) = error_baseline_unit_order(&case);
        assert!(issues.is_empty());
        assert_eq!(
            order
                .iter()
                .map(|index| case.units[*index].path.to_string_lossy())
                .collect::<Vec<_>>(),
            [
                Path::new("/src/a.ts").to_string_lossy(),
                Path::new("/node_modules/a/index.d.ts").to_string_lossy(),
                Path::new("/node_modules/a/node_modules/x/index.d.ts").to_string_lossy(),
                Path::new("/node_modules/a/node_modules/x/package.json").to_string_lossy(),
                Path::new("/node_modules/b/index.d.ts").to_string_lossy(),
                Path::new("/node_modules/b/node_modules/x/index.d.ts").to_string_lossy(),
                Path::new("/node_modules/b/node_modules/x/package.json").to_string_lossy(),
                Path::new("/node_modules/c/index.d.ts").to_string_lossy(),
                Path::new("/node_modules/c/node_modules/x/index.d.ts").to_string_lossy(),
                Path::new("/node_modules/c/node_modules/x/package.json").to_string_lossy(),
            ]
        );

        let source = case.units[9].source_text.clone();
        let diagnostic = CompilationDiagnostic {
            file_name: Some("/src/a.ts".to_owned()),
            source_text: Some(source),
            range: Some(TextRange::new(TextPos::new(78), TextPos::new(79))),
            code: Some(2345),
            category: Some(CompilationDiagnosticCategory::Error),
            message: concat!(
                "Argument of type 'import(\"/node_modules/c/node_modules/x/index\").default' ",
                "is not assignable to parameter of type ",
                "'import(\"/node_modules/a/node_modules/x/index\").default'.\n",
                "  Types have separate declarations of a private property 'x'.",
            )
            .to_owned(),
            related_information: Some(Vec::new()),
        };
        let artifact = render_error_baseline(&case, &[diagnostic]);
        let root = artifact.text.find("==== /src/a.ts").unwrap();
        let dependency = artifact
            .text
            .find("==== /node_modules/a/index.d.ts")
            .unwrap();
        assert!(root < dependency, "{}", artifact.text);
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
    fn matches_duplicate_basenames_by_content_across_virtual_paths() {
        let outputs = BTreeMap::from([
            (
                "/case/src/compiler/_namespaces/ts.js".into(),
                "compiler namespace\n".into(),
            ),
            (
                "/case/src/core/_namespaces/ts.js".into(),
                "core namespace\n".into(),
            ),
        ]);
        let baseline = concat!(
            "//// [ts.js] ////\n",
            "core namespace\n",
            "//// [ts.js] ////\n",
            "compiler namespace\n",
        );
        assert!(compare_emitted_output_sections(&outputs, baseline).is_match());
    }

    #[test]
    fn duplicate_basename_content_mismatches_remain_actionable() {
        let outputs = BTreeMap::from([
            ("/case/a/ts.js".into(), "first\n".into()),
            ("/case/b/ts.js".into(), "changed\n".into()),
        ]);
        let baseline = concat!(
            "//// [ts.js] ////\n",
            "first\n",
            "//// [ts.js] ////\n",
            "second\n",
        );
        let comparison = compare_emitted_output_sections(&outputs, baseline);
        assert_eq!(comparison.differences.len(), 1);
        assert_eq!(comparison.differences[0].section, "ts.js");
        assert!(matches!(
            comparison.differences[0].kind,
            OutputDifferenceKind::Content { .. }
        ));
    }

    #[test]
    fn duplicate_basename_extras_and_missing_sections_are_not_hidden() {
        let extra_outputs = BTreeMap::from([
            ("/case/a/ts.js".into(), "first\n".into()),
            ("/case/b/ts.js".into(), "second\n".into()),
            ("/case/c/ts.js".into(), "third\n".into()),
        ]);
        let baseline = concat!(
            "//// [ts.js] ////\n",
            "first\n",
            "//// [ts.js] ////\n",
            "second\n",
        );
        let comparison = compare_emitted_output_sections(&extra_outputs, baseline);
        assert_eq!(comparison.differences.len(), 1);
        assert_eq!(comparison.differences[0].section, "c/ts.js");
        assert!(matches!(
            comparison.differences[0].kind,
            OutputDifferenceKind::Unexpected { .. }
        ));

        let missing_outputs = BTreeMap::from([("/case/a/ts.js".into(), "first\n".into())]);
        let comparison = compare_emitted_output_sections(&missing_outputs, baseline);
        assert_eq!(comparison.differences.len(), 1);
        assert_eq!(comparison.differences[0].section, "ts.js");
        assert!(matches!(
            comparison.differences[0].kind,
            OutputDifferenceKind::Missing { .. }
        ));
    }

    #[test]
    fn excludes_javascript_input_echo_before_comparing_emitted_output() {
        let case = Case::parse(
            "inputEcho.ts",
            concat!(
                "// @allowJs: true\n",
                "// @outDir: ./out\n",
                "// @filename: /a.js\n",
                "\nconst value = 1;\n",
            ),
        )
        .unwrap();
        let outputs = BTreeMap::from([(
            "/case/out/a.js".into(),
            "\"use strict\";\nconst value = 1;\n".into(),
        )]);
        let baseline = concat!(
            "//// [a.js] ////\n",
            "const value = 1;\n",
            "//// [a.js] ////\n",
            "\"use strict\";\nconst value = 1;\n",
        );
        assert!(
            compare_case_emitted_output_sections(
                &outputs,
                baseline,
                &case,
                &OptionVariant::default(),
            )
            .is_match()
        );
    }

    #[test]
    fn input_echo_exclusion_preserves_legitimate_duplicate_outputs() {
        let case = Case::parse(
            "inputEcho.ts",
            concat!(
                "// @allowJs: true\n",
                "// @outDir: ./out\n",
                "// @filename: /a.js\n",
                "\nconst source = true;\n",
            ),
        )
        .unwrap();
        let outputs = BTreeMap::from([
            ("/case/out/one/a.js".into(), "const output = 1;\n".into()),
            ("/case/out/two/a.js".into(), "const output = 2;\n".into()),
        ]);
        let baseline = concat!(
            "//// [a.js] ////\n",
            "const source = true;\n",
            "//// [a.js] ////\n",
            "const output = 2;\n",
            "//// [a.js] ////\n",
            "const output = 1;\n",
        );
        assert!(
            compare_case_emitted_output_sections(
                &outputs,
                baseline,
                &case,
                &OptionVariant::default(),
            )
            .is_match()
        );
    }

    #[test]
    fn excludes_duplicate_declaration_input_echoes_by_content() {
        let case = Case::parse(
            "declarationEcho.ts",
            concat!(
                "// @filename: /node_modules/one/index.d.ts\n",
                "export interface One {}\n",
                "// @filename: /node_modules/two/index.d.ts\n",
                "export interface Two {}\n",
                "// @filename: /index.ts\n",
                "export {};\n",
            ),
        )
        .unwrap();
        let outputs = BTreeMap::from([("/index.js".into(), "export {};\n".into())]);
        let baseline = concat!(
            "//// [index.d.ts] ////\n",
            "export interface One {}\n",
            "//// [index.d.ts] ////\n",
            "export interface Two {}\n",
            "//// [index.js] ////\n",
            "export {};\n",
        );
        assert!(
            compare_case_emitted_output_sections(
                &outputs,
                baseline,
                &case,
                &OptionVariant::default(),
            )
            .is_match()
        );
    }

    #[test]
    fn matches_allow_js_out_dir_outputs_across_module_variants() {
        let case = Case::parse(
            "ambientRequireFunction.ts",
            concat!(
                "// @target: es2015\n",
                "// @module: commonjs, preserve\n",
                "// @allowJs: true\n",
                "// @outDir: ./out/\n",
                "// @noLib: true\n",
                "// @filename: node.d.ts\n",
                "declare function require(moduleName: string): any;\n",
                "declare module \"fs\" {\n",
                "    export function readFileSync(s: string): string;\n",
                "}\n",
                "// @filename: app.js\n",
                "/// <reference path=\"node.d.ts\"/>\n",
                "const fs = require(\"fs\");\n",
                "const text = fs.readFileSync(\"/a/b/c\");\n",
            ),
        )
        .unwrap();
        let baseline = concat!(
            "//// [app.js] ////\n",
            "\"use strict\";\n",
            "/// <reference path=\"node.d.ts\"/>\n",
            "const fs = require(\"fs\");\n",
            "const text = fs.readFileSync(\"/a/b/c\");\n",
        );
        let runs = run_case_against_baseline(&case, baseline).unwrap();
        assert_eq!(runs.len(), 2);
        for run in runs {
            assert!(
                run.compilation.diagnostics.is_empty(),
                "{:?}: {:?}",
                run.variant,
                run.compilation.diagnostics
            );
            assert!(
                run.compilation.outputs.contains_key("/.src/out/app.js"),
                "{:?}: {:?}",
                run.variant,
                run.compilation.outputs.keys().collect::<Vec<_>>()
            );
            assert!(
                run.comparison.is_match(),
                "{:?}: {:?}",
                run.variant,
                run.comparison.differences
            );
        }
    }

    #[test]
    fn preserves_boolean_looking_out_dir_as_a_path() {
        let case = Case::parse(
            "output.ts",
            "// @allowJs: true\n// @outDir: true\n// @filename: input.js\nvalue;\n",
        )
        .unwrap();
        let variant = expand_option_matrix(&case).remove(0);
        let options = fixture_compiler_options(&case, &variant);
        assert_eq!(options.out_dir.as_deref(), Some("true"));
    }

    #[test]
    fn ignores_leading_separator_for_declaration_input_but_compares_generated_namesakes() {
        let case = Case::parse(
            "ambientRequireFunction.ts",
            concat!(
                "// @declaration: true\n",
                "// @filename: node.d.ts\n",
                "\n",
                "declare function require(name: string): any;\n",
                "// @filename: app.ts\n",
                "export const value = 1;\n",
            ),
        )
        .unwrap();
        let baseline = concat!(
            "//// [node.d.ts] ////\n",
            "declare function require(name: string): any;\n",
            "//// [app.d.ts] ////\n",
            "export declare const value = 1;\n",
        );
        let outputs = BTreeMap::from([(
            "/case/out/app.d.ts".into(),
            "export declare const value = 1;\n".into(),
        )]);
        assert!(
            compare_case_emitted_output_sections(
                &outputs,
                baseline,
                &case,
                &OptionVariant::default(),
            )
            .is_match()
        );

        let mut with_generated_namesake = outputs;
        with_generated_namesake.insert(
            "/case/out/nested/node.d.ts".into(),
            "declare const generated: true;\n".into(),
        );
        let comparison = compare_case_emitted_output_sections(
            &with_generated_namesake,
            baseline,
            &case,
            &OptionVariant::default(),
        );
        assert_eq!(comparison.differences.len(), 1);
        assert_eq!(comparison.differences[0].section, "out/nested/node.d.ts");
        assert!(matches!(
            comparison.differences[0].kind,
            OutputDifferenceKind::Unexpected { .. }
        ));
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
            ..OptionVariant::default()
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
    fn invalid_declaration_only_case_reports_5069_without_outputs() {
        let case = Case::parse(
            "declarationOnlyError.ts",
            "// @emitDeclarationOnly: true\nvar hello = 'yo!';\n",
        )
        .unwrap();
        let compilation = compile_case(&case).unwrap();
        assert!(compilation.outputs.is_empty(), "{:?}", compilation.outputs);
        assert_eq!(
            compilation
                .diagnostics
                .iter()
                .filter_map(|diagnostic| diagnostic.code)
                .collect::<Vec<_>>(),
            [5069]
        );
    }

    #[test]
    fn ignores_basename_markers_for_nested_declaration_inputs() {
        let case = Case::parse(
            "amdLike.ts",
            concat!(
                "// @emitDeclarationOnly: true\n",
                "// @filename: typing.d.ts\n",
                "declare function define(): void;\n",
                "// @filename: deps/BaseClass.d.ts\n",
                "declare class BaseClass {}\n",
                "// @filename: ExtendedClass.js\n",
                "define();\n",
            ),
        )
        .unwrap();
        let outputs = BTreeMap::from([(
            "/case/definitions/ExtendedClass.d.ts".into(),
            "export declare const value: number;\n".into(),
        )]);
        let baseline = concat!(
            "//// [typing.d.ts] ////\n",
            "declare function define(): void;\n",
            "//// [BaseClass.d.ts] ////\n",
            "declare class BaseClass {}\n",
            "//// [ExtendedClass.js] ////\n",
            "define();\n",
            "//// [ExtendedClass.d.ts] ////\n",
            "export declare const value: number;\n",
        );
        let variant = OptionVariant {
            values: BTreeMap::from([("emitDeclarationOnly".into(), "true".into())]),
            ..OptionVariant::default()
        };
        assert!(
            compare_case_emitted_output_sections(&outputs, baseline, &case, &variant).is_match()
        );
    }

    #[test]
    fn still_compares_genuinely_emitted_declaration_sections() {
        let case = Case::parse(
            "declarations.ts",
            concat!(
                "// @filename: support/ambient.d.ts\n",
                "declare const ambient: string;\n",
                "// @filename: main.ts\n",
                "export const value = 1;\n",
            ),
        )
        .unwrap();
        let outputs = BTreeMap::from([(
            "/case/types/main.d.ts".into(),
            "export declare const value = 2;\n".into(),
        )]);
        let baseline = concat!(
            "//// [ambient.d.ts] ////\n",
            "declare const ambient: string;\n",
            "//// [main.d.ts] ////\n",
            "export declare const value = 1;\n",
        );
        let comparison = compare_case_emitted_output_sections(
            &outputs,
            baseline,
            &case,
            &OptionVariant::default(),
        );
        assert_eq!(comparison.differences.len(), 1);
        assert_eq!(comparison.differences[0].section, "main.d.ts");
        assert!(matches!(
            comparison.differences[0].kind,
            OutputDifferenceKind::Content { .. }
        ));
    }

    #[test]
    fn compares_source_named_declaration_sections_when_baseline_is_emitted_output() {
        let case = Case::parse(
            "input.ts",
            "// @filename: deps/BaseClass.d.ts\ndeclare class BaseClass {}\n",
        )
        .unwrap();
        let outputs = BTreeMap::from([(
            "/case/types/BaseClass.d.ts".into(),
            "declare class Different {}\n".into(),
        )]);
        let baseline = "//// [BaseClass.d.ts] ////\ndeclare class Generated {}\n";
        let comparison = compare_case_emitted_output_sections(
            &outputs,
            baseline,
            &case,
            &OptionVariant::default(),
        );
        assert_eq!(comparison.differences.len(), 1);
        assert!(matches!(
            comparison.differences[0].kind,
            OutputDifferenceKind::Content { .. }
        ));
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
