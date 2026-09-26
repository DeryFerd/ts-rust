//! Owned reports from one on-disk canonical project and forced source replay.

mod errors;
mod graph;
mod options;
mod provenance;

use std::{
    io::{self, BufRead, Write},
    path::Path,
    time::{Duration, Instant},
};

use serde::{Deserialize, Serialize};
use ts_ast::NodeRef;
use ts_compiler::{
    CanonicalCensusAttempt, CanonicalCensusCompletion, CanonicalCensusControl,
    CanonicalCensusDiagnosticScope, CanonicalCensusDiagnostics, CanonicalCensusEvent,
    CanonicalCensusLoadDisposition, CanonicalCensusOutcome, CanonicalCensusPhase,
    CanonicalCensusSkipReason, CanonicalProgramCheckError, CanonicalProgramCheckFailureClass,
    CanonicalProgramQueries, Program, ProgramDiagnostic,
};
use ts_vfs::OsFileSystem;

use crate::{
    CompilationDiagnosticCategory, SCORECARD_DIGEST_ALGORITHM,
    artifacts::{
        ArtifactRenderError,
        project::{
            ProjectArtifactRun, ProjectSemanticArtifacts, ordered_project_sources, render_project,
        },
    },
    compilation_diagnostic_category, stable_digest,
};

pub use graph::ProjectGraphReport;
pub use provenance::{ProjectFileDigest, ProjectRunProvenance};

/// A completed stage does not claim equality with another compiler.
#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
#[serde(tag = "status", rename_all = "snake_case")]
pub enum ProjectStage<T> {
    Complete { value: T },
    NoContent { detail: String },
    Unsupported { code: String, detail: String },
    Invariant { code: String, detail: String },
    Unavailable { detail: String },
}

impl<T> ProjectStage<T> {
    fn unavailable(detail: impl Into<String>) -> Self {
        Self::Unavailable {
            detail: detail.into(),
        }
    }

    fn failure(class: CanonicalProgramCheckFailureClass, detail: String) -> Self {
        match class {
            CanonicalProgramCheckFailureClass::Unsupported { capability_code } => {
                Self::Unsupported {
                    code: capability_code.to_owned(),
                    detail,
                }
            }
            CanonicalProgramCheckFailureClass::Fatal { invariant_code } => Self::Invariant {
                code: invariant_code.to_owned(),
                detail,
            },
        }
    }

    fn compiler_failure(error: &CanonicalProgramCheckError) -> Self {
        Self::failure(error.failure_class(), error.to_string())
    }

    fn is_invariant(&self) -> bool {
        matches!(self, Self::Invariant { .. })
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct ProjectTextArtifact {
    pub text: String,
    pub byte_count: usize,
    pub digest: String,
    pub digest_algorithm: &'static str,
}

impl ProjectTextArtifact {
    fn new(text: String) -> Self {
        Self {
            byte_count: text.len(),
            digest: stable_digest(text.as_bytes()),
            digest_algorithm: SCORECARD_DIGEST_ALGORITHM,
            text,
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct ProjectArtifactReport {
    pub output: ProjectStage<ProjectTextArtifact>,
    pub visited_nodes: Option<usize>,
    pub completed_nodes: usize,
    pub rendered_nodes: usize,
    /// Hashes path, kind, and byte range. It does not hash process-local IDs.
    pub walk_digest: Option<String>,
}

impl ProjectArtifactReport {
    fn unavailable(detail: &str) -> Self {
        Self {
            output: ProjectStage::unavailable(detail),
            visited_nodes: None,
            completed_nodes: 0,
            rendered_nodes: 0,
            walk_digest: None,
        }
    }

    fn from_run(program: &Program, run: &ProjectArtifactRun, walk: &[NodeRef]) -> Self {
        let output = match &run.text {
            Ok(text) => ProjectStage::Complete {
                value: ProjectTextArtifact::new(text.clone()),
            },
            Err(ArtifactRenderError { class, detail }) => {
                ProjectStage::failure(*class, detail.clone())
            }
        };
        let visited = walk
            .iter()
            .map(|reference| {
                let source = program
                    .source_file_by_id(reference.file)
                    .expect("the artifact walk validated the source");
                let node = program
                    .node(*reference)
                    .expect("the artifact walk validated the node");
                (
                    graph::path_identity(&source.file_name),
                    format!("{:?}", node.kind),
                    node.range.start.get(),
                    node.range.end.get(),
                )
            })
            .collect::<Vec<_>>();
        let bytes = serde_json::to_vec(&visited).expect("node visits contain only JSON values");
        Self {
            output,
            visited_nodes: Some(run.visited_nodes),
            completed_nodes: run.identities.len(),
            rendered_nodes: run.rendered_nodes,
            walk_digest: Some(stable_digest(&bytes)),
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct ProjectDiagnosticRange {
    pub start_byte: u32,
    pub end_byte: u32,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct ProjectDiagnosticRecord {
    pub file_name: Option<String>,
    pub range: Option<ProjectDiagnosticRange>,
    pub code: Option<u32>,
    pub category: CompilationDiagnosticCategory,
    pub message: String,
    pub related_information: Vec<Self>,
}

impl From<&ProgramDiagnostic> for ProjectDiagnosticRecord {
    fn from(diagnostic: &ProgramDiagnostic) -> Self {
        Self {
            file_name: diagnostic.file_name.as_deref().map(graph::path_identity),
            range: diagnostic.range.map(|range| ProjectDiagnosticRange {
                start_byte: range.start.get(),
                end_byte: range.end.get(),
            }),
            code: diagnostic.code,
            category: compilation_diagnostic_category(diagnostic.category),
            message: diagnostic.message.clone(),
            related_information: diagnostic
                .related_information
                .iter()
                .map(Self::from)
                .collect(),
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct ProjectDiagnosticArtifact {
    pub diagnostic_policy: &'static str,
    pub records: Vec<ProjectDiagnosticRecord>,
    pub json_digest: String,
    pub digest_algorithm: &'static str,
    pub errors_file_order: Vec<String>,
    pub pinned_error_baseline: ProjectStage<ProjectTextArtifact>,
}

impl ProjectDiagnosticArtifact {
    fn new(program: &Program, diagnostics: &[ProgramDiagnostic]) -> Self {
        let records = diagnostics
            .iter()
            .map(ProjectDiagnosticRecord::from)
            .collect::<Vec<_>>();
        let bytes =
            serde_json::to_vec(&records).expect("diagnostic records contain only JSON values");
        let rendered = errors::render(program, diagnostics);
        Self {
            diagnostic_policy: "Complete canonical Program snapshot. The runner does not invoke a separate declaration-diagnostic or emit stage.",
            records,
            json_digest: stable_digest(&bytes),
            digest_algorithm: SCORECARD_DIGEST_ALGORITHM,
            errors_file_order: rendered.file_order,
            pinned_error_baseline: rendered.output,
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct ProjectCheckReport {
    pub diagnostics: ProjectStage<ProjectDiagnosticArtifact>,
    pub types: ProjectArtifactReport,
    pub symbols: ProjectArtifactReport,
}

impl ProjectCheckReport {
    fn unavailable(detail: &str) -> Self {
        Self {
            diagnostics: ProjectStage::unavailable(detail),
            types: ProjectArtifactReport::unavailable(detail),
            symbols: ProjectArtifactReport::unavailable(detail),
        }
    }

    fn from_artifacts(
        program: &Program,
        diagnostics: &[ProgramDiagnostic],
        artifacts: &Result<ProjectSemanticArtifacts, String>,
    ) -> Self {
        let mut report = Self::unavailable("The artifact walk did not complete.");
        report.diagnostics = ProjectStage::Complete {
            value: ProjectDiagnosticArtifact::new(program, diagnostics),
        };
        match artifacts {
            Ok(artifacts) => {
                report.types = ProjectArtifactReport::from_run(
                    program,
                    &artifacts.types,
                    &artifacts.walk.types,
                );
                report.symbols = ProjectArtifactReport::from_run(
                    program,
                    &artifacts.symbols,
                    &artifacts.walk.symbols,
                );
            }
            Err(detail) => {
                let failure = ProjectStage::Invariant {
                    code: "INV.ARTIFACT.INPUT".to_owned(),
                    detail: detail.clone(),
                };
                report.types.output = failure.clone();
                report.symbols.output = failure;
            }
        }
        report
    }

    fn has_invariant(&self) -> bool {
        self.diagnostics.is_invariant()
            || matches!(&self.diagnostics, ProjectStage::Complete { value } if value.pinned_error_baseline.is_invariant())
            || self.types.output.is_invariant()
            || self.symbols.output.is_invariant()
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct ProjectReplayEquality {
    pub diagnostic_records: bool,
    pub fresh_diagnostics: ProjectStage<()>,
    pub error_bytes: Option<bool>,
    pub errors_file_order: Option<bool>,
    pub type_bytes: Option<bool>,
    pub symbol_bytes: Option<bool>,
    pub type_walk: Option<bool>,
    pub symbol_walk: Option<bool>,
    pub type_identities: Option<bool>,
    pub symbol_identities: Option<bool>,
    pub checker_store_identity: bool,
}

impl ProjectReplayEquality {
    fn has_mismatch(&self) -> bool {
        !self.diagnostic_records
            || !self.checker_store_identity
            || [
                self.error_bytes,
                self.errors_file_order,
                self.type_bytes,
                self.symbol_bytes,
                self.type_walk,
                self.symbol_walk,
                self.type_identities,
                self.symbol_identities,
            ]
            .contains(&Some(false))
    }
}

#[derive(Clone, Debug, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct ProjectReport {
    pub schema_version: u32,
    pub implementation: &'static str,
    pub run_id: String,
    pub config_path: String,
    pub header: String,
    pub construction: ProjectStage<()>,
    pub graph: ProjectStage<ProjectGraphReport>,
    pub cold: ProjectCheckReport,
    pub replay: ProjectStage<ProjectCheckReport>,
    pub replay_equality: ProjectStage<ProjectReplayEquality>,
    pub cross_implementation_comparison: ProjectStage<()>,
    pub provenance: ProjectRunProvenance,
}

impl ProjectReport {
    /// Invariant failures and observed replay mismatches need a failing process exit.
    #[must_use]
    pub fn has_invariant_failure(&self) -> bool {
        self.construction.is_invariant()
            || self.graph.is_invariant()
            || matches!(&self.graph, ProjectStage::Complete { value } if value.module_resolution_manifest.is_invariant())
            || self.cold.has_invariant()
            || self.replay.is_invariant()
            || matches!(&self.replay, ProjectStage::Complete { value } if value.has_invariant())
            || matches!(&self.replay_equality, ProjectStage::Complete { value } if value.has_mismatch())
    }
}

struct QueryReport {
    graph: graph::ProjectGraphReport,
    cold: ProjectCheckReport,
    replay: ProjectStage<ProjectCheckReport>,
    equality: ProjectStage<ProjectReplayEquality>,
}

/// Loads a real tsconfig without option overrides, then forces source replay.
///
/// # Errors
/// Returns an I/O error for a relative or non-UTF-8 config path. Compiler errors
/// remain in the report, with unavailable stages kept separate from empty output.
pub fn run_project(
    config_path: &Path,
    header: Option<&str>,
    run_id: &str,
) -> io::Result<ProjectReport> {
    if !config_path.is_absolute() {
        return Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            "the project config path must be absolute",
        ));
    }
    let config_path = config_path.to_str().ok_or_else(|| {
        io::Error::new(
            io::ErrorKind::InvalidInput,
            "the project config path must be UTF-8",
        )
    })?;
    let config_path = ts_path::normalize_path(config_path);
    let header = header.unwrap_or(&config_path).to_owned();
    let started = Instant::now();
    let provenance = ProjectRunProvenance::start(Path::new(&config_path));
    let mut report = ProjectReport {
        schema_version: 1,
        implementation: "rust-canonical",
        run_id: run_id.to_owned(),
        config_path: config_path.clone(),
        header: header.clone(),
        construction: ProjectStage::unavailable("Program construction has not completed."),
        graph: ProjectStage::unavailable("No Program graph was returned."),
        cold: ProjectCheckReport::unavailable("The canonical checker callback did not run."),
        replay: ProjectStage::unavailable("The canonical checker callback did not run."),
        replay_equality: ProjectStage::unavailable("Forced source replay did not complete."),
        cross_implementation_comparison: ProjectStage::unavailable(
            "This report contains one Rust process. A pinned Go report and full graph agreement are required for a cross-implementation comparison.",
        ),
        provenance,
    };
    let result = Program::try_from_config_with_canonical_checker_and_queries(
        &OsFileSystem::default(),
        &config_path,
        |program, queries| capture_queries(program, queries, &header),
    );
    match result {
        Err(error) => report.construction = ProjectStage::compiler_failure(&error),
        Ok((program, Some(queries))) => {
            report.construction = ProjectStage::Complete { value: () };
            report.graph = ProjectStage::Complete {
                value: queries.graph,
            };
            report.cold = queries.cold;
            report.replay = queries.replay;
            report.replay_equality = queries.equality;
            let expected = ProjectDiagnosticArtifact::new(&program, program.diagnostics());
            if !matches!(&report.cold.diagnostics, ProjectStage::Complete { value } if value == &expected)
            {
                report.cold.diagnostics = ProjectStage::Invariant {
                    code: "INV.PROJECT.COLD_DIAGNOSTICS".to_owned(),
                    detail:
                        "The cold query snapshot differs from the returned Program diagnostics."
                            .to_owned(),
                };
            }
        }
        Ok((program, None)) => {
            let detail = if program.options().no_check {
                "The project sets noCheck, so canonical checking and replay did not run."
            } else {
                "Config loading returned no canonical checker callback."
            };
            report.construction = ProjectStage::unavailable(detail);
            report.graph = ProjectStage::Complete {
                value: graph::snapshot_report(&program),
            };
            report.cold.diagnostics = ProjectStage::Complete {
                value: ProjectDiagnosticArtifact::new(&program, program.diagnostics()),
            };
            report.cold.types = ProjectArtifactReport::unavailable(detail);
            report.cold.symbols = ProjectArtifactReport::unavailable(detail);
            report.replay = ProjectStage::unavailable(detail);
        }
    }
    report.provenance.finish(started.elapsed());
    Ok(report)
}

fn capture_queries(
    program: &Program,
    queries: &mut CanonicalProgramQueries<'_>,
    header: &str,
) -> QueryReport {
    let graph = graph::snapshot_report(program);
    let sources = ordered_project_sources(program, program.ordered_root_file_names());
    let store = queries.semantic_store_id();
    let cold_diagnostics = queries.cold_diagnostic_snapshot();
    let cold_artifacts = render_project(
        program,
        queries,
        &sources,
        header,
        !cold_diagnostics.is_empty(),
    )
    .map_err(|error| error.to_string());
    let cold = ProjectCheckReport::from_artifacts(program, &cold_diagnostics, &cold_artifacts);
    if cold.has_invariant() {
        return QueryReport {
            graph,
            cold,
            replay: ProjectStage::unavailable(
                "A cold artifact invariant failed. Replay was not attempted.",
            ),
            equality: ProjectStage::unavailable(
                "Forced source replay did not run after the invariant failure.",
            ),
        };
    }
    let warm_diagnostics = match queries.replay_sources() {
        Ok(diagnostics) => diagnostics,
        Err(error) => {
            return QueryReport {
                graph,
                cold,
                replay: ProjectStage::compiler_failure(&error),
                equality: ProjectStage::unavailable(
                    "Forced source replay failed. No warm artifact comparison was made.",
                ),
            };
        }
    };
    let warm_artifacts = render_project(
        program,
        queries,
        &sources,
        header,
        !warm_diagnostics.is_empty(),
    )
    .map_err(|error| error.to_string());
    let warm = ProjectCheckReport::from_artifacts(program, &warm_diagnostics, &warm_artifacts);
    let mut equality = ProjectReplayEquality {
        diagnostic_records: cold_diagnostics == warm_diagnostics,
        fresh_diagnostics: ProjectStage::unavailable(
            "Snapshot and error-text equality do not prove that every diagnostic was produced again.",
        ),
        error_bytes: None,
        errors_file_order: None,
        type_bytes: None,
        symbol_bytes: None,
        type_walk: None,
        symbol_walk: None,
        type_identities: None,
        symbol_identities: None,
        checker_store_identity: store == queries.semantic_store_id(),
    };
    if let (ProjectStage::Complete { value: cold }, ProjectStage::Complete { value: warm }) =
        (&cold.diagnostics, &warm.diagnostics)
    {
        equality.error_bytes = match (&cold.pinned_error_baseline, &warm.pinned_error_baseline) {
            (ProjectStage::Complete { value: cold }, ProjectStage::Complete { value: warm }) => {
                Some(cold.text.as_bytes() == warm.text.as_bytes())
            }
            (ProjectStage::NoContent { .. }, ProjectStage::NoContent { .. }) => Some(true),
            (ProjectStage::NoContent { .. }, ProjectStage::Complete { .. })
            | (ProjectStage::Complete { .. }, ProjectStage::NoContent { .. }) => Some(false),
            _ => None,
        };
        if equality.error_bytes.is_some() {
            equality.errors_file_order = Some(cold.errors_file_order == warm.errors_file_order);
        }
    }
    if let (Ok(cold), Ok(warm)) = (&cold_artifacts, &warm_artifacts) {
        equality.type_walk = Some(cold.walk.types == warm.walk.types);
        equality.symbol_walk = Some(cold.walk.symbols == warm.walk.symbols);
        if let (Ok(cold_text), Ok(warm_text)) = (&cold.types.text, &warm.types.text) {
            equality.type_bytes = Some(cold_text.as_bytes() == warm_text.as_bytes());
            equality.type_identities = Some(cold.types.identities == warm.types.identities);
        }
        if let (Ok(cold_text), Ok(warm_text)) = (&cold.symbols.text, &warm.symbols.text) {
            equality.symbol_bytes = Some(cold_text.as_bytes() == warm_text.as_bytes());
            equality.symbol_identities = Some(cold.symbols.identities == warm.symbols.identities);
        }
    }
    QueryReport {
        graph,
        cold,
        replay: ProjectStage::Complete { value: warm },
        equality: ProjectStage::Complete { value: equality },
    }
}

/// One original requested root. Repeated and unloaded roots keep their own index.
#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ProjectCensusRoot {
    pub root_index: usize,
    pub requested_name: String,
    pub file_name: String,
    pub file_id: Option<usize>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum ProjectCensusAttempt {
    Ordinary,
    Root { root_index: usize },
}

impl From<CanonicalCensusAttempt> for ProjectCensusAttempt {
    fn from(attempt: CanonicalCensusAttempt) -> Self {
        match attempt {
            CanonicalCensusAttempt::Ordinary => Self::Ordinary,
            CanonicalCensusAttempt::Root(root_index) => Self::Root { root_index },
        }
    }
}

/// A location validated against the loaded Program, never a failed checker store.
#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ProjectCensusLocation {
    pub file_name: String,
    pub file_id: usize,
    pub syntax_kind: String,
    pub start_byte: u32,
    pub end_byte: u32,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ProjectCensusFailure {
    pub phase: String,
    pub class: String,
    pub code: String,
    pub detail: String,
    pub returned_error: String,
    /// The compiler envelope's file, which can differ from a nested node's file.
    pub reported_file_name: Option<String>,
    pub location: Option<ProjectCensusLocation>,
    pub location_unavailable: Option<String>,
}

impl ProjectCensusFailure {
    /// Preserves the returned error and validates only its typed node evidence.
    #[must_use]
    pub fn from_error(
        program: Option<&Program>,
        phase: CanonicalCensusPhase,
        error: &CanonicalProgramCheckError,
    ) -> Self {
        let node = census_error_node(error);
        let location = program.zip(node).and_then(|(program, reference)| {
            let node = program.node(reference)?;
            let source = program.source_file_by_id(reference.file)?;
            let start = usize::try_from(node.range.start.get()).ok()?;
            let end = usize::try_from(node.range.end.get()).ok()?;
            let text = source.source_text.as_str();
            if start > end || text.get(start..end).is_none() {
                return None;
            }
            Some(ProjectCensusLocation {
                file_name: graph::path_identity(&source.file_name),
                file_id: reference.file.index(),
                syntax_kind: format!("{:?}", node.kind),
                start_byte: node.range.start.get(),
                end_byte: node.range.end.get(),
            })
        });
        let location_unavailable = location.is_none().then(|| {
            if program.is_none() {
                "No loaded Program is available to validate a location."
            } else if node.is_none() {
                "This returned error has no supported typed node location."
            } else {
                "The returned node does not have a valid retained Program range."
            }
            .to_owned()
        });
        Self {
            phase: census_phase(phase).to_owned(),
            class: if error.failure_class().is_unsupported() {
                "unsupported"
            } else {
                "invariant"
            }
            .to_owned(),
            code: error.failure_class().code().to_owned(),
            detail: error.to_string(),
            returned_error: format!("{error:?}"),
            reported_file_name: census_error_file_name(error).map(graph::path_identity),
            location,
            location_unavailable,
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
#[serde(tag = "status", rename_all = "snake_case")]
pub enum ProjectCensusOutcome {
    SourceCheckComplete,
    OrdinaryCheckComplete,
    Unsupported { failure: ProjectCensusFailure },
    Invariant { failure: ProjectCensusFailure },
    SkippedByOriginalPolicy { reason: String },
    Unattempted { reason: String },
}

const CENSUS_PROGRAM_DIAGNOSTIC_POLICY: &str = "Final Program diagnostics in normal output order. Successful checking does not imply an empty diagnostic set.";
const CENSUS_RAW_CONTEXT_DIAGNOSTIC_POLICY: &str = "Raw full-graph binding and global diagnostics, followed by this context's checker records in issuance order. These records precede comment-directive filtering and are not final TypeScript errors. Cold roots do not run post-source checks. If post-source collection failed, this snapshot omits the collector's local compiler-generated diagnostic prefix.";
const CENSUS_PARTIAL_PROGRAM_DIAGNOSTIC_POLICY: &str = "The final Program diagnostic snapshot was collected, but the ordinary post-source attempt failed afterward.";
const CENSUS_UNLOADED_ROOT_REASON: &str =
    "The requested root was not loaded in the original Program.";

#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum ProjectCensusDiagnosticScope {
    Program,
    RawContext,
}

/// A reporting conversion failure, separate from the original checker failure.
#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ProjectCensusDiagnosticConversionError {
    pub class: String,
    pub code: String,
    pub detail: String,
    pub returned_error: String,
}

impl From<&CanonicalProgramCheckError> for ProjectCensusDiagnosticConversionError {
    fn from(error: &CanonicalProgramCheckError) -> Self {
        Self {
            class: if error.is_unsupported_boundary() {
                "unsupported"
            } else {
                "invariant"
            }
            .to_owned(),
            code: error.failure_class().code().to_owned(),
            detail: error.to_string(),
            returned_error: format!("{error:?}"),
        }
    }
}

/// Completeness applies to this payload, not to a project pass.
/// Raw context records have not passed through Program comment directives.
#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
#[serde(
    tag = "status",
    rename_all = "snake_case",
    rename_all_fields = "camelCase"
)]
pub enum ProjectCensusDiagnostics {
    CompleteProgram {
        records: Vec<serde_json::Value>,
        policy: String,
    },
    CompleteSourceContext {
        records: Vec<serde_json::Value>,
        policy: String,
    },
    Partial {
        scope: ProjectCensusDiagnosticScope,
        records: Vec<serde_json::Value>,
        policy: String,
        conversion_error: Option<ProjectCensusDiagnosticConversionError>,
    },
    UnavailableBeforeContext,
    Skipped {
        reason: String,
    },
    Unattempted {
        reason: String,
    },
    NotRecorded,
}

fn census_diagnostics(
    diagnostics: CanonicalCensusDiagnostics,
) -> io::Result<ProjectCensusDiagnostics> {
    let records = |diagnostics: Vec<ProgramDiagnostic>| {
        diagnostics
            .into_iter()
            .map(|diagnostic| {
                serde_json::to_value(ProjectDiagnosticRecord::from(&diagnostic))
                    .map_err(io::Error::other)
            })
            .collect::<io::Result<Vec<_>>>()
    };
    Ok(match diagnostics {
        CanonicalCensusDiagnostics::CompleteProgram { records: values } => {
            ProjectCensusDiagnostics::CompleteProgram {
                records: records(values)?,
                policy: CENSUS_PROGRAM_DIAGNOSTIC_POLICY.to_owned(),
            }
        }
        CanonicalCensusDiagnostics::CompleteSourceContext { records: values } => {
            ProjectCensusDiagnostics::CompleteSourceContext {
                records: records(values)?,
                policy: CENSUS_RAW_CONTEXT_DIAGNOSTIC_POLICY.to_owned(),
            }
        }
        CanonicalCensusDiagnostics::Partial {
            scope,
            records: values,
            conversion_error,
        } => {
            let (scope, policy) = match scope {
                CanonicalCensusDiagnosticScope::Program => (
                    ProjectCensusDiagnosticScope::Program,
                    CENSUS_PARTIAL_PROGRAM_DIAGNOSTIC_POLICY,
                ),
                CanonicalCensusDiagnosticScope::RawContext => (
                    ProjectCensusDiagnosticScope::RawContext,
                    CENSUS_RAW_CONTEXT_DIAGNOSTIC_POLICY,
                ),
            };
            ProjectCensusDiagnostics::Partial {
                scope,
                records: records(values)?,
                policy: policy.to_owned(),
                conversion_error: conversion_error.as_ref().map(Into::into),
            }
        }
        CanonicalCensusDiagnostics::UnavailableBeforeContext => {
            ProjectCensusDiagnostics::UnavailableBeforeContext
        }
        CanonicalCensusDiagnostics::Skipped(reason) => ProjectCensusDiagnostics::Skipped {
            reason: census_skip_reason(reason).to_owned(),
        },
        CanonicalCensusDiagnostics::Unattempted => ProjectCensusDiagnostics::Unattempted {
            reason: CENSUS_UNLOADED_ROOT_REASON.to_owned(),
        },
    })
}

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
#[serde(
    tag = "event",
    rename_all = "snake_case",
    rename_all_fields = "camelCase"
)]
pub enum ProjectCensusEvent {
    RunStarted {
        config_path: String,
        header: String,
        provenance: serde_json::Value,
        soft_deadline_ms: Option<u64>,
        unavailable: Vec<String>,
    },
    LoadStarted,
    Loaded {
        disposition: String,
        roots: Option<Vec<ProjectCensusRoot>>,
        graph: serde_json::Value,
        load_diagnostics: Vec<serde_json::Value>,
        load_elapsed_ms: u64,
        graph_serialization_elapsed_ms: u64,
    },
    LoadFailed {
        failure: ProjectCensusFailure,
        load_elapsed_ms: u64,
    },
    AttemptStarted {
        attempt: ProjectCensusAttempt,
    },
    PhaseStarted {
        attempt: ProjectCensusAttempt,
        phase: String,
    },
    PhaseFinished {
        attempt: ProjectCensusAttempt,
        phase: String,
        phase_elapsed_ms: u64,
    },
    AttemptFinished {
        attempt: ProjectCensusAttempt,
        outcome: ProjectCensusOutcome,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        diagnostics: Option<ProjectCensusDiagnostics>,
        attempt_elapsed_ms: u64,
    },
    Finished {
        completion: String,
        stop_reason: Option<String>,
        provenance: serde_json::Value,
    },
}

/// JSON-line envelope. Source identity is in the run record and graph identity
/// accompanies every record after the full loaded graph is serialized.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ProjectCensusRecord {
    pub schema_version: u32,
    pub report_kind: String,
    pub run_id: String,
    pub sequence: usize,
    pub elapsed_ms: u64,
    pub input_identity: Option<String>,
    #[serde(flatten)]
    pub event: ProjectCensusEvent,
}

#[derive(Clone, Debug, Default)]
pub struct ProjectCensusOptions {
    pub soft_deadline: Option<Duration>,
    pub supplied_build_record: Option<serde_json::Value>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ProjectCensusRunStatus {
    pub completion: String,
    pub has_invariant_failure: bool,
    /// Total time through the final output flush, including context drops.
    pub elapsed_ms: u64,
}

fn write_census_record<W: Write + ?Sized>(
    writer: &mut W,
    record: &ProjectCensusRecord,
) -> io::Result<()> {
    serde_json::to_writer(&mut *writer, record).map_err(io::Error::other)?;
    writeln!(writer)?;
    writer.flush()
}

fn census_millis(duration: Duration) -> io::Result<u64> {
    u64::try_from(duration.as_millis()).map_err(|_| {
        io::Error::new(
            io::ErrorKind::InvalidData,
            "census milliseconds exceed the JSON record range",
        )
    })
}

fn census_input_identity(
    graph: &serde_json::Value,
    roots: Option<&[ProjectCensusRoot]>,
) -> io::Result<String> {
    if let Some(roots) = roots {
        validate_census_roster(graph, roots)?;
    }
    Ok(stable_digest(
        &serde_json::to_vec(&(graph, roots)).map_err(io::Error::other)?,
    ))
}

fn validate_census_roster(
    graph: &serde_json::Value,
    roots: &[ProjectCensusRoot],
) -> io::Result<()> {
    let evidence = &graph["evidence"];
    let graph_roots = evidence["roots"]
        .as_array()
        .ok_or_else(|| invalid_census("The graph root roster is unavailable."))?;
    let sources = evidence["sources"]
        .as_array()
        .ok_or_else(|| invalid_census("The graph source load order is unavailable."))?;
    let case_sensitivity = match evidence["caseSensitive"].as_bool() {
        Some(true) => ts_path::CaseSensitivity::Sensitive,
        Some(false) => ts_path::CaseSensitivity::Insensitive,
        None => return Err(invalid_census("The graph path case rule is unavailable.")),
    };
    let canonical_path =
        |path: &str| ts_path::canonical_file_name(&ts_path::normalize_path(path), case_sensitivity);
    if roots.len() != graph_roots.len() {
        return Err(invalid_census("The census and graph root counts differ."));
    }
    for (index, (root, graph_root)) in roots.iter().zip(graph_roots).enumerate() {
        if root.root_index != index
            || graph_root["requestedName"].as_str() != Some(root.requested_name.as_str())
            || graph_root["fileName"].as_str() != Some(root.file_name.as_str())
            || graph_root["loaded"].as_bool() != Some(root.file_id.is_some())
        {
            return Err(invalid_census(
                "The census root differs from its graph entry.",
            ));
        }
        if let Some(file_id) = root.file_id {
            let source_path = sources
                .get(file_id)
                .and_then(|source| source["fileName"].as_str())
                .ok_or_else(|| invalid_census("The census file ID has no graph source entry."))?;
            if canonical_path(source_path) != canonical_path(&root.file_name) {
                return Err(invalid_census(
                    "The census file ID names a different graph source.",
                ));
            }
        }
    }
    Ok(())
}

/// Streams a diagnostic census without exposing a checked Program or checker.
/// The caller must open its new output before invoking this function.
///
/// # Errors
/// Rejects invalid request paths and stops immediately on any output error.
#[allow(clippy::too_many_lines)] // Keep the streaming event translation and stop rule together.
pub fn run_project_census<W: Write + ?Sized>(
    config_path: &Path,
    header: Option<&str>,
    run_id: &str,
    options: &ProjectCensusOptions,
    writer: &mut W,
) -> io::Result<ProjectCensusRunStatus> {
    let config_path = config_path
        .to_str()
        .filter(|_| config_path.is_absolute())
        .ok_or_else(|| {
            io::Error::new(
                io::ErrorKind::InvalidInput,
                "the project config path must be absolute UTF-8",
            )
        })?;
    if run_id.trim().is_empty() {
        return Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            "the census run ID must not be empty",
        ));
    }
    let config_path = ts_path::normalize_path(config_path);
    let started = Instant::now();
    let mut provenance = ProjectRunProvenance::start(Path::new(&config_path));
    provenance.supplied_build_record = options.supplied_build_record.clone();
    let mut sequence = 0;
    let mut input_identity = None;
    let mut has_invariant_failure = false;
    let mut emit = |event, identity: &Option<String>| {
        let record = ProjectCensusRecord {
            schema_version: 1,
            report_kind: "cold_root_failure_census".to_owned(),
            run_id: run_id.to_owned(),
            sequence,
            elapsed_ms: census_millis(started.elapsed())?,
            input_identity: identity.clone(),
            event,
        };
        write_census_record(writer, &record)?;
        sequence += 1;
        Ok::<_, io::Error>(())
    };
    emit(ProjectCensusEvent::RunStarted {
        config_path: config_path.clone(),
        header: header.unwrap_or(&config_path).to_owned(),
        provenance: serde_json::to_value(&provenance).map_err(io::Error::other)?,
        soft_deadline_ms: options.soft_deadline.map(census_millis).transpose()?,
        unavailable: vec![
            "Cold-root complete diagnostics and post-source queries are unavailable. Recorded cold-root diagnostics contain only raw context records before comment directives.".to_owned(),
            "Type/symbol artifacts, replay and cross-implementation comparison are unavailable.".to_owned(),
            "Source-check completion is not a diagnostic-free root or a project pass.".to_owned(),
        ],
    }, &input_identity)?;
    let completion = Program::run_canonical_root_census(
        &OsFileSystem::default(),
        &config_path,
        |program, event| -> io::Result<CanonicalCensusControl> {
            let event = match event {
                CanonicalCensusEvent::LoadStarted => ProjectCensusEvent::LoadStarted,
                CanonicalCensusEvent::Loaded {
                    disposition,
                    roots,
                    elapsed,
                } => {
                    let program = program.ok_or_else(|| {
                        io::Error::other("the loaded census event has no Program")
                    })?;
                    let serialization_started = Instant::now();
                    let graph = serde_json::to_value(graph::snapshot_report(program))
                        .map_err(io::Error::other)?;
                    let roots: Option<Vec<_>> = roots.map(|roots| {
                        roots
                            .into_iter()
                            .enumerate()
                            .map(|(root_index, root)| ProjectCensusRoot {
                                root_index,
                                requested_name: root.requested_name,
                                file_name: graph::path_identity(&root.file_name),
                                file_id: root.file_id.map(ts_ast::FileId::index),
                            })
                            .collect()
                    });
                    input_identity = Some(census_input_identity(&graph, roots.as_deref())?);
                    ProjectCensusEvent::Loaded {
                        disposition: match disposition {
                            CanonicalCensusLoadDisposition::Ready => "ready",
                            CanonicalCensusLoadDisposition::ConfigUnavailable => {
                                "config_unavailable"
                            }
                            CanonicalCensusLoadDisposition::NoCheck => "no_check",
                        }
                        .to_owned(),
                        roots,
                        graph,
                        load_diagnostics: program
                            .diagnostics()
                            .iter()
                            .map(|diagnostic| {
                                serde_json::to_value(ProjectDiagnosticRecord::from(diagnostic))
                                    .map_err(io::Error::other)
                            })
                            .collect::<io::Result<_>>()?,
                        load_elapsed_ms: census_millis(elapsed)?,
                        graph_serialization_elapsed_ms: census_millis(
                            serialization_started.elapsed(),
                        )?,
                    }
                }
                CanonicalCensusEvent::LoadFailed { error, elapsed } => {
                    has_invariant_failure |= !error.is_unsupported_boundary();
                    ProjectCensusEvent::LoadFailed {
                        failure: ProjectCensusFailure::from_error(
                            program,
                            CanonicalCensusPhase::Load,
                            &error,
                        ),
                        load_elapsed_ms: census_millis(elapsed)?,
                    }
                }
                CanonicalCensusEvent::AttemptStarted { attempt } => {
                    ProjectCensusEvent::AttemptStarted {
                        attempt: attempt.into(),
                    }
                }
                CanonicalCensusEvent::PhaseStarted { attempt, phase } => {
                    ProjectCensusEvent::PhaseStarted {
                        attempt: attempt.into(),
                        phase: census_phase(phase).to_owned(),
                    }
                }
                CanonicalCensusEvent::PhaseFinished {
                    attempt,
                    phase,
                    elapsed,
                } => ProjectCensusEvent::PhaseFinished {
                    attempt: attempt.into(),
                    phase: census_phase(phase).to_owned(),
                    phase_elapsed_ms: census_millis(elapsed)?,
                },
                CanonicalCensusEvent::AttemptFinished {
                    attempt,
                    outcome,
                    diagnostics,
                    elapsed,
                } => {
                    let attempt = ProjectCensusAttempt::from(attempt);
                    let outcome = match outcome {
                        CanonicalCensusOutcome::Complete => match attempt {
                            ProjectCensusAttempt::Ordinary => {
                                ProjectCensusOutcome::OrdinaryCheckComplete
                            }
                            ProjectCensusAttempt::Root { .. } => {
                                ProjectCensusOutcome::SourceCheckComplete
                            }
                        },
                        CanonicalCensusOutcome::Skipped(reason) => {
                            ProjectCensusOutcome::SkippedByOriginalPolicy {
                                reason: census_skip_reason(reason).to_owned(),
                            }
                        }
                        CanonicalCensusOutcome::Unloaded => ProjectCensusOutcome::Unattempted {
                            reason: CENSUS_UNLOADED_ROOT_REASON.to_owned(),
                        },
                        CanonicalCensusOutcome::Failure { phase, error } => {
                            let failure = ProjectCensusFailure::from_error(program, phase, &error);
                            if error.is_unsupported_boundary() {
                                ProjectCensusOutcome::Unsupported { failure }
                            } else {
                                has_invariant_failure = true;
                                ProjectCensusOutcome::Invariant { failure }
                            }
                        }
                    };
                    let diagnostics = census_diagnostics(diagnostics)?;
                    has_invariant_failure |= matches!(
                        &diagnostics,
                        ProjectCensusDiagnostics::Partial {
                            conversion_error: Some(error),
                            ..
                        } if error.class == "invariant"
                    );
                    ProjectCensusEvent::AttemptFinished {
                        attempt,
                        outcome,
                        diagnostics: Some(diagnostics),
                        attempt_elapsed_ms: census_millis(elapsed)?,
                    }
                }
            };
            emit(event, &input_identity)?;
            Ok(
                if options
                    .soft_deadline
                    .is_some_and(|deadline| started.elapsed() >= deadline)
                {
                    CanonicalCensusControl::Stop
                } else {
                    CanonicalCensusControl::Continue
                },
            )
        },
    )?;
    let completion = match completion {
        CanonicalCensusCompletion::Complete => "complete",
        CanonicalCensusCompletion::LoadUnavailable => "load_unavailable",
        CanonicalCensusCompletion::NoCheck => "no_check",
        CanonicalCensusCompletion::PreparationFailed => "preparation_failed",
        CanonicalCensusCompletion::Stopped => "stopped",
    }
    .to_owned();
    provenance.finish(started.elapsed());
    emit(
        ProjectCensusEvent::Finished {
            stop_reason: (completion == "stopped").then(|| {
                "The soft wall-time deadline was reached at an event boundary.".to_owned()
            }),
            completion: completion.clone(),
            provenance: serde_json::to_value(&provenance).map_err(io::Error::other)?,
        },
        &input_identity,
    )?;
    Ok(ProjectCensusRunStatus {
        completion,
        has_invariant_failure,
        elapsed_ms: census_millis(started.elapsed())?,
    })
}

fn census_phase(phase: CanonicalCensusPhase) -> &'static str {
    match phase {
        CanonicalCensusPhase::Load => "load",
        CanonicalCensusPhase::Preparation => "preparation",
        CanonicalCensusPhase::Binding => "binding",
        CanonicalCensusPhase::Context => "context",
        CanonicalCensusPhase::Source => "source",
        CanonicalCensusPhase::PostSource => "post_source",
    }
}

fn census_skip_reason(reason: CanonicalCensusSkipReason) -> &'static str {
    match reason {
        CanonicalCensusSkipReason::NoCheck => "no_check",
        CanonicalCensusSkipReason::DefaultLibrary => "default_library",
        CanonicalCensusSkipReason::DeclarationFile => "declaration_file",
        CanonicalCensusSkipReason::NoCheckDirective => "no_check_directive",
        CanonicalCensusSkipReason::UncheckedJavaScript => "unchecked_javascript",
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct ProjectCensusRootResult {
    pub root: ProjectCensusRoot,
    pub started: bool,
    pub input_identity: Option<String>,
    pub phase_reached: Option<String>,
    pub elapsed_ms: Option<u64>,
    pub outcome: ProjectCensusOutcome,
    pub diagnostics: ProjectCensusDiagnostics,
}

#[derive(Clone, Debug, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct ProjectCensusReadback {
    pub run_id: String,
    pub input_identity: Option<String>,
    pub completion: Option<String>,
    pub has_footer: bool,
    pub truncated_final_record: bool,
    pub roots: Option<Vec<ProjectCensusRootResult>>,
    pub ordinary_started: bool,
    pub ordinary: ProjectCensusOutcome,
    pub ordinary_diagnostics: ProjectCensusDiagnostics,
    pub records: Vec<ProjectCensusRecord>,
}

fn invalid_census(detail: &str) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, detail)
}

/// Reads complete JSON lines and joins outcomes to the original root roster.
/// Missing results remain unattempted. Only an EOF-truncated final JSON record
/// can be ignored. A complete malformed record is always an error.
///
/// # Errors
/// Rejects I/O errors, malformed records, changed identities and invalid event order.
#[allow(clippy::too_many_lines)] // Keep the complete event-order state machine in one place.
pub fn read_project_census(mut reader: impl BufRead) -> io::Result<ProjectCensusReadback> {
    let mut records = Vec::<ProjectCensusRecord>::new();
    let mut line = Vec::new();
    let mut truncated_final_record = false;
    loop {
        line.clear();
        if reader.read_until(b'\n', &mut line)? == 0 {
            break;
        }
        match serde_json::from_slice::<ProjectCensusRecord>(&line) {
            Ok(record) => records.push(record),
            Err(error) if !line.ends_with(b"\n") && error.is_eof() => {
                truncated_final_record = true;
                break;
            }
            Err(error) => return Err(io::Error::new(io::ErrorKind::InvalidData, error)),
        }
    }
    let first = records
        .first()
        .ok_or_else(|| invalid_census("No complete run identity was recorded."))?;
    if !matches!(first.event, ProjectCensusEvent::RunStarted { .. })
        || first.run_id.trim().is_empty()
    {
        return Err(invalid_census(
            "The first census record must identify the run.",
        ));
    }
    let run_id = first.run_id.clone();
    let mut input_identity = None;
    let mut loaded = false;
    let mut load_started = false;
    let mut load_failed = false;
    let mut disposition = None;
    let mut roots = None::<Vec<ProjectCensusRootResult>>;
    let mut ordinary_started = false;
    let mut ordinary = None;
    let mut ordinary_diagnostics = None;
    let mut active = None;
    let mut phases = Vec::<String>::new();
    let mut completed_phases = Vec::<String>::new();
    let mut preparation_failed = false;
    let mut next_root = 0;
    let mut completion = None;
    let mut last_elapsed = 0;
    for (index, record) in records.iter().enumerate() {
        if completion.is_some() {
            return Err(invalid_census(
                "A complete record follows the census footer.",
            ));
        }
        if record.schema_version != 1
            || record.report_kind != "cold_root_failure_census"
            || record.run_id != run_id
            || record.sequence != index
            || record.elapsed_ms < last_elapsed
        {
            return Err(invalid_census(
                "The census schema, run identity, sequence or clock changed.",
            ));
        }
        last_elapsed = record.elapsed_ms;
        if let ProjectCensusEvent::Loaded { graph, roots, .. } = &record.event {
            let expected = census_input_identity(graph, roots.as_deref())?;
            if record.input_identity.as_deref() != Some(expected.as_str()) {
                return Err(invalid_census(
                    "The loaded graph and root roster do not match their input identity.",
                ));
            }
            input_identity = Some(expected);
        }
        if record.input_identity != input_identity {
            return Err(invalid_census(
                "The complete input identity changed between events.",
            ));
        }
        match &record.event {
            ProjectCensusEvent::RunStarted { .. } => {
                if index != 0 {
                    return Err(invalid_census("The run identity was repeated."));
                }
            }
            ProjectCensusEvent::LoadStarted => {
                if index != 1 || load_started {
                    return Err(invalid_census("Invalid load start."));
                }
                load_started = true;
            }
            ProjectCensusEvent::Loaded {
                disposition: state,
                roots: roster,
                ..
            } => {
                if !load_started
                    || loaded
                    || load_failed
                    || !matches!(state.as_str(), "ready" | "config_unavailable" | "no_check")
                {
                    return Err(invalid_census("Invalid loaded disposition."));
                }
                if (state == "config_unavailable") != roster.is_none() {
                    return Err(invalid_census(
                        "Root coverage does not match the load disposition.",
                    ));
                }
                loaded = true;
                disposition = Some(state.clone());
                roots = roster.as_ref().map(|roster| {
                    roster
                        .iter()
                        .cloned()
                        .map(|root| ProjectCensusRootResult {
                            root,
                            started: false,
                            input_identity: record.input_identity.clone(),
                            phase_reached: None,
                            elapsed_ms: None,
                            outcome: ProjectCensusOutcome::Unattempted {
                                reason: "No completed root result was recorded.".to_owned(),
                            },
                            diagnostics: ProjectCensusDiagnostics::Unattempted {
                                reason: "No completed root result was recorded.".to_owned(),
                            },
                        })
                        .collect()
                });
                if roots.as_ref().is_some_and(|roots| {
                    roots
                        .iter()
                        .enumerate()
                        .any(|(index, root)| root.root.root_index != index)
                }) {
                    return Err(invalid_census(
                        "The original root indices are missing or repeated.",
                    ));
                }
            }
            ProjectCensusEvent::LoadFailed { failure, .. } => {
                if !load_started || loaded || load_failed || failure.phase != "load" {
                    return Err(invalid_census("Invalid load failure."));
                }
                validate_census_failure(failure, &failure.class)?;
                load_failed = true;
            }
            ProjectCensusEvent::AttemptStarted { attempt } => {
                if !loaded
                    || active.is_some()
                    || preparation_failed
                    || disposition.as_deref() == Some("config_unavailable")
                {
                    return Err(invalid_census(
                        "An attempt started without an available idle Program.",
                    ));
                }
                match attempt {
                    ProjectCensusAttempt::Ordinary => {
                        if ordinary_started
                            || next_root != 0
                            || !matches!(disposition.as_deref(), Some("ready" | "no_check"))
                        {
                            return Err(invalid_census("Invalid ordinary-order control start."));
                        }
                        ordinary_started = true;
                    }
                    ProjectCensusAttempt::Root { root_index } => {
                        if ordinary.is_none() {
                            return Err(invalid_census(
                                "A cold root preceded the ordinary-order result.",
                            ));
                        }
                        if *root_index != next_root {
                            return Err(invalid_census(
                                "Cold roots are not in original request order.",
                            ));
                        }
                        let root = roots
                            .as_mut()
                            .and_then(|roots| roots.get_mut(*root_index))
                            .ok_or_else(|| invalid_census("An attempt names an unknown root."))?;
                        if root.started {
                            return Err(invalid_census("A root attempt was repeated."));
                        }
                        root.started = true;
                        next_root += 1;
                    }
                }
                active = Some(*attempt);
                completed_phases.clear();
            }
            ProjectCensusEvent::PhaseStarted { attempt, phase } => {
                if active != Some(*attempt)
                    || disposition.as_deref() == Some("no_check")
                    || matches!(attempt, ProjectCensusAttempt::Root { root_index } if roots.as_ref().and_then(|roots| roots.get(*root_index)).is_none_or(|root| root.root.file_id.is_none()))
                    || !valid_census_phase_start(phase, *attempt, &phases, &completed_phases)
                {
                    return Err(invalid_census("Invalid phase start or nested phase."));
                }
                phases.push(phase.clone());
                if let ProjectCensusAttempt::Root { root_index } = attempt {
                    roots
                        .as_mut()
                        .and_then(|roots| roots.get_mut(*root_index))
                        .ok_or_else(|| invalid_census("Unknown root phase."))?
                        .phase_reached = Some(phase.clone());
                }
            }
            ProjectCensusEvent::PhaseFinished { attempt, phase, .. } => {
                if active != Some(*attempt) || phases.last() != Some(phase) {
                    return Err(invalid_census("A phase result has no matching start."));
                }
                phases.pop();
                completed_phases.push(phase.clone());
            }
            ProjectCensusEvent::AttemptFinished {
                attempt,
                outcome,
                diagnostics,
                attempt_elapsed_ms,
            } => {
                if active != Some(*attempt) {
                    return Err(invalid_census("An attempt result has no matching start."));
                }
                match outcome {
                    ProjectCensusOutcome::SourceCheckComplete => {
                        if !matches!(attempt, ProjectCensusAttempt::Root { .. })
                            || !phases.is_empty()
                            || !completed_phases.iter().any(|phase| phase == "source")
                        {
                            return Err(invalid_census("Invalid completed cold source check."));
                        }
                    }
                    ProjectCensusOutcome::OrdinaryCheckComplete => {
                        if *attempt != ProjectCensusAttempt::Ordinary
                            || !phases.is_empty()
                            || !completed_phases.iter().any(|phase| phase == "post_source")
                        {
                            return Err(invalid_census("Invalid completed ordinary-order check."));
                        }
                    }
                    ProjectCensusOutcome::Unsupported { failure }
                    | ProjectCensusOutcome::Invariant { failure } => {
                        let class = if matches!(outcome, ProjectCensusOutcome::Unsupported { .. }) {
                            "unsupported"
                        } else {
                            "invariant"
                        };
                        validate_census_failure(failure, class)?;
                        if failure.phase == "load"
                            || matches!(attempt, ProjectCensusAttempt::Root { .. })
                                && failure.phase == "post_source"
                            || !phases.contains(&failure.phase)
                                && !completed_phases.contains(&failure.phase)
                        {
                            return Err(invalid_census(
                                "The returned failure phase was not attempted.",
                            ));
                        }
                        preparation_failed = matches!(
                            failure.phase.as_str(),
                            "preparation" | "binding" | "context"
                        );
                    }
                    ProjectCensusOutcome::SkippedByOriginalPolicy { reason } => {
                        if !phases.is_empty()
                            || !completed_phases.is_empty()
                            || (disposition.as_deref() == Some("no_check"))
                                != (reason == "no_check")
                            || *attempt == ProjectCensusAttempt::Ordinary && reason != "no_check"
                            || matches!(attempt, ProjectCensusAttempt::Root { root_index } if roots.as_ref().and_then(|roots| roots.get(*root_index)).is_none_or(|root| root.root.file_id.is_none()))
                            || !matches!(
                                reason.as_str(),
                                "no_check"
                                    | "default_library"
                                    | "declaration_file"
                                    | "no_check_directive"
                                    | "unchecked_javascript"
                            )
                        {
                            return Err(invalid_census("Invalid policy skip."));
                        }
                    }
                    ProjectCensusOutcome::Unattempted { .. } => {
                        if !phases.is_empty()
                            || !completed_phases.is_empty()
                            || !matches!(attempt, ProjectCensusAttempt::Root { root_index } if roots.as_ref().and_then(|roots| roots.get(*root_index)).is_some_and(|root| root.root.file_id.is_none()))
                        {
                            return Err(invalid_census(
                                "An unloaded root has checker phase records.",
                            ));
                        }
                    }
                }
                if let Some(diagnostics) = diagnostics {
                    validate_census_diagnostics(diagnostics, *attempt, outcome, &completed_phases)?;
                }
                let diagnostics = diagnostics
                    .clone()
                    .unwrap_or(ProjectCensusDiagnostics::NotRecorded);
                match attempt {
                    ProjectCensusAttempt::Ordinary => {
                        ordinary = Some(outcome.clone());
                        ordinary_diagnostics = Some(diagnostics);
                    }
                    ProjectCensusAttempt::Root { root_index } => {
                        let root = roots
                            .as_mut()
                            .and_then(|roots| roots.get_mut(*root_index))
                            .ok_or_else(|| invalid_census("Unknown root result."))?;
                        root.outcome = outcome.clone();
                        root.diagnostics = diagnostics;
                        root.elapsed_ms = Some(*attempt_elapsed_ms);
                        if let ProjectCensusOutcome::Unsupported { failure }
                        | ProjectCensusOutcome::Invariant { failure } = outcome
                        {
                            root.phase_reached = Some(failure.phase.clone());
                        }
                    }
                }
                phases.clear();
                active = None;
            }
            ProjectCensusEvent::Finished {
                completion: state,
                stop_reason,
                ..
            } => {
                if !matches!(
                    state.as_str(),
                    "complete" | "load_unavailable" | "no_check" | "preparation_failed" | "stopped"
                ) || (state == "stopped") != stop_reason.is_some()
                    || state != "stopped" && active.is_some()
                {
                    return Err(invalid_census("Invalid census completion reason."));
                }
                if state == "complete"
                    && (disposition.as_deref() != Some("ready")
                        || preparation_failed
                        || ordinary.is_none()
                        || roots.as_ref().is_none_or(|roots| roots.len() != next_root))
                {
                    return Err(invalid_census(
                        "A complete footer has incomplete root coverage.",
                    ));
                }
                if state == "no_check"
                    && (disposition.as_deref() != Some("no_check")
                        || !matches!(ordinary.as_ref(), Some(ProjectCensusOutcome::SkippedByOriginalPolicy { reason }) if reason == "no_check")
                        || roots.as_ref().is_none_or(|roots| roots.len() != next_root))
                {
                    return Err(invalid_census(
                        "A noCheck footer lacks original noCheck policy.",
                    ));
                }
                if state == "preparation_failed" && !preparation_failed {
                    return Err(invalid_census(
                        "A preparation-failure footer has no returned preparation failure.",
                    ));
                }
                if state == "load_unavailable"
                    && !load_failed
                    && disposition.as_deref() != Some("config_unavailable")
                {
                    return Err(invalid_census(
                        "A load-unavailable footer lacks a load failure.",
                    ));
                }
                completion = Some(state.clone());
            }
        }
    }
    let unattempted = |was_started: bool| {
        let reason = if was_started && completion.as_deref() == Some("stopped") {
            "The soft wall-time stop interrupted this attempt at an event boundary."
        } else if was_started {
            "The attempt started but no returned outcome was recorded. Its interruption cause is unknown."
        } else {
            match completion.as_deref() {
                Some("preparation_failed") => {
                    "A common preparation failure prevented this attempt."
                }
                Some("stopped") => "The soft wall-time stop occurred before this attempt.",
                Some("load_unavailable") => {
                    "The original Program was unavailable for this attempt."
                }
                _ => {
                    "No attempt was recorded. The stream does not establish a process exit reason."
                }
            }
        };
        ProjectCensusOutcome::Unattempted {
            reason: reason.to_owned(),
        }
    };
    if let Some(roots) = &mut roots {
        for root in roots {
            if !root.started
                || active
                    == Some(ProjectCensusAttempt::Root {
                        root_index: root.root.root_index,
                    })
            {
                root.outcome = if completion.as_deref() == Some("no_check") {
                    ProjectCensusOutcome::SkippedByOriginalPolicy {
                        reason: "no_check".to_owned(),
                    }
                } else {
                    unattempted(root.started)
                };
                root.diagnostics = unrecorded_census_diagnostics(&root.outcome);
            }
        }
    }
    let ordinary = ordinary.unwrap_or_else(|| {
        if completion.as_deref() == Some("no_check") {
            ProjectCensusOutcome::SkippedByOriginalPolicy {
                reason: "no_check".to_owned(),
            }
        } else {
            unattempted(ordinary_started)
        }
    });
    let ordinary_diagnostics =
        ordinary_diagnostics.unwrap_or_else(|| unrecorded_census_diagnostics(&ordinary));
    Ok(ProjectCensusReadback {
        run_id,
        input_identity,
        has_footer: completion.is_some(),
        truncated_final_record,
        ordinary,
        ordinary_diagnostics,
        ordinary_started,
        roots,
        completion,
        records,
    })
}

fn unrecorded_census_diagnostics(outcome: &ProjectCensusOutcome) -> ProjectCensusDiagnostics {
    match outcome {
        ProjectCensusOutcome::SkippedByOriginalPolicy { reason } => {
            ProjectCensusDiagnostics::Skipped {
                reason: reason.clone(),
            }
        }
        ProjectCensusOutcome::Unattempted { reason } => ProjectCensusDiagnostics::Unattempted {
            reason: reason.clone(),
        },
        _ => ProjectCensusDiagnostics::NotRecorded,
    }
}

fn validate_census_diagnostics(
    diagnostics: &ProjectCensusDiagnostics,
    attempt: ProjectCensusAttempt,
    outcome: &ProjectCensusOutcome,
    completed_phases: &[String],
) -> io::Result<()> {
    let finished = |phase| completed_phases.iter().any(|completed| completed == phase);
    let failure_phase = match outcome {
        ProjectCensusOutcome::Unsupported { failure }
        | ProjectCensusOutcome::Invariant { failure } => Some(failure.phase.as_str()),
        _ => None,
    };
    let valid = match diagnostics {
        ProjectCensusDiagnostics::CompleteProgram { policy, .. } => {
            *policy == CENSUS_PROGRAM_DIAGNOSTIC_POLICY
                && attempt == ProjectCensusAttempt::Ordinary
                && matches!(outcome, ProjectCensusOutcome::OrdinaryCheckComplete)
                && finished("post_source")
        }
        ProjectCensusDiagnostics::CompleteSourceContext { policy, .. } => {
            *policy == CENSUS_RAW_CONTEXT_DIAGNOSTIC_POLICY
                && matches!(attempt, ProjectCensusAttempt::Root { .. })
                && matches!(outcome, ProjectCensusOutcome::SourceCheckComplete)
                && finished("source")
        }
        ProjectCensusDiagnostics::Partial {
            scope,
            policy,
            conversion_error,
            ..
        } => {
            if let Some(error) = conversion_error
                && (!matches!(error.class.as_str(), "unsupported" | "invariant")
                    || error.code.is_empty()
                    || error.returned_error.is_empty())
            {
                return Err(invalid_census("Invalid diagnostic conversion error."));
            }
            match scope {
                ProjectCensusDiagnosticScope::Program => {
                    *policy == CENSUS_PARTIAL_PROGRAM_DIAGNOSTIC_POLICY
                        && attempt == ProjectCensusAttempt::Ordinary
                        && failure_phase == Some("post_source")
                        && finished("post_source")
                        && conversion_error.is_none()
                }
                ProjectCensusDiagnosticScope::RawContext => {
                    *policy == CENSUS_RAW_CONTEXT_DIAGNOSTIC_POLICY
                        && (failure_phase.is_some_and(|phase| {
                            matches!(phase, "source" | "post_source") && finished(phase)
                        }) || matches!(attempt, ProjectCensusAttempt::Root { .. })
                            && matches!(outcome, ProjectCensusOutcome::SourceCheckComplete)
                            && finished("source")
                            && conversion_error.is_some())
                }
            }
        }
        ProjectCensusDiagnostics::UnavailableBeforeContext => {
            matches!(failure_phase, Some("preparation" | "binding" | "context"))
        }
        ProjectCensusDiagnostics::Skipped { reason } => matches!(
            outcome,
            ProjectCensusOutcome::SkippedByOriginalPolicy { reason: actual } if actual == reason
        ),
        ProjectCensusDiagnostics::Unattempted { reason } => matches!(
            outcome,
            ProjectCensusOutcome::Unattempted { reason: actual } if actual == reason
        ),
        ProjectCensusDiagnostics::NotRecorded => false,
    };
    if !valid {
        return Err(invalid_census(
            "Diagnostic completeness does not match the attempt, outcome or phase.",
        ));
    }
    Ok(())
}

fn valid_census_phase(phase: &str) -> bool {
    matches!(
        phase,
        "load" | "preparation" | "binding" | "context" | "source" | "post_source"
    )
}

fn valid_census_phase_start(
    phase: &str,
    attempt: ProjectCensusAttempt,
    active: &[String],
    completed: &[String],
) -> bool {
    let finished = |name| completed.iter().any(|phase| phase == name);
    if finished(phase) {
        return false;
    }
    match phase {
        "preparation" => active.is_empty() && completed.is_empty(),
        "binding" => active.len() == 1 && active[0] == "preparation",
        "context" => active.len() == 1 && active[0] == "preparation" && finished("binding"),
        "source" => {
            active.is_empty()
                && finished("preparation")
                && finished("binding")
                && finished("context")
        }
        "post_source" => {
            attempt == ProjectCensusAttempt::Ordinary && active.is_empty() && finished("source")
        }
        _ => false,
    }
}

fn validate_census_failure(failure: &ProjectCensusFailure, class: &str) -> io::Result<()> {
    if failure.class != class
        || !matches!(class, "unsupported" | "invariant")
        || failure.code.is_empty()
        || failure.returned_error.is_empty()
        || !valid_census_phase(&failure.phase)
        || failure.location.is_some() == failure.location_unavailable.is_some()
        || failure
            .location
            .as_ref()
            .is_some_and(|location| location.start_byte > location.end_byte)
    {
        return Err(invalid_census("Invalid returned-error evidence."));
    }
    Ok(())
}

fn census_error_node(error: &CanonicalProgramCheckError) -> Option<NodeRef> {
    match error {
        CanonicalProgramCheckError::ModuleSpecifierResolutionModeUnsupported(node)
        | CanonicalProgramCheckError::InvalidModuleSourceFile(node)
        | CanonicalProgramCheckError::InvalidModuleSpecifier(node)
        | CanonicalProgramCheckError::InvalidDiagnosticNode(node)
        | CanonicalProgramCheckError::ImportHelper { node, .. }
        | CanonicalProgramCheckError::InvalidRelatedDiagnosticNode { node, .. }
        | CanonicalProgramCheckError::ExternalModuleTargetUnsupported {
            specifier: node, ..
        }
        | CanonicalProgramCheckError::OmittedModuleTargetUnsupported {
            specifier: node, ..
        }
        | CanonicalProgramCheckError::MissingResolvedModuleTarget {
            specifier: node, ..
        } => Some(*node),
        CanonicalProgramCheckError::InvalidDiagnosticRange { node, .. } => *node,
        CanonicalProgramCheckError::SourceCheck { error, .. } => census_source_error_node(error),
        _ => None,
    }
}

fn census_error_file_name(error: &CanonicalProgramCheckError) -> Option<&str> {
    match error {
        CanonicalProgramCheckError::UnsupportedSourceKind { file_name, .. }
        | CanonicalProgramCheckError::FixedModuleFormatUnsupported { file_name }
        | CanonicalProgramCheckError::ImportMetaModuleIndicatorUnsupported { file_name }
        | CanonicalProgramCheckError::NodeModuleFactsUnsupported { file_name, .. }
        | CanonicalProgramCheckError::PlainEsmModuleResolutionUnsupported { file_name, .. }
        | CanonicalProgramCheckError::DeclarationFileCheckingUnsupported { file_name }
        | CanonicalProgramCheckError::Bind { file_name, .. }
        | CanonicalProgramCheckError::DeclarationBind { file_name, .. }
        | CanonicalProgramCheckError::SourceCheck { file_name, .. }
        | CanonicalProgramCheckError::ImportHelper { file_name, .. }
        | CanonicalProgramCheckError::MissingBoundFile { file_name, .. } => Some(file_name),
        CanonicalProgramCheckError::MissingResolvedModuleTarget {
            containing_file, ..
        } => Some(containing_file),
        _ => None,
    }
}

fn census_source_error_node(error: &ts_checker::semantic::SourceCheckError) -> Option<NodeRef> {
    use ts_checker::semantic::{
        SourceCheckError as E, SourceCheckProvenanceError as P, SourceObjectLiteralError as O,
        UnsupportedSourceSyntax as U,
    };
    match error {
        E::Arrow(node)
        | E::Call(node)
        | E::Enum(node)
        | E::Import(node)
        | E::Class(node)
        | E::Property(node)
        | E::Element(node)
        | E::PrimitiveOperator(node)
        | E::LogicalOperator(node)
        | E::Conditional(node) => Some(*node),
        E::Function(ts_checker::semantic::SourceFunctionInvariant::Callable(node)) => Some(*node),
        E::ObjectLiteral(O::InvalidCache { node, .. } | O::Capacity(node)) => Some(*node),
        E::Provenance(
            P::MissingNode(node)
            | P::NodeNotBound(node)
            | P::RepeatedNode(node)
            | P::MissingDeclarationSymbol(node)
            | P::InvalidDiagnosticNode(node)
            | P::MismatchedNodeData { node, .. }
            | P::InvalidParent { node, .. }
            | P::InvalidRange { node, .. },
        ) => Some(*node),
        E::Provenance(P::InvalidDiagnosticRange { node, .. }) => *node,
        E::Unsupported(
            U::Syntax { node, .. }
            | U::MissingExternalModuleFact { node, .. }
            | U::InvalidPrefixUnaryOperator { node, .. }
            | U::JsDoc(node)
            | U::MissingVariableType(node)
            | U::MissingVariableInitializer(node)
            | U::EmptyVariableDeclarationList(node)
            | U::InvalidLiteralSpelling(node)
            | U::InvalidLiteralFlags(node)
            | U::BigIntExponentiationTarget(node)
            | U::ConstAssertion(node)
            | U::NestedAssertion(node)
            | U::Arrow(node)
            | U::Call(node)
            | U::Enum(node)
            | U::Import(node)
            | U::Class(node)
            | U::Property(node)
            | U::Element(node)
            | U::New(node),
        ) => Some(*node),
        E::Unsupported(U::Variable(
            ts_checker::semantic::VariableUnsupported::IdentifierNotPrior { node, .. },
        )) => Some(*node),
        E::DeclaredType(error) => census_declared_error_node(error),
        E::Unsupported(U::Function(error)) => {
            use ts_checker::semantic::SourceFunctionUnsupported as F;
            match error {
                F::UnresolvedIdentifier(node)
                | F::Callable(node)
                | F::FunctionBody(node)
                | F::ResolverDeferred { node, .. }
                | F::AliasSymbol { node, .. }
                | F::MergedSymbol { node, .. }
                | F::NonFunctionSymbol { node, .. }
                | F::NonUniqueDeclaration { node, .. }
                | F::CrossFileDeclaration { node, .. }
                | F::ExpandoFunction { node, .. }
                | F::IdentifierNotHoisted { node, .. } => Some(*node),
            }
        }
        _ => None,
    }
}

fn census_declared_error_node(error: &ts_checker::semantic::DeclaredTypeError) -> Option<NodeRef> {
    use ts_checker::semantic::{
        DeclaredTypeError, DeclaredTypeUnavailable as D, TypeNodeUnavailable as T,
    };
    if let DeclaredTypeError::Unavailable(
        D::MissingOrForeignFacts(node)
        | D::DeclarationSymbolMismatch(node)
        | D::InvalidClassDeclaration(node)
        | D::InvalidInterfaceDeclaration(node)
        | D::UnsupportedInterfaceHeritageResolution(node)
        | D::InvalidTypeParameterDeclaration(node)
        | D::UnsupportedOuterTypeParameterContext { node, .. },
    ) = error
    {
        return Some(*node);
    }
    let DeclaredTypeError::TypeNodeUnavailable(error) = error else {
        return None;
    };
    match error {
        T::UnsupportedSyntax { node, .. }
        | T::ImportAliasTypeReference { node, .. }
        | T::NamespaceAlias { node, .. }
        | T::NamespaceAliasHost { node, .. }
        | T::InvalidImportAliasTarget { node, .. }
        | T::InvalidJsDocImportTypeTarget { node, .. }
        | T::UnsupportedReferenceTarget { node, .. }
        | T::GenericReferenceUnsupported { node, .. }
        | T::InvalidCachedSymbol { node, .. }
        | T::RecursiveTupleAliasUnsupported { node, .. }
        | T::JsDoc(node)
        | T::InvalidParenthesizedType(node)
        | T::InvalidTypeReference(node)
        | T::QualifiedTypeReference(node)
        | T::TypeArgumentsUnsupported(node)
        | T::MissingTypeReference(node)
        | T::ImportAliasCapabilityUnsupported(node)
        | T::JsDocImportTypeCapabilityUnsupported(node)
        | T::InvalidTypeAliasDeclaration(node)
        | T::JsDocTypeAlias(node)
        | T::MissingPlannedTypeReference(node)
        | T::InvalidLiteralType(node)
        | T::MissingPlannedLiteralType(node)
        | T::InvalidUnionType(node)
        | T::MissingPlannedUnionType(node)
        | T::UnsupportedUnionConstituent(node)
        | T::InvalidIntersectionType(node)
        | T::MissingPlannedIntersectionType(node)
        | T::UnsupportedIntersectionConstituent(node)
        | T::UnsupportedIntersectionProperty(node)
        | T::InvalidIndexedAccessType(node)
        | T::MissingPlannedIndexedAccessType(node)
        | T::InvalidKeyofType(node)
        | T::MissingPlannedKeyofType(node)
        | T::InvalidFunctionType(node)
        | T::InvalidTupleType(node)
        | T::MissingPlannedTupleType(node) => Some(*node),
        T::GenericAliasConstraintUnsupported { parameter, .. } => Some(*parameter),
        T::GenericAliasDefaultReferenceUnsupported { default_type, .. }
        | T::CircularGenericAliasDefault { default_type, .. } => Some(*default_type),
        T::UnsupportedTupleElementOrder { element, .. } => Some(*element),
        _ => None,
    }
}
