//! Owned reports from one on-disk canonical project and forced source replay.

mod graph;
mod options;
mod provenance;

use std::{io, path::Path, time::Instant};

use serde::Serialize;
use ts_ast::NodeRef;
use ts_compiler::{
    CanonicalProgramCheckError, CanonicalProgramCheckFailureClass, CanonicalProgramQueries,
    Program, ProgramDiagnostic,
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
    pub pinned_error_baseline: ProjectStage<ProjectTextArtifact>,
}

impl ProjectDiagnosticArtifact {
    fn new(diagnostics: &[ProgramDiagnostic]) -> Self {
        let records = diagnostics
            .iter()
            .map(ProjectDiagnosticRecord::from)
            .collect::<Vec<_>>();
        let bytes =
            serde_json::to_vec(&records).expect("diagnostic records contain only JSON values");
        Self {
            diagnostic_policy: "Complete canonical Program snapshot. The runner does not invoke a separate declaration-diagnostic or emit stage.",
            records,
            json_digest: stable_digest(&bytes),
            digest_algorithm: SCORECARD_DIGEST_ALGORITHM,
            pinned_error_baseline: ProjectStage::unavailable(
                "The pinned error-baseline renderer has no real-project input API. Structured records are not an errors.txt artifact.",
            ),
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
            value: ProjectDiagnosticArtifact::new(diagnostics),
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
            || self.types.output.is_invariant()
            || self.symbols.output.is_invariant()
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct ProjectReplayEquality {
    pub diagnostic_records: bool,
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
            let expected = ProjectDiagnosticArtifact::new(program.diagnostics());
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
                value: ProjectDiagnosticArtifact::new(program.diagnostics()),
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
        type_bytes: None,
        symbol_bytes: None,
        type_walk: None,
        symbol_walk: None,
        type_identities: None,
        symbol_identities: None,
        checker_store_identity: store == queries.semantic_store_id(),
    };
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
