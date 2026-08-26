//! Owned facts retained while loading a Program's source graph.

use std::collections::BTreeMap;

use ts_ast::FileId;
use ts_checker::semantic::{CanonicalModuleResolutionManifestInput, CanonicalModuleResolutionMode};
use ts_config::{
    ConfigInputKind, ConfigResolutionEvent, ConfigResolutionObservation, ProjectConfig,
};
use ts_core::TextRange;
use ts_module::{ModuleFormat, ResolutionOptions, ResolutionResult};
use ts_options::{CompilerOptions, ModuleKind};
use ts_path::{CaseSensitivity, is_absolute, normalize_path, resolve_path};

use crate::{CanonicalProgramCheckError, Program};

/// One root in the original input order, including duplicate and missing roots.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ProgramGraphRoot {
    pub requested_name: String,
    pub file_name: String,
    pub file_id: Option<FileId>,
}

/// One loaded source, with the text used by the parser.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ProgramGraphSource {
    pub file_id: FileId,
    pub file_name: String,
    pub source_text: String,
    pub is_default_library: bool,
    pub implied_node_format: ModuleKind,
    pub emit_module_mode: CanonicalModuleResolutionMode,
}

/// Config data already read by the Program loader.
#[derive(Clone, Debug, PartialEq)]
pub struct ProgramGraphConfig {
    /// VFS text from the leaf's later diagnostic read, not raw file bytes.
    /// This can differ from the resolver's retained parser input.
    pub source_text: Option<String>,
    /// The existing typed config after inheritance and path resolution.
    pub resolved: ProjectConfig,
}

/// Why the loader called the module resolver.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ProgramGraphResolutionKind {
    Module,
    JsxRuntime,
    ImportHelpers,
    AutomaticTypeDirective,
    TypeReference,
}

/// The exact request passed to the resolver.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ProgramGraphResolutionRequest {
    pub kind: ProgramGraphResolutionKind,
    pub containing_file: String,
    pub range: Option<TextRange>,
    pub specifier: String,
    /// `None` means the call used the resolver's default mode.
    pub mode: Option<ModuleFormat>,
}

/// A loaded target identified by path, without assuming file ID order.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ProgramGraphTarget {
    pub file_id: FileId,
    pub file_name: String,
    pub emit_module_mode: CanonicalModuleResolutionMode,
}

/// One resolver result, including failed lookups and ambient fallback.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ProgramGraphResolution {
    pub request: ProgramGraphResolutionRequest,
    /// Resolved file names are the resolver's terminal realpath results.
    pub result: ResolutionResult,
    /// An ambient declaration can satisfy a failed filesystem resolution.
    pub ambient_target: Option<String>,
    /// A resolved path can be absent here if the file could not be loaded.
    pub target: Option<ProgramGraphTarget>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ProgramGraphReferenceKind {
    Path,
    Library,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ProgramGraphReferenceTarget {
    pub file_name: String,
    pub file_id: Option<FileId>,
}

/// Path and library directives use loader operations, not module resolution.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ProgramGraphReference {
    pub containing_file: String,
    pub range: TextRange,
    pub specifier: String,
    pub kind: ProgramGraphReferenceKind,
    pub skipped: bool,
    pub targets: Vec<ProgramGraphReferenceTarget>,
}

/// Evidence the current loader does not retain for a complete graph comparison.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ProgramGraphMissingEvidence {
    /// The leaf config's VFS text was not retained.
    ConfigSourceText,
    /// The config resolver's parser inputs or read outcomes were not fully retained.
    ConfigParseInputs,
    /// Config inheritance probes, decisions, or inputs were not fully retained.
    ConfigExtendsInputs,
    /// A resolved module's original lookup path was not retained.
    ResolutionOriginalPaths,
    /// Root and path-reference loads do not record filesystem realpaths.
    SourceRealPaths,
    /// A resolver call did not retain its selected import/require condition.
    ResolutionDefaultModes,
    /// A package JSON path is not a name, version, or peer-dependency identity.
    PackageIdentities,
    /// The loader retains implied format, but not its package-scope inputs.
    SourcePackageScopes,
}

/// An owned snapshot, without filesystem reads or checker operations.
///
/// Roots retain input order and sources retain load order. Resolution records
/// retain resolver call order. This is not a claim of complete graph evidence.
#[derive(Clone, Debug, PartialEq)]
pub struct ProgramGraphSnapshot {
    pub current_directory: String,
    pub case_sensitivity: CaseSensitivity,
    pub roots: Vec<ProgramGraphRoot>,
    pub sources: Vec<ProgramGraphSource>,
    pub options: CompilerOptions,
    pub config_file_path: Option<String>,
    pub config: Option<ProgramGraphConfig>,
    /// Observations from the same config resolution, including failed loads.
    /// Read events retain VFS parser text, not raw disk bytes. Completeness
    /// describes event retention, not config validity or a complete Program.
    pub config_resolution_observation: Option<ConfigResolutionObservation>,
    pub resolution_options: Option<ResolutionOptions>,
    pub resolutions: Vec<ProgramGraphResolution>,
    pub references: Vec<ProgramGraphReference>,
    /// The same manifest builder used at canonical checker construction.
    pub module_resolution_manifest:
        Result<CanonicalModuleResolutionManifestInput, CanonicalProgramCheckError>,
    pub package_export_specifiers: BTreeMap<String, Vec<String>>,
    pub package_display_specifiers: BTreeMap<(FileId, String), String>,
    pub missing_evidence: Vec<ProgramGraphMissingEvidence>,
}

impl Program {
    /// Returns the original root names before normalization or deduplication.
    #[must_use]
    pub fn ordered_root_file_names(&self) -> &[String] {
        &self.ordered_root_file_names
    }

    /// Copies the loaded graph without reading files or changing checker state.
    #[must_use]
    pub fn project_graph_snapshot(&self) -> ProgramGraphSnapshot {
        let roots = self
            .ordered_root_file_names
            .iter()
            .map(|requested_name| {
                let file_name = if is_absolute(requested_name) {
                    normalize_path(requested_name)
                } else {
                    resolve_path(&self.current_directory, &[requested_name])
                };
                let file_id = self.source_file(&file_name).map(|source| source.id);
                ProgramGraphRoot {
                    requested_name: requested_name.clone(),
                    file_name,
                    file_id,
                }
            })
            .collect();
        let sources = self
            .source_files
            .iter()
            .map(|source| ProgramGraphSource {
                file_id: source.id,
                file_name: source.file_name.clone(),
                source_text: source.source_text.clone(),
                is_default_library: source.is_default_library,
                implied_node_format: source.implied_node_format,
                emit_module_mode: self.canonical_emit_module_mode(source),
            })
            .collect();
        let mut resolutions = self.graph_resolutions.clone();
        for resolution in &mut resolutions {
            resolution.target = resolution
                .result
                .resolved
                .as_ref()
                .map(|resolved| resolved.resolved_file_name.as_str())
                .or(resolution.ambient_target.as_deref())
                .and_then(|file_name| self.source_file(file_name))
                .map(|source| ProgramGraphTarget {
                    file_id: source.id,
                    file_name: source.file_name.clone(),
                    emit_module_mode: self.canonical_emit_module_mode(source),
                });
        }
        let mut references = self.graph_references.clone();
        for reference in &mut references {
            for target in &mut reference.targets {
                target.file_id = self.source_file(&target.file_name).map(|source| source.id);
            }
        }
        ProgramGraphSnapshot {
            current_directory: self.current_directory.clone(),
            case_sensitivity: self.case_sensitivity,
            roots,
            sources,
            options: self.options.clone(),
            config_file_path: self.config_file_path.clone(),
            config: self.graph_config.clone(),
            config_resolution_observation: self.graph_config_resolution_observation.clone(),
            resolution_options: self.graph_resolution_options.clone(),
            resolutions,
            references,
            module_resolution_manifest: self.canonical_module_resolution_manifest(),
            package_export_specifiers: self.package_export_specifiers.clone(),
            package_display_specifiers: self.package_display_specifiers.clone(),
            missing_evidence: self.project_graph_missing_evidence(),
        }
    }

    pub(super) fn record_graph_resolution(
        &mut self,
        request: ProgramGraphResolutionRequest,
        result: &ResolutionResult,
        ambient_target: Option<&str>,
    ) {
        self.graph_resolutions.push(ProgramGraphResolution {
            request,
            result: result.clone(),
            ambient_target: ambient_target.map(str::to_owned),
            target: None,
        });
    }

    fn project_graph_missing_evidence(&self) -> Vec<ProgramGraphMissingEvidence> {
        let mut missing = Vec::new();
        if let Some(config_path) = &self.config_file_path {
            let later_text_retained = self
                .graph_config
                .as_ref()
                .is_some_and(|config| config.source_text.is_some());
            let parser_text_retained = self
                .graph_config_resolution_observation
                .as_ref()
                .is_some_and(|observation| {
                    observation.events.iter().any(|event| {
                        matches!(
                            event,
                            ConfigResolutionEvent::ReadFile {
                                path,
                                kind: ConfigInputKind::Config,
                                result: Ok(_),
                            } if path == config_path
                        )
                    })
                });
            if !later_text_retained && !parser_text_retained {
                missing.push(ProgramGraphMissingEvidence::ConfigSourceText);
            }
            if self
                .graph_config_resolution_observation
                .as_ref()
                .is_none_or(|observation| !observation.is_complete())
            {
                missing.push(ProgramGraphMissingEvidence::ConfigParseInputs);
                missing.push(ProgramGraphMissingEvidence::ConfigExtendsInputs);
            }
        }
        if self
            .graph_resolutions
            .iter()
            .any(|resolution| resolution.result.effective_mode.is_none())
        {
            missing.push(ProgramGraphMissingEvidence::ResolutionDefaultModes);
        }
        if self
            .source_files
            .iter()
            .any(|source| !source.is_default_library)
        {
            missing.push(ProgramGraphMissingEvidence::SourceRealPaths);
            missing.push(ProgramGraphMissingEvidence::PackageIdentities);
            missing.push(ProgramGraphMissingEvidence::SourcePackageScopes);
        }
        missing
    }
}

#[cfg(test)]
mod tests {
    use ts_config::{ConfigObservationLimits, resolve_config_file_with_observation};
    use ts_module::{ModuleFormat, ResolutionResult};
    use ts_vfs::{FileSystem, MemoryFileSystem};

    use super::{
        Program, ProgramGraphMissingEvidence, ProgramGraphResolutionKind,
        ProgramGraphResolutionRequest,
    };

    #[test]
    fn config_evidence_gaps_follow_observation_retention() {
        let filesystem = MemoryFileSystem::new(true);
        let path = "/project/tsconfig.json";
        filesystem
            .write_file(
                path,
                r#"{"files":[],"compilerOptions":{"noCheck":true,"noEmit":true,"noLib":true}}"#,
            )
            .unwrap();
        let mut program = Program::from_config(&filesystem, path);
        let complete = program.graph_config_resolution_observation.clone().unwrap();
        let limited = resolve_config_file_with_observation(
            &filesystem,
            path,
            ConfigObservationLimits {
                max_events: 1,
                max_string_bytes: usize::MAX,
            },
        );
        assert!(!limited.observation.is_complete());
        program.graph_config_resolution_observation = Some(limited.observation);
        let missing = program.project_graph_missing_evidence();
        assert!(missing.contains(&ProgramGraphMissingEvidence::ConfigParseInputs));
        assert!(missing.contains(&ProgramGraphMissingEvidence::ConfigExtendsInputs));
        assert!(!missing.contains(&ProgramGraphMissingEvidence::ConfigSourceText));

        program.graph_config.as_mut().unwrap().source_text = None;
        assert!(
            program
                .project_graph_missing_evidence()
                .contains(&ProgramGraphMissingEvidence::ConfigSourceText)
        );
        program.graph_config_resolution_observation = Some(complete);
        assert!(
            !program
                .project_graph_missing_evidence()
                .contains(&ProgramGraphMissingEvidence::ConfigSourceText)
        );
        assert!(
            !program
                .project_graph_missing_evidence()
                .contains(&ProgramGraphMissingEvidence::ConfigParseInputs)
        );
        assert!(
            !program
                .project_graph_missing_evidence()
                .contains(&ProgramGraphMissingEvidence::ConfigExtendsInputs)
        );
    }

    #[test]
    fn resolution_evidence_requires_an_observed_effective_mode() {
        let mut program = Program::default();
        program.record_graph_resolution(
            ProgramGraphResolutionRequest {
                kind: ProgramGraphResolutionKind::Module,
                containing_file: "/project/main.ts".to_owned(),
                range: None,
                specifier: "pkg".to_owned(),
                mode: Some(ModuleFormat::Esm),
            },
            &ResolutionResult::default(),
            None,
        );
        assert!(
            program
                .project_graph_missing_evidence()
                .contains(&ProgramGraphMissingEvidence::ResolutionDefaultModes)
        );
        program.graph_resolutions[0].request.mode = None;
        program.graph_resolutions[0].result.effective_mode = Some(ModuleFormat::CommonJs);
        assert!(
            !program
                .project_graph_missing_evidence()
                .contains(&ProgramGraphMissingEvidence::ResolutionDefaultModes)
        );
    }
}
