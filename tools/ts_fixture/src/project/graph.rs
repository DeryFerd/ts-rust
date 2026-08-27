use serde::Serialize;
use serde_json::{Value, json};
use ts_ast::NodeRef;
use ts_checker::semantic::{CanonicalModuleResolutionInput, CanonicalModuleResolutionMode};
use ts_compiler::{
    CanonicalProgramCheckError, Program, ProgramGraphMissingEvidence,
    ProgramGraphPackageScopeDecision, ProgramGraphPackageScopeEvent,
    ProgramGraphPackageScopeObservation, ProgramGraphReferenceKind, ProgramGraphResolutionKind,
    ProgramGraphSnapshot,
};
use ts_config::{ConfigInputKind, ConfigResolutionEvent, ConfigResolutionObservation};
use ts_module::{
    FailedLookupKind, ModuleFormat, PackageJsonInputEvent, PackageJsonInputPurpose,
    PackageJsonInputs, ResolutionMode,
};
use ts_options::ModuleResolutionKind;

use super::{
    ProjectStage,
    options::{module_name, normalized_options},
};
use crate::{SCORECARD_DIGEST_ALGORITHM, stable_digest};

#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct ProjectGraphReport {
    /// Owns paths, input digests, options, references, and resolution results.
    pub evidence: Value,
    pub module_resolution_manifest: ProjectStage<Vec<Value>>,
    pub missing_evidence: Vec<String>,
    /// This hashes observed evidence only. Missing evidence remains missing.
    pub digest: String,
    pub digest_algorithm: &'static str,
}

pub(super) fn path_identity(path: &str) -> String {
    path.strip_prefix("/__typescript/lib/")
        .or_else(|| path.strip_prefix("bundled:///libs/"))
        .map_or_else(
            || path.to_owned(),
            |name| format!("typescript-lib:///{name}"),
        )
}

const fn mode_name(mode: CanonicalModuleResolutionMode) -> &'static str {
    match mode {
        CanonicalModuleResolutionMode::None => "none",
        CanonicalModuleResolutionMode::CommonJs => "commonjs",
        CanonicalModuleResolutionMode::Esm => "esm",
    }
}

const fn format_name(mode: ModuleFormat) -> &'static str {
    match mode {
        ModuleFormat::CommonJs => "commonjs",
        ModuleFormat::Esm => "esm",
    }
}

fn parser_input_text_report(text: &str) -> Value {
    json!({
        "status": "read",
        "parserInputText": text,
        "parserInputTextUtf8ByteCount": text.len(),
        "parserInputTextDigest": stable_digest(text.as_bytes()),
        "digestAlgorithm": SCORECARD_DIGEST_ALGORITHM,
    })
}

fn config_observation_report(observation: &ConfigResolutionObservation) -> Value {
    let events = observation
        .events
        .iter()
        .map(|event| match event {
            ConfigResolutionEvent::FileExists { path, exists } => json!({
                "kind": "file_exists",
                "path": path_identity(path),
                "exists": exists,
            }),
            ConfigResolutionEvent::DirectoryExists { path, exists } => json!({
                "kind": "directory_exists",
                "path": path_identity(path),
                "exists": exists,
            }),
            ConfigResolutionEvent::ReadFile { path, kind, result } => {
                let result = match result {
                    Ok(text) => parser_input_text_report(text),
                    Err(error) => json!({
                        "status": "error",
                        "errorKind": format!("{:?}", error.kind),
                        "message": error.message,
                    }),
                };
                json!({
                    "kind": "read_file",
                    "path": path_identity(path),
                    "inputKind": match kind {
                        ConfigInputKind::Config => "config",
                        ConfigInputKind::PackageJson => "package_json",
                    },
                    "result": result,
                })
            }
            ConfigResolutionEvent::Extends {
                config_path,
                specifier,
                resolved_path,
            } => json!({
                "kind": "extends",
                "configPath": path_identity(config_path),
                "specifier": specifier,
                "resolvedPath": resolved_path.as_deref().map(path_identity),
            }),
            ConfigResolutionEvent::Cycle { path, chain } => json!({
                "kind": "cycle",
                "path": path_identity(path),
                "chain": chain.iter().map(|path| path_identity(path)).collect::<Vec<_>>(),
            }),
        })
        .collect::<Vec<_>>();
    json!({
        "retentionComplete": observation.is_complete(),
        "omittedEvents": observation.omitted_events,
        "textRepresentation": "vfs_parser_input",
        "events": events,
    })
}

// Cache hits retain the original worker's inputs, not a new set of reads.
fn package_json_inputs_report(inputs: Option<&PackageJsonInputs>) -> Value {
    let Some(inputs) = inputs else {
        return Value::Null;
    };
    let events = inputs
        .events
        .iter()
        .map(|event| match event {
            PackageJsonInputEvent::FileExists { path, exists } => json!({
                "kind": "file_exists",
                "path": path_identity(path),
                "exists": exists,
            }),
            PackageJsonInputEvent::ReadFile {
                path,
                purpose,
                result,
            } => {
                let result = match result {
                    Ok(text) => parser_input_text_report(text),
                    Err(error) => json!({
                        "status": "error",
                        "errorKind": format!("{:?}", error.kind),
                        "message": error.message,
                    }),
                };
                json!({
                    "kind": "read_file",
                    "path": path_identity(path),
                    "purpose": match purpose {
                        PackageJsonInputPurpose::DefaultMode => "default_mode",
                        PackageJsonInputPurpose::PackageResolution => "package_resolution",
                    },
                    "result": result,
                })
            }
        })
        .collect::<Vec<_>>();
    json!({
        "inputOrigin": "resolver_worker",
        "retentionComplete": inputs.is_complete(),
        "omittedEvents": inputs.omitted_events,
        "textRepresentation": "vfs_parser_input",
        "events": events,
    })
}

fn source_package_scope_observation_report(
    program: &Program,
    observation: &ProgramGraphPackageScopeObservation,
) -> Value {
    let events = observation
        .events
        .iter()
        .map(|event| {
            let (file_id, mut report) = match event {
                ProgramGraphPackageScopeEvent::FileExists {
                    file_id,
                    path,
                    exists,
                } => (
                    file_id,
                    json!({"kind": "file_exists", "path": path_identity(path), "exists": exists}),
                ),
                ProgramGraphPackageScopeEvent::ReadFile {
                    file_id,
                    path,
                    result,
                } => {
                    let result = match result {
                        Ok(text) => parser_input_text_report(text),
                        Err(error) => json!({
                            "status": "error",
                            "errorKind": format!("{:?}", error.kind),
                            "message": error.message,
                        }),
                    };
                    (
                        file_id,
                        json!({"kind": "read_file", "path": path_identity(path), "result": result}),
                    )
                }
                ProgramGraphPackageScopeEvent::Decision {
                    file_id,
                    implied_node_format,
                    reason,
                } => (
                    file_id,
                    json!({
                        "kind": "decision",
                        "impliedNodeFormat": module_name(*implied_node_format),
                        "reason": match reason {
                            ProgramGraphPackageScopeDecision::FixedExtension => "fixed_extension",
                            ProgramGraphPackageScopeDecision::PackageJson => "package_json",
                            ProgramGraphPackageScopeDecision::InvalidPackageJson => "invalid_package_json",
                            ProgramGraphPackageScopeDecision::ReadFailure => "read_failure",
                            ProgramGraphPackageScopeDecision::NoPackage => "no_package",
                        },
                    }),
                ),
            };
            let source = program
                .source_file_by_id(*file_id)
                .expect("the retained package-scope source belongs to this Program");
            report["sourceFile"] = json!(path_identity(&source.file_name));
            report
        })
        .collect::<Vec<_>>();
    json!({
        "retentionComplete": observation.is_complete(),
        "omittedEvents": observation.omitted_events,
        "textRepresentation": "vfs_parser_input",
        "events": events,
    })
}

fn missing_evidence_report(graph: &ProgramGraphSnapshot) -> Vec<String> {
    let mut missing = graph
        .missing_evidence
        .iter()
        .map(|missing| {
            match missing {
                ProgramGraphMissingEvidence::ConfigSourceText => "config_source_text",
                ProgramGraphMissingEvidence::ConfigParseInputs => "config_parse_inputs",
                ProgramGraphMissingEvidence::ConfigExtendsInputs => "config_extends_inputs",
                ProgramGraphMissingEvidence::SourceRealPaths => "source_real_paths",
                ProgramGraphMissingEvidence::ResolutionOriginalPaths => "resolution_original_paths",
                ProgramGraphMissingEvidence::ResolutionDefaultModes => "resolution_default_modes",
                ProgramGraphMissingEvidence::PackageIdentities => "package_identities",
                ProgramGraphMissingEvidence::SourcePackageScopes => "source_package_scopes",
            }
            .to_owned()
        })
        .collect::<Vec<_>>();
    if graph.resolutions.iter().any(|resolution| {
        resolution
            .result
            .package_json_inputs
            .as_ref()
            .is_none_or(|inputs| !inputs.is_complete())
    }) {
        missing.push("resolution_package_json_inputs".to_owned());
    }
    if !graph.options.skips_type_checking(true, true)
        && graph.sources.iter().any(|source| source.is_default_library)
    {
        missing.push("default_library_semantic_diagnostics".to_owned());
    }
    missing
}

fn manifest_node_location(program: &Program, reference: NodeRef) -> Value {
    let source = program
        .source_file_by_id(reference.file)
        .filter(|source| reference.is_for(source.parse.arena.id(), source.id));
    let node = source.and_then(|_| program.node(reference));
    json!({
        "containingFile": source.map(|source| path_identity(&source.file_name)),
        "range": node.map(|node| json!({
            "startByte": node.range.start.get(),
            "endByte": node.range.end.get(),
        })),
    })
}

#[allow(clippy::too_many_lines)] // Each manifest error retains its typed fields without raw IDs.
fn manifest_failure(
    program: &Program,
    error: &CanonicalProgramCheckError,
) -> ProjectStage<Vec<Value>> {
    let detail = match error {
        CanonicalProgramCheckError::ModuleSpecifierResolutionModeUnsupported(node) => json!({
            "kind": "module_specifier_resolution_mode_unsupported",
            "location": manifest_node_location(program, *node),
        }),
        CanonicalProgramCheckError::InvalidModuleSourceFile(node) => json!({
            "kind": "invalid_module_source_file",
            "location": manifest_node_location(program, *node),
        }),
        CanonicalProgramCheckError::InvalidModuleSpecifier(node) => json!({
            "kind": "invalid_module_specifier",
            "location": manifest_node_location(program, *node),
        }),
        CanonicalProgramCheckError::ExternalModuleTargetUnsupported {
            specifier,
            target_file_name,
        } => json!({
            "kind": "external_module_target_unsupported",
            "location": manifest_node_location(program, *specifier),
            "targetFile": path_identity(target_file_name),
        }),
        CanonicalProgramCheckError::OmittedModuleTargetUnsupported {
            specifier,
            target_file_name,
            reason,
        } => json!({
            "kind": "omitted_module_target_unsupported",
            "location": manifest_node_location(program, *specifier),
            "targetFile": path_identity(target_file_name),
            "reason": match reason {
                ts_compiler::CanonicalModuleTargetOmission::NoResolve => json!({"kind": "no_resolve"}),
                ts_compiler::CanonicalModuleTargetOmission::JavaScriptDisabled => json!({"kind": "javascript_disabled"}),
                ts_compiler::CanonicalModuleTargetOmission::NodeModuleJavaScriptDepth { depth, limit } => json!({
                    "kind": "node_module_javascript_depth", "depth": depth, "limit": limit,
                }),
            },
        }),
        CanonicalProgramCheckError::MissingResolvedModuleTarget {
            containing_file,
            specifier,
            resolved_file_name,
        } => json!({
            "kind": "missing_resolved_module_target",
            "containingFile": path_identity(containing_file),
            "location": manifest_node_location(program, *specifier),
            "targetFile": path_identity(resolved_file_name),
        }),
        CanonicalProgramCheckError::PlainEsmModuleResolutionUnsupported {
            file_name,
            module,
            module_resolution,
        } => json!({
            "kind": "plain_esm_module_resolution_unsupported",
            "fileName": path_identity(file_name),
            "module": module_name(*module),
            "moduleResolution": match module_resolution {
                ModuleResolutionKind::Classic => "classic",
                ModuleResolutionKind::Node10 => "node10",
                ModuleResolutionKind::Node16 => "node16",
                ModuleResolutionKind::NodeNext => "nodenext",
                ModuleResolutionKind::Bundler => "bundler",
            },
        }),
        CanonicalProgramCheckError::UnsupportedSourceKind {
            file_name,
            script_kind,
        } => json!({
            "kind": "unsupported_source_kind",
            "fileName": path_identity(file_name),
            "scriptKind": match script_kind {
                ts_path::ScriptKind::Unknown => "unknown",
                ts_path::ScriptKind::Js => "js",
                ts_path::ScriptKind::Jsx => "jsx",
                ts_path::ScriptKind::Ts => "ts",
                ts_path::ScriptKind::Tsx => "tsx",
                ts_path::ScriptKind::External => "external",
                ts_path::ScriptKind::Json => "json",
                ts_path::ScriptKind::Deferred => "deferred",
            },
        }),
        CanonicalProgramCheckError::ImportMetaModuleIndicatorUnsupported { file_name } => json!({
            "kind": "import_meta_module_indicator_unsupported",
            "fileName": path_identity(file_name),
        }),
        CanonicalProgramCheckError::FixedModuleFormatUnsupported { .. }
        | CanonicalProgramCheckError::NodeModuleFactsUnsupported { .. }
        | CanonicalProgramCheckError::DeclarationFileCheckingUnsupported { .. }
        | CanonicalProgramCheckError::ProjectReferencesUnsupported { .. }
        | CanonicalProgramCheckError::Bind { .. }
        | CanonicalProgramCheckError::DeclarationBind { .. }
        | CanonicalProgramCheckError::Context(_)
        | CanonicalProgramCheckError::SourceCheck { .. }
        | CanonicalProgramCheckError::ImportHelper { .. }
        | CanonicalProgramCheckError::MissingBoundFile { .. }
        | CanonicalProgramCheckError::InvalidDiagnosticNode(_)
        | CanonicalProgramCheckError::InvalidDiagnosticRange { .. }
        | CanonicalProgramCheckError::InvalidRelatedDiagnosticNode { .. }
        | CanonicalProgramCheckError::DiagnosticFormat(_) => {
            return ProjectStage::Invariant {
                code: "INV.PROJECT.MANIFEST_FAILURE_KIND".to_owned(),
                detail: json!({
                    "kind": "unhandled_manifest_failure",
                    "compilerFailureCode": error.failure_class().code(),
                })
                .to_string(),
            };
        }
    };
    ProjectStage::failure(error.failure_class(), detail.to_string())
}

#[allow(clippy::too_many_lines)] // The report retains each graph field without debug serialization.
pub(super) fn snapshot_report(program: &Program) -> ProjectGraphReport {
    let graph = program.project_graph_snapshot();
    let roots = graph
        .roots
        .iter()
        .map(|root| {
            json!({
                "requestedName": root.requested_name,
                "fileName": path_identity(&root.file_name),
                "loaded": root.file_id.is_some(),
            })
        })
        .collect::<Vec<_>>();
    let sources = graph
        .sources
        .iter()
        .map(|source| {
            json!({
                "fileName": path_identity(&source.file_name),
                "byteCount": source.source_text.len(),
                "digest": stable_digest(source.source_text.as_bytes()),
                "defaultLibrary": source.is_default_library,
                "declarationFile": ts_path::is_declaration_file(&source.file_name),
                "impliedNodeFormat": module_name(source.implied_node_format),
                "emitModuleMode": mode_name(source.emit_module_mode),
            })
        })
        .collect::<Vec<_>>();
    let resolutions = graph.resolutions.iter().map(|resolution| {
        let request = &resolution.request;
        let resolved = resolution.result.resolved.as_ref().map(|target| json!({
            "fileName": path_identity(&target.resolved_file_name),
            "originalFileName": path_identity(&target.original_file_name),
            "extension": target.extension.map(ts_path::FileExtension::as_str),
            "resolvedUsingTsExtension": target.resolved_using_ts_extension,
            "externalLibraryImport": target.is_external_library_import,
            "packageJson": target.package_json.as_deref().map(path_identity),
        }));
        let target = resolution.target.as_ref().map(|target| json!({
            "fileName": path_identity(&target.file_name),
            "emitModuleMode": mode_name(target.emit_module_mode),
        }));
        let failed = resolution.result.failed_lookups.iter().map(|lookup| json!({
            "kind": match lookup.kind {
                FailedLookupKind::File => "file",
                FailedLookupKind::Directory => "directory",
                FailedLookupKind::PackageJson => "package_json",
            },
            "path": path_identity(&lookup.path),
        })).collect::<Vec<_>>();
        json!({
            "kind": match request.kind {
                ProgramGraphResolutionKind::Module => "module",
                ProgramGraphResolutionKind::JsxRuntime => "jsx_runtime",
                ProgramGraphResolutionKind::ImportHelpers => "import_helpers",
                ProgramGraphResolutionKind::AutomaticTypeDirective => "automatic_type_directive",
                ProgramGraphResolutionKind::TypeReference => "type_reference",
            },
            "containingFile": path_identity(&request.containing_file),
            "range": request.range.map(|range| json!({"startByte": range.start.get(), "endByte": range.end.get()})),
            "specifier": request.specifier,
            "mode": request.mode.map(format_name),
            "effectiveMode": resolution.result.effective_mode.map(format_name),
            "resolved": resolved,
            "ambientTarget": resolution.ambient_target.as_deref().map(path_identity),
            "loadedTarget": target,
            "failedLookups": failed,
            "packageJsonInputs": package_json_inputs_report(resolution.result.package_json_inputs.as_ref()),
        })
    }).collect::<Vec<_>>();
    let references = graph.references.iter().map(|reference| json!({
        "containingFile": path_identity(&reference.containing_file),
        "range": {"startByte": reference.range.start.get(), "endByte": reference.range.end.get()},
        "specifier": reference.specifier,
        "kind": match reference.kind {
            ProgramGraphReferenceKind::Path => "path",
            ProgramGraphReferenceKind::Library => "library",
        },
        "skipped": reference.skipped,
        "targets": reference.targets.iter().map(|target| json!({
            "fileName": path_identity(&target.file_name),
            "loaded": target.file_id.is_some(),
        })).collect::<Vec<_>>(),
    })).collect::<Vec<_>>();
    let resolution_options = graph.resolution_options.as_ref().map(|options| {
        json!({
            "mode": match options.mode {
                ResolutionMode::Classic => "classic", ResolutionMode::Node10 => "node10",
                ResolutionMode::Node16 => "node16", ResolutionMode::NodeNext => "nodenext",
                ResolutionMode::Bundler => "bundler",
            },
            "allowArbitraryExtensions": options.allow_arbitrary_extensions,
            "allowJavascript": options.allow_javascript,
            "resolveJson": options.resolve_json,
            "resolvePackageJsonExports": options.resolve_package_json_exports,
            "resolvePackageJsonImports": options.resolve_package_json_imports,
            "preferTypes": options.prefer_types,
            "preserveSymlinks": options.preserve_symlinks,
            "customConditions": options.custom_conditions,
            "moduleSuffixes": options.module_suffixes,
            "baseUrl": options.base_url,
            "paths": options.paths,
            "rootDirs": options.root_dirs,
            "typeRoots": options.type_roots,
            "types": options.types,
        })
    });
    let config = graph.config.as_ref().map(|config| json!({
        "fileName": graph.config_file_path,
        "diagnosticSourceTextDigest": config.source_text.as_deref().map(|text| stable_digest(text.as_bytes())),
        "diagnosticSourceTextUtf8ByteCount": config.source_text.as_ref().map(String::len),
        "resolvedPath": config.resolved.path,
        "resolvedFiles": config.resolved.files,
        "resolvedInclude": config.resolved.include,
        "resolvedExclude": config.resolved.exclude,
        "extends": config.resolved.extends.as_ref().map(|extends| extends.paths().collect::<Vec<_>>()),
        "references": config.resolved.references.iter().map(|reference| json!({
            "path": reference.path, "prepend": reference.prepend, "circular": reference.circular,
        })).collect::<Vec<_>>(),
    }));
    let ordered_artifact_files =
        super::ordered_project_sources(program, program.ordered_root_file_names())
            .iter()
            .map(|source| path_identity(&source.file_name))
            .collect::<Vec<_>>();
    let mut package_display_choices = graph
        .package_display_specifiers
        .iter()
        .map(|((enclosing, target), specifier)| {
            let source = program
                .source_file_by_id(*enclosing)
                .expect("the retained package display location belongs to this Program");
            (
                path_identity(&source.file_name),
                path_identity(target),
                specifier.as_str(),
            )
        })
        .collect::<Vec<_>>();
    package_display_choices.sort_unstable();
    let package_display_specifiers = package_display_choices
        .iter()
        .map(|(enclosing, target, specifier)| {
            json!({
                "enclosingFile": enclosing,
                "targetFile": target,
                "specifier": specifier,
            })
        })
        .collect::<Vec<_>>();
    let evidence = json!({
        "currentDirectory": graph.current_directory,
        "caseSensitive": graph.case_sensitivity == ts_path::CaseSensitivity::Sensitive,
        "roots": roots,
        "sources": sources,
        "options": normalized_options(&graph.options),
        "configFilePath": graph.config_file_path,
        "config": config,
        "configResolutionObservation": graph.config_resolution_observation.as_ref().map(config_observation_report),
        "sourcePackageScopeObservation": source_package_scope_observation_report(program, &graph.source_package_scope_observation),
        "resolutionOptions": resolution_options,
        "resolutions": resolutions,
        "references": references,
        "packageExportSpecifiers": graph.package_export_specifiers,
        "packageDisplaySpecifiers": package_display_specifiers,
        "artifactFileOrder": ordered_artifact_files,
    });
    let module_resolution_manifest = match &graph.module_resolution_manifest {
        Err(error) => manifest_failure(program, error),
        Ok(manifest) => {
            let entries = manifest.entries().iter().map(|entry| {
                let specifier = entry.specifier();
                let source = program.source_file_by_id(specifier.file)?;
                let node = program.node(specifier)?;
                let resolution = match entry.resolution() {
                    CanonicalModuleResolutionInput::Unresolved => json!({"status": "unresolved"}),
                    CanonicalModuleResolutionInput::Resolved(target) => {
                        let target_source = program.source_file_by_id(target.target_file())?;
                        json!({
                            "status": "resolved",
                            "fileName": path_identity(&target_source.file_name),
                            "usageMode": mode_name(target.usage_mode()),
                            "targetMode": mode_name(target.target_mode()),
                        })
                    }
                };
                Some(json!({
                    "containingFile": path_identity(&source.file_name),
                    "range": {"startByte": node.range.start.get(), "endByte": node.range.end.get()},
                    "resolution": resolution,
                }))
            }).collect::<Option<Vec<_>>>();
            entries.map_or_else(
                || ProjectStage::Invariant {
                    code: "INV.PROJECT.MANIFEST_NODE".to_owned(),
                    detail: "The project manifest refers to a missing source, node, or target."
                        .to_owned(),
                },
                |value| ProjectStage::Complete { value },
            )
        }
    };
    let missing_evidence = missing_evidence_report(&graph);
    let bytes = serde_json::to_vec(&(&evidence, &module_resolution_manifest, &missing_evidence))
        .expect("graph evidence contains only JSON values");
    ProjectGraphReport {
        evidence,
        module_resolution_manifest,
        missing_evidence,
        digest: stable_digest(&bytes),
        digest_algorithm: SCORECARD_DIGEST_ALGORITHM,
    }
}

#[cfg(test)]
mod input_evidence_tests;

#[cfg(test)]
mod tests {
    use std::io;

    use serde_json::{Value, json};
    use ts_compiler::Program;
    use ts_config::{
        ConfigInputKind, ConfigReadError, ConfigResolutionEvent, ConfigResolutionObservation,
    };
    use ts_options::{CompilerOptions, ModuleKind, ModuleResolutionKind};
    use ts_vfs::{FileSystem, MemoryFileSystem};

    use super::{ProjectStage, config_observation_report, snapshot_report};
    use crate::{SCORECARD_DIGEST_ALGORITHM, stable_digest};

    fn graph_options() -> CompilerOptions {
        CompilerOptions {
            no_check: true,
            no_emit: true,
            no_lib: true,
            module: ModuleKind::EsNext,
            module_resolution: ModuleResolutionKind::Bundler,
            ..CompilerOptions::default()
        }
    }

    #[test]
    fn graph_report_tracks_alias_choices_without_source_or_import_changes() {
        let filesystem = MemoryFileSystem::new(true);
        filesystem
            .write_file(
                "/shared/package.json",
                r#"{"name":"real-package","exports":{".":"./index.js"}}"#,
            )
            .unwrap();
        filesystem
            .write_file(
                "/shared/index.d.ts",
                "export interface Item { value: number; }",
            )
            .unwrap();
        for (directory, alias) in [("/one", "alias-one"), ("/two", "alias-two")] {
            filesystem.add_directory_link("/shared", &format!("{directory}/node_modules/{alias}"));
            filesystem
                .write_file(
                    &format!("{directory}/bridge.d.ts"),
                    &format!("export type {{ Item }} from '{alias}';"),
                )
                .unwrap();
            filesystem
                .write_file(
                    &format!("{directory}/use.ts"),
                    "import {} from './bridge'; export {};",
                )
                .unwrap();
        }
        filesystem
            .write_file(
                "/outside/use.ts",
                "import {} from '../one/bridge'; export {};",
            )
            .unwrap();
        let roots = ["/one/use.ts", "/two/use.ts", "/outside/use.ts"].map(str::to_owned);
        let build = || Program::new_with_options(&filesystem, "/", &roots, graph_options());
        let before = snapshot_report(&build());
        let choice = |enclosing: &str, specifier: &str| {
            json!({
                "enclosingFile": enclosing,
                "targetFile": "/shared/index.d.ts",
                "specifier": specifier,
            })
        };
        let mut expected = vec![
            choice("/one/bridge.d.ts", "alias-one"),
            choice("/one/use.ts", "alias-one"),
            choice("/two/bridge.d.ts", "alias-two"),
            choice("/two/use.ts", "alias-two"),
        ];
        assert_eq!(before.evidence["packageDisplaySpecifiers"], json!(expected));

        filesystem.add_directory_link("/shared", "/outside/node_modules/alias-one");
        let after = snapshot_report(&build());
        expected.insert(2, choice("/outside/use.ts", "alias-one"));
        assert_eq!(after.evidence["packageDisplaySpecifiers"], json!(expected));
        let mut previous_evidence = before.evidence.clone();
        previous_evidence["packageDisplaySpecifiers"] = json!(expected);
        assert_eq!(previous_evidence, after.evidence);
        assert_eq!(
            before.module_resolution_manifest,
            after.module_resolution_manifest
        );
        assert_eq!(before.missing_evidence, after.missing_evidence);
        assert_ne!(before.digest, after.digest);
        assert_eq!(after, snapshot_report(&build()));
    }

    #[test]
    fn graph_report_manifest_failures_are_stable_across_rebuilt_programs() {
        let filesystem = MemoryFileSystem::new(true);
        filesystem
            .write_file("/project/script.ts", "const value = 1;")
            .unwrap();
        for (text, expected_code, expected_kind, target) in [
            (
                "import { value } from './script';",
                "M00.EXTERNAL_MODULE_TARGET",
                "external_module_target_unsupported",
                Some("/project/script.ts"),
            ),
            (
                "import type { value } from './script' with { 'resolution-mode': 'invalid' };",
                "M00.SPECIFIER_RESOLUTION_MODE",
                "module_specifier_resolution_mode_unsupported",
                None,
            ),
        ] {
            filesystem.write_file("/project/main.ts", text).unwrap();
            let roots = ["/project/main.ts".to_owned()];
            let first = Program::new_with_options(&filesystem, "/", &roots, graph_options());
            let second = Program::new_with_options(&filesystem, "/", &roots, graph_options());
            assert!(first.options().no_check);
            assert_ne!(
                first.project_graph_snapshot().module_resolution_manifest,
                second.project_graph_snapshot().module_resolution_manifest,
            );
            let first_report = snapshot_report(&first);
            let second_report = snapshot_report(&second);
            assert_eq!(first_report, second_report);

            let ProjectStage::Unsupported { code, detail } =
                &first_report.module_resolution_manifest
            else {
                panic!("expected an unsupported manifest: {first_report:?}");
            };
            assert_eq!(code, expected_code);
            let start = text.find("'./script'").unwrap();
            let mut expected = json!({
                "kind": expected_kind,
                "location": {
                    "containingFile": "/project/main.ts",
                    "range": {"startByte": start, "endByte": start + "'./script'".len()},
                },
            });
            if let Some(target) = target {
                expected["targetFile"] = json!(target);
            }
            assert_eq!(serde_json::from_str::<Value>(detail).unwrap(), expected);
        }
    }

    #[test]
    fn manifest_import_helper_errors_remain_unexpected_failures() {
        use ts_ast::NodeRef;
        use ts_checker::semantic::{
            CanonicalModuleExportQueryError, alias::CanonicalAliasTargetUnavailable,
        };
        use ts_compiler::{CanonicalImportHelperError, CanonicalProgramCheckError};

        let filesystem = MemoryFileSystem::new(true);
        filesystem
            .write_file("/project/main.ts", "export {};")
            .unwrap();
        let program = Program::new_with_options(
            &filesystem,
            "/project",
            &["main.ts".to_owned()],
            graph_options(),
        );
        let source = &program.source_files()[0];
        let node = NodeRef::new(source.parse.arena.id(), source.id, source.parse.source_file);
        for (helper, compiler_code) in [
            (
                CanonicalImportHelperError::ModuleSymbolUnavailable {
                    file_name: "/project/node_modules/tslib/index.d.ts".to_owned(),
                },
                "M00.IMPORT_HELPER_MODULE",
            ),
            (
                CanonicalImportHelperError::Export(CanonicalModuleExportQueryError::Target(
                    CanonicalAliasTargetUnavailable::MalformedDeclaration(node),
                )),
                "INV.PROGRAM.IMPORT_HELPER",
            ),
        ] {
            let error = CanonicalProgramCheckError::ImportHelper {
                file_name: source.file_name.clone(),
                node,
                error: Box::new(helper),
            };
            assert_eq!(error.failure_class().code(), compiler_code);
            assert_eq!(
                super::manifest_failure(&program, &error),
                ProjectStage::Invariant {
                    code: "INV.PROJECT.MANIFEST_FAILURE_KIND".to_owned(),
                    detail: json!({
                        "kind": "unhandled_manifest_failure",
                        "compilerFailureCode": compiler_code,
                    })
                    .to_string(),
                },
            );
        }
    }

    #[test]
    fn graph_report_retains_ordered_config_inputs_and_inheritance_outcomes() {
        let filesystem = MemoryFileSystem::new(true);
        let leaf = "{\r\n\"extends\":[\"preset\",\"./missing\"],\"files\":[\"main.ts\"],\"compilerOptions\":{\"noCheck\":true,\"noEmit\":true,\"noLib\":true}}\r\n";
        let package = r#"{"tsconfig":"configs/base"}"#;
        let base = r#"{"extends":"../../../tsconfig.json","compilerOptions":{"strict":true}}"#;
        for (path, text) in [
            ("/project/tsconfig.json", leaf),
            ("/project/node_modules/preset/package.json", package),
            ("/project/node_modules/preset/configs/base.json", base),
            ("/project/main.ts", "const value = 1;"),
        ] {
            filesystem.write_file(path, text).unwrap();
        }
        let program = Program::from_config(&filesystem, "/project/tsconfig.json");
        assert!(!program.diagnostics().is_empty());
        let graph = snapshot_report(&program);
        let observation = &graph.evidence["configResolutionObservation"];
        assert_eq!(observation["retentionComplete"], true);
        assert_eq!(observation["omittedEvents"], 0);
        assert_eq!(observation["textRepresentation"], "vfs_parser_input");
        let events = observation["events"].as_array().unwrap();
        let reads = events
            .iter()
            .filter(|event| event["kind"] == "read_file")
            .collect::<Vec<_>>();
        for (read, path, kind, text) in [
            (reads[0], "/project/tsconfig.json", "config", leaf),
            (
                reads[1],
                "/project/node_modules/preset/package.json",
                "package_json",
                package,
            ),
            (
                reads[2],
                "/project/node_modules/preset/configs/base.json",
                "config",
                base,
            ),
        ] {
            assert_eq!(read["path"], path);
            assert_eq!(read["inputKind"], kind);
            assert_eq!(
                read["result"],
                json!({
                    "status": "read",
                    "parserInputText": text,
                    "parserInputTextUtf8ByteCount": text.len(),
                    "parserInputTextDigest": stable_digest(text.as_bytes()),
                    "digestAlgorithm": SCORECARD_DIGEST_ALGORITHM,
                })
            );
        }
        assert!(
            events
                .iter()
                .any(|event| event["kind"] == "directory_exists")
        );
        assert!(events.iter().any(|event| event == &json!({
            "kind": "cycle",
            "path": "/project/tsconfig.json",
            "chain": ["/project/tsconfig.json", "/project/node_modules/preset/configs/base.json", "/project/tsconfig.json"],
        })));
        assert!(events.iter().any(|event| event["kind"] == "extends"
            && event["specifier"] == "./missing"
            && event["resolvedPath"].is_null()));
        assert_eq!(
            graph.evidence["config"]["diagnosticSourceTextDigest"],
            stable_digest(leaf.as_bytes()),
        );
        for gap in ["source_real_paths", "package_identities"] {
            assert!(graph.missing_evidence.iter().any(|missing| missing == gap));
        }
        assert_eq!(
            graph.evidence["sourcePackageScopeObservation"]["retentionComplete"],
            true
        );
        for gap in [
            "config_parse_inputs",
            "config_extends_inputs",
            "source_package_scopes",
        ] {
            assert!(!graph.missing_evidence.iter().any(|missing| missing == gap));
        }
    }

    #[test]
    fn config_observation_retention_does_not_imply_a_loaded_config() {
        for text in [None, Some("!")] {
            let filesystem = MemoryFileSystem::new(true);
            if let Some(text) = text {
                filesystem
                    .write_file("/project/tsconfig.json", text)
                    .unwrap();
            }
            let program = Program::from_config(&filesystem, "/project/tsconfig.json");
            let graph = snapshot_report(&program);
            assert!(graph.evidence["config"].is_null());
            assert_eq!(
                graph.evidence["configResolutionObservation"]["retentionComplete"],
                true
            );
            assert!(!program.diagnostics().is_empty());
        }
    }

    #[test]
    fn config_observation_report_retains_read_errors_and_omission_count() {
        let observation = ConfigResolutionObservation {
            events: vec![ConfigResolutionEvent::ReadFile {
                path: "/project/tsconfig.json".to_owned(),
                kind: ConfigInputKind::Config,
                result: Err(ConfigReadError {
                    kind: io::ErrorKind::PermissionDenied,
                    message: "denied".to_owned(),
                }),
            }],
            omitted_events: 3,
        };
        assert_eq!(
            config_observation_report(&observation),
            json!({
                "retentionComplete": false,
                "omittedEvents": 3,
                "textRepresentation": "vfs_parser_input",
                "events": [{
                    "kind": "read_file",
                    "path": "/project/tsconfig.json",
                    "inputKind": "config",
                    "result": {"status": "error", "errorKind": "PermissionDenied", "message": "denied"},
                }],
            })
        );
    }

    #[test]
    fn graph_report_keeps_actual_original_paths_and_effective_default_modes() {
        let filesystem = MemoryFileSystem::new(true);
        for (path, text) in [
            (
                "/project/main.ts",
                "/// <reference types='pkg' />\nconst value = 1;",
            ),
            (
                "/packages/pkg/package.json",
                r#"{"name":"@types/pkg","types":"index.d.ts"}"#,
            ),
            (
                "/packages/pkg/index.d.ts",
                "export declare const value: number;",
            ),
        ] {
            filesystem.write_file(path, text).unwrap();
        }
        filesystem.add_directory_link("/packages/pkg", "/project/node_modules/@types/pkg");
        let program = Program::new_with_options(
            &filesystem,
            "/project",
            &["main.ts".to_owned()],
            CompilerOptions {
                module: ModuleKind::None,
                module_resolution: ModuleResolutionKind::Node10,
                types: Some(Vec::new()),
                ..graph_options()
            },
        );
        let graph = snapshot_report(&program);
        let resolution = &graph.evidence["resolutions"][0];
        assert_eq!(resolution["kind"], "type_reference");
        assert!(resolution["mode"].is_null());
        assert_eq!(resolution["effectiveMode"], "commonjs");
        assert_eq!(
            resolution["resolved"]["originalFileName"],
            "/project/node_modules/@types/pkg/index.d.ts"
        );
        assert_eq!(
            resolution["resolved"]["fileName"],
            "/packages/pkg/index.d.ts"
        );
        assert!(
            !graph
                .missing_evidence
                .iter()
                .any(|gap| gap == "resolution_original_paths" || gap == "resolution_default_modes")
        );
        assert!(
            graph
                .missing_evidence
                .iter()
                .any(|gap| gap == "source_real_paths")
        );
    }
}
