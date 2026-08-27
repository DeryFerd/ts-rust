use serde::Serialize;
use serde_json::{Value, json};
use ts_ast::NodeRef;
use ts_checker::semantic::{CanonicalModuleResolutionInput, CanonicalModuleResolutionMode};
use ts_compiler::{
    CanonicalProgramCheckError, Program, ProgramGraphMissingEvidence, ProgramGraphReferenceKind,
    ProgramGraphResolutionKind,
};
use ts_module::{FailedLookupKind, ModuleFormat, ResolutionMode};
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
            "resolved": resolved,
            "ambientTarget": resolution.ambient_target.as_deref().map(path_identity),
            "loadedTarget": target,
            "failedLookups": failed,
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
        "sourceDigest": config.source_text.as_deref().map(|text| stable_digest(text.as_bytes())),
        "sourceByteCount": config.source_text.as_ref().map(String::len),
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
    let mut missing_evidence = graph
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
    if !graph.options.skips_type_checking(true, true)
        && graph.sources.iter().any(|source| source.is_default_library)
    {
        missing_evidence.push("default_library_semantic_diagnostics".to_owned());
    }
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
mod tests {
    use serde_json::{Value, json};
    use ts_compiler::Program;
    use ts_options::{CompilerOptions, ModuleKind, ModuleResolutionKind};
    use ts_vfs::{FileSystem, MemoryFileSystem};

    use super::{ProjectStage, snapshot_report};

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
}
