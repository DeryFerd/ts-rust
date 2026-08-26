use serde::Serialize;
use serde_json::{Value, json};
use ts_checker::semantic::{CanonicalModuleResolutionInput, CanonicalModuleResolutionMode};
use ts_compiler::{
    Program, ProgramGraphMissingEvidence, ProgramGraphReferenceKind, ProgramGraphResolutionKind,
};
use ts_module::{FailedLookupKind, ModuleFormat, ResolutionMode};

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
            "extension": target.extension.map(|extension| extension.as_str()),
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
        "artifactFileOrder": ordered_artifact_files,
    });
    let module_resolution_manifest = match &graph.module_resolution_manifest {
        Err(error) => ProjectStage::compiler_failure(error),
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
