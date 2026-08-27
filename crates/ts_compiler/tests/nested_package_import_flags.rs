use ts_ast::{NodeData, NodeRef};
use ts_compiler::{Program, ProgramGraphMissingEvidence, ProgramGraphResolutionKind};
use ts_module::ModuleFormat;
use ts_options::{CompilerOptions, ModuleKind, ModuleResolutionKind};
use ts_vfs::{FileSystem, MemoryFileSystem};

fn variable(program: &Program, name: &str) -> NodeRef {
    let source = program.source_file("/project/main.mts").unwrap();
    source
        .parse
        .arena
        .iter()
        .find_map(|(node, record)| {
            let NodeData::VariableDeclaration(declaration) = &record.data else {
                return None;
            };
            matches!(
                &source.parse.arena.get(declaration.name)?.data,
                NodeData::Identifier(identifier) if identifier.text == name
            )
            .then(|| source.node_ref(node).unwrap())
        })
        .unwrap()
}

fn options(preserve_symlinks: bool) -> CompilerOptions {
    CompilerOptions {
        module: ModuleKind::NodeNext,
        module_specified: true,
        module_resolution: ModuleResolutionKind::NodeNext,
        preserve_symlinks,
        lib: Some(vec!["es5".to_owned()]),
        skip_lib_check: true,
        no_emit: true,
        types: Some(Vec::new()),
        ..CompilerOptions::default()
    }
}

#[test]
#[allow(clippy::too_many_lines)] // Check resolver flags, loaded targets, and canonical replay together.
fn nested_package_import_flags_reach_graph_without_changing_targets_or_replay() {
    for physical_root in ["/store", "/store/node_modules"] {
        for preserve_symlinks in [false, true] {
            let filesystem = MemoryFileSystem::new(true);
            for (path, text) in [
                (
                    "/project/package.json".to_owned(),
                    r##"{"name":"app","type":"module","imports":{"#dep":"pkg"}}"##,
                ),
                (
                    "/project/main.mts".to_owned(),
                    concat!(
                        "import { value as nestedImport } from '#dep';\n",
                        "import nestedRequire = require('#dep');\n",
                        "import { value as directImport } from 'pkg';\n",
                        "import directRequire = require('pkg');\n",
                        "const importedValue: number = nestedImport;\n",
                        "const directImportedValue: number = directImport;\n",
                        "const requiredValue: string = nestedRequire.value;\n",
                        "const directRequiredValue: string = directRequire.value;\n",
                    ),
                ),
                (
                    format!("{physical_root}/pkg/package.json"),
                    r#"{"name":"pkg","version":"1.0.0","type":"module","exports":{".":{"import":"./esm.d.mts","require":"./commonjs.d.cts"}}}"#,
                ),
                (
                    format!("{physical_root}/pkg/esm.d.mts"),
                    "export declare const value: number;",
                ),
                (
                    format!("{physical_root}/pkg/commonjs.d.cts"),
                    "export declare const value: string;",
                ),
            ] {
                filesystem.write_file(&path, text).unwrap();
            }
            filesystem
                .add_directory_link(&format!("{physical_root}/pkg"), "/project/node_modules/pkg");
            let (program, checked) = Program::try_new_with_canonical_checker_and_queries(
                &filesystem,
                "/project",
                &["main.mts".to_owned()],
                options(preserve_symlinks),
                |program, queries| {
                    for (name, expected) in [
                        ("importedValue", "number"),
                        ("directImportedValue", "number"),
                        ("requiredValue", "string"),
                        ("directRequiredValue", "string"),
                    ] {
                        let type_ = queries
                            .get_type_at_location(variable(program, name))
                            .unwrap();
                        assert_eq!(queries.type_to_string(type_).unwrap(), expected);
                    }
                    let graph = program.project_graph_snapshot();
                    assert!(queries.replay_sources().unwrap().is_empty());
                    assert_eq!(program.project_graph_snapshot(), graph);
                },
            )
            .unwrap();
            assert_eq!(checked, Some(()));
            assert!(
                program.diagnostics().is_empty(),
                "{:?}",
                program.diagnostics()
            );
            let graph = program.project_graph_snapshot();
            let resolutions = graph
                .resolutions
                .iter()
                .filter(|resolution| {
                    resolution.request.kind == ProgramGraphResolutionKind::Module
                        && matches!(resolution.request.specifier.as_str(), "#dep" | "pkg")
                })
                .collect::<Vec<_>>();
            assert_eq!(resolutions.len(), 4);
            for resolution in resolutions {
                let usage = resolution.result.effective_mode.unwrap();
                let suffix = if usage == ModuleFormat::Esm {
                    "esm.d.mts"
                } else {
                    "commonjs.d.cts"
                };
                let logical = format!("/project/node_modules/pkg/{suffix}");
                let selected = if preserve_symlinks {
                    logical.clone()
                } else {
                    format!("{physical_root}/pkg/{suffix}")
                };
                let resolved = resolution.result.resolved.as_ref().unwrap();
                assert_eq!(resolved.original_file_name, logical);
                assert_eq!(resolved.resolved_file_name, selected);
                assert_eq!(resolution.request.mode, Some(usage));
                assert_eq!(
                    resolved.is_external_library_import,
                    resolution.request.specifier == "pkg" || selected.contains("/node_modules/")
                );
                let target = resolution.target.as_ref().unwrap();
                assert_eq!(target.file_name, selected);
                assert_eq!(program.source_file(&selected).unwrap().id, target.file_id);
                assert!(
                    resolution
                        .result
                        .package_json_inputs
                        .as_ref()
                        .unwrap()
                        .is_complete()
                );
            }
            assert!(
                graph
                    .missing_evidence
                    .contains(&ProgramGraphMissingEvidence::SourceRealPaths)
            );
            assert!(
                graph
                    .missing_evidence
                    .contains(&ProgramGraphMissingEvidence::PackageIdentities)
            );
            assert!(
                !graph
                    .missing_evidence
                    .contains(&ProgramGraphMissingEvidence::SourcePackageScopes)
            );
        }
    }
}

#[test]
fn missing_nested_package_import_keeps_an_unresolved_graph_entry() {
    for preserve_symlinks in [false, true] {
        let filesystem = MemoryFileSystem::new(true);
        filesystem
            .write_file(
                "/project/package.json",
                r##"{"name":"app","type":"module","imports":{"#missing":"missing"}}"##,
            )
            .unwrap();
        filesystem
            .write_file("/project/main.mts", "import '#missing';")
            .unwrap();
        let program = Program::new_with_options(
            &filesystem,
            "/project",
            &["main.mts".to_owned()],
            CompilerOptions {
                no_check: true,
                no_lib: true,
                ..options(preserve_symlinks)
            },
        );
        let graph = program.project_graph_snapshot();
        let resolution = graph
            .resolutions
            .iter()
            .find(|resolution| resolution.request.specifier == "#missing")
            .unwrap();
        assert!(resolution.result.resolved.is_none());
        assert!(resolution.target.is_none());
        assert_eq!(resolution.result.effective_mode, Some(ModuleFormat::Esm));
        assert!(
            resolution
                .result
                .package_json_inputs
                .as_ref()
                .unwrap()
                .is_complete()
        );
        assert!(!resolution.result.failed_lookups.is_empty());
        assert_eq!(program.project_graph_snapshot(), graph);
    }
}
