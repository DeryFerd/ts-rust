use ts_ast::{NodeData, NodeRef};
use ts_checker::semantic::CanonicalModuleResolutionMode;
use ts_compiler::{CanonicalModuleResolutionLookup, Program};
use ts_options::{CompilerOptions, ModuleKind, ModuleResolutionKind};
use ts_vfs::{FileSystem, MemoryFileSystem};

fn specifier(program: &Program, path: &str) -> NodeRef {
    let source = program.source_file(path).unwrap();
    source
        .parse
        .arena
        .iter()
        .find_map(|(node, record)| {
            matches!(&record.data, NodeData::StringLiteral(text) if text.text == "./producer.cjs")
                .then(|| source.node_ref(node).unwrap())
        })
        .unwrap()
}

#[test]
fn nodenext_namespace_manifest_keeps_bare_and_wrapped_import_modes() {
    let filesystem = MemoryFileSystem::new(true);
    for (path, text) in [
        ("/project/producer.cts", "export const value: number = 1;"),
        (
            "/project/consumer.mts",
            "import * as ns from './producer.cjs'; export type Copy = typeof ns; export const copied = ns;",
        ),
        (
            "/project/consumer.cts",
            "import * as ns from './producer.cjs'; export type Copy = typeof ns; export const copied = ns;",
        ),
    ] {
        filesystem.write_file(path, text).unwrap();
    }
    let (program, result) = Program::try_new_with_canonical_checker_and_queries(
        &filesystem,
        "/project",
        &[
            "producer.cts".to_owned(),
            "consumer.mts".to_owned(),
            "consumer.cts".to_owned(),
        ],
        CompilerOptions {
            module: ModuleKind::NodeNext,
            module_specified: true,
            module_resolution: ModuleResolutionKind::NodeNext,
            lib: Some(vec!["es5".to_owned()]),
            skip_lib_check: true,
            no_emit: true,
            ..CompilerOptions::default()
        },
        |program, queries| {
            let target = program.source_file("/project/producer.cts").unwrap();
            let mut targets = Vec::new();
            for (path, mode) in [
                ("/project/consumer.mts", CanonicalModuleResolutionMode::Esm),
                (
                    "/project/consumer.cts",
                    CanonicalModuleResolutionMode::CommonJs,
                ),
            ] {
                let CanonicalModuleResolutionLookup::Resolved(resolved) =
                    queries.module_resolution(specifier(program, path))
                else {
                    panic!("missing producer resolution for {path}");
                };
                assert_eq!(resolved.target_file(), target.id);
                assert_eq!(resolved.usage_mode(), mode);
                assert_eq!(
                    resolved.target_mode(),
                    CanonicalModuleResolutionMode::CommonJs
                );
                assert!(!resolved.is_ambient_module());
                assert_eq!(
                    queries
                        .get_symbol_declarations(resolved.target_symbol())
                        .unwrap(),
                    &[target.node_ref(target.parse.source_file).unwrap()]
                );
                targets.push(resolved.target_symbol());
            }
            assert_eq!(targets[0], targets[1]);
            assert!(queries.replay_sources().unwrap().is_empty());
        },
    )
    .unwrap();
    assert_eq!(result, Some(()));
    assert!(
        program.diagnostics().is_empty(),
        "{:?}",
        program.diagnostics()
    );
}
