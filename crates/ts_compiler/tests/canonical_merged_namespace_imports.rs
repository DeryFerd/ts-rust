use ts_ast::{NodeData, NodeRef, SyntaxKind};
use ts_compiler::Program;
use ts_options::{CompilerOptions, ModuleKind, ModuleResolutionKind, ScriptTarget};
use ts_vfs::{FileSystem, MemoryFileSystem};

const FILES: [(&str, &str); 4] = [
    (
        "consumer.ts",
        include_str!("../../ts_checker/tests/fixtures/namespace_merged_dependency/consumer.ts"),
    ),
    (
        "provider.ts",
        include_str!("../../ts_checker/tests/fixtures/namespace_merged_dependency/provider.ts"),
    ),
    (
        "dependency.ts",
        include_str!("../../ts_checker/tests/fixtures/namespace_merged_dependency/dependency.ts"),
    ),
    (
        "augmentation.ts",
        include_str!("../../ts_checker/tests/fixtures/namespace_merged_dependency/augmentation.ts"),
    ),
];

fn variable(program: &Program, path: &str, name: &str) -> NodeRef {
    let source = program.source_file(path).unwrap();
    source
        .parse
        .arena
        .iter()
        .find_map(|(node, record)| {
            let NodeData::VariableDeclaration(variable) = &record.data else {
                return None;
            };
            let NodeData::Identifier(identifier) = &source.parse.arena.get(variable.name)?.data
            else {
                return None;
            };
            (identifier.text == name).then(|| source.node_ref(node).unwrap())
        })
        .unwrap()
}

#[test]
fn namespace_imports_keep_augmented_module_owners_and_replay() {
    for merge_through_star in [false, true] {
        let filesystem = MemoryFileSystem::new(true);
        for (path, source) in FILES {
            filesystem
                .write_file(&format!("/project/{path}"), source)
                .unwrap();
        }
        filesystem
            .write_file(
                "/project/namespace-read.ts",
                "import * as provider from './provider'; export const observed = provider.forwarded.value;",
            )
            .unwrap();
        if merge_through_star {
            filesystem
                .write_file(
                    "/project/dependency.ts",
                    &format!("{}export * from './marker';\n", FILES[2].1),
                )
                .unwrap();
            filesystem
                .write_file("/project/marker.ts", "export interface Marker {}\n")
                .unwrap();
        }
        let mut roots = FILES.map(|(path, _)| path.to_owned()).to_vec();
        roots.push("namespace-read.ts".to_owned());
        let (program, result) = Program::try_new_with_canonical_checker_and_queries(
            &filesystem,
            "/project",
            &roots,
            CompilerOptions {
                module: ModuleKind::EsNext,
                module_specified: true,
                module_resolution: ModuleResolutionKind::Bundler,
                target: ScriptTarget::Es2022,
                lib: Some(vec!["es5".to_owned()]),
                no_emit: true,
                ..CompilerOptions::default()
            },
            |program, queries| {
                let dependency = program.source_file("/project/dependency.ts").unwrap();
                let source = dependency.node_ref(dependency.parse.source_file).unwrap();
                let module = queries.get_symbol_at_location(source).unwrap().unwrap();
                let declarations = queries.get_symbol_declarations(module).unwrap().to_vec();
                assert_eq!(declarations[0], source);
                if merge_through_star {
                    assert_eq!(declarations.len(), 2);
                    let augmentation = program.source_file("/project/augmentation.ts").unwrap();
                    let declaration = augmentation
                        .parse
                        .arena
                        .iter()
                        .find_map(|(node, record)| {
                            (record.kind == SyntaxKind::ModuleDeclaration)
                                .then(|| augmentation.node_ref(node).unwrap())
                        })
                        .unwrap();
                    assert_eq!(declarations[1], declaration);
                    assert_eq!(
                        queries.get_symbol_at_location(declaration),
                        Ok(Some(module))
                    );
                }
                let forwarded = variable(program, "/project/provider.ts", "forwarded");
                let value = variable(program, "/project/dependency.ts", "value");
                let namespace = queries.get_type_at_location(forwarded).unwrap();
                let number = queries.get_type_at_location(value).unwrap();
                assert_eq!(queries.type_to_string(number).unwrap(), "number");
                assert_ne!(namespace, number);
                assert_eq!(queries.get_type_at_location(source), Ok(namespace));
                let value_symbol = queries.get_symbol_at_location(value).unwrap().unwrap();
                let observed = variable(program, "/project/namespace-read.ts", "observed");
                let observer = program.source_file("/project/namespace-read.ts").unwrap();
                let NodeData::VariableDeclaration(variable) =
                    &observer.parse.arena.get(observed.node).unwrap().data
                else {
                    panic!("the observer is a variable declaration");
                };
                let access = observer.node_ref(variable.initializer.unwrap()).unwrap();
                assert_eq!(queries.get_type_at_location(observed), Ok(number));
                assert_eq!(queries.get_type_at_location(access), Ok(number));
                assert_eq!(
                    queries.get_symbol_at_location(access),
                    Ok(Some(value_symbol))
                );
                assert!(queries.replay_sources().unwrap().is_empty());
                assert_eq!(queries.get_type_at_location(forwarded), Ok(namespace));
                assert_eq!(queries.get_type_at_location(value), Ok(number));
                assert_eq!(queries.get_type_at_location(source), Ok(namespace));
                assert_eq!(queries.get_type_at_location(observed), Ok(number));
                assert_eq!(queries.get_type_at_location(access), Ok(number));
                assert_eq!(
                    queries.get_symbol_at_location(access),
                    Ok(Some(value_symbol))
                );
                assert_eq!(queries.get_symbol_at_location(source), Ok(Some(module)));
                assert_eq!(
                    queries.get_symbol_declarations(module).unwrap(),
                    declarations
                );
            },
        )
        .unwrap_or_else(|error| panic!("merge_through_star={merge_through_star}: {error:?}"));
        assert_eq!(result, Some(()));
        assert!(
            program.diagnostics().is_empty(),
            "{:?}",
            program.diagnostics()
        );
        for (path, source) in FILES {
            if !merge_through_star || path != "dependency.ts" {
                assert_eq!(
                    program
                        .source_file(&format!("/project/{path}"))
                        .unwrap()
                        .source_text,
                    source,
                );
            }
        }
    }
}
