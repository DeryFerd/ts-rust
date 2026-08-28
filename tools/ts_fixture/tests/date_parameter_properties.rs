use std::{env, fs, path::PathBuf};

use ts_ast::NodeData;
use ts_compiler::Program;
use ts_fixture::{RunnerOptions, run_upstream_diagnostic_baselines};
use ts_options::{CompilerOptions, ModuleKind, ModuleResolutionKind, ScriptTarget};
use ts_vfs::{FileSystem, MemoryFileSystem};

const DATE_CASE: &str =
    "testdata/tests/cases/compiler/parameterPropertyWithDefaultValueExtended.ts";

fn options() -> CompilerOptions {
    CompilerOptions {
        target: ScriptTarget::Es2015,
        module: ModuleKind::EsNext,
        module_specified: true,
        module_resolution: ModuleResolutionKind::Bundler,
        strict: true,
        exact_optional_property_types: true,
        no_emit: true,
        ..CompilerOptions::default()
    }
}

#[test]
fn original_date_and_native_library_controls_match_complete_error_artifacts() {
    let Ok(repository) = env::var("TS_GO_REPO") else {
        return;
    };
    for case in [
        DATE_CASE,
        "_submodules/TypeScript/tests/cases/compiler/capturedLetConstInLoop2_ES6.ts",
        "_submodules/TypeScript/tests/cases/compiler/argumentsObjectCreatesRestForJs.ts",
        "_submodules/TypeScript/tests/cases/compiler/argumentsPropertyNameInJsMode2.ts",
    ] {
        let mut output = Vec::new();
        let summary = run_upstream_diagnostic_baselines(
            &PathBuf::from(&repository),
            &RunnerOptions {
                filter: Some(case.to_owned()),
                diagnostics: true,
                canonical_checker: true,
                scorecard_json: env::var_os("TS_DATE_PARAMETER_SCORECARD_DIR").map(|directory| {
                    PathBuf::from(directory)
                        .join(format!("{}.json", case.rsplit('/').next().unwrap()))
                }),
                ..RunnerOptions::default()
            },
            &mut output,
        )
        .unwrap();
        assert_eq!(summary.selected_cases, 1, "{case}");
        assert_eq!(summary.executed_variants, 1, "{case}");
        assert_eq!(
            summary.matched,
            1,
            "{case}: {}",
            String::from_utf8_lossy(&output)
        );
        assert_eq!(summary.mismatched, 0, "{case}");
        assert_eq!(summary.missing, 0, "{case}");
    }
}

#[test]
fn original_date_parameter_properties_keep_real_types_and_replay_identities() {
    let Ok(repository) = env::var("TS_GO_REPO") else {
        return;
    };
    let text = fs::read_to_string(PathBuf::from(repository).join(DATE_CASE)).unwrap();
    let filesystem = MemoryFileSystem::new(true);
    filesystem.write_file("/project/input.ts", &text).unwrap();
    let (program, checked) = Program::try_new_with_canonical_checker_and_queries(
        &filesystem,
        "/project",
        &["input.ts".to_owned()],
        options(),
        |program, queries| {
            let source = program.source_file("/project/input.ts").unwrap();
            let mut types = Vec::new();
            let mut symbols = Vec::new();
            let mut property_types = Vec::new();
            let mut property_symbols = Vec::new();
            let mut date_types = Vec::new();
            let mut date_constructors = Vec::new();
            for (node, record) in source.parse.arena.iter() {
                let NodeData::ClassDeclaration(class) = &record.data else {
                    continue;
                };
                let name = source.node_ref(class.name.unwrap()).unwrap();
                let class_type = queries.get_type_at_location(name).unwrap();
                let class_symbol = queries.get_symbol_at_location(name).unwrap().unwrap();
                assert_eq!(
                    queries.get_symbol_declarations(class_symbol).unwrap(),
                    &[source.node_ref(node).unwrap()]
                );
                types.push((name, class_type));
                symbols.push((name, class_symbol));
                let [constructor] = class.members.nodes.as_slice() else {
                    panic!("each original class has one constructor");
                };
                let NodeData::ConstructorDeclaration(constructor) =
                    &source.parse.arena.get(*constructor).unwrap().data
                else {
                    panic!("the class member is a constructor");
                };
                let [parameter] = constructor.parameters.nodes.as_slice() else {
                    panic!("each original constructor has one parameter property");
                };
                let parameter_node = source.node_ref(*parameter).unwrap();
                let NodeData::ParameterDeclaration(parameter) =
                    &source.parse.arena.get(*parameter).unwrap().data
                else {
                    panic!("the constructor has a parameter property");
                };
                let name = source.node_ref(parameter.name).unwrap();
                let type_ = queries.get_type_at_location(name).unwrap();
                let symbol = queries.get_symbol_at_location(name).unwrap().unwrap();
                assert_eq!(
                    queries.get_symbol_declarations(symbol).unwrap(),
                    &[parameter_node]
                );
                assert_eq!(queries.intrinsic_any_name(type_).unwrap(), None);
                assert!(!property_symbols.contains(&symbol));
                property_types.push(type_);
                property_symbols.push(symbol);
                types.push((name, type_));
                symbols.push((name, symbol));
                if let Some(initializer) = parameter.initializer {
                    let initializer_node = source.node_ref(initializer).unwrap();
                    let date_type = queries.get_type_at_location(initializer_node).unwrap();
                    assert_eq!(queries.type_to_string(date_type).unwrap(), "Date");
                    assert_eq!(queries.intrinsic_any_name(date_type).unwrap(), None);
                    date_types.push(date_type);
                    types.push((initializer_node, date_type));
                    let NodeData::NewExpression(initializer) =
                        &source.parse.arena.get(initializer).unwrap().data
                    else {
                        panic!("the original default constructs Date");
                    };
                    let constructor = source.node_ref(initializer.expression).unwrap();
                    let constructor_type = queries.get_type_at_location(constructor).unwrap();
                    assert_ne!(constructor_type, date_type);
                    assert_eq!(
                        queries.type_to_string(constructor_type).unwrap(),
                        "DateConstructor"
                    );
                    let constructor_symbol = queries
                        .get_symbol_at_location(constructor)
                        .unwrap()
                        .unwrap();
                    date_constructors.push((constructor_type, constructor_symbol));
                    types.push((constructor, constructor_type));
                    symbols.push((constructor, constructor_symbol));
                }
            }
            assert_eq!(property_types.len(), 5);
            assert_eq!(date_types.len(), 4);
            assert!(date_types.iter().all(|type_| *type_ == date_types[0]));
            assert!(
                date_constructors
                    .iter()
                    .all(|constructor| *constructor == date_constructors[0])
            );
            for index in [0, 3, 4] {
                assert_eq!(property_types[index], date_types[0]);
            }
            assert_eq!(property_types[1], property_types[2]);
            assert_ne!(property_types[1], date_types[0]);
            assert_eq!(
                queries.type_to_string(property_types[1]).unwrap(),
                "Date | undefined"
            );
            for _ in 0..2 {
                assert!(queries.replay_sources().unwrap().is_empty());
                for &(node, type_) in &types {
                    assert_eq!(queries.get_type_at_location(node).unwrap(), type_);
                }
                for &(node, symbol) in &symbols {
                    assert_eq!(queries.get_symbol_at_location(node).unwrap(), Some(symbol));
                }
            }
        },
    )
    .unwrap();
    assert!(checked.is_some());
    assert!(
        program.diagnostics().is_empty(),
        "{:?}",
        program.diagnostics()
    );
}

#[test]
fn date_parameter_properties_do_not_suppress_later_diagnostics() {
    let filesystem = MemoryFileSystem::new(true);
    filesystem
        .write_file(
            "/project/input.ts",
            concat!(
                "export class DatedRecord { constructor(readonly created = new Date()) {} }\n",
                "export class OptionalDatedRecord { constructor(readonly created?: Date) {} }\n",
                "const value: number = 'wrong';",
            ),
        )
        .unwrap();
    let program = Program::try_new_with_canonical_checker(
        &filesystem,
        "/project",
        &["input.ts".to_owned()],
        options(),
    )
    .unwrap();
    let [diagnostic] = program.diagnostics() else {
        panic!("{:?}", program.diagnostics());
    };
    assert_eq!(diagnostic.code, Some(2322));
}
