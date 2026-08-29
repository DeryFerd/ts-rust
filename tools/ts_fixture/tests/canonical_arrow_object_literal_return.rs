use std::{env, fs, path::PathBuf};

use ts_ast::NodeData;
use ts_compiler::Program;
use ts_fixture::{RunnerOptions, run_upstream_diagnostic_baselines};
use ts_options::{CompilerOptions, ScriptTarget};
use ts_vfs::{FileSystem, MemoryFileSystem};

const CASE: &str =
    "_submodules/TypeScript/tests/cases/compiler/arrowFunctionWithObjectLiteralBody5.ts";
const INPUT: &str = "/.src/arrowFunctionWithObjectLiteralBody5.ts";

#[test]
fn original_arrow_object_literal_returns_match_complete_error_artifact() {
    let Ok(repository) = env::var("TS_GO_REPO") else {
        return;
    };
    let mut output = Vec::new();
    let summary = run_upstream_diagnostic_baselines(
        &PathBuf::from(repository),
        &RunnerOptions {
            filter: Some(CASE.to_owned()),
            diagnostics: true,
            canonical_checker: true,
            ..RunnerOptions::default()
        },
        &mut output,
    )
    .unwrap();
    assert_eq!(summary.selected_cases, 1);
    assert_eq!(summary.executed_variants, 1);
    assert_eq!(summary.matched, 1, "{}", String::from_utf8_lossy(&output));
    assert_eq!(summary.mismatched, 0);
    assert_eq!(summary.missing, 0);
}

#[test]
#[allow(clippy::too_many_lines)] // Check all four original arrows and their replay identities.
fn original_arrow_object_literal_returns_keep_types_and_replay_identities() {
    let Ok(repository) = env::var("TS_GO_REPO") else {
        return;
    };
    let text = fs::read_to_string(PathBuf::from(repository).join(CASE)).unwrap();
    let filesystem = MemoryFileSystem::new(true);
    filesystem.write_file(INPUT, &text).unwrap();
    let (program, checked) = Program::try_new_with_canonical_checker_and_queries(
        &filesystem,
        "/.src",
        &[INPUT.to_owned()],
        CompilerOptions {
            target: ScriptTarget::Es2015,
            ..CompilerOptions::default()
        },
        |program, queries| {
            let source = program.source_file(INPUT).unwrap();
            let mut names = Vec::new();
            let mut types = Vec::new();
            let mut symbols = Vec::new();
            let mut error_types = Vec::new();
            let mut object_type = None;
            for (node, record) in source.parse.arena.iter() {
                let NodeData::VariableDeclaration(variable) = &record.data else {
                    continue;
                };
                let NodeData::Identifier(name) =
                    &source.parse.arena.get(variable.name).unwrap().data
                else {
                    panic!("each original arrow has one variable name")
                };
                let name_node = source.node_ref(variable.name).unwrap();
                let initializer = variable.initializer.unwrap();
                let NodeData::ArrowFunction(arrow) =
                    &source.parse.arena.get(initializer).unwrap().data
                else {
                    panic!("each original initializer is an arrow")
                };
                let initializer = source.node_ref(initializer).unwrap();
                let body = source.node_ref(arrow.body).unwrap();
                let callable = queries.get_type_at_location(name_node).unwrap();
                let body_type = queries.get_type_at_location(body).unwrap();
                assert_eq!(queries.get_type_at_location(initializer).unwrap(), callable);
                assert_eq!(queries.intrinsic_any_name(callable).unwrap(), None);
                assert_eq!(queries.intrinsic_any_name(body_type).unwrap(), None);
                if name.text == "c" {
                    assert_eq!(
                        queries.type_to_string(callable).unwrap(),
                        "() => { name: string; message: string; }",
                    );
                    assert!(object_type.replace(body_type).is_none());
                } else {
                    assert!(matches!(name.text.as_str(), "a" | "b" | "d"));
                    assert_eq!(queries.type_to_string(callable).unwrap(), "() => Error");
                    assert_eq!(queries.type_to_string(body_type).unwrap(), "Error");
                    error_types.push(body_type);
                }
                let symbol = queries.get_symbol_at_location(name_node).unwrap().unwrap();
                assert_eq!(
                    queries.get_symbol_declarations(symbol).unwrap(),
                    &[source.node_ref(node).unwrap()],
                );
                names.push(name.text.as_str());
                types.extend([
                    (name_node, callable),
                    (initializer, callable),
                    (body, body_type),
                ]);
                symbols.push((name_node, symbol));
            }
            assert_eq!(names, ["a", "b", "c", "d"]);
            assert_eq!(error_types.len(), 3);
            assert!(error_types.iter().all(|type_| *type_ == error_types[0]));
            assert_ne!(object_type.unwrap(), error_types[0]);
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
