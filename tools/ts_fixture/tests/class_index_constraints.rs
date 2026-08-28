use std::{env, fs, path::PathBuf};

use ts_ast::NodeData;
use ts_compiler::{Program, ProgramDiagnostic};
use ts_diagnostics::Category;
use ts_fixture::{Case, RunnerOptions, run_upstream_diagnostic_baselines};
use ts_options::{CompilerOptions, ScriptTarget};
use ts_vfs::{FileSystem, MemoryFileSystem};

fn options() -> CompilerOptions {
    CompilerOptions {
        target: ScriptTarget::Es2015,
        lib: Some(vec!["es5".to_owned()]),
        no_emit: true,
        ..CompilerOptions::default()
    }
}

fn diagnostic(source: &str, name: &str, code: u32, message: String) -> ProgramDiagnostic {
    let parsed = ts_parser::parse_source_file(source);
    let range = parsed
        .arena
        .iter()
        .find_map(|(_, record)| match &record.data {
            NodeData::Identifier(identifier) if identifier.text == name => Some(record.range),
            _ => None,
        })
        .unwrap();
    ProgramDiagnostic {
        file_name: Some("/project/input.ts".to_owned()),
        range: Some(range),
        code: Some(code),
        category: Category::Error,
        message,
        related_information: Vec::new(),
    }
}

fn index_error(source: &str, name: &str, type_: &str) -> ProgramDiagnostic {
    diagnostic(
        source,
        name,
        2411,
        format!(
            "Property '{name}' of type '{type_}' is not assignable to 'string' index type 'number'."
        ),
    )
}

fn initialization_error(source: &str, name: &str) -> ProgramDiagnostic {
    diagnostic(
        source,
        name,
        2564,
        format!(
            "Property '{name}' has no initializer and is not definitely assigned in the constructor."
        ),
    )
}

fn check_source(source: &str, options: CompilerOptions, expected: &[ProgramDiagnostic]) {
    let filesystem = MemoryFileSystem::new(true);
    filesystem.write_file("/project/input.ts", source).unwrap();
    let (program, checked) = Program::try_new_with_canonical_checker_and_queries(
        &filesystem,
        "/project",
        &["input.ts".to_owned()],
        options,
        |_, queries| {
            let cold = queries.cold_diagnostic_snapshot();
            assert_eq!(cold, expected, "{source}");
            assert_eq!(queries.replay_sources().unwrap(), cold, "{source}");
        },
    )
    .unwrap_or_else(|error| panic!("{source}: {error:?}"));
    checked.expect("the canonical checker must run");
    assert_eq!(program.diagnostics(), expected, "{source}");
}

#[test]
fn original_class_indexer_cases_match_complete_go_artifacts() {
    let Some(repository) = env::var_os("TS_GO_REPO").map(PathBuf::from) else {
        return;
    };
    for name in ["classIndexer.ts", "classIndexer3.ts", "classIndexer5.ts"] {
        let path = repository
            .join("_submodules/TypeScript/tests/cases/compiler")
            .join(name);
        if name == "classIndexer3.ts" {
            let case = Case::parse(&path, fs::read(&path).unwrap()).unwrap();
            assert_eq!(
                case.directive_values("target").collect::<Vec<_>>(),
                ["es2015"]
            );
            let [unit] = case.units.as_slice() else {
                panic!("the original fixture must retain one source unit");
            };
            let source = unit.source_text.as_scannable_str();
            check_source(
                source,
                options(),
                &[
                    initialization_error(source, "x"),
                    index_error(source, "y", "string"),
                    initialization_error(source, "y"),
                ],
            );
        }
        let mut output = Vec::new();
        let summary = run_upstream_diagnostic_baselines(
            &repository,
            &RunnerOptions {
                filter: Some(path.to_string_lossy().into_owned()),
                diagnostics: true,
                canonical_checker: true,
                ..RunnerOptions::default()
            },
            &mut output,
        )
        .unwrap();
        let output = String::from_utf8(output).unwrap();
        assert_eq!(summary.selected_cases, 1, "{name}: {output}");
        assert_eq!(summary.executed_variants, 1, "{name}: {output}");
        assert_eq!(summary.matched, 1, "{name}: {output}");
        assert!(summary.is_success(), "{name}: {output}");
        println!("{name}: {output}");
    }
}

#[test]
fn inherited_index_error_keeps_both_initialization_errors() {
    let source = concat!(
        "class NumericIndex { [key: string]: number; }\n",
        "class Entry extends NumericIndex { count: number; label: string; }",
    );
    check_source(
        source,
        options(),
        &[
            initialization_error(source, "count"),
            index_error(source, "label", "string"),
            initialization_error(source, "label"),
        ],
    );
}

#[test]
fn inherited_index_uses_assignability_for_literal_any_and_never_types() {
    check_source(
        concat!(
            "class NumericIndex { [key: string]: number; }\n",
            "class Entry extends NumericIndex { readonly literal = 1; dynamic: any; impossible!: never; }",
        ),
        options(),
        &[],
    );
}

#[test]
fn inherited_index_checks_private_and_protected_but_not_private_identifiers_or_statics() {
    let source = concat!(
        "class NumericIndex { [key: string]: number; }\n",
        "class Entry extends NumericIndex { private hidden: string = 'a'; ",
        "protected guarded: string = 'b'; #secret: string = 'c'; static title: string = 'd'; }",
    );
    check_source(
        source,
        options(),
        &[
            index_error(source, "hidden", "string"),
            index_error(source, "guarded", "string"),
        ],
    );
}

#[test]
fn optional_members_use_the_non_missing_property_type() {
    let source = concat!(
        "class NumericIndex { [key: string]: number; }\n",
        "class Entry extends NumericIndex { optional?: number; }",
    );
    for (strict, exact) in [(true, false), (true, true), (false, false)] {
        let expected = if strict && !exact {
            vec![index_error(source, "optional", "number | undefined")]
        } else {
            Vec::new()
        };
        check_source(
            source,
            CompilerOptions {
                strict,
                strict_null_checks: strict,
                strict_property_initialization: strict,
                exact_optional_property_types: exact,
                ..options()
            },
            &expected,
        );
    }
}

#[test]
fn inherited_index_does_not_repeat_a_base_property_error() {
    let source = concat!(
        "class NumericIndex { [key: string]: number; }\n",
        "class First extends NumericIndex { label: string = 'a'; }\n",
        "class Second extends First { title: string = 'b'; }",
    );
    check_source(
        source,
        options(),
        &[
            index_error(source, "label", "string"),
            index_error(source, "title", "string"),
        ],
    );
}

#[test]
fn inherited_index_checks_method_types_after_their_bodies() {
    let source = concat!(
        "class NumericIndex { [key: string]: number; }\n",
        "class Entry extends NumericIndex { read(): number { return 1; } }",
    );
    check_source(
        source,
        options(),
        &[index_error(source, "read", "() => number")],
    );
}
