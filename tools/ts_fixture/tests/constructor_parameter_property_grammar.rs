use std::{env, fs, path::PathBuf};

use ts_checker::semantic::SourceCheckError;
use ts_compiler::{CanonicalProgramCheckError, Program, ProgramDiagnostic};
use ts_core::{TextPos, TextRange};
use ts_diagnostics::Category;
use ts_fixture::{Case, RunnerOptions, run_upstream_diagnostic_baselines};
use ts_options::{CompilerOptions, ScriptTarget};
use ts_vfs::{FileSystem, MemoryFileSystem};

fn options() -> CompilerOptions {
    CompilerOptions {
        lib: Some(vec!["es5".to_owned()]),
        no_emit: true,
        strict: false,
        target: ScriptTarget::Es2015,
        ..CompilerOptions::default()
    }
}

fn check_source(source: &str, name: &str, expected: &[ProgramDiagnostic]) {
    let filesystem = MemoryFileSystem::new(true);
    let path = format!("/project/{name}");
    filesystem.write_file(&path, source).unwrap();
    let (program, checked) = Program::try_new_with_canonical_checker_and_queries(
        &filesystem,
        "/project",
        &[name.to_owned()],
        options(),
        |_, queries| {
            let cold = queries.cold_diagnostic_snapshot();
            assert_eq!(cold, expected, "{name}");
            assert_eq!(queries.replay_sources().unwrap(), cold, "{name}");
        },
    )
    .unwrap_or_else(|error| panic!("{name}: {error:?}"));
    checked.expect("the canonical checker must run");
    assert_eq!(program.diagnostics(), expected, "{name}");
}

#[test]
fn original_parameter_lists_match_full_go_error_artifacts() {
    let Some(repository) = env::var_os("TS_GO_REPO").map(PathBuf::from) else {
        return;
    };
    for (name, parameters) in [
        (
            "ParameterList7.ts",
            vec!["public p1:string", "private p2:number"],
        ),
        (
            "ParameterList8.ts",
            vec!["public p1:string", "private p2:number", "public p3:any"],
        ),
    ] {
        let path = repository
            .join("_submodules/TypeScript/tests/cases/compiler")
            .join(name);
        let bytes = fs::read(&path).unwrap();
        let case = Case::parse(&path, bytes).unwrap();
        assert_eq!(
            case.directive_values("target").collect::<Vec<_>>(),
            ["es2015"]
        );
        let [unit] = case.units.as_slice() else {
            panic!("{name} must have one unchanged source unit");
        };
        let source = unit.source_text.as_scannable_str();
        let expected = parameters
            .iter()
            .map(|parameter| {
                let start = source.find(parameter).unwrap();
                ProgramDiagnostic {
                    file_name: Some(format!("/project/{name}")),
                    range: Some(TextRange::new(
                        TextPos::new(u32::try_from(start).unwrap()),
                        TextPos::new(u32::try_from(start + parameter.len()).unwrap()),
                    )),
                    code: Some(2369),
                    category: Category::Error,
                    message:
                        "A parameter property is only allowed in a constructor implementation."
                            .to_owned(),
                    related_information: Vec::new(),
                }
            })
            .collect::<Vec<_>>();
        check_source(source, name, &expected);

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
        assert_eq!(summary.selected_cases, 1, "{output}");
        assert_eq!(summary.executed_variants, 1, "{output}");
        assert_eq!(summary.matched, 1, "{output}");
        assert!(summary.is_success(), "{output}");
        println!("{output}");
    }
}

#[test]
fn valid_parameter_property_constructor_keeps_body_checking() {
    check_source(
        "class Model { constructor(public value: number) { this.value = 2; const n: number = this.value; } }",
        "valid.ts",
        &[],
    );
}

#[test]
fn nonempty_overload_implementation_does_not_return_partial_grammar_diagnostics() {
    let filesystem = MemoryFileSystem::new(true);
    filesystem
        .write_file(
            "/project/body.ts",
            "class Model { constructor(public input: number); constructor(public value: any) { missing; } }",
        )
        .unwrap();
    let error = Program::try_new_with_canonical_checker(
        &filesystem,
        "/project",
        &["body.ts".to_owned()],
        options(),
    )
    .expect_err("the grammar check must not skip the implementation body");
    assert!(matches!(
        error,
        CanonicalProgramCheckError::SourceCheck {
            file_name,
            error: SourceCheckError::Class(_) | SourceCheckError::Unsupported(_),
        } if file_name == "/project/body.ts"
    ));
}
