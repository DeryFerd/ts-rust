use ts_compiler::Program;
use ts_options::{CompilerOptions, ScriptTarget};
use ts_vfs::{FileSystem, MemoryFileSystem};

fn check_case(
    name: &str,
    files: &[(&str, &str)],
    strict: bool,
    target: ScriptTarget,
    expected: &[(&str, u32)],
) -> Result<(), String> {
    let filesystem = MemoryFileSystem::new(true);
    for (path, source) in files {
        filesystem
            .write_file(&format!("/project/{path}"), source)
            .unwrap();
    }
    let roots = files
        .iter()
        .map(|(path, _)| (*path).to_owned())
        .collect::<Vec<_>>();
    let (program, ()) = Program::try_new_with_canonical_checker_and_queries(
        &filesystem,
        "/project",
        &roots,
        CompilerOptions {
            lib: Some(vec!["es5".to_owned()]),
            no_emit: true,
            strict,
            target,
            ..CompilerOptions::default()
        },
        |_, queries| {
            let cold = queries.cold_diagnostic_snapshot();
            let store = queries.semantic_store_id();
            for _ in 0..2 {
                assert_eq!(queries.replay_sources().unwrap(), cold, "{name}");
                assert_eq!(queries.semantic_store_id(), store, "{name}");
            }
        },
    )
    .map_err(|error| format!("{name}: {error:?}"))
    .map(|(program, result)| (program, result.expect("the canonical checker ran")))?;
    let actual = program
        .diagnostics()
        .iter()
        .map(|diagnostic| {
            (
                diagnostic
                    .file_name
                    .as_deref()
                    .unwrap()
                    .strip_prefix("/project/")
                    .unwrap(),
                diagnostic.code.unwrap(),
            )
        })
        .collect::<Vec<_>>();
    println!("{name}: {:?}", program.diagnostics());
    if actual != expected {
        return Err(format!("{name}: actual={actual:?}, expected={expected:?}"));
    }
    Ok(())
}

#[test]
fn root_constructor_admission_matches_the_original_inputs_and_defaults() {
    for (name, source, expected) in [
        (
            "forwarded_parameter",
            concat!(
                "class Base { constructor(public value: string) {} } ",
                "class Model extends Base { constructor(value: string) { super(value); } }",
            ),
            &[][..],
        ),
        (
            "local_body",
            "class Model { constructor() { const value = 1; } }",
            &[][..],
        ),
        (
            "missing_super",
            "class Base {} class Model extends Base { constructor() {} }",
            &[("input.ts", 2377)][..],
        ),
    ] {
        check_case(
            name,
            &[("input.ts", source)],
            false,
            ScriptTarget::Es5,
            expected,
        )
        .unwrap();
    }
}

#[test]
fn admitted_later_method_retains_the_earlier_diagnostic_and_replay() {
    check_case(
        "retained_earlier",
        &[
            ("first.ts", r#"const first: number = "wrong";"#),
            ("later.ts", "class Later { method(value: string) {} }"),
        ],
        false,
        ScriptTarget::Es5,
        &[("first.ts", 2322)],
    )
    .unwrap();
}

#[test]
fn root_static_name_priority_is_consistent_for_exported_classes() {
    let mut errors = Vec::new();
    for (name, source) in [
        (
            "script_static_name",
            "class C { static foo: string; bar() { let k = foo; } }",
        ),
        (
            "exported_static_name",
            "export class C { static foo: string; bar() { let k = foo; } }",
        ),
    ] {
        if let Err(error) = check_case(
            name,
            &[("input.ts", source)],
            false,
            ScriptTarget::Es5,
            &[("input.ts", 2662)],
        ) {
            errors.push(error);
        }
    }
    assert!(errors.is_empty(), "{}", errors.join("\n"));
}

#[test]
fn root_duplicate_priority_retains_initializer_diagnostics() {
    for (name, source, expected) in [
        (
            "duplicate_property",
            "class Model { value: number = 1; value: number = 2; }",
            &[("input.ts", 2300), ("input.ts", 2300)][..],
        ),
        (
            "duplicate_initializer",
            "class Model { value: number = 2; accessor value: string = 'next'; }",
            &[("input.ts", 2300), ("input.ts", 2322), ("input.ts", 2300)][..],
        ),
    ] {
        check_case(
            name,
            &[("input.ts", source)],
            true,
            ScriptTarget::EsNext,
            expected,
        )
        .unwrap();
    }
}
