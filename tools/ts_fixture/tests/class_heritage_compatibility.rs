use std::{env, path::PathBuf};

use ts_compiler::Program;
use ts_fixture::{RunnerOptions, run_upstream_diagnostic_baselines};
use ts_options::{CompilerOptions, ModuleKind, ModuleResolutionKind, ScriptTarget};
use ts_vfs::{FileSystem, MemoryFileSystem};

fn program(source: &str) -> Program {
    let filesystem = MemoryFileSystem::new(true);
    filesystem.write_file("/project/input.ts", source).unwrap();
    Program::try_new_with_canonical_checker(
        &filesystem,
        "/project",
        &["input.ts".to_owned()],
        CompilerOptions {
            target: ScriptTarget::Es2015,
            module: ModuleKind::EsNext,
            module_specified: true,
            module_resolution: ModuleResolutionKind::Bundler,
            lib: Some(vec!["es5".to_owned()]),
            strict: false,
            strict_function_types: false,
            strict_null_checks: false,
            strict_property_initialization: false,
            no_emit: true,
            ..CompilerOptions::default()
        },
    )
    .unwrap_or_else(|error| panic!("{source}: {error:?}"))
}

#[test]
fn original_heritage_cases_match_complete_go_diagnostic_artifacts() {
    let Ok(repository) = env::var("TS_GO_REPO") else {
        return;
    };
    for case in [
        "inheritanceGrandParentPrivateMemberCollision",
        "inheritanceGrandParentPrivateMemberCollisionWithPublicMember",
        "inheritanceGrandParentPublicMemberCollisionWithPrivateMember",
        "inheritanceStaticFuncOverridingProperty",
        "inheritanceStaticMembersIncompatible",
        "inheritanceStaticPropertyOverridingMethod",
    ] {
        let mut output = Vec::new();
        let summary = run_upstream_diagnostic_baselines(
            &PathBuf::from(&repository),
            &RunnerOptions {
                filter: Some(format!(
                    "_submodules/TypeScript/tests/cases/compiler/{case}.ts"
                )),
                diagnostics: true,
                canonical_checker: true,
                scorecard_json: env::var_os("TS_CLASS_HERITAGE_SCORECARD_DIR")
                    .map(|directory| PathBuf::from(directory).join(format!("{case}.json"))),
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
fn renamed_private_collisions_keep_the_base_name_and_reduced_detail_name() {
    for (base_visibility, own_visibility, detail) in [
        (
            "private",
            "private",
            "Types have separate declarations of a private property 'run'.",
        ),
        (
            "private",
            "public",
            "Property 'run' is private in type 'Ancestor' but not in type 'Child'.",
        ),
        (
            "public",
            "private",
            "Property 'run' is private in type 'Child' but not in type 'Ancestor'.",
        ),
    ] {
        let source = format!(
            "class Ancestor {{ {base_visibility} run() {{}} }}\n\
             class Parent extends Ancestor {{}}\n\
             class Child extends Parent {{ {own_visibility} run() {{}} }}"
        );
        let program = program(&source);
        let [diagnostic] = program.diagnostics() else {
            panic!("{source}: {:?}", program.diagnostics());
        };
        assert_eq!(diagnostic.code, Some(2415));
        assert_eq!(
            diagnostic.message,
            format!("Class 'Child' incorrectly extends base class 'Parent'.\n  {detail}")
        );
        let range = diagnostic.range.unwrap();
        assert_eq!(range.start.get() as usize, source.find("Child").unwrap());
        assert_eq!(range.len(), 5);
    }
}

#[test]
fn instance_errors_suppress_static_side_errors() {
    for (source, code) in [
        (
            concat!(
                "class Ancestor { private run() {} static value: string; } ",
                "class Parent extends Ancestor {} ",
                "class Child extends Parent { private run() {} static value: number; }",
            ),
            2415,
        ),
        (
            concat!(
                "class Parent { run() { return 'text'; } static value: string; } ",
                "class Child extends Parent { run() { return 1; } static value: number; }",
            ),
            2416,
        ),
    ] {
        let program = program(source);
        let [diagnostic] = program.diagnostics() else {
            panic!("{source}: {:?}", program.diagnostics());
        };
        assert_eq!(diagnostic.code, Some(code), "{source}");
    }
}

#[test]
fn compatible_members_and_separate_sides_remain_valid() {
    for source in [
        "class Parent { static value: string; } class Child extends Parent { static value: string; }",
        "class Parent { static run() { return 'first'; } } class Child extends Parent { static run() { return 'second'; } }",
        "class Parent { static value: string; } class Child extends Parent { value: number; }",
        "class Parent { value: string; } class Child extends Parent { static value: number; }",
        "class Ancestor { private run() {} } class Parent extends Ancestor {} class Child extends Parent {}",
        "class Parent { protected run() {} } class Child extends Parent { public run() {} }",
    ] {
        let program = program(source);
        assert!(
            program.diagnostics().is_empty(),
            "{source}: {:?}",
            program.diagnostics()
        );
    }
}

#[test]
fn static_heritage_does_not_compare_constructor_parameters() {
    let source = concat!(
        "class Parent { constructor(value: number) {} static value: string; } ",
        "class Child extends Parent { constructor(value: string) { super(1); } static value: string; }",
    );
    let program = program(source);
    assert!(
        program.diagnostics().is_empty(),
        "{:?}",
        program.diagnostics()
    );
}

#[test]
fn static_heritage_reports_the_first_incompatible_base_member() {
    let source = concat!(
        "class Parent { static first: string; static second: number; } ",
        "class Child extends Parent { static second: string; static first: number; }",
    );
    let program = program(source);
    let [diagnostic] = program.diagnostics() else {
        panic!("{:?}", program.diagnostics());
    };
    assert_eq!(diagnostic.code, Some(2417));
    assert_eq!(
        diagnostic.message,
        concat!(
            "Class static side 'typeof Child' incorrectly extends base class static side 'typeof Parent'.\n",
            "  Types of property 'first' are incompatible.\n",
            "    Type 'number' is not assignable to type 'string'.",
        )
    );
}

#[test]
fn string_to_function_assignment_reports_a_type_error() {
    let program = program("let callback: () => string = 'text';");
    let [diagnostic] = program.diagnostics() else {
        panic!("{:?}", program.diagnostics());
    };
    assert_eq!(diagnostic.code, Some(2322));
    assert_eq!(
        diagnostic.message,
        "Type 'string' is not assignable to type '() => string'."
    );
}
