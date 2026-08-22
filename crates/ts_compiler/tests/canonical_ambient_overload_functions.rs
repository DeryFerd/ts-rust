use ts_compiler::Program;
use ts_options::{CompilerOptions, ModuleKind, ModuleResolutionKind, ScriptTarget};
use ts_vfs::{FileSystem, MemoryFileSystem};

fn canonical_options() -> CompilerOptions {
    CompilerOptions {
        module: ModuleKind::EsNext,
        module_specified: true,
        module_resolution: ModuleResolutionKind::Bundler,
        lib: Some(vec!["es5".to_owned()]),
        strict: true,
        target: ScriptTarget::Es2015,
        ..CompilerOptions::default()
    }
}

fn pinned_strict_false_options() -> CompilerOptions {
    CompilerOptions {
        no_implicit_any: false,
        strict: false,
        strict_bind_call_apply: false,
        strict_builtin_iterator_return: false,
        strict_function_types: false,
        strict_null_checks: false,
        strict_property_initialization: false,
        target: ScriptTarget::Es2015,
        use_unknown_in_catch_variables: false,
        ..CompilerOptions::default()
    }
}

fn pinned_strict_property_options() -> CompilerOptions {
    CompilerOptions {
        strict_null_checks: true,
        strict_property_initialization: true,
        ..pinned_strict_false_options()
    }
}

#[test]
fn canonical_program_checks_local_ambient_overload_order_and_hoisting() {
    let fs = MemoryFileSystem::new(true);
    fs.write_file(
        "/project/main.ts",
        concat!(
            "export {};\n",
            "const before: string = ordered(1);\n",
            "declare function ordered(value: number): string;\n",
            "declare function ordered(value: number): number;\n",
            "declare function choose(value: number): 'number';\n",
            "declare function choose(value: string, suffix?: string): 'string';\n",
            "const numberResult: 'number' = choose(1);\n",
            "const stringResult: 'string' = choose('x', '!');\n",
        ),
    )
    .unwrap();

    let program = Program::try_new_with_canonical_checker(
        &fs,
        "/project",
        &["main.ts".to_owned()],
        canonical_options(),
    )
    .unwrap();

    assert!(program.diagnostics().is_empty());
}

#[test]
fn pinned_strict_false_fixture_checks_exactly_without_diagnostics() {
    // Pinned typescript-go dc37b524:
    // `_submodules/TypeScript/tests/cases/compiler/ambiguousOverloadResolution.ts`.
    //
    // Direct class heritage and the bare instance field are both admitted
    // when strictNullChecks and strictPropertyInitialization are disabled.
    // The original fixture's annotated uninitialized `var` is also admitted
    // under those options, so the complete overload-resolution case checks.
    let fs = MemoryFileSystem::new(true);
    fs.write_file(
        "/project/ambiguousOverloadResolution.ts",
        concat!(
            "class A { }\n",
            "class B extends A { x: number; }\n",
            "\n",
            "declare function f(p: A, q: B): number;\n",
            "declare function f(p: B, q: A): string;\n",
            "\n",
            "var x: B;\n",
            "var t: number = f(x, x);\n",
        ),
    )
    .unwrap();
    let program = Program::try_new_with_canonical_checker(
        &fs,
        "/project",
        &["ambiguousOverloadResolution.ts".to_owned()],
        pinned_strict_false_options(),
    )
    .unwrap();

    assert!(program.diagnostics().is_empty());
}

#[test]
fn strict_property_options_report_field_and_unassigned_variable_reads() {
    let fs = MemoryFileSystem::new(true);
    fs.write_file(
        "/project/ambiguousOverloadResolution.ts",
        concat!(
            "class A { }\n",
            "class B extends A { x: number; }\n",
            "\n",
            "declare function f(p: A, q: B): number;\n",
            "declare function f(p: B, q: A): string;\n",
            "\n",
            "var x: B;\n",
            "var t: number = f(x, x);\n",
        ),
    )
    .unwrap();

    let program = Program::try_new_with_canonical_checker(
        &fs,
        "/project",
        &["ambiguousOverloadResolution.ts".to_owned()],
        pinned_strict_property_options(),
    )
    .unwrap();

    assert_eq!(
        program
            .diagnostics()
            .iter()
            .map(|diagnostic| diagnostic.code)
            .collect::<Vec<_>>(),
        [Some(2564), Some(2454), Some(2454)]
    );
}

#[test]
fn definite_field_variant_reports_only_unassigned_variable_reads() {
    let fs = MemoryFileSystem::new(true);
    fs.write_file(
        "/project/ambiguousOverloadResolution.ts",
        concat!(
            "class A { }\n",
            "class B extends A { x!: number; }\n",
            "\n",
            "declare function f(p: A, q: B): number;\n",
            "declare function f(p: B, q: A): string;\n",
            "\n",
            "var x: B;\n",
            "var t: number = f(x, x);\n",
        ),
    )
    .unwrap();

    let program = Program::try_new_with_canonical_checker(
        &fs,
        "/project",
        &["ambiguousOverloadResolution.ts".to_owned()],
        pinned_strict_property_options(),
    )
    .unwrap();

    assert_eq!(
        program
            .diagnostics()
            .iter()
            .map(|diagnostic| diagnostic.code)
            .collect::<Vec<_>>(),
        [Some(2454), Some(2454)]
    );
}
