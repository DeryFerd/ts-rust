use ts_checker::semantic::{SourceCheckError, UnsupportedSourceSyntax};
use ts_compiler::{
    CanonicalProgramCheckError, CanonicalProgramCheckFailureClass, Program,
};
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
fn pinned_strict_false_fixture_advances_to_uninitialized_variable() {
    // Pinned typescript-go dc37b524:
    // `_submodules/TypeScript/tests/cases/compiler/ambiguousOverloadResolution.ts`.
    //
    // Direct class heritage and the bare instance field are both admitted
    // when strictNullChecks and strictPropertyInitialization are disabled.
    // The original fixture therefore reaches the later top-level variable.
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
    let error = Program::try_new_with_canonical_checker(
        &fs,
        "/project",
        &["ambiguousOverloadResolution.ts".to_owned()],
        pinned_strict_false_options(),
    )
    .unwrap_err();

    assert_eq!(
        error.failure_class(),
        CanonicalProgramCheckFailureClass::Unsupported {
            capability_code: "E00.SOURCE_SYNTAX",
        }
    );
    assert!(
        matches!(
            &error,
            CanonicalProgramCheckError::SourceCheck {
                error: SourceCheckError::Unsupported(
                    UnsupportedSourceSyntax::MissingVariableInitializer(_)
                ),
                ..
            }
        ),
        "{error:?}"
    );
}

#[test]
fn both_strict_property_options_stop_at_the_uninitialized_class_field() {
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

    let error = Program::try_new_with_canonical_checker(
        &fs,
        "/project",
        &["ambiguousOverloadResolution.ts".to_owned()],
        pinned_strict_property_options(),
    )
    .unwrap_err();

    assert_eq!(
        error.failure_class(),
        CanonicalProgramCheckFailureClass::Unsupported {
            capability_code: "E00.SOURCE_SYNTAX",
        }
    );
    assert!(
        matches!(
            &error,
            CanonicalProgramCheckError::SourceCheck {
                error: SourceCheckError::Unsupported(UnsupportedSourceSyntax::Class(_)),
                ..
            }
        ),
        "{error:?}"
    );
}

#[test]
fn definite_field_variant_advances_under_both_options_to_uninitialized_variable() {
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

    let error = Program::try_new_with_canonical_checker(
        &fs,
        "/project",
        &["ambiguousOverloadResolution.ts".to_owned()],
        pinned_strict_property_options(),
    )
    .unwrap_err();

    assert_eq!(
        error.failure_class(),
        CanonicalProgramCheckFailureClass::Unsupported {
            capability_code: "E00.SOURCE_SYNTAX",
        }
    );
    assert!(
        matches!(
            &error,
            CanonicalProgramCheckError::SourceCheck {
                error: SourceCheckError::Unsupported(
                    UnsupportedSourceSyntax::MissingVariableInitializer(_)
                ),
                ..
            }
        ),
        "{error:?}"
    );
}
