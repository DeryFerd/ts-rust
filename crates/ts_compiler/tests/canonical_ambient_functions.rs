use ts_compiler::{CanonicalProgramCheckFailureClass, Program};
use ts_options::{CompilerOptions, ModuleKind, ModuleResolutionKind};
use ts_vfs::{FileSystem, MemoryFileSystem};

fn canonical_options() -> CompilerOptions {
    CompilerOptions {
        module: ModuleKind::EsNext,
        module_specified: true,
        module_resolution: ModuleResolutionKind::Bundler,
        lib: Some(vec!["es5".to_owned()]),
        strict: true,
        ..CompilerOptions::default()
    }
}

#[test]
fn canonical_program_checks_hoisted_local_ambient_function_calls() {
    let fs = MemoryFileSystem::new(true);
    fs.write_file(
        "/project/main.ts",
        concat!(
            "export {};\n",
            "const before: string = formatNumber(1);\n",
            "declare function formatNumber(value: LaterNumber): string;\n",
            "type LaterNumber = number;\n",
            "const after: string = formatNumber(2);\n",
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
fn canonical_program_reports_ambient_function_argument_mismatch() {
    let fs = MemoryFileSystem::new(true);
    fs.write_file(
        "/project/main.ts",
        concat!(
            "export {};\n",
            "declare function takeNumber(value: number): string;\n",
            "const result = takeNumber(\"wrong\");\n",
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

    assert_eq!(
        program
            .diagnostics()
            .iter()
            .map(|diagnostic| diagnostic.code)
            .collect::<Vec<_>>(),
        [Some(2345)]
    );
}

#[test]
fn canonical_program_keeps_optional_generic_ambient_function_as_a_typed_boundary() {
    let fs = MemoryFileSystem::new(true);
    fs.write_file(
        "/project/main.ts",
        "export {};\ndeclare function identity<T>(value?: T): T;\n",
    )
    .unwrap();

    let error = Program::try_new_with_canonical_checker(
        &fs,
        "/project",
        &["main.ts".to_owned()],
        canonical_options(),
    )
    .unwrap_err();

    assert_eq!(
        error.failure_class(),
        CanonicalProgramCheckFailureClass::Unsupported {
            capability_code: "E00.SOURCE_SYNTAX",
        }
    );
}
