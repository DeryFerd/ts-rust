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
fn canonical_program_checks_direct_ambient_variables_and_forward_reads() {
    let fs = MemoryFileSystem::new(true);
    fs.write_file(
        "/project/main.ts",
        concat!(
            "export {};\n",
            "const beforeConst: number = ambientConst;\n",
            "const beforeLet: string = ambientLet;\n",
            "const beforeVar: boolean = ambientVar;\n",
            "declare const ambientConst: number;\n",
            "declare let ambientLet: string;\n",
            "declare var ambientVar: boolean;\n",
            "const afterConst: number = ambientConst;\n",
            "const afterLet: string = ambientLet;\n",
            "const afterVar: boolean = ambientVar;\n",
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
fn canonical_program_keeps_unannotated_ambient_variable_as_a_typed_boundary() {
    let fs = MemoryFileSystem::new(true);
    fs.write_file("/project/main.ts", "export {};\ndeclare const missing;\n")
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
