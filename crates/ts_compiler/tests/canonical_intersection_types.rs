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
fn canonical_program_checks_direct_intersection_composition_and_reads() {
    let fs = MemoryFileSystem::new(true);
    fs.write_file(
        "/project/main.ts",
        concat!(
            "export {};\n",
            "interface Left { left: string; shared: string }\n",
            "interface Right { right: number; shared: string }\n",
            "type Both = Left & Right;\n",
            "type Full = { left: string; right: number; shared: string };\n",
            "const full: Full = { left: \"left\", right: 1, shared: \"shared\" };\n",
            "const both: Both = full;\n",
            "const left: string = both.left;\n",
            "const right: number = both.right;\n",
            "const shared: string = both.shared;\n",
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
fn canonical_program_keeps_optional_intersection_properties_as_a_typed_boundary() {
    let fs = MemoryFileSystem::new(true);
    fs.write_file(
        "/project/main.ts",
        "export {};\ntype Unsupported = { value?: string } & { other: number };\n",
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
            capability_code: "T06.TYPE_NODE",
        }
    );
}
