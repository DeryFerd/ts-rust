use ts_compiler::Program;
use ts_options::CompilerOptions;
use ts_vfs::{FileSystem, MemoryFileSystem};

#[test]
fn canonical_skip_lib_check_suppresses_declaration_bind_diagnostics() {
    let fs = MemoryFileSystem::new(true);
    fs.write_file(
        "/project/target.d.ts",
        concat!(
            "export declare const value: number; ",
            "declare const duplicate: number; ",
            "declare const duplicate: string;",
        ),
    )
    .unwrap();

    let program = Program::try_new_with_canonical_checker(
        &fs,
        "/project",
        &["target.d.ts".to_owned()],
        CompilerOptions {
            lib: Some(vec!["es5".to_owned()]),
            skip_lib_check: true,
            ..CompilerOptions::default()
        },
    )
    .unwrap();

    assert!(
        program.diagnostics().is_empty(),
        "{:?}",
        program.diagnostics()
    );
}
