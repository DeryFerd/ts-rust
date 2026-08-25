use ts_compiler::Program;
use ts_options::CompilerOptions;
use ts_vfs::{FileSystem, MemoryFileSystem};

#[test]
fn canonical_program_checks_authenticated_arrow_expandos() {
    let fs = MemoryFileSystem::new(true);
    fs.write_file(
        "/project/main.ts",
        concat!("const foo = () => {};\n", "foo.bar = 42;\n", "export {};\n",),
    )
    .unwrap();

    let program = Program::try_new_with_canonical_checker(
        &fs,
        "/project",
        &["main.ts".to_owned()],
        CompilerOptions {
            declaration: true,
            lib: Some(vec!["es5".to_owned()]),
            ..CompilerOptions::default()
        },
    )
    .unwrap();

    assert!(program.diagnostics().is_empty());

    let source = program.source_file("/project/main.ts").unwrap();
    assert_eq!(source.binding.file_id(), Some(source.id));
    assert!(
        source
            .binding
            .root_scope()
            .unwrap()
            .symbols
            .get("foo")
            .is_some()
    );
}
