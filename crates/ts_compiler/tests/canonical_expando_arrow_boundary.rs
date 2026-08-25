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

#[test]
fn canonical_program_reports_exact_implicit_any_array_expando_diagnostics() {
    let source = concat!(
        "function f1() {}\n",
        "f1.a = [];\n",
        "const f2 = function () {};\n",
        "f2.a = [];\n",
        "const f3 = () => {};\n",
        "f3.a = [];\n",
        "export {};\n",
    );
    let fs = MemoryFileSystem::new(true);
    fs.write_file("/project/main.ts", source).unwrap();

    let program = Program::try_new_with_canonical_checker(
        &fs,
        "/project",
        &["main.ts".to_owned()],
        CompilerOptions {
            no_emit: true,
            no_implicit_any: true,
            lib: Some(vec!["es5".to_owned()]),
            ..CompilerOptions::default()
        },
    )
    .unwrap();

    assert_eq!(program.diagnostics().len(), 3);
    for (diagnostic, expected) in program.diagnostics().iter().zip(["f1.a", "f2.a", "f3.a"]) {
        assert_eq!(diagnostic.file_name.as_deref(), Some("/project/main.ts"));
        assert_eq!(diagnostic.code, Some(7008));
        assert_eq!(
            diagnostic.message,
            "Member 'a' implicitly has an 'any[]' type.",
        );
        let range = diagnostic.range.unwrap();
        let start = usize::try_from(range.start.get()).unwrap();
        let end = usize::try_from(range.end.get()).unwrap();
        assert_eq!(&source[start..end], expected);
    }
}
