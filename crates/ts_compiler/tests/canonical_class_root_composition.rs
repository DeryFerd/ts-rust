use ts_compiler::Program;
use ts_options::CompilerOptions;
use ts_vfs::{FileSystem, MemoryFileSystem};

#[test]
fn admitted_class_method_keeps_the_earlier_files_canonical_diagnostic() {
    let fs = MemoryFileSystem::new(true);
    fs.write_file("/project/first.ts", r#"const first: number = "wrong";"#)
        .unwrap();
    fs.write_file(
        "/project/later.ts",
        "class Later { method(value: string) {} }",
    )
    .unwrap();
    let program = Program::try_new_with_canonical_checker(
        &fs,
        "/project",
        &["first.ts".to_owned(), "later.ts".to_owned()],
        CompilerOptions {
            lib: Some(vec!["es5".to_owned()]),
            ..CompilerOptions::default()
        },
    )
    .unwrap();

    let [diagnostic] = program.diagnostics() else {
        panic!("the admitted later class must retain the earlier assignment diagnostic");
    };
    assert_eq!(diagnostic.code, Some(2322));
}
