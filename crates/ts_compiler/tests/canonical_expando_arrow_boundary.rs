use ts_compiler::{CanonicalProgramCheckFailureClass, Program};
use ts_options::CompilerOptions;
use ts_vfs::{FileSystem, MemoryFileSystem};

#[test]
fn canonical_expando_arrow_is_a_typed_boundary_not_an_invariant() {
    let fs = MemoryFileSystem::new(true);
    fs.write_file(
        "/project/main.ts",
        concat!("const foo = () => {};\n", "foo.bar = 42;\n", "export {};\n",),
    )
    .unwrap();

    let error = Program::try_new_with_canonical_checker(
        &fs,
        "/project",
        &["main.ts".to_owned()],
        CompilerOptions {
            declaration: true,
            lib: Some(vec!["es5".to_owned()]),
            ..CompilerOptions::default()
        },
    )
    .unwrap_err();

    assert_eq!(
        error.failure_class(),
        CanonicalProgramCheckFailureClass::Unsupported {
            capability_code: "E00.SOURCE_SYNTAX",
        }
    );
}
