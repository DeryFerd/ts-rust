use ts_compiler::Program;
use ts_options::CompilerOptions;
use ts_vfs::{FileSystem, MemoryFileSystem};

#[test]
fn canonical_global_interface_merge_is_a_typed_boundary_not_a_panic() {
    let fs = MemoryFileSystem::new(true);
    fs.write_file(
        "/project/main.ts",
        concat!(
            "interface Node { ",
            "children?: readonly Node[]; ",
            "index?: number; ",
            "}",
        ),
    )
    .unwrap();

    let Err(error) = Program::try_new_with_canonical_checker(
        &fs,
        "/project",
        &["main.ts".to_owned()],
        CompilerOptions {
            lib: Some(vec!["es5".to_owned(), "dom".to_owned()]),
            skip_lib_check: true,
            ..CompilerOptions::default()
        },
    ) else {
        panic!("expected an unsupported global interface merge");
    };

    assert!(error.is_unsupported_boundary(), "{error:?}");
}
