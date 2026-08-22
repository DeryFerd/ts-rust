use ts_compiler::Program;
use ts_options::{CompilerOptions, ModuleKind, ModuleResolutionKind};
use ts_vfs::{FileSystem, MemoryFileSystem};

fn javascript_options() -> CompilerOptions {
    CompilerOptions {
        allow_js: true,
        module: ModuleKind::EsNext,
        module_specified: true,
        module_resolution: ModuleResolutionKind::Bundler,
        lib: Some(vec!["es5".to_owned()]),
        ..CompilerOptions::default()
    }
}

#[test]
fn canonical_program_binds_javascript_scripts_and_es_modules() {
    for (name, source) in [
        ("input.js", "const value = 1;\n"),
        ("module.js", "export const value = 1;\n"),
        ("view.jsx", "export const value = <div />;\n"),
    ] {
        let filesystem = MemoryFileSystem::new(true);
        let path = format!("/project/{name}");
        filesystem.write_file(&path, source).unwrap();

        let program = Program::try_new_with_canonical_checker(
            &filesystem,
            "/project",
            &[name.to_owned()],
            javascript_options(),
        )
        .unwrap_or_else(|error| panic!("failed to bind {name}: {error:?}"));

        assert!(program.source_file(&path).is_some());
        assert!(
            program.diagnostics().is_empty(),
            "{:?}",
            program.diagnostics()
        );
    }
}

#[test]
fn unchecked_javascript_es_modules_share_one_bundler_graph() {
    let filesystem = MemoryFileSystem::new(true);
    filesystem
        .write_file(
            "/project/importer.js",
            "import { value } from './target.js';\nexport const copy = value;\n",
        )
        .unwrap();
    filesystem
        .write_file("/project/target.js", "export const value = 1;\n")
        .unwrap();

    let program = Program::try_new_with_canonical_checker(
        &filesystem,
        "/project",
        &["importer.js".to_owned()],
        javascript_options(),
    )
    .unwrap();

    assert!(program.source_file("/project/importer.js").is_some());
    assert!(program.source_file("/project/target.js").is_some());
    assert!(
        program.diagnostics().is_empty(),
        "{:?}",
        program.diagnostics()
    );
}

#[test]
fn unchecked_javascript_keeps_typescript_source_diagnostics() {
    let filesystem = MemoryFileSystem::new(true);
    filesystem
        .write_file(
            "/project/input.js",
            "/** @type {string} */ const value = 1;\n",
        )
        .unwrap();
    filesystem
        .write_file("/project/input.ts", "const typed: string = 1;\n")
        .unwrap();

    let program = Program::try_new_with_canonical_checker(
        &filesystem,
        "/project",
        &["input.js".to_owned(), "input.ts".to_owned()],
        javascript_options(),
    )
    .unwrap();

    let [diagnostic] = program.diagnostics() else {
        panic!(
            "expected one TypeScript diagnostic: {:?}",
            program.diagnostics()
        );
    };
    assert_eq!(diagnostic.file_name.as_deref(), Some("/project/input.ts"));
    assert_eq!(diagnostic.code, Some(2322));
}
