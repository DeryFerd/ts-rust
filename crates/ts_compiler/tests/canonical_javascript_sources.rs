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
        no_emit: true,
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
fn canonical_program_checks_javascript_arrow_expandos() {
    for binding in ["var", "let", "const"] {
        let filesystem = MemoryFileSystem::new(true);
        filesystem
            .write_file(
                "/project/input.js",
                &format!(
                    "{binding} callback = () => {{}};\n\
                     callback.value = 1;\n\
                     const copied = callback.value;\n"
                ),
            )
            .unwrap();
        let mut options = javascript_options();
        options.check_js = true;

        let program = Program::try_new_with_canonical_checker(
            &filesystem,
            "/project",
            &["input.js".to_owned()],
            options,
        )
        .unwrap_or_else(|error| panic!("failed to check {binding} arrow expando: {error:?}"));

        assert!(
            program.diagnostics().is_empty(),
            "{binding}: {:?}",
            program.diagnostics(),
        );
        assert!(program.source_file("/project/input.js").is_some());
    }
}

#[test]
fn canonical_program_honors_javascript_function_expando_jsdoc_annotations() {
    for (value, expected_diagnostic) in [("'ready'", None), ("1", Some(2322))] {
        let filesystem = MemoryFileSystem::new(true);
        filesystem
            .write_file(
                "/project/input.js",
                &format!(
                    "function work() {{}}\n\
                     /** @type {{string}} */\n\
                     work.value = {value};\n\
                     const copied = work.value;\n"
                ),
            )
            .unwrap();
        let mut options = javascript_options();
        options.check_js = true;

        let program = Program::try_new_with_canonical_checker(
            &filesystem,
            "/project",
            &["input.js".to_owned()],
            options,
        )
        .unwrap_or_else(|error| panic!("failed to check annotated function property: {error:?}"));

        assert_eq!(
            program
                .diagnostics()
                .iter()
                .map(|diagnostic| diagnostic.code)
                .collect::<Vec<_>>(),
            expected_diagnostic
                .into_iter()
                .map(Some)
                .collect::<Vec<_>>(),
            "value: {value}",
        );
    }
}

#[test]
fn canonical_program_checks_jsdoc_boolean_constructor_field_assignments() {
    let filesystem = MemoryFileSystem::new(true);
    filesystem
        .write_file(
            "/project/input.js",
            concat!(
                "class C {\n",
                "  constructor() {\n",
                "    /** @type {boolean} */\n",
                "    this.a = true;\n",
                "    this.a = !!this.a;\n",
                "  }\n",
                "}\n",
            ),
        )
        .unwrap();
    let mut options = javascript_options();
    options.check_js = true;
    options.no_implicit_any = true;

    let program = Program::try_new_with_canonical_checker(
        &filesystem,
        "/project",
        &["input.js".to_owned()],
        options,
    )
    .unwrap();

    assert!(
        program.diagnostics().is_empty(),
        "{:?}",
        program.diagnostics()
    );
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
fn javascript_require_of_type_only_export_equals_reports_exact_ts18042() {
    let filesystem = MemoryFileSystem::new(true);
    filesystem
        .write_file(
            "/project/t.ts",
            "type Strings = string[]; export = Strings;\n",
        )
        .unwrap();
    filesystem
        .write_file("/project/main.js", "const t = require(\"./t\");\n")
        .unwrap();

    let program = Program::try_new_with_canonical_checker(
        &filesystem,
        "/project",
        &["main.js".to_owned()],
        CompilerOptions {
            allow_js: true,
            check_js: true,
            module: ModuleKind::CommonJs,
            module_specified: true,
            lib: Some(vec!["es5".to_owned()]),
            no_emit: true,
            ..CompilerOptions::default()
        },
    )
    .unwrap();

    assert!(program.source_file("/project/t.ts").is_some());
    let [diagnostic] = program.diagnostics() else {
        panic!(
            "expected exactly one JavaScript type-only require diagnostic: {:?}",
            program.diagnostics()
        );
    };
    assert_eq!(diagnostic.file_name.as_deref(), Some("/project/main.js"));
    assert_eq!(diagnostic.code, Some(18042));
    assert_eq!(
        diagnostic.message,
        "'t' is a type and cannot be imported in JavaScript files. Use 'import(\"./t\")' in a JSDoc type annotation.",
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

#[test]
fn leading_ts_check_directives_override_global_javascript_checking() {
    for (source, check_js, expect_error) in [
        (
            "// @ts-check\nconst value = true; value.missing;",
            false,
            true,
        ),
        (
            "// @ts-nocheck\nconst value = true; value.missing;",
            true,
            false,
        ),
        (
            "// @ts-check\n// @ts-nocheck\nconst value = true; value.missing;",
            true,
            false,
        ),
        (
            "// @ts-nocheck\n// @ts-check\nconst value = true; value.missing;",
            false,
            true,
        ),
        (
            "const value = true;\n// @ts-check\nvalue.missing;",
            false,
            false,
        ),
        (
            "/* @ts-check */\nconst value = true; value.missing;",
            false,
            false,
        ),
        (
            "/// @ts-check\nconst value = true; value.missing;",
            false,
            true,
        ),
    ] {
        let filesystem = MemoryFileSystem::new(true);
        filesystem.write_file("/project/input.js", source).unwrap();
        let mut options = javascript_options();
        options.check_js = check_js;

        let program =
            Program::new_with_options(&filesystem, "/project", &["input.js".to_owned()], options);
        let actual = program
            .diagnostics()
            .iter()
            .any(|diagnostic| diagnostic.code == Some(2339));
        assert_eq!(actual, expect_error, "source: {source}");
    }
}

#[test]
fn canonical_ts_nocheck_disables_global_javascript_checking() {
    let filesystem = MemoryFileSystem::new(true);
    filesystem
        .write_file(
            "/project/input.js",
            "// @ts-nocheck\nconst value = true; value.missing;\n",
        )
        .unwrap();
    let mut options = javascript_options();
    options.check_js = true;

    let program = Program::try_new_with_canonical_checker(
        &filesystem,
        "/project",
        &["input.js".to_owned()],
        options,
    )
    .unwrap();

    assert!(
        program.diagnostics().is_empty(),
        "{:?}",
        program.diagnostics()
    );
}
