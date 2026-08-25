use ts_compiler::Program;
use ts_options::{CompilerOptions, ModuleKind, ScriptTarget};
use ts_vfs::{FileSystem, MemoryFileSystem};

fn helper_options() -> CompilerOptions {
    CompilerOptions {
        module: ModuleKind::CommonJs,
        module_specified: true,
        target: ScriptTarget::Es2015,
        import_helpers: true,
        lib: Some(vec!["es5".to_owned()]),
        ..CompilerOptions::default()
    }
}

fn helper_filesystem(exports: &str) -> MemoryFileSystem {
    let filesystem = MemoryFileSystem::new(true);
    filesystem
        .write_file(
            "/project/dependency.ts",
            "export const value: number = 1; export { value as default };\n",
        )
        .unwrap();
    filesystem
        .write_file(
            "/project/node_modules/tslib/package.json",
            r#"{"name":"tslib","main":"tslib.js","typings":"tslib.d.ts"}"#,
        )
        .unwrap();
    filesystem
        .write_file("/project/node_modules/tslib/tslib.d.ts", exports)
        .unwrap();
    filesystem
}

#[test]
fn missing_commonjs_helper_package_reports_exact_ts2354_at_the_import() {
    let filesystem = MemoryFileSystem::new(true);
    filesystem
        .write_file(
            "/project/dependency.ts",
            "export const value: number = 1; export { value as default };\n",
        )
        .unwrap();
    let source = concat!(
        "import selected from './dependency';\n",
        "export const message = selected;\n",
    );
    filesystem.write_file("/project/main.ts", source).unwrap();

    let program = Program::try_new_with_canonical_checker(
        &filesystem,
        "/project",
        &["main.ts".to_owned()],
        helper_options(),
    )
    .unwrap();

    let [diagnostic] = program.diagnostics() else {
        panic!(
            "expected exactly one missing tslib diagnostic: {:?}",
            program.diagnostics(),
        )
    };
    assert_eq!(diagnostic.file_name.as_deref(), Some("/project/main.ts"));
    assert_eq!(diagnostic.code, Some(2354));
    assert_eq!(
        diagnostic.message,
        "This syntax requires an imported helper but module 'tslib' cannot be found.",
    );
    let range = diagnostic.range.unwrap();
    let start = usize::try_from(range.start.get()).unwrap();
    let end = usize::try_from(range.end.get()).unwrap();
    assert_eq!(&source[start..end], "import selected from './dependency';");
    assert!(
        program
            .source_file("/project/node_modules/tslib/tslib.d.ts")
            .is_none()
    );
}

#[test]
fn missing_commonjs_import_helpers_report_exact_ordered_ts2343_diagnostics() {
    let filesystem = helper_filesystem("export declare const notAHelper: any;\n");
    filesystem
        .write_file(
            "/project/main.ts",
            "import selected from './dependency';\nexport const message = selected;\n",
        )
        .unwrap();
    filesystem
        .write_file(
            "/project/combined.ts",
            concat!(
                "import selected, * as dependency from './dependency';\n",
                "export const message = selected;\n",
                "export const namespaceMessage = dependency.default;\n",
            ),
        )
        .unwrap();

    let program = Program::try_new_with_canonical_checker(
        &filesystem,
        "/project",
        &["main.ts".to_owned(), "combined.ts".to_owned()],
        helper_options(),
    )
    .unwrap();

    assert!(
        program
            .source_file("/project/node_modules/tslib/tslib.d.ts")
            .is_some()
    );
    assert_eq!(
        program
            .diagnostics()
            .iter()
            .map(|diagnostic| (
                diagnostic.file_name.as_deref(),
                diagnostic.code,
                diagnostic.message.as_str(),
            ))
            .collect::<Vec<_>>(),
        [
            (
                Some("/project/combined.ts"),
                Some(2343),
                "This syntax requires an imported helper named '__importStar' which does not exist in 'tslib'. Consider upgrading your version of 'tslib'.",
            ),
            (
                Some("/project/main.ts"),
                Some(2343),
                "This syntax requires an imported helper named '__importDefault' which does not exist in 'tslib'. Consider upgrading your version of 'tslib'.",
            ),
        ],
    );
    for diagnostic in program.diagnostics() {
        let source = program
            .source_file(diagnostic.file_name.as_deref().unwrap())
            .unwrap();
        let range = diagnostic.range.unwrap();
        let start = usize::try_from(range.start.get()).unwrap();
        let end = usize::try_from(range.end.get()).unwrap();
        assert!(source.source_text[start..end].starts_with("import "));
    }
}

#[test]
fn available_commonjs_import_helpers_do_not_produce_diagnostics() {
    let filesystem = helper_filesystem(concat!(
        "export declare const __importDefault: any;\n",
        "export declare const __importStar: any;\n",
    ));
    filesystem
        .write_file(
            "/project/main.ts",
            concat!(
                "import selected, * as dependency from './dependency';\n",
                "export const value = selected;\n",
                "export const namespaced = dependency.default;\n",
            ),
        )
        .unwrap();

    let program = Program::try_new_with_canonical_checker(
        &filesystem,
        "/project",
        &["main.ts".to_owned()],
        helper_options(),
    )
    .unwrap();

    assert!(
        program.diagnostics().is_empty(),
        "{:?}",
        program.diagnostics()
    );
}

#[test]
fn unused_or_disabled_commonjs_import_helpers_remain_unchecked() {
    for (source, enabled) in [
        ("import selected from './dependency';\n", true),
        (
            "import selected from './dependency';\nexport const value = selected;\n",
            false,
        ),
    ] {
        let filesystem = helper_filesystem("export declare const notAHelper: any;\n");
        filesystem.write_file("/project/main.ts", source).unwrap();
        let mut options = helper_options();
        options.import_helpers = enabled;

        let program = Program::try_new_with_canonical_checker(
            &filesystem,
            "/project",
            &["main.ts".to_owned()],
            options,
        )
        .unwrap();

        assert!(
            program.diagnostics().is_empty(),
            "enabled={enabled}: {:?}",
            program.diagnostics()
        );
        assert!(
            program
                .source_file("/project/node_modules/tslib/tslib.d.ts")
                .is_none()
        );
    }
}
