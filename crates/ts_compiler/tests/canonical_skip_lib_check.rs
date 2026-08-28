use ts_compiler::{Program, ProgramGraphResolutionKind};
use ts_options::{CompilerOptions, ScriptTarget};
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

#[test]
fn canonical_skip_lib_check_matches_processing_diagnostic_fixture() {
    let fs = MemoryFileSystem::new(true);
    // These are the unchanged virtual files from processingDiagnosticSkipLibCheck.ts.
    for (file, source) in [
        (
            "/node_modules/foo/index.d.ts",
            concat!(
                "/// <reference types=\"cookie-session\"/>\r\n",
                "export const foo = 1;\r\n\r\n",
            ),
        ),
        (
            "/node_modules/foo/package.json",
            concat!(
                "{\r\n",
                "    \"name\": \"foo\",\r\n",
                "    \"version\": \"1.0.0\",\r\n",
                "    \"types\": \"index.d.ts\"\r\n",
                "}\r\n",
            ),
        ),
        (
            "/index.ts",
            "import { foo } from 'foo';\r\nconst y = foo;\r\n\r\n",
        ),
        (
            "/tsconfig.json",
            concat!(
                "{\r\n",
                "    \"compilerOptions\": {\r\n",
                "        \"strict\": true,\r\n",
                "        \"skipLibCheck\": true\r\n",
                "    }\r\n",
                "}",
            ),
        ),
    ] {
        fs.write_file(file, source).unwrap();
    }
    // Use the baseline harness's explicit root and default target.
    let (program, checked) = Program::try_new_with_canonical_checker_and_queries_with_config_path(
        &fs,
        "/.src",
        &["/index.ts".to_owned()],
        CompilerOptions {
            target: ScriptTarget::Es2025,
            strict: true,
            strict_specified: true,
            skip_lib_check: true,
            ..CompilerOptions::default()
        },
        Some("/tsconfig.json"),
        |_, _| (),
    )
    .unwrap();
    assert_eq!(checked, Some(()));
    assert!(
        program.diagnostics().is_empty(),
        "{:?}",
        program.diagnostics()
    );
    assert!(
        program
            .source_file("/node_modules/foo/index.d.ts")
            .is_some()
    );
    let graph = program.project_graph_snapshot();
    let reference = graph
        .resolutions
        .iter()
        .find(|resolution| {
            resolution.request.kind == ProgramGraphResolutionKind::TypeReference
                && resolution.request.specifier == "cookie-session"
        })
        .unwrap();
    assert_eq!(
        reference.request.containing_file,
        "/node_modules/foo/index.d.ts"
    );
    assert!(reference.result.resolved.is_none());
}
