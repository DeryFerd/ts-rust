use ts_ast::{NodeData, NodeRef};
use ts_checker::semantic::CanonicalModuleResolutionMode;
use ts_compiler::{CanonicalModuleResolutionLookup, Program};
use ts_options::{CompilerOptions, ModuleKind, ModuleResolutionKind};
use ts_vfs::{FileSystem, MemoryFileSystem};

fn module_options(module: ModuleKind, module_resolution: ModuleResolutionKind) -> CompilerOptions {
    CompilerOptions {
        module,
        module_specified: module != ModuleKind::None,
        module_resolution,
        lib: Some(vec!["es5".to_owned()]),
        ..CompilerOptions::default()
    }
}

fn specifier(program: &Program, file_name: &str, expected: &str) -> NodeRef {
    let source = program.source_file(file_name).expect("module source");
    source
        .parse
        .arena
        .iter()
        .find_map(|(node, record)| match &record.data {
            NodeData::StringLiteral(text) if text.text == expected => source.node_ref(node),
            _ => None,
        })
        .expect("module specifier")
}

#[test]
fn canonical_imports_publish_exact_modes_for_commonjs_and_esm() {
    for (module, resolution, expected_mode) in [
        (
            ModuleKind::CommonJs,
            ModuleResolutionKind::Node10,
            CanonicalModuleResolutionMode::CommonJs,
        ),
        (
            ModuleKind::EsNext,
            ModuleResolutionKind::Node10,
            CanonicalModuleResolutionMode::Esm,
        ),
        (
            ModuleKind::None,
            ModuleResolutionKind::Node10,
            CanonicalModuleResolutionMode::Esm,
        ),
        (
            ModuleKind::Preserve,
            ModuleResolutionKind::Bundler,
            CanonicalModuleResolutionMode::Esm,
        ),
    ] {
        let filesystem = MemoryFileSystem::new(true);
        filesystem
            .write_file("/project/target.ts", "export const value: number = 1;\n")
            .unwrap();
        filesystem
            .write_file(
                "/project/importer.ts",
                "import { value } from './target';\nconst incorrect: string = value;\n",
            )
            .unwrap();

        let (program, modes) = Program::try_new_with_canonical_checker_and_queries(
            &filesystem,
            "/project",
            &["importer.ts".to_owned()],
            module_options(module, resolution),
            |program, queries| {
                let import = specifier(program, "/project/importer.ts", "./target");
                let CanonicalModuleResolutionLookup::Resolved(resolved) =
                    queries.module_resolution(import)
                else {
                    panic!("missing canonical module resolution for {module:?}/{resolution:?}");
                };
                (resolved.usage_mode(), resolved.target_mode())
            },
        )
        .unwrap_or_else(|error| panic!("failed {module:?}/{resolution:?}: {error:?}"));

        assert_eq!(modes, Some((expected_mode, expected_mode)));
        let [diagnostic] = program.diagnostics() else {
            panic!(
                "expected one import assignment error: {:?}",
                program.diagnostics()
            );
        };
        assert_eq!(diagnostic.code, Some(2322));
        assert_eq!(
            diagnostic.file_name.as_deref(),
            Some("/project/importer.ts")
        );
    }
}

#[test]
fn node_next_resolutions_follow_the_nearest_package_type() {
    for (package_type, expected_mode) in [
        ("module", CanonicalModuleResolutionMode::Esm),
        ("commonjs", CanonicalModuleResolutionMode::CommonJs),
    ] {
        let filesystem = MemoryFileSystem::new(true);
        filesystem
            .write_file(
                "/project/package.json",
                &format!("{{\"type\":\"{package_type}\"}}"),
            )
            .unwrap();
        filesystem
            .write_file("/project/target.ts", "export const value: number = 1;\n")
            .unwrap();
        filesystem
            .write_file(
                "/project/importer.ts",
                "import { value } from './target.js';\nconst copy: number = value;\n",
            )
            .unwrap();

        let (program, modes) = Program::try_new_with_canonical_checker_and_queries(
            &filesystem,
            "/project",
            &["importer.ts".to_owned()],
            module_options(ModuleKind::NodeNext, ModuleResolutionKind::NodeNext),
            |program, queries| {
                let import = specifier(program, "/project/importer.ts", "./target.js");
                let CanonicalModuleResolutionLookup::Resolved(resolved) =
                    queries.module_resolution(import)
                else {
                    panic!("missing NodeNext module resolution for {package_type}");
                };
                (resolved.usage_mode(), resolved.target_mode())
            },
        )
        .unwrap_or_else(|error| panic!("failed NodeNext {package_type}: {error:?}"));

        assert_eq!(modes, Some((expected_mode, expected_mode)));
        assert!(
            program.diagnostics().is_empty(),
            "{:?}",
            program.diagnostics()
        );
    }
}

#[test]
fn unresolved_url_side_effect_imports_report_ts2882_with_default_options() {
    const SPECIFIER: &str = "https://deno.land/std@0.208.0/path/mod.ts";
    for node_modules_exist in [false, true] {
        let filesystem = MemoryFileSystem::new(true);
        if node_modules_exist {
            filesystem
                .write_file(
                    "/node_modules/foo/package.json",
                    r#"{"name":"foo","version":"1.0.0"}"#,
                )
                .unwrap();
            filesystem
                .write_file(
                    "/node_modules/foo/index.d.ts",
                    "export declare function useFoo(): string;\n",
                )
                .unwrap();
        }
        filesystem
            .write_file("/src/index.ts", &format!("import \"{SPECIFIER}\"\n"))
            .unwrap();

        let program = Program::try_new_with_canonical_checker(
            &filesystem,
            "/",
            &["/src/index.ts".to_owned()],
            CompilerOptions {
                lib: Some(vec!["es5".to_owned()]),
                ..CompilerOptions::default()
            },
        )
        .unwrap();

        let [diagnostic] = program.diagnostics() else {
            panic!(
                "expected one URL import diagnostic with node_modules={node_modules_exist}: {:?}",
                program.diagnostics()
            );
        };
        assert_eq!(diagnostic.file_name.as_deref(), Some("/src/index.ts"));
        assert_eq!(diagnostic.code, Some(2882));
        assert_eq!(
            diagnostic.message,
            format!(
                "Cannot find module or type declarations for side-effect import of '{SPECIFIER}'."
            )
        );
        let range = diagnostic.range.expect("URL import diagnostic range");
        assert_eq!(range.start.get(), 7);
        assert_eq!(
            range.end.get(),
            u32::try_from(7 + SPECIFIER.len() + 2).unwrap()
        );
    }
}

#[test]
fn disabled_side_effect_import_checking_also_suppresses_url_diagnostics() {
    let filesystem = MemoryFileSystem::new(true);
    filesystem
        .write_file(
            "/src/index.ts",
            "import \"https://deno.land/std@0.208.0/path/mod.ts\";\n",
        )
        .unwrap();

    let program = Program::try_new_with_canonical_checker(
        &filesystem,
        "/",
        &["/src/index.ts".to_owned()],
        CompilerOptions {
            lib: Some(vec!["es5".to_owned()]),
            no_unchecked_side_effect_imports: false,
            no_unchecked_side_effect_imports_specified: true,
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
fn javascript_emission_reports_ts5055_without_overwriting_its_input() {
    const SOURCE: &str = "export const value = 1;\n";
    let filesystem = MemoryFileSystem::new(true);
    filesystem.write_file("/project/input.js", SOURCE).unwrap();
    let program = Program::new_with_options(
        &filesystem,
        "/project",
        &["input.js".to_owned()],
        CompilerOptions {
            allow_js: true,
            no_lib: true,
            ..CompilerOptions::default()
        },
    );

    let emitted = program.emit();
    assert!(emitted.files.is_empty(), "{:?}", emitted.files);
    let [diagnostic] = emitted.diagnostics.as_slice() else {
        panic!(
            "expected one output collision diagnostic: {:?}",
            emitted.diagnostics
        );
    };
    assert_eq!(diagnostic.code, Some(5055));
    assert_eq!(
        diagnostic.message,
        "Cannot write file '/project/input.js' because it would overwrite input file."
    );
    assert_eq!(filesystem.read_file("/project/input.js").unwrap(), SOURCE);
}

#[test]
fn ordinary_declaration_modules_are_checked_without_skip_lib_check() {
    let filesystem = MemoryFileSystem::new(true);
    filesystem
        .write_file(
            "/project/target.d.ts",
            "export interface Shape { value: string }\n",
        )
        .unwrap();
    filesystem
        .write_file(
            "/project/importer.ts",
            concat!(
                "import type { Shape } from './target';\n",
                "const value: Shape = { value: 'ok' };\n",
            ),
        )
        .unwrap();

    let program = Program::try_new_with_canonical_checker(
        &filesystem,
        "/project",
        &["importer.ts".to_owned()],
        module_options(ModuleKind::EsNext, ModuleResolutionKind::Node10),
    )
    .unwrap();

    assert!(program.source_file("/project/target.d.ts").is_some());
    assert!(
        program.diagnostics().is_empty(),
        "{:?}",
        program.diagnostics()
    );
}

#[test]
fn fixed_module_extensions_are_admitted_with_their_declared_formats() {
    for (extension, target_name) in [("mts", "target.mts"), ("cts", "target.cts")] {
        let filesystem = MemoryFileSystem::new(true);
        let source = format!("export const value: number = 1; // {extension}\n");
        filesystem
            .write_file(&format!("/project/{target_name}"), &source)
            .unwrap();

        let program = Program::try_new_with_canonical_checker(
            &filesystem,
            "/project",
            &[target_name.to_owned()],
            module_options(ModuleKind::EsNext, ModuleResolutionKind::Node10),
        )
        .unwrap_or_else(|error| panic!("failed to check {target_name}: {error:?}"));

        assert!(
            program
                .source_file(&format!("/project/{target_name}"))
                .is_some()
        );
        assert!(
            program.diagnostics().is_empty(),
            "{:?}",
            program.diagnostics()
        );
    }
}

#[test]
fn malformed_jsdoc_import_type_does_not_trigger_module_resolution() {
    let filesystem = MemoryFileSystem::new(true);
    filesystem
        .write_file(
            "/project/input.js",
            "/** @type {@import('missing').Type} */\nlet value;\n",
        )
        .unwrap();
    let mut options = module_options(ModuleKind::EsNext, ModuleResolutionKind::Bundler);
    options.allow_js = true;
    options.check_js = true;
    options.no_emit = true;

    let program = Program::try_new_with_canonical_checker(
        &filesystem,
        "/project",
        &["input.js".to_owned()],
        options,
    )
    .unwrap();

    assert!(
        program
            .diagnostics()
            .iter()
            .any(|diagnostic| diagnostic.code == Some(1110)),
        "{:?}",
        program.diagnostics()
    );
    assert!(
        program
            .diagnostics()
            .iter()
            .all(|diagnostic| diagnostic.code != Some(2307)),
        "{:?}",
        program.diagnostics()
    );
}

#[test]
fn javascript_root_without_allow_js_reports_exact_ts6504() {
    let filesystem = MemoryFileSystem::new(true);
    filesystem
        .write_file("/project/input.js", "var value;\n")
        .unwrap();
    let mut options = module_options(ModuleKind::EsNext, ModuleResolutionKind::Bundler);
    options.allow_js = false;
    options.allow_js_specified = true;
    options.check_js = true;
    options.no_emit = true;

    let program = Program::try_new_with_canonical_checker(
        &filesystem,
        "/project",
        &["input.js".to_owned()],
        options,
    )
    .unwrap();

    assert_eq!(
        program
            .diagnostics()
            .iter()
            .filter_map(|diagnostic| diagnostic.code)
            .collect::<Vec<_>>(),
        [5052, 6504]
    );
    let diagnostic = program
        .diagnostics()
        .iter()
        .find(|diagnostic| diagnostic.code == Some(6504))
        .expect("JavaScript root diagnostic");
    assert_eq!(
        diagnostic.message,
        concat!(
            "File 'input.js' is a JavaScript file. ",
            "Did you mean to enable the 'allowJs' option?\n",
            "  The file is in the program because:\n",
            "    Root file specified for compilation",
        )
    );
    assert!(program.source_file("/project/input.js").is_none());
}

#[test]
fn source_map_paths_are_relative_to_the_emitted_map_directory() {
    let filesystem = MemoryFileSystem::new(true);
    filesystem
        .write_file("/project/src/nested/main.ts", "export const value = 1;\n")
        .unwrap();
    let program = Program::new_with_options(
        &filesystem,
        "/project",
        &["src/nested/main.ts".to_owned()],
        CompilerOptions {
            out_dir: Some("/project/dist".to_owned()),
            root_dir: Some("/project/src".to_owned()),
            source_map: true,
            no_lib: true,
            ..CompilerOptions::default()
        },
    );
    let emitted = program.emit();
    let map = emitted
        .files
        .iter()
        .find(|file| file.file_name == "/project/dist/nested/main.js.map")
        .expect("external source map");
    let json: serde_json::Value = serde_json::from_str(&map.text).unwrap();

    assert_eq!(
        json["sources"],
        serde_json::json!(["../../src/nested/main.ts"])
    );
}

#[test]
fn declaration_maps_use_relative_paths_without_inlining_source_text() {
    const SOURCE: &str = "export const greeting = 'hello';\n";
    let filesystem = MemoryFileSystem::new(true);
    filesystem
        .write_file("/project/src/nested/api.ts", SOURCE)
        .unwrap();
    let program = Program::new_with_options(
        &filesystem,
        "/project",
        &["src/nested/api.ts".to_owned()],
        CompilerOptions {
            declaration: true,
            declaration_dir: Some("/project/types".to_owned()),
            declaration_map: true,
            inline_sources: true,
            out_dir: Some("/project/dist".to_owned()),
            root_dir: Some("/project/src".to_owned()),
            source_map: true,
            no_lib: true,
            ..CompilerOptions::default()
        },
    );
    let emitted = program.emit();
    let javascript = emitted
        .files
        .iter()
        .find(|file| file.file_name == "/project/dist/nested/api.js")
        .expect("JavaScript output");
    let javascript_map = emitted
        .files
        .iter()
        .find(|file| file.file_name == "/project/dist/nested/api.js.map")
        .expect("JavaScript source map");
    let declaration = emitted
        .files
        .iter()
        .find(|file| file.file_name == "/project/types/nested/api.d.ts")
        .expect("declaration output");
    let declaration_map = emitted
        .files
        .iter()
        .find(|file| file.file_name == "/project/types/nested/api.d.ts.map")
        .expect("declaration source map");
    let javascript_json: serde_json::Value = serde_json::from_str(&javascript_map.text).unwrap();
    let declaration_json: serde_json::Value = serde_json::from_str(&declaration_map.text).unwrap();

    assert_eq!(
        javascript_json["sources"],
        serde_json::json!(["../../src/nested/api.ts"])
    );
    assert_eq!(
        declaration_json["sources"],
        serde_json::json!(["../../src/nested/api.ts"])
    );
    assert_eq!(
        javascript_json["sourcesContent"],
        serde_json::json!([SOURCE])
    );
    assert!(declaration_json.get("sourcesContent").is_none());
    assert!(javascript.text.ends_with("//# sourceMappingURL=api.js.map"));
    assert!(
        declaration
            .text
            .ends_with("//# sourceMappingURL=api.d.ts.map")
    );
}

#[test]
fn preceding_comment_directives_suppress_errors_and_report_unused_expectations() {
    let filesystem = MemoryFileSystem::new(true);
    let source = concat!(
        "// @ts-ignore\n",
        "const ignored: string = 1;\n",
        "// @ts-expect-error\n",
        "// explanatory comment\n",
        "\n",
        "const expected: string = 2;\n",
        "// @ts-expect-error\n",
        "const valid: string = 'ok';\n",
        "/* @ts-ignore */\n",
        "const blockIgnored: string = 3;\n",
        "/* @ts-ignore */\n",
        "/* intervening block comment */\n",
        "const unsuppressed: string = 4;\n",
    );
    filesystem.write_file("/project/input.ts", source).unwrap();

    let program = Program::try_new_with_canonical_checker(
        &filesystem,
        "/project",
        &["input.ts".to_owned()],
        module_options(ModuleKind::EsNext, ModuleResolutionKind::Node10),
    )
    .unwrap();

    assert_eq!(
        program
            .diagnostics()
            .iter()
            .filter_map(|diagnostic| diagnostic.code)
            .collect::<Vec<_>>(),
        [2578, 2322],
        "{:?}",
        program.diagnostics()
    );
    assert_eq!(
        program.diagnostics()[0].message,
        "Unused '@ts-expect-error' directive."
    );
}

#[test]
fn typescript_nocheck_suppresses_bind_errors_and_unused_expectations() {
    let filesystem = MemoryFileSystem::new(true);
    filesystem
        .write_file(
            "/project/input.ts",
            concat!(
                "// @ts-nocheck\n",
                "// @ts-expect-error\n",
                "const valid: string = 'ok';\n",
                "const duplicate = 1;\n",
                "const duplicate = 2;\n",
                "const invalid: string = 1;\n",
            ),
        )
        .unwrap();

    let canonical = Program::try_new_with_canonical_checker(
        &filesystem,
        "/project",
        &["input.ts".to_owned()],
        module_options(ModuleKind::EsNext, ModuleResolutionKind::Node10),
    )
    .unwrap();
    assert!(
        canonical.diagnostics().is_empty(),
        "{:?}",
        canonical.diagnostics()
    );

    let legacy = Program::new_with_options(
        &filesystem,
        "/project",
        &["input.ts".to_owned()],
        module_options(ModuleKind::EsNext, ModuleResolutionKind::Node10),
    );
    assert!(
        legacy.diagnostics().is_empty(),
        "{:?}",
        legacy.diagnostics()
    );
}

#[test]
fn leading_nocheck_directives_support_all_ecmascript_line_breaks() {
    for line_break in ["\n", "\r\n", "\r", "\u{2028}", "\u{2029}"] {
        let filesystem = MemoryFileSystem::new(true);
        let source =
            format!("\u{feff}// @ts-nocheck{line_break}const invalid: string = 1;{line_break}");
        filesystem.write_file("/project/input.ts", &source).unwrap();

        let program = Program::try_new_with_canonical_checker(
            &filesystem,
            "/project",
            &["input.ts".to_owned()],
            module_options(ModuleKind::EsNext, ModuleResolutionKind::Node10),
        )
        .unwrap();

        assert!(
            program.diagnostics().is_empty(),
            "line break {line_break:?}: {:?}",
            program.diagnostics()
        );
    }
}
