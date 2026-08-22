use std::collections::BTreeSet;

use ts_compiler::{Program, ProgramOptionsOverride};
use ts_options::CompilerOptions;
use ts_vfs::{FileSystem, MemoryFileSystem};

#[test]
fn allow_js_discovers_all_supported_javascript_extensions() {
    let fs = MemoryFileSystem::new(true);
    fs.write_file(
        "/project/tsconfig.json",
        r#"{"include":["src/**/*"],"compilerOptions":{"allowJs":true,"noLib":true}}"#,
    )
    .unwrap();
    for (name, source) in [
        ("typed.ts", "export const typed = 1;"),
        ("plain.js", "export const plain = 1;"),
        ("component.jsx", "export const component = 1;"),
        ("module.mjs", "export const moduleValue = 1;"),
        ("common.cjs", "exports.common = 1;"),
    ] {
        fs.write_file(&format!("/project/src/{name}"), source)
            .unwrap();
    }

    let program = Program::from_config(&fs, "/project/tsconfig.json");
    for name in [
        "typed.ts",
        "plain.js",
        "component.jsx",
        "module.mjs",
        "common.cjs",
    ] {
        assert!(
            program
                .source_file(&format!("/project/src/{name}"))
                .is_some(),
            "missing JavaScript project input {name}"
        );
    }
}

#[test]
fn command_line_allow_js_override_controls_project_discovery() {
    let fs = MemoryFileSystem::new(true);
    fs.write_file(
        "/project/tsconfig.json",
        r#"{"include":["src/**/*"],"compilerOptions":{"noLib":true}}"#,
    )
    .unwrap();
    fs.write_file("/project/src/main.ts", "export const typed = 1;")
        .unwrap();
    fs.write_file("/project/src/helper.js", "export const helper = 1;")
        .unwrap();

    let without_override = Program::from_config(&fs, "/project/tsconfig.json");
    assert!(
        without_override
            .source_file("/project/src/helper.js")
            .is_none()
    );

    let with_override = Program::from_config_with_command_line_options(
        &fs,
        "/project/tsconfig.json",
        ProgramOptionsOverride::default(),
        &CompilerOptions {
            allow_js: true,
            ..CompilerOptions::default()
        },
        &BTreeSet::from(["allowjs".to_owned()]),
    );
    assert!(
        with_override
            .source_file("/project/src/helper.js")
            .is_some()
    );
}

#[test]
fn resolve_json_module_only_discovers_explicit_json_include_patterns() {
    let fs = MemoryFileSystem::new(true);
    fs.write_file("/project/src/main.ts", "export const typed = 1;")
        .unwrap();
    fs.write_file("/project/src/settings.json", r#"{"enabled":true}"#)
        .unwrap();
    fs.write_file(
        "/project/tsconfig.json",
        r#"{"include":["src/**/*"],"compilerOptions":{"resolveJsonModule":true,"noLib":true}}"#,
    )
    .unwrap();

    let broad_include = Program::from_config(&fs, "/project/tsconfig.json");
    assert!(broad_include.source_file("/project/src/main.ts").is_some());
    assert!(
        broad_include
            .source_file("/project/src/settings.json")
            .is_none()
    );
    assert!(
        broad_include
            .source_file("/project/tsconfig.json")
            .is_none()
    );

    fs.write_file(
        "/project/tsconfig.json",
        r#"{"include":["src/**/*.ts","src/**/*.json"],"compilerOptions":{"resolveJsonModule":true,"noLib":true}}"#,
    )
    .unwrap();
    let explicit_include = Program::from_config(&fs, "/project/tsconfig.json");
    assert!(
        explicit_include
            .source_file("/project/src/main.ts")
            .is_some()
    );
    assert!(
        explicit_include
            .source_file("/project/src/settings.json")
            .is_some()
    );
    assert!(
        explicit_include
            .source_file("/project/tsconfig.json")
            .is_none()
    );
}
