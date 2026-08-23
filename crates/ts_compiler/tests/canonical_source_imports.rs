use ts_compiler::Program;
use ts_options::{CompilerOptions, ModuleKind, ModuleResolutionKind};
use ts_vfs::{FileSystem, MemoryFileSystem};

fn wildcard_package_import_filesystem(importer: &str, target: &str) -> MemoryFileSystem {
    let filesystem = MemoryFileSystem::new(true);
    filesystem
        .write_file(
            "/project/package.json",
            r##"{"type":"module","imports":{"#/*.omg":"./src/*","#generated/*":"./src/*.ts"}}"##,
        )
        .unwrap();
    filesystem
        .write_file("/project/src/foo.ts", target)
        .unwrap();
    filesystem
        .write_file("/project/src/index.ts", importer)
        .unwrap();
    filesystem
}

fn nodenext_package_import_options() -> CompilerOptions {
    CompilerOptions {
        lib: Some(vec!["es5".to_owned()]),
        module: ModuleKind::NodeNext,
        module_specified: true,
        module_resolution: ModuleResolutionKind::NodeNext,
        no_emit: true,
        ..CompilerOptions::default()
    }
}

#[test]
fn canonical_wildcard_package_import_reports_captured_typescript_extension() {
    let importer = "import { hello } from \"#/foo.ts.omg\";\n\nhello();\n";
    let filesystem = wildcard_package_import_filesystem(
        importer,
        "export function hello() { return \"world\"; }\n",
    );

    let program = Program::try_new_with_canonical_checker(
        &filesystem,
        "/project",
        &["src/foo.ts".to_owned(), "src/index.ts".to_owned()],
        nodenext_package_import_options(),
    )
    .unwrap();

    let [diagnostic] = program.diagnostics() else {
        panic!(
            "expected one TS5097 diagnostic: {:?}",
            program.diagnostics()
        );
    };
    assert_eq!(
        diagnostic.file_name.as_deref(),
        Some("/project/src/index.ts")
    );
    assert_eq!(diagnostic.code, Some(5097));
    assert_eq!(
        diagnostic.message,
        "An import path can only end with a '.ts' extension when 'allowImportingTsExtensions' is enabled."
    );
    let range = diagnostic.range.expect("module specifier range");
    let start = importer.find("\"#/foo.ts.omg\"").unwrap();
    assert_eq!(range.start.get(), u32::try_from(start).unwrap());
    assert_eq!(
        range.end.get(),
        u32::try_from(start + "\"#/foo.ts.omg\"".len()).unwrap()
    );
}

#[test]
fn canonical_typescript_extension_imports_preserve_supported_exemptions() {
    const TARGET: &str = concat!(
        "export const value: number = 1;\n",
        "export interface Shape { value: number; }\n",
    );
    for (name, importer, allow_extensions, rewrite_extensions, no_check) in [
        (
            "type-only import",
            "import type { Shape } from \"#/foo.ts.omg\";\nconst result: Shape = { value: 1 };\n",
            false,
            false,
            false,
        ),
        (
            "side-effect import",
            "import \"#/foo.ts.omg\";\n",
            false,
            false,
            false,
        ),
        (
            "configured target extension",
            "import { value } from \"#generated/foo\";\nconst result: number = value;\n",
            false,
            false,
            false,
        ),
        (
            "allowed TypeScript extension",
            "import { value } from \"#/foo.ts.omg\";\nconst result: number = value;\n",
            true,
            false,
            false,
        ),
        (
            "rewritten TypeScript extension",
            "import { value } from \"#/foo.ts.omg\";\nconst result: number = value;\n",
            false,
            true,
            false,
        ),
        (
            "noCheck",
            "import { value } from \"#/foo.ts.omg\";\nconst result: number = value;\n",
            false,
            false,
            true,
        ),
        (
            "source no-check directive",
            "// @ts-nocheck\nimport { value } from \"#/foo.ts.omg\";\nconst result: number = value;\n",
            false,
            false,
            false,
        ),
    ] {
        let filesystem = wildcard_package_import_filesystem(importer, TARGET);
        let mut options = nodenext_package_import_options();
        options.allow_importing_ts_extensions = allow_extensions;
        options.rewrite_relative_import_extensions = rewrite_extensions;
        options.no_check = no_check;

        let program = Program::try_new_with_canonical_checker(
            &filesystem,
            "/project",
            &["src/foo.ts".to_owned(), "src/index.ts".to_owned()],
            options,
        )
        .unwrap_or_else(|error| panic!("{name}: {error:?}"));

        assert!(
            program.diagnostics().is_empty(),
            "{name}: {:?}",
            program.diagnostics()
        );
    }
}

#[test]
fn canonical_declaration_sources_may_import_typescript_extensions() {
    let filesystem =
        wildcard_package_import_filesystem("export {};\n", "export const value: number = 1;\n");
    filesystem
        .write_file(
            "/project/src/index.d.ts",
            "import { value } from \"#/foo.ts.omg\";\nexport declare const exposed: number;\n",
        )
        .unwrap();
    let mut options = nodenext_package_import_options();
    options.skip_lib_check = true;

    let program = Program::try_new_with_canonical_checker(
        &filesystem,
        "/project",
        &["src/foo.ts".to_owned(), "src/index.d.ts".to_owned()],
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
fn canonical_typescript_extension_diagnostics_follow_comment_directives() {
    const TARGET: &str = "export const value: number = 1;\n";

    for (directive, allow_extensions, expected_codes) in [
        ("// @ts-ignore", false, [].as_slice()),
        ("// @ts-expect-error", false, [].as_slice()),
        ("// @ts-expect-error", true, [2578].as_slice()),
    ] {
        let importer = format!(
            "{directive}\nimport {{ value }} from \"#/foo.ts.omg\";\nconst result: number = value;\n"
        );
        let filesystem = wildcard_package_import_filesystem(&importer, TARGET);
        let mut options = nodenext_package_import_options();
        options.allow_importing_ts_extensions = allow_extensions;

        let program = Program::try_new_with_canonical_checker(
            &filesystem,
            "/project",
            &["src/foo.ts".to_owned(), "src/index.ts".to_owned()],
            options,
        )
        .unwrap();

        assert_eq!(
            program
                .diagnostics()
                .iter()
                .filter_map(|diagnostic| diagnostic.code)
                .collect::<Vec<_>>(),
            expected_codes,
            "directive={directive}, allow_extensions={allow_extensions}"
        );
    }
}

#[test]
fn canonical_program_checks_importer_first_array_values_through_bundler_manifest() {
    let fs = MemoryFileSystem::new(true);
    fs.write_file(
        "/project/importer.ts",
        concat!(
            "import { values } from './target'; ",
            "const copy: string[] = values; ",
            "const bad: number = values;",
        ),
    )
    .unwrap();
    fs.write_file(
        "/project/target.ts",
        "export const values: string[] = ['value'];",
    )
    .unwrap();

    let program = Program::try_new_with_canonical_checker(
        &fs,
        "/project",
        &["importer.ts".to_owned()],
        CompilerOptions {
            module: ModuleKind::EsNext,
            module_specified: true,
            module_resolution: ModuleResolutionKind::Bundler,
            lib: Some(vec!["es5".to_owned()]),
            ..CompilerOptions::default()
        },
    )
    .unwrap();

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
        [(
            Some("/project/importer.ts"),
            Some(2322),
            "Type 'string[]' is not assignable to type 'number'.",
        )]
    );
}

#[test]
fn canonical_program_resolves_referenced_ambient_modules() {
    let fs = MemoryFileSystem::new(true);
    fs.write_file(
        "/project/modules.d.ts",
        "declare module 'ambient' { export const value: number; }",
    )
    .unwrap();
    fs.write_file(
        "/project/importer.ts",
        concat!(
            "/// <reference path='./modules.d.ts' />\n",
            "import { value } from 'ambient';",
        ),
    )
    .unwrap();

    let program = Program::try_new_with_canonical_checker(
        &fs,
        "/project",
        &["importer.ts".to_owned()],
        CompilerOptions {
            module: ModuleKind::EsNext,
            module_specified: true,
            module_resolution: ModuleResolutionKind::Bundler,
            lib: Some(vec!["es5".to_owned()]),
            skip_lib_check: true,
            ..CompilerOptions::default()
        },
    )
    .unwrap_or_else(|error| panic!("ambient module import failed: {error:?}"));

    assert!(
        program.diagnostics().is_empty(),
        "{:?}",
        program.diagnostics()
    );
    assert!(program.source_file("/project/modules.d.ts").is_some());
}

#[test]
fn canonical_program_combines_type_imports_with_imported_generic_calls() {
    let fs = MemoryFileSystem::new(true);
    fs.write_file(
        "/project/importer.ts",
        concat!(
            "import type { User } from './target'; ",
            "import { identity } from './target'; ",
            "export const user: User = { id: 1 }; ",
            "export const result: User = identity(user); ",
            "export const literal = identity('x'); ",
            "export const explicit = identity<string>('x'); ",
            "export const bad: { id: string } = identity(user);",
        ),
    )
    .unwrap();
    fs.write_file(
        "/project/target.ts",
        concat!(
            "export type User = { id: number }; ",
            "export function identity<T>(value: T): T { return value; }",
        ),
    )
    .unwrap();

    let program = Program::try_new_with_canonical_checker(
        &fs,
        "/project",
        &["importer.ts".to_owned()],
        CompilerOptions {
            module: ModuleKind::EsNext,
            module_specified: true,
            module_resolution: ModuleResolutionKind::Bundler,
            lib: Some(vec!["es5".to_owned()]),
            strict: true,
            ..CompilerOptions::default()
        },
    )
    .unwrap();

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
        [(
            Some("/project/importer.ts"),
            Some(2322),
            "Type 'User' is not assignable to type '{ id: string; }'.\n  Types of property 'id' are incompatible.\n    Type 'number' is not assignable to type 'string'.",
        )]
    );
}

#[test]
fn canonical_program_consumes_declaration_exports_in_both_program_orders() {
    let fs = MemoryFileSystem::new(true);
    fs.write_file(
        "/project/target.d.ts",
        concat!(
            "export declare const value: number; ",
            "export type Scalar = number; ",
            "export interface Model { count: number; } ",
            // A declaration-file source check would try to resolve this name.
            // The importer never reads it, so skipLibCheck must leave it alone.
            "export declare const unchecked: MissingGlobal;",
            // Binder diagnostics are skipped too, while all declaration
            // symbols remain available to the two importers.
            "declare const duplicate: number; ",
            "declare const duplicate: string;",
        ),
    )
    .unwrap();
    fs.write_file(
        "/project/cold.ts",
        concat!(
            "import { value } from './target'; ",
            "import type { Scalar } from './target'; ",
            "const good: number = value; ",
            "const typed: Scalar = value; ",
            "const bad: string = value;",
        ),
    )
    .unwrap();
    fs.write_file(
        "/project/warm.ts",
        concat!(
            "import { value } from './target'; ",
            "import type { Model } from './target'; ",
            "const good: number = value; ",
            "const model: Model = { count: value }; ",
            "const bad: boolean = value;",
        ),
    )
    .unwrap();

    for (roots, target_first) in [
        (vec!["cold.ts".to_owned(), "warm.ts".to_owned()], false),
        (
            vec![
                "target.d.ts".to_owned(),
                "cold.ts".to_owned(),
                "warm.ts".to_owned(),
            ],
            true,
        ),
    ] {
        let program = Program::try_new_with_canonical_checker(
            &fs,
            "/project",
            &roots,
            CompilerOptions {
                module: ModuleKind::EsNext,
                module_specified: true,
                module_resolution: ModuleResolutionKind::Bundler,
                lib: Some(vec!["es5".to_owned()]),
                skip_lib_check: true,
                strict: true,
                ..CompilerOptions::default()
            },
        )
        .unwrap();

        let cold = program.source_file("/project/cold.ts").unwrap();
        let warm = program.source_file("/project/warm.ts").unwrap();
        let target = program.source_file("/project/target.d.ts").unwrap();
        assert_eq!(target.id.index() < cold.id.index(), target_first);
        assert!(cold.id.index() < warm.id.index());
        // The exact list also proves that the unresolvable declaration above
        // did not produce a target-file diagnostic under skipLibCheck.
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
                    Some("/project/cold.ts"),
                    Some(2322),
                    "Type 'number' is not assignable to type 'string'.",
                ),
                (
                    Some("/project/warm.ts"),
                    Some(2322),
                    "Type 'number' is not assignable to type 'boolean'.",
                ),
            ]
        );
    }
}

#[test]
#[allow(clippy::too_many_lines)] // Keeps every declaration near-miss in one table-driven boundary proof.
fn canonical_program_fails_closed_on_declaration_import_near_misses() {
    let options = || CompilerOptions {
        module: ModuleKind::EsNext,
        module_specified: true,
        module_resolution: ModuleResolutionKind::Bundler,
        lib: Some(vec!["es5".to_owned()]),
        skip_lib_check: true,
        strict: true,
        ..CompilerOptions::default()
    };
    for (case, target_name, target_source, importer_source) in [
        (
            "ambient global",
            "target.d.ts",
            "declare const value: number;",
            "import { value } from './target'; const copy = value;",
        ),
        (
            "missing declare modifier",
            "target.d.ts",
            "export const value: number;",
            "import { value } from './target'; const copy = value;",
        ),
        (
            "reversed declaration modifiers",
            "target.d.ts",
            "declare export const value: number;",
            "import { value } from './target'; const copy = value;",
        ),
        (
            "declaration initializer",
            "target.d.ts",
            "export declare const value: number = 1;",
            "import { value } from './target'; const copy = value;",
        ),
        (
            "missing declaration annotation",
            "target.d.ts",
            "export declare const value;",
            "import { value } from './target'; const copy = value;",
        ),
        (
            "ordinary source without initializer",
            "target.ts",
            "export const value: number;",
            "import { value } from './target'; const copy = value;",
        ),
        (
            "default export",
            "target.d.ts",
            "declare const value: number; export default value;",
            "import { value } from './target'; const copy = value;",
        ),
        (
            "type-only namespace import",
            "target.d.ts",
            "export declare const value: number;",
            "import type * as value from './target'; const copy = value;",
        ),
    ] {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(&format!("/project/{target_name}"), target_source)
            .unwrap();
        fs.write_file("/project/importer.ts", importer_source)
            .unwrap();

        let Err(error) = Program::try_new_with_canonical_checker(
            &fs,
            "/project",
            &["importer.ts".to_owned()],
            options(),
        ) else {
            panic!("expected unsupported declaration import: {case}");
        };
        assert!(error.is_unsupported_boundary(), "{case}: {error:?}");
    }
}

#[test]
fn canonical_program_reports_missing_imported_interface_type_arguments() {
    let fs = MemoryFileSystem::new(true);
    fs.write_file(
        "/project/target.d.ts",
        "export interface Model<T> { value: T; }",
    )
    .unwrap();
    fs.write_file(
        "/project/importer.ts",
        "import type { Model } from './target'; const model: Model = { value: 1 };",
    )
    .unwrap();

    let program = Program::try_new_with_canonical_checker(
        &fs,
        "/project",
        &["importer.ts".to_owned()],
        CompilerOptions {
            module: ModuleKind::EsNext,
            module_specified: true,
            module_resolution: ModuleResolutionKind::Bundler,
            lib: Some(vec!["es5".to_owned()]),
            skip_lib_check: true,
            strict: true,
            ..CompilerOptions::default()
        },
    )
    .unwrap_or_else(|error| panic!("generic declaration import failed: {error:?}"));

    let [diagnostic] = program.diagnostics() else {
        panic!(
            "expected one generic arity diagnostic: {:?}",
            program.diagnostics()
        );
    };
    assert_eq!(
        diagnostic.file_name.as_deref(),
        Some("/project/importer.ts")
    );
    assert_eq!(diagnostic.code, Some(2314));
}

#[test]
fn canonical_program_resolves_declaration_reexports_without_fallback() {
    let fs = MemoryFileSystem::new(true);
    fs.write_file(
        "/project/importer.ts",
        "import { value } from './target'; const copy = value;",
    )
    .unwrap();
    fs.write_file("/project/target.d.ts", "export { value } from './base';")
        .unwrap();
    fs.write_file("/project/base.d.ts", "export declare const value: number;")
        .unwrap();
    let program = Program::try_new_with_canonical_checker(
        &fs,
        "/project",
        &["importer.ts".to_owned()],
        CompilerOptions {
            module: ModuleKind::EsNext,
            module_specified: true,
            module_resolution: ModuleResolutionKind::Bundler,
            lib: Some(vec!["es5".to_owned()]),
            skip_lib_check: true,
            strict: true,
            ..CompilerOptions::default()
        },
    )
    .unwrap_or_else(|error| panic!("declaration reexport failed: {error:?}"));

    assert!(
        program.diagnostics().is_empty(),
        "{:?}",
        program.diagnostics()
    );
    assert!(program.source_file("/project/target.d.ts").is_some());
    assert!(program.source_file("/project/base.d.ts").is_some());
}
