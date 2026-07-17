use ts_compiler::Program;
use ts_options::{CompilerOptions, ModuleKind, ModuleResolutionKind};
use ts_vfs::{FileSystem, MemoryFileSystem};

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
            "namespace export",
            "target.d.ts",
            "export declare namespace value {}",
            "import { value } from './target'; const copy = value;",
        ),
        (
            "generic type export",
            "target.d.ts",
            "export interface Model<T> { value: T; }",
            concat!(
                "import type { Model } from './target'; ",
                "const model: Model = { value: 1 };",
            ),
        ),
    ] {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(&format!("/project/{target_name}"), target_source)
            .unwrap();
        fs.write_file("/project/importer.ts", importer_source)
            .unwrap();

        let error = Program::try_new_with_canonical_checker(
            &fs,
            "/project",
            &["importer.ts".to_owned()],
            options(),
        )
        .unwrap_err();
        assert!(error.is_unsupported_boundary(), "{case}: {error:?}");
    }

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
    let error = Program::try_new_with_canonical_checker(
        &fs,
        "/project",
        &["importer.ts".to_owned()],
        options(),
    )
    .unwrap_err();
    assert!(
        error.is_unsupported_boundary(),
        "re-export must remain an explicit boundary: {error:?}"
    );
}
