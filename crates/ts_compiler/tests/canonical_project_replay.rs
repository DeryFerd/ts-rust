use ts_ast::{NodeData, NodeRef};
use ts_compiler::{CanonicalProgramCheckError, Program};
use ts_vfs::{FileSystem, MemoryFileSystem};

fn identifier(program: &Program, file_name: &str, name: &str) -> NodeRef {
    let source = program.source_file(file_name).expect("program source");
    source
        .parse
        .arena
        .iter()
        .find_map(|(node, record)| match &record.data {
            NodeData::Identifier(identifier) if identifier.text == name => source.node_ref(node),
            _ => None,
        })
        .expect("source identifier")
}

#[test]
fn canonical_project_replay_owns_complete_cold_and_warm_diagnostics() {
    let filesystem = MemoryFileSystem::new(true);
    filesystem
        .write_file(
            "/project/tsconfig.json",
            r#"{
                "extends":"./missing.json",
                "files":["main.ts","duplicate.ts"],
                "compilerOptions":{
                    "strict":true,"noEmit":true,"lib":["es5"],"types":[],
                    "module":"esnext","moduleResolution":"bundler",
                    "unknownCompilerOption":true
                }
            }"#,
        )
        .unwrap();
    filesystem
        .write_file(
            "/project/main.ts",
            concat!(
                "import { pair } from './target';\n",
                "const bad: string = null;\n",
                "const tooFew = pair<string, number>('left');\n",
            ),
        )
        .unwrap();
    filesystem
        .write_file(
            "/project/target.ts",
            "export function pair<T, U>(left: T, right: U): U { return right; }\n",
        )
        .unwrap();
    filesystem
        .write_file(
            "/project/duplicate.ts",
            "let duplicate: number = 1; let duplicate: number = 2;\n",
        )
        .unwrap();

    let (program, snapshots) = Program::try_from_config_with_canonical_checker_and_queries(
        &filesystem,
        "/project/tsconfig.json",
        |program, queries| {
            let cold = queries.cold_diagnostic_snapshot();
            assert!(queries.has_diagnostics());
            assert!(program.diagnostics().len() < cold.len());
            assert!(cold.iter().any(|diagnostic| diagnostic.code == Some(2322)));
            assert!(cold.iter().any(|diagnostic| diagnostic.code == Some(2451)));
            assert!(cold.iter().any(|diagnostic| diagnostic.code == Some(5023)));
            assert!(cold.iter().any(|diagnostic| diagnostic.code == Some(6053)));
            let arity = cold
                .iter()
                .find(|diagnostic| diagnostic.code == Some(2554))
                .expect("missing argument diagnostic");
            let [related] = arity.related_information.as_slice() else {
                panic!("expected one related parameter declaration");
            };
            assert_eq!(related.file_name.as_deref(), Some("/project/target.ts"));
            assert_eq!(related.code, Some(6210));

            let value = identifier(program, "/project/main.ts", "bad");
            let store = queries.semantic_store_id();
            let type_id = queries.get_type_at_location(value).unwrap();
            let symbol = queries.get_symbol_at_location(value).unwrap();
            let warm = queries.replay_sources().unwrap();
            assert_eq!(cold, warm);
            assert_eq!(queries.cold_diagnostic_snapshot(), cold);
            assert_eq!(queries.semantic_store_id(), store);
            assert_eq!(queries.get_type_at_location(value).unwrap(), type_id);
            assert_eq!(queries.get_symbol_at_location(value).unwrap(), symbol);
            assert_eq!(queries.replay_sources().unwrap(), warm);
            (cold, warm)
        },
    )
    .unwrap();

    let (cold, warm) = snapshots.expect("canonical checker ran");
    assert_eq!(program.diagnostics(), cold);
    assert_eq!(program.diagnostics(), warm);
}

#[test]
fn canonical_project_replay_preserves_directives_and_source_eligibility() {
    let filesystem = MemoryFileSystem::new(true);
    filesystem
        .write_file(
            "/project/tsconfig.json",
            r#"{
                "files":["main.ts","ignored.ts","unchecked.js","skipped.d.ts"],
                "compilerOptions":{
                    "strict":true,"noEmit":true,"lib":["es5"],"types":[],
                    "allowJs":true,"checkJs":false,"skipLibCheck":true
                }
            }"#,
        )
        .unwrap();
    filesystem
        .write_file(
            "/project/main.ts",
            concat!(
                "// @ts-expect-error\n",
                "const suppressed: string = null;\n",
                "// @ts-ignore\n",
                "const ignored: string = null;\n",
                "// @ts-expect-error\n",
                "const unused: number = 1;\n",
                "const visible: string = null;\n",
            ),
        )
        .unwrap();
    filesystem
        .write_file(
            "/project/ignored.ts",
            "// @ts-nocheck\nconst ignoredFile: string = null;\n",
        )
        .unwrap();
    filesystem
        .write_file(
            "/project/unchecked.js",
            "const unchecked = MissingGlobal;\n",
        )
        .unwrap();
    filesystem
        .write_file(
            "/project/skipped.d.ts",
            "declare const skipped: NeverProvided;\n",
        )
        .unwrap();

    let (program, snapshots) = Program::try_from_config_with_canonical_checker_and_queries(
        &filesystem,
        "/project/tsconfig.json",
        |_, queries| {
            let cold = queries.cold_diagnostic_snapshot();
            assert_eq!(
                cold.iter()
                    .map(|diagnostic| (diagnostic.file_name.as_deref(), diagnostic.code))
                    .collect::<Vec<_>>(),
                [
                    (Some("/project/main.ts"), Some(2578)),
                    (Some("/project/main.ts"), Some(2322)),
                ],
            );
            let warm = queries.replay_sources().unwrap();
            assert_eq!(cold, warm);
            (cold, warm)
        },
    )
    .unwrap();

    let (cold, warm) = snapshots.expect("canonical checker ran");
    assert_eq!(program.diagnostics(), cold);
    assert_eq!(program.diagnostics(), warm);
}

#[test]
fn canonical_project_replay_retains_per_source_jsx_runtime_facts() {
    let filesystem = MemoryFileSystem::new(true);
    filesystem
        .write_file(
            "/project/tsconfig.json",
            r#"{
                "files":["classic.tsx","automatic.tsx","missing.tsx"],
                "compilerOptions":{
                    "strict":true,"noImplicitAny":false,"noEmit":true,
                    "lib":["es5"],"types":[],"skipLibCheck":true,
                    "module":"esnext","moduleResolution":"bundler","jsx":"react-jsx"
                }
            }"#,
        )
        .unwrap();
    filesystem
        .write_file(
            "/project/classic.tsx",
            concat!(
                "/** @jsxRuntime classic */\n",
                "/** @jsx Classic.h */\n",
                "declare const Classic: any;\n",
                "const classic = <div />;\n",
            ),
        )
        .unwrap();
    filesystem
        .write_file(
            "/project/automatic.tsx",
            "/** @jsxImportSource ui */\nconst automatic = <div />;\n",
        )
        .unwrap();
    filesystem
        .write_file(
            "/project/missing.tsx",
            "/** @jsxImportSource absent */\nconst missing = <div />;\n",
        )
        .unwrap();
    filesystem
        .write_file(
            "/project/node_modules/ui/jsx-runtime.d.ts",
            "export declare const jsx: any;\n",
        )
        .unwrap();

    let (program, snapshots) = Program::try_from_config_with_canonical_checker_and_queries(
        &filesystem,
        "/project/tsconfig.json",
        |program, queries| {
            let cold = queries.cold_diagnostic_snapshot();
            let [runtime] = cold.as_slice() else {
                panic!("expected only the unresolved JSX runtime: {cold:?}");
            };
            assert_eq!(runtime.file_name.as_deref(), Some("/project/missing.tsx"));
            assert_eq!(runtime.code, Some(2875));
            assert!(runtime.message.contains("'absent/jsx-runtime'"));
            let locations = [
                identifier(program, "/project/classic.tsx", "classic"),
                identifier(program, "/project/automatic.tsx", "automatic"),
                identifier(program, "/project/missing.tsx", "missing"),
            ];
            let identities = locations.map(|node| {
                (
                    queries.get_type_at_location(node).unwrap(),
                    queries.get_symbol_at_location(node).unwrap(),
                )
            });
            let store = queries.semantic_store_id();
            let warm = queries.replay_sources().unwrap();
            assert_eq!(cold, warm);
            for (node, identity) in locations.into_iter().zip(identities) {
                assert_eq!(
                    (
                        queries.get_type_at_location(node).unwrap(),
                        queries.get_symbol_at_location(node).unwrap(),
                    ),
                    identity,
                );
            }
            assert_eq!(queries.semantic_store_id(), store);
            (cold, warm)
        },
    )
    .unwrap();

    let (cold, warm) = snapshots.expect("canonical checker ran");
    assert_eq!(program.diagnostics(), cold);
    assert_eq!(program.diagnostics(), warm);
}

#[test]
fn canonical_project_replay_is_unavailable_without_a_checked_program() {
    for config in [
        None,
        Some("!"),
        Some(r#"{"files":["main.ts"],"compilerOptions":{"noCheck":true,"noEmit":true}}"#),
    ] {
        let filesystem = MemoryFileSystem::new(true);
        if let Some(config) = config {
            filesystem
                .write_file("/project/tsconfig.json", config)
                .unwrap();
        }
        filesystem
            .write_file("/project/main.ts", "const value = 1;\n")
            .unwrap();
        let (_, snapshot) = Program::try_from_config_with_canonical_checker_and_queries(
            &filesystem,
            "/project/tsconfig.json",
            |_, queries| queries.replay_sources(),
        )
        .unwrap();
        assert!(snapshot.is_none());
    }

    let filesystem = MemoryFileSystem::new(true);
    filesystem
        .write_file(
            "/project/tsconfig.json",
            r#"{
                "files":["settings.json"],
                "compilerOptions":{
                    "module":"esnext","moduleResolution":"bundler",
                    "resolveJsonModule":true,"lib":["es5"],"noEmit":true
                }
            }"#,
        )
        .unwrap();
    filesystem
        .write_file("/project/settings.json", r#"{"enabled":true}"#)
        .unwrap();
    let error = Program::try_from_config_with_canonical_checker_and_queries(
        &filesystem,
        "/project/tsconfig.json",
        |_, queries| queries.replay_sources(),
    )
    .unwrap_err();
    assert!(matches!(
        error,
        CanonicalProgramCheckError::UnsupportedSourceKind { .. }
    ));
}
