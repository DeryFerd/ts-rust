use std::collections::BTreeMap;

use serde::Deserialize;
use ts_ast::NodeData;
use ts_compiler::{CanonicalTypeFormatFlags, Program};
use ts_options::{CompilerOptions, ModuleKind, ModuleResolutionKind, ScriptTarget};
use ts_vfs::{FileSystem, MemoryFileSystem};

#[derive(Deserialize)]
#[serde(rename_all = "camelCase")]
struct ExportCase {
    name: String,
    main: Option<String>,
    export_file: Option<String>,
    #[serde(default)]
    codes: Vec<u32>,
    files: BTreeMap<String, String>,
}

#[test]
#[allow(clippy::too_many_lines)] // Keep the unchanged review inputs and replay checks together.
fn export_equals_artifacts_preserve_declared_value_and_alias_roles() {
    let cases: Vec<ExportCase> = serde_json::from_str(include_str!(
        "../../../docs/probes/export_equals_artifact_cases.json"
    ))
    .unwrap();
    let mut checked = 0;
    for case in cases {
        let (expected_export, expected_read) = match case.name.as_str() {
            "original_invocation" => ("() => void", None),
            "function" => ("() => number", None),
            "mutable_union_initial" => ("string | number", Some("number")),
            "mutable_union_assigned" => ("string | number", Some("string")),
            "mutable_nullable" => ("number | undefined", Some("number")),
            "imported_named" => ("number", Some("number")),
            "imported_require" => ("() => number", Some("() => number")),
            "imported_namespace" => ("typeof local", Some("typeof local")),
            "class" | "enum" => ("Value", Some("typeof Value")),
            _ => continue,
        };
        checked += 1;
        let main = case.main.as_deref().unwrap_or("input.ts");
        let export_file = case.export_file.as_deref().unwrap_or(main);
        let filesystem = MemoryFileSystem::new(true);
        for (file, text) in &case.files {
            filesystem
                .write_file(&format!("/project/{file}"), text)
                .unwrap();
        }
        let (program, result) = Program::try_new_with_canonical_checker_and_queries(
            &filesystem,
            "/project",
            &[main.to_owned()],
            CompilerOptions {
                module: ModuleKind::NodeNext,
                module_specified: true,
                module_resolution: ModuleResolutionKind::NodeNext,
                target: ScriptTarget::EsNext,
                strict: true,
                strict_specified: true,
                no_emit: true,
                lib: Some(vec!["es5".to_owned()]),
                ..CompilerOptions::default()
            },
            |program, queries| {
                let source = program
                    .source_file(&format!("/project/{export_file}"))
                    .unwrap();
                let exported = source
                    .parse
                    .arena
                    .iter()
                    .find_map(|(_, record)| {
                        let NodeData::ExportAssignment(export) = &record.data else {
                            return None;
                        };
                        source.node_ref(export.expression)
                    })
                    .unwrap();
                let source = program.source_file(&format!("/project/{main}")).unwrap();
                let read = source.parse.arena.iter().find_map(|(_, record)| {
                    let NodeData::VariableDeclaration(variable) = &record.data else {
                        return None;
                    };
                    matches!(
                        &source.parse.arena.get(variable.name).unwrap().data,
                        NodeData::Identifier(name) if name.text == "observed"
                    )
                    .then(|| source.node_ref(variable.initializer.unwrap()).unwrap())
                });
                let before = queries.cold_diagnostic_snapshot();
                let mut identities = Vec::new();
                for (node, expected) in
                    std::iter::once((exported, expected_export)).chain(read.zip(expected_read))
                {
                    let type_ = queries.get_type_at_location(node).unwrap();
                    let symbol = queries.get_symbol_at_location(node).unwrap().unwrap();
                    assert_eq!(
                        queries
                            .type_to_string_at_location_with_flags(
                                type_,
                                node,
                                CanonicalTypeFormatFlags::NO_TRUNCATION
                            )
                            .unwrap(),
                        expected,
                        "{}",
                        case.name,
                    );
                    identities.push((node, type_, symbol));
                }
                if let [exported, read] = identities.as_slice() {
                    assert_eq!(exported.2, read.2, "{}", case.name);
                    assert_eq!(
                        exported.1 == read.1,
                        expected_read == Some(expected_export),
                        "{}",
                        case.name
                    );
                }
                for _ in 0..2 {
                    assert_eq!(queries.replay_sources().unwrap(), before);
                    for (node, type_, symbol) in &identities {
                        assert_eq!(queries.get_type_at_location(*node), Ok(*type_));
                        assert_eq!(queries.get_symbol_at_location(*node), Ok(Some(*symbol)));
                    }
                }
                if case.name == "original_invocation" {
                    assert_eq!(before.len(), 1);
                    assert_eq!(before[0].code, Some(2349));
                    assert_eq!(before[0].related_information[0].code, Some(7038));
                }
            },
        )
        .unwrap();
        result.expect("canonical checker ran");
        assert_eq!(
            program
                .diagnostics()
                .iter()
                .filter_map(|diagnostic| diagnostic.code)
                .collect::<Vec<_>>(),
            case.codes,
            "{}",
            case.name,
        );
    }
    assert_eq!(checked, 10);
}
