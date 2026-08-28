use ts_ast::{FileId, NodeData, NodeRef};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId,
};
use ts_parser::parse_source_file;

use super::{CanonicalArtifactQueryError, CanonicalCheckerContext};
use crate::semantic::{CanonicalCheckerOptions, ClassError, SymbolNodeLinks, TypeNodeLinks};

struct Fixture {
    owner: SemanticSymbolId,
    class_name: NodeRef,
    namespace_name: NodeRef,
    exported: NodeRef,
    read: NodeRef,
    files: [FileId; 3],
}

fn with_sources(
    namespace_first: bool,
    namespace: &str,
    check: impl FnOnce(&mut CanonicalCheckerContext<'_>, &Fixture),
) {
    let class = "declare class Value { value: number; static label: string; }";
    let declarations = if namespace_first {
        [namespace, class]
    } else {
        [class, namespace]
    };
    let texts = [
        declarations[0],
        declarations[1],
        "const observed = Value; export = Value;",
    ];
    let parsed = texts.map(parse_source_file);
    let files = [154_100, 154_101, 154_102].map(FileId::new);
    let mut binder = CanonicalBinder::new();
    for (index, (source, file)) in parsed.iter().zip(files).enumerate() {
        assert!(source.diagnostics.is_empty(), "{:?}", source.diagnostics);
        binder
            .bind_source_file_with_facts(
                &source.arena,
                source.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source(format!("\"/cold-namespace-{index}.ts\"")),
                    CanonicalSourceLanguage::TypeScript,
                    index != 2,
                    if index == 2 {
                        CanonicalModuleState::External
                    } else {
                        CanonicalModuleState::Script
                    },
                ),
            )
            .unwrap();
    }
    for (source, file) in parsed.iter().zip(files) {
        binder
            .bind_typescript_declaration_slice(&source.arena, file)
            .unwrap();
    }
    let mut context = CanonicalCheckerContext::new(
        binder.finish(),
        parsed
            .iter()
            .zip(files)
            .map(|(source, file)| (file, &source.arena))
            .collect(),
        CanonicalCheckerOptions::default(),
    )
    .unwrap();
    let mut class = None;
    let mut namespace_name = None;
    let mut exported = None;
    let mut read = None;
    for (source, file) in parsed.iter().zip(files) {
        let reference = |node| NodeRef::new(source.arena.id(), file, node);
        for (node, record) in source.arena.iter() {
            match &record.data {
                NodeData::ClassDeclaration(data) => {
                    class = Some((reference(node), reference(data.name.unwrap())));
                }
                NodeData::ModuleDeclaration(data) => namespace_name = Some(reference(data.name)),
                NodeData::ExportAssignment(data) => exported = Some(reference(data.expression)),
                NodeData::VariableDeclaration(data) if file == files[2] => {
                    read = data.initializer.map(reference);
                }
                _ => {}
            }
        }
    }
    let (class, class_name) = class.unwrap();
    let owner = context.file(class.file).unwrap().1.symbol(class).unwrap();
    let fixture = Fixture {
        owner: context.store().get_merged_symbol(owner).unwrap(),
        class_name,
        namespace_name: namespace_name.unwrap(),
        exported: exported.unwrap(),
        read: read.unwrap(),
        files,
    };
    check(&mut context, &fixture);
}

fn snapshot(
    context: &CanonicalCheckerContext<'_>,
    fixture: &Fixture,
) -> impl std::fmt::Debug + PartialEq + use<> {
    let store = context.store();
    let owner = store.symbol(fixture.owner).unwrap();
    (
        [
            store.type_len(),
            store.symbol_len(),
            store.signature_len(),
            store.mapper_len(),
        ],
        store.checker_link_allocated_lengths(),
        store.declared_type_links(fixture.owner).cloned(),
        store.value_symbol_links(fixture.owner).cloned(),
        (
            owner.flags(),
            owner.declarations().map(<[_]>::to_vec),
            owner.value_declaration(),
            [owner.members(), owner.exports()].map(|table| {
                table.map(|table| {
                    (
                        table,
                        store
                            .symbol_table(table)
                            .unwrap()
                            .iter()
                            .map(|(name, symbol)| (name.to_owned(), symbol))
                            .collect::<Vec<_>>(),
                    )
                })
            }),
        ),
        [
            fixture.namespace_name,
            fixture.class_name,
            fixture.exported,
            fixture.read,
        ]
        .map(|node| {
            (
                store.type_node_links(node).cloned(),
                store.symbol_node_links(node).cloned(),
            )
        }),
        fixture.files.map(|file| {
            store
                .source_file_links(context.source_file(file).unwrap())
                .cloned()
        }),
        context.diagnostics().as_slice().to_vec(),
    )
}

#[test]
fn cold_merged_namespace_value_identity_survives_source_check_and_replay() {
    for (namespace_first, declared_first) in [false, true].into_iter().flat_map(|namespace_first| {
        [false, true].map(|declared_first| (namespace_first, declared_first))
    }) {
        with_sources(
            namespace_first,
            "declare namespace Value {}",
            |context, fixture| {
                if declared_first {
                    context.get_type_at_location(fixture.class_name).unwrap();
                }
                assert!(
                    context
                        .store()
                        .value_symbol_links(fixture.owner)
                        .is_none_or(|links| links.resolved_type.is_none())
                );
                let value = context
                    .get_type_at_location(fixture.namespace_name)
                    .unwrap();
                let members = context.get_nongeneric_class_members(fixture.owner).unwrap();
                let instance = members.shells().instance_type();
                assert_eq!(value, members.shells().value_type());
                assert_ne!(value, instance);
                assert_eq!(members.declared_instance_properties().len(), 1);
                assert_eq!(members.declared_static_properties().len(), 1);
                for file in fixture.files {
                    assert!(
                        context
                            .store()
                            .source_file_links(context.source_file(file).unwrap())
                            .is_none_or(|links| !links.type_checked)
                    );
                }
                assert_eq!(
                    context.get_type_at_location(fixture.class_name),
                    Ok(instance)
                );
                assert_eq!(
                    context.get_type_at_location(fixture.namespace_name),
                    Ok(value)
                );
                context.check_source_file(fixture.files[2]).unwrap();
                let queries = [
                    (fixture.class_name, instance),
                    (fixture.exported, instance),
                    (fixture.read, value),
                    (fixture.namespace_name, value),
                ];
                for (node, expected) in queries {
                    assert_eq!(context.get_type_at_location(node), Ok(expected));
                    assert_eq!(
                        context.get_symbol_at_location(node),
                        Ok(Some(fixture.owner))
                    );
                }
                let before = snapshot(context, fixture);
                for _ in 0..2 {
                    context.recheck_source_file(fixture.files[2]).unwrap();
                    assert_eq!(
                        context.get_nongeneric_class_members(fixture.owner).unwrap(),
                        members
                    );
                    for (node, expected) in queries {
                        assert_eq!(context.get_type_at_location(node), Ok(expected));
                        assert_eq!(
                            context.get_symbol_at_location(node),
                            Ok(Some(fixture.owner))
                        );
                    }
                    assert_eq!(snapshot(context, fixture), before);
                }
                assert!(context.diagnostics().is_empty());
            },
        );
    }
}

#[test]
fn cold_merged_namespace_name_caches_reject_before_publication_and_recover() {
    for (prepared, change_type) in [false, true]
        .into_iter()
        .flat_map(|prepared| [false, true].map(|change_type| (prepared, change_type)))
    {
        with_sources(false, "declare namespace Value {}", |context, fixture| {
            if prepared {
                context
                    .get_type_at_location(fixture.namespace_name)
                    .unwrap();
            }
            let type_links = context
                .store()
                .type_node_links(fixture.namespace_name)
                .cloned();
            let symbol_links = context
                .store()
                .symbol_node_links(fixture.namespace_name)
                .cloned();
            if change_type {
                let number = context.store().intrinsic_bootstrap().unwrap().number_type;
                assert!(context.store_mut_for_test().set_type_node_links(
                    fixture.namespace_name,
                    TypeNodeLinks {
                        resolved_type: Some(number),
                        ..TypeNodeLinks::default()
                    },
                ));
            } else {
                let members = context
                    .store()
                    .symbol(fixture.owner)
                    .unwrap()
                    .members()
                    .unwrap();
                let wrong = context
                    .store()
                    .symbol_table(members)
                    .unwrap()
                    .get_source("value")
                    .unwrap();
                assert!(context.store_mut_for_test().set_symbol_node_links(
                    fixture.namespace_name,
                    SymbolNodeLinks {
                        resolved_symbol: Some(wrong)
                    },
                ));
            }
            let before = snapshot(context, fixture);
            for _ in 0..2 {
                assert!(matches!(
                    context.get_type_at_location(fixture.namespace_name),
                    Err(CanonicalArtifactQueryError::InvalidType { .. }
                        | CanonicalArtifactQueryError::InvalidSymbol { .. })
                ));
                assert_eq!(snapshot(context, fixture), before);
            }
            assert!(
                context
                    .store_mut_for_test()
                    .set_type_node_links(fixture.namespace_name, type_links.unwrap_or_default(),)
            );
            assert!(
                context.store_mut_for_test().set_symbol_node_links(
                    fixture.namespace_name,
                    symbol_links.unwrap_or_default(),
                )
            );
            let value = context
                .get_type_at_location(fixture.namespace_name)
                .unwrap();
            assert_eq!(
                value,
                context
                    .get_nongeneric_class_members(fixture.owner)
                    .unwrap()
                    .shells()
                    .value_type()
            );
        });
    }
}

#[test]
fn cold_merged_namespace_nonempty_body_remains_unsupported_without_writes() {
    with_sources(
        false,
        "declare namespace Value { export const extra: number; }",
        |context, fixture| {
            let before = snapshot(context, fixture);
            for _ in 0..2 {
                assert!(matches!(
                    context.get_type_at_location(fixture.namespace_name),
                    Err(CanonicalArtifactQueryError::Class {
                        error: ClassError::Unsupported(_),
                        ..
                    })
                ));
                assert_eq!(snapshot(context, fixture), before);
            }
        },
    );
}
