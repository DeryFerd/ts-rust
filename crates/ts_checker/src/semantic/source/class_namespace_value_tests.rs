use ts_ast::{FileId, NodeData, NodeRef};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    CheckFlags, EscapedName, SemanticSymbolId, SymbolFlags,
};
use ts_parser::parse_source_file;

use crate::semantic::{CanonicalCheckerContext, CanonicalCheckerOptions};

fn with_sources(
    texts: &[(&str, bool)],
    check: impl FnOnce(&mut CanonicalCheckerContext<'_>, &[FileId]),
) {
    let parsed = texts
        .iter()
        .map(|(text, _)| parse_source_file(text))
        .collect::<Vec<_>>();
    let files = (0..texts.len())
        .map(|index| FileId::new(149_100 + u32::try_from(index).unwrap()))
        .collect::<Vec<_>>();
    let mut binder = CanonicalBinder::new();
    for ((source, file), (text, declaration)) in parsed.iter().zip(&files).zip(texts) {
        assert!(
            source.diagnostics.is_empty(),
            "{text}: {:?}",
            source.diagnostics
        );
        binder
            .bind_source_file_with_facts(
                &source.arena,
                source.source_file,
                *file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source(format!("\"/class-namespace-{}.ts\"", file.index())),
                    CanonicalSourceLanguage::TypeScript,
                    *declaration,
                    if *declaration {
                        CanonicalModuleState::Script
                    } else {
                        CanonicalModuleState::External
                    },
                ),
            )
            .unwrap();
    }
    for (source, file) in parsed.iter().zip(&files) {
        binder
            .bind_typescript_declaration_slice(&source.arena, *file)
            .unwrap();
    }
    let mut context = CanonicalCheckerContext::new(
        binder.finish(),
        parsed
            .iter()
            .zip(&files)
            .map(|(source, file)| (*file, &source.arena))
            .collect(),
        CanonicalCheckerOptions::default(),
    )
    .unwrap();
    check(&mut context, &files);
}

fn owner(context: &CanonicalCheckerContext<'_>, file: FileId) -> SemanticSymbolId {
    let (arena, bound) = context.file(file).unwrap();
    arena
        .iter()
        .find_map(|(node, record)| {
            matches!(record.data, NodeData::ClassDeclaration(_))
                .then(|| bound.symbol(NodeRef::new(arena.id(), file, node)).unwrap())
        })
        .and_then(|symbol| context.store().get_merged_symbol(symbol))
        .unwrap()
}

fn reads(context: &CanonicalCheckerContext<'_>, file: FileId) -> Vec<NodeRef> {
    let (arena, _) = context.file(file).unwrap();
    arena.iter().filter_map(|(_, record)| {
        let NodeData::VariableDeclaration(variable) = &record.data else { return None };
        let node = variable.initializer?;
        matches!(&arena.get(node)?.data, NodeData::Identifier(identifier) if identifier.text == "Value")
            .then_some(NodeRef::new(arena.id(), file, node))
    }).collect()
}

fn snapshot(
    context: &CanonicalCheckerContext<'_>,
    symbol: SemanticSymbolId,
) -> impl std::fmt::Debug + PartialEq + use<> {
    let store = context.store();
    let record = store.symbol(symbol).unwrap();
    (
        [
            store.type_len(),
            store.symbol_len(),
            store.signature_len(),
            store.mapper_len(),
            store.symbol_store().symbol_table_len(),
        ],
        store.checker_link_allocated_lengths(),
        store.relation_state_snapshot(),
        (
            record.flags(),
            record.check_flags(),
            record.parent(),
            record.value_declaration(),
            record.declarations().map(<[_]>::to_vec),
        ),
        [record.members(), record.exports()].map(|table| {
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
        store.declared_type_links(symbol).cloned(),
        store.value_symbol_links(symbol).cloned(),
        context.diagnostics().as_slice().to_vec(),
    )
}

#[test]
fn class_namespace_source_global_reads_preserve_members_exports_and_replay() {
    with_sources(
        &[
            (
                "declare class Value { value: number; static label: string; }",
                true,
            ),
            ("declare namespace Value {}", true),
            (
                "const first = Value; const second = Value; export = Value;",
                false,
            ),
        ],
        |context, files| {
            let symbol = owner(context, files[0]);
            let record = context.store().symbol(symbol).unwrap();
            let tables = (record.members(), record.exports());
            let declarations = record.declarations().unwrap().to_vec();
            assert_eq!(declarations.len(), 2);
            assert!(record.flags().contains(SymbolFlags::TRANSIENT));
            assert!(
                context
                    .store()
                    .source_merged_symbol_declarations_match(symbol)
            );
            assert!(!context.store().source_symbol_declarations_match(symbol));
            let instance_member = context
                .store()
                .symbol_table(tables.0.unwrap())
                .unwrap()
                .get_source("value")
                .unwrap();
            let static_member = context
                .store()
                .symbol_table(tables.1.unwrap())
                .unwrap()
                .get_source("label")
                .unwrap();
            let prototype = context
                .store()
                .symbol_table(tables.1.unwrap())
                .unwrap()
                .get_source("prototype")
                .unwrap();
            let parents = [instance_member, static_member, prototype]
                .map(|member| context.store().symbol(member).unwrap().parent());

            context.check_source_file(files[2]).unwrap();
            assert!(context.diagnostics().is_empty());
            let members = context.get_nongeneric_class_members(symbol).unwrap();
            let instance = members.shells().instance_type();
            let value = members.shells().value_type();
            assert_ne!(instance, value);
            assert_eq!(members.declared_instance_properties(), &[instance_member]);
            assert_eq!(members.declared_static_properties(), &[static_member]);
            assert_eq!(members.prototype(), prototype);
            let record = context.store().symbol(symbol).unwrap();
            assert_eq!((record.members(), record.exports()), tables);
            assert_eq!(record.declarations(), Some(declarations.as_slice()));
            assert_eq!(
                [instance_member, static_member, prototype].map(|member| context
                    .store()
                    .symbol(member)
                    .unwrap()
                    .parent()),
                parents
            );
            for member in [instance_member, static_member, prototype] {
                assert_eq!(context.store().get_parent_of_symbol(member), Some(symbol));
            }
            let references = reads(context, files[2]);
            assert_eq!(references.len(), 2);
            let before = snapshot(context, symbol);
            for _ in 0..2 {
                for reference in &references {
                    assert_eq!(context.get_type_at_location(*reference), Ok(value));
                    assert_eq!(context.get_symbol_at_location(*reference), Ok(Some(symbol)));
                }
                context.recheck_source_file(files[2]).unwrap();
                assert_eq!(
                    context.get_nongeneric_class_members(symbol).unwrap(),
                    members
                );
                assert_eq!(snapshot(context, symbol), before);
            }
        },
    );
}

#[test]
fn class_namespace_source_local_reads_keep_namespace_exports() {
    with_sources(
        &[(
            concat!(
                "class Value { value: number = 1; static label: string = 'label'; } ",
                "namespace Value { export var extra = 2; } ",
                "const observed = Value; export = Value;",
            ),
            false,
        )],
        |context, files| {
            let symbol = owner(context, files[0]);
            let exports = context.store().symbol(symbol).unwrap().exports().unwrap();
            let extra = context
                .store()
                .symbol_table(exports)
                .unwrap()
                .get_source("extra")
                .unwrap();
            context.check_source_file(files[0]).unwrap();
            let members = context.get_nongeneric_class_members(symbol).unwrap();
            assert!(members.declared_static_properties().contains(&extra));
            assert_eq!(
                context.store().symbol(symbol).unwrap().exports(),
                Some(exports)
            );
            let value = members.shells().value_type();
            for reference in reads(context, files[0]) {
                assert_eq!(context.get_type_at_location(reference), Ok(value));
                assert_eq!(context.get_symbol_at_location(reference), Ok(Some(symbol)));
            }
            let before = snapshot(context, symbol);
            context.recheck_source_file(files[0]).unwrap();
            assert_eq!(snapshot(context, symbol), before);
            assert!(context.diagnostics().is_empty());
        },
    );
}

#[test]
fn class_namespace_source_unsupported_global_body_keeps_all_exports() {
    with_sources(
        &[
            (
                "declare class Value { value: number; static label: string; }",
                true,
            ),
            (
                "declare namespace Value { export const extra: number; }",
                true,
            ),
            ("const observed = Value; export = Value;", false),
        ],
        |context, files| {
            let symbol = owner(context, files[0]);
            let exports = context.store().symbol(symbol).unwrap().exports().unwrap();
            assert!(
                context
                    .store()
                    .symbol_table(exports)
                    .unwrap()
                    .get_source("extra")
                    .is_some()
            );
            let before = snapshot(context, symbol);
            for _ in 0..2 {
                assert!(context.check_source_file(files[2]).is_err());
                assert_eq!(snapshot(context, symbol), before);
            }
        },
    );
}

#[test]
fn class_namespace_source_dropped_merge_is_rejected_before_writes() {
    with_sources(
        &[
            ("declare class Value { value: number; }", true),
            ("declare namespace Value {}", true),
            ("const observed = Value; export = Value;", false),
        ],
        |context, files| {
            let symbol = owner(context, files[0]);
            context.check_source_file(files[2]).unwrap();
            let members = context.get_nongeneric_class_members(symbol).unwrap();
            let record = context.store().symbol(symbol).unwrap();
            let flags = record.flags();
            let declarations = record.declarations().unwrap().to_vec();
            let class = record.value_declaration().unwrap();
            assert!(context.store_mut_for_test().set_symbol_declarations(
                symbol,
                Some(vec![class]),
                Some(class)
            ));
            assert!(context.store_mut_for_test().set_symbol_flags(
                symbol,
                SymbolFlags::CLASS,
                CheckFlags::NONE
            ));
            let before = snapshot(context, symbol);
            for _ in 0..2 {
                assert!(context.get_nongeneric_class_members(symbol).is_err());
                assert_eq!(snapshot(context, symbol), before);
            }
            assert!(context.store_mut_for_test().set_symbol_declarations(
                symbol,
                Some(declarations),
                Some(class)
            ));
            assert!(
                context
                    .store_mut_for_test()
                    .set_symbol_flags(symbol, flags, CheckFlags::NONE)
            );
            let restored = snapshot(context, symbol);
            assert_eq!(
                context.get_nongeneric_class_members(symbol).unwrap(),
                members
            );
            assert_eq!(snapshot(context, symbol), restored);
        },
    );
}
