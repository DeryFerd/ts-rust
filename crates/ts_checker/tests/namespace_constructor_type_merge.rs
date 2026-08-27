use ts_ast::{FileId, NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SymbolFlags,
};
use ts_checker::semantic::{CanonicalCheckerContext, CanonicalCheckerOptions, TypeData};
use ts_parser::{ParseResult, parse_source_file};

const FILE: FileId = FileId::new(14_810);

fn context(parsed: &ParseResult) -> CanonicalCheckerContext<'_> {
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            FILE,
            CanonicalSourceFileFacts::new(
                EscapedName::source("\"/namespace-constructor.ts\""),
                CanonicalSourceLanguage::TypeScript,
                false,
                CanonicalModuleState::Script,
            ),
        )
        .unwrap();
    binder
        .bind_typescript_declaration_slice(&parsed.arena, FILE)
        .unwrap();
    CanonicalCheckerContext::new(
        binder.finish(),
        vec![(FILE, &parsed.arena)],
        CanonicalCheckerOptions::default(),
    )
    .unwrap()
}

fn node(parsed: &ParseResult, kind: SyntaxKind) -> NodeRef {
    parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            (record.kind == kind).then_some(NodeRef::new(parsed.arena.id(), FILE, node))
        })
        .unwrap()
}

fn counts(checker: &CanonicalCheckerContext<'_>) -> (usize, usize, usize, usize) {
    let store = checker.store();
    (
        store.type_len(),
        store.symbol_len(),
        store.signature_len(),
        store.mapper_len(),
    )
}

#[test]
fn namespace_constructor_merge_type_only_control_keeps_its_empty_local_flags() {
    let parsed = parse_source_file("declare namespace NS { interface Foo {} }");
    let mut checker = context(&parsed);
    let interface = node(&parsed, SyntaxKind::InterfaceDeclaration);
    let bound = checker.file(FILE).unwrap().1;
    let symbol = bound.symbol(interface).unwrap();
    let local = bound.local_symbol(interface).unwrap();
    assert_eq!(
        checker.store().symbol(local).unwrap().flags(),
        SymbolFlags::NONE
    );
    let type_ = checker.get_declared_type_of_symbol(symbol).unwrap();
    checker.check_source_file(FILE).unwrap();
    assert_eq!(checker.type_to_string(type_).unwrap(), "Foo");
    let warm = counts(&checker);
    checker.recheck_source_file(FILE).unwrap();
    assert_eq!(checker.get_declared_type_of_symbol(symbol).unwrap(), type_);
    assert_eq!(counts(&checker), warm);
    assert!(checker.diagnostics().is_empty());
}

#[test]
#[allow(clippy::too_many_lines)] // Check both meanings before and after source publication.
fn namespace_constructor_merge_preserves_cold_and_warm_type_and_value_identities() {
    for declarations in [
        "interface Foo {} var Foo: new () => number;",
        "var Foo: new () => number; interface Foo {}",
    ] {
        for query_first in [true, false] {
            let parsed = parse_source_file(&format!("declare namespace NS {{ {declarations} }}"));
            let mut checker = context(&parsed);
            let interface = node(&parsed, SyntaxKind::InterfaceDeclaration);
            let variable = node(&parsed, SyntaxKind::VariableDeclaration);
            let constructor = node(&parsed, SyntaxKind::ConstructorType);
            let namespace = node(&parsed, SyntaxKind::ModuleDeclaration);
            let bound = checker.file(FILE).unwrap().1;
            let store = checker.store();
            let symbol = store
                .get_merged_symbol(bound.symbol(interface).unwrap())
                .unwrap();
            let local = bound.local_symbol(interface).unwrap();
            assert_eq!(bound.local_symbol(variable), Some(local));
            assert_eq!(
                store.get_merged_symbol(bound.symbol(variable).unwrap()),
                Some(symbol)
            );
            let owner = store.symbol(symbol).unwrap();
            assert_eq!(
                owner.flags(),
                SymbolFlags::INTERFACE | SymbolFlags::FUNCTION_SCOPED_VARIABLE
            );
            assert_eq!(owner.value_declaration(), Some(variable));
            assert_eq!(owner.declarations().unwrap().len(), 2);
            assert_eq!(
                store.symbol(local).unwrap().flags(),
                SymbolFlags::EXPORT_VALUE
            );
            assert_eq!(store.symbol(local).unwrap().value_declaration(), None);
            assert_eq!(store.symbol(local).unwrap().export_symbol(), Some(symbol));
            assert_eq!(store.get_parent_of_symbol(symbol), bound.symbol(namespace));

            let cold = if query_first {
                let interface_type = checker.get_declared_type_of_symbol(symbol).unwrap();
                let constructor_type = checker.get_type_from_type_node(constructor).unwrap();
                assert_ne!(interface_type, constructor_type);
                assert!(checker.store().value_symbol_links(symbol).is_none());
                Some((interface_type, constructor_type))
            } else {
                None
            };

            checker.check_source_file(FILE).unwrap();

            let interface_type = checker.get_declared_type_of_symbol(symbol).unwrap();
            let constructor_type = checker.get_type_from_type_node(constructor).unwrap();
            if let Some(cold) = cold {
                assert_eq!((interface_type, constructor_type), cold);
            }
            assert_ne!(interface_type, constructor_type);
            assert!(matches!(
                checker.store().type_payload(interface_type).unwrap().data(),
                TypeData::Interface(_)
            ));
            assert_eq!(
                checker
                    .store()
                    .type_payload(interface_type)
                    .unwrap()
                    .symbol(),
                Some(symbol)
            );
            assert_eq!(
                checker
                    .store()
                    .declared_type_links(symbol)
                    .unwrap()
                    .declared_type,
                Some(interface_type)
            );
            assert_eq!(
                checker.type_to_string(constructor_type).unwrap(),
                "new () => number"
            );
            assert_eq!(
                checker
                    .store()
                    .value_symbol_links(symbol)
                    .unwrap()
                    .resolved_type,
                Some(constructor_type)
            );
            let NodeData::VariableDeclaration(data) =
                &parsed.arena.get(variable.node).unwrap().data
            else {
                unreachable!()
            };
            let name = NodeRef::new(parsed.arena.id(), FILE, data.name);
            assert_eq!(
                checker.get_type_at_location(name).unwrap(),
                constructor_type
            );
            assert_eq!(
                checker.get_symbol_at_location(interface).unwrap(),
                Some(symbol)
            );
            assert_eq!(checker.get_symbol_at_location(name).unwrap(), Some(symbol));
            assert!(checker.diagnostics().is_empty());

            let warm = counts(&checker);
            checker.recheck_source_file(FILE).unwrap();
            assert_eq!(
                checker.get_declared_type_of_symbol(symbol).unwrap(),
                interface_type
            );
            assert_eq!(
                checker.get_type_from_type_node(constructor).unwrap(),
                constructor_type
            );
            assert_eq!(
                checker.get_type_at_location(name).unwrap(),
                constructor_type
            );
            assert_eq!(counts(&checker), warm);
            assert!(checker.diagnostics().is_empty());
        }
    }
}
