use ts_ast::{FileId, NodeData, NodeRef};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId,
};
use ts_checker::semantic::{CanonicalCheckerContext, CanonicalCheckerOptions, TypeData, TypeId};
use ts_parser::{ParseResult, parse_source_file};

const SOURCE: &str = concat!(
    "interface Base { id: number }\n",
    "interface Derived extends Base { label: string }\n",
    "const ok: Derived = { id: 1, label: \"x\" };\n",
    "const bad: Derived = { label: \"x\" };\n",
    "function read(value: Derived): number { return value.id; }\n",
);

fn interface_symbol(
    parsed: &ParseResult,
    file: FileId,
    context: &CanonicalCheckerContext<'_>,
    expected: &str,
) -> SemanticSymbolId {
    let declaration = parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            let NodeData::InterfaceDeclaration(interface) = &record.data else {
                return None;
            };
            let NodeData::Identifier(name) = &parsed.arena.get(interface.name)?.data else {
                return None;
            };
            (name.text == expected).then_some(NodeRef::new(parsed.arena.id(), file, node))
        })
        .unwrap_or_else(|| panic!("missing interface {expected}"));
    let raw = context.file(file).unwrap().1.symbol(declaration).unwrap();
    context.store().get_merged_symbol(raw).unwrap()
}

fn declared_type(context: &CanonicalCheckerContext<'_>, symbol: SemanticSymbolId) -> TypeId {
    context
        .store()
        .declared_type_links(symbol)
        .and_then(|links| links.declared_type)
        .unwrap_or_else(|| panic!("missing declared type for {symbol:?}"))
}

fn read_access(parsed: &ParseResult, file: FileId) -> NodeRef {
    parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            let NodeData::PropertyAccessExpression(access) = &record.data else {
                return None;
            };
            let NodeData::Identifier(name) = &parsed.arena.get(access.name)?.data else {
                return None;
            };
            (name.text == "id").then_some(NodeRef::new(parsed.arena.id(), file, node))
        })
        .expect("missing inherited property read")
}

#[test]
fn direct_interface_heritage_publishes_inherited_properties_for_relations_and_reads() {
    let parsed = parse_source_file(SOURCE);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(0);
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            file,
            CanonicalSourceFileFacts::new(
                EscapedName::source("\"/project/interface-heritage.ts\""),
                CanonicalSourceLanguage::TypeScript,
                false,
                CanonicalModuleState::Script,
            ),
        )
        .unwrap();
    binder
        .bind_typescript_declaration_slice(&parsed.arena, file)
        .unwrap();
    let mut context = CanonicalCheckerContext::new(
        binder.finish(),
        [(file, &parsed.arena)].into_iter().collect(),
        CanonicalCheckerOptions::default(),
    )
    .unwrap();
    let base_symbol = interface_symbol(&parsed, file, &context, "Base");
    let derived_symbol = interface_symbol(&parsed, file, &context, "Derived");
    let access = read_access(&parsed, file);

    context.check_source_file(file).unwrap();

    let diagnostics = context.diagnostics().as_slice();
    assert_eq!(diagnostics.len(), 1, "{diagnostics:?}");
    assert_eq!(diagnostics[0].diagnostic.code(), 2741);
    assert_eq!(diagnostics[0].diagnostic.arguments[0], "id");
    assert_eq!(diagnostics[0].related_information.len(), 1);
    assert_eq!(
        diagnostics[0].related_information[0].diagnostic.code(),
        2728
    );

    let base_type = declared_type(&context, base_symbol);
    let derived_type = declared_type(&context, derived_symbol);
    let TypeData::Interface(derived) = context.store().type_payload(derived_type).unwrap().data()
    else {
        panic!("Derived must retain its interface payload")
    };
    assert!(derived.base_types_resolved);
    assert_eq!(
        derived.resolved_base_types.as_deref(),
        Some(&[base_type][..])
    );
    let properties = derived
        .reference
        .object
        .structured
        .properties
        .as_deref()
        .expect("Derived must publish its final property list");
    assert_eq!(
        properties
            .iter()
            .map(|property| {
                context
                    .store()
                    .symbol(*property)
                    .unwrap()
                    .name()
                    .as_utf8()
                    .unwrap()
            })
            .collect::<Vec<_>>(),
        ["label", "id"]
    );
    let read_type = context
        .store()
        .type_node_links(access)
        .and_then(|links| links.resolved_type)
        .expect("the inherited property read must be typed");
    assert_eq!(context.type_to_string(read_type).unwrap(), "number");
    assert_eq!(
        context.is_type_assignable_to(derived_type, base_type),
        Ok(true)
    );
    assert_eq!(
        context.is_type_assignable_to(base_type, derived_type),
        Ok(false)
    );

    let warm_state = (
        context.store().type_len(),
        context.store().mapper_len(),
        context.store().signature_len(),
        context.store().index_info_len(),
        context.store().symbol_store().symbol_table_len(),
        context.store().relation_state_snapshot(),
        context.diagnostics().clone(),
    );
    context.check_source_file(file).unwrap();
    assert_eq!(
        (
            context.store().type_len(),
            context.store().mapper_len(),
            context.store().signature_len(),
            context.store().index_info_len(),
            context.store().symbol_store().symbol_table_len(),
            context.store().relation_state_snapshot(),
            context.diagnostics().clone(),
        ),
        warm_state
    );
}
