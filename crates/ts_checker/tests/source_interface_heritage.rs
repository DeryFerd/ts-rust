use ts_ast::{FileId, NodeData, NodeRef};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, SourceCheckError, TypeData, TypeId,
};
use ts_parser::{ParseResult, parse_source_file};

const SOURCE: &str = concat!(
    "interface Base { id: number }\n",
    "interface Derived extends Base { label: string }\n",
    "const ok: Derived = { id: 1, label: \"x\" };\n",
    "const bad: Derived = { label: \"x\" };\n",
    "function read(value: Derived): number { return value.id; }\n",
);

fn checker_context<'arena>(
    parsed: &'arena ParseResult,
    file: FileId,
    path: &str,
) -> CanonicalCheckerContext<'arena> {
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            file,
            CanonicalSourceFileFacts::new(
                EscapedName::source(format!("\"{path}\"")),
                CanonicalSourceLanguage::TypeScript,
                false,
                CanonicalModuleState::Script,
            ),
        )
        .unwrap();
    binder
        .bind_typescript_declaration_slice(&parsed.arena, file)
        .unwrap();
    CanonicalCheckerContext::new(
        binder.finish(),
        [(file, &parsed.arena)].into_iter().collect(),
        CanonicalCheckerOptions::default(),
    )
    .unwrap()
}

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

fn variable_name(parsed: &ParseResult, file: FileId, expected: &str) -> NodeRef {
    let name = parsed
        .arena
        .iter()
        .find_map(|(_, record)| {
            let NodeData::VariableDeclaration(variable) = &record.data else {
                return None;
            };
            let NodeData::Identifier(name) = &parsed.arena.get(variable.name)?.data else {
                return None;
            };
            (name.text == expected).then_some(variable.name)
        })
        .unwrap_or_else(|| panic!("missing variable {expected}"));
    NodeRef::new(parsed.arena.id(), file, name)
}

fn node_text(parsed: &ParseResult, node: NodeRef) -> &str {
    let range = parsed.arena.get(node.node).unwrap().range;
    &parsed.arena.source_text().unwrap()
        [usize::try_from(range.start.get()).unwrap()..usize::try_from(range.end.get()).unwrap()]
}

fn read_access(parsed: &ParseResult, file: FileId, expected: &str) -> NodeRef {
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
            (name.text == expected).then_some(NodeRef::new(parsed.arena.id(), file, node))
        })
        .unwrap_or_else(|| panic!("missing property read {expected}"))
}

fn interface_property_names(
    context: &CanonicalCheckerContext<'_>,
    type_: TypeId,
) -> (Vec<String>, Vec<String>) {
    let TypeData::Interface(interface) = context.store().type_payload(type_).unwrap().data() else {
        panic!("expected an interface type")
    };
    assert!(interface.declared_members_resolved);
    let mut declared = interface
        .declared_members
        .and_then(|members| context.store().symbol_table(members))
        .map(|members| {
            members
                .iter()
                .map(|(name, _)| name.as_utf8().unwrap().to_owned())
                .collect::<Vec<_>>()
        })
        .unwrap_or_default();
    declared.sort();
    let resolved = interface
        .reference
        .object
        .structured
        .properties
        .as_deref()
        .unwrap_or_default()
        .iter()
        .map(|property| {
            context
                .store()
                .symbol(*property)
                .unwrap()
                .name()
                .as_utf8()
                .unwrap()
                .to_owned()
        })
        .collect();
    (declared, resolved)
}

#[test]
fn direct_interface_heritage_publishes_inherited_properties_for_relations_and_reads() {
    let parsed = parse_source_file(SOURCE);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(0);
    let mut context = checker_context(&parsed, file, "/project/interface-heritage.ts");
    let base_symbol = interface_symbol(&parsed, file, &context, "Base");
    let derived_symbol = interface_symbol(&parsed, file, &context, "Derived");
    let access = read_access(&parsed, file, "id");

    context.check_source_file(file).unwrap();

    let diagnostics = context.diagnostics().as_slice();
    assert_eq!(diagnostics.len(), 1, "{diagnostics:?}");
    assert_eq!(diagnostics[0].diagnostic.code(), 2741);
    assert_eq!(
        diagnostics[0].diagnostic.arguments,
        ["id", "{ label: string; }", "Derived"]
    );
    assert_eq!(
        diagnostics[0].node,
        Some(variable_name(&parsed, file, "bad"))
    );
    assert_eq!(diagnostics[0].related_information.len(), 1);
    assert_eq!(
        diagnostics[0].related_information[0].diagnostic.code(),
        2728
    );
    assert_eq!(
        diagnostics[0].related_information[0].diagnostic.arguments,
        ["id"]
    );
    assert_eq!(
        node_text(&parsed, diagnostics[0].related_information[0].node.unwrap()),
        "id"
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
    assert_eq!(
        interface_property_names(&context, derived_type),
        (
            vec!["label".to_owned()],
            vec!["label".to_owned(), "id".to_owned()]
        )
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

#[test]
fn direct_interface_heritage_keeps_own_and_base_declaration_order_separate() {
    let parsed = parse_source_file(concat!(
        "interface Base { first: number; second: string }\n",
        "interface Derived extends Base { third: boolean; fourth: number }\n",
        "function read(value: Derived): string { return value.second; }\n",
    ));
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(1);
    let mut context = checker_context(&parsed, file, "/project/interface-heritage-member-order.ts");
    let base_symbol = interface_symbol(&parsed, file, &context, "Base");
    let derived_symbol = interface_symbol(&parsed, file, &context, "Derived");
    let access = read_access(&parsed, file, "second");

    context.check_source_file(file).unwrap();

    assert!(context.diagnostics().is_empty());
    let base_type = declared_type(&context, base_symbol);
    let derived_type = declared_type(&context, derived_symbol);
    assert_eq!(
        interface_property_names(&context, base_type),
        (
            vec!["first".to_owned(), "second".to_owned()],
            vec!["first".to_owned(), "second".to_owned()]
        )
    );
    assert_eq!(
        interface_property_names(&context, derived_type),
        (
            vec!["fourth".to_owned(), "third".to_owned()],
            vec![
                "third".to_owned(),
                "fourth".to_owned(),
                "first".to_owned(),
                "second".to_owned(),
            ]
        )
    );
    let read_type = context
        .store()
        .type_node_links(access)
        .and_then(|links| links.resolved_type)
        .expect("the inherited property read must be typed");
    assert_eq!(context.type_to_string(read_type).unwrap(), "string");
}

#[test]
fn empty_and_optional_derived_interfaces_remain_structural() {
    let parsed = parse_source_file(concat!(
        "interface Base { id: number }\n",
        "interface Empty extends Base {}\n",
        "interface Optional extends Base { label?: string }\n",
        "const base: Base = { id: 1 };\n",
        "const empty: Empty = base;\n",
        "const optional: Optional = base;\n",
    ));
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(2);
    let mut context = checker_context(&parsed, file, "/project/interface-heritage-structural.ts");
    let base_symbol = interface_symbol(&parsed, file, &context, "Base");
    let empty_symbol = interface_symbol(&parsed, file, &context, "Empty");
    let optional_symbol = interface_symbol(&parsed, file, &context, "Optional");

    context.check_source_file(file).unwrap();

    assert!(context.diagnostics().is_empty());
    let base_type = declared_type(&context, base_symbol);
    let empty_type = declared_type(&context, empty_symbol);
    let optional_type = declared_type(&context, optional_symbol);
    assert_eq!(
        interface_property_names(&context, empty_type),
        (Vec::new(), vec!["id".to_owned()])
    );
    assert_eq!(
        interface_property_names(&context, optional_type),
        (
            vec!["label".to_owned()],
            vec!["label".to_owned(), "id".to_owned()]
        )
    );
    for (source, target) in [
        (empty_type, base_type),
        (base_type, empty_type),
        (optional_type, base_type),
        (base_type, optional_type),
        (empty_type, optional_type),
        (optional_type, empty_type),
    ] {
        assert_eq!(
            context.is_type_assignable_to(source, target),
            Ok(true),
            "{source:?} must be structurally assignable to {target:?}"
        );
    }
}

#[test]
fn forward_base_with_recursive_derived_property_resolves_cold_and_warm() {
    let parsed = parse_source_file(concat!(
        "interface Forward extends Later { own: number }\n",
        "interface Later { back: Forward }\n",
        "function read(value: Forward): number { return value.own; }\n",
    ));
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(3);
    let mut context = checker_context(
        &parsed,
        file,
        "/project/interface-heritage-forward-recursive.ts",
    );
    let forward_symbol = interface_symbol(&parsed, file, &context, "Forward");
    let later_symbol = interface_symbol(&parsed, file, &context, "Later");

    context.check_source_file(file).unwrap();

    assert!(context.diagnostics().is_empty());
    let forward_type = declared_type(&context, forward_symbol);
    let later_type = declared_type(&context, later_symbol);
    assert_eq!(
        interface_property_names(&context, forward_type),
        (
            vec!["own".to_owned()],
            vec!["own".to_owned(), "back".to_owned()]
        )
    );
    let back_property = {
        let TypeData::Interface(forward) =
            context.store().type_payload(forward_type).unwrap().data()
        else {
            panic!("Forward must retain its interface payload")
        };
        forward
            .reference
            .object
            .structured
            .properties
            .as_ref()
            .unwrap()[1]
    };
    assert_eq!(
        context
            .store()
            .value_symbol_links(back_property)
            .and_then(|links| links.resolved_type),
        Some(forward_type)
    );
    assert_eq!(
        context.is_type_assignable_to(forward_type, later_type),
        Ok(true)
    );
    assert_eq!(
        context.is_type_assignable_to(later_type, forward_type),
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

#[test]
fn compatible_interface_overrides_replace_inherited_properties() {
    for (index, source) in [
        concat!(
            "interface Base { value: number; inherited: string }\n",
            "interface Derived extends Base { value: number }\n",
            "function read(value: Derived): number { return value.value; }\n",
        ),
        concat!(
            "interface Base { value: {} }\n",
            "interface Derived extends Base { value: any }\n",
        ),
    ]
    .into_iter()
    .enumerate()
    {
        let parsed = parse_source_file(source);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(u32::try_from(index + 100).unwrap());
        let mut context = checker_context(&parsed, file, "/project/interface-override.ts");

        context.check_source_file(file).unwrap();
        assert!(context.diagnostics().is_empty());
        let base = interface_symbol(&parsed, file, &context, "Base");
        let derived = interface_symbol(&parsed, file, &context, "Derived");
        let base_type = declared_type(&context, base);
        let derived_type = declared_type(&context, derived);
        assert_eq!(
            context.is_type_assignable_to(derived_type, base_type),
            Ok(true)
        );

        let TypeData::Interface(derived_data) =
            context.store().type_payload(derived_type).unwrap().data()
        else {
            panic!("derived declaration must retain its interface payload")
        };
        let own_property = context
            .store()
            .symbol_table(derived_data.declared_members.unwrap())
            .unwrap()
            .get_source("value")
            .unwrap();
        assert_eq!(
            context
                .store()
                .symbol_table(derived_data.reference.object.structured.members.unwrap())
                .unwrap()
                .get_source("value"),
            Some(own_property)
        );
        assert_eq!(
            derived_data
                .reference
                .object
                .structured
                .properties
                .as_deref()
                .unwrap()
                .iter()
                .filter(|property| **property == own_property)
                .count(),
            1
        );

        let warm = (
            context.store().type_len(),
            context.store().symbol_store().symbol_table_len(),
            context.store().relation_state_snapshot(),
        );
        context.recheck_source_file(file).unwrap();
        assert_eq!(
            (
                context.store().type_len(),
                context.store().symbol_store().symbol_table_len(),
                context.store().relation_state_snapshot(),
            ),
            warm
        );
    }
}

#[test]
#[allow(clippy::too_many_lines)] // Every heritage boundary must retain the same cold graph state.
fn unsupported_interface_heritage_shapes_fail_before_semantic_publication() {
    let cases = [
        (
            "cycle",
            concat!(
                "interface Left extends Right { left: number }\n",
                "interface Right extends Left { right: number }\n",
                "function read(value: Left): number { return value.left; }\n",
            ),
        ),
        (
            "chain",
            concat!(
                "interface Root { root: number }\n",
                "interface Middle extends Root { middle: number }\n",
                "interface Leaf extends Middle { leaf: number }\n",
                "function read(value: Leaf): number { return value.leaf; }\n",
            ),
        ),
        (
            "incompatible-override",
            concat!(
                "interface Base { value: number }\n",
                "interface Derived extends Base { value: string }\n",
                "function read(value: Derived): string { return value.value; }\n",
            ),
        ),
        (
            "generic-base",
            concat!(
                "interface Base<T> { value: T }\n",
                "interface Derived extends Base<number> { own: number }\n",
                "function read(value: Derived): number { return value.own; }\n",
            ),
        ),
        (
            "generic-derived",
            concat!(
                "interface Base { value: number }\n",
                "interface Derived<T> extends Base { own: T }\n",
                "function read(value: Derived<number>): number { return value.own; }\n",
            ),
        ),
        (
            "base-call-signature",
            concat!(
                "interface Base { (): number }\n",
                "interface Derived extends Base { own: number }\n",
                "function read(value: Derived): number { return value.own; }\n",
            ),
        ),
        (
            "derived-call-signature",
            concat!(
                "interface Base { value: number }\n",
                "interface Derived extends Base { (): number }\n",
                "function read(value: Derived): number { return value.value; }\n",
            ),
        ),
        (
            "base-index-signature",
            concat!(
                "interface Base { [key: string]: number }\n",
                "interface Derived extends Base { own: number }\n",
                "function read(value: Derived): number { return value.own; }\n",
            ),
        ),
        (
            "alias-base",
            concat!(
                "interface Base { value: number }\n",
                "type Alias = Base;\n",
                "interface Derived extends Alias { own: number }\n",
                "function read(value: Derived): number { return value.own; }\n",
            ),
        ),
        (
            "qualified-base",
            concat!(
                "namespace Types { export interface Base { value: number } }\n",
                "interface Derived extends Types.Base { own: number }\n",
                "function read(value: Derived): number { return value.own; }\n",
            ),
        ),
    ];

    for (index, (name, source)) in cases.into_iter().enumerate() {
        let parsed = parse_source_file(source);
        assert!(
            parsed.diagnostics.is_empty(),
            "{name}: {:?}",
            parsed.diagnostics
        );
        let file = FileId::new(u32::try_from(index + 10).unwrap());
        let mut context = checker_context(
            &parsed,
            file,
            &format!("/project/interface-heritage-{name}.ts"),
        );
        let before = (
            context.store().type_len(),
            context.store().symbol_store().symbol_table_len(),
        );

        let first = context.check_source_file(file).unwrap_err();
        assert!(
            matches!(first, SourceCheckError::Unsupported(_)),
            "{name}: {first:?}"
        );
        assert_eq!(
            (
                context.store().type_len(),
                context.store().symbol_store().symbol_table_len(),
            ),
            before,
            "{name} published semantic identities before rejecting the boundary",
        );
        assert_eq!(context.check_source_file(file), Err(first), "{name}");
    }
}

#[test]
fn compatible_interface_bases_merge_properties_in_declaration_order() {
    let parsed = parse_source_file(concat!(
        "interface First { data: any; which: number; metaKey: any }\n",
        "interface Second { data: any }\n",
        "interface Combined extends First, Second {}\n",
        "const value: Combined = { data: 1, which: 2, metaKey: 3 };\n",
    ));
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(40);
    let mut context = checker_context(&parsed, file, "/project/multiple-bases.ts");
    let first = interface_symbol(&parsed, file, &context, "First");
    let second = interface_symbol(&parsed, file, &context, "Second");
    let combined = interface_symbol(&parsed, file, &context, "Combined");

    context.check_source_file(file).unwrap();
    assert!(
        context.diagnostics().is_empty(),
        "{:?}",
        context.diagnostics()
    );

    let first_type = declared_type(&context, first);
    let second_type = declared_type(&context, second);
    let combined_type = declared_type(&context, combined);
    let TypeData::Interface(interface) =
        context.store().type_payload(combined_type).unwrap().data()
    else {
        panic!("Combined must retain its interface payload")
    };
    assert_eq!(
        interface.resolved_base_types.as_deref(),
        Some(&[first_type, second_type][..]),
    );
    assert_eq!(
        interface_property_names(&context, combined_type),
        (
            Vec::new(),
            vec!["data".to_owned(), "which".to_owned(), "metaKey".to_owned()],
        ),
    );
    assert_eq!(
        context.is_type_assignable_to(combined_type, first_type),
        Ok(true)
    );
    assert_eq!(
        context.is_type_assignable_to(combined_type, second_type),
        Ok(true)
    );

    let warm = (
        context.store().type_len(),
        context.store().symbol_len(),
        context.store().relation_state_snapshot(),
    );
    context.recheck_source_file(file).unwrap();
    assert_eq!(
        (
            context.store().type_len(),
            context.store().symbol_len(),
            context.store().relation_state_snapshot(),
        ),
        warm,
    );
}
