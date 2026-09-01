use ts_ast::{FileId, NodeData, NodeRef};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    CheckFlags, EscapedName, SemanticSymbolId, SymbolFlags,
};
use ts_checker::semantic::{
    AliasTargetState, CanonicalCheckerContext, CanonicalCheckerOptions,
    CanonicalModuleResolutionEntry, CanonicalModuleResolutionManifestInput,
    CanonicalModuleResolutionMode, CanonicalResolvedModuleInput, SourceCheckError, TypeData,
    TypeId,
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
    checker_context_with_options(parsed, file, path, CanonicalCheckerOptions::default())
}

fn checker_context_with_options<'arena>(
    parsed: &'arena ParseResult,
    file: FileId,
    path: &str,
    options: CanonicalCheckerOptions,
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
        options,
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

fn own_interface_property(
    context: &CanonicalCheckerContext<'_>,
    type_: TypeId,
    name: &str,
) -> SemanticSymbolId {
    let TypeData::Interface(interface) = context.store().type_payload(type_).unwrap().data() else {
        panic!("expected an interface type")
    };
    context
        .store()
        .symbol_table(interface.declared_members.unwrap())
        .unwrap()
        .get_source(name)
        .unwrap_or_else(|| panic!("missing own property {name}"))
}

fn override_snapshot(
    context: &CanonicalCheckerContext<'_>,
) -> impl std::fmt::Debug + PartialEq + use<> {
    let store = context.store();
    (
        [
            store.type_len(),
            store.type_alias_len(),
            store.symbol_len(),
            store.mapper_len(),
            store.signature_len(),
            store.index_info_len(),
            store.symbol_store().symbol_table_len(),
        ],
        store.relation_state_snapshot(),
        context.diagnostics().clone(),
    )
}

#[test]
#[allow(clippy::too_many_lines)] // Cold checks and forced replay share the source and proxy identities.
fn generic_base_function_parameters_preserve_lazy_members_cold_and_warm() {
    for method in ["", "; next(): T"] {
        for (parameter_type, body, reads_inherited) in [
            ("Derived", "return value.own;", false),
            ("Derived", "return 1;", false),
            ("Derived", "return value.value;", true),
            ("Base<number>", "return value.value;", true),
        ] {
            let source = format!(
                "interface Base<T> {{ value: T{method} }}\n\
                 interface Derived extends Base<number> {{ own: number }}\n\
                 function read(value: {parameter_type}): number {{ {body} }}\n",
            );
            let parsed = parse_source_file(&source);
            assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
            let file = FileId::new(42);
            let mut context =
                checker_context(&parsed, file, "/project/generic-base-callable-graph.ts");
            context
                .check_source_file(file)
                .unwrap_or_else(|error| panic!("{parameter_type}, {body}, {method}: {error:?}"));
            assert!(context.diagnostics().is_empty());
            let derived = declared_type(
                &context,
                interface_symbol(&parsed, file, &context, "Derived"),
            );
            let TypeData::Interface(data) = context.store().type_payload(derived).unwrap().data()
            else {
                panic!("Derived must retain its interface identity")
            };
            let base = data.resolved_base_types.as_ref().unwrap()[0];
            let members = context
                .store()
                .symbol_table(data.reference.object.structured.members.unwrap())
                .unwrap();
            let inherited = members.get_source("value").unwrap();
            let next = members.get_source("next");
            assert_eq!(next.is_some(), !method.is_empty());
            let number = context.store().intrinsic_bootstrap().unwrap().number_type;
            assert_eq!(
                context
                    .store()
                    .value_symbol_links(inherited)
                    .unwrap()
                    .resolved_type,
                reads_inherited.then_some(number),
            );
            if let Some(next) = next {
                assert!(
                    context
                        .store()
                        .value_symbol_links(next)
                        .unwrap()
                        .resolved_type
                        .is_none()
                );
            }
            let parameter = parsed
                .arena
                .iter()
                .find_map(|(node, record)| {
                    (record.kind == ts_ast::SyntaxKind::Parameter).then_some(NodeRef::new(
                        parsed.arena.id(),
                        file,
                        node,
                    ))
                })
                .unwrap();
            let parameter = context.file(file).unwrap().1.symbol(parameter).unwrap();
            assert_eq!(
                context
                    .store()
                    .value_symbol_links(parameter)
                    .unwrap()
                    .resolved_type,
                Some(if parameter_type == "Derived" {
                    derived
                } else {
                    base
                }),
            );
            let snapshot = |context: &CanonicalCheckerContext<'_>| {
                (
                    context.store().type_len(),
                    context.store().symbol_len(),
                    context.store().mapper_len(),
                    context.store().signature_len(),
                    context.store().index_info_len(),
                    context.store().symbol_store().symbol_table_len(),
                    context.store().relation_state_snapshot(),
                    context.diagnostics().clone(),
                )
            };
            let warm = snapshot(&context);
            for _ in 0..2 {
                context.recheck_source_file(file).unwrap_or_else(|error| {
                    panic!("warm {parameter_type}, {body}, {method}: {error:?}")
                });
                assert_eq!(snapshot(&context), warm);
                assert_eq!(
                    context
                        .store()
                        .value_symbol_links(inherited)
                        .unwrap()
                        .resolved_type,
                    reads_inherited.then_some(number),
                );
                if let Some(next) = next {
                    assert!(
                        context
                            .store()
                            .value_symbol_links(next)
                            .unwrap()
                            .resolved_type
                            .is_none()
                    );
                }
            }
        }
    }
}

#[test]
#[allow(clippy::too_many_lines)] // Both bodies must keep the same inherited index through forced replay.
fn generic_base_index_values_preserve_callable_cold_and_warm_checks() {
    let declarations =
        parse_source_file("interface Base<T> { value: T; [index: number]: Array<number>; }");
    assert!(
        declarations.diagnostics.is_empty(),
        "{:?}",
        declarations.diagnostics
    );
    for (body, reads_inherited) in [("return 1;", false), ("return value.value;", true)] {
        let source = format!(
            "interface Array<T> {{}} interface ReadonlyArray<T> {{}}\n\
             interface Derived extends Base<number> {{}}\n\
             function read(value: Derived): number {{ {body} }}",
        );
        let parsed = parse_source_file(&source);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(43);
        let library_file = FileId::new(1043);
        let mut binder = CanonicalBinder::new();
        for (file, source, is_declaration) in
            [(library_file, &declarations, true), (file, &parsed, false)]
        {
            binder
                .bind_source_file_with_facts(
                    &source.arena,
                    source.source_file,
                    file,
                    CanonicalSourceFileFacts::new(
                        EscapedName::source(if is_declaration {
                            "\"/project/index-base.d.ts\""
                        } else {
                            "\"/project/generic-base-index-graph.ts\""
                        }),
                        CanonicalSourceLanguage::TypeScript,
                        is_declaration,
                        CanonicalModuleState::Script,
                    ),
                )
                .unwrap();
            binder
                .bind_typescript_declaration_slice(&source.arena, file)
                .unwrap();
        }
        let mut context = CanonicalCheckerContext::new(
            binder.finish(),
            [(library_file, &declarations.arena), (file, &parsed.arena)]
                .into_iter()
                .collect(),
            CanonicalCheckerOptions::default(),
        )
        .unwrap();
        context.check_source_file(file).unwrap();
        assert!(context.diagnostics().is_empty());
        let derived = declared_type(
            &context,
            interface_symbol(&parsed, file, &context, "Derived"),
        );
        let TypeData::Interface(data) = context.store().type_payload(derived).unwrap().data()
        else {
            panic!("Derived must retain its interface identity")
        };
        let base = data.resolved_base_types.as_ref().unwrap()[0];
        let structured = &data.reference.object.structured;
        let index = structured.index_infos.as_ref().unwrap()[0];
        let TypeData::TypeReference(base_data) = context.store().type_payload(base).unwrap().data()
        else {
            panic!("Base<number> must retain its type-reference identity")
        };
        assert_eq!(
            base_data.object.structured.index_infos.as_deref(),
            Some(&[index][..]),
        );
        let value = context
            .store()
            .symbol_table(structured.members.unwrap())
            .and_then(|members| members.get_source("value"))
            .unwrap();
        let number = context.store().intrinsic_bootstrap().unwrap().number_type;
        let array = context.store().index_info(index).unwrap().value_type();
        assert_eq!(context.type_to_string(array).unwrap(), "number[]");
        assert_eq!(
            context
                .store()
                .value_symbol_links(value)
                .unwrap()
                .resolved_type,
            reads_inherited.then_some(number),
        );
        let snapshot = |context: &CanonicalCheckerContext<'_>| {
            (
                context.store().type_len(),
                context.store().symbol_len(),
                context.store().mapper_len(),
                context.store().signature_len(),
                context.store().index_info_len(),
                context.store().symbol_store().symbol_table_len(),
                context.store().relation_state_snapshot(),
                context.diagnostics().clone(),
            )
        };
        let warm = snapshot(&context);
        for _ in 0..2 {
            context.recheck_source_file(file).unwrap();
            assert_eq!(snapshot(&context), warm);
            assert_eq!(
                context.store().index_info(index).unwrap().value_type(),
                array
            );
            assert_eq!(
                context
                    .store()
                    .value_symbol_links(value)
                    .unwrap()
                    .resolved_type,
                reads_inherited.then_some(number),
            );
        }
    }
}

#[test]
fn keyof_alias_with_nested_generic_heritage_checks_cold_and_warm() {
    let parsed = parse_source_file(concat!(
        "interface Array<T> {} interface ReadonlyArray<T> {} ",
        "interface Base<T> { value: T } ",
        "interface Derived extends Base<number> { own: number } ",
        "type Keys = keyof { nested: Derived }; ",
        "function read(value: Keys): number { return 1; }",
    ));
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(44);
    let mut context = checker_context(&parsed, file, "/project/nested-heritage-keyof.ts");
    context.check_source_file(file).unwrap();
    assert!(context.diagnostics().is_empty());
    let parameter = parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            (record.kind == ts_ast::SyntaxKind::Parameter).then_some(NodeRef::new(
                parsed.arena.id(),
                file,
                node,
            ))
        })
        .unwrap();
    let parameter = context.file(file).unwrap().1.symbol(parameter).unwrap();
    let key = context
        .store()
        .value_symbol_links(parameter)
        .unwrap()
        .resolved_type
        .unwrap();
    assert_eq!(context.type_to_string(key).unwrap(), "\"nested\"");
    let snapshot = |context: &CanonicalCheckerContext<'_>| {
        (
            context.store().type_len(),
            context.store().symbol_len(),
            context.store().mapper_len(),
            context.store().signature_len(),
            context.store().index_info_len(),
            context.store().symbol_store().symbol_table_len(),
            context.store().relation_state_snapshot(),
            context.diagnostics().clone(),
        )
    };
    let warm = snapshot(&context);
    for _ in 0..2 {
        context.recheck_source_file(file).unwrap();
        assert_eq!(snapshot(&context), warm);
        assert_eq!(
            context
                .store()
                .value_symbol_links(parameter)
                .unwrap()
                .resolved_type,
            Some(key)
        );
    }
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
        concat!(
            "type EventName = 'added' | 'removed';\n",
            "interface Base { value: EventName; inherited: string }\n",
            "interface Derived extends Base { value: 'added' }\n",
            "function read(value: Derived): 'added' { return value.value; }\n",
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
fn interface_override_modifiers_preserve_own_flags() {
    for (base, own, optional, readonly, reverse_assignable) in [
        ("value?: string", "value: string", false, false, false),
        (
            "readonly value: string",
            "value: string",
            false,
            false,
            true,
        ),
        ("value: string", "readonly value: string", false, true, true),
        (
            "readonly value?: string",
            "readonly value?: string",
            true,
            true,
            true,
        ),
    ] {
        let source =
            format!("interface Base {{ {base} }}\ninterface Derived extends Base {{ {own} }}\n");
        let parsed = parse_source_file(&source);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(103);
        let mut context = checker_context(&parsed, file, "/project/interface-override-flags.ts");
        context.check_source_file(file).unwrap();
        assert!(
            context.diagnostics().is_empty(),
            "{:?}",
            context.diagnostics()
        );
        let base = declared_type(&context, interface_symbol(&parsed, file, &context, "Base"));
        let derived = declared_type(
            &context,
            interface_symbol(&parsed, file, &context, "Derived"),
        );
        let property = own_interface_property(&context, derived, "value");
        let symbol = context.store().symbol(property).unwrap();
        assert_eq!(symbol.flags().contains(SymbolFlags::OPTIONAL), optional);
        assert_eq!(
            symbol.check_flags().contains(CheckFlags::READONLY),
            readonly
        );
        assert_eq!(context.is_type_assignable_to(derived, base), Ok(true));
        assert_eq!(
            context.is_type_assignable_to(base, derived),
            Ok(reverse_assignable),
        );
        let warm = override_snapshot(&context);
        context.check_source_file(file).unwrap();
        context.recheck_source_file(file).unwrap();
        assert_eq!(override_snapshot(&context), warm);
        assert_eq!(own_interface_property(&context, derived, "value"), property);
    }
}

#[test]
#[allow(clippy::too_many_lines)] // Each invalid extension keeps its real property and replay state.
fn incompatible_interface_overrides_report_diagnostics_and_keep_own_properties() {
    let cases = [
        (
            concat!(
                "interface Base { value: number }\n",
                "interface Derived extends Base { value: string }\n",
                "function read(value: Derived): string { return value.value; }\n",
            ),
            (false, false),
            "value",
            ("string", Some("string"), false),
            concat!(
                "Interface 'Derived' incorrectly extends interface 'Base'.\n",
                "  Types of property 'value' are incompatible.\n",
                "    Type 'string' is not assignable to type 'number'.",
            ),
        ),
        (
            concat!(
                "type EventName = 'added' | 'removed';\n",
                "interface Base { type: EventName }\n",
                "interface Derived extends Base { type: 'other' }\n",
                "function read(value: Derived): 'other' { return value.type; }\n",
            ),
            (true, false),
            "type",
            ("\"other\"", Some("\"other\""), false),
            concat!(
                "Interface 'Derived' incorrectly extends interface 'Base'.\n",
                "  Types of property 'type' are incompatible.\n",
                "    Type '\"other\"' is not assignable to type 'EventName'.",
            ),
        ),
        (
            concat!(
                "interface Base { value: string | undefined }\n",
                "interface Derived extends Base { value?: string }\n",
                "function read(value: Derived): string | undefined { return value.value; }\n",
            ),
            (true, false),
            "value",
            ("string", Some("string | undefined"), true),
            concat!(
                "Interface 'Derived' incorrectly extends interface 'Base'.\n",
                "  Property 'value' is optional in type 'Derived' but required in type 'Base'.",
            ),
        ),
        (
            concat!(
                "interface Base { value: string }\n",
                "interface Derived extends Base { value?: string }\n",
                "function read(value: Derived): string | undefined { return value.value; }\n",
            ),
            (true, false),
            "value",
            ("string", Some("string | undefined"), true),
            concat!(
                "Interface 'Derived' incorrectly extends interface 'Base'.\n",
                "  Types of property 'value' are incompatible.\n",
                "    Type 'string | undefined' is not assignable to type 'string'.\n",
                "      Type 'undefined' is not assignable to type 'string'.",
            ),
        ),
        (
            concat!(
                "interface Base { value: string }\n",
                "interface Derived extends Base { value?: string }\n",
            ),
            (true, true),
            "value",
            ("string", None, true),
            concat!(
                "Interface 'Derived' incorrectly extends interface 'Base'.\n",
                "  Property 'value' is optional in type 'Derived' but required in type 'Base'.",
            ),
        ),
        (
            concat!(
                "interface Base { value: string }\n",
                "interface Derived extends Base { value?: any }\n",
            ),
            (true, false),
            "value",
            ("any", None, true),
            concat!(
                "Interface 'Derived' incorrectly extends interface 'Base'.\n",
                "  Property 'value' is optional in type 'Derived' but required in type 'Base'.",
            ),
        ),
        (
            concat!(
                "interface Base { value: unknown }\n",
                "interface Derived extends Base { value?: unknown }\n",
            ),
            (true, false),
            "value",
            ("unknown", None, true),
            concat!(
                "Interface 'Derived' incorrectly extends interface 'Base'.\n",
                "  Property 'value' is optional in type 'Derived' but required in type 'Base'.",
            ),
        ),
        (
            concat!(
                "interface Base { value: string }\n",
                "interface Derived extends Base { value?: unknown }\n",
            ),
            (true, false),
            "value",
            ("unknown", None, true),
            concat!(
                "Interface 'Derived' incorrectly extends interface 'Base'.\n",
                "  Types of property 'value' are incompatible.\n",
                "    Type 'unknown' is not assignable to type 'string'.",
            ),
        ),
        (
            concat!(
                "interface Base { p: string }\n",
                "interface Derived extends Base { p: string | undefined }\n",
            ),
            (true, false),
            "p",
            ("string | undefined", None, false),
            concat!(
                "Interface 'Derived' incorrectly extends interface 'Base'.\n",
                "  Types of property 'p' are incompatible.\n",
                "    Type 'string | undefined' is not assignable to type 'string'.\n",
                "      Type 'undefined' is not assignable to type 'string'.",
            ),
        ),
        (
            concat!(
                "interface InnerBase { x: string; y: string }\n",
                "interface InnerDerived { x?: string; y: number }\n",
                "interface Base { p: InnerBase }\n",
                "interface Derived extends Base { p: InnerDerived }\n",
            ),
            (true, false),
            "p",
            ("InnerDerived", None, false),
            concat!(
                "Interface 'Derived' incorrectly extends interface 'Base'.\n",
                "  The types of 'p.x' are incompatible between these types.\n",
                "    Type 'string | undefined' is not assignable to type 'string'.\n",
                "      Type 'undefined' is not assignable to type 'string'.",
            ),
        ),
        (
            concat!(
                "interface InnerBase { x: string; y: string }\n",
                "interface InnerDerived { x?: string; y: number }\n",
                "interface Base { p: InnerBase }\n",
                "interface Derived extends Base { p: InnerDerived }\n",
            ),
            (true, true),
            "p",
            ("InnerDerived", None, false),
            concat!(
                "Interface 'Derived' incorrectly extends interface 'Base'.\n",
                "  Types of property 'p' are incompatible.\n",
                "    Type 'InnerDerived' is not assignable to type 'InnerBase'.\n",
                "      Property 'x' is optional in type 'InnerDerived' but required in type 'InnerBase'.",
            ),
        ),
        (
            concat!(
                "namespace Events {\n",
                "export interface Base { value: number }\n",
                "export interface Derived extends Base { value: string }\n",
                "}\n",
                "function read(value: Events.Derived): string { return value.value; }\n",
            ),
            (false, false),
            "value",
            ("string", Some("string"), false),
            concat!(
                "Interface 'Derived' incorrectly extends interface 'Base'.\n",
                "  Types of property 'value' are incompatible.\n",
                "    Type 'string' is not assignable to type 'number'.",
            ),
        ),
    ];
    for (
        source,
        (strict_null_checks, exact_optional_property_types),
        property_name,
        (property_display, read_display, optional),
        expected_diagnostic,
    ) in cases
    {
        for query_first in [false, true] {
            let parsed = parse_source_file(source);
            assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
            let file = FileId::new(11);
            let mut options = CanonicalCheckerOptions::default();
            options.intrinsic.strict_null_checks = strict_null_checks;
            options.intrinsic.exact_optional_property_types = exact_optional_property_types;
            let mut context = checker_context_with_options(
                &parsed,
                file,
                "/project/interface-heritage-incompatible-override.ts",
                options,
            );
            let base_owner = interface_symbol(&parsed, file, &context, "Base");
            let derived_owner = interface_symbol(&parsed, file, &context, "Derived");
            let queried =
                query_first.then(|| context.get_declared_type_of_symbol(derived_owner).unwrap());
            assert!(context.diagnostics().is_empty());
            context.check_source_file(file).unwrap();
            let [diagnostic] = context.diagnostics().as_slice() else {
                panic!(
                    "expected one invalid-extension diagnostic: {:?}",
                    context.diagnostics()
                )
            };
            assert_eq!(diagnostic.diagnostic.code(), 2430);
            assert_eq!(diagnostic.diagnostic.arguments, ["Derived", "Base"]);
            assert_eq!(diagnostic.diagnostic.render().unwrap(), expected_diagnostic);
            let anchor = diagnostic.node.unwrap();
            assert_eq!(anchor.file, file);
            assert_eq!(node_text(&parsed, anchor), "Derived");
            assert!(diagnostic.related_information.is_empty());

            let derived = declared_type(&context, derived_owner);
            let base = declared_type(&context, base_owner);
            if let Some(queried) = queried {
                assert_eq!(queried, derived);
            }
            let own = own_interface_property(&context, derived, property_name);
            let own_type = context
                .store()
                .value_symbol_links(own)
                .unwrap()
                .resolved_type
                .unwrap();
            assert_eq!(context.type_to_string(own_type).unwrap(), property_display);
            assert_eq!(
                context
                    .store()
                    .symbol(own)
                    .unwrap()
                    .flags()
                    .contains(SymbolFlags::OPTIONAL),
                optional,
            );
            if let Some(read_display) = read_display {
                let read = read_access(&parsed, file, property_name);
                let read_type = context
                    .store()
                    .type_node_links(read)
                    .unwrap()
                    .resolved_type
                    .unwrap();
                assert_eq!(context.type_to_string(read_type).unwrap(), read_display);
                if optional {
                    let TypeData::Union(union) =
                        context.store().type_payload(read_type).unwrap().data()
                    else {
                        panic!("strict optional property reads must retain undefined")
                    };
                    let undefined = context
                        .store()
                        .intrinsic_bootstrap()
                        .unwrap()
                        .undefined_type;
                    assert_eq!(union.union.types.len(), 2);
                    assert!(union.union.types.contains(&own_type));
                    assert!(union.union.types.contains(&undefined));
                } else {
                    assert_eq!(read_type, own_type);
                }
            }
            assert_eq!(context.is_type_assignable_to(derived, base), Ok(false));

            let warm = override_snapshot(&context);
            context.check_source_file(file).unwrap();
            for _ in 0..2 {
                context.recheck_source_file(file).unwrap();
                assert_eq!(override_snapshot(&context), warm);
                assert_eq!(
                    own_interface_property(&context, derived, property_name),
                    own
                );
            }
        }
    }
}

fn imported_override_context<'arena>(
    source: &'arena ParseResult,
    file: FileId,
    provider: &'arena ParseResult,
    provider_file: FileId,
) -> CanonicalCheckerContext<'arena> {
    let files = [
        (file, source, "\"/project/override.ts\""),
        (provider_file, provider, "\"/project/events.ts\""),
    ];
    let mut binder = CanonicalBinder::new();
    for (file, parsed, path) in files {
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source(path),
                    CanonicalSourceLanguage::TypeScript,
                    false,
                    CanonicalModuleState::External,
                ),
            )
            .unwrap();
    }
    for (file, parsed, _) in files {
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
    }
    let specifier = source
        .arena
        .iter()
        .find_map(|(_, record)| match &record.data {
            NodeData::ImportDeclaration(import) => Some(NodeRef::new(
                source.arena.id(),
                file,
                import.module_specifier,
            )),
            _ => None,
        })
        .unwrap();
    let mut options = CanonicalCheckerOptions::default();
    options.intrinsic.strict_null_checks = true;
    CanonicalCheckerContext::new_with_module_resolutions(
        binder.finish(),
        files
            .iter()
            .map(|(file, parsed, _)| (*file, &parsed.arena))
            .collect(),
        options,
        CanonicalModuleResolutionManifestInput::new([CanonicalModuleResolutionEntry::resolved(
            specifier,
            CanonicalResolvedModuleInput::new(
                provider_file,
                CanonicalModuleResolutionMode::Esm,
                CanonicalModuleResolutionMode::Esm,
            ),
        )]),
    )
    .unwrap()
}

#[test]
#[allow(clippy::too_many_lines)] // Imported ownership, diagnostics and query order share one source pair.
fn imported_interface_overrides_use_the_provider_alias_owner() {
    let provider = parse_source_file(concat!(
        "export type EventName = 'added' | 'removed';\n",
        "export interface Base { type: EventName; inherited: number }\n",
    ));
    let file = FileId::new(105);
    let provider_file = FileId::new(106);
    for (literal, compatible) in [("added", true), ("other", false)] {
        let source = parse_source_file(&format!(
            "import type {{ Base as ImportedBase }} from './events';\n\
             type EventName = 'local';\n\
             interface Derived extends ImportedBase {{ type: '{literal}' }}\n\
             function read(event: Derived): '{literal}' {{ return event.type; }}\n",
        ));
        for (provider_first, query_first) in [(false, false), (false, true), (true, false)] {
            let mut context = imported_override_context(&source, file, &provider, provider_file);
            let base_owner = interface_symbol(&provider, provider_file, &context, "Base");
            let derived_owner = interface_symbol(&source, file, &context, "Derived");
            if provider_first {
                context.check_source_file(provider_file).unwrap();
            }
            let queried =
                query_first.then(|| context.get_declared_type_of_symbol(derived_owner).unwrap());
            assert!(context.diagnostics().is_empty());
            context.check_source_file(file).unwrap();
            let base = declared_type(&context, base_owner);
            let derived = declared_type(&context, derived_owner);
            if let Some(queried) = queried {
                assert_eq!(queried, derived);
            }
            assert_eq!(context.is_type_assignable_to(derived, base), Ok(compatible));
            assert_eq!(
                interface_property_names(&context, derived),
                (
                    vec!["type".to_owned()],
                    vec!["type".to_owned(), "inherited".to_owned()],
                ),
            );
            let own = own_interface_property(&context, derived, "type");
            let inherited = own_interface_property(&context, base, "type");
            assert_ne!(own, inherited);
            let own_type = context
                .store()
                .value_symbol_links(own)
                .unwrap()
                .resolved_type
                .unwrap();
            assert_eq!(
                context.type_to_string(own_type).unwrap(),
                format!("\"{literal}\"")
            );
            let read = read_access(&source, file, "type");
            assert_eq!(
                context.store().type_node_links(read).unwrap().resolved_type,
                Some(own_type)
            );
            let inherited_type = context
                .store()
                .value_symbol_links(inherited)
                .unwrap()
                .resolved_type
                .unwrap();
            let alias = context
                .store()
                .type_payload(inherited_type)
                .unwrap()
                .alias()
                .unwrap();
            let alias_owner = context.store().type_alias(alias).unwrap().symbol().unwrap();
            let declarations = context
                .store()
                .symbol(alias_owner)
                .unwrap()
                .declarations()
                .unwrap();
            assert_eq!(declarations.len(), 1);
            assert_eq!(declarations[0].file, provider_file);
            assert_eq!(declarations[0].arena, provider.arena.id());
            let NodeData::TypeAliasDeclaration(declaration) =
                &provider.arena.get(declarations[0].node).unwrap().data
            else {
                panic!("the inherited property must retain the provider alias declaration")
            };
            assert_eq!(
                node_text(
                    &provider,
                    NodeRef::new(provider.arena.id(), provider_file, declaration.name)
                ),
                "EventName",
            );
            let imported = source
                .arena
                .iter()
                .find_map(|(node, record)| {
                    matches!(record.data, NodeData::ImportSpecifier(_)).then_some(NodeRef::new(
                        source.arena.id(),
                        file,
                        node,
                    ))
                })
                .unwrap();
            let imported = context.file(file).unwrap().1.symbol(imported).unwrap();
            let imported = context.store().get_merged_symbol(imported).unwrap();
            assert_ne!(imported, base_owner);
            assert_eq!(
                context
                    .store()
                    .alias_symbol_links(imported)
                    .unwrap()
                    .alias_target,
                AliasTargetState::Resolved(base_owner),
            );
            assert_eq!(
                context
                    .store()
                    .source_file_links(context.source_file(provider_file).unwrap())
                    .is_some_and(|links| links.type_checked),
                provider_first,
            );
            if compatible {
                assert!(context.diagnostics().is_empty());
            } else {
                let [diagnostic] = context.diagnostics().as_slice() else {
                    panic!("expected one invalid imported extension diagnostic")
                };
                assert_eq!(diagnostic.diagnostic.code(), 2430);
                assert_eq!(diagnostic.diagnostic.arguments, ["Derived", "Base"]);
                assert_eq!(
                    diagnostic.diagnostic.render().unwrap(),
                    concat!(
                        "Interface 'Derived' incorrectly extends interface 'Base'.\n",
                        "  Types of property 'type' are incompatible.\n",
                        "    Type '\"other\"' is not assignable to type 'EventName'.",
                    )
                );
                let anchor = diagnostic.node.unwrap();
                assert_eq!(anchor.file, file);
                assert_eq!(node_text(&source, anchor), "Derived");
                assert!(diagnostic.related_information.is_empty());
            }
            let warm = override_snapshot(&context);
            context.check_source_file(file).unwrap();
            for _ in 0..2 {
                context.recheck_source_file(file).unwrap();
                assert_eq!(override_snapshot(&context), warm);
                assert_eq!(own_interface_property(&context, derived, "type"), own);
            }
        }
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
    ];

    for (index, (name, source)) in [0, 2, 3, 4, 5, 6].into_iter().zip(cases) {
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
fn transitive_interface_bases_preserve_all_inherited_properties() {
    let parsed = parse_source_file(concat!(
        "interface Root { root: number }\n",
        "interface Middle extends Root { middle: number }\n",
        "interface Leaf extends Middle { leaf: number }\n",
        "const item: Leaf = { root: 1, middle: 2, leaf: 3 };\n",
        "function read(value: Leaf): number { return value.root; }\n",
    ));
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(44);
    let mut context = checker_context(&parsed, file, "/project/transitive-interface-base.ts");

    context.check_source_file(file).unwrap();
    assert!(context.diagnostics().is_empty());

    let root = interface_symbol(&parsed, file, &context, "Root");
    let leaf = interface_symbol(&parsed, file, &context, "Leaf");
    assert_eq!(
        context.is_type_assignable_to(declared_type(&context, leaf), declared_type(&context, root)),
        Ok(true)
    );
    assert_eq!(
        interface_property_names(&context, declared_type(&context, leaf)),
        (
            vec![String::from("leaf")],
            vec![
                String::from("leaf"),
                String::from("middle"),
                String::from("root"),
            ],
        )
    );

    let warm = (
        context.store().type_len(),
        context.store().symbol_len(),
        context.store().signature_len(),
        context.diagnostics().clone(),
    );
    context.recheck_source_file(file).unwrap();
    assert_eq!(
        (
            context.store().type_len(),
            context.store().symbol_len(),
            context.store().signature_len(),
            context.diagnostics().clone(),
        ),
        warm,
    );
}

#[test]
fn qualified_namespace_interface_bases_preserve_inherited_properties() {
    let parsed = parse_source_file(concat!(
        "namespace Types { export interface Base { value: number } }\n",
        "interface Derived extends Types.Base { own: number }\n",
        "const item: Derived = { value: 1, own: 2 };\n",
        "function read(value: Derived): number { return value.value; }\n",
    ));
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(43);
    let mut context = checker_context(&parsed, file, "/project/qualified-interface-base.ts");

    context.check_source_file(file).unwrap();
    assert!(context.diagnostics().is_empty());

    let base = interface_symbol(&parsed, file, &context, "Base");
    let derived = interface_symbol(&parsed, file, &context, "Derived");
    assert_eq!(
        context.is_type_assignable_to(
            declared_type(&context, derived),
            declared_type(&context, base)
        ),
        Ok(true)
    );
    assert_eq!(
        interface_property_names(&context, declared_type(&context, derived)),
        (
            vec![String::from("own")],
            vec![String::from("own"), String::from("value")],
        )
    );

    let warm = (
        context.store().type_len(),
        context.store().symbol_len(),
        context.store().signature_len(),
        context.diagnostics().clone(),
    );
    context.recheck_source_file(file).unwrap();
    assert_eq!(
        (
            context.store().type_len(),
            context.store().symbol_len(),
            context.store().signature_len(),
            context.diagnostics().clone(),
        ),
        warm,
    );
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

#[test]
fn callable_interfaces_keep_derived_signatures_before_inherited_signatures() {
    let parsed = parse_source_file(concat!(
        "interface Base { (): string; }\n",
        "interface Derived extends Base { (value: string): string; }\n",
        "declare const callable: Derived;\n",
        "const inherited = callable();\n",
        "const own = callable('value');\n",
    ));
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(41);
    let mut context = checker_context(&parsed, file, "/project/callable-heritage.ts");
    let derived = interface_symbol(&parsed, file, &context, "Derived");

    context.check_source_file(file).unwrap();
    assert!(
        context.diagnostics().is_empty(),
        "{:?}",
        context.diagnostics()
    );

    let TypeData::Interface(interface) = context
        .store()
        .type_payload(declared_type(&context, derived))
        .unwrap()
        .data()
    else {
        panic!("the callable derived interface must retain its interface identity")
    };
    let [own, inherited] = interface
        .reference
        .object
        .structured
        .signatures
        .as_deref()
        .unwrap()
    else {
        panic!("the derived interface must retain one own and one inherited signature")
    };
    assert_eq!(
        context.store().signature(*own).unwrap().parameters().len(),
        1
    );
    assert!(
        context
            .store()
            .signature(*inherited)
            .unwrap()
            .parameters()
            .is_empty()
    );

    let warm = (
        context.store().type_len(),
        context.store().signature_len(),
        context.diagnostics().clone(),
    );
    context.recheck_source_file(file).unwrap();
    assert_eq!(
        (
            context.store().type_len(),
            context.store().signature_len(),
            context.diagnostics().clone(),
        ),
        warm,
    );
}

#[test]
fn merged_interface_reports_one_conflicting_inherited_property() {
    let parsed = parse_source_file(concat!(
        "interface A { value: string; }\n",
        "interface B extends A {}\n",
        "interface C { value: number; }\n",
        "interface D extends C {}\n",
        "interface Combined extends B {}\n",
        "interface Combined extends D {}\n",
    ));
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(42);
    let mut context = checker_context(&parsed, file, "/project/conflicting-interface-bases.ts");
    let combined = interface_symbol(&parsed, file, &context, "Combined");

    context.check_source_file(file).unwrap();

    let [diagnostic] = context.diagnostics().as_slice() else {
        panic!("expected one conflicting-interface diagnostic")
    };
    assert_eq!(diagnostic.diagnostic.code(), 2320);
    assert_eq!(node_text(&parsed, diagnostic.node.unwrap()), "Combined");
    assert_eq!(
        diagnostic.diagnostic.render().unwrap(),
        concat!(
            "Interface 'Combined' cannot simultaneously extend types 'B' and 'D'.\n",
            "  Named property 'value' of types 'B' and 'D' are not identical.",
        ),
    );
    assert!(context.store().declared_type_links(combined).is_none());

    let warm = (
        context.store().type_len(),
        context.store().symbol_len(),
        context.store().signature_len(),
        context.diagnostics().clone(),
    );
    context.recheck_source_file(file).unwrap();
    assert_eq!(
        (
            context.store().type_len(),
            context.store().symbol_len(),
            context.store().signature_len(),
            context.diagnostics().clone(),
        ),
        warm,
    );
}
