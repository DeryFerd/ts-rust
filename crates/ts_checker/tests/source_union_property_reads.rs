use ts_ast::{FileId, NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    CheckFlags, EscapedName, SemanticSymbolId, SymbolFlags,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, SourceCheckError, TypeData, TypeId,
    UnsupportedSourceSyntax, ValueSymbolLinks,
};
use ts_parser::{ParseResult, parse_source_file};

fn context(parsed: &ParseResult, file: FileId) -> CanonicalCheckerContext<'_> {
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            file,
            CanonicalSourceFileFacts::new(
                EscapedName::source(format!("\"/project/union-read-{}.ts\"", file.index())),
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

fn access_parts(parsed: &ParseResult, file: FileId) -> (NodeRef, NodeRef, NodeRef) {
    parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            let NodeData::PropertyAccessExpression(access) = &record.data else {
                return None;
            };
            (record.kind == SyntaxKind::PropertyAccessExpression).then(|| {
                (
                    NodeRef::new(parsed.arena.id(), file, node),
                    NodeRef::new(parsed.arena.id(), file, access.expression),
                    NodeRef::new(parsed.arena.id(), file, access.name),
                )
            })
        })
        .expect("fixture must contain one property access")
}

fn resolved_type(context: &CanonicalCheckerContext<'_>, node: NodeRef) -> TypeId {
    context
        .store()
        .type_node_links(node)
        .and_then(|links| links.resolved_type)
        .unwrap_or_else(|| panic!("missing resolved type for {node:?}"))
}

fn cached_union_property(
    context: &CanonicalCheckerContext<'_>,
    union: TypeId,
    name: &str,
) -> Option<SemanticSymbolId> {
    let TypeData::Union(data) = context.store().type_payload(union).unwrap().data() else {
        panic!("receiver must remain a union")
    };
    data.union
        .property_cache
        .and_then(|cache| context.store().symbol_table(cache))
        .and_then(|cache| cache.get_source(name))
}

fn union_has_property_cache(context: &CanonicalCheckerContext<'_>, union: TypeId) -> bool {
    let TypeData::Union(data) = context.store().type_payload(union).unwrap().data() else {
        panic!("receiver must remain a union")
    };
    data.union
        .property_cache
        .is_some_and(|cache| context.store().symbol_table(cache).is_some())
}

type ObservableState = (
    usize,
    usize,
    usize,
    Option<TypeId>,
    Option<SemanticSymbolId>,
    Vec<(u32, Option<NodeRef>, String)>,
);

fn observable_state(context: &CanonicalCheckerContext<'_>, access: NodeRef) -> ObservableState {
    (
        context.store().type_len(),
        context.store().symbol_store().checker_created_symbol_len(),
        context.store().symbol_store().symbol_table_len(),
        context
            .store()
            .type_node_links(access)
            .and_then(|links| links.resolved_type),
        context
            .store()
            .symbol_node_links(access)
            .and_then(|links| links.resolved_symbol),
        context
            .diagnostics()
            .as_slice()
            .iter()
            .map(|diagnostic| {
                (
                    diagnostic.diagnostic.code(),
                    diagnostic.node,
                    diagnostic.diagnostic.render().unwrap(),
                )
            })
            .collect(),
    )
}

#[test]
fn named_declared_union_read_publishes_synthetic_property_and_replays_warm() {
    let parsed = parse_source_file(concat!(
        "type Left = { value: string };\n",
        "type Right = { value: number };\n",
        "type Both = Left | Right;\n",
        "function read(input: Both): string | number { return input.value; }\n",
    ));
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(0);
    let (access, receiver, _) = access_parts(&parsed, file);
    let mut context = context(&parsed, file);

    context.check_source_file(file).unwrap();

    assert!(context.diagnostics().is_empty());
    let union = resolved_type(&context, receiver);
    let property_type = resolved_type(&context, access);
    assert_eq!(
        context.type_to_string(property_type).unwrap(),
        "string | number"
    );
    let property = context
        .store()
        .symbol_node_links(access)
        .and_then(|links| links.resolved_symbol)
        .expect("successful access must publish its synthetic symbol");
    assert_eq!(
        cached_union_property(&context, union, "value"),
        Some(property)
    );
    let record = context.store().symbol(property).unwrap();
    assert_eq!(
        record.flags(),
        SymbolFlags::PROPERTY | SymbolFlags::TRANSIENT
    );
    assert_eq!(
        record.check_flags(),
        CheckFlags::SYNTHETIC_PROPERTY
            | CheckFlags::CONTAINS_PUBLIC
            | CheckFlags::HAS_NON_UNIFORM_TYPE
    );
    assert_eq!(
        context.store().value_symbol_links(property),
        Some(&ValueSymbolLinks {
            resolved_type: Some(property_type),
            containing_type: Some(union),
            ..ValueSymbolLinks::default()
        })
    );

    let warm = observable_state(&context, access);
    context.recheck_source_file(file).unwrap();
    assert_eq!(observable_state(&context, access), warm);
}

#[test]
fn interface_and_type_literal_union_read_publishes_a_shared_literal_property() {
    let parsed = parse_source_file(concat!(
        "interface Left { kind: \"left\" }\n",
        "type Right = { kind: \"right\" };\n",
        "type Both = Left | Right;\n",
        "function read(input: Both): \"left\" | \"right\" { return input.kind; }\n",
    ));
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(6);
    let (access, receiver, _) = access_parts(&parsed, file);
    let mut context = context(&parsed, file);

    context.check_source_file(file).unwrap();

    assert!(context.diagnostics().is_empty());
    let union = resolved_type(&context, receiver);
    let property_type = resolved_type(&context, access);
    assert_eq!(
        context.type_to_string(property_type).unwrap(),
        "\"left\" | \"right\""
    );
    let property = cached_union_property(&context, union, "kind")
        .expect("the shared literal property must be cached");
    assert_eq!(
        context.store().symbol(property).unwrap().check_flags(),
        CheckFlags::SYNTHETIC_PROPERTY
            | CheckFlags::CONTAINS_PUBLIC
            | CheckFlags::HAS_NON_UNIFORM_TYPE
            | CheckFlags::HAS_LITERAL_TYPE
    );

    let warm = observable_state(&context, access);
    context.recheck_source_file(file).unwrap();
    assert_eq!(observable_state(&context, access), warm);
}

#[test]
fn partial_declared_union_read_emits_first_missing_ts2339_and_replays_warm() {
    let parsed = parse_source_file(concat!(
        "type Left = { value: string };\n",
        "type Right = { other: number };\n",
        "type Both = Left | Right;\n",
        "function read(input: Both): any { return input.value; }\n",
    ));
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(1);
    let (access, receiver, name) = access_parts(&parsed, file);
    let mut context = context(&parsed, file);

    context.check_source_file(file).unwrap();

    let union = resolved_type(&context, receiver);
    assert_eq!(
        resolved_type(&context, access),
        context.store().intrinsic_bootstrap().unwrap().error_type
    );
    assert!(context.store().symbol_node_links(access).is_none());
    let partial = cached_union_property(&context, union, "value")
        .expect("partial lookup must retain its filtered synthetic memo");
    let record = context.store().symbol(partial).unwrap();
    assert_eq!(
        record.flags(),
        SymbolFlags::PROPERTY | SymbolFlags::TRANSIENT
    );
    assert_eq!(
        record.check_flags(),
        CheckFlags::SYNTHETIC_PROPERTY | CheckFlags::CONTAINS_PUBLIC | CheckFlags::READ_PARTIAL
    );
    let [diagnostic] = context.diagnostics().as_slice() else {
        panic!("expected one TS2339")
    };
    assert_eq!(diagnostic.node, Some(name));
    assert_eq!(diagnostic.range_override, None);
    assert_eq!(diagnostic.diagnostic.code(), 2339);
    assert_eq!(
        diagnostic.diagnostic.render().unwrap(),
        concat!(
            "Property 'value' does not exist on type 'Both'.\n",
            "  Property 'value' does not exist on type 'Right'.",
        )
    );
    assert!(diagnostic.related_information.is_empty());

    let warm = observable_state(&context, access);
    context.recheck_source_file(file).unwrap();
    assert_eq!(observable_state(&context, access), warm);
}

#[test]
fn all_missing_declared_union_read_caches_only_namespace_and_replays_warm() {
    let parsed = parse_source_file(concat!(
        "type Left = { left: string };\n",
        "type Right = { right: number };\n",
        "function read(input: Left | Right): any { return input.missing; }\n",
    ));
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(2);
    let (access, receiver, name) = access_parts(&parsed, file);
    let mut context = context(&parsed, file);

    context.check_source_file(file).unwrap();

    let union = resolved_type(&context, receiver);
    assert_eq!(
        resolved_type(&context, access),
        context.store().intrinsic_bootstrap().unwrap().error_type
    );
    assert!(context.store().symbol_node_links(access).is_none());
    assert!(union_has_property_cache(&context, union));
    assert_eq!(cached_union_property(&context, union, "missing"), None);
    let [diagnostic] = context.diagnostics().as_slice() else {
        panic!("expected one TS2339")
    };
    assert_eq!(diagnostic.node, Some(name));
    assert_eq!(diagnostic.range_override, None);
    assert_eq!(diagnostic.diagnostic.code(), 2339);
    assert_eq!(
        diagnostic.diagnostic.render().unwrap(),
        concat!(
            "Property 'missing' does not exist on type 'Left | Right'.\n",
            "  Property 'missing' does not exist on type 'Left'.",
        )
    );
    assert!(diagnostic.related_information.is_empty());

    let warm = observable_state(&context, access);
    context.recheck_source_file(file).unwrap();
    assert_eq!(observable_state(&context, access), warm);
}

#[test]
fn stable_common_spelling_suggestion_emits_ts2551_with_first_missing_detail() {
    let parsed = parse_source_file(concat!(
        "type A = { notInB: string; notInC: string };\n",
        "type B = { notInC: number };\n",
        "type AB = A | B;\n",
        "function read(input: AB): any { return input.notInB; }\n",
    ));
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(3);
    let (access, receiver, name) = access_parts(&parsed, file);
    let mut context = context(&parsed, file);

    context.check_source_file(file).unwrap();

    let union = resolved_type(&context, receiver);
    assert_eq!(
        resolved_type(&context, access),
        context.store().intrinsic_bootstrap().unwrap().error_type
    );
    assert!(context.store().symbol_node_links(access).is_none());
    assert!(
        cached_union_property(&context, union, "notInB").is_some(),
        "partial lookup must retain its filtered synthetic memo"
    );
    let [diagnostic] = context.diagnostics().as_slice() else {
        panic!("expected one TS2551")
    };
    assert_eq!(diagnostic.node, Some(name));
    assert_eq!(diagnostic.range_override, None);
    assert_eq!(diagnostic.diagnostic.code(), 2551);
    assert_eq!(
        diagnostic.diagnostic.render().unwrap(),
        concat!(
            "Property 'notInB' does not exist on type 'AB'. Did you mean 'notInC'?\n",
            "  Property 'notInB' does not exist on type 'B'.",
        )
    );
    assert!(diagnostic.related_information.is_empty());

    let warm = observable_state(&context, access);
    context.recheck_source_file(file).unwrap();
    assert_eq!(observable_state(&context, access), warm);
}

#[test]
#[allow(clippy::too_many_lines)] // Global, constituent, and warm identities share one source check.
fn apparent_global_object_property_keeps_declared_owner_and_union_identity() {
    let parsed = parse_source_file(concat!(
        "interface Object { toString: string }\n",
        "type Left = { left: string };\n",
        "type Right = { right: number };\n",
        "type Both = Left | Right;\n",
        "function read(input: Both): any { return input.toString; }\n",
    ));
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(4);
    let (access, receiver, _) = access_parts(&parsed, file);
    let mut context = context(&parsed, file);

    context.check_source_file(file).unwrap();

    assert!(context.diagnostics().is_empty());
    let union = resolved_type(&context, receiver);
    let string = context.store().intrinsic_bootstrap().unwrap().string_type;
    let number = context.store().intrinsic_bootstrap().unwrap().number_type;
    assert_eq!(resolved_type(&context, access), string);
    let TypeData::Union(data) = context.store().type_payload(union).unwrap().data() else {
        panic!("receiver must remain a union")
    };
    let constituents = data.union.types.clone();
    assert_eq!(constituents.len(), 2);
    assert!(data.union.property_cache.is_none());

    let object = context
        .store()
        .symbol_table(context.globals())
        .unwrap()
        .get_source("Object")
        .unwrap();
    let members = context.store().symbol(object).unwrap().members().unwrap();
    let property = context
        .store()
        .symbol_table(members)
        .unwrap()
        .get_source("toString")
        .unwrap();
    let record = context.store().symbol(property).unwrap();
    assert_eq!(record.parent(), Some(object));
    assert_eq!(record.flags(), SymbolFlags::PROPERTY);
    assert_eq!(record.check_flags(), CheckFlags::NONE);
    assert_eq!(
        context
            .store()
            .symbol_node_links(access)
            .unwrap()
            .resolved_symbol,
        Some(property)
    );
    assert_eq!(
        context.store().value_symbol_links(property),
        Some(&ValueSymbolLinks {
            resolved_type: Some(string),
            ..ValueSymbolLinks::default()
        })
    );
    let TypeData::Interface(object_type) = context
        .store()
        .type_payload(context.global_types().object_type)
        .unwrap()
        .data()
    else {
        panic!("Object must retain its declared interface")
    };
    assert!(!object_type.declared_members_resolved);
    assert!(object_type.reference.object.structured.members.is_none());

    let warm = observable_state(&context, access);
    assert_eq!(context.type_to_string(union).unwrap(), "Both");
    assert_eq!(context.type_to_string(string).unwrap(), "string");
    let mut fields = Vec::new();
    for (constituent, name, field, expected) in [
        (constituents[0], "Left", "left", string),
        (constituents[1], "Right", "right", number),
    ] {
        assert_eq!(context.type_to_string(constituent).unwrap(), name);
        let type_record = context.store().type_payload(constituent).unwrap();
        let TypeData::Object(object) = type_record.data() else {
            panic!("each constituent must retain its own object type")
        };
        let [property] = object.structured.properties.as_deref().unwrap() else {
            panic!("each constituent must retain exactly its own field")
        };
        let record = context.store().symbol(*property).unwrap();
        assert_eq!(record.name().as_utf8(), Some(field));
        assert_eq!(record.parent(), type_record.symbol());
        assert_eq!(
            context
                .store()
                .value_symbol_links(*property)
                .unwrap()
                .resolved_type,
            Some(expected)
        );
        fields.push((*property, expected));
    }
    assert_eq!(observable_state(&context, access), warm);

    context.recheck_source_file(file).unwrap();
    assert_eq!(observable_state(&context, access), warm);
    assert_eq!(resolved_type(&context, receiver), union);
    let TypeData::Union(data) = context.store().type_payload(union).unwrap().data() else {
        panic!("receiver must remain a union after recheck")
    };
    assert_eq!(data.union.types, constituents);
    assert!(data.union.property_cache.is_none());
    for (property, expected) in fields {
        assert_eq!(
            context
                .store()
                .value_symbol_links(property)
                .unwrap()
                .resolved_type,
            Some(expected)
        );
    }
}

#[test]
fn missing_global_object_member_keeps_the_union_diagnostic() {
    let parsed = parse_source_file(concat!(
        "interface Object { toString: string }\n",
        "type Left = { left: string };\n",
        "type Right = { right: number };\n",
        "type Both = Left | Right;\n",
        "function read(input: Both): any { return input.missing; }\n",
    ));
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(7);
    let (access, receiver, name) = access_parts(&parsed, file);
    let mut context = context(&parsed, file);

    context.check_source_file(file).unwrap();

    let union = resolved_type(&context, receiver);
    assert_eq!(context.type_to_string(union).unwrap(), "Both");
    assert_eq!(
        resolved_type(&context, access),
        context.store().intrinsic_bootstrap().unwrap().error_type
    );
    assert!(context.store().symbol_node_links(access).is_none());
    assert_eq!(cached_union_property(&context, union, "missing"), None);
    let [diagnostic] = context.diagnostics().as_slice() else {
        panic!("expected one TS2339")
    };
    assert_eq!(diagnostic.node, Some(name));
    assert_eq!(diagnostic.diagnostic.code(), 2339);
    assert_eq!(
        diagnostic.diagnostic.render().unwrap(),
        concat!(
            "Property 'missing' does not exist on type 'Both'.\n",
            "  Property 'missing' does not exist on type 'Left'.",
        )
    );
    assert!(diagnostic.related_information.is_empty());

    let warm = observable_state(&context, access);
    context.recheck_source_file(file).unwrap();
    assert_eq!(observable_state(&context, access), warm);
    assert_eq!(resolved_type(&context, receiver), union);
}

#[test]
fn comparator_dependent_spelling_tie_fails_closed_before_union_publication() {
    let parsed = parse_source_file(concat!(
        "type Left = { abcxef: string; abcdxf: string };\n",
        "type Right = { abcxef: number; abcdxf: number };\n",
        "type Both = Left | Right;\n",
        "function read(input: Both): any { return input.abcdef; }\n",
    ));
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(5);
    let (access, receiver, _) = access_parts(&parsed, file);
    let mut context = context(&parsed, file);

    assert_eq!(
        context.check_source_file(file),
        Err(SourceCheckError::Unsupported(
            UnsupportedSourceSyntax::Property(access)
        ))
    );

    let union = resolved_type(&context, receiver);
    let TypeData::Union(data) = context.store().type_payload(union).unwrap().data() else {
        panic!("receiver must remain a union")
    };
    assert!(data.union.property_cache.is_none());
    assert!(context.store().type_node_links(access).is_none());
    assert!(context.store().symbol_node_links(access).is_none());
    assert!(context.diagnostics().is_empty());
}
