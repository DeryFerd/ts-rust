use ts_ast::{FileId, NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, IntrinsicBootstrapOptions, TypeData, TypeId,
};
use ts_parser::{ParseResult, parse_source_file};

const FILE: FileId = FileId::new(96_600);

fn context(parsed: &ParseResult) -> CanonicalCheckerContext<'_> {
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            FILE,
            CanonicalSourceFileFacts::new(
                EscapedName::source("\"/polymorphic-super.ts\""),
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
        CanonicalCheckerOptions {
            intrinsic: IntrinsicBootstrapOptions {
                strict_null_checks: true,
                ..IntrinsicBootstrapOptions::default()
            },
            ..CanonicalCheckerOptions::default()
        },
    )
    .unwrap()
}

fn class_symbol(
    context: &CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    expected: &str,
) -> SemanticSymbolId {
    let declaration = parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            let NodeData::ClassDeclaration(class) = &record.data else {
                return None;
            };
            let NodeData::Identifier(name) = &parsed.arena.get(class.name?)?.data else {
                return None;
            };
            (name.text == expected).then_some(NodeRef::new(parsed.arena.id(), FILE, node))
        })
        .unwrap();
    context.file(FILE).unwrap().1.symbol(declaration).unwrap()
}

fn node_type(context: &CanonicalCheckerContext<'_>, node: NodeRef) -> TypeId {
    context
        .store()
        .type_node_links(node)
        .unwrap()
        .resolved_type
        .unwrap()
}

fn class_instance(context: &CanonicalCheckerContext<'_>, symbol: SemanticSymbolId) -> TypeId {
    context
        .store()
        .declared_type_links(symbol)
        .unwrap()
        .declared_type
        .unwrap()
}

fn this_type(context: &CanonicalCheckerContext<'_>, instance: TypeId) -> TypeId {
    let TypeData::Interface(class) = context.store().type_payload(instance).unwrap().data() else {
        panic!("a class has an interface payload")
    };
    class.this_type.unwrap()
}

fn member(
    context: &CanonicalCheckerContext<'_>,
    class: SemanticSymbolId,
    name: &str,
) -> SemanticSymbolId {
    context
        .store()
        .symbol(class)
        .unwrap()
        .members()
        .and_then(|table| context.store().symbol_table(table))
        .and_then(|table| table.get_source(name))
        .unwrap()
}

#[test]
fn class_polymorphic_super_uses_base_members_and_derived_this_cold_and_warm() {
    let parsed = parse_source_file(concat!(
        "class Base { self(first: number, second: string) { return this; } ",
        "static label() { return 'base'; } } ",
        "class Derived extends Base { ",
        "constructor() { super(); } ",
        "self(first: number, second: string) { return this; } ",
        "read() { return super.self(1, 'read'); } ",
        "pending() { return this.later(); } ",
        "later() { return super.self(2, 'later'); } ",
        "static label() { return super.label(); } }",
    ));
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let mut context = context(&parsed);
    context.check_source_file(FILE).unwrap();
    assert!(
        context.diagnostics().is_empty(),
        "{:?}",
        context.diagnostics()
    );

    let base = class_symbol(&context, &parsed, "Base");
    let derived = class_symbol(&context, &parsed, "Derived");
    let base_instance = class_instance(&context, base);
    let base_this = this_type(&context, base_instance);
    let derived_this = this_type(&context, class_instance(&context, derived));
    let base_self = member(&context, base, "self");
    let derived_self = member(&context, derived, "self");
    assert_ne!(base_self, derived_self);
    let base_self_type = context
        .store()
        .value_symbol_links(base_self)
        .unwrap()
        .resolved_type
        .unwrap();
    let base_self_declaration = context
        .store()
        .symbol(base_self)
        .unwrap()
        .value_declaration()
        .unwrap();
    let original_signature = context
        .store()
        .signature_links(base_self_declaration)
        .unwrap()
        .resolved_signature
        .signature()
        .unwrap();
    let accesses = parsed
        .arena
        .iter()
        .filter_map(|(node, record)| {
            let NodeData::PropertyAccessExpression(access) = &record.data else {
                return None;
            };
            if parsed.arena.get(access.expression)?.kind != SyntaxKind::SuperKeyword {
                return None;
            }
            let NodeData::Identifier(name) = &parsed.arena.get(access.name)?.data else {
                return None;
            };
            Some((
                NodeRef::new(parsed.arena.id(), FILE, node),
                NodeRef::new(parsed.arena.id(), FILE, access.expression),
                name.text.clone(),
            ))
        })
        .collect::<Vec<_>>();
    assert_eq!(accesses.len(), 3);
    let mut instance_view = None;
    for (access, receiver, name) in &accesses {
        if name == "label" {
            assert_eq!(
                node_type(&context, *receiver),
                context
                    .store()
                    .value_symbol_links(base)
                    .unwrap()
                    .resolved_type
                    .unwrap()
            );
            continue;
        }
        let view = node_type(&context, *receiver);
        assert_ne!(view, base_instance);
        assert_eq!(context.type_to_string(view).unwrap(), "Base");
        if let Some(previous) = instance_view.replace(view) {
            assert_eq!(view, previous);
        }
        let TypeData::TypeReference(reference) = context.store().type_payload(view).unwrap().data()
        else {
            panic!("instance super retains a real type reference")
        };
        assert_eq!(reference.object.target, Some(base_instance));
        assert_eq!(
            reference.resolved_type_arguments.as_deref(),
            Some(&[derived_this][..])
        );
        assert!(reference.object.mapper.is_none());
        assert!(reference.object.structured.members.is_none());
        assert_eq!(
            context
                .store()
                .symbol_node_links(*access)
                .unwrap()
                .resolved_symbol,
            Some(base_self)
        );

        let mapped = node_type(&context, *access);
        assert_ne!(mapped, base_self_type);
        assert_eq!(
            context.type_to_string(mapped).unwrap(),
            "(first: number, second: string) => this"
        );
        let TypeData::Object(value) = context.store().type_payload(mapped).unwrap().data() else {
            panic!("the selected method has an instantiated callable value")
        };
        assert_eq!(value.target, Some(base_self_type));
        let mapper = value.mapper.unwrap();
        assert_eq!(
            context.store().map_type(mapper, base_this),
            Some(derived_this)
        );
        let [signature] = value.structured.signatures.as_deref().unwrap() else {
            panic!("the selected method retains one signature")
        };
        let signature = context.store().signature(*signature).unwrap();
        assert_eq!(signature.target(), Some(original_signature));
        assert_eq!(signature.mapper(), Some(mapper));
        assert_eq!(signature.declaration(), Some(base_self_declaration));
        assert_eq!(signature.resolved_return_type(), Some(derived_this));
        let original = context.store().signature(original_signature).unwrap();
        assert_eq!(signature.parameters().len(), 2);
        for (source, actual) in original.parameters().iter().zip(signature.parameters()) {
            let source_record = context.store().symbol(*source).unwrap();
            let actual_record = context.store().symbol(*actual).unwrap();
            assert_eq!(actual_record.name(), source_record.name());
            assert_eq!(actual_record.declarations(), source_record.declarations());
            let source_links = context.store().value_symbol_links(*source).unwrap();
            let actual_links = context.store().value_symbol_links(*actual).unwrap();
            assert_eq!(actual_links.resolved_type, source_links.resolved_type);
            if actual != source {
                assert_eq!(actual_links.target, Some(*source));
                assert_eq!(actual_links.mapper, Some(mapper));
            }
        }
    }
    assert_eq!(
        context
            .store()
            .signature(original_signature)
            .unwrap()
            .resolved_return_type(),
        Some(base_this)
    );
    let (super_call, super_callee) = parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            let NodeData::CallExpression(call) = &record.data else {
                return None;
            };
            (parsed.arena.get(call.expression)?.kind == SyntaxKind::SuperKeyword).then_some((
                NodeRef::new(parsed.arena.id(), FILE, node),
                NodeRef::new(parsed.arena.id(), FILE, call.expression),
            ))
        })
        .unwrap();
    let base_value = context
        .store()
        .value_symbol_links(base)
        .unwrap()
        .resolved_type
        .unwrap();
    assert_eq!(node_type(&context, super_callee), base_value);
    let constructor = context
        .store()
        .signature_links(super_call)
        .unwrap()
        .resolved_signature
        .signature()
        .unwrap();
    assert_eq!(
        context
            .store()
            .signature(constructor)
            .unwrap()
            .resolved_return_type(),
        Some(base_instance)
    );
    assert_eq!(
        node_type(&context, super_call),
        context.store().intrinsic_bootstrap().unwrap().void_type
    );
    for name in ["read", "pending", "later", "self"] {
        let symbol = member(&context, derived, name);
        let declaration = context
            .store()
            .symbol(symbol)
            .unwrap()
            .value_declaration()
            .unwrap();
        let signature = context
            .store()
            .signature_links(declaration)
            .unwrap()
            .resolved_signature
            .signature()
            .unwrap();
        assert_eq!(
            context
                .store()
                .signature(signature)
                .unwrap()
                .resolved_return_type(),
            Some(derived_this)
        );
    }
    let counts = |context: &CanonicalCheckerContext<'_>| {
        (
            context.store().type_len(),
            context.store().symbol_len(),
            context.store().signature_len(),
            context.store().mapper_len(),
        )
    };
    let before = counts(&context);
    let identities = accesses
        .iter()
        .map(|(access, receiver, _)| (node_type(&context, *access), node_type(&context, *receiver)))
        .collect::<Vec<_>>();
    context.recheck_source_file(FILE).unwrap();
    assert_eq!(counts(&context), before);
    assert!(
        context.diagnostics().is_empty(),
        "{:?}",
        context.diagnostics()
    );
    for ((access, receiver, _), expected) in accesses.iter().zip(identities) {
        assert_eq!(
            (node_type(&context, *access), node_type(&context, *receiver)),
            expected
        );
    }
}

#[test]
fn class_polymorphic_super_preserves_this_free_object_and_named_returns() {
    let parsed = parse_source_file(concat!(
        "class Named {} ",
        "interface Shape { value: number; } ",
        "const named = new Named(); ",
        "const shape: Shape = { value: 1 }; ",
        "class Base { ",
        "objectMethod() { return { value: { text: 'base' } }; } ",
        "namedMethod() { return named; } ",
        "shapeMethod() { return shape; } } ",
        "class Derived extends Base { ",
        "readObject() { return super.objectMethod(); } ",
        "readNamed() { return super.namedMethod(); } ",
        "readShape() { return super.shapeMethod(); } }",
    ));
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let mut context = context(&parsed);
    context.check_source_file(FILE).unwrap();
    assert!(
        context.diagnostics().is_empty(),
        "{:?}",
        context.diagnostics()
    );
    let base = class_symbol(&context, &parsed, "Base");
    let derived = class_symbol(&context, &parsed, "Derived");
    let signature = |context: &CanonicalCheckerContext<'_>, class, name| {
        let member = member(context, class, name);
        let declaration = context
            .store()
            .symbol(member)
            .unwrap()
            .value_declaration()
            .unwrap();
        context
            .store()
            .signature_links(declaration)
            .unwrap()
            .resolved_signature
            .signature()
            .unwrap()
    };
    for (base_name, derived_name) in [
        ("objectMethod", "readObject"),
        ("namedMethod", "readNamed"),
        ("shapeMethod", "readShape"),
    ] {
        let original = signature(&context, base, base_name);
        let returned = signature(&context, derived, derived_name);
        assert_eq!(
            context
                .store()
                .signature(returned)
                .unwrap()
                .resolved_return_type(),
            context
                .store()
                .signature(original)
                .unwrap()
                .resolved_return_type(),
            "{base_name}",
        );
        let access = parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                let NodeData::PropertyAccessExpression(access) = &record.data else {
                    return None;
                };
                let NodeData::Identifier(name) = &parsed.arena.get(access.name)?.data else {
                    return None;
                };
                (parsed.arena.get(access.expression)?.kind == SyntaxKind::SuperKeyword
                    && name.text == base_name)
                    .then_some(NodeRef::new(parsed.arena.id(), FILE, node))
            })
            .unwrap();
        assert_eq!(
            node_type(&context, access),
            context
                .store()
                .value_symbol_links(member(&context, base, base_name))
                .unwrap()
                .resolved_type
                .unwrap(),
            "{base_name} keeps its unchanged method and signature identities",
        );
    }
    let before = (
        context.store().type_len(),
        context.store().symbol_len(),
        context.store().signature_len(),
        context.store().mapper_len(),
    );
    context.recheck_source_file(FILE).unwrap();
    assert!(
        context.diagnostics().is_empty(),
        "{:?}",
        context.diagnostics()
    );
    assert_eq!(
        (
            context.store().type_len(),
            context.store().symbol_len(),
            context.store().signature_len(),
            context.store().mapper_len(),
        ),
        before,
    );
}

#[test]
fn class_polymorphic_super_maps_an_inherited_method_for_each_derived_class() {
    let parsed = parse_source_file(concat!(
        "class Base { self() { return this; } } ",
        "class Middle extends Base {} ",
        "class First extends Middle { self() { return this; } read() { return super.self(); } } ",
        "class Second extends Middle { read() { return super.self(); } }",
    ));
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let mut context = context(&parsed);
    context.check_source_file(FILE).unwrap();
    assert!(
        context.diagnostics().is_empty(),
        "{:?}",
        context.diagnostics()
    );
    let base = class_symbol(&context, &parsed, "Base");
    let middle = class_symbol(&context, &parsed, "Middle");
    let original = member(&context, base, "self");
    let base_this = this_type(&context, class_instance(&context, base));
    let middle_instance = class_instance(&context, middle);
    let mut views = Vec::new();
    let mut mapped_methods = Vec::new();
    for name in ["First", "Second"] {
        let class = class_symbol(&context, &parsed, name);
        let derived_this = this_type(&context, class_instance(&context, class));
        let declaration = context
            .store()
            .symbol(member(&context, class, "read"))
            .unwrap()
            .value_declaration()
            .unwrap();
        let read_range = parsed.arena.get(declaration.node).unwrap().range;
        let access = parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                let NodeData::PropertyAccessExpression(access) = &record.data else {
                    return None;
                };
                (record.range.start >= read_range.start
                    && record.range.end <= read_range.end
                    && parsed.arena.get(access.expression)?.kind == SyntaxKind::SuperKeyword)
                    .then_some((
                        NodeRef::new(parsed.arena.id(), FILE, node),
                        NodeRef::new(parsed.arena.id(), FILE, access.expression),
                    ))
            })
            .unwrap();
        let view = node_type(&context, access.1);
        let mapped = node_type(&context, access.0);
        let TypeData::TypeReference(reference) = context.store().type_payload(view).unwrap().data()
        else {
            panic!("instance super has a type reference")
        };
        assert_eq!(reference.object.target, Some(middle_instance));
        assert_eq!(
            reference.resolved_type_arguments.as_deref(),
            Some(&[derived_this][..])
        );
        assert_eq!(
            context
                .store()
                .symbol_node_links(access.0)
                .unwrap()
                .resolved_symbol,
            Some(original)
        );
        let TypeData::Object(method) = context.store().type_payload(mapped).unwrap().data() else {
            panic!("an inherited method has a mapped callable")
        };
        assert_eq!(
            context.store().map_type(method.mapper.unwrap(), base_this),
            Some(derived_this)
        );
        let signature = method.structured.signatures.as_ref().unwrap()[0];
        assert_eq!(
            context
                .store()
                .signature(signature)
                .unwrap()
                .resolved_return_type(),
            Some(derived_this)
        );
        views.push(view);
        mapped_methods.push(mapped);
    }
    assert_ne!(views[0], views[1]);
    assert_ne!(mapped_methods[0], mapped_methods[1]);
    let before = (
        context.store().type_len(),
        context.store().mapper_len(),
        context.store().signature_len(),
    );
    context.recheck_source_file(FILE).unwrap();
    assert_eq!(
        (
            context.store().type_len(),
            context.store().mapper_len(),
            context.store().signature_len()
        ),
        before
    );
}
