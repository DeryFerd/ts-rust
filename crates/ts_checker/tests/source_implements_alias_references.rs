use ts_ast::{FileId, NodeData, NodeId, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    CheckFlags, EscapedName, SemanticSymbolId, SymbolFlags,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerDiagnostic, CanonicalCheckerOptions,
    IntrinsicBootstrapOptions, SignatureId, TypeData, TypeId, type_records::StructuredTypeData,
    types::TypeFlags,
};
use ts_parser::{ParseResult, parse_source_file};

const FILE: FileId = FileId::new(495_620);

fn context(parsed: &ParseResult) -> CanonicalCheckerContext<'_> {
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            FILE,
            CanonicalSourceFileFacts::new(
                EscapedName::source("\"/project/implements-alias-references.ts\""),
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
                exact_optional_property_types: false,
            },
            strict_function_types: true,
            no_implicit_any: true,
            ..CanonicalCheckerOptions::default()
        },
    )
    .unwrap()
}

fn node(parsed: &ParseResult, id: NodeId) -> NodeRef {
    NodeRef::new(parsed.arena.id(), FILE, id)
}

fn name_node(parsed: &ParseResult, declaration: NodeRef) -> NodeRef {
    let name = match &parsed.arena.get(declaration.node).unwrap().data {
        NodeData::ClassDeclaration(data) => data.name.unwrap(),
        NodeData::TypeAliasDeclaration(data) => data.name,
        NodeData::PropertyDeclaration(data) => data.name,
        NodeData::PropertySignatureDeclaration(data) => data.name,
        NodeData::MethodDeclaration(data) => data.name,
        _ => panic!("expected a named declaration"),
    };
    node(parsed, name)
}

fn declaration(parsed: &ParseResult, expected: &str) -> NodeRef {
    parsed
        .arena
        .iter()
        .filter(|(_, record)| {
            matches!(
                record.kind,
                SyntaxKind::ClassDeclaration | SyntaxKind::TypeAliasDeclaration
            )
        })
        .map(|(id, _)| node(parsed, id))
        .find(|&declaration| {
            matches!(&parsed.arena.get(name_node(parsed, declaration).node).unwrap().data,
                NodeData::Identifier(name) if name.text == expected)
        })
        .unwrap_or_else(|| panic!("missing declaration {expected}"))
}

fn member(parsed: &ParseResult, owner: NodeRef, expected: &str) -> NodeRef {
    let parent = match &parsed.arena.get(owner.node).unwrap().data {
        NodeData::ClassDeclaration(_) => owner.node,
        NodeData::TypeAliasDeclaration(data) => data.type_,
        _ => panic!("expected a class or object alias"),
    };
    parsed
        .arena
        .iter()
        .filter(|(_, record)| {
            record.parent == Some(parent)
                && matches!(
                    record.kind,
                    SyntaxKind::PropertyDeclaration
                        | SyntaxKind::PropertySignature
                        | SyntaxKind::MethodDeclaration
                )
        })
        .map(|(id, _)| node(parsed, id))
        .find(|&member| {
            matches!(&parsed.arena.get(name_node(parsed, member).node).unwrap().data,
                NodeData::Identifier(name) if name.text == expected)
        })
        .unwrap_or_else(|| panic!("missing member {expected}"))
}

fn symbol(context: &CanonicalCheckerContext<'_>, declaration: NodeRef) -> SemanticSymbolId {
    let raw = context.file(FILE).unwrap().1.symbol(declaration).unwrap();
    context.store().get_merged_symbol(raw).unwrap()
}

fn heritage(parsed: &ParseResult, class: NodeRef) -> NodeRef {
    let NodeData::ClassDeclaration(data) = &parsed.arena.get(class.node).unwrap().data else {
        panic!("expected the implementing class")
    };
    let [clause] = data.heritage_clauses.as_ref().unwrap().nodes.as_slice() else {
        panic!("expected one implements clause")
    };
    let NodeData::HeritageClause(data) = &parsed.arena.get(*clause).unwrap().data else {
        unreachable!()
    };
    assert_eq!(data.token, SyntaxKind::ImplementsKeyword);
    let [reference] = data.types.nodes.as_slice() else {
        panic!("expected one written implementation")
    };
    let record = parsed.arena.get(*reference).unwrap();
    assert_eq!(record.parent, Some(*clause));
    assert_eq!(record.kind, SyntaxKind::ExpressionWithTypeArguments);
    node(parsed, *reference)
}

fn formal(
    context: &mut CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    alias: NodeRef,
) -> TypeId {
    let NodeData::TypeAliasDeclaration(data) = &parsed.arena.get(alias.node).unwrap().data else {
        panic!("expected the generic source alias")
    };
    let [parameter] = data.type_parameters.as_ref().unwrap().nodes.as_slice() else {
        panic!("expected one source formal")
    };
    let parameter = node(parsed, *parameter);
    let owner = symbol(context, alias);
    let parameter_symbol = symbol(context, parameter);
    assert_eq!(
        parsed.arena.get(parameter.node).unwrap().parent,
        Some(alias.node)
    );
    assert_eq!(
        context.store().symbol(parameter_symbol).unwrap().parent(),
        Some(owner)
    );
    let type_ = context
        .get_declared_type_of_symbol(parameter_symbol)
        .unwrap();
    let record = context.store().type_payload(type_).unwrap();
    assert_eq!(record.flags(), TypeFlags::TYPE_PARAMETER);
    assert_eq!(record.symbol(), Some(parameter_symbol));
    let TypeData::TypeParameter(data) = record.data() else {
        unreachable!()
    };
    assert_eq!(data.target, None);
    assert_eq!(data.mapper, None);
    assert_eq!(
        context
            .store()
            .type_alias_links(owner)
            .unwrap()
            .type_parameters
            .as_deref(),
        Some([type_].as_slice())
    );
    type_
}

fn structured<'a>(
    context: &'a CanonicalCheckerContext<'_>,
    type_: TypeId,
) -> &'a StructuredTypeData {
    match context.store().type_payload(type_).unwrap().data() {
        TypeData::Interface(data) => &data.reference.object.structured,
        TypeData::TypeReference(data) => &data.object.structured,
        TypeData::Object(data) => &data.structured,
        TypeData::Intersection(data) => &data.intersection.structured,
        _ => panic!("expected a resolved object or intersection"),
    }
}

fn property(context: &CanonicalCheckerContext<'_>, type_: TypeId, name: &str) -> SemanticSymbolId {
    let members = match context.store().type_payload(type_).unwrap().data() {
        TypeData::Intersection(data) => data.intersection.property_cache,
        _ => structured(context, type_).members,
    };
    context
        .store()
        .symbol_table(members.unwrap())
        .unwrap()
        .get_source(name)
        .unwrap_or_else(|| panic!("missing property {name}"))
}

fn property_type(context: &CanonicalCheckerContext<'_>, property: SemanticSymbolId) -> TypeId {
    context
        .store()
        .value_symbol_links(property)
        .and_then(|links| links.resolved_type)
        .unwrap()
}

fn assert_alias_argument(
    context: &CanonicalCheckerContext<'_>,
    type_: TypeId,
    alias: SemanticSymbolId,
    argument: TypeId,
) {
    let record = context.store().type_payload(type_).unwrap();
    let identity = context.store().type_alias(record.alias().unwrap()).unwrap();
    assert_eq!(identity.symbol(), Some(alias));
    assert_eq!(identity.type_arguments(), Some([argument].as_slice()));
}

fn signature(context: &CanonicalCheckerContext<'_>, declaration: NodeRef) -> SignatureId {
    context
        .store()
        .signature_links(declaration)
        .and_then(|links| links.resolved_signature.signature())
        .unwrap()
}

fn snapshot(
    context: &CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    properties: &[SemanticSymbolId],
) -> impl std::fmt::Debug + PartialEq + use<> {
    let store = context.store();
    let nodes = parsed
        .arena
        .iter()
        .map(|(id, _)| node(parsed, id))
        .collect::<Vec<_>>();
    let owners = nodes
        .iter()
        .filter_map(|node| context.file(FILE).unwrap().1.symbol(*node))
        .chain(properties.iter().copied())
        .collect::<Vec<_>>();
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
        nodes
            .iter()
            .map(|&node| {
                (
                    node,
                    store.type_node_links(node).cloned(),
                    store.symbol_node_links(node).cloned(),
                    store.signature_links(node).cloned(),
                )
            })
            .collect::<Vec<_>>(),
        owners
            .into_iter()
            .map(|owner| {
                (
                    owner,
                    store.declared_type_links(owner).cloned(),
                    store.type_alias_links(owner).cloned(),
                    store.value_symbol_links(owner).cloned(),
                )
            })
            .collect::<Vec<_>>(),
        store.relation_state_snapshot(),
        context.diagnostics().clone(),
    )
}

fn assert_replay(
    context: &mut CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    properties: &[SemanticSymbolId],
) {
    let cold = snapshot(context, parsed, properties);
    context.check_source_file(FILE).unwrap();
    assert_eq!(snapshot(context, parsed, properties), cold);
    for _ in 0..2 {
        context.recheck_source_file(FILE).unwrap();
        assert_eq!(snapshot(context, parsed, properties), cold);
        assert!(
            context
                .store()
                .source_file_links(context.source_file(FILE).unwrap())
                .unwrap()
                .type_checked
        );
    }
}

fn assert_diagnostic(
    diagnostic: &CanonicalCheckerDiagnostic,
    node: NodeRef,
    code: u32,
    arguments: &[&str],
    text: &str,
) {
    assert_eq!(diagnostic.node, Some(node));
    assert_eq!(diagnostic.range_override, None);
    assert_eq!(diagnostic.diagnostic.code(), code);
    assert_eq!(diagnostic.diagnostic.arguments, arguments);
    assert_eq!(diagnostic.diagnostic.render().unwrap(), text);
}

fn assert_missing_note(diagnostic: &CanonicalCheckerDiagnostic, declaration_name: NodeRef) {
    let [note] = diagnostic.related_information.as_slice() else {
        panic!("expected the missing property's source declaration")
    };
    assert_eq!(note.node, Some(declaration_name));
    assert_eq!(note.diagnostic.code(), 2728);
    assert_eq!(note.diagnostic.arguments, ["label"]);
    assert_eq!(
        note.diagnostic.render().unwrap(),
        "'label' is declared here."
    );
}

#[test]
fn implements_aliases_keep_defaults_substitutions_callables_and_replay() {
    let parsed = parse_source_file(concat!(
        "type Cell<T = string> = { value: T };\n",
        "type Tagged<T> = Cell<T> & { tag: number };\n",
        "type Reader = { read: () => number };\n",
        "class DefaultCell implements Cell { value: string = \"x\"; }\n",
        "class NumberCell implements Cell<number> { value: number = 1; }\n",
        "class TaggedNumber implements Tagged<number> { value: number = 2; tag: number = 3; }\n",
        "class ReaderImpl implements Reader { read(): number { return 1; } }\n",
    ));
    let mut context = context(&parsed);
    context.check_source_file(FILE).unwrap();
    assert!(
        context.diagnostics().is_empty(),
        "{:?}",
        context.diagnostics()
    );
    let cell = declaration(&parsed, "Cell");
    let tagged = declaration(&parsed, "Tagged");
    let reader = declaration(&parsed, "Reader");
    let cell_owner = symbol(&context, cell);
    let tagged_owner = symbol(&context, tagged);
    let reader_owner = symbol(&context, reader);
    for owner in [cell_owner, tagged_owner, reader_owner] {
        assert!(
            context
                .store()
                .symbol(owner)
                .unwrap()
                .flags()
                .contains(SymbolFlags::TYPE_ALIAS)
        );
    }
    let cell_formal = formal(&mut context, &parsed, cell);
    let tagged_formal = formal(&mut context, &parsed, tagged);
    assert_ne!(cell_formal, tagged_formal);
    let string = context.store().intrinsic_bootstrap().unwrap().string_type;
    let number = context.store().intrinsic_bootstrap().unwrap().number_type;
    let mut implementations = Vec::new();
    let mut properties = Vec::new();
    for (name, alias, own_names) in [
        ("DefaultCell", cell_owner, ["value"].as_slice()),
        ("NumberCell", cell_owner, ["value"].as_slice()),
        ("TaggedNumber", tagged_owner, ["value", "tag"].as_slice()),
        ("ReaderImpl", reader_owner, ["read"].as_slice()),
    ] {
        let class = declaration(&parsed, name);
        let reference = heritage(&parsed, class);
        let implemented = context.get_type_from_type_node(reference).unwrap();
        assert_eq!(
            context
                .store()
                .symbol_node_links(reference)
                .unwrap()
                .resolved_symbol,
            Some(alias)
        );
        let owner = symbol(&context, class);
        let members = context.get_nongeneric_class_members(owner).unwrap();
        let own = own_names
            .iter()
            .map(|name| symbol(&context, member(&parsed, class, name)))
            .collect::<Vec<_>>();
        assert_eq!(members.base(), None);
        assert_eq!(members.instance_properties(), own);
        assert_eq!(
            members.instance_properties(),
            members.declared_instance_properties()
        );
        let TypeData::Interface(instance) = context
            .store()
            .type_payload(members.shells().instance_type())
            .unwrap()
            .data()
        else {
            panic!("expected the real class instance")
        };
        assert_eq!(instance.resolved_base_types, None);
        assert_eq!(
            instance.resolved_base_constructor_type,
            Some(
                context
                    .store()
                    .intrinsic_bootstrap()
                    .unwrap()
                    .undefined_type
            )
        );
        assert_eq!(
            context.is_type_assignable_to(members.shells().instance_type(), implemented),
            Ok(true)
        );
        for name in own_names {
            let target = property(&context, implemented, name);
            assert!(!own.contains(&target));
            properties.push(target);
        }
        implementations.push((reference, implemented, owner, members));
    }
    let default = implementations[0].1;
    let explicit = implementations[1].1;
    assert_ne!(default, explicit);
    assert_alias_argument(&context, default, cell_owner, string);
    assert_alias_argument(&context, explicit, cell_owner, number);
    let original = symbol(&context, member(&parsed, cell, "value"));
    for (implemented, expected) in [(default, string), (explicit, number)] {
        let copied = property(&context, implemented, "value");
        let links = context.store().value_symbol_links(copied).unwrap();
        assert_eq!(links.target, Some(original));
        assert_eq!(
            context.store().map_type(links.mapper.unwrap(), cell_formal),
            Some(expected)
        );
        assert_eq!(links.resolved_type, Some(expected));
        let record = context.store().symbol(copied).unwrap();
        assert!(record.check_flags().contains(CheckFlags::INSTANTIATED));
        assert_eq!(
            record.declarations(),
            context.store().symbol(original).unwrap().declarations()
        );
    }
    let tagged_type = implementations[2].1;
    assert!(matches!(
        context.store().type_payload(tagged_type).unwrap().data(),
        TypeData::Intersection(_)
    ));
    assert_alias_argument(&context, tagged_type, tagged_owner, number);
    for name in ["value", "tag"] {
        assert_eq!(
            property_type(&context, property(&context, tagged_type, name)),
            number
        );
    }
    let read = member(&parsed, reader, "read");
    let NodeData::PropertySignatureDeclaration(read_data) =
        &parsed.arena.get(read.node).unwrap().data
    else {
        unreachable!()
    };
    let function = node(&parsed, read_data.type_);
    assert_eq!(
        parsed.arena.get(function.node).unwrap().kind,
        SyntaxKind::FunctionType
    );
    let callable = context.get_type_from_type_node(function).unwrap();
    assert_eq!(
        property_type(&context, property(&context, implementations[3].1, "read")),
        callable
    );
    let method = member(&parsed, declaration(&parsed, "ReaderImpl"), "read");
    assert!(
        context
            .store()
            .symbol(symbol(&context, read))
            .unwrap()
            .flags()
            .contains(SymbolFlags::PROPERTY)
    );
    assert!(
        context
            .store()
            .symbol(symbol(&context, method))
            .unwrap()
            .flags()
            .contains(SymbolFlags::METHOD)
    );
    let callback_signature = signature(&context, function);
    let method_signature = signature(&context, method);
    assert_ne!(callback_signature, method_signature);
    for (signature, declaration) in [(callback_signature, function), (method_signature, method)] {
        assert_eq!(
            context.store().signature(signature).unwrap().declaration(),
            Some(declaration)
        );
        assert_eq!(context.get_return_type_of_signature(signature), Ok(number));
    }
    assert_replay(&mut context, &parsed, &properties);
    for (reference, implemented, owner, members) in implementations {
        assert_eq!(context.get_type_from_type_node(reference), Ok(implemented));
        assert_eq!(
            context.get_nongeneric_class_members(owner).unwrap(),
            members
        );
    }
    assert_eq!(
        context.get_return_type_of_signature(callback_signature),
        Ok(number)
    );
    assert_eq!(
        context.get_return_type_of_signature(method_signature),
        Ok(number)
    );
}

#[test]
fn implements_union_alias_reports_2422_at_the_reference_and_replays() {
    let parsed = parse_source_file(concat!(
        "type Choice = { value: number } | { label: string };\n",
        "class Invalid implements Choice { value: number = 1; label: string = \"x\"; }\n",
    ));
    let mut context = context(&parsed);
    context.check_source_file(FILE).unwrap();
    let reference = heritage(&parsed, declaration(&parsed, "Invalid"));
    let [diagnostic] = context.diagnostics().as_slice() else {
        panic!(
            "expected one invalid implements base diagnostic: {:?}",
            context.diagnostics()
        )
    };
    assert_diagnostic(
        diagnostic,
        reference,
        2422,
        &[],
        "A class can only implement an object type or intersection of object types with statically known members.",
    );
    assert!(diagnostic.related_information.is_empty());
    let implemented = context.get_type_from_type_node(reference).unwrap();
    assert!(matches!(
        context.store().type_payload(implemented).unwrap().data(),
        TypeData::Union(_)
    ));
    assert_replay(&mut context, &parsed, &[]);
    assert_eq!(context.get_type_from_type_node(reference), Ok(implemented));
}

#[test]
fn implements_aliases_report_missing_object_and_class_members_and_replay() {
    let parsed = parse_source_file(concat!(
        "type Required = { value: number; label: string };\n",
        "class Missing implements Required { value: number = 1; }\n",
        "class RequiredClass { value: number = 1; label: string = \"x\"; }\n",
        "type ClassAlias = RequiredClass;\n",
        "class MissingClass implements ClassAlias { value: number = 1; }\n",
    ));
    let mut context = context(&parsed);
    context.check_source_file(FILE).unwrap();
    let missing = declaration(&parsed, "Missing");
    let missing_class = declaration(&parsed, "MissingClass");
    let required = declaration(&parsed, "Required");
    let required_class = declaration(&parsed, "RequiredClass");
    let [object_error, class_error] = context.diagnostics().as_slice() else {
        panic!(
            "expected object and class implementation diagnostics: {:?}",
            context.diagnostics()
        )
    };
    assert_diagnostic(
        object_error,
        name_node(&parsed, missing),
        2420,
        &["Missing", "Required"],
        concat!(
            "Class 'Missing' incorrectly implements interface 'Required'.\n",
            "  Property 'label' is missing in type 'Missing' but required in type 'Required'.",
        ),
    );
    assert_missing_note(
        object_error,
        name_node(&parsed, member(&parsed, required, "label")),
    );
    assert_diagnostic(
        class_error,
        name_node(&parsed, missing_class),
        2720,
        &["MissingClass", "RequiredClass"],
        concat!(
            "Class 'MissingClass' incorrectly implements class 'RequiredClass'. Did you mean to extend 'RequiredClass' and inherit its members as a subclass?\n",
            "  Property 'label' is missing in type 'MissingClass' but required in type 'RequiredClass'.",
        ),
    );
    assert_missing_note(
        class_error,
        name_node(&parsed, member(&parsed, required_class, "label")),
    );
    let class_alias = symbol(&context, declaration(&parsed, "ClassAlias"));
    let target_owner = symbol(&context, required_class);
    let target_type = context.get_declared_type_of_symbol(target_owner).unwrap();
    let class_reference = heritage(&parsed, missing_class);
    assert_eq!(
        context.get_type_from_type_node(class_reference),
        Ok(target_type)
    );
    assert_eq!(
        context
            .store()
            .symbol_node_links(class_reference)
            .unwrap()
            .resolved_symbol,
        Some(class_alias)
    );
    assert_eq!(
        context.store().type_payload(target_type).unwrap().symbol(),
        Some(target_owner)
    );
    assert_ne!(class_alias, target_owner);
    for class in [missing, missing_class] {
        let owner = symbol(&context, class);
        let implemented = context
            .get_type_from_type_node(heritage(&parsed, class))
            .unwrap();
        let members = context.get_nongeneric_class_members(owner).unwrap();
        assert_eq!(members.base(), None);
        assert_eq!(
            members.instance_properties(),
            [symbol(&context, member(&parsed, class, "value"))]
        );
        assert_eq!(
            members.instance_properties(),
            members.declared_instance_properties()
        );
        assert_eq!(
            context.is_type_assignable_to(members.shells().instance_type(), implemented),
            Ok(false)
        );
    }
    assert_replay(&mut context, &parsed, &[]);
    assert_eq!(
        context.get_type_from_type_node(class_reference),
        Ok(target_type)
    );
}
