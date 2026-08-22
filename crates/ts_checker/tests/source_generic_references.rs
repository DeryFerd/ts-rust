use ts_ast::{FileId, NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, TypeData, TypeId,
    type_records::TypeCacheState, types::ObjectFlags,
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
                EscapedName::source("\"/project/generic-references.ts\""),
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

fn declaration_name(parsed: &ParseResult, node: NodeRef) -> Option<&str> {
    let name = match &parsed.arena.get(node.node)?.data {
        NodeData::ClassDeclaration(declaration) => declaration.name?,
        NodeData::InterfaceDeclaration(declaration) => declaration.name,
        NodeData::TypeAliasDeclaration(declaration) => declaration.name,
        _ => return None,
    };
    let NodeData::Identifier(name) = &parsed.arena.get(name)?.data else {
        return None;
    };
    Some(&name.text)
}

fn named_symbol(
    parsed: &ParseResult,
    file: FileId,
    context: &CanonicalCheckerContext<'_>,
    kind: SyntaxKind,
    expected: &str,
) -> SemanticSymbolId {
    let declaration = parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            let node = NodeRef::new(parsed.arena.id(), file, node);
            (record.kind == kind && declaration_name(parsed, node) == Some(expected))
                .then_some(node)
        })
        .unwrap_or_else(|| panic!("missing {kind:?} {expected}"));
    let raw = context.file(file).unwrap().1.symbol(declaration).unwrap();
    context.store().get_merged_symbol(raw).unwrap()
}

fn alias_parts(
    parsed: &ParseResult,
    file: FileId,
    context: &CanonicalCheckerContext<'_>,
    expected: &str,
) -> (SemanticSymbolId, NodeRef) {
    let (declaration, rhs) = parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            let NodeData::TypeAliasDeclaration(alias) = &record.data else {
                return None;
            };
            let declaration = NodeRef::new(parsed.arena.id(), file, node);
            (declaration_name(parsed, declaration) == Some(expected)).then_some((
                declaration,
                NodeRef::new(parsed.arena.id(), file, alias.type_),
            ))
        })
        .unwrap_or_else(|| panic!("missing type alias {expected}"));
    let raw = context.file(file).unwrap().1.symbol(declaration).unwrap();
    (context.store().get_merged_symbol(raw).unwrap(), rhs)
}

fn assert_direct_reference(
    context: &CanonicalCheckerContext<'_>,
    reference: TypeId,
    target: TypeId,
    arguments: &[TypeId],
) {
    let record = context.store().type_payload(reference).unwrap();
    assert!(
        record
            .object_flags()
            .contains(ObjectFlags::REFERENCE | ObjectFlags::FROM_TYPE_NODE)
    );
    let TypeData::TypeReference(reference) = record.data() else {
        panic!("an instantiated class or interface must be a type-reference shell")
    };
    assert_eq!(reference.object.target, Some(target));
    assert_eq!(reference.object.mapper, None);
    assert_eq!(
        reference.resolved_type_arguments.as_deref(),
        Some(arguments)
    );
}

#[test]
fn local_generic_class_and_interface_references_share_exact_cold_and_warm_identities() {
    let parsed = parse_source_file(concat!(
        "interface Box<T> {}\n",
        "class Pair<Left, Right> {}\n",
        "type TextBox = Box<string>;\n",
        "type TextBoxAgain = Box<string>;\n",
        "type MixedPair = Pair<string, number>;\n",
    ));
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(0);
    let mut context = context(&parsed, file);
    let box_symbol = named_symbol(
        &parsed,
        file,
        &context,
        SyntaxKind::InterfaceDeclaration,
        "Box",
    );
    let pair_symbol = named_symbol(
        &parsed,
        file,
        &context,
        SyntaxKind::ClassDeclaration,
        "Pair",
    );
    let (text_box, text_box_node) = alias_parts(&parsed, file, &context, "TextBox");
    let (text_box_again, text_box_again_node) =
        alias_parts(&parsed, file, &context, "TextBoxAgain");
    let (mixed_pair, mixed_pair_node) = alias_parts(&parsed, file, &context, "MixedPair");
    let (string, number) = {
        let bootstrap = context.store().intrinsic_bootstrap().unwrap();
        (bootstrap.string_type, bootstrap.number_type)
    };

    let text_box_type = context.get_declared_type_of_symbol(text_box).unwrap();
    let text_box_again_type = context.get_declared_type_of_symbol(text_box_again).unwrap();
    let mixed_pair_type = context.get_declared_type_of_symbol(mixed_pair).unwrap();
    assert_eq!(text_box_again_type, text_box_type);
    let box_target = context
        .store()
        .declared_type_links(box_symbol)
        .and_then(|links| links.declared_type)
        .unwrap();
    let pair_target = context
        .store()
        .declared_type_links(pair_symbol)
        .and_then(|links| links.declared_type)
        .unwrap();
    assert_direct_reference(&context, text_box_type, box_target, &[string]);
    assert_direct_reference(&context, mixed_pair_type, pair_target, &[string, number]);

    for (alias, node, resolved, target_symbol) in [
        (text_box, text_box_node, text_box_type, box_symbol),
        (
            text_box_again,
            text_box_again_node,
            text_box_type,
            box_symbol,
        ),
        (mixed_pair, mixed_pair_node, mixed_pair_type, pair_symbol),
    ] {
        assert_eq!(
            context
                .store()
                .type_alias_links(alias)
                .and_then(|links| links.declared_type),
            Some(resolved)
        );
        assert_eq!(
            context
                .store()
                .type_node_links(node)
                .and_then(|links| links.resolved_type),
            Some(resolved)
        );
        assert_eq!(
            context
                .store()
                .symbol_node_links(node)
                .and_then(|links| links.resolved_symbol),
            Some(target_symbol)
        );
    }
    for target in [box_target, pair_target] {
        let TypeData::Interface(target) = context.store().type_payload(target).unwrap().data()
        else {
            panic!("a generic class/interface target retains its interface payload")
        };
        let TypeCacheState::Allocated(instantiations) = &target.reference.object.instantiations
        else {
            panic!("a generic class/interface target owns its identity cache")
        };
        assert_eq!(instantiations.len(), 2);
    }
    assert!(context.diagnostics().is_empty());

    let warm = (
        context.store().type_len(),
        context.store().mapper_len(),
        context.store().type_alias_len(),
        [text_box_node, text_box_again_node, mixed_pair_node]
            .map(|node| context.store().type_node_links(node).cloned()),
        context.diagnostics().clone(),
    );
    assert_eq!(
        context.get_declared_type_of_symbol(text_box),
        Ok(text_box_type)
    );
    assert_eq!(
        context.get_declared_type_of_symbol(text_box_again),
        Ok(text_box_type)
    );
    assert_eq!(
        context.get_declared_type_of_symbol(mixed_pair),
        Ok(mixed_pair_type)
    );
    assert_eq!(
        (
            context.store().type_len(),
            context.store().mapper_len(),
            context.store().type_alias_len(),
            [text_box_node, text_box_again_node, mixed_pair_node]
                .map(|node| context.store().type_node_links(node).cloned()),
            context.diagnostics().clone(),
        ),
        warm
    );
}

#[test]
fn generic_interface_declarations_keep_their_declared_target_until_members_are_needed() {
    let parsed = parse_source_file(concat!(
        "interface Box<T> { value: T; }\n",
        "type TextBox = Box<string>;\n",
    ));
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(2);
    let mut context = context(&parsed, file);
    let symbol = named_symbol(
        &parsed,
        file,
        &context,
        SyntaxKind::InterfaceDeclaration,
        "Box",
    );
    let (alias, reference) = alias_parts(&parsed, file, &context, "TextBox");
    let string = context.store().intrinsic_bootstrap().unwrap().string_type;

    let target = context.get_declared_type_of_symbol(symbol).unwrap();
    let TypeData::Interface(interface) = context.store().type_payload(target).unwrap().data()
    else {
        panic!("a generic interface must retain its declared interface target")
    };
    assert_eq!(
        interface
            .reference
            .resolved_type_arguments
            .as_deref()
            .map(<[_]>::len),
        Some(1)
    );
    assert!(!interface.declared_members_resolved);

    let instantiated = context.get_declared_type_of_symbol(alias).unwrap();
    assert_direct_reference(&context, instantiated, target, &[string]);
    assert_eq!(
        context
            .store()
            .type_node_links(reference)
            .and_then(|links| links.resolved_type),
        Some(instantiated)
    );

    let warm = (
        context.store().type_len(),
        context.store().mapper_len(),
        context.diagnostics().clone(),
    );
    assert_eq!(context.get_declared_type_of_symbol(symbol), Ok(target));
    assert_eq!(context.get_declared_type_of_symbol(alias), Ok(instantiated));
    assert_eq!(
        (
            context.store().type_len(),
            context.store().mapper_len(),
            context.diagnostics().clone(),
        ),
        warm
    );
}

#[test]
fn local_class_interface_reference_arity_diagnostics_are_pinned_and_idempotent() {
    let parsed = parse_source_file(concat!(
        "interface Box<T> {}\n",
        "interface Plain {}\n",
        "type Missing = Box;\n",
        "type Extra = Box<string, number>;\n",
        "type NotGeneric = Plain<string>;\n",
    ));
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(1);
    let mut context = context(&parsed, file);
    let aliases =
        ["Missing", "Extra", "NotGeneric"].map(|name| alias_parts(&parsed, file, &context, name));
    let error_type = context.store().intrinsic_bootstrap().unwrap().error_type;

    for (alias, _) in aliases {
        assert_eq!(context.get_declared_type_of_symbol(alias), Ok(error_type));
    }
    assert_eq!(
        context
            .diagnostics()
            .as_slice()
            .iter()
            .map(|diagnostic| (
                diagnostic.diagnostic.code(),
                diagnostic.diagnostic.arguments.clone(),
                diagnostic.node,
            ))
            .collect::<Vec<_>>(),
        [
            (
                2314,
                vec!["Box<T>".to_owned(), "1".to_owned()],
                Some(aliases[0].1),
            ),
            (
                2314,
                vec!["Box<T>".to_owned(), "1".to_owned()],
                Some(aliases[1].1),
            ),
            (2315, vec!["Plain".to_owned()], Some(aliases[2].1),),
        ]
    );

    let warm = (
        context.store().type_len(),
        context.store().type_alias_len(),
        aliases.map(|(_, node)| context.store().type_node_links(node).cloned()),
        context.diagnostics().clone(),
    );
    for (alias, _) in aliases {
        assert_eq!(context.get_declared_type_of_symbol(alias), Ok(error_type));
    }
    assert_eq!(
        (
            context.store().type_len(),
            context.store().type_alias_len(),
            aliases.map(|(_, node)| context.store().type_node_links(node).cloned()),
            context.diagnostics().clone(),
        ),
        warm
    );
}
