use ts_ast::{FileId, NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId, SymbolFlags,
};
use ts_checker::semantic::{
    AliasTargetState, CanonicalCheckerContext, CanonicalCheckerOptions,
    CanonicalModuleResolutionEntry, CanonicalModuleResolutionManifestInput,
    CanonicalModuleResolutionMode, CanonicalResolvedModuleInput, ClassMembers,
    IntrinsicBootstrapOptions, TypeData, TypeId,
};
use ts_parser::{ParseResult, parse_source_file};

const PROVIDER: FileId = FileId::new(206_201);
const CONSUMER: FileId = FileId::new(206_202);
const BASE: &str = concat!(
    "class Base {\n",
    "  value: string = 'base';\n",
    "  read(): string { return this.value; }\n",
    "}\n",
    "export { Base as PublicBase };\n",
);
const DERIVED: &str = concat!(
    "import { PublicBase as ImportedBase } from './base';\n",
    "class Derived extends ImportedBase {\n",
    "  readAgain(): string { return this.value; }\n",
    "}\n",
    "declare const instance: Derived;\n",
    "const result: string = instance.read();\n",
);

fn only_node(parsed: &ParseResult, file: FileId, kind: SyntaxKind) -> NodeRef {
    let mut nodes = parsed.arena.iter().filter_map(|(node, record)| {
        (record.kind == kind).then_some(NodeRef::new(parsed.arena.id(), file, node))
    });
    let node = nodes.next().unwrap_or_else(|| panic!("missing {kind:?}"));
    assert!(nodes.next().is_none(), "expected one {kind:?}");
    node
}

fn named(parsed: &ParseResult, file: FileId, kind: SyntaxKind, expected: &str) -> NodeRef {
    parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            if record.kind != kind {
                return None;
            }
            let name = match &record.data {
                NodeData::ClassDeclaration(data) => data.name?,
                NodeData::ImportSpecifier(data) => data.name,
                NodeData::ExportSpecifier(data) => data.name,
                NodeData::VariableDeclaration(data) => data.name,
                NodeData::PropertyDeclaration(data) => data.name,
                _ => return None,
            };
            let NodeData::Identifier(name) = &parsed.arena.get(name)?.data else {
                return None;
            };
            (name.text == expected).then_some(NodeRef::new(parsed.arena.id(), file, node))
        })
        .unwrap_or_else(|| panic!("missing {kind:?} {expected}"))
}

fn context<'arena>(
    provider: &'arena ParseResult,
    consumer: &'arena ParseResult,
) -> CanonicalCheckerContext<'arena> {
    let sources = [
        (PROVIDER, provider, "\"/project/base.ts\""),
        (CONSUMER, consumer, "\"/project/derived.ts\""),
    ];
    let mut binder = CanonicalBinder::new();
    for (file, parsed, path) in sources {
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
    for (file, parsed, _) in sources {
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
    }
    let import = only_node(consumer, CONSUMER, SyntaxKind::ImportDeclaration);
    let NodeData::ImportDeclaration(import) = &consumer.arena.get(import.node).unwrap().data
    else {
        unreachable!()
    };
    let module = NodeRef::new(consumer.arena.id(), CONSUMER, import.module_specifier);
    CanonicalCheckerContext::new_with_module_resolutions(
        binder.finish(),
        sources
            .into_iter()
            .map(|(file, parsed, _)| (file, &parsed.arena))
            .collect(),
        CanonicalCheckerOptions {
            intrinsic: IntrinsicBootstrapOptions {
                strict_null_checks: true,
                ..IntrinsicBootstrapOptions::default()
            },
            no_implicit_any: true,
            no_emit: true,
            ..CanonicalCheckerOptions::default()
        },
        CanonicalModuleResolutionManifestInput::new([CanonicalModuleResolutionEntry::resolved(
            module,
            CanonicalResolvedModuleInput::new(
                PROVIDER,
                CanonicalModuleResolutionMode::Esm,
                CanonicalModuleResolutionMode::Esm,
            ),
        )]),
    )
    .unwrap()
}

fn symbol(context: &CanonicalCheckerContext<'_>, node: NodeRef) -> SemanticSymbolId {
    let raw = context.file(node.file).unwrap().1.symbol(node).unwrap();
    context.store().get_merged_symbol(raw).unwrap()
}

fn value_type(context: &CanonicalCheckerContext<'_>, owner: SemanticSymbolId) -> TypeId {
    context
        .store()
        .value_symbol_links(owner)
        .unwrap()
        .resolved_type
        .unwrap()
}

fn heritage_expression(parsed: &ParseResult) -> NodeRef {
    let heritage = only_node(parsed, CONSUMER, SyntaxKind::ExpressionWithTypeArguments);
    let NodeData::ExpressionWithTypeArguments(data) =
        &parsed.arena.get(heritage.node).unwrap().data
    else {
        unreachable!()
    };
    NodeRef::new(parsed.arena.id(), CONSUMER, data.expression)
}

fn returned(parsed: &ParseResult, file: FileId) -> NodeRef {
    let statement = only_node(parsed, file, SyntaxKind::ReturnStatement);
    let NodeData::ReturnStatement(data) = &parsed.arena.get(statement.node).unwrap().data else {
        unreachable!()
    };
    NodeRef::new(parsed.arena.id(), file, data.expression.unwrap())
}

fn counts(context: &CanonicalCheckerContext<'_>) -> [usize; 9] {
    let store = context.store();
    [
        store.type_len(),
        store.symbol_len(),
        store.signature_len(),
        store.mapper_len(),
        store.type_alias_len(),
        store.index_info_len(),
        store.symbol_store().symbol_table_len(),
        store.merged_symbol_len(),
        store.type_resolution_len(),
    ]
}

#[allow(clippy::too_many_lines)] // Keep both alias hops and class identities in one check.
fn assert_imported_base(
    context: &mut CanonicalCheckerContext<'_>,
    provider: &ParseResult,
    consumer: &ParseResult,
) -> (ClassMembers, ClassMembers) {
    let base_declaration = named(provider, PROVIDER, SyntaxKind::ClassDeclaration, "Base");
    let base_owner = symbol(context, base_declaration);
    let export_alias = symbol(
        context,
        named(provider, PROVIDER, SyntaxKind::ExportSpecifier, "PublicBase"),
    );
    let import_alias = symbol(
        context,
        named(consumer, CONSUMER, SyntaxKind::ImportSpecifier, "ImportedBase"),
    );
    let derived_owner = symbol(
        context,
        named(consumer, CONSUMER, SyntaxKind::ClassDeclaration, "Derived"),
    );
    let base = context.get_nongeneric_class_members(base_owner).unwrap();
    let derived = context.get_nongeneric_class_members(derived_owner).unwrap();
    let inherited = derived.base().unwrap();
    assert_eq!(base.shells().declaration(), base_declaration);
    assert_eq!(inherited.symbol(), base_owner);
    assert_eq!(inherited.instance_type(), base.shells().instance_type());
    assert_eq!(
        inherited.applied_instance_type(),
        base.shells().instance_type()
    );
    assert_eq!(inherited.value_type(), base.shells().value_type());
    assert_ne!(derived.shells().instance_type(), inherited.instance_type());
    assert_ne!(derived.shells().value_type(), inherited.value_type());
    let store = context.store();
    let base_record = store.symbol(base_owner).unwrap();
    assert_eq!(base_record.flags(), SymbolFlags::CLASS);
    assert_eq!(base_record.export_symbol(), None);
    assert_eq!(base_record.declarations(), Some(&[base_declaration][..]));
    assert_ne!(export_alias, base_owner);
    assert_ne!(import_alias, export_alias);
    assert_eq!(
        store.symbol(export_alias).unwrap().flags(),
        SymbolFlags::ALIAS
    );
    let export_links = store.alias_symbol_links(export_alias).unwrap();
    assert_eq!(
        export_links.alias_target,
        AliasTargetState::Resolved(base_owner)
    );
    let import_links = store.alias_symbol_links(import_alias).unwrap();
    assert_eq!(import_links.immediate_target, Some(export_alias));
    assert_eq!(
        import_links.alias_target,
        AliasTargetState::Resolved(base_owner)
    );
    assert_eq!(import_links.type_only_declaration, None);
    assert_eq!(value_type(context, import_alias), inherited.value_type());
    let TypeData::Interface(instance) = store
        .type_payload(derived.shells().instance_type())
        .unwrap()
        .data()
    else {
        panic!("the derived class must keep its own instance")
    };
    assert_eq!(
        instance.resolved_base_constructor_type,
        Some(inherited.value_type())
    );
    assert_eq!(
        instance.resolved_base_types.as_deref(),
        Some(&[inherited.instance_type()][..])
    );
    let field = symbol(
        context,
        named(provider, PROVIDER, SyntaxKind::PropertyDeclaration, "value"),
    );
    assert!(derived.instance_properties().contains(&field));
    let string = store.intrinsic_bootstrap().unwrap().string_type;
    assert_eq!(value_type(context, field), string);
    let heritage = heritage_expression(consumer);
    assert_eq!(
        store
            .type_node_links(heritage)
            .and_then(|links| links.resolved_type),
        Some(inherited.value_type())
    );
    assert_eq!(
        store
            .symbol_node_links(heritage)
            .and_then(|links| links.resolved_symbol),
        Some(import_alias)
    );
    assert_eq!(
        context.get_symbol_at_location(heritage),
        Ok(Some(import_alias))
    );
    assert_eq!(
        context.get_type_at_location(heritage),
        Ok(inherited.value_type())
    );
    for (file, parsed) in [(PROVIDER, provider), (CONSUMER, consumer)] {
        let read = returned(parsed, file);
        assert_eq!(
            context
                .store()
                .type_node_links(read)
                .and_then(|links| links.resolved_type),
            Some(string)
        );
        assert_eq!(context.get_type_at_location(read), Ok(string));
        assert_eq!(context.get_symbol_at_location(read), Ok(Some(field)));
        assert!(
            context
                .store()
                .source_file_links(context.source_file(file).unwrap())
                .unwrap()
                .type_checked
        );
    }
    let call = only_node(consumer, CONSUMER, SyntaxKind::CallExpression);
    assert_eq!(context.get_type_at_location(call), Ok(string));
    (base, derived)
}

fn assert_replay(
    context: &mut CanonicalCheckerContext<'_>,
    provider: &ParseResult,
    consumer: &ParseResult,
) {
    let members = assert_imported_base(context, provider, consumer);
    let warm_counts = counts(context);
    let warm_relations = context.store().relation_state_snapshot();
    let diagnostics = context.diagnostics().clone();
    for _ in 0..2 {
        context.check_source_file(CONSUMER).unwrap();
        context.recheck_source_file(CONSUMER).unwrap();
        context.recheck_source_file(PROVIDER).unwrap();
        assert_eq!(assert_imported_base(context, provider, consumer), members);
        assert_eq!(counts(context), warm_counts);
        assert_eq!(context.store().relation_state_snapshot(), warm_relations);
        assert_eq!(context.diagnostics(), &diagnostics);
    }
}

#[test]
fn imported_local_class_exports_keep_base_identity_and_inherited_types() {
    let provider = parse_source_file(BASE);
    let consumer = parse_source_file(DERIVED);
    for provider_first in [false, true] {
        let mut context = context(&provider, &consumer);
        if provider_first {
            context.check_source_file(PROVIDER).unwrap();
        }
        context.check_source_file(CONSUMER).unwrap();
        assert_imported_base(&mut context, &provider, &consumer);
        assert!(
            context.diagnostics().is_empty(),
            "{:?}",
            context.diagnostics()
        );
        assert_replay(&mut context, &provider, &consumer);
    }
}

#[test]
fn imported_local_class_exports_keep_exact_provider_errors_on_replay() {
    let provider = parse_source_file(&format!("{BASE}const wrong: string = 1;"));
    let consumer = parse_source_file(DERIVED);
    let declaration = named(&provider, PROVIDER, SyntaxKind::VariableDeclaration, "wrong");
    let NodeData::VariableDeclaration(variable) =
        &provider.arena.get(declaration.node).unwrap().data
    else {
        unreachable!()
    };
    let name = NodeRef::new(provider.arena.id(), PROVIDER, variable.name);
    for provider_first in [false, true] {
        let mut context = context(&provider, &consumer);
        if provider_first {
            context.check_source_file(PROVIDER).unwrap();
        }
        context.check_source_file(CONSUMER).unwrap();
        assert_imported_base(&mut context, &provider, &consumer);
        let [diagnostic] = context.diagnostics().as_slice() else {
            panic!("the provider must keep its one assignment error")
        };
        assert_eq!(diagnostic.node, Some(name));
        assert_eq!(diagnostic.diagnostic.code(), 2322);
        assert_eq!(diagnostic.diagnostic.arguments, ["number", "string"]);
        assert_eq!(
            diagnostic.diagnostic.render().unwrap(),
            "Type 'number' is not assignable to type 'string'."
        );
        assert_eq!(diagnostic.range_override, None);
        assert!(diagnostic.related_information.is_empty());
        assert_replay(&mut context, &provider, &consumer);
    }
}

#[test]
#[allow(clippy::too_many_lines)] // Keep the imported generic base and its replay checks together.
fn imported_local_generic_class_heritage_keeps_applied_base_identity() {
    let provider = parse_source_file("class Base<T> { value!: T; } export { Base as PublicBase };");
    let consumer = parse_source_file(concat!(
        "import { PublicBase as ImportedBase } from './base';\n",
        "class Derived extends ImportedBase<string> {}\n",
    ));
    let heritage = heritage_expression(&consumer);
    let wrapper = only_node(&consumer, CONSUMER, SyntaxKind::ExpressionWithTypeArguments);
    let mut context = context(&provider, &consumer);
    let base_declaration = named(&provider, PROVIDER, SyntaxKind::ClassDeclaration, "Base");
    let base_owner = symbol(&context, base_declaration);
    let derived_declaration = named(&consumer, CONSUMER, SyntaxKind::ClassDeclaration, "Derived");
    let derived_owner = symbol(&context, derived_declaration);
    let parameter = only_node(&provider, PROVIDER, SyntaxKind::TypeParameter);
    let parameter_owner = symbol(&context, parameter);
    let field_declaration = named(
        &provider,
        PROVIDER,
        SyntaxKind::PropertyDeclaration,
        "value",
    );
    let field = symbol(&context, field_declaration);
    let export_alias = symbol(
        &context,
        named(
            &provider,
            PROVIDER,
            SyntaxKind::ExportSpecifier,
            "PublicBase",
        ),
    );
    let import_alias = symbol(
        &context,
        named(
            &consumer,
            CONSUMER,
            SyntaxKind::ImportSpecifier,
            "ImportedBase",
        ),
    );
    let check = |context: &mut CanonicalCheckerContext<'_>| {
        let base = context.get_nongeneric_class_members(base_owner).unwrap();
        let derived = context.get_nongeneric_class_members(derived_owner).unwrap();
        let formal = context
            .get_declared_type_of_symbol(parameter_owner)
            .unwrap();
        assert_eq!(
            context.get_declared_type_of_symbol(base_owner),
            Ok(base.shells().instance_type())
        );
        assert_eq!(
            context.get_declared_type_of_symbol(derived_owner),
            Ok(derived.shells().instance_type())
        );
        assert_eq!(base.shells().declaration(), base_declaration);
        assert_eq!(derived.shells().declaration(), derived_declaration);
        assert_ne!(
            base.shells().instance_type(),
            derived.shells().instance_type()
        );
        assert_ne!(base.shells().value_type(), derived.shells().value_type());
        let inherited = derived.base().unwrap();
        assert_eq!(inherited.symbol(), base_owner);
        assert_eq!(inherited.instance_type(), base.shells().instance_type());
        assert_eq!(inherited.value_type(), base.shells().value_type());
        let applied = inherited.applied_instance_type();
        assert_ne!(applied, inherited.instance_type());

        let store = context.store();
        let string = store.intrinsic_bootstrap().unwrap().string_type;
        let TypeData::TypeReference(reference) = store.type_payload(applied).unwrap().data() else {
            panic!("the base must keep its string argument")
        };
        assert_eq!(reference.object.target, Some(inherited.instance_type()));
        assert_eq!(
            reference.resolved_type_arguments.as_deref(),
            Some(&[string][..])
        );
        let TypeData::Interface(instance) = store
            .type_payload(derived.shells().instance_type())
            .unwrap()
            .data()
        else {
            panic!("the derived class must keep its own instance")
        };
        assert_eq!(
            instance.resolved_base_types.as_deref(),
            Some(&[applied][..])
        );
        assert_eq!(
            instance.resolved_base_constructor_type,
            Some(inherited.value_type())
        );
        let TypeData::Interface(base_instance) = store
            .type_payload(base.shells().instance_type())
            .unwrap()
            .data()
        else {
            panic!("the base must keep its original formal")
        };
        assert_eq!(
            base_instance.reference.resolved_type_arguments.as_deref(),
            Some(&[formal][..])
        );
        assert_eq!(
            provider.arena.get(parameter.node).unwrap().parent,
            Some(base_declaration.node)
        );
        assert_eq!(
            store.symbol(parameter_owner).unwrap().parent(),
            Some(base_owner)
        );
        let formal_record = store.type_payload(formal).unwrap();
        assert_eq!(formal_record.symbol(), Some(parameter_owner));
        let TypeData::TypeParameter(parameter_type) = formal_record.data() else {
            panic!("the original formal must remain a type parameter")
        };
        assert_eq!(parameter_type.target, None);
        assert_eq!(parameter_type.mapper, None);
        assert_eq!(
            store.symbol(field).unwrap().declarations(),
            Some(&[field_declaration][..])
        );
        assert_eq!(store.symbol(field).unwrap().parent(), Some(base_owner));
        let field_links = store.value_symbol_links(field).unwrap();
        assert_eq!(field_links.resolved_type, Some(formal));
        assert_eq!(field_links.target, None);
        assert_eq!(field_links.mapper, None);
        assert_eq!(base.instance_properties(), &[field]);
        assert_eq!(derived.instance_properties(), &[field]);
        assert!(derived.declared_instance_properties().is_empty());
        assert_eq!(
            store
                .signature(base.default_construct_signature())
                .unwrap()
                .resolved_return_type(),
            Some(base.shells().instance_type())
        );

        assert_ne!(import_alias, export_alias);
        assert_ne!(export_alias, base_owner);
        assert_eq!(
            store.symbol(base_owner).unwrap().flags(),
            SymbolFlags::CLASS
        );
        for alias in [export_alias, import_alias] {
            assert_eq!(store.symbol(alias).unwrap().flags(), SymbolFlags::ALIAS);
            let links = store.alias_symbol_links(alias).unwrap();
            assert_eq!(links.alias_target, AliasTargetState::Resolved(base_owner));
            assert_eq!(links.type_only_declaration, None);
        }
        assert_eq!(
            store
                .alias_symbol_links(import_alias)
                .unwrap()
                .immediate_target,
            Some(export_alias)
        );
        assert_eq!(value_type(context, import_alias), inherited.value_type());
        assert_eq!(
            store
                .type_node_links(heritage)
                .and_then(|links| links.resolved_type),
            Some(inherited.value_type())
        );
        assert_eq!(
            store
                .symbol_node_links(heritage)
                .and_then(|links| links.resolved_symbol),
            Some(import_alias)
        );
        assert_eq!(
            store
                .type_node_links(wrapper)
                .and_then(|links| links.resolved_type),
            Some(applied)
        );
        for file in [PROVIDER, CONSUMER] {
            assert!(
                store
                    .source_file_links(context.source_file(file).unwrap())
                    .unwrap()
                    .type_checked
            );
        }
        assert!(context.diagnostics().is_empty());
        (base, derived, formal)
    };
    context.check_source_file(CONSUMER).unwrap();
    let identities = check(&mut context);
    let warm_counts = counts(&context);
    let relations = context.store().relation_state_snapshot();
    let diagnostics = context.diagnostics().clone();
    for _ in 0..2 {
        context.check_source_file(CONSUMER).unwrap();
        context.recheck_source_file(CONSUMER).unwrap();
        assert_eq!(check(&mut context), identities);
        assert_eq!(counts(&context), warm_counts);
        assert_eq!(context.store().relation_state_snapshot(), relations);
        assert_eq!(context.diagnostics(), &diagnostics);
    }
}
