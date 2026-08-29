use ts_ast::{FileId, NodeData, NodeRef};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId,
};
use ts_checker::semantic::{
    AliasSymbolLinks, AliasTargetState, CanonicalCheckerContext, CanonicalCheckerDiagnostics,
    CanonicalCheckerOptions, CanonicalModuleResolutionEntry,
    CanonicalModuleResolutionManifestInput, CanonicalModuleResolutionMode,
    CanonicalResolvedModuleInput, SignatureId, SourceFileLinks, SymbolNodeLinks, TypeAliasLinks,
    TypeData, TypeId, TypeMapperId, TypeNodeLinks, ValueSymbolLinks,
};
use ts_parser::{ParseResult, parse_source_file};

const SOURCE: FileId = FileId::new(46_201);
const BARREL: FileId = FileId::new(46_202);
const PROVIDER: FileId = FileId::new(46_203);
const SUBSCRIPTION: &str = concat!(
    "import type { Noop } from '../types';\n\n",
    "export type Subscription = {\n",
    "  unsubscribe: Noop;\n",
    "};\n",
);
const BARREL_SOURCE: &str = "export * from './utils';\n";
const PROVIDER_SOURCE: &str = "export type Noop = () => void;\n";

#[derive(Clone, Copy)]
struct Alias {
    declaration: NodeRef,
    body: NodeRef,
}

#[derive(Clone, Copy)]
struct Property {
    owner: NodeRef,
    declaration: NodeRef,
    annotation: NodeRef,
}

#[derive(Debug, Eq, PartialEq)]
struct SignatureState {
    id: SignatureId,
    declaration: Option<NodeRef>,
    return_type: Option<TypeId>,
    target: Option<SignatureId>,
    mapper: Option<TypeMapperId>,
}

#[derive(Debug, Eq, PartialEq)]
struct Snapshot {
    counts: [usize; 6],
    sources: [Option<SourceFileLinks>; 3],
    annotations: Vec<Option<TypeNodeLinks>>,
    reference_symbols: Vec<Option<SymbolNodeLinks>>,
    values: Vec<Option<ValueSymbolLinks>>,
    aliases: Vec<Option<TypeAliasLinks>>,
    import: Option<AliasSymbolLinks>,
    signatures: Vec<SignatureState>,
    diagnostics: CanonicalCheckerDiagnostics,
}

fn module_specifier(parsed: &ParseResult, file: FileId) -> NodeRef {
    parsed
        .arena
        .iter()
        .find_map(|(_, record)| {
            let specifier = match &record.data {
                NodeData::ImportDeclaration(import) => import.module_specifier,
                NodeData::ExportDeclaration(export) => export.module_specifier?,
                _ => return None,
            };
            Some(NodeRef::new(parsed.arena.id(), file, specifier))
        })
        .expect("the importer and barrel each have one module specifier")
}

fn context<'arena>(
    source: &'arena ParseResult,
    barrel: &'arena ParseResult,
    provider: &'arena ParseResult,
) -> CanonicalCheckerContext<'arena> {
    let files = [
        (SOURCE, source, "\"/project/src/utils/createSubject.ts\""),
        (BARREL, barrel, "\"/project/src/types/index.ts\""),
        (PROVIDER, provider, "\"/project/src/types/utils.ts\""),
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
    let resolutions = [
        (module_specifier(source, SOURCE), BARREL),
        (module_specifier(barrel, BARREL), PROVIDER),
    ];
    CanonicalCheckerContext::new_with_module_resolutions(
        binder.finish(),
        files
            .into_iter()
            .map(|(file, parsed, _)| (file, &parsed.arena))
            .collect(),
        CanonicalCheckerOptions::default(),
        CanonicalModuleResolutionManifestInput::new(resolutions.map(|(specifier, target)| {
            CanonicalModuleResolutionEntry::resolved(
                specifier,
                CanonicalResolvedModuleInput::new(
                    target,
                    CanonicalModuleResolutionMode::Esm,
                    CanonicalModuleResolutionMode::Esm,
                ),
            )
        })),
    )
    .unwrap()
}

fn alias(parsed: &ParseResult, file: FileId, expected: &str) -> Alias {
    parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            let NodeData::TypeAliasDeclaration(alias) = &record.data else {
                return None;
            };
            let NodeData::Identifier(name) = &parsed.arena.get(alias.name)?.data else {
                return None;
            };
            (name.text == expected).then_some(Alias {
                declaration: NodeRef::new(parsed.arena.id(), file, node),
                body: NodeRef::new(parsed.arena.id(), file, alias.type_),
            })
        })
        .unwrap_or_else(|| panic!("the source declares type {expected}"))
}

fn property(parsed: &ParseResult, owner: Alias, expected: &str) -> Property {
    let NodeData::TypeLiteralNode(literal) = &parsed.arena.get(owner.body.node).unwrap().data
    else {
        panic!("the property owner must be the original type literal");
    };
    literal
        .members
        .nodes
        .iter()
        .find_map(|&node| {
            let (name, annotation) = match &parsed.arena.get(node)?.data {
                NodeData::PropertyDeclaration(property) => (property.name, property.type_?),
                NodeData::PropertySignatureDeclaration(property) => (property.name, property.type_),
                _ => return None,
            };
            let NodeData::Identifier(name) = &parsed.arena.get(name)?.data else {
                return None;
            };
            if name.text != expected {
                return None;
            }
            assert_eq!(parsed.arena.get(node)?.parent, Some(owner.body.node));
            assert_eq!(parsed.arena.get(annotation)?.parent, Some(node));
            Some(Property {
                owner: owner.body,
                declaration: NodeRef::new(parsed.arena.id(), owner.body.file, node),
                annotation: NodeRef::new(parsed.arena.id(), owner.body.file, annotation),
            })
        })
        .unwrap_or_else(|| panic!("the type literal declares {expected}"))
}

fn import_binding(source: &ParseResult) -> NodeRef {
    source
        .arena
        .iter()
        .find_map(|(node, record)| {
            matches!(record.data, NodeData::ImportSpecifier(_)).then_some(NodeRef::new(
                source.arena.id(),
                SOURCE,
                node,
            ))
        })
        .expect("the source has one named type import")
}

fn symbol(context: &CanonicalCheckerContext<'_>, node: NodeRef) -> SemanticSymbolId {
    context
        .file(node.file)
        .unwrap()
        .1
        .symbol(node)
        .and_then(|symbol| context.store().get_merged_symbol(symbol))
        .unwrap()
}

fn node_type(context: &CanonicalCheckerContext<'_>, node: NodeRef) -> Option<TypeId> {
    context
        .store()
        .type_node_links(node)
        .and_then(|links| links.resolved_type)
}

fn value_type(context: &CanonicalCheckerContext<'_>, symbol: SemanticSymbolId) -> Option<TypeId> {
    context
        .store()
        .value_symbol_links(symbol)
        .and_then(|links| links.resolved_type)
}

fn assert_unchecked(context: &CanonicalCheckerContext<'_>, file: FileId) {
    assert!(
        context
            .store()
            .source_file_links(context.source_file(file).unwrap())
            .is_none_or(|links| !links.type_checked),
    );
}

fn assert_type_only_import(
    context: &CanonicalCheckerContext<'_>,
    binding: NodeRef,
    target: SemanticSymbolId,
) {
    let imported = symbol(context, binding);
    let links = context.store().alias_symbol_links(imported).unwrap();
    assert_eq!(links.immediate_target, Some(target));
    assert_eq!(links.alias_target, AliasTargetState::Resolved(target));
    assert_eq!(links.type_only_declaration, Some(binding));
    assert!(context.store().value_symbol_links(imported).is_none());
    assert!(context.store().value_symbol_links(target).is_none());
}

fn assert_callable(
    context: &mut CanonicalCheckerContext<'_>,
    noop: Alias,
    type_: TypeId,
) -> SignatureId {
    let owner = symbol(context, noop.declaration);
    let function_owner = symbol(context, noop.body);
    assert_eq!(context.get_declared_type_of_symbol(owner), Ok(type_));
    assert_eq!(context.get_type_from_type_node(noop.body), Ok(type_));
    let record = context.store().type_payload(type_).unwrap();
    assert_eq!(record.symbol(), Some(function_owner));
    assert_eq!(
        context
            .store()
            .type_alias(record.alias().unwrap())
            .unwrap()
            .symbol(),
        Some(owner)
    );
    let TypeData::Object(object) = record.data() else {
        panic!("Noop must keep its declared function type");
    };
    assert_eq!(object.target, None);
    assert_eq!(object.mapper, None);
    assert_eq!(object.structured.call_signature_count, 1);
    let [signature] = object.structured.signatures.as_deref().unwrap() else {
        panic!("Noop has one call signature");
    };
    let signature = *signature;
    let record = context.store().signature(signature).unwrap();
    assert_eq!(record.declaration(), Some(noop.body));
    assert!(record.parameters().is_empty());
    assert!(record.type_parameters().is_empty());
    assert_eq!(record.target(), None);
    assert_eq!(record.mapper(), None);
    let void = context.store().intrinsic_bootstrap().unwrap().void_type;
    assert_eq!(context.get_return_type_of_signature(signature), Ok(void));
    assert_eq!(
        context
            .store()
            .signature(signature)
            .unwrap()
            .resolved_return_type(),
        Some(void)
    );
    signature
}

fn assert_property_type(
    context: &CanonicalCheckerContext<'_>,
    property: Property,
    target: SemanticSymbolId,
    type_: TypeId,
) {
    assert_eq!(node_type(context, property.annotation), Some(type_));
    assert_eq!(
        context
            .store()
            .symbol_node_links(property.annotation)
            .unwrap()
            .resolved_symbol,
        Some(target),
    );
    assert_eq!(
        value_type(context, symbol(context, property.declaration)),
        Some(type_)
    );
}

fn snapshot(
    context: &CanonicalCheckerContext<'_>,
    properties: &[Property],
    aliases: &[SemanticSymbolId],
    binding: NodeRef,
) -> Snapshot {
    let store = context.store();
    let imported = symbol(context, binding);
    let values = properties
        .iter()
        .map(|property| symbol(context, property.declaration))
        .chain(aliases.iter().copied())
        .chain([imported]);
    Snapshot {
        counts: [
            store.type_len(),
            store.symbol_len(),
            store.signature_len(),
            store.mapper_len(),
            store.type_alias_len(),
            store.symbol_store().symbol_table_len(),
        ],
        sources: [SOURCE, BARREL, PROVIDER].map(|file| {
            store
                .source_file_links(context.source_file(file).unwrap())
                .cloned()
        }),
        annotations: properties
            .iter()
            .map(|property| store.type_node_links(property.annotation).cloned())
            .collect(),
        reference_symbols: properties
            .iter()
            .map(|property| store.symbol_node_links(property.annotation).cloned())
            .collect(),
        values: values
            .map(|symbol| store.value_symbol_links(symbol).cloned())
            .collect(),
        aliases: aliases
            .iter()
            .map(|&symbol| store.type_alias_links(symbol).cloned())
            .collect(),
        import: store.alias_symbol_links(imported).cloned(),
        signatures: store
            .signatures()
            .map(|(id, signature)| SignatureState {
                id,
                declaration: signature.declaration(),
                return_type: signature.resolved_return_type(),
                target: signature.target(),
                mapper: signature.mapper(),
            })
            .collect(),
        diagnostics: context.diagnostics().clone(),
    }
}

fn assert_source_replay(
    context: &mut CanonicalCheckerContext<'_>,
    properties: &[Property],
    aliases: &[SemanticSymbolId],
    binding: NodeRef,
) {
    let before = snapshot(context, properties, aliases, binding);
    context.check_source_file(SOURCE).unwrap();
    assert_eq!(snapshot(context, properties, aliases, binding), before);
    context.recheck_source_file(SOURCE).unwrap();
    assert_eq!(snapshot(context, properties, aliases, binding), before);
}

#[test]
fn original_subscription_source_checks_through_the_export_star_route() {
    let source = parse_source_file(SUBSCRIPTION);
    let barrel = parse_source_file(BARREL_SOURCE);
    let provider = parse_source_file(PROVIDER_SOURCE);
    let mut context = context(&source, &barrel, &provider);
    let subscription = alias(&source, SOURCE, "Subscription");
    let unsubscribe = property(&source, subscription, "unsubscribe");
    let noop = alias(&provider, PROVIDER, "Noop");
    let binding = import_binding(&source);
    let aliases = [
        symbol(&context, subscription.declaration),
        symbol(&context, noop.declaration),
    ];
    let module = symbol(&context, context.source_file(BARREL).unwrap().node_ref());
    let before = snapshot(&context, &[unsubscribe], &aliases, binding);
    assert_eq!(
        context.get_module_export_by_name(module, "Noop"),
        Ok(Some(aliases[1]))
    );
    assert_eq!(
        snapshot(&context, &[unsubscribe], &aliases, binding),
        before
    );
    assert!(
        context
            .store()
            .alias_symbol_links(symbol(&context, binding))
            .is_none()
    );

    context.check_source_file(SOURCE).unwrap();

    let callable = node_type(&context, unsubscribe.annotation).unwrap();
    let signature = assert_callable(&mut context, noop, callable);
    assert_property_type(&context, unsubscribe, aliases[1], callable);
    assert_type_only_import(&context, binding, aliases[1]);
    assert_unchecked(&context, BARREL);
    assert_unchecked(&context, PROVIDER);
    assert!(context.diagnostics().is_empty());
    assert_source_replay(&mut context, &[unsubscribe], &aliases, binding);
    assert_eq!(assert_callable(&mut context, noop, callable), signature);
    assert_property_type(&context, unsubscribe, aliases[1], callable);
    assert_type_only_import(&context, binding, aliases[1]);
}

#[test]
fn subscription_property_queries_keep_identity_in_both_query_orders() {
    for declaration_first in [false, true] {
        let source = parse_source_file(SUBSCRIPTION);
        let barrel = parse_source_file(BARREL_SOURCE);
        let provider = parse_source_file(PROVIDER_SOURCE);
        let mut context = context(&source, &barrel, &provider);
        let subscription = alias(&source, SOURCE, "Subscription");
        let unsubscribe = property(&source, subscription, "unsubscribe");
        let noop = alias(&provider, PROVIDER, "Noop");
        let binding = import_binding(&source);
        let aliases = [
            symbol(&context, subscription.declaration),
            symbol(&context, noop.declaration),
        ];
        assert!(
            context
                .store()
                .alias_symbol_links(symbol(&context, binding))
                .is_none()
        );
        let first =
            declaration_first.then(|| context.get_declared_type_of_symbol(aliases[0]).unwrap());

        let callable = context
            .get_type_from_type_node(unsubscribe.annotation)
            .unwrap();

        let declared = context.get_declared_type_of_symbol(aliases[0]).unwrap();
        if let Some(first) = first {
            assert_eq!(declared, first);
        }
        assert_eq!(node_type(&context, subscription.body), Some(declared));
        let signature = assert_callable(&mut context, noop, callable);
        assert_property_type(&context, unsubscribe, aliases[1], callable);
        assert_type_only_import(&context, binding, aliases[1]);
        for file in [SOURCE, BARREL, PROVIDER] {
            assert_unchecked(&context, file);
        }
        let before = snapshot(&context, &[unsubscribe], &aliases, binding);
        assert_eq!(
            context.get_type_from_type_node(unsubscribe.annotation),
            Ok(callable)
        );
        assert_eq!(
            context.get_declared_type_of_symbol(aliases[0]),
            Ok(declared)
        );
        assert_eq!(assert_callable(&mut context, noop, callable), signature);
        assert_eq!(
            snapshot(&context, &[unsubscribe], &aliases, binding),
            before
        );

        context.check_source_file(SOURCE).unwrap();
        assert!(context.diagnostics().is_empty());
        assert_property_type(&context, unsubscribe, aliases[1], callable);
        assert_source_replay(&mut context, &[unsubscribe], &aliases, binding);
    }
}

#[test]
fn distinct_property_roots_share_only_the_import_and_callable() {
    let text =
        format!("{SUBSCRIPTION}\nexport type OtherSubscription = {{\n  unsubscribe: Noop;\n}};\n");
    for reverse in [false, true] {
        let source = parse_source_file(&text);
        let barrel = parse_source_file(BARREL_SOURCE);
        let provider = parse_source_file(PROVIDER_SOURCE);
        let mut context = context(&source, &barrel, &provider);
        let declarations = [
            alias(&source, SOURCE, "Subscription"),
            alias(&source, SOURCE, "OtherSubscription"),
        ];
        let properties = declarations.map(|owner| property(&source, owner, "unsubscribe"));
        let noop = alias(&provider, PROVIDER, "Noop");
        let binding = import_binding(&source);
        let aliases = [
            symbol(&context, declarations[0].declaration),
            symbol(&context, declarations[1].declaration),
            symbol(&context, noop.declaration),
        ];
        assert_ne!(properties[0].owner, properties[1].owner);
        assert_ne!(properties[0].declaration, properties[1].declaration);
        assert_ne!(properties[0].annotation, properties[1].annotation);
        assert_ne!(
            symbol(&context, properties[0].declaration),
            symbol(&context, properties[1].declaration)
        );
        let [first, second] = if reverse { [1, 0] } else { [0, 1] };

        let callable = context
            .get_type_from_type_node(properties[first].annotation)
            .unwrap();

        assert_eq!(node_type(&context, properties[second].annotation), None);
        assert_eq!(
            value_type(&context, symbol(&context, properties[second].declaration)),
            None
        );
        let import = context
            .store()
            .alias_symbol_links(symbol(&context, binding))
            .cloned();
        assert_eq!(
            context.get_type_from_type_node(properties[second].annotation),
            Ok(callable)
        );
        assert_eq!(
            context
                .store()
                .alias_symbol_links(symbol(&context, binding)),
            import.as_ref()
        );
        let signature = assert_callable(&mut context, noop, callable);
        assert_type_only_import(&context, binding, aliases[2]);

        context.check_source_file(SOURCE).unwrap();
        assert_ne!(
            node_type(&context, declarations[0].body),
            node_type(&context, declarations[1].body)
        );
        for property in properties {
            assert_property_type(&context, property, aliases[2], callable);
        }
        assert!(context.diagnostics().is_empty());
        let before = snapshot(&context, &properties, &aliases, binding);
        for index in [second, first] {
            assert_eq!(
                context.get_type_from_type_node(properties[index].annotation),
                Ok(callable)
            );
        }
        assert_eq!(assert_callable(&mut context, noop, callable), signature);
        assert_eq!(snapshot(&context, &properties, &aliases, binding), before);
        assert_source_replay(&mut context, &properties, &aliases, binding);
    }
}

#[test]
fn original_generic_template_property_queries_keep_sibling_values_cold() {
    let source = parse_source_file(concat!(
        "import type { Noop } from '../types';\n",
        "export type SubscriptionTemplate<T> = {\n",
        "  unsubscribe: Noop;\n",
        "  untouched: T;\n",
        "};\n",
    ));
    let barrel = parse_source_file(BARREL_SOURCE);
    let provider = parse_source_file(PROVIDER_SOURCE);
    let mut context = context(&source, &barrel, &provider);
    let template = alias(&source, SOURCE, "SubscriptionTemplate");
    let properties = [
        property(&source, template, "unsubscribe"),
        property(&source, template, "untouched"),
    ];
    let noop = alias(&provider, PROVIDER, "Noop");
    let binding = import_binding(&source);
    let aliases = [
        symbol(&context, template.declaration),
        symbol(&context, noop.declaration),
    ];

    let target = context.get_declared_type_of_symbol(aliases[0]).unwrap();

    let TypeData::Object(object) = context.store().type_payload(target).unwrap().data() else {
        panic!("the generic alias must retain its original object target");
    };
    assert_eq!(object.target, None);
    assert_eq!(object.mapper, None);
    assert!(object.structured.members.is_none());
    assert!(object.structured.properties.is_none());
    assert_eq!(
        context.store().type_payload(target).unwrap().symbol(),
        Some(symbol(&context, template.body))
    );
    assert!(
        context
            .store()
            .alias_symbol_links(symbol(&context, binding))
            .is_none()
    );
    for property in properties {
        assert_eq!(node_type(&context, property.annotation), None);
        assert_eq!(
            value_type(&context, symbol(&context, property.declaration)),
            None
        );
    }

    let callable = context
        .get_type_from_type_node(properties[0].annotation)
        .unwrap();

    let signature = assert_callable(&mut context, noop, callable);
    assert_type_only_import(&context, binding, aliases[1]);
    assert_eq!(node_type(&context, properties[1].annotation), None);
    for property in properties {
        assert_eq!(
            value_type(&context, symbol(&context, property.declaration)),
            None
        );
    }
    let before = snapshot(&context, &properties, &aliases, binding);
    assert_eq!(context.get_declared_type_of_symbol(aliases[0]), Ok(target));
    assert_eq!(
        context.get_type_from_type_node(properties[0].annotation),
        Ok(callable)
    );
    assert_eq!(assert_callable(&mut context, noop, callable), signature);
    assert_eq!(snapshot(&context, &properties, &aliases, binding), before);

    context.check_source_file(SOURCE).unwrap();
    for property in properties {
        assert_eq!(
            value_type(&context, symbol(&context, property.declaration)),
            None
        );
    }
    assert_eq!(node_type(&context, template.body), Some(target));
    assert_eq!(
        node_type(&context, properties[0].annotation),
        Some(callable)
    );
    assert!(context.diagnostics().is_empty());
    assert_source_replay(&mut context, &properties, &aliases, binding);
    assert_type_only_import(&context, binding, aliases[1]);
}
