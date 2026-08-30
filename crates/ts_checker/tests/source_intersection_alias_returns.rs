use ts_ast::{FileId, NodeData, NodeRef};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId, SymbolFlags,
};
use ts_checker::semantic::{
    AliasSymbolLinks, AliasTargetState, CanonicalCheckerContext, CanonicalCheckerDiagnostics,
    CanonicalCheckerOptions, CanonicalModuleResolutionEntry,
    CanonicalModuleResolutionManifestInput, CanonicalModuleResolutionMode,
    CanonicalResolvedModuleInput, DeclaredTypeLinks, SignatureId, SignatureLinks, SourceFileLinks,
    SymbolNodeLinks, TypeAliasId, TypeAliasLinks, TypeData, TypeId, TypeMapperId, TypeNodeLinks,
    ValueSymbolLinks,
    type_records::{IntersectionTypeData, ObjectTypeData},
};
use ts_parser::{ParseResult, parse_source_file};

const SOURCE: FileId = FileId::new(46_211);
const BARREL: FileId = FileId::new(46_212);
const PROVIDER: FileId = FileId::new(46_213);
const SOURCE_TEXT: &str = concat!(
    "import type { Noop } from '../types';\n",
    "export type Subscription = { unsubscribe: Noop; };\n",
    "export type Observer<T> = { next: (value: T) => void };\n",
    "export type Subject<T> = { subscribe: (value: Observer<T>) => Subscription; } & Observer<T>;\n",
    "export default <T>(): Subject<T> => {\n",
    "  const next = (value: T) => {};\n",
    "  const subscribe = (observer: Observer<T>): Subscription => {\n",
    "    return { unsubscribe: () => {} };\n",
    "  };\n",
    "  return { next, subscribe };\n",
    "};\n",
);
const BARREL_TEXT: &str = "export * from './utils';\n";
const PROVIDER_TEXT: &str = "export type Noop = () => void;\n";

#[derive(Clone, Copy)]
struct Alias {
    declaration: NodeRef,
    body: NodeRef,
    parameter: Option<NodeRef>,
}

#[derive(Clone, Copy)]
struct Property {
    declaration: NodeRef,
    annotation: NodeRef,
}

struct Arrow {
    declaration: NodeRef,
    binding: NodeRef,
    annotation: Option<NodeRef>,
    type_parameters: Vec<NodeRef>,
    parameters: Vec<NodeRef>,
    returned: Option<NodeRef>,
}

fn module_specifier(parsed: &ParseResult, file: FileId) -> NodeRef {
    parsed
        .arena
        .iter()
        .find_map(|(_, record)| {
            let node = match &record.data {
                NodeData::ImportDeclaration(import) => import.module_specifier,
                NodeData::ExportDeclaration(export) => export.module_specifier?,
                _ => return None,
            };
            Some(NodeRef::new(parsed.arena.id(), file, node))
        })
        .unwrap()
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
    CanonicalCheckerContext::new_with_module_resolutions(
        binder.finish(),
        files
            .into_iter()
            .map(|(file, parsed, _)| (file, &parsed.arena))
            .collect(),
        CanonicalCheckerOptions::default(),
        CanonicalModuleResolutionManifestInput::new(
            [
                (module_specifier(source, SOURCE), BARREL),
                (module_specifier(barrel, BARREL), PROVIDER),
            ]
            .map(|(specifier, target)| {
                CanonicalModuleResolutionEntry::resolved(
                    specifier,
                    CanonicalResolvedModuleInput::new(
                        target,
                        CanonicalModuleResolutionMode::Esm,
                        CanonicalModuleResolutionMode::Esm,
                    ),
                )
            }),
        ),
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
            let node_ref = |node| NodeRef::new(parsed.arena.id(), file, node);
            (name.text == expected).then(|| Alias {
                declaration: node_ref(node),
                body: node_ref(alias.type_),
                parameter: alias.type_parameters.as_ref().map(|parameters| {
                    let [parameter] = parameters.nodes.as_slice() else {
                        panic!("this alias has one original type parameter")
                    };
                    node_ref(*parameter)
                }),
            })
        })
        .unwrap()
}

fn property_node(parsed: &ParseResult, owner: NodeRef, expected: &str) -> NodeRef {
    let members = match &parsed.arena.get(owner.node).unwrap().data {
        NodeData::TypeLiteralNode(literal) => &literal.members.nodes,
        NodeData::ObjectLiteralExpression(literal) => &literal.properties.nodes,
        _ => panic!("expected the original type or value literal"),
    };
    members
        .iter()
        .find_map(|&node| {
            let name = match &parsed.arena.get(node)?.data {
                NodeData::PropertyDeclaration(property) => property.name,
                NodeData::PropertySignatureDeclaration(property) => property.name,
                NodeData::PropertyAssignment(property) => property.name,
                NodeData::ShorthandPropertyAssignment(property) => property.name,
                _ => return None,
            };
            let NodeData::Identifier(name) = &parsed.arena.get(name)?.data else {
                return None;
            };
            (name.text == expected).then_some(NodeRef::new(owner.arena, owner.file, node))
        })
        .unwrap()
}

fn property(parsed: &ParseResult, owner: NodeRef, name: &str) -> Property {
    let declaration = property_node(parsed, owner, name);
    let annotation = match &parsed.arena.get(declaration.node).unwrap().data {
        NodeData::PropertyDeclaration(property) => property.type_.unwrap(),
        NodeData::PropertySignatureDeclaration(property) => property.type_,
        _ => panic!("expected the written property annotation"),
    };
    Property {
        declaration,
        annotation: NodeRef::new(owner.arena, owner.file, annotation),
    }
}

fn arrow(parsed: &ParseResult, declaration: NodeRef) -> Arrow {
    let node_ref = |node| NodeRef::new(parsed.arena.id(), SOURCE, node);
    let record = parsed.arena.get(declaration.node).unwrap();
    let NodeData::ArrowFunction(arrow) = &record.data else {
        panic!("expected a source arrow")
    };
    let NodeData::Block(body) = &parsed.arena.get(arrow.body).unwrap().data else {
        panic!("all four original arrows have block bodies")
    };
    let returned = body.statements.nodes.last().and_then(|&node| {
        let NodeData::ReturnStatement(returned) = &parsed.arena.get(node)?.data else {
            return None;
        };
        returned.expression.map(node_ref)
    });
    Arrow {
        declaration,
        binding: node_ref(record.parent.unwrap()),
        annotation: arrow.type_.map(node_ref),
        type_parameters: arrow
            .type_parameters
            .as_ref()
            .into_iter()
            .flat_map(|parameters| parameters.nodes.iter().copied())
            .map(node_ref)
            .collect(),
        parameters: arrow
            .parameters
            .nodes
            .iter()
            .copied()
            .map(node_ref)
            .collect(),
        returned,
    }
}

fn local_arrow(parsed: &ParseResult, expected: &str) -> Arrow {
    let declaration = parsed
        .arena
        .iter()
        .find_map(|(_, record)| {
            let NodeData::VariableDeclaration(variable) = &record.data else {
                return None;
            };
            let NodeData::Identifier(name) = &parsed.arena.get(variable.name)?.data else {
                return None;
            };
            (name.text == expected).then_some(NodeRef::new(
                parsed.arena.id(),
                SOURCE,
                variable.initializer.unwrap(),
            ))
        })
        .unwrap();
    arrow(parsed, declaration)
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

fn value_type(context: &CanonicalCheckerContext<'_>, owner: SemanticSymbolId) -> TypeId {
    context
        .store()
        .value_symbol_links(owner)
        .and_then(|links| links.resolved_type)
        .unwrap()
}

fn object<'store>(
    context: &'store CanonicalCheckerContext<'_>,
    type_: TypeId,
) -> &'store ObjectTypeData {
    let TypeData::Object(object) = context.store().type_payload(type_).unwrap().data() else {
        panic!("expected a canonical object")
    };
    object
}

fn constituents(context: &CanonicalCheckerContext<'_>, type_: TypeId) -> [TypeId; 2] {
    let TypeData::Intersection(intersection) = context.store().type_payload(type_).unwrap().data()
    else {
        panic!("Subject must keep its original intersection")
    };
    intersection
        .intersection
        .types
        .as_slice()
        .try_into()
        .unwrap()
}

fn member(context: &CanonicalCheckerContext<'_>, type_: TypeId, name: &str) -> SemanticSymbolId {
    context
        .store()
        .symbol_table(object(context, type_).structured.members.unwrap())
        .unwrap()
        .get_source(name)
        .unwrap()
}

fn signature(context: &CanonicalCheckerContext<'_>, type_: TypeId) -> SignatureId {
    let object = object(context, type_);
    assert_eq!(object.structured.call_signature_count, 1);
    let [signature] = object.structured.signatures.as_deref().unwrap() else {
        panic!("expected one canonical call signature")
    };
    *signature
}

fn parameter(context: &CanonicalCheckerContext<'_>, declaration: NodeRef) -> TypeId {
    let owner = symbol(context, declaration);
    let type_ = context
        .store()
        .declared_type_links(owner)
        .unwrap()
        .declared_type
        .unwrap();
    let record = context.store().type_payload(type_).unwrap();
    assert_eq!(record.symbol(), Some(owner));
    let TypeData::TypeParameter(parameter) = record.data() else {
        panic!("the type parameter must retain its source owner")
    };
    assert_eq!(parameter.target, None);
    assert_eq!(parameter.mapper, None);
    type_
}

fn assert_alias(
    context: &CanonicalCheckerContext<'_>,
    type_: TypeId,
    owner: SemanticSymbolId,
    arguments: Option<&[TypeId]>,
) {
    let alias = context
        .store()
        .type_payload(type_)
        .unwrap()
        .alias()
        .and_then(|alias| context.store().type_alias(alias))
        .unwrap();
    assert_eq!(alias.symbol(), Some(owner));
    assert_eq!(alias.type_arguments(), arguments);
}

fn declared_alias(context: &CanonicalCheckerContext<'_>, alias: Alias) -> TypeId {
    let owner = symbol(context, alias.declaration);
    let links = context.store().type_alias_links(owner).unwrap();
    let type_ = links.declared_type.unwrap();
    let arguments = alias.parameter.map(|node| [parameter(context, node)]);
    let arguments = arguments.as_ref().map(<[TypeId; 1]>::as_slice);
    assert_eq!(links.type_parameters.as_deref(), arguments);
    if arguments.is_none() {
        assert!(links.instantiations.is_none());
    }
    assert_alias(context, type_, owner, arguments);
    assert_eq!(node_type(context, alias.body), Some(type_));
    type_
}

#[derive(Debug, Eq, PartialEq)]
struct SubjectIdentity {
    original: TypeId,
    original_inline: TypeId,
    original_observer: TypeId,
    instance: TypeId,
    inline: TypeId,
    observer: TypeId,
    parameter: TypeId,
}

#[allow(clippy::too_many_lines)] // Keep exact original and mapped owner checks together.
fn assert_subject(
    context: &CanonicalCheckerContext<'_>,
    subject: Alias,
    observer: Alias,
    literal: NodeRef,
    factory: &Arrow,
    instance: TypeId,
) -> SubjectIdentity {
    let original = declared_alias(context, subject);
    let original_observer = declared_alias(context, observer);
    let subject_parameter = parameter(context, subject.parameter.unwrap());
    let observer_parameter = parameter(context, observer.parameter.unwrap());
    let [factory_parameter] = factory.type_parameters.as_slice() else {
        panic!("the default factory owns its one type parameter")
    };
    let factory_parameter = parameter(context, *factory_parameter);
    assert_ne!(subject_parameter, observer_parameter);
    assert_ne!(subject_parameter, factory_parameter);
    assert_ne!(observer_parameter, factory_parameter);
    assert_ne!(original, instance);
    assert_alias(
        context,
        instance,
        symbol(context, subject.declaration),
        Some(&[factory_parameter]),
    );
    let [original_inline, inherited] = constituents(context, original);
    let [inline, mapped_observer] = constituents(context, instance);
    assert_eq!(
        context
            .store()
            .type_payload(original_inline)
            .unwrap()
            .symbol(),
        Some(symbol(context, literal))
    );
    assert_eq!(node_type(context, literal), Some(original_inline));
    assert!(
        context
            .store()
            .type_payload(original_inline)
            .unwrap()
            .alias()
            .is_none()
    );
    assert_eq!(object(context, original_inline).target, None);
    assert_eq!(object(context, original_inline).mapper, None);
    assert_eq!(
        context
            .store()
            .type_node_links(literal)
            .unwrap()
            .outer_type_parameters
            .as_deref(),
        Some(&[subject_parameter][..])
    );
    assert_eq!(object(context, inherited).target, Some(original_observer));
    assert_eq!(
        context.store().map_type(
            object(context, inherited).mapper.unwrap(),
            observer_parameter
        ),
        Some(subject_parameter)
    );
    assert_alias(
        context,
        inherited,
        symbol(context, observer.declaration),
        Some(&[subject_parameter]),
    );
    assert_ne!(inline, original_inline);
    assert_eq!(object(context, inline).target, Some(original_inline));
    assert_eq!(
        context.store().type_payload(inline).unwrap().symbol(),
        Some(symbol(context, literal))
    );
    assert!(
        context
            .store()
            .type_payload(inline)
            .unwrap()
            .alias()
            .is_none()
    );
    assert_eq!(
        context
            .store()
            .map_type(object(context, inline).mapper.unwrap(), subject_parameter),
        Some(factory_parameter)
    );
    assert_ne!(mapped_observer, inherited);
    assert_eq!(
        object(context, mapped_observer).target,
        Some(original_observer)
    );
    assert_eq!(
        context.store().map_type(
            object(context, mapped_observer).mapper.unwrap(),
            observer_parameter
        ),
        Some(factory_parameter)
    );
    assert_alias(
        context,
        mapped_observer,
        symbol(context, observer.declaration),
        Some(&[factory_parameter]),
    );
    SubjectIdentity {
        original,
        original_inline,
        original_observer,
        instance,
        inline,
        observer: mapped_observer,
        parameter: factory_parameter,
    }
}

fn assert_source_callable(
    context: &CanonicalCheckerContext<'_>,
    arrow: &Arrow,
    returned: TypeId,
) -> (TypeId, SignatureId) {
    let owner = symbol(context, arrow.declaration);
    let owner_record = context.store().symbol(owner).unwrap();
    assert_eq!(owner_record.flags(), SymbolFlags::FUNCTION);
    assert_eq!(owner_record.declarations(), Some(&[arrow.declaration][..]));
    let type_ = value_type(context, owner);
    let binding = symbol(context, arrow.binding);
    assert_ne!(owner, binding);
    if matches!(
        context
            .file(SOURCE)
            .unwrap()
            .0
            .get(arrow.binding.node)
            .unwrap()
            .data,
        NodeData::PropertyAssignment(_)
    ) {
        assert!(context.store().value_symbol_links(binding).is_none());
    } else {
        assert_eq!(value_type(context, binding), type_);
    }
    assert_eq!(
        context.store().type_payload(type_).unwrap().symbol(),
        Some(owner)
    );
    assert_eq!(object(context, type_).target, None);
    assert_eq!(object(context, type_).mapper, None);
    let signature = signature(context, type_);
    assert_eq!(
        context
            .store()
            .signature_links(arrow.declaration)
            .unwrap()
            .resolved_signature
            .signature(),
        Some(signature)
    );
    let record = context.store().signature(signature).unwrap();
    assert_eq!(record.declaration(), Some(arrow.declaration));
    assert_eq!(
        record.type_parameters(),
        arrow
            .type_parameters
            .iter()
            .map(|&node| parameter(context, node))
            .collect::<Vec<_>>()
    );
    assert_eq!(
        record.parameters(),
        arrow
            .parameters
            .iter()
            .map(|&node| symbol(context, node))
            .collect::<Vec<_>>()
    );
    assert_eq!(record.target(), None);
    assert_eq!(record.mapper(), None);
    assert_eq!(record.resolved_return_type(), Some(returned));
    (type_, signature)
}

fn assert_mapped_callable(
    context: &CanonicalCheckerContext<'_>,
    property: Property,
    receiver: TypeId,
    name: &str,
    source_parameter: TypeId,
    mapped_parameter: TypeId,
    returned: TypeId,
) -> (TypeId, SignatureId) {
    let original = symbol(context, property.declaration);
    let source = value_type(context, original);
    assert_eq!(node_type(context, property.annotation), Some(source));
    let proxy = member(context, receiver, name);
    let substitution = object(context, receiver).mapper.unwrap();
    assert_ne!(proxy, original);
    let links = context.store().value_symbol_links(proxy).unwrap();
    assert_eq!(links.target, Some(original));
    assert_eq!(links.mapper, Some(substitution));
    let mapped = links.resolved_type.unwrap();
    assert_ne!(mapped, source);
    assert_eq!(object(context, mapped).target, Some(source));
    assert_eq!(object(context, mapped).mapper, Some(substitution));
    let source_signature = signature(context, source);
    let mapped_signature = signature(context, mapped);
    let NodeData::FunctionTypeNode(function) = &context
        .file(SOURCE)
        .unwrap()
        .0
        .get(property.annotation.node)
        .unwrap()
        .data
    else {
        panic!("the property retains its original function annotation")
    };
    let [source_parameter_node] = function.parameters.nodes.as_slice() else {
        panic!("each original property callable has one value parameter")
    };
    let source_parameter_owner = symbol(
        context,
        NodeRef::new(property.annotation.arena, SOURCE, *source_parameter_node),
    );
    let source_record = context.store().signature(source_signature).unwrap();
    assert_eq!(source_record.declaration(), Some(property.annotation));
    assert_eq!(source_record.target(), None);
    assert_eq!(source_record.mapper(), None);
    assert!(source_record.type_parameters().is_empty());
    assert_eq!(source_record.parameters(), &[source_parameter_owner]);
    assert_eq!(
        value_type(context, source_record.parameters()[0]),
        source_parameter
    );
    assert_eq!(source_record.resolved_return_type(), Some(returned));
    let mapped_record = context.store().signature(mapped_signature).unwrap();
    assert_eq!(mapped_record.declaration(), Some(property.annotation));
    assert_eq!(mapped_record.target(), Some(source_signature));
    assert_eq!(mapped_record.mapper(), Some(substitution));
    assert!(mapped_record.type_parameters().is_empty());
    assert_eq!(mapped_record.parameters().len(), 1);
    assert_ne!(mapped_record.parameters()[0], source_record.parameters()[0]);
    assert_eq!(
        value_type(context, mapped_record.parameters()[0]),
        mapped_parameter
    );
    assert_eq!(mapped_record.resolved_return_type(), Some(returned));
    (mapped, mapped_signature)
}

#[derive(Debug, Eq, PartialEq)]
struct NodeState {
    node: NodeRef,
    type_: Option<TypeNodeLinks>,
    symbol: Option<SymbolNodeLinks>,
    signature: Option<SignatureLinks>,
}

#[derive(Debug, Eq, PartialEq)]
struct SymbolState {
    symbol: SemanticSymbolId,
    value: Option<ValueSymbolLinks>,
    declared: Option<DeclaredTypeLinks>,
    alias: Option<TypeAliasLinks>,
    import: Option<AliasSymbolLinks>,
}

#[derive(Debug, Eq, PartialEq)]
enum StructuredState {
    Object(ObjectTypeData),
    Intersection(IntersectionTypeData),
}

#[derive(Debug, Eq, PartialEq)]
struct TypeState {
    type_: TypeId,
    owner: Option<SemanticSymbolId>,
    alias: Option<TypeAliasId>,
    alias_owner: Option<SemanticSymbolId>,
    alias_arguments: Option<Vec<TypeId>>,
    structure: StructuredState,
}

#[derive(Debug, Eq, PartialEq)]
struct SignatureState {
    id: SignatureId,
    declaration: Option<NodeRef>,
    type_parameters: Vec<TypeId>,
    parameters: Vec<SemanticSymbolId>,
    return_type: Option<TypeId>,
    target: Option<SignatureId>,
    mapper: Option<TypeMapperId>,
}

#[derive(Debug, Eq, PartialEq)]
struct Snapshot {
    counts: [usize; 7],
    sources: [Option<SourceFileLinks>; 3],
    nodes: Vec<NodeState>,
    symbols: Vec<SymbolState>,
    types: Vec<TypeState>,
    signatures: Vec<SignatureState>,
    diagnostics: CanonicalCheckerDiagnostics,
}

fn snapshot(context: &CanonicalCheckerContext<'_>) -> Snapshot {
    let store = context.store();
    Snapshot {
        counts: [
            store.type_len(),
            store.symbol_len(),
            store.signature_len(),
            store.mapper_len(),
            store.type_alias_len(),
            store.index_info_len(),
            store.symbol_store().symbol_table_len(),
        ],
        sources: [SOURCE, BARREL, PROVIDER].map(|file| {
            store
                .source_file_links(context.source_file(file).unwrap())
                .cloned()
        }),
        nodes: [SOURCE, BARREL, PROVIDER]
            .into_iter()
            .flat_map(|file| {
                let arena = context.file(file).unwrap().0;
                arena.iter().map(move |(node, _)| {
                    let node = NodeRef::new(arena.id(), file, node);
                    NodeState {
                        node,
                        type_: store.type_node_links(node).cloned(),
                        symbol: store.symbol_node_links(node).cloned(),
                        signature: store.signature_links(node).cloned(),
                    }
                })
            })
            .collect(),
        symbols: store
            .symbol_store()
            .symbols()
            .map(|(symbol, _)| SymbolState {
                symbol,
                value: store.value_symbol_links(symbol).cloned(),
                declared: store.declared_type_links(symbol).cloned(),
                alias: store.type_alias_links(symbol).cloned(),
                import: store.alias_symbol_links(symbol).cloned(),
            })
            .collect(),
        types: store
            .types()
            .filter_map(|(type_, record)| {
                let structure = match record.data() {
                    TypeData::Object(object) => StructuredState::Object(object.clone()),
                    TypeData::Intersection(intersection) => {
                        StructuredState::Intersection(intersection.clone())
                    }
                    _ => return None,
                };
                let alias = record.alias().and_then(|alias| store.type_alias(alias));
                Some(TypeState {
                    type_,
                    owner: record.symbol(),
                    alias: record.alias(),
                    alias_owner: alias
                        .and_then(ts_checker::semantic::type_records::TypeAlias::symbol),
                    alias_arguments: alias
                        .and_then(|alias| alias.type_arguments().map(<[TypeId]>::to_vec)),
                    structure,
                })
            })
            .collect(),
        signatures: store
            .signatures()
            .map(|(id, signature)| SignatureState {
                id,
                declaration: signature.declaration(),
                type_parameters: signature.type_parameters().to_vec(),
                parameters: signature.parameters().to_vec(),
                return_type: signature.resolved_return_type(),
                target: signature.target(),
                mapper: signature.mapper(),
            })
            .collect(),
        diagnostics: context.diagnostics().clone(),
    }
}

fn assert_type_only_import(context: &CanonicalCheckerContext<'_>, binding: NodeRef, noop: Alias) {
    let imported = symbol(context, binding);
    let target = symbol(context, noop.declaration);
    let links = context.store().alias_symbol_links(imported).unwrap();
    assert_eq!(links.immediate_target, Some(target));
    assert_eq!(links.alias_target, AliasTargetState::Resolved(target));
    assert_eq!(links.type_only_declaration, Some(binding));
    assert!(context.store().value_symbol_links(imported).is_none());
    assert!(context.store().value_symbol_links(target).is_none());
    for file in [BARREL, PROVIDER] {
        assert!(
            context
                .store()
                .source_file_links(context.source_file(file).unwrap())
                .is_none_or(|links| !links.type_checked)
        );
    }
}

#[allow(clippy::too_many_lines)] // Keep both query orders on the exact same source and identity checks.
fn check_subject(query_first: bool) {
    let source = parse_source_file(SOURCE_TEXT);
    let barrel = parse_source_file(BARREL_TEXT);
    let provider = parse_source_file(PROVIDER_TEXT);
    let mut context = context(&source, &barrel, &provider);
    let node_ref = |node| NodeRef::new(source.arena.id(), SOURCE, node);
    let subscription = alias(&source, SOURCE, "Subscription");
    let observer = alias(&source, SOURCE, "Observer");
    let subject = alias(&source, SOURCE, "Subject");
    let noop = alias(&provider, PROVIDER, "Noop");
    let NodeData::IntersectionTypeNode(intersection) =
        &source.arena.get(subject.body.node).unwrap().data
    else {
        unreachable!()
    };
    let inline = node_ref(intersection.types.nodes[0]);
    let unsubscribe_property = property(&source, subscription.body, "unsubscribe");
    let next_property = property(&source, observer.body, "next");
    let subscribe_property = property(&source, inline, "subscribe");
    let exported = source
        .arena
        .iter()
        .find_map(|(_, record)| {
            let NodeData::ExportAssignment(export) = &record.data else {
                return None;
            };
            assert!(!export.is_export_equals);
            Some(node_ref(export.expression))
        })
        .unwrap();
    let factory = arrow(&source, exported);
    let next = local_arrow(&source, "next");
    let subscribe = local_arrow(&source, "subscribe");
    let subscription_object = subscribe.returned.unwrap();
    let unsubscribe_assignment = property_node(&source, subscription_object, "unsubscribe");
    let NodeData::PropertyAssignment(assignment) =
        &source.arena.get(unsubscribe_assignment.node).unwrap().data
    else {
        unreachable!()
    };
    let unsubscribe = arrow(&source, node_ref(assignment.initializer));
    let binding = source
        .arena
        .iter()
        .find_map(|(node, record)| {
            matches!(record.data, NodeData::ImportSpecifier(_)).then_some(node_ref(node))
        })
        .unwrap();
    let annotation = factory.annotation.unwrap();

    let early = if query_first {
        // This written annotation is the first semantic query. It must not check the file.
        let instance = context.get_type_from_type_node(annotation).unwrap();
        let identity = assert_subject(&context, subject, observer, inline, &factory, instance);
        for file in [SOURCE, BARREL, PROVIDER] {
            assert!(
                context
                    .store()
                    .source_file_links(context.source_file(file).unwrap())
                    .is_none_or(|links| !links.type_checked)
            );
        }
        for type_ in [
            identity.original_inline,
            identity.original_observer,
            identity.inline,
            identity.observer,
        ] {
            assert!(object(&context, type_).structured.members.is_none());
            assert!(object(&context, type_).structured.properties.is_none());
        }
        for property in [unsubscribe_property, next_property, subscribe_property] {
            assert!(node_type(&context, property.annotation).is_none());
            assert!(
                context
                    .store()
                    .value_symbol_links(symbol(&context, property.declaration))
                    .is_none()
            );
        }
        Some(identity)
    } else {
        None
    };

    context.check_source_file(SOURCE).unwrap();
    assert!(
        context.diagnostics().is_empty(),
        "{:?}",
        context.diagnostics()
    );
    assert!(
        context
            .store()
            .source_file_links(context.source_file(SOURCE).unwrap())
            .unwrap()
            .type_checked
    );
    let factory_type = value_type(&context, symbol(&context, factory.declaration));
    let factory_signature = signature(&context, factory_type);
    let instance = context
        .store()
        .signature(factory_signature)
        .unwrap()
        .resolved_return_type()
        .unwrap();
    let identity = assert_subject(&context, subject, observer, inline, &factory, instance);
    if let Some(early) = early {
        assert_eq!(identity, early);
    }
    assert_eq!(node_type(&context, annotation), Some(instance));
    let subscription_type = declared_alias(&context, subscription);
    let noop_type = declared_alias(&context, noop);
    let void = context.store().intrinsic_bootstrap().unwrap().void_type;
    assert_eq!(
        context
            .store()
            .type_payload(subscription_type)
            .unwrap()
            .symbol(),
        Some(symbol(&context, subscription.body))
    );
    assert_eq!(object(&context, subscription_type).target, None);
    assert_eq!(object(&context, subscription_type).mapper, None);
    assert_eq!(
        context.store().type_payload(noop_type).unwrap().symbol(),
        Some(symbol(&context, noop.body))
    );
    assert_eq!(object(&context, noop_type).target, None);
    assert_eq!(object(&context, noop_type).mapper, None);
    let noop_signature = signature(&context, noop_type);
    let noop_record = context.store().signature(noop_signature).unwrap();
    assert_eq!(noop_record.declaration(), Some(noop.body));
    assert!(noop_record.type_parameters().is_empty());
    assert!(noop_record.parameters().is_empty());
    assert_eq!(noop_record.target(), None);
    assert_eq!(noop_record.mapper(), None);
    assert_eq!(noop_record.resolved_return_type(), Some(void));
    assert_eq!(
        node_type(&context, unsubscribe_property.annotation),
        Some(noop_type)
    );
    assert_eq!(
        value_type(&context, symbol(&context, unsubscribe_property.declaration)),
        noop_type
    );
    assert_eq!(
        context
            .store()
            .symbol_node_links(unsubscribe_property.annotation)
            .unwrap()
            .resolved_symbol,
        Some(symbol(&context, noop.declaration))
    );
    assert_type_only_import(&context, binding, noop);

    assert_eq!(
        assert_source_callable(&context, &factory, instance),
        (factory_type, factory_signature)
    );
    let (next_type, next_signature) = assert_source_callable(&context, &next, void);
    let (subscribe_type, subscribe_signature) =
        assert_source_callable(&context, &subscribe, subscription_type);
    let (unsubscribe_type, unsubscribe_signature) =
        assert_source_callable(&context, &unsubscribe, void);
    assert!(factory.parameters.is_empty());
    assert_eq!(next.parameters.len(), 1);
    assert_eq!(subscribe.parameters.len(), 1);
    assert!(unsubscribe.parameters.is_empty());
    assert_eq!(
        value_type(&context, symbol(&context, next.parameters[0])),
        identity.parameter
    );
    assert_eq!(
        value_type(&context, symbol(&context, subscribe.parameters[0])),
        identity.observer
    );
    assert_eq!(
        node_type(&context, subscribe.annotation.unwrap()),
        Some(subscription_type)
    );
    let (mapped_subscribe, mapped_subscribe_signature) = assert_mapped_callable(
        &context,
        subscribe_property,
        identity.inline,
        "subscribe",
        constituents(&context, identity.original)[1],
        identity.observer,
        subscription_type,
    );
    let (mapped_next, mapped_next_signature) = assert_mapped_callable(
        &context,
        next_property,
        identity.observer,
        "next",
        parameter(&context, observer.parameter.unwrap()),
        identity.parameter,
        void,
    );
    let subject_object = factory.returned.unwrap();
    let subject_object_type = node_type(&context, subject_object).unwrap();
    let subscription_object_type = node_type(&context, subscription_object).unwrap();
    assert_ne!(subject_object_type, instance);
    assert_ne!(subscription_object_type, subscription_type);
    for (literal, type_, name, expected) in [
        (subject_object, subject_object_type, "next", next_type),
        (
            subject_object,
            subject_object_type,
            "subscribe",
            subscribe_type,
        ),
        (
            subscription_object,
            subscription_object_type,
            "unsubscribe",
            unsubscribe_type,
        ),
    ] {
        let declaration = property_node(&source, literal, name);
        let original = symbol(&context, declaration);
        let proxy = member(&context, type_, name);
        assert_ne!(proxy, original);
        let record = context.store().symbol(proxy).unwrap();
        assert_eq!(
            record.flags(),
            SymbolFlags::PROPERTY | SymbolFlags::TRANSIENT
        );
        assert_eq!(record.declarations(), Some(&[declaration][..]));
        let links = context.store().value_symbol_links(proxy).unwrap();
        assert_eq!(links.target, Some(original));
        assert_eq!(links.resolved_type, Some(expected));
    }

    let annotations = [
        (annotation, instance),
        (subject.body, identity.original),
        (observer.body, identity.original_observer),
        (subscription.body, subscription_type),
        (noop.body, noop_type),
        (unsubscribe_property.annotation, noop_type),
        (subscribe.annotation.unwrap(), subscription_type),
    ];
    let locations = [
        (factory.declaration, factory_type),
        (next.declaration, next_type),
        (subscribe.declaration, subscribe_type),
        (unsubscribe.declaration, unsubscribe_type),
        (subject_object, subject_object_type),
        (subscription_object, subscription_object_type),
    ];
    let returns = [
        (factory_signature, instance),
        (next_signature, void),
        (subscribe_signature, subscription_type),
        (unsubscribe_signature, void),
        (mapped_subscribe_signature, subscription_type),
        (mapped_next_signature, void),
        (noop_signature, void),
    ];
    let relations = [
        (subject_object_type, instance),
        (subscription_object_type, subscription_type),
        (subscribe_type, mapped_subscribe),
        (next_type, mapped_next),
        (unsubscribe_type, noop_type),
    ];
    for (actual, expected) in relations {
        assert_eq!(context.is_type_assignable_to(actual, expected), Ok(true));
    }
    for (node, expected) in locations {
        assert_eq!(context.get_type_at_location(node), Ok(expected));
    }
    for (node, expected) in annotations {
        assert_eq!(context.get_type_from_type_node(node), Ok(expected));
    }
    for (signature, expected) in returns {
        assert_eq!(
            context.get_return_type_of_signature(signature),
            Ok(expected)
        );
    }
    let before = snapshot(&context);
    context.check_source_file(SOURCE).unwrap();
    assert_eq!(snapshot(&context), before);
    context.recheck_source_file(SOURCE).unwrap();
    assert_eq!(snapshot(&context), before);
    for (node, expected) in locations {
        assert_eq!(context.get_type_at_location(node), Ok(expected));
    }
    for (node, expected) in annotations {
        assert_eq!(context.get_type_from_type_node(node), Ok(expected));
    }
    for (signature, expected) in returns {
        assert_eq!(
            context.get_return_type_of_signature(signature),
            Ok(expected)
        );
    }
    for (actual, expected) in relations {
        assert_eq!(context.is_type_assignable_to(actual, expected), Ok(true));
    }
    for (alias, expected) in [
        (subject, identity.original),
        (observer, identity.original_observer),
        (subscription, subscription_type),
        (noop, noop_type),
    ] {
        assert_eq!(
            context.get_declared_type_of_symbol(symbol(&context, alias.declaration)),
            Ok(expected)
        );
    }
    assert_eq!(
        assert_subject(&context, subject, observer, inline, &factory, instance),
        identity
    );
    assert_type_only_import(&context, binding, noop);
    assert_eq!(snapshot(&context), before);
    assert!(context.diagnostics().is_empty());
}

#[test]
fn exported_alias_return_in_subject_intersection_checks_source_first() {
    check_subject(false);
}

#[test]
fn exported_alias_return_in_subject_intersection_checks_query_first() {
    check_subject(true);
}
