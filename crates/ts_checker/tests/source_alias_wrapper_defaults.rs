use ts_ast::{FileId, NodeData, NodeRef};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    CheckFlags, EscapedName, SemanticSymbolId, SymbolFlags,
};
use ts_checker::semantic::{
    AliasSymbolLinks, AliasTargetState, CanonicalCheckerContext, CanonicalCheckerDiagnostics,
    CanonicalCheckerOptions, CanonicalModuleResolutionEntry,
    CanonicalModuleResolutionManifestInput, CanonicalModuleResolutionMode,
    CanonicalResolvedModuleInput, ConditionalRootId, DeclaredTypeLinks, IntrinsicBootstrapOptions,
    MembersAndExportsLinks, SourceFileLinks, SymbolNodeLinks, TypeAliasId, TypeAliasLinks,
    TypeData, TypeId, TypeNodeLinks, ValueSymbolLinks,
    type_records::{
        CacheHashKey, ConditionalTypeData, InterfaceTypeData, ObjectTypeData, TupleTypeData,
        TypeCacheState, TypeParameterData, TypeReferenceData,
    },
    types::{ObjectFlags, TypeFlags},
};
use ts_parser::{ParseResult, parse_source_file};

const LIBRARY: FileId = FileId::new(46_240);
const SOURCE: FileId = FileId::new(46_241);
const PROVIDER: FileId = FileId::new(46_242);

// Keep these inputs equal to the retained imported-alias-body control.
const LIBRARY_TEXT: &str = "interface Array<T> {} interface ReadonlyArray<T> {}";
const IMPORTED_PROVIDER_TEXT: &str = concat!(
    "export type Box<Value> = { value: Value };\n",
    "export type Bound<Value extends string = string> = { value: Value };\n",
);
const IMPORTED_SOURCE_TEXT: &str = concat!(
    "import type { Box, Bound } from './provider';\n",
    "export type Direct<T> = Box<T>;\n",
    "export type Check<T> = Box<T> extends unknown ? T : never;\n",
    "export type Captured<T> = T extends infer Local ? Box<Local> : Box<T>;\n",
    "export type Constrained<T extends string> = Bound<T>;\n",
    "export type Defaulted = Bound;\n",
);

fn context<'arena>(
    files: &[(FileId, &'arena ParseResult, &str, CanonicalModuleState)],
    resolutions: &[(NodeRef, FileId)],
) -> CanonicalCheckerContext<'arena> {
    let mut binder = CanonicalBinder::new();
    for &(file, parsed, path, module) in files {
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
                    module,
                ),
            )
            .unwrap();
    }
    for &(file, parsed, _, _) in files {
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
    }
    CanonicalCheckerContext::new_with_module_resolutions(
        binder.finish(),
        files
            .iter()
            .map(|&(file, parsed, _, _)| (file, &parsed.arena))
            .collect(),
        CanonicalCheckerOptions {
            intrinsic: IntrinsicBootstrapOptions {
                strict_null_checks: true,
                exact_optional_property_types: false,
            },
            ..CanonicalCheckerOptions::default()
        },
        CanonicalModuleResolutionManifestInput::new(resolutions.iter().map(
            |&(specifier, target)| {
                CanonicalModuleResolutionEntry::resolved(
                    specifier,
                    CanonicalResolvedModuleInput::new(
                        target,
                        CanonicalModuleResolutionMode::Esm,
                        CanonicalModuleResolutionMode::Esm,
                    ),
                )
            },
        )),
    )
    .unwrap()
}

fn local_context<'arena>(
    provider: &'arena ParseResult,
    source: &'arena ParseResult,
) -> CanonicalCheckerContext<'arena> {
    context(
        &[
            (
                PROVIDER,
                provider,
                "\"/project/provider.ts\"",
                CanonicalModuleState::Script,
            ),
            (
                SOURCE,
                source,
                "\"/project/source.ts\"",
                CanonicalModuleState::Script,
            ),
        ],
        &[],
    )
}

struct Alias {
    declaration: NodeRef,
    body: NodeRef,
    parameters: Vec<NodeRef>,
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
            (name.text == expected).then(|| Alias {
                declaration: NodeRef::new(parsed.arena.id(), file, node),
                body: NodeRef::new(parsed.arena.id(), file, alias.type_),
                parameters: alias
                    .type_parameters
                    .iter()
                    .flat_map(|parameters| &parameters.nodes)
                    .map(|node| NodeRef::new(parsed.arena.id(), file, *node))
                    .collect(),
            })
        })
        .unwrap_or_else(|| panic!("missing alias {expected}"))
}

#[derive(Clone, Copy)]
struct Property {
    declaration: NodeRef,
    annotation: NodeRef,
}

fn property(parsed: &ParseResult, owner: &Alias, expected: &str) -> Property {
    let NodeData::TypeLiteralNode(literal) = &parsed.arena.get(owner.body.node).unwrap().data
    else {
        panic!("the provider has an actual object type literal");
    };
    literal
        .members
        .nodes
        .iter()
        .find_map(|node| {
            let (name, annotation) = match &parsed.arena.get(*node)?.data {
                NodeData::PropertyDeclaration(property) => (property.name, property.type_?),
                NodeData::PropertySignatureDeclaration(property) => (property.name, property.type_),
                _ => return None,
            };
            let NodeData::Identifier(name) = &parsed.arena.get(name)?.data else {
                return None;
            };
            (name.text == expected).then_some(Property {
                declaration: NodeRef::new(parsed.arena.id(), owner.body.file, *node),
                annotation: NodeRef::new(parsed.arena.id(), owner.body.file, annotation),
            })
        })
        .unwrap_or_else(|| panic!("missing property {expected}"))
}

fn variable(parsed: &ParseResult, expected: &str) -> (NodeRef, Option<NodeRef>) {
    parsed
        .arena
        .iter()
        .find_map(|(_, record)| {
            let NodeData::VariableDeclaration(variable) = &record.data else {
                return None;
            };
            let NodeData::Identifier(name) = &parsed.arena.get(variable.name)?.data else {
                return None;
            };
            (name.text == expected).then(|| {
                (
                    NodeRef::new(parsed.arena.id(), SOURCE, variable.type_.unwrap()),
                    variable
                        .initializer
                        .map(|node| NodeRef::new(parsed.arena.id(), SOURCE, node)),
                )
            })
        })
        .unwrap_or_else(|| panic!("missing variable {expected}"))
}

fn reference_argument(parsed: &ParseResult, node: NodeRef) -> NodeRef {
    let NodeData::TypeReferenceNode(reference) = &parsed.arena.get(node.node).unwrap().data else {
        panic!("the request has a written type reference");
    };
    let [argument] = reference.type_arguments.as_ref().unwrap().nodes.as_slice() else {
        panic!("the reference has one written argument");
    };
    NodeRef::new(parsed.arena.id(), node.file, *argument)
}

fn symbol(context: &CanonicalCheckerContext<'_>, node: NodeRef) -> SemanticSymbolId {
    let bound = context.file(node.file).unwrap().1;
    context
        .store()
        .get_merged_symbol(bound.symbol(node).unwrap())
        .unwrap()
}

fn parameter(context: &CanonicalCheckerContext<'_>, declaration: NodeRef) -> TypeId {
    let owner = symbol(context, declaration);
    let type_ = context
        .store()
        .declared_type_links(owner)
        .and_then(|links| links.declared_type)
        .unwrap();
    assert_eq!(
        context.store().type_payload(type_).unwrap().symbol(),
        Some(owner)
    );
    type_
}

fn node_type(context: &CanonicalCheckerContext<'_>, node: NodeRef) -> Option<TypeId> {
    context
        .store()
        .type_node_links(node)
        .and_then(|links| links.resolved_type)
}

fn object<'context>(
    context: &'context CanonicalCheckerContext<'_>,
    type_: TypeId,
) -> &'context ObjectTypeData {
    let TypeData::Object(object) = context.store().type_payload(type_).unwrap().data() else {
        panic!("the alias keeps its anonymous object identity");
    };
    object
}

fn cache_key(arguments: &[TypeId], identity: Option<(u64, &[TypeId])>) -> CacheHashKey {
    let mut hasher = xxhash_rust::xxh3::Xxh3::new();
    let write_list = |hasher: &mut xxhash_rust::xxh3::Xxh3, types: &[TypeId]| {
        hasher.update(&u64::try_from(types.len()).unwrap().to_le_bytes());
        for type_ in types {
            hasher.update(&type_.get().to_le_bytes());
        }
    };
    write_list(&mut hasher, arguments);
    if let Some((owner, visible_arguments)) = identity {
        hasher.update(&[1]);
        hasher.update(&owner.to_le_bytes());
        write_list(&mut hasher, visible_arguments);
    } else {
        hasher.update(&[0]);
    }
    CacheHashKey::new(hasher.digest128())
}

fn visible_id(context: &CanonicalCheckerContext<'_>, declaration: NodeRef) -> u64 {
    context
        .store()
        .symbol_store()
        .assigned_global_symbol_id(symbol(context, declaration))
        .unwrap()
}

fn assert_request(
    context: &CanonicalCheckerContext<'_>,
    provider: &Alias,
    supplied: &[TypeId],
    visible: Option<(&Alias, &[TypeId])>,
    expected: TypeId,
) {
    let identity =
        visible.map(|(alias, arguments)| (visible_id(context, alias.declaration), arguments));
    assert_eq!(
        context
            .store()
            .type_alias_links(symbol(context, provider.declaration))
            .unwrap()
            .instantiations
            .as_ref()
            .unwrap()
            .get(&cache_key(supplied, identity)),
        Some(&expected)
    );
}

fn assert_instance(
    context: &CanonicalCheckerContext<'_>,
    provider: &Alias,
    visible: &Alias,
    instance: TypeId,
    physical_arguments: &[TypeId],
    visible_arguments: Option<&[TypeId]>,
) -> TypeId {
    let store = context.store();
    let provider_owner = symbol(context, provider.declaration);
    let visible_owner = symbol(context, visible.declaration);
    let source_owner = symbol(context, provider.body);
    assert_ne!(provider_owner, source_owner);
    let links = store.type_alias_links(provider_owner).unwrap();
    let target = links.declared_type.unwrap();
    let parameters = links.type_parameters.as_deref().unwrap();
    assert_eq!(parameters.len(), provider.parameters.len());
    assert_eq!(parameters.len(), physical_arguments.len());
    let record = store.type_payload(instance).unwrap();
    assert_eq!(record.symbol(), Some(source_owner));
    assert!(
        record
            .object_flags()
            .contains(ObjectFlags::ANONYMOUS | ObjectFlags::INSTANTIATED)
    );
    assert!(
        !record
            .object_flags()
            .intersects(ObjectFlags::CLASS | ObjectFlags::INTERFACE | ObjectFlags::REFERENCE)
    );
    let metadata = store.type_alias(record.alias().unwrap()).unwrap();
    assert_eq!(metadata.symbol(), Some(visible_owner));
    assert_eq!(metadata.type_arguments(), visible_arguments);
    let data = object(context, instance);
    assert_eq!(data.target, Some(target));
    for ((parameter_, declaration), argument) in parameters
        .iter()
        .zip(&provider.parameters)
        .zip(physical_arguments)
    {
        assert_eq!(parameter(context, *declaration), *parameter_);
        assert_eq!(
            store.map_type(data.mapper.unwrap(), *parameter_),
            Some(*argument)
        );
    }
    let target_record = store.type_payload(target).unwrap();
    assert_eq!(target_record.symbol(), Some(source_owner));
    let target_metadata = store.type_alias(target_record.alias().unwrap()).unwrap();
    assert_eq!(target_metadata.symbol(), Some(provider_owner));
    assert_eq!(target_metadata.type_arguments(), Some(parameters));
    assert_eq!(object(context, target).target, None);
    assert_eq!(object(context, target).mapper, None);
    assert_eq!(node_type(context, provider.body), Some(target));
    let TypeCacheState::Allocated(instantiations) = &object(context, target).instantiations else {
        panic!("the original object owns its physical instances");
    };
    assert_eq!(
        instantiations.get(&cache_key(
            physical_arguments,
            Some((
                visible_id(context, visible.declaration),
                visible_arguments.unwrap_or(&[])
            ))
        )),
        Some(&instance)
    );
    target
}

fn assert_cold_property(context: &CanonicalCheckerContext<'_>, property: Property) {
    assert_eq!(
        context
            .store()
            .value_symbol_links(symbol(context, property.declaration))
            .and_then(|links| links.resolved_type),
        None
    );
    assert_eq!(node_type(context, property.annotation), None);
}

fn assert_parameter_property(
    context: &CanonicalCheckerContext<'_>,
    property: Property,
    declaration: NodeRef,
) {
    let type_ = parameter(context, declaration);
    assert_eq!(
        context.store().type_payload(type_).unwrap().flags(),
        TypeFlags::TYPE_PARAMETER
    );
    assert_eq!(
        context
            .store()
            .value_symbol_links(symbol(context, property.declaration)),
        Some(&ValueSymbolLinks {
            resolved_type: Some(type_),
            ..ValueSymbolLinks::default()
        })
    );
    assert_eq!(node_type(context, property.annotation), Some(type_));
    assert_eq!(
        context
            .store()
            .symbol_node_links(property.annotation)
            .and_then(|links| links.resolved_symbol),
        Some(symbol(context, declaration))
    );
}

fn assert_unchecked(context: &CanonicalCheckerContext<'_>, file: FileId) {
    assert!(
        context
            .store()
            .source_file_links(context.source_file(file).unwrap())
            .is_none_or(|links| !links.type_checked)
    );
}

fn assert_read(
    context: &mut CanonicalCheckerContext<'_>,
    source: &ParseResult,
    variable_name: &str,
    receiver: TypeId,
    original: Property,
    expected: TypeId,
) -> NodeRef {
    let read = variable(source, variable_name).1.unwrap();
    let NodeData::PropertyAccessExpression(access) = &source.arena.get(read.node).unwrap().data
    else {
        panic!("the source reads a real property");
    };
    let NodeData::Identifier(name) = &source.arena.get(access.name).unwrap().data else {
        unreachable!();
    };
    let store = context.store();
    let members = object(context, receiver).structured.members.unwrap();
    let copied = store
        .symbol_table(members)
        .unwrap()
        .get_source(&name.text)
        .unwrap();
    let raw = symbol(context, original.declaration);
    assert_ne!(copied, raw);
    let source_symbol = store.symbol(raw).unwrap();
    let copied_symbol = store.symbol(copied).unwrap();
    assert!(copied_symbol.flags().contains(SymbolFlags::TRANSIENT));
    assert!(
        copied_symbol
            .check_flags()
            .contains(CheckFlags::INSTANTIATED)
    );
    assert_eq!(copied_symbol.declarations(), source_symbol.declarations());
    assert_eq!(
        copied_symbol.value_declaration(),
        source_symbol.value_declaration()
    );
    assert_eq!(copied_symbol.parent(), source_symbol.parent());
    let links = store.value_symbol_links(copied).unwrap();
    assert_eq!(links.target, Some(raw));
    assert_eq!(links.mapper, object(context, receiver).mapper);
    assert_eq!(links.resolved_type, Some(expected));
    assert_eq!(node_type(context, read), Some(expected));
    assert_eq!(context.get_type_at_location(read), Ok(expected));
    read
}

#[derive(Debug, Eq, PartialEq)]
struct NodeState {
    node: NodeRef,
    type_: Option<TypeNodeLinks>,
    symbol: Option<SymbolNodeLinks>,
}

#[derive(Debug, Eq, PartialEq)]
struct SymbolState {
    symbol: SemanticSymbolId,
    declared: Option<DeclaredTypeLinks>,
    type_alias: Option<TypeAliasLinks>,
    imported: Option<AliasSymbolLinks>,
    value: Option<ValueSymbolLinks>,
    exports: Option<MembersAndExportsLinks>,
}

#[derive(Debug, Eq, PartialEq)]
enum PayloadState {
    Object(Box<ObjectTypeData>),
    Reference(Box<TypeReferenceData>),
    Interface(Box<InterfaceTypeData>),
    Tuple(Box<TupleTypeData>),
    Parameter(Box<TypeParameterData>),
    Conditional(Box<ConditionalTypeData>),
    Other,
}

#[derive(Debug, Eq, PartialEq)]
struct TypeState {
    type_: TypeId,
    flags: TypeFlags,
    object_flags: ObjectFlags,
    symbol: Option<SemanticSymbolId>,
    alias: Option<TypeAliasId>,
    alias_owner: Option<SemanticSymbolId>,
    alias_arguments: Option<Vec<TypeId>>,
    payload: PayloadState,
}

#[derive(Debug, Eq, PartialEq)]
struct RootState {
    root: ConditionalRootId,
    node: NodeRef,
    check: TypeId,
    extends: TypeId,
    distributive: bool,
    infer: Option<Vec<TypeId>>,
    outer: Option<Vec<TypeId>>,
    instantiations: TypeCacheState,
    alias: Option<TypeAliasId>,
}

#[derive(Debug, Eq, PartialEq)]
struct Snapshot {
    counts: [usize; 8],
    sources: Vec<Option<SourceFileLinks>>,
    nodes: Vec<NodeState>,
    symbols: Vec<SymbolState>,
    types: Vec<TypeState>,
    roots: Vec<RootState>,
    diagnostics: CanonicalCheckerDiagnostics,
}

#[allow(clippy::too_many_lines)] // Compare the public caches used by the same replay.
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
            store.conditional_root_len(),
            store.symbol_store().symbol_table_len(),
        ],
        sources: context
            .file_order()
            .iter()
            .map(|file| {
                store
                    .source_file_links(context.source_file(*file).unwrap())
                    .cloned()
            })
            .collect(),
        nodes: context
            .file_order()
            .iter()
            .flat_map(|file| {
                let arena = context.file(*file).unwrap().0;
                arena.iter().map(move |(node, _)| {
                    let node = NodeRef::new(arena.id(), *file, node);
                    NodeState {
                        node,
                        type_: store.type_node_links(node).cloned(),
                        symbol: store.symbol_node_links(node).cloned(),
                    }
                })
            })
            .collect(),
        symbols: store
            .symbol_store()
            .symbols()
            .map(|(symbol, _)| SymbolState {
                symbol,
                declared: store.declared_type_links(symbol).cloned(),
                type_alias: store.type_alias_links(symbol).cloned(),
                imported: store.alias_symbol_links(symbol).cloned(),
                value: store.value_symbol_links(symbol).cloned(),
                exports: store.members_and_exports_links(symbol).cloned(),
            })
            .collect(),
        types: store
            .types()
            .map(|(type_, record)| {
                let payload = match record.data() {
                    TypeData::Object(data) => PayloadState::Object(Box::new(data.clone())),
                    TypeData::TypeReference(data) => {
                        PayloadState::Reference(Box::new(data.clone()))
                    }
                    TypeData::Interface(data) => PayloadState::Interface(Box::new(data.clone())),
                    TypeData::Tuple(data) => PayloadState::Tuple(Box::new(data.clone())),
                    TypeData::TypeParameter(data) => {
                        PayloadState::Parameter(Box::new(data.clone()))
                    }
                    TypeData::Conditional(data) => {
                        PayloadState::Conditional(Box::new(data.clone()))
                    }
                    _ => PayloadState::Other,
                };
                let alias = record.alias().and_then(|alias| store.type_alias(alias));
                TypeState {
                    type_,
                    flags: record.flags(),
                    object_flags: record.object_flags(),
                    symbol: record.symbol(),
                    alias: record.alias(),
                    alias_owner: alias
                        .and_then(ts_checker::semantic::type_records::TypeAlias::symbol),
                    alias_arguments: alias
                        .and_then(|alias| alias.type_arguments().map(<[TypeId]>::to_vec)),
                    payload,
                }
            })
            .collect(),
        roots: store
            .types()
            .filter_map(|(_, record)| {
                let TypeData::Conditional(conditional) = record.data() else {
                    return None;
                };
                let root = store.conditional_root(conditional.root).unwrap();
                Some(RootState {
                    root: root.id(),
                    node: root.node(),
                    check: root.check_type(),
                    extends: root.extends_type(),
                    distributive: root.is_distributive(),
                    infer: root.infer_type_parameters().map(<[TypeId]>::to_vec),
                    outer: root.outer_type_parameters().map(<[TypeId]>::to_vec),
                    instantiations: root.instantiations().clone(),
                    alias: root.alias(),
                })
            })
            .collect(),
        diagnostics: context.diagnostics().clone(),
    }
}

fn replay(
    context: &mut CanonicalCheckerContext<'_>,
    aliases: &[(&Alias, TypeId)],
    annotations: &[(NodeRef, TypeId)],
    reads: &[(NodeRef, TypeId)],
) {
    let before = snapshot(context);
    for _ in 0..2 {
        for &(alias, expected) in aliases.iter().rev().chain(aliases) {
            let owner = symbol(context, alias.declaration);
            assert_eq!(context.get_declared_type_of_symbol(owner), Ok(expected));
            assert_eq!(context.get_type_from_type_node(alias.body), Ok(expected));
        }
        for &(node, expected) in annotations.iter().rev().chain(annotations) {
            assert_eq!(context.get_type_from_type_node(node), Ok(expected));
        }
        for &(node, expected) in reads {
            assert_eq!(context.get_type_at_location(node), Ok(expected));
        }
        context.check_source_file(SOURCE).unwrap();
        context.recheck_source_file(SOURCE).unwrap();
        assert_eq!(snapshot(context), before);
    }
}

#[test]
fn closed_alias_defaults_keep_visible_identity_and_lazy_properties() {
    let provider = parse_source_file("type Box<T = string> = { value: T; spare: number };");
    let source = parse_source_file(concat!(
        "type Defaulted = Box; type Explicit = Box<string>; ",
        "declare const defaulted: Defaulted; declare const explicit: Explicit; ",
        "const first: string = defaulted.value; const second: string = explicit.value;",
    ));
    let box_ = alias(&provider, PROVIDER, "Box");
    let defaulted = alias(&source, SOURCE, "Defaulted");
    let explicit = alias(&source, SOURCE, "Explicit");
    let value = property(&provider, &box_, "value");
    let spare = property(&provider, &box_, "spare");
    for query_first in [false, true] {
        let mut context = local_context(&provider, &source);
        assert_cold_property(&context, value);
        assert_cold_property(&context, spare);
        if !query_first {
            context.check_source_file(SOURCE).unwrap();
        }
        let omitted = context.get_type_from_type_node(defaulted.body).unwrap();
        let supplied = context.get_type_from_type_node(explicit.body).unwrap();
        let string = context.store().intrinsic_bootstrap().unwrap().string_type;
        assert_ne!(omitted, supplied);
        let target = assert_instance(&context, &box_, &defaulted, omitted, &[string], None);
        assert_eq!(
            assert_instance(&context, &box_, &explicit, supplied, &[string], None),
            target
        );
        assert_request(&context, &box_, &[], Some((&defaulted, &[])), omitted);
        assert_request(&context, &box_, &[string], Some((&explicit, &[])), supplied);
        assert_eq!(
            context
                .store()
                .type_alias_links(symbol(&context, box_.declaration))
                .unwrap()
                .instantiations
                .as_ref()
                .unwrap()
                .get(&cache_key(
                    &[string],
                    Some((visible_id(&context, defaulted.declaration), &[]))
                )),
            None
        );
        if query_first {
            assert_cold_property(&context, value);
        } else {
            assert_parameter_property(&context, value, box_.parameters[0]);
        }
        assert_cold_property(&context, spare);
        assert_unchecked(&context, PROVIDER);
        if query_first {
            assert_unchecked(&context, SOURCE);
            for instance in [omitted, supplied] {
                assert_eq!(object(&context, instance).structured.members, None);
                assert_eq!(object(&context, instance).structured.properties, None);
            }
        }
        context.check_source_file(SOURCE).unwrap();
        assert!(context.diagnostics().is_empty());
        let first = assert_read(&mut context, &source, "first", omitted, value, string);
        let second = assert_read(&mut context, &source, "second", supplied, value, string);
        for instance in [omitted, supplied] {
            let members = object(&context, instance).structured.members.unwrap();
            let spare_copy = context
                .store()
                .symbol_table(members)
                .unwrap()
                .get_source("spare")
                .unwrap();
            assert_eq!(
                context
                    .store()
                    .value_symbol_links(spare_copy)
                    .unwrap()
                    .resolved_type,
                None
            );
        }
        assert_parameter_property(&context, value, box_.parameters[0]);
        assert_cold_property(&context, spare);
        replay(
            &mut context,
            &[(&defaulted, omitted), (&explicit, supplied)],
            &[
                (variable(&source, "defaulted").0, omitted),
                (variable(&source, "explicit").0, supplied),
            ],
            &[(first, string), (second, string)],
        );
        assert_unchecked(&context, PROVIDER);
        assert_parameter_property(&context, value, box_.parameters[0]);
        assert_cold_property(&context, spare);
    }
}

#[test]
#[allow(clippy::too_many_lines)] // Compare written requests with the shared physical instance.
fn partial_alias_defaults_keep_supplied_keys_and_effective_arguments() {
    let provider = parse_source_file("type Pair<L, R = number> = { left: L; right: R };");
    let source = parse_source_file(concat!(
        "type Wrapped<T> = Pair<T>; declare const wrapped: Wrapped<string>; ",
        "declare const omitted: Pair<string>; declare const explicit: Pair<string, number>; ",
        "const left: string = wrapped.left; const right: number = wrapped.right;",
    ));
    let pair = alias(&provider, PROVIDER, "Pair");
    let wrapped = alias(&source, SOURCE, "Wrapped");
    let annotations = ["wrapped", "omitted", "explicit"].map(|name| variable(&source, name).0);
    for query_first in [false, true] {
        let mut context = local_context(&provider, &source);
        for name in ["left", "right"] {
            assert_cold_property(&context, property(&provider, &pair, name));
        }
        if !query_first {
            context.check_source_file(SOURCE).unwrap();
        }
        let [wrapped_type, omitted, explicit] =
            annotations.map(|node| context.get_type_from_type_node(node).unwrap());
        let string = context.store().intrinsic_bootstrap().unwrap().string_type;
        let number = context.store().intrinsic_bootstrap().unwrap().number_type;
        let wrapped_parameter = parameter(&context, wrapped.parameters[0]);
        let declared = context
            .get_declared_type_of_symbol(symbol(&context, wrapped.declaration))
            .unwrap();
        let target = assert_instance(
            &context,
            &pair,
            &wrapped,
            wrapped_type,
            &[string, number],
            Some(&[string]),
        );
        assert_eq!(
            assert_instance(
                &context,
                &pair,
                &wrapped,
                declared,
                &[wrapped_parameter, number],
                Some(&[wrapped_parameter])
            ),
            target
        );
        for instance in [omitted, explicit] {
            assert_eq!(
                assert_instance(
                    &context,
                    &pair,
                    &pair,
                    instance,
                    &[string, number],
                    Some(&[string, number])
                ),
                target
            );
        }
        assert_ne!(wrapped_type, omitted);
        assert_eq!(omitted, explicit);
        assert_ne!(
            cache_key(&[string], None),
            cache_key(&[string, number], None)
        );
        assert_request(&context, &pair, &[string], None, omitted);
        assert_request(&context, &pair, &[string, number], None, explicit);
        assert_request(
            &context,
            &pair,
            &[wrapped_parameter],
            Some((&wrapped, &[wrapped_parameter])),
            declared,
        );
        assert_eq!(
            context
                .store()
                .type_alias_links(symbol(&context, pair.declaration))
                .unwrap()
                .instantiations
                .as_ref()
                .unwrap()
                .get(&cache_key(
                    &[wrapped_parameter, number],
                    Some((
                        visible_id(&context, wrapped.declaration),
                        &[wrapped_parameter]
                    ))
                )),
            None
        );
        assert_request(&context, &wrapped, &[string], None, wrapped_type);
        for (name, parameter) in ["left", "right"].into_iter().zip(&pair.parameters) {
            let property = property(&provider, &pair, name);
            if query_first {
                assert_cold_property(&context, property);
            } else {
                assert_parameter_property(&context, property, *parameter);
            }
        }
        if query_first {
            assert_unchecked(&context, SOURCE);
        }
        assert_unchecked(&context, PROVIDER);
        context.check_source_file(SOURCE).unwrap();
        assert!(context.diagnostics().is_empty());
        let left = assert_read(
            &mut context,
            &source,
            "left",
            wrapped_type,
            property(&provider, &pair, "left"),
            string,
        );
        let right = assert_read(
            &mut context,
            &source,
            "right",
            wrapped_type,
            property(&provider, &pair, "right"),
            number,
        );
        for (name, parameter) in ["left", "right"].into_iter().zip(&pair.parameters) {
            assert_parameter_property(&context, property(&provider, &pair, name), *parameter);
        }
        replay(
            &mut context,
            &[(&wrapped, declared)],
            &[
                (annotations[0], wrapped_type),
                (annotations[1], omitted),
                (annotations[2], explicit),
            ],
            &[(left, string), (right, number)],
        );
        assert_unchecked(&context, PROVIDER);
        for (name, parameter) in ["left", "right"].into_iter().zip(&pair.parameters) {
            assert_parameter_property(&context, property(&provider, &pair, name), *parameter);
        }
    }
}

fn assert_constraint_diagnostic(context: &CanonicalCheckerContext<'_>, node: NodeRef) {
    let [diagnostic] = context.diagnostics().as_slice() else {
        panic!(
            "expected one constraint diagnostic: {:?}",
            context.diagnostics()
        );
    };
    assert_eq!(diagnostic.diagnostic.code(), 2344);
    assert_eq!(diagnostic.node, Some(node));
    assert_eq!(diagnostic.range_override, None);
    assert_eq!(
        diagnostic.diagnostic.render().unwrap(),
        "Type 'number' does not satisfy the constraint 'string'."
    );
}

#[test]
fn alias_wrapper_defaults_preserve_constraint_diagnostics_and_recovery() {
    let provider = parse_source_file("type Bound<T extends string = string> = { value: T };");
    let source = parse_source_file(concat!(
        "type Defaulted = Bound; type Explicit = Bound<string>; type Rejected = Bound<number>; ",
        "declare const value: Rejected; const read: number = value.value;",
    ));
    let bound = alias(&provider, PROVIDER, "Bound");
    let aliases = ["Defaulted", "Explicit", "Rejected"].map(|name| alias(&source, SOURCE, name));
    let bad_argument = reference_argument(&source, aliases[2].body);
    let value = property(&provider, &bound, "value");
    for query_first in [false, true] {
        let mut context = local_context(&provider, &source);
        assert_cold_property(&context, value);
        if !query_first {
            context.check_source_file(SOURCE).unwrap();
        }
        let types = aliases
            .each_ref()
            .map(|alias| context.get_type_from_type_node(alias.body).unwrap());
        let string = context.store().intrinsic_bootstrap().unwrap().string_type;
        let number = context.store().intrinsic_bootstrap().unwrap().number_type;
        for ((alias, type_), argument) in aliases.iter().zip(types).zip([string, string, number]) {
            assert_instance(&context, &bound, alias, type_, &[argument], None);
        }
        let TypeData::TypeParameter(data) = context
            .store()
            .type_payload(parameter(&context, bound.parameters[0]))
            .unwrap()
            .data()
        else {
            unreachable!();
        };
        assert_eq!(data.constraint, Some(string));
        if query_first {
            assert_cold_property(&context, value);
            assert_unchecked(&context, SOURCE);
        }
        context.check_source_file(SOURCE).unwrap();
        assert_constraint_diagnostic(&context, bad_argument);
        let read = assert_read(&mut context, &source, "read", types[2], value, number);
        assert_parameter_property(&context, value, bound.parameters[0]);
        let alias_queries = aliases.iter().zip(types).collect::<Vec<_>>();
        replay(
            &mut context,
            &alias_queries,
            &[(variable(&source, "value").0, types[2])],
            &[(read, number)],
        );
        assert_unchecked(&context, PROVIDER);
        assert_parameter_property(&context, value, bound.parameters[0]);
    }
}

fn module_specifier(source: &ParseResult) -> NodeRef {
    source
        .arena
        .iter()
        .find_map(|(_, record)| {
            let NodeData::ImportDeclaration(import) = &record.data else {
                return None;
            };
            Some(NodeRef::new(
                source.arena.id(),
                SOURCE,
                import.module_specifier,
            ))
        })
        .unwrap()
}

fn assert_import(
    context: &CanonicalCheckerContext<'_>,
    source: &ParseResult,
    expected: &str,
    provider: &Alias,
) {
    let binding = source
        .arena
        .iter()
        .find_map(|(node, record)| {
            let NodeData::ImportSpecifier(import) = &record.data else {
                return None;
            };
            let NodeData::Identifier(name) = &source.arena.get(import.name)?.data else {
                return None;
            };
            (name.text == expected).then_some(NodeRef::new(source.arena.id(), SOURCE, node))
        })
        .unwrap();
    let imported = symbol(context, binding);
    let target = symbol(context, provider.declaration);
    assert_ne!(imported, target);
    let links = context.store().alias_symbol_links(imported).unwrap();
    assert_eq!(links.immediate_target, Some(target));
    assert_eq!(links.alias_target, AliasTargetState::Resolved(target));
    assert_eq!(links.type_only_declaration, Some(binding));
    assert_eq!(context.store().value_symbol_links(imported), None);
    assert_eq!(context.store().value_symbol_links(target), None);
}

// This active control needs the imported-alias-body commit in the composed gate.
#[test]
#[allow(clippy::too_many_lines)] // Keep the retained modules and both query orders together.
fn imported_bound_defaults_require_imported_alias_body_integration() {
    let library = parse_source_file(LIBRARY_TEXT);
    let provider = parse_source_file(IMPORTED_PROVIDER_TEXT);
    let source = parse_source_file(IMPORTED_SOURCE_TEXT);
    let provider_box = alias(&provider, PROVIDER, "Box");
    let provider_bound = alias(&provider, PROVIDER, "Bound");
    let aliases = ["Direct", "Check", "Captured", "Constrained", "Defaulted"]
        .map(|name| alias(&source, SOURCE, name));
    for query_first in [false, true] {
        let mut context = context(
            &[
                (
                    LIBRARY,
                    &library,
                    "\"/project/globals.ts\"",
                    CanonicalModuleState::Script,
                ),
                (
                    SOURCE,
                    &source,
                    "\"/project/source.ts\"",
                    CanonicalModuleState::External,
                ),
                (
                    PROVIDER,
                    &provider,
                    "\"/project/provider.ts\"",
                    CanonicalModuleState::External,
                ),
            ],
            &[(module_specifier(&source), PROVIDER)],
        );
        if !query_first {
            context.check_source_file(SOURCE).unwrap();
        }
        let types = aliases
            .each_ref()
            .map(|alias| context.get_type_from_type_node(alias.body).unwrap());
        if query_first {
            assert_unchecked(&context, SOURCE);
        }
        let direct_parameter = parameter(&context, aliases[0].parameters[0]);
        assert_instance(
            &context,
            &provider_box,
            &aliases[0],
            types[0],
            &[direct_parameter],
            Some(&[direct_parameter]),
        );
        let string = context.store().intrinsic_bootstrap().unwrap().string_type;
        let constrained_parameter = parameter(&context, aliases[3].parameters[0]);
        let provider_parameter = parameter(&context, provider_bound.parameters[0]);
        assert_ne!(constrained_parameter, provider_parameter);
        for parameter in [constrained_parameter, provider_parameter] {
            let TypeData::TypeParameter(data) =
                context.store().type_payload(parameter).unwrap().data()
            else {
                unreachable!();
            };
            assert_eq!(data.constraint, Some(string));
        }
        assert_instance(
            &context,
            &provider_bound,
            &aliases[3],
            types[3],
            &[constrained_parameter],
            Some(&[constrained_parameter]),
        );
        assert_instance(
            &context,
            &provider_bound,
            &aliases[4],
            types[4],
            &[string],
            None,
        );
        assert_request(
            &context,
            &provider_bound,
            &[],
            Some((&aliases[4], &[])),
            types[4],
        );
        for type_ in [types[0], types[3], types[4]] {
            assert_eq!(object(&context, type_).structured.members, None);
            assert_eq!(object(&context, type_).structured.properties, None);
        }
        for type_ in [types[1], types[2]] {
            let TypeData::Conditional(data) = context.store().type_payload(type_).unwrap().data()
            else {
                panic!("the retained conditional aliases keep their actual type family");
            };
            assert_eq!(data.resolved_true_type, None);
            assert_eq!(data.resolved_false_type, None);
            assert_eq!(data.resolved_inferred_true_type, None);
            assert_eq!(data.resolved_default_constraint, None);
            assert_eq!(data.resolved_constraint_of_distributive, None);
        }
        assert_import(&context, &source, "Box", &provider_box);
        assert_import(&context, &source, "Bound", &provider_bound);
        assert_cold_property(&context, property(&provider, &provider_box, "value"));
        assert_cold_property(&context, property(&provider, &provider_bound, "value"));
        assert_unchecked(&context, PROVIDER);
        context.check_source_file(SOURCE).unwrap();
        assert!(context.diagnostics().is_empty());
        let alias_queries = aliases.iter().zip(types).collect::<Vec<_>>();
        replay(&mut context, &alias_queries, &[], &[]);
        assert_unchecked(&context, PROVIDER);
    }
}
