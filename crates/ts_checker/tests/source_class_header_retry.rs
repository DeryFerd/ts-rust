use ts_ast::{FileId, NodeData, NodeId, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalNameResolverOptions, CanonicalSourceFileFacts,
    CanonicalSourceLanguage, CheckFlags, EscapedName, SemanticSymbolId, SymbolFlags,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerDiagnostics, CanonicalCheckerOptions, ClassMembers,
    DeclaredTypeError, DeclaredTypeLinks, IntrinsicBootstrapOptions, NodeLinks,
    RelationStateSnapshot, SignatureId, SignatureLinks, SourceFileLinks, SymbolNodeLinks, TypeData,
    TypeId, TypeNodeLinks, TypeNodeUnavailable, ValueSymbolLinks, signatures::SignatureFlags,
    types::ObjectFlags,
};
use ts_options::ScriptTarget;
use ts_parser::{ParseResult, parse_source_file};

const LIBRARY_FILE: FileId = FileId::new(202_480);
const FILE: FileId = FileId::new(202_481);
const LIBRARY: &str = "interface Array<T> {} interface ReadonlyArray<T> {}";
const SELF_CLASS: &str =
    "class A { next: A | null = null; constructor(readonly children: (A | null)[]) {} }";

fn context<'a>(library: &'a ParseResult, parsed: &'a ParseResult) -> CanonicalCheckerContext<'a> {
    let mut binder = CanonicalBinder::new();
    for (source, file, path, declaration, default_library) in [
        (library, LIBRARY_FILE, "\"/project/lib.d.ts\"", true, true),
        (
            parsed,
            FILE,
            "\"/project/class-header-retry.ts\"",
            false,
            false,
        ),
    ] {
        assert!(source.diagnostics.is_empty(), "{:?}", source.diagnostics);
        binder
            .bind_source_file_with_facts(
                &source.arena,
                source.source_file,
                file,
                CanonicalSourceFileFacts::new_with_default_library(
                    EscapedName::source(path),
                    CanonicalSourceLanguage::TypeScript,
                    declaration,
                    default_library,
                    CanonicalModuleState::Script,
                ),
            )
            .unwrap();
        binder
            .bind_typescript_declaration_slice(&source.arena, file)
            .unwrap();
    }
    let context = CanonicalCheckerContext::new(
        binder.finish(),
        vec![(LIBRARY_FILE, &library.arena), (FILE, &parsed.arena)],
        CanonicalCheckerOptions {
            intrinsic: IntrinsicBootstrapOptions {
                strict_null_checks: true,
                ..IntrinsicBootstrapOptions::default()
            },
            strict_property_initialization: true,
            no_implicit_any: true,
            name_resolution: CanonicalNameResolverOptions {
                emit_target: ScriptTarget::Es2022,
                ..CanonicalNameResolverOptions::default()
            },
            ..CanonicalCheckerOptions::default()
        },
    )
    .unwrap();
    let store = context.store();
    let bound = context.file(LIBRARY_FILE).unwrap().1;
    let locals = store
        .symbol_table(bound.locals(bound.source_file()).unwrap())
        .unwrap();
    for (name, target) in [
        ("Array", context.global_types().array_type),
        ("ReadonlyArray", context.global_types().readonly_array_type),
    ] {
        let symbol = store
            .get_merged_symbol(locals.get_source(name).unwrap())
            .unwrap();
        assert_eq!(
            store.symbol(symbol).unwrap().flags(),
            SymbolFlags::INTERFACE
        );
        let [declaration] = store.symbol(symbol).unwrap().declarations().unwrap() else {
            unreachable!()
        };
        assert!(declaration.is_for(library.arena.id(), LIBRARY_FILE));
        assert_eq!(bound.symbol(*declaration), Some(symbol));
        assert_eq!(
            store.declared_type_links(symbol).unwrap().declared_type,
            Some(target)
        );
        assert_eq!(store.type_payload(target).unwrap().symbol(), Some(symbol));
    }
    assert_ne!(
        context.global_types().array_type,
        context.global_types().readonly_array_type
    );
    context
}

fn node(parsed: &ParseResult, id: NodeId) -> NodeRef {
    NodeRef::new(parsed.arena.id(), FILE, id)
}

fn symbol(context: &CanonicalCheckerContext<'_>, declaration: NodeRef) -> SemanticSymbolId {
    let raw = context.file(FILE).unwrap().1.symbol(declaration).unwrap();
    context.store().get_merged_symbol(raw).unwrap()
}

struct Nodes {
    class: NodeRef,
    next: NodeRef,
    next_name: NodeRef,
    next_annotation: NodeRef,
    next_initializer: NodeRef,
    constructor: NodeRef,
    parameter: NodeRef,
    parameter_name: NodeRef,
    parameter_annotation: NodeRef,
    construction: NodeRef,
    callee: NodeRef,
    argument: NodeRef,
}

fn nodes(parsed: &ParseResult) -> Nodes {
    let class = parsed
        .arena
        .iter()
        .find_map(|(id, record)| {
            (record.kind == SyntaxKind::ClassDeclaration).then_some(node(parsed, id))
        })
        .unwrap();
    let NodeData::ClassDeclaration(class_data) = &parsed.arena.get(class.node).unwrap().data else {
        unreachable!()
    };
    let mut field = None;
    let mut constructor = None;
    for &id in &class_data.members.nodes {
        let declaration = node(parsed, id);
        match &parsed.arena.get(id).unwrap().data {
            NodeData::PropertyDeclaration(property) => {
                assert!(field.is_none());
                field = Some((
                    declaration,
                    node(parsed, property.name),
                    node(parsed, property.type_.unwrap()),
                    node(parsed, property.initializer.unwrap()),
                ));
            }
            NodeData::ConstructorDeclaration(data) => {
                let [parameter] = data.parameters.nodes.as_slice() else {
                    unreachable!()
                };
                constructor = Some((declaration, node(parsed, *parameter)));
            }
            _ => panic!("the original class retains its field and constructor"),
        }
    }
    let (next, next_name, next_annotation, next_initializer) = field.unwrap();
    let (constructor, parameter) = constructor.unwrap();
    let NodeData::ParameterDeclaration(data) = &parsed.arena.get(parameter.node).unwrap().data
    else {
        unreachable!()
    };
    let (construction, callee, argument) = parsed
        .arena
        .iter()
        .find_map(|(id, record)| {
            let NodeData::NewExpression(new) = &record.data else {
                return None;
            };
            let [argument] = new.arguments.as_ref()?.nodes.as_slice() else {
                unreachable!()
            };
            Some((
                node(parsed, id),
                node(parsed, new.expression),
                node(parsed, *argument),
            ))
        })
        .unwrap();
    assert_eq!(
        parsed.arena.get(argument.node).unwrap().kind,
        SyntaxKind::ArrayLiteralExpression
    );
    Nodes {
        class,
        next,
        next_name,
        next_annotation,
        next_initializer,
        constructor,
        parameter,
        parameter_name: node(parsed, data.name),
        parameter_annotation: node(parsed, data.type_.unwrap()),
        construction,
        callee,
        argument,
    }
}

type NodePublication = (
    NodeRef,
    Option<NodeLinks>,
    Option<TypeNodeLinks>,
    Option<SymbolNodeLinks>,
    Option<SignatureLinks>,
);
type SymbolPublication = (
    SemanticSymbolId,
    Option<DeclaredTypeLinks>,
    Option<ValueSymbolLinks>,
);

#[derive(Debug, Eq, PartialEq)]
struct Publication {
    counts: [usize; 7],
    relations: RelationStateSnapshot,
    nodes: Vec<NodePublication>,
    symbols: Vec<SymbolPublication>,
    source: Option<SourceFileLinks>,
    diagnostics: CanonicalCheckerDiagnostics,
}

fn publication(context: &CanonicalCheckerContext<'_>, parsed: &ParseResult) -> Publication {
    let store = context.store();
    Publication {
        counts: [
            store.type_len(),
            store.symbol_len(),
            store.signature_len(),
            store.mapper_len(),
            store.type_alias_len(),
            store.index_info_len(),
            store.symbol_store().symbol_table_len(),
        ],
        relations: store.relation_state_snapshot(),
        nodes: parsed
            .arena
            .iter()
            .map(|(id, _)| {
                let node = node(parsed, id);
                (
                    node,
                    store.node_links(node).cloned(),
                    store.type_node_links(node).cloned(),
                    store.symbol_node_links(node).cloned(),
                    store.signature_links(node).cloned(),
                )
            })
            .collect(),
        symbols: store
            .symbol_store()
            .symbols()
            .map(|(symbol, _)| {
                (
                    symbol,
                    store.declared_type_links(symbol).cloned(),
                    store.value_symbol_links(symbol).cloned(),
                )
            })
            .collect(),
        source: store
            .source_file_links(context.source_file(FILE).unwrap())
            .cloned(),
        diagnostics: context.diagnostics().clone(),
    }
}

fn cached_type(context: &CanonicalCheckerContext<'_>, node: NodeRef) -> TypeId {
    context
        .store()
        .type_node_links(node)
        .and_then(|links| links.resolved_type)
        .unwrap()
}

fn assert_array(context: &CanonicalCheckerContext<'_>, array: TypeId, element: TypeId) {
    let TypeData::TypeReference(reference) = context.store().type_payload(array).unwrap().data()
    else {
        panic!("the array must retain its real library target")
    };
    assert_eq!(
        reference.object.target,
        Some(context.global_types().array_type)
    );
    assert_eq!(
        reference.resolved_type_arguments.as_deref(),
        Some(&[element][..])
    );
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Identities {
    instance: TypeId,
    value: TypeId,
    union: TypeId,
    children: TypeId,
    next: SemanticSymbolId,
    property: SemanticSymbolId,
    local: SemanticSymbolId,
    signature: SignatureId,
}

#[allow(clippy::too_many_lines)] // Check the self union and both parameter-property symbols together.
fn identities(
    context: &CanonicalCheckerContext<'_>,
    nodes: &Nodes,
    members: &ClassMembers,
) -> Identities {
    let store = context.store();
    let owner = symbol(context, nodes.class);
    let instance = members.shells().instance_type();
    let value = members.shells().value_type();
    assert_eq!(store.type_payload(instance).unwrap().symbol(), Some(owner));
    assert_eq!(
        store.declared_type_links(owner).unwrap().declared_type,
        Some(instance)
    );
    assert_eq!(
        store.value_symbol_links(owner).unwrap().resolved_type,
        Some(value)
    );
    let TypeData::Interface(class) = store.type_payload(instance).unwrap().data() else {
        unreachable!()
    };
    assert!(class.this_type.is_some());
    assert_ne!(class.this_type, Some(instance));
    let union = cached_type(context, nodes.next_annotation);
    let TypeData::Union(data) = store.type_payload(union).unwrap().data() else {
        panic!("the written self union must retain both constituents")
    };
    assert_eq!(
        data.union.types,
        [store.intrinsic_bootstrap().unwrap().null_type, instance]
    );
    let next = symbol(context, nodes.next);
    let property = symbol(context, nodes.parameter);
    let bound = context.file(FILE).unwrap().1;
    let local = store
        .symbol_table(bound.locals(nodes.constructor).unwrap())
        .unwrap()
        .get_source("children")
        .unwrap();
    assert_ne!(local, property);
    let children = cached_type(context, nodes.parameter_annotation);
    assert_array(context, children, union);
    for (symbol, flags, check_flags, parent) in [
        (
            local,
            SymbolFlags::FUNCTION_SCOPED_VARIABLE,
            CheckFlags::NONE,
            None,
        ),
        (
            property,
            SymbolFlags::PROPERTY,
            CheckFlags::READONLY,
            Some(owner),
        ),
    ] {
        let record = store.symbol(symbol).unwrap();
        assert_eq!(record.flags(), flags);
        assert_eq!(record.check_flags(), check_flags);
        assert_eq!(record.parent(), parent);
        assert_eq!(record.declarations(), Some(&[nodes.parameter][..]));
        assert_eq!(record.value_declaration(), Some(nodes.parameter));
        assert_eq!(
            store.value_symbol_links(symbol).unwrap().resolved_type,
            Some(children)
        );
    }
    let instance_members = store
        .symbol_table(members.instance_members().unwrap())
        .unwrap();
    assert_eq!(instance_members.get_source("next"), Some(next));
    assert_eq!(instance_members.get_source("children"), Some(property));
    assert_eq!(
        store
            .symbol_table(members.static_members())
            .unwrap()
            .get_source("children"),
        None
    );
    let signature = members.default_construct_signature();
    let record = store.signature(signature).unwrap();
    assert_eq!(record.flags(), SignatureFlags::CONSTRUCT);
    assert_eq!(record.declaration(), Some(nodes.constructor));
    assert_eq!(record.parameters(), [local]);
    assert_eq!(record.min_argument_count(), 1);
    assert_eq!(record.resolved_return_type(), Some(instance));
    assert_eq!(
        store
            .signature_links(nodes.constructor)
            .unwrap()
            .resolved_signature
            .signature(),
        Some(signature)
    );
    Identities {
        instance,
        value,
        union,
        children,
        next,
        property,
        local,
        signature,
    }
}

fn assert_header_is_pending(
    context: &CanonicalCheckerContext<'_>,
    nodes: &Nodes,
    identity: Identities,
) {
    assert!(
        context
            .store()
            .source_file_links(context.source_file(FILE).unwrap())
            .is_none_or(|links| !links.type_checked)
    );
    assert!(
        context
            .store()
            .value_symbol_links(identity.next)
            .is_none_or(|links| links.resolved_type.is_none())
    );
    for node in [nodes.construction, nodes.callee, nodes.argument] {
        assert!(context.store().type_node_links(node).is_none());
        assert!(context.store().signature_links(node).is_none());
    }
    assert!(context.diagnostics().is_empty());
}

fn assert_completed(
    context: &mut CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    nodes: &Nodes,
    members: &ClassMembers,
    identity: Identities,
) {
    assert!(
        context
            .store()
            .source_file_links(context.source_file(FILE).unwrap())
            .unwrap()
            .type_checked
    );
    assert!(context.diagnostics().is_empty());
    assert_eq!(identities(context, nodes, members), identity);
    assert_eq!(
        context
            .store()
            .value_symbol_links(identity.next)
            .unwrap()
            .resolved_type,
        Some(identity.union)
    );
    for (annotation, expected) in [
        (nodes.next_annotation, identity.union),
        (nodes.parameter_annotation, identity.children),
    ] {
        assert_eq!(
            context.get_type_from_type_node(annotation).unwrap(),
            expected
        );
        assert_eq!(context.get_type_at_location(annotation).unwrap(), expected);
    }
    for (location, expected) in [
        (nodes.next_name, identity.union),
        (nodes.parameter_name, identity.children),
        (nodes.construction, identity.instance),
        (nodes.callee, identity.value),
    ] {
        assert_eq!(context.get_type_at_location(location).unwrap(), expected);
    }
    assert_eq!(
        context.get_symbol_at_location(nodes.next_name).unwrap(),
        Some(identity.next)
    );
    for symbol in [identity.property, identity.local] {
        assert_eq!(
            context.get_symbol_declarations(symbol).unwrap(),
            &[nodes.parameter]
        );
    }
    let raw_null = context
        .store()
        .intrinsic_bootstrap()
        .unwrap()
        .null_widening_type;
    assert_eq!(
        context
            .get_type_at_location(nodes.next_initializer)
            .unwrap(),
        raw_null
    );
    let argument_type = context.get_type_at_location(nodes.argument).unwrap();
    let never = context
        .store()
        .intrinsic_bootstrap()
        .unwrap()
        .implicit_never_type;
    assert_array(context, argument_type, never);
    assert!(
        context
            .store()
            .type_payload(argument_type)
            .unwrap()
            .object_flags()
            .contains(ObjectFlags::ARRAY_LITERAL)
    );
    assert_eq!(
        context
            .store()
            .signature_links(nodes.construction)
            .unwrap()
            .resolved_signature
            .signature(),
        Some(identity.signature)
    );
    for (id, record) in parsed.arena.iter() {
        if matches!(record.data, NodeData::TypeReferenceNode(_)) {
            assert_eq!(
                context.get_type_from_type_node(node(parsed, id)).unwrap(),
                identity.instance
            );
        }
    }
}

fn assert_final_replay(
    context: &mut CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    nodes: &Nodes,
    members: &ClassMembers,
    identity: Identities,
) {
    assert_completed(context, parsed, nodes, members, identity);
    let warm = publication(context, parsed);
    for _ in 0..2 {
        assert_eq!(
            context
                .get_nongeneric_class_members(symbol(context, nodes.class))
                .unwrap(),
            *members
        );
        context.check_source_file(FILE).unwrap();
        context.recheck_source_file(FILE).unwrap();
        assert_completed(context, parsed, nodes, members, identity);
        assert_eq!(publication(context, parsed), warm);
    }
}

#[test]
fn source_first_self_class_keeps_header_and_construction_identities() {
    let library = parse_source_file(LIBRARY);
    let parsed = parse_source_file(&format!("{SELF_CLASS}\nconst root = new A([]);\n"));
    let nodes = nodes(&parsed);
    let mut context = context(&library, &parsed);
    context.check_source_file(FILE).unwrap();
    let members = context
        .get_nongeneric_class_members(symbol(&context, nodes.class))
        .unwrap();
    let identity = identities(&context, &nodes, &members);
    assert_final_replay(&mut context, &parsed, &nodes, &members, identity);
}

#[test]
fn member_query_first_keeps_self_class_header_pending_until_source_check() {
    let library = parse_source_file(LIBRARY);
    let parsed = parse_source_file(&format!("{SELF_CLASS}\nconst root = new A([]);\n"));
    let nodes = nodes(&parsed);
    let mut context = context(&library, &parsed);
    let owner = symbol(&context, nodes.class);
    let members = context.get_nongeneric_class_members(owner).unwrap();
    let identity = identities(&context, &nodes, &members);
    assert_header_is_pending(&context, &nodes, identity);
    let header = publication(&context, &parsed);
    assert_eq!(
        context.get_nongeneric_class_members(owner).unwrap(),
        members
    );
    assert_header_is_pending(&context, &nodes, identity);
    assert_eq!(publication(&context, &parsed), header);
    context.check_source_file(FILE).unwrap();
    assert_final_replay(&mut context, &parsed, &nodes, &members, identity);
}

#[test]
fn failed_self_union_query_preserves_header_for_source_retry() {
    let library = parse_source_file(LIBRARY);
    let parsed = parse_source_file(&format!("{SELF_CLASS}\nconst root = new A([]);\n"));
    let nodes = nodes(&parsed);
    let mut context = context(&library, &parsed);
    let owner = symbol(&context, nodes.class);
    let members = context.get_nongeneric_class_members(owner).unwrap();
    let identity = identities(&context, &nodes, &members);
    let expected = DeclaredTypeError::TypeNodeUnavailable(
        TypeNodeUnavailable::InvalidCachedUnionType(identity.instance),
    );
    let header = publication(&context, &parsed);
    for _ in 0..2 {
        assert_eq!(
            context.get_type_from_type_node(nodes.next_annotation),
            Err(expected)
        );
        assert_header_is_pending(&context, &nodes, identity);
        assert_eq!(publication(&context, &parsed), header);
        assert_eq!(
            context.get_nongeneric_class_members(owner).unwrap(),
            members
        );
        assert_eq!(identities(&context, &nodes, &members), identity);
        assert_eq!(publication(&context, &parsed), header);
    }
    context.check_source_file(FILE).unwrap();
    assert_final_replay(&mut context, &parsed, &nodes, &members, identity);
}
