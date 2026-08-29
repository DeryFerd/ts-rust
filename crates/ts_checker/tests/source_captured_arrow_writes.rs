use ts_ast::{FileId, FlowFlags, FlowNodePayload, NodeData, NodeId, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId, SymbolFlags,
};
use ts_checker::semantic::{
    ArrayLiteralLinks, CanonicalCheckerContext, CanonicalCheckerOptions, DeclaredTypeLinks,
    IntrinsicBootstrapOptions, MappedSymbolLinks, NodeLinks, SignatureId, SignatureLinks,
    SourceFileLinks, SymbolNodeLinks, SymbolReferenceLinks, TypeAliasLinks, TypeData, TypeId,
    TypeNodeLinks, ValueSymbolLinks,
    signatures::SignatureFlags,
    type_records::ObjectTypeData,
    types::{ObjectFlags, TypeFlags},
};
use ts_parser::{ParseResult, parse_source_file};

const LIBRARY_FILE: FileId = FileId::new(8_260);
const SOURCE_FILE: FileId = FileId::new(8_261);
const LIBRARY: &str = include_str!("../../ts_bundled/libs/lib.es5.d.ts");

fn context<'arena>(
    library: &'arena ParseResult,
    source: &'arena ParseResult,
) -> CanonicalCheckerContext<'arena> {
    let files = [
        (LIBRARY_FILE, library, "\"/lib/lib.es5.d.ts\"", true),
        (
            SOURCE_FILE,
            source,
            "\"/project/captured-writes.ts\"",
            false,
        ),
    ];
    let mut binder = CanonicalBinder::new();
    for &(file, parsed, path, library) in &files {
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new_with_default_library(
                    EscapedName::source(path),
                    CanonicalSourceLanguage::TypeScript,
                    library,
                    library,
                    if library {
                        CanonicalModuleState::Script
                    } else {
                        CanonicalModuleState::External
                    },
                ),
            )
            .unwrap();
    }
    for &(file, parsed, _, _) in &files {
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
    }
    CanonicalCheckerContext::new(
        binder.finish(),
        files
            .into_iter()
            .map(|(file, parsed, _, _)| (file, &parsed.arena))
            .collect(),
        CanonicalCheckerOptions {
            intrinsic: IntrinsicBootstrapOptions {
                strict_null_checks: true,
                exact_optional_property_types: false,
            },
            strict_function_types: true,
            ..CanonicalCheckerOptions::default()
        },
    )
    .unwrap()
}

fn node_ref(parsed: &ParseResult, node: NodeId) -> NodeRef {
    NodeRef::new(parsed.arena.id(), SOURCE_FILE, node)
}

fn only_node(parsed: &ParseResult, kind: SyntaxKind) -> NodeRef {
    let mut nodes = parsed
        .arena
        .iter()
        .filter_map(|(node, record)| (record.kind == kind).then_some(node_ref(parsed, node)));
    let node = nodes.next().expect("the source must contain this node");
    assert!(nodes.next().is_none(), "expected one {kind:?}");
    node
}

fn variable(parsed: &ParseResult, expected: &str) -> NodeRef {
    let mut declarations = parsed.arena.iter().filter_map(|(node, record)| {
        let NodeData::VariableDeclaration(variable) = &record.data else {
            return None;
        };
        let NodeData::Identifier(name) = &parsed.arena.get(variable.name)?.data else {
            return None;
        };
        (name.text == expected).then_some(node_ref(parsed, node))
    });
    let declaration = declarations.next().expect("the local must exist");
    assert!(declarations.next().is_none(), "duplicate local {expected}");
    declaration
}

fn symbol(context: &CanonicalCheckerContext<'_>, node: NodeRef) -> SemanticSymbolId {
    let raw = context.file(node.file).unwrap().1.symbol(node).unwrap();
    context.store().get_merged_symbol(raw).unwrap()
}

fn value_type(context: &CanonicalCheckerContext<'_>, owner: SemanticSymbolId) -> TypeId {
    context
        .store()
        .value_symbol_links(owner)
        .and_then(|links| links.resolved_type)
        .unwrap()
}

fn cached_type(context: &CanonicalCheckerContext<'_>, node: NodeRef) -> TypeId {
    context
        .store()
        .type_node_links(node)
        .and_then(|links| links.resolved_type)
        .unwrap_or_else(|| panic!("missing checked expression type at {node:?}"))
}

fn signature(context: &CanonicalCheckerContext<'_>, node: NodeRef) -> SignatureId {
    context
        .store()
        .signature_links(node)
        .and_then(|links| links.resolved_signature.signature())
        .unwrap()
}

fn object<'a>(context: &'a CanonicalCheckerContext<'_>, type_: TypeId) -> &'a ObjectTypeData {
    let TypeData::Object(object) = context.store().type_payload(type_).unwrap().data() else {
        panic!("expected a source callable or property-alias object")
    };
    object
}

fn array_element(context: &CanonicalCheckerContext<'_>, type_: TypeId) -> TypeId {
    let array = match context.store().type_payload(type_).unwrap().data() {
        TypeData::TypeReference(array) => array,
        TypeData::Interface(interface) if type_ == context.global_types().array_type => {
            &interface.reference
        }
        _ => panic!("expected a canonical Array reference"),
    };
    assert_eq!(array.object.target, Some(context.global_types().array_type));
    let [element] = array.resolved_type_arguments.as_deref().unwrap() else {
        panic!("Array must retain its one element type")
    };
    *element
}

#[derive(Debug, Eq, PartialEq)]
struct Callable {
    owner: SemanticSymbolId,
    binding: SemanticSymbolId,
    type_: TypeId,
    signature: SignatureId,
    type_parameters: Vec<TypeId>,
    parameters: Vec<(SemanticSymbolId, TypeId)>,
    returned: TypeId,
}

#[allow(clippy::too_many_lines)] // Check the signature together with both real source owners.
fn callable(
    context: &CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    node: NodeRef,
) -> Callable {
    let record = parsed.arena.get(node.node).unwrap();
    let NodeData::ArrowFunction(arrow) = &record.data else {
        panic!("expected an actual TypeScript arrow")
    };
    let owner = symbol(context, node);
    let binding_node = node_ref(parsed, record.parent.unwrap());
    let binding = symbol(context, binding_node);
    assert_ne!(owner, binding);
    let owner_record = context.store().symbol(owner).unwrap();
    assert_eq!(owner_record.flags(), SymbolFlags::FUNCTION);
    assert_eq!(owner_record.declarations(), Some(&[node][..]));
    assert_eq!(owner_record.value_declaration(), Some(node));
    let binding_record = context.store().symbol(binding).unwrap();
    let binding_flags = match parsed.arena.get(binding_node.node).unwrap().kind {
        SyntaxKind::ExportAssignment | SyntaxKind::PropertyAssignment => SymbolFlags::PROPERTY,
        SyntaxKind::VariableDeclaration => SymbolFlags::BLOCK_SCOPED_VARIABLE,
        kind => panic!("unexpected arrow binding {kind:?}"),
    };
    assert_eq!(binding_record.flags(), binding_flags);
    assert_eq!(binding_record.declarations(), Some(&[binding_node][..]));
    assert_eq!(binding_record.value_declaration(), Some(binding_node));
    let type_ = value_type(context, owner);
    if parsed.arena.get(binding_node.node).unwrap().kind == SyntaxKind::PropertyAssignment {
        // Object literals publish the value on a source-backed property clone.
        assert_eq!(context.store().value_symbol_links(binding), None);
    } else {
        assert_eq!(value_type(context, binding), type_);
    }
    assert_eq!(cached_type(context, node), type_);
    assert_eq!(
        context.store().type_payload(type_).unwrap().symbol(),
        Some(owner)
    );
    let signature = signature(context, node);
    assert_eq!(
        object(context, type_).structured.signatures.as_deref(),
        Some(&[signature][..])
    );
    assert_eq!(object(context, type_).structured.call_signature_count, 1);
    assert_eq!(object(context, type_).target, None);
    assert_eq!(object(context, type_).mapper, None);
    let type_parameters = arrow
        .type_parameters
        .as_ref()
        .into_iter()
        .flat_map(|parameters| &parameters.nodes)
        .map(|&declaration| {
            let owner = symbol(context, node_ref(parsed, declaration));
            let type_ = context
                .store()
                .declared_type_links(owner)
                .unwrap()
                .declared_type
                .unwrap();
            let record = context.store().type_payload(type_).unwrap();
            assert_eq!(record.flags(), TypeFlags::TYPE_PARAMETER);
            assert_eq!(record.symbol(), Some(owner));
            let TypeData::TypeParameter(parameter) = record.data() else {
                unreachable!()
            };
            assert_eq!(parameter.target, None);
            assert_eq!(parameter.mapper, None);
            type_
        })
        .collect::<Vec<_>>();
    let parameters = arrow
        .parameters
        .nodes
        .iter()
        .map(|&declaration| {
            let owner = symbol(context, node_ref(parsed, declaration));
            (owner, value_type(context, owner))
        })
        .collect::<Vec<_>>();
    let record = context.store().signature(signature).unwrap();
    assert_eq!(record.declaration(), Some(node));
    assert_eq!(record.flags(), SignatureFlags::NONE);
    assert_eq!(record.type_parameters(), type_parameters);
    assert_eq!(
        record.parameters(),
        parameters
            .iter()
            .map(|&(owner, _)| owner)
            .collect::<Vec<_>>()
    );
    assert_eq!(record.target(), None);
    assert_eq!(record.mapper(), None);
    assert_eq!(record.this_parameter(), None);
    assert_eq!(record.resolved_type_predicate(), None);
    assert_eq!(
        record.min_argument_count(),
        i32::try_from(parameters.len()).unwrap()
    );
    Callable {
        owner,
        binding,
        type_,
        signature,
        type_parameters,
        parameters,
        returned: record.resolved_return_type().unwrap(),
    }
}

#[derive(Debug, Eq, PartialEq)]
struct SourceProof {
    callables: Vec<Callable>,
    locations: Vec<(NodeRef, TypeId, Option<SemanticSymbolId>)>,
    annotations: Vec<(NodeRef, TypeId)>,
    returns: Vec<(SignatureId, TypeId)>,
}

// Read the checked source first. Public queries must not supply a missing producer.
#[allow(clippy::too_many_lines)]
fn source_proof(
    context: &CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    library: &ParseResult,
    call_count: usize,
    bad_values: bool,
) -> SourceProof {
    let bootstrap = context.store().intrinsic_bootstrap().unwrap();
    let exported = only_node(parsed, SyntaxKind::ExportAssignment);
    let NodeData::ExportAssignment(export) = &parsed.arena.get(exported.node).unwrap().data else {
        unreachable!()
    };
    assert!(!export.is_export_equals);
    let factory_node = node_ref(parsed, export.expression);
    let NodeData::ArrowFunction(factory) = &parsed.arena.get(factory_node.node).unwrap().data
    else {
        unreachable!()
    };
    let factory_state = callable(context, parsed, factory_node);
    let [t] = factory_state.type_parameters.as_slice() else {
        panic!("the factory must own T")
    };
    let t = *t;
    assert_eq!(factory_state.parameters.len(), 1);
    assert_eq!(factory_state.parameters[0].1, t);
    assert_eq!(factory_state.returned, t);
    let mut proof = SourceProof {
        locations: vec![(factory_node, factory_state.type_, None)],
        annotations: vec![(node_ref(parsed, factory.type_.unwrap()), t)],
        returns: vec![(factory_state.signature, t)],
        callables: vec![factory_state],
    };
    let NodeData::Block(factory_body) = &parsed.arena.get(factory.body).unwrap().data else {
        unreachable!()
    };
    let NodeData::ReturnStatement(returned) = &parsed
        .arena
        .get(*factory_body.statements.nodes.last().unwrap())
        .unwrap()
        .data
    else {
        panic!("the factory must retain its final return")
    };
    let returned = node_ref(parsed, returned.expression.unwrap());
    assert_eq!(cached_type(context, returned), t);
    proof
        .locations
        .push((returned, t, Some(proof.callables[0].parameters[0].0)));
    let NodeData::ParameterDeclaration(seed) =
        &parsed.arena.get(factory.parameters.nodes[0]).unwrap().data
    else {
        unreachable!()
    };
    proof
        .annotations
        .push((node_ref(parsed, seed.type_.unwrap()), t));
    proof.locations.push((
        node_ref(parsed, seed.name),
        t,
        Some(proof.callables[0].parameters[0].0),
    ));

    let observers_node = variable(parsed, "_observers");
    let NodeData::VariableDeclaration(observers) =
        &parsed.arena.get(observers_node.node).unwrap().data
    else {
        unreachable!()
    };
    let observers_owner = symbol(context, observers_node);
    let owner = context.store().symbol(observers_owner).unwrap();
    assert_eq!(owner.flags(), SymbolFlags::BLOCK_SCOPED_VARIABLE);
    assert_eq!(owner.declarations(), Some(&[observers_node][..]));
    assert_eq!(owner.value_declaration(), Some(observers_node));
    let (_, bound) = context.file(SOURCE_FILE).unwrap();
    assert_eq!(
        bound.block_scope_container(observers_node),
        Some(factory_node)
    );
    assert_eq!(
        context
            .store()
            .symbol_table(bound.locals(factory_node).unwrap())
            .unwrap()
            .get_source("_observers"),
        Some(observers_owner)
    );
    let annotation = node_ref(parsed, observers.type_.unwrap());
    let array = value_type(context, observers_owner);
    assert_eq!(cached_type(context, annotation), array);
    proof.annotations.push((annotation, array));
    proof.locations.push((
        node_ref(parsed, observers.name),
        array,
        Some(observers_owner),
    ));
    let element = array_element(context, array);
    let alias = context
        .store()
        .type_payload(element)
        .unwrap()
        .alias()
        .unwrap();
    let alias = context.store().type_alias(alias).unwrap();
    assert_eq!(alias.type_arguments(), Some(&[t][..]));
    let alias_owner = alias.symbol().unwrap();
    let alias_links = context.store().type_alias_links(alias_owner).unwrap();
    let [alias_t] = alias_links.type_parameters.as_deref().unwrap() else {
        panic!("Observer must keep its own type parameter")
    };
    assert_ne!(*alias_t, t);
    let alias_declaration = context
        .store()
        .symbol(alias_owner)
        .unwrap()
        .declarations()
        .unwrap()[0];
    let NodeData::TypeAliasDeclaration(alias_declaration) =
        &parsed.arena.get(alias_declaration.node).unwrap().data
    else {
        unreachable!()
    };
    let alias_parameter = node_ref(
        parsed,
        alias_declaration.type_parameters.as_ref().unwrap().nodes[0],
    );
    assert_eq!(
        context.store().type_payload(*alias_t).unwrap().symbol(),
        Some(symbol(context, alias_parameter))
    );
    assert_eq!(object(context, element).target, alias_links.declared_type);
    assert_eq!(
        context
            .store()
            .map_type(object(context, element).mapper.unwrap(), *alias_t),
        Some(t)
    );

    let initial = node_ref(parsed, observers.initializer.unwrap());
    assert_eq!(
        array_element(context, cached_type(context, initial)),
        bootstrap.implicit_never_type
    );
    proof
        .locations
        .push((initial, cached_type(context, initial), None));
    for name in ["before", "after"] {
        let declaration = variable(parsed, name);
        let NodeData::VariableDeclaration(local) =
            &parsed.arena.get(declaration.node).unwrap().data
        else {
            unreachable!()
        };
        let local_owner = symbol(context, declaration);
        assert_eq!(value_type(context, local_owner), array);
        let read = node_ref(parsed, local.initializer.unwrap());
        assert_eq!(cached_type(context, read), array);
        proof.locations.push((read, array, Some(observers_owner)));
        proof
            .locations
            .push((node_ref(parsed, local.name), array, Some(local_owner)));
    }

    let assignment = only_node(parsed, SyntaxKind::BinaryExpression);
    let NodeData::BinaryExpression(binary) = &parsed.arena.get(assignment.node).unwrap().data
    else {
        unreachable!()
    };
    assert_eq!(
        parsed.arena.get(binary.operator_token).unwrap().kind,
        SyntaxKind::EqualsToken
    );
    let left = node_ref(parsed, binary.left);
    let right = node_ref(parsed, binary.right);
    assert_eq!(cached_type(context, left), array);
    assert_eq!(
        context
            .store()
            .symbol_node_links(left)
            .unwrap()
            .resolved_symbol,
        Some(observers_owner)
    );
    let rhs = cached_type(context, right);
    assert_eq!(cached_type(context, assignment), rhs);
    assert_ne!(rhs, array);
    assert!(
        context
            .store()
            .type_payload(rhs)
            .unwrap()
            .object_flags()
            .contains(ObjectFlags::ARRAY_LITERAL)
    );
    assert_eq!(
        array_element(context, rhs),
        if bad_values {
            bootstrap.number_type
        } else {
            bootstrap.implicit_never_type
        }
    );
    proof.locations.extend([
        (left, array, Some(observers_owner)),
        (right, rhs, None),
        (assignment, rhs, None),
    ]);
    let statement = parsed.arena.get(assignment.node).unwrap().parent.unwrap();
    assert_eq!(
        parsed.arena.get(statement).unwrap().kind,
        SyntaxKind::ExpressionStatement
    );
    let block = parsed.arena.get(statement).unwrap().parent.unwrap();
    let reset = node_ref(parsed, parsed.arena.get(block).unwrap().parent.unwrap());
    let NodeData::ArrowFunction(reset_arrow) = &parsed.arena.get(reset.node).unwrap().data else {
        panic!("the captured write must remain in its stored arrow")
    };
    assert_eq!(reset_arrow.body, block);
    assert_eq!(reset_arrow.type_, None);
    let reset_state = callable(context, parsed, reset);
    assert!(reset_state.type_parameters.is_empty());
    assert!(reset_state.parameters.is_empty());
    assert_eq!(reset_state.returned, bootstrap.void_type);
    assert_ne!(reset_state.owner, observers_owner);
    assert!(bound.locals(reset).is_none_or(|locals| {
        context
            .store()
            .symbol_table(locals)
            .unwrap()
            .get_source("_observers")
            .is_none()
    }));
    proof.locations.push((reset, reset_state.type_, None));
    proof
        .returns
        .push((reset_state.signature, bootstrap.void_type));
    proof.callables.push(reset_state);

    let calls = parsed
        .arena
        .iter()
        .filter_map(|(node, record)| {
            matches!(record.data, NodeData::CallExpression(_)).then_some(node_ref(parsed, node))
        })
        .collect::<Vec<_>>();
    assert_eq!(calls.len(), call_count);
    if !calls.is_empty() {
        assert_subscribe(
            context,
            parsed,
            library,
            &calls,
            reset,
            observers_owner,
            array,
            element,
            &mut proof,
        );
    }
    proof
}

#[allow(clippy::too_many_arguments, clippy::too_many_lines)]
fn assert_subscribe(
    context: &CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    library: &ParseResult,
    calls: &[NodeRef],
    reset: NodeRef,
    observers: SemanticSymbolId,
    array: TypeId,
    element: TypeId,
    proof: &mut SourceProof,
) {
    let subscribe_binding = variable(parsed, "subscribe");
    let NodeData::VariableDeclaration(variable) =
        &parsed.arena.get(subscribe_binding.node).unwrap().data
    else {
        unreachable!()
    };
    let subscribe = node_ref(parsed, variable.initializer.unwrap());
    let NodeData::ArrowFunction(arrow) = &parsed.arena.get(subscribe.node).unwrap().data else {
        unreachable!()
    };
    let state = callable(context, parsed, subscribe);
    assert!(state.type_parameters.is_empty());
    let [(observer, observer_type)] = state.parameters.as_slice() else {
        panic!("subscribe must retain its original observer parameter")
    };
    let observer = *observer;
    assert_eq!(*observer_type, element);
    assert_eq!(
        cached_type(context, node_ref(parsed, arrow.type_.unwrap())),
        state.returned
    );
    proof
        .annotations
        .push((node_ref(parsed, arrow.type_.unwrap()), state.returned));
    proof.locations.push((subscribe, state.type_, None));
    proof.returns.push((state.signature, state.returned));
    let NodeData::ParameterDeclaration(parameter) =
        &parsed.arena.get(arrow.parameters.nodes[0]).unwrap().data
    else {
        unreachable!()
    };
    proof
        .annotations
        .push((node_ref(parsed, parameter.type_.unwrap()), element));
    proof
        .locations
        .push((node_ref(parsed, parameter.name), element, Some(observer)));
    let NodeData::Block(body) = &parsed.arena.get(arrow.body).unwrap().data else {
        unreachable!()
    };
    let NodeData::ExpressionStatement(first) =
        &parsed.arena.get(body.statements.nodes[0]).unwrap().data
    else {
        panic!("subscribe must start with the real push statement")
    };
    assert_eq!(node_ref(parsed, first.expression), calls[0]);
    let NodeData::ReturnStatement(returned) = &parsed
        .arena
        .get(*body.statements.nodes.last().unwrap())
        .unwrap()
        .data
    else {
        panic!("subscribe must retain its returned object")
    };
    let returned = node_ref(parsed, returned.expression.unwrap());
    let NodeData::ObjectLiteralExpression(literal) = &parsed.arena.get(returned.node).unwrap().data
    else {
        unreachable!()
    };
    let [property_node] = literal.properties.nodes.as_slice() else {
        panic!("the returned object must contain the reset child")
    };
    let property_node = node_ref(parsed, *property_node);
    let NodeData::PropertyAssignment(property) =
        &parsed.arena.get(property_node.node).unwrap().data
    else {
        unreachable!()
    };
    assert_eq!(node_ref(parsed, property.initializer), reset);
    let returned_type = cached_type(context, returned);
    let property_clone = context
        .store()
        .symbol_table(object(context, returned_type).structured.members.unwrap())
        .unwrap()
        .get_source("unsubscribe")
        .unwrap();
    let property_owner = symbol(context, property_node);
    assert_ne!(property_clone, property_owner);
    let property_record = context.store().symbol(property_clone).unwrap();
    assert_eq!(
        property_record.flags(),
        SymbolFlags::PROPERTY | SymbolFlags::TRANSIENT
    );
    assert_eq!(property_record.declarations(), Some(&[property_node][..]));
    assert_eq!(property_record.value_declaration(), Some(property_node));
    let property_links = context.store().value_symbol_links(property_clone).unwrap();
    assert_eq!(property_links.target, Some(property_owner));
    assert_eq!(
        property_links.resolved_type,
        Some(cached_type(context, reset))
    );
    proof.locations.push((returned, returned_type, None));

    let library_method = library
        .arena
        .iter()
        .find_map(|(node, record)| {
            let NodeData::MethodSignatureDeclaration(method) = &record.data else {
                return None;
            };
            let NodeData::Identifier(name) = &library.arena.get(method.name)?.data else {
                return None;
            };
            if name.text != "push" {
                return None;
            }
            let NodeData::InterfaceDeclaration(interface) =
                &library.arena.get(record.parent?)?.data
            else {
                return None;
            };
            let NodeData::Identifier(owner) = &library.arena.get(interface.name)?.data else {
                return None;
            };
            (owner.text == "Array").then_some(NodeRef::new(library.arena.id(), LIBRARY_FILE, node))
        })
        .unwrap();
    let method_owner = symbol(context, library_method);
    let method = context.store().symbol(method_owner).unwrap();
    assert_eq!(method.flags(), SymbolFlags::METHOD);
    assert_eq!(method.declarations(), Some(&[library_method][..]));
    let array_owner = context
        .store()
        .type_payload(context.global_types().array_type)
        .unwrap()
        .symbol()
        .unwrap();
    assert_eq!(method.parent(), Some(array_owner));
    let source_type = value_type(context, method_owner);
    let source_signature = signature(context, library_method);
    let source_record = context.store().signature(source_signature).unwrap();
    assert_eq!(source_record.declaration(), Some(library_method));
    assert!(source_record.has_rest_parameter());
    let source_element = array_element(context, value_type(context, source_record.parameters()[0]));
    let number = context.store().intrinsic_bootstrap().unwrap().number_type;
    let mut mapped_identity = None;
    for (index, &call) in calls.iter().enumerate() {
        let NodeData::CallExpression(call_data) = &parsed.arena.get(call.node).unwrap().data else {
            unreachable!()
        };
        let callee = node_ref(parsed, call_data.expression);
        let NodeData::PropertyAccessExpression(access) =
            &parsed.arena.get(callee.node).unwrap().data
        else {
            unreachable!()
        };
        let receiver = node_ref(parsed, access.expression);
        let name = node_ref(parsed, access.name);
        assert_eq!(cached_type(context, receiver), array);
        assert_eq!(
            context
                .store()
                .symbol_node_links(receiver)
                .unwrap()
                .resolved_symbol,
            Some(observers)
        );
        assert_eq!(
            context
                .store()
                .symbol_node_links(callee)
                .unwrap()
                .resolved_symbol,
            Some(method_owner)
        );
        let mapped_type = cached_type(context, callee);
        let mapped = object(context, mapped_type);
        assert_eq!(mapped.target, Some(source_type));
        let mapper = mapped.mapper.unwrap();
        assert_eq!(
            context.store().map_type(mapper, source_element),
            Some(element)
        );
        let selected = signature(context, call);
        assert_eq!(
            mapped.structured.signatures.as_deref(),
            Some(&[selected][..])
        );
        let selected_record = context.store().signature(selected).unwrap();
        assert_eq!(selected_record.declaration(), Some(library_method));
        assert_eq!(selected_record.target(), Some(source_signature));
        assert_eq!(selected_record.mapper(), Some(mapper));
        assert!(selected_record.type_parameters().is_empty());
        assert_eq!(selected_record.parameters().len(), 1);
        assert!(selected_record.has_rest_parameter());
        assert_eq!(value_type(context, selected_record.parameters()[0]), array);
        assert_eq!(selected_record.resolved_return_type(), Some(number));
        assert_eq!(cached_type(context, call), number);
        let identity = (mapped_type, selected, mapper);
        if let Some(expected) = mapped_identity {
            assert_eq!(identity, expected);
        }
        mapped_identity = Some(identity);
        let [argument] = call_data.arguments.nodes.as_slice() else {
            panic!("each push must retain its one argument")
        };
        let argument = node_ref(parsed, *argument);
        let argument_type = cached_type(context, argument);
        if index == 0 {
            assert_eq!(argument_type, element);
            assert_eq!(
                context
                    .store()
                    .symbol_node_links(argument)
                    .unwrap()
                    .resolved_symbol,
                Some(observer)
            );
        }
        proof.locations.extend([
            (receiver, array, Some(observers)),
            (callee, mapped_type, Some(method_owner)),
            (name, mapped_type, Some(method_owner)),
            (argument, argument_type, (index == 0).then_some(observer)),
            (call, number, None),
        ]);
        proof.returns.push((selected, number));
        let (_, bound) = context.file(SOURCE_FILE).unwrap();
        assert_eq!(bound.flow_container(call), Some(subscribe));
        let graph = bound.flow_graph().nodes();
        let rows = graph
            .iter()
            .filter(|row| row.payload == Some(FlowNodePayload::Ast(call)))
            .collect::<Vec<_>>();
        assert_eq!(rows.len(), 2);
        assert_eq!(
            rows.iter()
                .filter(|row| row.flags.contains(FlowFlags::ARRAY_MUTATION))
                .count(),
            1
        );
        let call_row = rows
            .iter()
            .find(|row| row.flags.contains(FlowFlags::CALL))
            .unwrap();
        let mutation = graph.get(call_row.antecedent.unwrap()).unwrap();
        assert!(mutation.flags.contains(FlowFlags::ARRAY_MUTATION));
        assert_eq!(mutation.payload, Some(FlowNodePayload::Ast(call)));
    }
    proof.callables.push(state);
}

#[derive(Debug, Eq, PartialEq)]
struct NodeState {
    node: NodeRef,
    common: Option<NodeLinks>,
    symbol: Option<SymbolNodeLinks>,
    type_: Option<TypeNodeLinks>,
    signature: Option<SignatureLinks>,
    array: Option<ArrayLiteralLinks>,
}

#[derive(Debug, Eq, PartialEq)]
struct SymbolState {
    symbol: SemanticSymbolId,
    value: Option<ValueSymbolLinks>,
    declared: Option<DeclaredTypeLinks>,
    alias: Option<TypeAliasLinks>,
    mapped: Option<MappedSymbolLinks>,
    references: Option<SymbolReferenceLinks>,
}

#[derive(Debug, Eq, PartialEq)]
struct Publication {
    counts: [usize; 7],
    nodes: Vec<NodeState>,
    symbols: Vec<SymbolState>,
    source: Option<SourceFileLinks>,
}

fn publication(context: &CanonicalCheckerContext<'_>) -> Publication {
    let store = context.store();
    Publication {
        counts: [
            store.type_len(),
            store.type_alias_len(),
            store.symbol_len(),
            store.signature_len(),
            store.mapper_len(),
            store.index_info_len(),
            store.symbol_store().symbol_table_len(),
        ],
        nodes: context
            .file_order()
            .iter()
            .flat_map(|&file| {
                let (arena, _) = context.file(file).unwrap();
                arena.iter().map(move |(node, _)| {
                    let node = NodeRef::new(arena.id(), file, node);
                    NodeState {
                        node,
                        common: store.node_links(node).cloned(),
                        symbol: store.symbol_node_links(node).cloned(),
                        type_: store.type_node_links(node).cloned(),
                        signature: store.signature_links(node).cloned(),
                        array: store.array_literal_links(node).cloned(),
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
                mapped: store.mapped_symbol_links(symbol).cloned(),
                references: store.symbol_reference_links(symbol).cloned(),
            })
            .collect(),
        source: store
            .source_file_links(context.source_file(SOURCE_FILE).unwrap())
            .cloned(),
    }
}

fn public_queries(context: &mut CanonicalCheckerContext<'_>, proof: &SourceProof) {
    for &(node, type_, symbol) in &proof.locations {
        assert_eq!(context.get_type_at_location(node), Ok(type_), "{node:?}");
        assert_eq!(context.get_symbol_at_location(node), Ok(symbol), "{node:?}");
    }
    for &(node, type_) in &proof.annotations {
        assert_eq!(context.get_type_from_type_node(node), Ok(type_), "{node:?}");
    }
    for &(signature, returned) in &proof.returns {
        assert_eq!(
            context.get_return_type_of_signature(signature),
            Ok(returned)
        );
    }
}

fn check_source(text: &str, call_count: usize, bad_values: bool) {
    let library = parse_source_file(LIBRARY);
    let parsed = parse_source_file(text);
    let mut context = context(&library, &parsed);
    assert!(context.global_type_diagnostics().next().is_none());
    context.check_source_file(SOURCE_FILE).unwrap();
    assert!(
        context
            .store()
            .source_file_links(context.source_file(SOURCE_FILE).unwrap())
            .unwrap()
            .type_checked
    );
    let diagnostics = context.diagnostics().as_slice();
    if bad_values {
        let bad_push = only_node(&parsed, SyntaxKind::StringLiteral);
        let bad_element = only_node(&parsed, SyntaxKind::NumericLiteral);
        assert_eq!(diagnostics.len(), 2, "{diagnostics:?}");
        for (diagnostic, (code, node)) in diagnostics
            .iter()
            .zip([(2345, bad_push), (2322, bad_element)])
        {
            assert_eq!(diagnostic.diagnostic.code(), code);
            assert_eq!(diagnostic.node, Some(node));
            assert_eq!(diagnostic.range_override, None);
            assert_eq!(diagnostic.diagnostic.arguments.len(), 2);
            assert_eq!(diagnostic.diagnostic.arguments[1], "Observer<T>");
            assert!(diagnostic.related_information.is_empty());
        }
        assert_eq!(diagnostics[0].diagnostic.arguments[0], "string");
        assert_eq!(diagnostics[1].diagnostic.arguments[0], "number");
    } else {
        assert!(diagnostics.is_empty(), "{diagnostics:?}");
    }
    let proof = source_proof(&context, &parsed, &library, call_count, bad_values);
    let before = publication(&context);
    let diagnostics = context.diagnostics().as_slice().to_vec();
    public_queries(&mut context, &proof);
    assert_eq!(publication(&context), before);
    for _ in 0..2 {
        context.recheck_source_file(SOURCE_FILE).unwrap();
        assert_eq!(
            source_proof(&context, &parsed, &library, call_count, bad_values),
            proof
        );
        public_queries(&mut context, &proof);
        assert_eq!(context.diagnostics().as_slice(), diagnostics);
        assert_eq!(publication(&context), before);
    }
}

#[test]
fn captured_reset_uses_the_factory_local_declared_array() {
    check_source(
        concat!(
            "type Observer<T> = { next: (value: T) => void; };\n",
            "export default <T>(seed: T): T => {\n",
            "  let _observers: Observer<T>[] = [];\n",
            "  const before = _observers;\n",
            "  const unsubscribe = () => { _observers = []; };\n",
            "  const after = _observers;\n",
            "  return seed;\n",
            "};\n",
        ),
        0,
        false,
    );
}

#[test]
fn call_first_subscribe_keeps_array_method_and_returned_reset_identity() {
    check_source(
        concat!(
            "type Observer<T> = { next: (value: T) => void; };\n",
            "type Subscription = { unsubscribe: () => void; };\n",
            "export default <T>(seed: T): T => {\n",
            "  let _observers: Observer<T>[] = [];\n",
            "  const before = _observers;\n",
            "  const subscribe = (observer: Observer<T>): Subscription => {\n",
            "    _observers.push(observer);\n",
            "    return { unsubscribe: () => { _observers = []; } };\n",
            "  };\n",
            "  const after = _observers;\n",
            "  return seed;\n",
            "};\n",
        ),
        1,
        false,
    );
}

#[test]
fn captured_array_calls_and_writes_report_the_actual_bad_values() {
    check_source(
        concat!(
            "type Observer<T> = { next: (value: T) => void; };\n",
            "type Subscription = { unsubscribe: () => void; };\n",
            "export default <T>(seed: T): T => {\n",
            "  let _observers: Observer<T>[] = [];\n",
            "  const before = _observers;\n",
            "  const subscribe = (observer: Observer<T>): Subscription => {\n",
            "    _observers.push(observer);\n",
            "    _observers.push('bad');\n",
            "    return { unsubscribe: () => { _observers = [1]; } };\n",
            "  };\n",
            "  const after = _observers;\n",
            "  return seed;\n",
            "};\n",
        ),
        2,
        true,
    );
}
