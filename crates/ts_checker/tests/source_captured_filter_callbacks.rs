use ts_ast::{FileId, NodeData, NodeId, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId, SymbolFlags,
};
use ts_checker::semantic::{
    ArrayLiteralLinks, CanonicalCheckerContext, CanonicalCheckerOptions, DeclaredTypeLinks,
    IntrinsicBootstrapOptions, MappedSymbolLinks, NodeLinks, SignatureId, SignatureLinks,
    SourceFileLinks, SymbolNodeLinks, SymbolReferenceLinks, TypeAliasLinks, TypeData, TypeId,
    TypeNodeLinks, ValueSymbolLinks, signatures::SignatureFlags, types::TypeFlags,
};
use ts_parser::{ParseResult, parse_source_file};

const LIBRARY_FILE: FileId = FileId::new(8_280);
const SOURCE_FILE: FileId = FileId::new(8_281);
const LIBRARY: &str = include_str!("../../ts_bundled/libs/lib.es5.d.ts");
const SOURCE: &str = concat!(
    "type Observer<T> = { next: (value: T) => void; };\n",
    "type Subscription = { unsubscribe: () => void; };\n",
    "export default <T>(seed: T): T => {\n",
    "  let _observers: Observer<T>[] = [];\n",
    "  const subscribe = (observer: Observer<T>): Subscription => {\n",
    "    _observers.push(observer);\n",
    "    return {\n",
    "      unsubscribe: () => {\n",
    "        _observers = _observers.filter((o) => o !== observer);\n",
    "      },\n",
    "    };\n",
    "  };\n",
    "  return seed;\n",
    "};\n",
);

fn context<'arena>(
    library: &'arena ParseResult,
    source: &'arena ParseResult,
) -> CanonicalCheckerContext<'arena> {
    let files = [
        (LIBRARY_FILE, library, "\"/lib/lib.es5.d.ts\"", true),
        (
            SOURCE_FILE,
            source,
            "\"/project/captured-filter.ts\"",
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
            no_implicit_any: true,
            ..CanonicalCheckerOptions::default()
        },
    )
    .unwrap()
}

fn reference(parsed: &ParseResult, node: NodeId) -> NodeRef {
    NodeRef::new(parsed.arena.id(), SOURCE_FILE, node)
}

fn variable(parsed: &ParseResult, expected: &str) -> NodeRef {
    let mut nodes = parsed.arena.iter().filter_map(|(node, record)| {
        let NodeData::VariableDeclaration(variable) = &record.data else {
            return None;
        };
        let NodeData::Identifier(name) = &parsed.arena.get(variable.name)?.data else {
            return None;
        };
        (name.text == expected).then_some(reference(parsed, node))
    });
    let node = nodes.next().expect("the named variable must exist");
    assert!(nodes.next().is_none());
    node
}

fn symbol(context: &CanonicalCheckerContext<'_>, node: NodeRef) -> SemanticSymbolId {
    let symbol = context.file(node.file).unwrap().1.symbol(node).unwrap();
    context.store().get_merged_symbol(symbol).unwrap()
}

fn cached_type(context: &CanonicalCheckerContext<'_>, node: NodeRef) -> TypeId {
    context
        .store()
        .type_node_links(node)
        .and_then(|links| links.resolved_type)
        .unwrap_or_else(|| panic!("missing checked type at {node:?}"))
}

fn value_type(context: &CanonicalCheckerContext<'_>, symbol: SemanticSymbolId) -> TypeId {
    context
        .store()
        .value_symbol_links(symbol)
        .and_then(|links| links.resolved_type)
        .unwrap()
}

fn signature(context: &CanonicalCheckerContext<'_>, node: NodeRef) -> SignatureId {
    context
        .store()
        .signature_links(node)
        .and_then(|links| links.resolved_signature.signature())
        .unwrap()
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

#[test]
#[allow(clippy::too_many_lines)] // Follow the real nested callback through source, call, and replay queries.
fn captured_filter_keeps_the_generic_receiver_and_outer_observer() {
    let library = parse_source_file(LIBRARY);
    let parsed = parse_source_file(SOURCE);
    let mut context = context(&library, &parsed);
    assert!(context.global_type_diagnostics().next().is_none());
    let call = parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            let NodeData::CallExpression(call) = &record.data else {
                return None;
            };
            let NodeData::PropertyAccessExpression(access) =
                &parsed.arena.get(call.expression)?.data
            else {
                return None;
            };
            let NodeData::Identifier(name) = &parsed.arena.get(access.name)?.data else {
                return None;
            };
            (name.text == "filter").then_some(reference(&parsed, node))
        })
        .unwrap();
    let NodeData::CallExpression(call_data) = &parsed.arena.get(call.node).unwrap().data else {
        unreachable!()
    };
    let [callback] = call_data.arguments.nodes.as_slice() else {
        panic!("filter must retain its one original callback")
    };
    let callback = reference(&parsed, *callback);
    let NodeData::ArrowFunction(arrow) = &parsed.arena.get(callback.node).unwrap().data else {
        unreachable!()
    };
    let [parameter] = arrow.parameters.nodes.as_slice() else {
        panic!("the callback must retain its one unannotated parameter")
    };
    let parameter = reference(&parsed, *parameter);
    let NodeData::ParameterDeclaration(parameter_data) =
        &parsed.arena.get(parameter.node).unwrap().data
    else {
        unreachable!()
    };
    assert_eq!(parameter_data.type_, None);
    let parameter_symbol = symbol(&context, parameter);
    let callback_owner = symbol(&context, callback);
    assert!(context.store().type_node_links(callback).is_none());
    assert!(context.store().signature_links(callback).is_none());
    assert!(
        context
            .store()
            .value_symbol_links(parameter_symbol)
            .is_none()
    );

    context.check_source_file(SOURCE_FILE).unwrap();

    assert!(
        context.diagnostics().is_empty(),
        "{:?}",
        context.diagnostics()
    );
    let observers_node = variable(&parsed, "_observers");
    let observers_symbol = symbol(&context, observers_node);
    let array_type = value_type(&context, observers_symbol);
    let array = context
        .store()
        .canonical_array_reference(context.global_types(), array_type)
        .unwrap()
        .unwrap();
    assert!(!array.readonly);
    let observer_type = array.element_type;
    let subscribe_node = variable(&parsed, "subscribe");
    let NodeData::VariableDeclaration(subscribe) =
        &parsed.arena.get(subscribe_node.node).unwrap().data
    else {
        unreachable!()
    };
    let subscribe = reference(&parsed, subscribe.initializer.unwrap());
    let NodeData::ArrowFunction(subscribe_data) = &parsed.arena.get(subscribe.node).unwrap().data
    else {
        unreachable!()
    };
    let observer = reference(&parsed, subscribe_data.parameters.nodes[0]);
    let observer_symbol = symbol(&context, observer);
    assert_ne!(parameter_symbol, observer_symbol);
    assert_eq!(value_type(&context, parameter_symbol), observer_type);
    assert_eq!(value_type(&context, observer_symbol), observer_type);
    let observer_record = context.store().type_payload(observer_type).unwrap();
    assert!(
        !observer_record
            .flags()
            .intersects(TypeFlags::ANY | TypeFlags::UNKNOWN)
    );
    let alias = context
        .store()
        .type_alias(observer_record.alias().unwrap())
        .unwrap();
    let [t] = alias.type_arguments().unwrap() else {
        panic!("Observer<T> must keep the factory parameter")
    };
    let t = *t;
    let t_owner = context.store().type_payload(t).unwrap().symbol().unwrap();
    let t_declaration = context
        .store()
        .symbol(t_owner)
        .unwrap()
        .declarations()
        .unwrap()[0];
    let factory = reference(
        &parsed,
        parsed
            .arena
            .get(t_declaration.node)
            .unwrap()
            .parent
            .unwrap(),
    );
    let NodeData::ArrowFunction(factory_data) = &parsed.arena.get(factory.node).unwrap().data
    else {
        panic!("T must remain owned by the actual outer arrow")
    };
    assert_eq!(
        factory_data.type_parameters.as_ref().unwrap().nodes,
        [t_declaration.node]
    );
    let (alias_declaration, alias_parameter) = parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            let NodeData::TypeAliasDeclaration(declaration) = &record.data else {
                return None;
            };
            let NodeData::Identifier(name) = &parsed.arena.get(declaration.name)?.data else {
                return None;
            };
            (name.text == "Observer").then(|| {
                (
                    reference(&parsed, node),
                    reference(
                        &parsed,
                        declaration.type_parameters.as_ref().unwrap().nodes[0],
                    ),
                )
            })
        })
        .unwrap();
    let alias_owner = symbol(&context, alias_declaration);
    let alias_parameter_owner = symbol(&context, alias_parameter);
    let alias_t = context
        .store()
        .declared_type_links(alias_parameter_owner)
        .unwrap()
        .declared_type
        .unwrap();
    assert_eq!(alias.symbol(), Some(alias_owner));
    assert_eq!(
        context
            .store()
            .type_alias_links(alias_owner)
            .unwrap()
            .type_parameters
            .as_deref(),
        Some(&[alias_t][..])
    );
    assert_eq!(
        context.store().type_payload(alias_t).unwrap().symbol(),
        Some(alias_parameter_owner)
    );
    assert_eq!(
        parsed.arena.get(alias_parameter.node).unwrap().parent,
        Some(alias_declaration.node)
    );
    assert_ne!(alias_t, t);
    assert_eq!(
        context.store().type_payload(t).unwrap().flags(),
        TypeFlags::TYPE_PARAMETER
    );

    let comparison = reference(&parsed, arrow.body);
    let NodeData::BinaryExpression(binary) = &parsed.arena.get(comparison.node).unwrap().data
    else {
        panic!("the original callback comparison must remain unchanged")
    };
    assert_eq!(
        parsed.arena.get(binary.operator_token).unwrap().kind,
        SyntaxKind::ExclamationEqualsEqualsToken
    );
    let callback_read = reference(&parsed, binary.left);
    let captured_read = reference(&parsed, binary.right);
    let boolean = context.store().intrinsic_bootstrap().unwrap().boolean_type;
    assert_eq!(cached_type(&context, callback_read), observer_type);
    assert_eq!(cached_type(&context, captured_read), observer_type);
    assert_eq!(cached_type(&context, comparison), boolean);
    let callback_type = cached_type(&context, callback);
    assert_eq!(value_type(&context, callback_owner), callback_type);
    assert_eq!(
        context
            .store()
            .type_payload(callback_type)
            .unwrap()
            .symbol(),
        Some(callback_owner)
    );
    let callback_signature = signature(&context, callback);
    let record = context.store().signature(callback_signature).unwrap();
    assert_eq!(record.declaration(), Some(callback));
    assert_eq!(record.parameters(), [parameter_symbol]);
    assert_eq!(record.flags(), SignatureFlags::NONE);
    assert_eq!(record.min_argument_count(), 1);
    assert!(record.type_parameters().is_empty());
    assert_eq!(record.resolved_return_type(), Some(boolean));
    assert_eq!(record.resolved_type_predicate(), None);

    let callee = reference(&parsed, call_data.expression);
    let NodeData::PropertyAccessExpression(access) = &parsed.arena.get(callee.node).unwrap().data
    else {
        unreachable!()
    };
    let receiver = reference(&parsed, access.expression);
    let assignment = reference(
        &parsed,
        parsed.arena.get(call.node).unwrap().parent.unwrap(),
    );
    let NodeData::BinaryExpression(assigned) = &parsed.arena.get(assignment.node).unwrap().data
    else {
        panic!("filter must remain the captured assignment's right-hand side")
    };
    assert_eq!(assigned.right, call.node);
    let assignment_target = reference(&parsed, assigned.left);
    assert_eq!(cached_type(&context, receiver), array_type);
    assert_eq!(cached_type(&context, assignment_target), array_type);
    assert_eq!(cached_type(&context, call), array_type);
    assert_eq!(cached_type(&context, assignment), array_type);
    let (_, bound) = context.file(SOURCE_FILE).unwrap();
    let writer = bound.container(call).unwrap();
    assert_eq!(bound.flow_container(assignment_target), Some(writer));
    assert_ne!(writer, factory);
    assert_ne!(writer, subscribe);
    assert_ne!(writer, callback);
    assert_eq!(bound.container(observer), Some(subscribe));
    let array_owner = context
        .store()
        .type_payload(context.global_types().array_type)
        .unwrap()
        .symbol()
        .unwrap();
    let members = context
        .store()
        .symbol(array_owner)
        .unwrap()
        .members()
        .unwrap();
    let method = context
        .store()
        .symbol_table(members)
        .unwrap()
        .get_source("filter")
        .unwrap();
    assert_eq!(
        context.store().symbol(method).unwrap().flags(),
        SymbolFlags::METHOD
    );
    let selected = signature(&context, call);
    let selected_record = context.store().signature(selected).unwrap();
    assert!(
        context
            .store()
            .symbol(method)
            .unwrap()
            .declarations()
            .unwrap()
            .contains(&selected_record.declaration().unwrap())
    );
    assert_eq!(selected_record.resolved_return_type(), Some(array_type));

    let locations = [
        (callback_read, observer_type, Some(parameter_symbol)),
        (captured_read, observer_type, Some(observer_symbol)),
        (receiver, array_type, Some(observers_symbol)),
        (assignment_target, array_type, Some(observers_symbol)),
        (callee, cached_type(&context, callee), Some(method)),
        (callback, callback_type, None),
        (comparison, boolean, None),
        (call, array_type, None),
        (assignment, array_type, None),
    ];
    let warm = publication(&context);
    for _ in 0..2 {
        for (node, type_, symbol) in locations {
            assert_eq!(context.get_type_at_location(node), Ok(type_), "{node:?}");
            assert_eq!(context.get_symbol_at_location(node), Ok(symbol), "{node:?}");
        }
        assert_eq!(
            context.get_return_type_of_signature(callback_signature),
            Ok(boolean)
        );
        assert_eq!(
            context.get_return_type_of_signature(selected),
            Ok(array_type)
        );
        assert_eq!(publication(&context), warm);
        context.recheck_source_file(SOURCE_FILE).unwrap();
        assert!(context.diagnostics().is_empty());
        assert_eq!(publication(&context), warm);
    }
}
