use ts_ast::{FileId, NodeData, NodeId, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId, SymbolFlags,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, IntrinsicBootstrapOptions, SignatureId,
    TypeData, TypeId, signatures::SignatureFlags,
};
use ts_parser::{ParseResult, parse_source_file};

const LIBRARY_FILE: FileId = FileId::new(205_730);
const SOURCE_FILE: FileId = FileId::new(205_731);
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
            "\"/project/contextual-callback-parameters.ts\"",
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
            no_implicit_any: true,
            strict_function_types: true,
            ..CanonicalCheckerOptions::default()
        },
    )
    .unwrap()
}

fn node(parsed: &ParseResult, id: NodeId) -> NodeRef {
    NodeRef::new(parsed.arena.id(), SOURCE_FILE, id)
}

fn child(parsed: &ParseResult, parent: NodeRef, id: NodeId) -> NodeRef {
    let record = parsed.arena.get(id).unwrap();
    let owner = parsed.arena.get(parent.node).unwrap();
    assert_eq!(record.parent, Some(parent.node));
    assert!(owner.range.start <= record.range.start);
    assert!(record.range.end <= owner.range.end);
    node(parsed, id)
}

fn inside(parsed: &ParseResult, mut candidate: NodeId, parent: NodeId) -> bool {
    loop {
        if candidate == parent {
            return true;
        }
        let Some(next) = parsed.arena.get(candidate).unwrap().parent else {
            return false;
        };
        candidate = next;
    }
}

fn declaration(parsed: &ParseResult, expected: &str) -> NodeRef {
    let mut matches = parsed.arena.iter().filter_map(|(id, record)| {
        let name = match &record.data {
            NodeData::VariableDeclaration(data) => data.name,
            NodeData::TypeAliasDeclaration(data) => data.name,
            NodeData::ParameterDeclaration(data) => data.name,
            _ => return None,
        };
        let NodeData::Identifier(name) = &parsed.arena.get(name)?.data else {
            return None;
        };
        (name.text == expected).then_some(node(parsed, id))
    });
    let result = matches
        .next()
        .unwrap_or_else(|| panic!("missing declaration {expected}"));
    assert!(
        matches.next().is_none(),
        "expected one declaration {expected}"
    );
    result
}

fn symbol(context: &CanonicalCheckerContext<'_>, declaration: NodeRef) -> SemanticSymbolId {
    let raw = context
        .file(SOURCE_FILE)
        .unwrap()
        .1
        .symbol(declaration)
        .unwrap();
    context.store().get_merged_symbol(raw).unwrap()
}

fn value_type(context: &CanonicalCheckerContext<'_>, symbol: SemanticSymbolId) -> TypeId {
    context
        .store()
        .value_symbol_links(symbol)
        .and_then(|links| links.resolved_type)
        .expect("the real symbol must retain its resolved type")
}

fn signature(context: &CanonicalCheckerContext<'_>, location: NodeRef) -> SignatureId {
    context
        .store()
        .signature_links(location)
        .and_then(|links| links.resolved_signature.signature())
        .expect("the actual declaration or call must retain its signature")
}

fn callable_signature(context: &CanonicalCheckerContext<'_>, type_: TypeId) -> SignatureId {
    let TypeData::Object(object) = context.store().type_payload(type_).unwrap().data() else {
        panic!("the callback must keep its real callable type")
    };
    let [signature] = object.structured.signatures.as_deref().unwrap() else {
        panic!("the callback must keep its one call signature")
    };
    assert_eq!(object.structured.call_signature_count, 1);
    *signature
}

struct Callback {
    call: NodeRef,
    callee: NodeRef,
    receiver: NodeRef,
    arrow: NodeRef,
    parameter: NodeRef,
    name: NodeRef,
    usage: NodeRef,
    body_call: NodeRef,
    body_callee: NodeRef,
    body_argument: Option<NodeRef>,
}

fn callback(parsed: &ParseResult) -> Callback {
    let mut matches = parsed.arena.iter().filter_map(|(id, record)| {
        let NodeData::CallExpression(call) = &record.data else {
            return None;
        };
        let NodeData::PropertyAccessExpression(property) = &parsed.arena.get(call.expression)?.data
        else {
            return None;
        };
        let NodeData::Identifier(name) = &parsed.arena.get(property.name)?.data else {
            return None;
        };
        (name.text == "forEach").then_some((node(parsed, id), call, property))
    });
    let (call, call_data, property) = matches.next().expect("the real forEach call");
    assert!(matches.next().is_none());
    let [arrow] = call_data.arguments.nodes.as_slice() else {
        panic!("forEach must keep its one callback argument")
    };
    let arrow = child(parsed, call, *arrow);
    let NodeData::ArrowFunction(arrow_data) = &parsed.arena.get(arrow.node).unwrap().data else {
        panic!("the forEach argument must remain an arrow")
    };
    assert!(arrow_data.type_.is_none());
    assert!(arrow_data.type_parameters.is_none());
    let [parameter] = arrow_data.parameters.nodes.as_slice() else {
        panic!("this control has one inferred callback parameter")
    };
    let parameter = child(parsed, arrow, *parameter);
    let NodeData::ParameterDeclaration(parameter_data) =
        &parsed.arena.get(parameter.node).unwrap().data
    else {
        panic!("the callback must keep its actual parameter")
    };
    assert!(parameter_data.type_.is_none());
    assert!(parameter_data.initializer.is_none());
    assert!(parameter_data.question_token.is_none());
    assert!(parameter_data.dot_dot_dot_token.is_none());
    let name = child(parsed, parameter, parameter_data.name);
    let NodeData::Identifier(parameter_name) = &parsed.arena.get(name.node).unwrap().data else {
        panic!("the inferred parameter must be an identifier")
    };
    let body = child(parsed, arrow, arrow_data.body);
    assert_eq!(parsed.arena.get(body.node).unwrap().kind, SyntaxKind::Block);
    let mut body_calls = parsed.arena.iter().filter_map(|(id, record)| {
        let NodeData::CallExpression(call) = &record.data else {
            return None;
        };
        inside(parsed, id, body.node).then_some((node(parsed, id), call))
    });
    let (body_call, body_data) = body_calls.next().unwrap();
    assert!(body_calls.next().is_none());
    let mut uses = parsed.arena.iter().filter_map(|(id, record)| {
        let NodeData::Identifier(identifier) = &record.data else {
            return None;
        };
        (identifier.text == parameter_name.text && inside(parsed, id, body.node))
            .then_some(node(parsed, id))
    });
    let usage = uses
        .next()
        .expect("the body must use its inferred parameter");
    assert!(uses.next().is_none());
    let callee = child(parsed, call, call_data.expression);
    Callback {
        call,
        callee,
        receiver: child(parsed, callee, property.expression),
        arrow,
        parameter,
        name,
        usage,
        body_call,
        body_callee: child(parsed, body_call, body_data.expression),
        body_argument: body_data
            .arguments
            .nodes
            .first()
            .map(|&id| child(parsed, body_call, id)),
    }
}

#[derive(Debug, Eq, PartialEq)]
struct Observation {
    parameter_type: TypeId,
    parameter: SemanticSymbolId,
    array: TypeId,
    callable: TypeId,
    source_signature: SignatureId,
    method: SemanticSymbolId,
    call_signature: SignatureId,
    body_signature: SignatureId,
}

fn observe(
    context: &mut CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    callback: &Callback,
) -> Observation {
    let alias = declaration(parsed, "NotifyCallback");
    let NodeData::TypeAliasDeclaration(alias_data) = &parsed.arena.get(alias.node).unwrap().data
    else {
        unreachable!()
    };
    let alias_rhs = child(parsed, alias, alias_data.type_);
    let parameter_type = context.get_type_at_location(alias_rhs).unwrap();
    let element_signature = callable_signature(context, parameter_type);
    assert_eq!(
        context
            .store()
            .signature(element_signature)
            .unwrap()
            .declaration(),
        Some(alias_rhs)
    );
    let void_type = context.store().intrinsic_bootstrap().unwrap().void_type;
    assert_eq!(
        context.get_return_type_of_signature(element_signature),
        Ok(void_type)
    );
    let queue = declaration(parsed, "queue");
    let original_queue = declaration(parsed, "originalQueue");
    let array = value_type(context, symbol(context, queue));
    assert_eq!(value_type(context, symbol(context, original_queue)), array);
    let TypeData::TypeReference(reference) = context.store().type_payload(array).unwrap().data()
    else {
        panic!("the local queue must keep its declared Array reference")
    };
    assert_eq!(
        reference.object.target,
        Some(context.global_types().array_type)
    );
    assert_eq!(
        reference.resolved_type_arguments.as_deref(),
        Some(&[parameter_type][..])
    );
    assert_eq!(context.get_type_at_location(callback.receiver), Ok(array));
    assert_eq!(
        context.get_symbol_at_location(callback.receiver),
        Ok(Some(symbol(context, original_queue)))
    );

    let owner = symbol(context, callback.arrow);
    let parameter = symbol(context, callback.parameter);
    let callable = context.get_type_at_location(callback.arrow).unwrap();
    assert_eq!(
        context.store().symbol(owner).unwrap().flags(),
        SymbolFlags::FUNCTION
    );
    assert_eq!(
        context.store().symbol(owner).unwrap().declarations(),
        Some(&[callback.arrow][..])
    );
    assert_eq!(
        context.store().symbol(owner).unwrap().value_declaration(),
        Some(callback.arrow)
    );
    assert_eq!(value_type(context, owner), callable);
    assert_eq!(
        context.store().type_payload(callable).unwrap().symbol(),
        Some(owner)
    );
    assert_eq!(
        context.store().symbol(parameter).unwrap().flags(),
        SymbolFlags::FUNCTION_SCOPED_VARIABLE
    );
    assert_eq!(
        context.store().symbol(parameter).unwrap().declarations(),
        Some(&[callback.parameter][..])
    );
    assert_eq!(value_type(context, parameter), parameter_type);
    for location in [callback.parameter, callback.name, callback.usage] {
        assert_eq!(
            context.get_symbol_at_location(location),
            Ok(Some(parameter))
        );
        assert_eq!(context.get_type_at_location(location), Ok(parameter_type));
        assert_eq!(
            context.file(SOURCE_FILE).unwrap().1.container(location),
            Some(callback.arrow)
        );
    }
    let source_signature = signature(context, callback.arrow);
    assert_eq!(callable_signature(context, callable), source_signature);
    assert_eq!(
        context.get_return_type_of_signature(source_signature),
        Ok(void_type)
    );
    let record = context.store().signature(source_signature).unwrap();
    assert_eq!(record.declaration(), Some(callback.arrow));
    assert_eq!(record.flags(), SignatureFlags::NONE);
    assert_eq!(record.parameters(), &[parameter]);
    assert_eq!(record.min_argument_count(), 1);
    assert_eq!(record.resolved_return_type(), Some(void_type));
    assert!(record.type_parameters().is_empty());
    assert_eq!(record.target(), None);
    assert_eq!(record.mapper(), None);

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
        .get_source("forEach")
        .unwrap();
    assert_eq!(
        context.store().symbol(method).unwrap().flags(),
        SymbolFlags::METHOD
    );
    assert_eq!(
        context.get_symbol_at_location(callback.callee),
        Ok(Some(method))
    );
    let call_signature = signature(context, callback.call);
    assert_eq!(
        context.get_return_type_of_signature(call_signature),
        Ok(void_type)
    );
    let record = context.store().signature(call_signature).unwrap();
    let method_declaration = record.declaration().unwrap();
    assert_eq!(method_declaration.file, LIBRARY_FILE);
    assert!(
        context
            .store()
            .symbol(method)
            .unwrap()
            .declarations()
            .unwrap()
            .contains(&method_declaration)
    );
    assert_eq!(record.parameters().len(), 2);
    assert_eq!(record.min_argument_count(), 1);
    assert!(!record.has_rest_parameter());
    assert_eq!(context.get_type_at_location(callback.call), Ok(void_type));
    assert_eq!(
        context.get_type_at_location(callback.body_call),
        Ok(void_type)
    );
    let body_signature = signature(context, callback.body_call);
    assert_eq!(
        context.get_return_type_of_signature(body_signature),
        Ok(void_type)
    );
    if callback.body_callee != callback.usage {
        let notify = declaration(parsed, "notifyFn");
        let notify_symbol = symbol(context, notify);
        assert_eq!(
            context.get_symbol_at_location(callback.body_callee),
            Ok(Some(notify_symbol))
        );
        assert_eq!(
            context.get_type_at_location(callback.body_callee),
            Ok(value_type(context, notify_symbol))
        );
    }
    Observation {
        parameter_type,
        parameter,
        array,
        callable,
        source_signature,
        method,
        call_signature,
        body_signature,
    }
}

fn state(context: &CanonicalCheckerContext<'_>) -> impl std::fmt::Debug + PartialEq + use<> {
    let store = context.store();
    (
        [
            store.type_len(),
            store.type_alias_len(),
            store.symbol_len(),
            store.signature_len(),
            store.mapper_len(),
            store.index_info_len(),
            store.symbol_store().symbol_table_len(),
        ],
        context.diagnostics().clone(),
        store
            .source_file_links(context.source_file(SOURCE_FILE).unwrap())
            .cloned(),
        context
            .file_order()
            .iter()
            .flat_map(|&file| {
                let arena = context.file(file).unwrap().0;
                arena.iter().map(move |(id, _)| {
                    let node = NodeRef::new(arena.id(), file, id);
                    (
                        node,
                        store.node_links(node).cloned(),
                        store.type_node_links(node).cloned(),
                        store.symbol_node_links(node).cloned(),
                        store.signature_links(node).cloned(),
                        store.array_literal_links(node).cloned(),
                    )
                })
            })
            .collect::<Vec<_>>(),
        store
            .symbol_store()
            .symbols()
            .map(|(symbol, record)| {
                (
                    symbol,
                    record.flags(),
                    record.declarations().map(<[_]>::to_vec),
                    record.value_declaration(),
                    store.value_symbol_links(symbol).cloned(),
                    store.declared_type_links(symbol).cloned(),
                    store.type_alias_links(symbol).cloned(),
                    store.mapped_symbol_links(symbol).cloned(),
                    store.symbol_reference_links(symbol).cloned(),
                )
            })
            .collect::<Vec<_>>(),
    )
}

fn check_program(element: &str, name: &str, body: &str, bad_argument: bool) {
    // Keep the captured queue and nested flush from notifyManager's forEach context.
    let source = format!(
        r#"
type NotifyCallback = {element};
type NotifyFunction = (callback: () => void) => void;
export function createNotifyManager(notifyFn: NotifyFunction) {{
    let queue: Array<NotifyCallback> = [];
    const flush = (): void => {{
        const originalQueue = queue;
        originalQueue.forEach(({name}) => {{ {body} }});
    }};
    return queue;
}}
"#
    );
    let library = parse_source_file(LIBRARY);
    let parsed = parse_source_file(&source);
    let callback = callback(&parsed);
    for query_first in [false, true] {
        let mut context = context(&library, &parsed);
        assert!(context.global_type_diagnostics().next().is_none());
        let parameter = symbol(&context, callback.parameter);
        assert!(context.store().value_symbol_links(parameter).is_none());
        assert!(context.store().signature_links(callback.arrow).is_none());
        let early = if query_first {
            Some(context.get_type_at_location(callback.name).unwrap())
        } else {
            context.check_source_file(SOURCE_FILE).unwrap();
            None
        };
        if bad_argument {
            let argument = callback.body_argument.unwrap();
            let node = parsed.arena.get(argument.node).unwrap();
            assert_eq!(node.kind, SyntaxKind::NumericLiteral);
            assert_eq!(
                &source[node.range.start.get() as usize..node.range.end.get() as usize],
                "123"
            );
            let [diagnostic] = context.diagnostics().as_slice() else {
                panic!("only the bad callback body argument must fail")
            };
            assert_eq!(diagnostic.node, Some(argument));
            assert_eq!(diagnostic.range_override, None);
            assert_eq!(diagnostic.diagnostic.code(), 2345);
            assert_eq!(
                diagnostic.diagnostic.render().unwrap(),
                "Argument of type 'number' is not assignable to parameter of type 'string'."
            );
            assert!(diagnostic.related_information.is_empty());
        } else {
            assert!(
                context.diagnostics().is_empty(),
                "{:?}",
                context.diagnostics()
            );
        }
        let observed = observe(&mut context, &parsed, &callback);
        if let Some(early) = early {
            assert_eq!(early, observed.parameter_type);
        }
        let before = state(&context);
        for _ in 0..2 {
            context.check_source_file(SOURCE_FILE).unwrap();
            context.recheck_source_file(SOURCE_FILE).unwrap();
            assert_eq!(observe(&mut context, &parsed, &callback), observed);
            assert_eq!(state(&context), before);
            assert!(context.store().type_resolution_is_empty());
        }
    }
}

#[test]
fn notify_queue_for_each_infers_the_callback_type_and_keeps_its_owner() {
    check_program("() => void", "callback", "notifyFn(callback);", false);
}

#[test]
fn for_each_can_call_the_renamed_inferred_callback() {
    check_program("() => void", "task", "task();", false);
}

#[test]
fn for_each_checks_arguments_inside_the_contextually_typed_callback() {
    check_program("(value: string) => void", "task", "task(123);", true);
}
