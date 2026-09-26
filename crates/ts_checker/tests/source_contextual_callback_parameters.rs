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

#[derive(Clone, Copy, Debug)]
enum CallbackCallPosition {
    Returned,
    WrappedLocalInitializer,
}

#[allow(clippy::too_many_lines)] // Keep position, owner, diagnostic and replay checks together.
fn check_positioned_callback(position: CallbackCallPosition, bad_argument: bool) {
    let (element, body) = if bad_argument {
        ("(value: string) => void", "task(123);")
    } else {
        ("() => void", "task();")
    };
    let call = format!("originalQueue.forEach((task) => {{ {body} }})");
    let statement = match position {
        CallbackCallPosition::Returned => format!("return {call};"),
        CallbackCallPosition::WrappedLocalInitializer => {
            format!("const completed = ({call}) as void;")
        }
    };
    let source = format!(
        r#"
type NotifyCallback = {element};
type NotifyFunction = (callback: () => void) => void;
export function createNotifyManager(notifyFn: NotifyFunction) {{
    let queue: Array<NotifyCallback> = [];
    const flush = (): void => {{
        const originalQueue = queue;
        {statement}
    }};
    return queue;
}}
"#
    );
    let library = parse_source_file(LIBRARY);
    let parsed = parse_source_file(&source);
    let callback = callback(&parsed);
    let flush_declaration = declaration(&parsed, "flush");
    let NodeData::VariableDeclaration(flush_data) =
        &parsed.arena.get(flush_declaration.node).unwrap().data
    else {
        unreachable!()
    };
    let flush = child(&parsed, flush_declaration, flush_data.initializer.unwrap());
    assert_eq!(
        parsed.arena.get(flush.node).unwrap().kind,
        SyntaxKind::ArrowFunction
    );
    let mut wrapper_locations = Vec::new();
    let result_declaration = match position {
        CallbackCallPosition::Returned => {
            let parent = node(
                &parsed,
                parsed
                    .arena
                    .get(callback.call.node)
                    .unwrap()
                    .parent
                    .unwrap(),
            );
            let NodeData::ReturnStatement(returned) = &parsed.arena.get(parent.node).unwrap().data
            else {
                panic!("the contextual call must remain the returned expression")
            };
            assert_eq!(returned.expression, Some(callback.call.node));
            assert_eq!(child(&parsed, parent, callback.call.node), callback.call);
            None
        }
        CallbackCallPosition::WrappedLocalInitializer => {
            let completed = declaration(&parsed, "completed");
            let NodeData::VariableDeclaration(data) =
                &parsed.arena.get(completed.node).unwrap().data
            else {
                unreachable!()
            };
            assert!(data.type_.is_none());
            let assertion = child(&parsed, completed, data.initializer.unwrap());
            let NodeData::AsExpression(asserted) = &parsed.arena.get(assertion.node).unwrap().data
            else {
                panic!("the local initializer must retain its written assertion")
            };
            let asserted_type = child(&parsed, assertion, asserted.type_);
            assert_eq!(
                parsed.arena.get(asserted_type.node).unwrap().kind,
                SyntaxKind::VoidKeyword
            );
            let parenthesized = child(&parsed, assertion, asserted.expression);
            let NodeData::ParenthesizedExpression(parenthesized_data) =
                &parsed.arena.get(parenthesized.node).unwrap().data
            else {
                panic!("the call must retain its written parentheses")
            };
            assert_eq!(parenthesized_data.expression, callback.call.node);
            assert_eq!(
                child(&parsed, parenthesized, callback.call.node),
                callback.call
            );
            wrapper_locations.extend([
                parenthesized,
                assertion,
                child(&parsed, completed, data.name),
                completed,
            ]);
            Some(completed)
        }
    };

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
            let record = parsed.arena.get(argument.node).unwrap();
            assert_eq!(record.kind, SyntaxKind::NumericLiteral);
            assert_eq!(
                &source[record.range.start.get() as usize..record.range.end.get() as usize],
                "123"
            );
            let [diagnostic] = context.diagnostics().as_slice() else {
                panic!("only the callback's bad argument must fail in {position:?}")
            };
            assert_eq!(diagnostic.node, Some(argument));
            assert_eq!(diagnostic.range_override, None);
            assert_eq!(diagnostic.diagnostic.code(), 2345);
            assert_eq!(diagnostic.diagnostic.arguments, ["number", "string"]);
            assert_eq!(
                diagnostic.diagnostic.render().unwrap(),
                "Argument of type 'number' is not assignable to parameter of type 'string'."
            );
            assert!(diagnostic.diagnostic.details.is_empty());
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
        let void_type = context.store().intrinsic_bootstrap().unwrap().void_type;
        let flush_signature = signature(&context, flush);
        let check_position = |context: &mut CanonicalCheckerContext<'_>| {
            let bound = context.file(SOURCE_FILE).unwrap().1;
            assert_eq!(bound.container(callback.call), Some(flush));
            assert_eq!(bound.container(callback.arrow), Some(flush));
            assert_eq!(
                context.get_return_type_of_signature(flush_signature),
                Ok(void_type)
            );
            for &location in &wrapper_locations {
                assert_eq!(
                    context.get_type_at_location(location),
                    Ok(void_type),
                    "{location:?}"
                );
            }
            if let Some(declaration) = result_declaration {
                assert_eq!(value_type(context, symbol(context, declaration)), void_type);
            }
        };
        check_position(&mut context);
        let before = state(&context);
        for _ in 0..2 {
            context.check_source_file(SOURCE_FILE).unwrap();
            context.recheck_source_file(SOURCE_FILE).unwrap();
            assert_eq!(observe(&mut context, &parsed, &callback), observed);
            check_position(&mut context);
            assert_eq!(state(&context), before);
            assert!(context.store().type_resolution_is_empty());
        }
    }
}

#[test]
fn returned_and_wrapped_local_calls_keep_contextual_callback_types() {
    for position in [
        CallbackCallPosition::Returned,
        CallbackCallPosition::WrappedLocalInitializer,
    ] {
        check_positioned_callback(position, false);
    }
}

#[test]
fn returned_and_wrapped_local_callbacks_keep_native_argument_errors() {
    for position in [
        CallbackCallPosition::Returned,
        CallbackCallPosition::WrappedLocalInitializer,
    ] {
        check_positioned_callback(position, true);
    }
}

fn fixed_parameter_callback(parsed: &ParseResult) -> Callback {
    let mut calls = parsed.arena.iter().filter_map(|(id, record)| {
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
        (name.text == "run").then_some((node(parsed, id), call, property))
    });
    let (call, call_data, property) = calls.next().unwrap();
    assert!(calls.next().is_none());
    let [argument] = call_data.arguments.nodes.as_slice() else {
        panic!("run must retain its one callback argument")
    };
    let arrow = child(parsed, call, *argument);
    let NodeData::ArrowFunction(arrow_data) = &parsed.arena.get(arrow.node).unwrap().data else {
        unreachable!()
    };
    assert!(arrow_data.type_parameters.is_none());
    let [parameter] = arrow_data.parameters.nodes.as_slice() else {
        panic!("the callback must retain its one inferred parameter")
    };
    let parameter = child(parsed, arrow, *parameter);
    let NodeData::ParameterDeclaration(parameter_data) =
        &parsed.arena.get(parameter.node).unwrap().data
    else {
        unreachable!()
    };
    assert!(parameter_data.type_.is_none());
    let name = child(parsed, parameter, parameter_data.name);
    let mut body_calls = parsed.arena.iter().filter_map(|(id, record)| {
        let NodeData::CallExpression(call) = &record.data else {
            return None;
        };
        inside(parsed, id, arrow_data.body).then_some((node(parsed, id), call))
    });
    let (body_call, body_data) = body_calls.next().unwrap();
    assert!(body_calls.next().is_none());
    let callee = child(parsed, call, call_data.expression);
    let body_callee = child(parsed, body_call, body_data.expression);
    Callback {
        call,
        callee,
        receiver: child(parsed, callee, property.expression),
        arrow,
        parameter,
        name,
        usage: body_callee,
        body_call,
        body_callee,
        body_argument: Some(child(parsed, body_call, body_data.arguments.nodes[0])),
    }
}

fn fixed_callback_parameter_annotation(parsed: &ParseResult, function: NodeRef) -> NodeRef {
    let NodeData::FunctionTypeNode(data) = &parsed.arena.get(function.node).unwrap().data else {
        panic!("the inline annotation must keep its function type")
    };
    assert!(data.type_parameters.is_none());
    let [parameter] = data.parameters.nodes.as_slice() else {
        panic!("the fixed function type must keep one parameter")
    };
    let parameter = child(parsed, function, *parameter);
    let NodeData::ParameterDeclaration(data) = &parsed.arena.get(parameter.node).unwrap().data
    else {
        unreachable!()
    };
    child(parsed, parameter, data.type_.unwrap())
}

#[allow(clippy::too_many_lines)] // Follow the fixed parameter's real member and callback owners.
fn check_fixed_parameter_callback(position: CallbackCallPosition, bad_argument: bool) {
    let argument = if bad_argument { "123" } else { "'ok'" };
    let call = format!("runner.run((task) => {{ task({argument}); }})");
    let statement = match position {
        CallbackCallPosition::Returned => format!("return {call};"),
        CallbackCallPosition::WrappedLocalInitializer => {
            format!("const completed = ({call}) as void;")
        }
    };
    let source = format!(
        "export function visit(runner: {{ run: \
         (callback: (task: (value: string) => void) => void) => void }}): void {{\n\
         {statement}\n}}\n"
    );
    let library = parse_source_file(LIBRARY);
    let parsed = parse_source_file(&source);
    let callback = fixed_parameter_callback(&parsed);
    let runner = declaration(&parsed, "runner");
    let NodeData::ParameterDeclaration(runner_data) = &parsed.arena.get(runner.node).unwrap().data
    else {
        unreachable!()
    };
    let receiver_annotation = child(&parsed, runner, runner_data.type_.unwrap());
    let NodeData::TypeLiteralNode(receiver_data) =
        &parsed.arena.get(receiver_annotation.node).unwrap().data
    else {
        unreachable!()
    };
    let [property] = receiver_data.members.nodes.as_slice() else {
        panic!("the receiver must keep its one fixed property")
    };
    let property = child(&parsed, receiver_annotation, *property);
    let NodeData::PropertyDeclaration(property_data) =
        &parsed.arena.get(property.node).unwrap().data
    else {
        unreachable!()
    };
    let callee_annotation = child(&parsed, property, property_data.type_.unwrap());
    let target_annotation = fixed_callback_parameter_annotation(&parsed, callee_annotation);
    let element_annotation = fixed_callback_parameter_annotation(&parsed, target_annotation);
    let outer = node(
        &parsed,
        parsed.arena.get(runner.node).unwrap().parent.unwrap(),
    );
    assert_eq!(
        parsed.arena.get(outer.node).unwrap().kind,
        SyntaxKind::FunctionDeclaration
    );
    let call_parent = parsed
        .arena
        .get(callback.call.node)
        .unwrap()
        .parent
        .unwrap();
    assert_eq!(
        parsed.arena.get(call_parent).unwrap().kind,
        match position {
            CallbackCallPosition::Returned => SyntaxKind::ReturnStatement,
            CallbackCallPosition::WrappedLocalInitializer => SyntaxKind::ParenthesizedExpression,
        }
    );

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
            let record = parsed.arena.get(argument.node).unwrap();
            assert_eq!(record.kind, SyntaxKind::NumericLiteral);
            assert_eq!(
                &source[record.range.start.get() as usize..record.range.end.get() as usize],
                "123"
            );
            let [diagnostic] = context.diagnostics().as_slice() else {
                panic!("only the callback's bad argument must fail")
            };
            assert_eq!(diagnostic.node, Some(argument));
            assert_eq!(diagnostic.range_override, None);
            assert_eq!(diagnostic.diagnostic.code(), 2345);
            assert_eq!(diagnostic.diagnostic.arguments, ["number", "string"]);
            assert_eq!(
                diagnostic.diagnostic.render().unwrap(),
                "Argument of type 'number' is not assignable to parameter of type 'string'."
            );
            assert!(diagnostic.diagnostic.details.is_empty());
            assert!(diagnostic.related_information.is_empty());
        } else {
            assert!(
                context.diagnostics().is_empty(),
                "{:?}",
                context.diagnostics()
            );
        }
        let receiver_type = context.get_type_at_location(receiver_annotation).unwrap();
        let callee_type = context.get_type_at_location(callee_annotation).unwrap();
        let target_type = context.get_type_at_location(target_annotation).unwrap();
        let element_type = context.get_type_at_location(element_annotation).unwrap();
        let owner = symbol(&context, callback.arrow);
        let property_owner = symbol(&context, property);
        let runner_owner = symbol(&context, runner);
        let callable = context.get_type_at_location(callback.arrow).unwrap();
        let void_type = context.store().intrinsic_bootstrap().unwrap().void_type;
        let source_signature = callable_signature(&context, callable);
        let target_signature = callable_signature(&context, target_type);
        assert_ne!(source_signature, target_signature);
        if let Some(early) = early {
            assert_eq!(early, element_type);
        }
        let check = |context: &mut CanonicalCheckerContext<'_>| {
            assert_eq!(value_type(context, runner_owner), receiver_type);
            assert_eq!(value_type(context, property_owner), callee_type);
            assert_eq!(value_type(context, parameter), element_type);
            assert_eq!(value_type(context, owner), callable);
            assert_eq!(
                context.store().type_payload(callable).unwrap().symbol(),
                Some(owner)
            );
            assert_eq!(
                context.get_symbol_at_location(callback.callee),
                Ok(Some(property_owner))
            );
            assert_eq!(
                context.get_type_at_location(callback.receiver),
                Ok(receiver_type)
            );
            assert_eq!(
                context.get_type_at_location(callback.callee),
                Ok(callee_type)
            );
            for location in [callback.parameter, callback.name, callback.usage] {
                assert_eq!(
                    context.get_symbol_at_location(location),
                    Ok(Some(parameter))
                );
                assert_eq!(context.get_type_at_location(location), Ok(element_type));
                assert_eq!(
                    context.file(SOURCE_FILE).unwrap().1.container(location),
                    Some(callback.arrow)
                );
            }
            assert_eq!(
                context
                    .file(SOURCE_FILE)
                    .unwrap()
                    .1
                    .container(callback.call),
                Some(outer)
            );
            let record = context.store().signature(source_signature).unwrap();
            assert_eq!(record.declaration(), Some(callback.arrow));
            assert_eq!(record.parameters(), &[parameter]);
            assert_eq!(record.min_argument_count(), 1);
            assert!(record.type_parameters().is_empty());
            assert_eq!(record.target(), None);
            assert_eq!(record.mapper(), None);
            assert_eq!(
                context.get_return_type_of_signature(source_signature),
                Ok(void_type)
            );
            assert_eq!(
                context.get_return_type_of_signature(target_signature),
                Ok(void_type)
            );
            for (call, declaration) in [
                (callback.call, callee_annotation),
                (callback.body_call, element_annotation),
            ] {
                assert_eq!(context.get_type_at_location(call), Ok(void_type));
                let selected = signature(context, call);
                assert_eq!(
                    context.store().signature(selected).unwrap().declaration(),
                    Some(declaration)
                );
                assert_eq!(
                    context.get_return_type_of_signature(selected),
                    Ok(void_type)
                );
            }
        };
        check(&mut context);
        let before = state(&context);
        for _ in 0..2 {
            context.check_source_file(SOURCE_FILE).unwrap();
            context.recheck_source_file(SOURCE_FILE).unwrap();
            check(&mut context);
            assert_eq!(state(&context), before);
            assert!(context.store().type_resolution_is_empty());
        }
    }
}

#[test]
fn fixed_parameter_callbacks_keep_return_and_initializer_contexts() {
    for position in [
        CallbackCallPosition::Returned,
        CallbackCallPosition::WrappedLocalInitializer,
    ] {
        for bad_argument in [false, true] {
            check_fixed_parameter_callback(position, bad_argument);
        }
    }
}
