use ts_ast::{FileId, NodeData, NodeId, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId, SymbolFlags,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, IntrinsicBootstrapOptions, SignatureId,
    SignatureLinks, SourceFileLinks, SymbolNodeLinks, TypeData, TypeId, TypeNodeLinks,
};
use ts_parser::{ParseResult, parse_source_file};

const LIBRARY_FILE: FileId = FileId::new(9_420);
const SOURCE_FILE: FileId = FileId::new(9_421);
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
            "\"/project/captured-array-statement-lists.ts\"",
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

fn node_ref(parsed: &ParseResult, node: NodeId) -> NodeRef {
    NodeRef::new(parsed.arena.id(), SOURCE_FILE, node)
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
        .unwrap_or_else(|| panic!("missing checked type at {node:?}"))
}

fn array_element(context: &CanonicalCheckerContext<'_>, type_: TypeId) -> TypeId {
    let TypeData::TypeReference(array) = context.store().type_payload(type_).unwrap().data()
    else {
        panic!("expected a canonical Array reference")
    };
    assert_eq!(array.object.target, Some(context.global_types().array_type));
    let [element] = array.resolved_type_arguments.as_deref().unwrap() else {
        panic!("Array must retain one element type")
    };
    *element
}

enum Element {
    Callback,
    Number,
    String,
}

fn assert_element(context: &CanonicalCheckerContext<'_>, type_: TypeId, expected: &Element) {
    let bootstrap = context.store().intrinsic_bootstrap().unwrap();
    match expected {
        Element::Number => assert_eq!(type_, bootstrap.number_type),
        Element::String => assert_eq!(type_, bootstrap.string_type),
        Element::Callback => {
            let TypeData::Object(callback) = context.store().type_payload(type_).unwrap().data()
            else {
                panic!("NotifyCallback must keep its real function type")
            };
            assert_eq!(callback.structured.call_signature_count, 1);
            let [signature] = callback.structured.signatures.as_deref().unwrap() else {
                panic!("NotifyCallback must have one call signature")
            };
            let signature = context.store().signature(*signature).unwrap();
            assert!(signature.parameters().is_empty());
            assert_eq!(signature.resolved_return_type(), Some(bootstrap.void_type));
        }
    }
}

#[derive(Debug, Eq, PartialEq)]
struct Queue {
    declaration: NodeRef,
    owner: SemanticSymbolId,
    container: NodeRef,
    name: NodeRef,
    annotation: NodeRef,
    type_: TypeId,
    element: TypeId,
}

fn queues(context: &CanonicalCheckerContext<'_>, parsed: &ParseResult) -> Vec<Queue> {
    let (_, bound) = context.file(SOURCE_FILE).unwrap();
    parsed
        .arena
        .iter()
        .filter_map(|(node, record)| {
            let NodeData::VariableDeclaration(variable) = &record.data else {
                return None;
            };
            let NodeData::Identifier(name) = &parsed.arena.get(variable.name)?.data else {
                return None;
            };
            if name.text != "queue" {
                return None;
            }
            let declaration = node_ref(parsed, node);
            let owner = symbol(context, declaration);
            let record = context.store().symbol(owner).unwrap();
            assert_eq!(record.flags(), SymbolFlags::BLOCK_SCOPED_VARIABLE);
            assert_eq!(record.declarations(), Some(&[declaration][..]));
            assert_eq!(record.value_declaration(), Some(declaration));
            let type_ = value_type(context, owner);
            let annotation = node_ref(parsed, variable.type_.unwrap());
            assert_eq!(cached_type(context, annotation), type_);
            Some(Queue {
                declaration,
                owner,
                container: bound.container(declaration).unwrap(),
                name: node_ref(parsed, variable.name),
                annotation,
                type_,
                element: array_element(context, type_),
            })
        })
        .collect()
}

#[derive(Debug, Eq, PartialEq)]
struct Push {
    call: NodeRef,
    receiver: NodeRef,
    argument: NodeRef,
    signature: SignatureId,
    queue: usize,
}

fn assert_call_scope(
    context: &CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    call: NodeRef,
    queue: &Queue,
    captured: bool,
) {
    let (_, bound) = context.file(SOURCE_FILE).unwrap();
    let callable = bound.container(call).unwrap();
    assert_eq!(parsed.arena.get(callable.node).unwrap().kind, SyntaxKind::ArrowFunction);
    assert_eq!(callable != queue.container, captured);
    if captured {
        assert_eq!(
            parsed.arena.get(queue.container.node).unwrap().kind,
            SyntaxKind::FunctionDeclaration
        );
        assert_eq!(bound.container(callable), Some(queue.container));
    }
    let statement = parsed.arena.get(call.node).unwrap().parent.unwrap();
    let record = parsed.arena.get(statement).unwrap();
    let NodeData::ExpressionStatement(expression) = &record.data else {
        panic!("the push must remain an expression statement")
    };
    assert_eq!(expression.expression, call.node);
    let block = record.parent.unwrap();
    let record = parsed.arena.get(block).unwrap();
    assert_eq!(record.kind, SyntaxKind::Block);
    assert_eq!(bound.block_scope_container(call), Some(node_ref(parsed, block)));
    let conditional = parsed.arena.get(record.parent.unwrap()).unwrap();
    assert_eq!(conditional.kind, SyntaxKind::IfStatement);
}

fn pushes(
    context: &CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    queues: &[Queue],
    expected: &[(usize, bool)],
) -> Vec<Push> {
    let number = context.store().intrinsic_bootstrap().unwrap().number_type;
    let calls = parsed
        .arena
        .iter()
        .filter_map(|(node, record)| {
            let NodeData::CallExpression(call) = &record.data else {
                return None;
            };
            Some((node_ref(parsed, node), call))
        })
        .collect::<Vec<_>>();
    assert_eq!(calls.len(), expected.len());
    calls
        .into_iter()
        .zip(expected)
        .map(|((node, call), &(queue, captured))| {
            let NodeData::PropertyAccessExpression(access) =
                &parsed.arena.get(call.expression).unwrap().data
            else {
                panic!("expected the real queue.push call")
            };
            let NodeData::Identifier(name) = &parsed.arena.get(access.name).unwrap().data else {
                unreachable!()
            };
            assert_eq!(name.text, "push");
            let receiver = node_ref(parsed, access.expression);
            let binding = &queues[queue];
            assert_eq!(cached_type(context, receiver), binding.type_);
            assert_eq!(
                context
                    .store()
                    .symbol_node_links(receiver)
                    .unwrap()
                    .resolved_symbol,
                Some(binding.owner)
            );
            assert_call_scope(context, parsed, node, binding, captured);
            let [argument] = call.arguments.nodes.as_slice() else {
                panic!("each push must retain one argument")
            };
            let signature = context
                .store()
                .signature_links(node)
                .unwrap()
                .resolved_signature
                .signature()
                .unwrap();
            let record = context.store().signature(signature).unwrap();
            assert_eq!(record.declaration().unwrap().file, LIBRARY_FILE);
            assert!(record.target().is_some());
            assert!(record.mapper().is_some());
            assert!(record.has_rest_parameter());
            assert_eq!(record.parameters().len(), 1);
            assert_eq!(value_type(context, record.parameters()[0]), binding.type_);
            assert_eq!(record.resolved_return_type(), Some(number));
            assert_eq!(cached_type(context, node), number);
            Push {
                call: node,
                receiver,
                argument: node_ref(parsed, *argument),
                signature,
                queue,
            }
        })
        .collect()
}

#[derive(Debug, Eq, PartialEq)]
struct NodePublication {
    node: NodeRef,
    type_: Option<TypeNodeLinks>,
    symbol: Option<SymbolNodeLinks>,
    signature: Option<SignatureLinks>,
}

#[derive(Debug, Eq, PartialEq)]
struct Publication {
    counts: [usize; 7],
    nodes: Vec<NodePublication>,
    source: Option<SourceFileLinks>,
}

fn publication(context: &CanonicalCheckerContext<'_>, parsed: &ParseResult) -> Publication {
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
        nodes: parsed
            .arena
            .iter()
            .map(|(node, _)| {
                let node = node_ref(parsed, node);
                NodePublication {
                    node,
                    type_: store.type_node_links(node).cloned(),
                    symbol: store.symbol_node_links(node).cloned(),
                    signature: store.signature_links(node).cloned(),
                }
            })
            .collect(),
        source: store
            .source_file_links(context.source_file(SOURCE_FILE).unwrap())
            .cloned(),
    }
}

fn public_queries(context: &mut CanonicalCheckerContext<'_>, queues: &[Queue], pushes: &[Push]) {
    let number = context.store().intrinsic_bootstrap().unwrap().number_type;
    for queue in queues {
        assert_eq!(
            context.get_type_from_type_node(queue.annotation),
            Ok(queue.type_)
        );
        assert_eq!(context.get_type_at_location(queue.name), Ok(queue.type_));
        assert_eq!(
            context.get_symbol_at_location(queue.name),
            Ok(Some(queue.owner))
        );
    }
    for push in pushes {
        let queue = &queues[push.queue];
        assert_eq!(context.get_type_at_location(push.receiver), Ok(queue.type_));
        assert_eq!(
            context.get_symbol_at_location(push.receiver),
            Ok(Some(queue.owner))
        );
        assert_eq!(context.get_type_at_location(push.call), Ok(number));
        assert_eq!(
            context.get_return_type_of_signature(push.signature),
            Ok(number)
        );
    }
}

fn check_source(
    text: &str,
    elements: &[Element],
    expected_calls: &[(usize, bool)],
    errors: &[(usize, &str, &str)],
) {
    let library = parse_source_file(LIBRARY);
    let parsed = parse_source_file(text);
    let mut context = context(&library, &parsed);
    assert!(context.global_type_diagnostics().next().is_none());
    context.check_source_file(SOURCE_FILE).unwrap();
    let bindings = queues(&context, &parsed);
    assert_eq!(bindings.len(), elements.len());
    for (binding, element) in bindings.iter().zip(elements) {
        assert_element(&context, binding.element, element);
    }
    for pair in bindings.windows(2) {
        assert_ne!(pair[0].owner, pair[1].owner);
        assert_ne!(pair[0].container, pair[1].container);
        assert_ne!(pair[0].type_, pair[1].type_);
    }
    let calls = pushes(&context, &parsed, &bindings, expected_calls);
    let diagnostics = context.diagnostics().as_slice().to_vec();
    assert_eq!(diagnostics.len(), errors.len(), "{diagnostics:?}");
    for (diagnostic, &(call, source, target)) in diagnostics.iter().zip(errors) {
        assert_eq!(diagnostic.diagnostic.code(), 2345);
        assert_eq!(diagnostic.node, Some(calls[call].argument));
        assert_eq!(diagnostic.range_override, None);
        assert_eq!(
            diagnostic.diagnostic.arguments,
            [source.to_owned(), target.to_owned()]
        );
        assert!(diagnostic.related_information.is_empty());
    }
    let before = publication(&context, &parsed);
    assert!(before.source.as_ref().unwrap().type_checked);
    public_queries(&mut context, &bindings, &calls);
    assert_eq!(publication(&context, &parsed), before);
    context.check_source_file(SOURCE_FILE).unwrap();
    assert_eq!(context.diagnostics().as_slice(), diagnostics);
    assert_eq!(publication(&context, &parsed), before);
    for _ in 0..2 {
        context.recheck_source_file(SOURCE_FILE).unwrap();
        assert_eq!(queues(&context, &parsed), bindings);
        assert_eq!(pushes(&context, &parsed, &bindings, expected_calls), calls);
        public_queries(&mut context, &bindings, &calls);
        assert_eq!(context.diagnostics().as_slice(), diagnostics);
        assert_eq!(publication(&context, &parsed), before);
    }
}

#[test]
fn captured_queue_push_in_an_if_list_uses_the_outer_function_declaration() {
    check_source(
        r"
type NotifyCallback = () => void;
export function createNotifyManager() {
    let queue: Array<NotifyCallback> = [];
    let transactions = 0;
    const schedule = (callback: NotifyCallback): void => {
        if (transactions) {
            queue.push(callback);
        }
    };
    return queue;
}
",
        &[Element::Callback],
        &[(0, true)],
        &[],
    );
}

#[test]
fn an_inner_queue_keeps_its_own_element_type_and_binding() {
    check_source(
        r"
type NotifyCallback = () => void;
export function createNotifyManager() {
    let queue: Array<NotifyCallback> = [];
    let transactions = 0;
    const schedule = (callback: NotifyCallback): void => {
        if (transactions) {
            queue.push(callback);
        }
    };
    const local = (value: number, active: boolean): void => {
        let queue: number[] = [];
        if (active) {
            queue.push(value);
        }
    };
    return queue;
}
",
        &[Element::Callback, Element::Number],
        &[(0, true), (1, false)],
        &[],
    );
}

#[test]
fn captured_and_shadowed_push_arguments_keep_their_real_diagnostics() {
    check_source(
        r"
export function createNotifyManager() {
    let queue: number[] = [];
    const schedule = (active: boolean): void => {
        if (active) {
            queue.push('bad');
        }
    };
    const local = (active: boolean): void => {
        let queue: string[] = [];
        if (active) {
            queue.push(1);
        }
    };
    return queue;
}
",
        &[Element::Number, Element::String],
        &[(0, true), (1, false)],
        &[(0, "string", "number"), (1, "number", "string")],
    );
}
