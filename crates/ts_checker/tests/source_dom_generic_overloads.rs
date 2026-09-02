use ts_ast::{FileId, NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId, SymbolFlags,
};
use ts_checker::semantic::types::TypeFlags;
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerDiagnostics, CanonicalCheckerOptions,
    IntrinsicBootstrapOptions, SignatureId, SignatureLinks, TypeData, TypeId,
    TypeNodeLinks,
};
use ts_diagnostics::Category;
use ts_parser::{ParseResult, parse_source_file};

const ES5: FileId = FileId::new(311_000);
const DOM: FileId = FileId::new(311_001);
const SOURCE: FileId = FileId::new(311_002);

struct Input {
    file: FileId,
    name: &'static str,
    parsed: ParseResult,
}

struct Inputs([Input; 3]);

impl Inputs {
    fn new(source: &str) -> Self {
        Self(
            [
                (
                    ES5,
                    "/lib.es5.d.ts",
                    include_str!("../../ts_bundled/libs/lib.es5.d.ts"),
                ),
                (
                    DOM,
                    "/lib.dom.d.ts",
                    include_str!("../../ts_bundled/libs/lib.dom.d.ts"),
                ),
                (SOURCE, "/consumer.ts", source),
            ]
            .map(|(file, name, source)| Input {
                file,
                name,
                parsed: parse_source_file(source),
            }),
        )
    }

    fn parsed(&self, file: FileId) -> &ParseResult {
        &self
            .0
            .iter()
            .find(|input| input.file == file)
            .unwrap()
            .parsed
    }

    fn context(&self) -> CanonicalCheckerContext<'_> {
        let mut binder = CanonicalBinder::new();
        for input in &self.0 {
            assert!(
                input.parsed.diagnostics.is_empty(),
                "{}: {:?}",
                input.name,
                input.parsed.diagnostics
            );
            binder
                .bind_source_file_with_facts(
                    &input.parsed.arena,
                    input.parsed.source_file,
                    input.file,
                    CanonicalSourceFileFacts::new_with_default_library(
                        EscapedName::source(input.name),
                        CanonicalSourceLanguage::TypeScript,
                        input.file != SOURCE,
                        input.file != SOURCE,
                        if input.file == SOURCE {
                            CanonicalModuleState::External
                        } else {
                            CanonicalModuleState::Script
                        },
                    ),
                )
                .unwrap();
        }
        for input in &self.0 {
            binder
                .bind_typescript_declaration_slice(&input.parsed.arena, input.file)
                .unwrap();
        }
        let context = CanonicalCheckerContext::new(
            binder.finish(),
            self.0
                .iter()
                .map(|input| (input.file, &input.parsed.arena))
                .collect(),
            CanonicalCheckerOptions {
                no_implicit_any: true,
                strict_function_types: true,
                intrinsic: IntrinsicBootstrapOptions {
                    strict_null_checks: true,
                    exact_optional_property_types: false,
                },
                ..CanonicalCheckerOptions::default()
            },
        )
        .unwrap();
        assert!(context.global_type_diagnostics().next().is_none());
        context
    }
}

#[derive(Debug)]
struct Function {
    declaration: NodeRef,
    name: NodeRef,
    formals: Vec<NodeRef>,
    parameters: Vec<NodeRef>,
}

fn dom_overloads(inputs: &Inputs) -> [Function; 2] {
    let parsed = inputs.parsed(DOM);
    let node_ref = |node| NodeRef::new(parsed.arena.id(), DOM, node);
    let mut functions = parsed
        .arena
        .iter()
        .filter_map(|(node, record)| {
            let NodeData::FunctionDeclaration(function) = &record.data else {
                return None;
            };
            let name = function.name?;
            let NodeData::Identifier(identifier) = &parsed.arena.get(name)?.data else {
                return None;
            };
            (record.parent == Some(parsed.source_file) && identifier.text == "addEventListener")
                .then(|| Function {
                    declaration: node_ref(node),
                    name: node_ref(name),
                    formals: function
                        .type_parameters
                        .as_ref()
                        .map_or_else(Vec::new, |list| {
                            list.nodes.iter().copied().map(node_ref).collect()
                        }),
                    parameters: function
                        .parameters
                        .nodes
                        .iter()
                        .copied()
                        .map(node_ref)
                        .collect(),
                })
        })
        .collect::<Vec<_>>();
    functions.sort_by_key(|function| {
        parsed
            .arena
            .get(function.declaration.node)
            .unwrap()
            .range
            .start
    });
    assert_eq!(functions.len(), 2);
    functions.try_into().unwrap()
}

fn interface(inputs: &Inputs, name: &str) -> NodeRef {
    let parsed = inputs.parsed(DOM);
    parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            let NodeData::InterfaceDeclaration(interface) = &record.data else {
                return None;
            };
            let NodeData::Identifier(identifier) = &parsed.arena.get(interface.name)?.data else {
                return None;
            };
            (record.parent == Some(parsed.source_file) && identifier.text == name)
                .then_some(NodeRef::new(parsed.arena.id(), DOM, node))
        })
        .unwrap()
}

fn source_nodes(inputs: &Inputs, kind: SyntaxKind) -> Vec<NodeRef> {
    let parsed = inputs.parsed(SOURCE);
    let mut nodes = parsed
        .arena
        .iter()
        .filter_map(|(node, record)| {
            (record.kind == kind
                && (kind != SyntaxKind::Identifier
                    || matches!(&record.data, NodeData::Identifier(identifier)
                        if identifier.text == "addEventListener")))
            .then_some(NodeRef::new(parsed.arena.id(), SOURCE, node))
        })
        .collect::<Vec<_>>();
    nodes.sort_by_key(|node| parsed.arena.get(node.node).unwrap().range.start);
    nodes
}

fn annotation(inputs: &Inputs, node: NodeRef) -> NodeRef {
    let parsed = inputs.parsed(node.file);
    let NodeData::ParameterDeclaration(parameter) = &parsed.arena.get(node.node).unwrap().data
    else {
        panic!("expected a written parameter")
    };
    NodeRef::new(node.arena, node.file, parameter.type_.unwrap())
}

fn symbol(context: &CanonicalCheckerContext<'_>, node: NodeRef) -> SemanticSymbolId {
    let raw = context.file(node.file).unwrap().1.symbol(node).unwrap();
    context.store().get_merged_symbol(raw).unwrap()
}

fn signature(context: &CanonicalCheckerContext<'_>, node: NodeRef) -> SignatureId {
    context
        .store()
        .signature_links(node)
        .unwrap()
        .resolved_signature
        .signature()
        .unwrap()
}

fn parameter_types(context: &CanonicalCheckerContext<'_>, signature: SignatureId) -> Vec<TypeId> {
    let store = context.store();
    store
        .signature(signature)
        .unwrap()
        .parameters()
        .iter()
        .map(|&symbol| {
            store
                .value_symbol_links(symbol)
                .unwrap()
                .resolved_type
                .unwrap()
        })
        .collect()
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct Group {
    owner: SemanticSymbolId,
    callable: TypeId,
    signatures: [SignatureId; 2],
    formal: TypeId,
    constraint: TypeId,
    callback: SignatureId,
    receiver: TypeId,
    event: TypeId,
    options: TypeId,
}

#[allow(clippy::too_many_lines)] // Keep each written declaration and its cached metadata together.
fn assert_group(context: &mut CanonicalCheckerContext<'_>, inputs: &Inputs) -> Group {
    let rows = dom_overloads(inputs);
    let owner = symbol(context, rows[0].declaration);
    let callable = context.get_type_at_location(rows[0].name).unwrap();
    let signatures = rows
        .each_ref()
        .map(|row| signature(context, row.declaration));
    assert_eq!(rows[0].formals.len(), 1);
    assert!(rows[1].formals.is_empty());
    let formal_node = rows[0].formals[0];
    let parsed = inputs.parsed(DOM);
    let NodeData::TypeParameterDeclaration(parameter) =
        &parsed.arena.get(formal_node.node).unwrap().data
    else {
        panic!("expected the written K parameter")
    };
    let constraint_node = NodeRef::new(parsed.arena.id(), DOM, parameter.constraint.unwrap());
    let formal = context
        .get_declared_type_of_symbol(symbol(context, formal_node))
        .unwrap();
    let constraint = context.get_type_from_type_node(constraint_node).unwrap();
    let receiver = context
        .get_declared_type_of_symbol(symbol(context, interface(inputs, "Window")))
        .unwrap();
    let event_map = context
        .get_declared_type_of_symbol(symbol(context, interface(inputs, "WindowEventMap")))
        .unwrap();
    let options_record = context
        .get_declared_type_of_symbol(symbol(
            context,
            interface(inputs, "AddEventListenerOptions"),
        ))
        .unwrap();
    let options_base = context
        .get_type_from_type_node(annotation(inputs, rows[0].parameters[2]))
        .unwrap();
    let fallback_listener = context
        .get_type_from_type_node(annotation(inputs, rows[1].parameters[1]))
        .unwrap();
    let store = context.store();
    let owner_record = store.symbol(owner).unwrap();
    assert_eq!(
        owner_record.flags().without(SymbolFlags::TRANSIENT),
        SymbolFlags::FUNCTION
    );
    assert!(owner_record.parent().is_none());
    assert!(owner_record.exports().is_none());
    assert_eq!(
        owner_record.declarations(),
        Some(&rows.each_ref().map(|row| row.declaration)[..])
    );
    assert_eq!(owner_record.value_declaration(), Some(rows[0].declaration));
    let TypeData::Object(object) = store.type_payload(callable).unwrap().data() else {
        panic!("the two global declarations must share one callable object")
    };
    assert_eq!(object.structured.call_signature_count, 2);
    assert_eq!(
        object.structured.signatures.as_deref(),
        Some(&signatures[..])
    );
    assert!(object.structured.members.is_none());
    let bootstrap = store.intrinsic_bootstrap().unwrap();
    for (index, row) in rows.iter().enumerate() {
        assert_eq!(symbol(context, row.declaration), owner);
        let signature = store.signature(signatures[index]).unwrap();
        assert_eq!(signature.declaration(), Some(row.declaration));
        assert_eq!(signature.parameters().len(), 3);
        assert_eq!(signature.min_argument_count(), 2);
        assert_eq!(signature.type_parameters().len(), usize::from(index == 0));
        assert_eq!(signature.resolved_return_type(), Some(bootstrap.void_type));
        assert!(!signature.has_rest_parameter());
        assert!(signature.this_parameter().is_none());
        assert!(signature.target().is_none());
        assert!(signature.mapper().is_none());
        assert_eq!(
            signature.parameters(),
            row.parameters
                .iter()
                .map(|&node| symbol(context, node))
                .collect::<Vec<_>>()
        );
    }
    assert_eq!(
        store.signature(signatures[0]).unwrap().type_parameters(),
        [formal]
    );
    let TypeData::TypeParameter(parameter) = store.type_payload(formal).unwrap().data() else {
        panic!("K must retain its declared type parameter")
    };
    assert_eq!(parameter.constraint, Some(constraint));
    assert!(!parameter.is_this_type);
    assert!(parameter.target.is_none());
    assert!(parameter.mapper.is_none());
    let TypeData::Union(keys) = store.type_payload(constraint).unwrap().data() else {
        panic!("keyof WindowEventMap must keep its finite event-name union")
    };
    assert!(!keys.union.types.is_empty());
    assert!(keys.union.types.iter().all(|&key| {
        store
            .type_payload(key)
            .unwrap()
            .flags()
            .contains(TypeFlags::STRING_LITERAL)
    }));
    let generic_types = parameter_types(context, signatures[0]);
    let fallback_types = parameter_types(context, signatures[1]);
    assert_eq!(generic_types[0], formal);
    assert_eq!(fallback_types[0], bootstrap.string_type);
    assert_eq!(fallback_types[1], fallback_listener);
    let TypeData::Object(callback_object) = store.type_payload(generic_types[1]).unwrap().data()
    else {
        panic!("the listener must keep its written function type")
    };
    assert_eq!(callback_object.structured.call_signature_count, 1);
    let [callback] = callback_object.structured.signatures.as_deref().unwrap() else {
        panic!("the listener must retain one callback signature")
    };
    let callback = *callback;
    let callback_record = store.signature(callback).unwrap();
    assert_eq!(
        callback_record.declaration(),
        Some(annotation(inputs, rows[0].parameters[1]))
    );
    assert_eq!(callback_record.parameters().len(), 1);
    assert_eq!(callback_record.min_argument_count(), 1);
    assert!(callback_record.type_parameters().is_empty());
    assert!(!callback_record.has_rest_parameter());
    assert_eq!(
        callback_record.resolved_return_type(),
        Some(bootstrap.any_type)
    );
    let this = callback_record.this_parameter().unwrap();
    assert_eq!(store.symbol(this).unwrap().name().as_utf8(), Some("this"));
    assert_eq!(
        store.value_symbol_links(this).unwrap().resolved_type,
        Some(receiver)
    );
    let event = parameter_types(context, callback)[0];
    let TypeData::IndexedAccess(indexed) = store.type_payload(event).unwrap().data() else {
        panic!("the callback event must retain WindowEventMap[K]")
    };
    assert_eq!(indexed.object_type, event_map);
    assert_eq!(indexed.index_type, formal);
    let TypeData::Union(base) = store.type_payload(options_base).unwrap().data() else {
        panic!("the written options must retain boolean and AddEventListenerOptions")
    };
    let boolean_parts = match store.type_payload(bootstrap.boolean_type).unwrap().data() {
        TypeData::Union(boolean) => boolean.union.types.as_slice(),
        _ => std::slice::from_ref(&bootstrap.boolean_type),
    };
    assert_eq!(base.union.types.len(), boolean_parts.len() + 1);
    assert!(base.union.types.contains(&options_record));
    assert!(
        boolean_parts
            .iter()
            .all(|part| base.union.types.contains(part))
    );
    let options = generic_types[2];
    assert_eq!(fallback_types[2], options);
    let TypeData::Union(optional) = store.type_payload(options).unwrap().data() else {
        panic!("the optional options parameter must add undefined")
    };
    assert_eq!(optional.union.types.len(), base.union.types.len() + 1);
    assert!(optional.union.types.contains(&bootstrap.undefined_type));
    assert!(
        base.union
            .types
            .iter()
            .all(|part| optional.union.types.contains(part))
    );
    Group {
        owner,
        callable,
        signatures,
        formal,
        constraint,
        callback,
        receiver,
        event,
        options,
    }
}

#[derive(Debug, Eq, PartialEq)]
struct Snapshot {
    counts: [usize; 4],
    group: Group,
    nodes: Vec<(Option<TypeNodeLinks>, Option<SignatureLinks>)>,
    diagnostics: CanonicalCheckerDiagnostics,
}

fn snapshot(context: &CanonicalCheckerContext<'_>, nodes: &[NodeRef], group: &Group) -> Snapshot {
    let store = context.store();
    Snapshot {
        counts: [
            store.type_len(),
            store.symbol_len(),
            store.signature_len(),
            store.mapper_len(),
        ],
        group: group.clone(),
        nodes: nodes
            .iter()
            .map(|&node| {
                (
                    store.type_node_links(node).cloned(),
                    store.signature_links(node).cloned(),
                )
            })
            .collect(),
        diagnostics: context.diagnostics().clone(),
    }
}

#[test]
fn dom_generic_global_overloads_keep_written_types_and_cold_warm_replay() {
    let inputs = Inputs::new("export {};\nconst listener = addEventListener;\n");
    let reads = source_nodes(&inputs, SyntaxKind::Identifier);
    assert_eq!(reads.len(), 1);
    for read_first in [false, true] {
        let mut context = inputs.context();
        for row in dom_overloads(&inputs) {
            assert!(
                context
                    .store()
                    .signature_links(row.declaration)
                    .is_none_or(|links| links.resolved_signature.signature().is_none())
            );
        }
        let cold = read_first.then(|| context.get_type_at_location(reads[0]).unwrap());
        context.check_source_file(SOURCE).unwrap();
        let group = assert_group(&mut context, &inputs);
        assert_eq!(context.get_type_at_location(reads[0]), Ok(group.callable));
        if let Some(cold) = cold {
            assert_eq!(cold, group.callable);
        }
        assert!(
            context.diagnostics().is_empty(),
            "{:?}",
            context.diagnostics()
        );
        let before = snapshot(&context, &reads, &group);
        for _ in 0..2 {
            context.check_source_file(SOURCE).unwrap();
            context.recheck_source_file(SOURCE).unwrap();
            assert_eq!(assert_group(&mut context, &inputs), group);
            assert_eq!(context.get_type_at_location(reads[0]), Ok(group.callable));
            assert_eq!(snapshot(&context, &reads, &group), before);
        }
    }
}

#[test]
fn dom_generic_global_overloads_keep_native_constraint_and_listener_errors() {
    let inputs = Inputs::new(
        r"
export {};
declare function callback(): void;
addEventListener<number>('click', callback);
addEventListener<'click'>('click', 123);
",
    );
    let calls = source_nodes(&inputs, SyntaxKind::CallExpression);
    assert_eq!(calls.len(), 2);
    let mut context = inputs.context();
    context.check_source_file(SOURCE).unwrap();
    let group = assert_group(&mut context, &inputs);
    let parsed = inputs.parsed(SOURCE);
    let NodeData::CallExpression(constraint_call) = &parsed.arena.get(calls[0].node).unwrap().data
    else {
        panic!("expected the explicit constraint call")
    };
    let NodeData::CallExpression(listener_call) = &parsed.arena.get(calls[1].node).unwrap().data
    else {
        panic!("expected the explicit listener call")
    };
    let expected = [
        (
            2344,
            NodeRef::new(
                parsed.arena.id(),
                SOURCE,
                constraint_call.type_arguments.as_ref().unwrap().nodes[0],
            ),
            ["number", "keyof WindowEventMap"],
            "Type 'number' does not satisfy the constraint 'keyof WindowEventMap'.",
        ),
        (
            2345,
            NodeRef::new(parsed.arena.id(), SOURCE, listener_call.arguments.nodes[1]),
            ["number", "(this: Window, ev: PointerEvent) => any"],
            "Argument of type 'number' is not assignable to parameter of type '(this: Window, ev: PointerEvent) => any'.",
        ),
    ];
    assert_eq!(context.diagnostics().len(), expected.len());
    for (diagnostic, (code, node, arguments, message)) in
        context.diagnostics().as_slice().iter().zip(expected)
    {
        assert_eq!(diagnostic.diagnostic.code(), code);
        assert_eq!(diagnostic.diagnostic.category(), Category::Error);
        assert_eq!(diagnostic.node, Some(node));
        assert_eq!(diagnostic.diagnostic.arguments, arguments);
        assert_eq!(diagnostic.diagnostic.render().unwrap(), message);
        assert!(diagnostic.range_override.is_none());
        assert!(diagnostic.related_information.is_empty());
    }
    let before = snapshot(&context, &calls, &group);
    for _ in 0..2 {
        context.check_source_file(SOURCE).unwrap();
        context.recheck_source_file(SOURCE).unwrap();
        assert_eq!(assert_group(&mut context, &inputs), group);
        assert_eq!(snapshot(&context, &calls, &group), before);
    }
}
