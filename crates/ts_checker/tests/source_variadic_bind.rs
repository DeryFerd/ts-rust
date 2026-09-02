use ts_ast::{FileId, NodeData, NodeId, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId, SymbolFlags,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, IntrinsicBootstrapOptions, SignatureId,
    TypeData, TypeId, signatures::ElementFlags,
};
use ts_parser::{ParseResult, parse_source_file};

const LIBRARY: FileId = FileId::new(203_124);
const FILE: FileId = FileId::new(203_125);
const ES5: &str = include_str!("../../ts_bundled/libs/lib.es5.d.ts");

struct Fixture {
    library: ParseResult,
    source: ParseResult,
}

impl Fixture {
    fn new(source: &str) -> Self {
        let library = parse_source_file(ES5);
        let source = parse_source_file(source);
        assert!(library.diagnostics.is_empty(), "{:?}", library.diagnostics);
        assert!(source.diagnostics.is_empty(), "{:?}", source.diagnostics);
        Self { library, source }
    }

    fn context(&self) -> CanonicalCheckerContext<'_> {
        let files = [(LIBRARY, &self.library), (FILE, &self.source)];
        let mut binder = CanonicalBinder::new();
        for (file, parsed) in files {
            let library = file == LIBRARY;
            binder
                .bind_source_file_with_facts(
                    &parsed.arena,
                    parsed.source_file,
                    file,
                    CanonicalSourceFileFacts::new_with_default_library(
                        EscapedName::source(if library {
                            "\"/lib/lib.es5.d.ts\""
                        } else {
                            "\"/project/variadic-bind.ts\""
                        }),
                        CanonicalSourceLanguage::TypeScript,
                        library,
                        library,
                        CanonicalModuleState::Script,
                    ),
                )
                .unwrap();
        }
        for (file, parsed) in files {
            binder
                .bind_typescript_declaration_slice(&parsed.arena, file)
                .unwrap();
        }
        CanonicalCheckerContext::new(
            binder.finish(),
            files
                .into_iter()
                .map(|(file, parsed)| (file, &parsed.arena))
                .collect(),
            CanonicalCheckerOptions {
                intrinsic: IntrinsicBootstrapOptions {
                    strict_null_checks: true,
                    ..IntrinsicBootstrapOptions::default()
                },
                strict_bind_call_apply: true,
                strict_function_types: true,
                strict_property_initialization: true,
                no_implicit_any: true,
                no_implicit_this: true,
                ..CanonicalCheckerOptions::default()
            },
        )
        .unwrap()
    }
}

fn node(parsed: &ParseResult, file: FileId, id: NodeId) -> NodeRef {
    NodeRef::new(parsed.arena.id(), file, id)
}

fn nodes(parsed: &ParseResult, kind: SyntaxKind) -> Vec<NodeRef> {
    let mut nodes = parsed
        .arena
        .iter()
        .filter_map(|(id, record)| (record.kind == kind).then_some(node(parsed, FILE, id)))
        .collect::<Vec<_>>();
    nodes.sort_by_key(|node| parsed.arena.get(node.node).unwrap().range.start);
    nodes
}

fn only(parsed: &ParseResult, kind: SyntaxKind) -> NodeRef {
    let nodes = nodes(parsed, kind);
    let [node] = nodes.as_slice() else {
        panic!("expected one source {kind:?}")
    };
    *node
}

fn symbol(context: &CanonicalCheckerContext<'_>, declaration: NodeRef) -> SemanticSymbolId {
    let raw = context
        .file(declaration.file)
        .unwrap()
        .1
        .symbol(declaration)
        .unwrap();
    context.store().get_merged_symbol(raw).unwrap()
}

fn signature(context: &CanonicalCheckerContext<'_>, declaration: NodeRef) -> SignatureId {
    context
        .store()
        .signature_links(declaration)
        .and_then(|links| links.resolved_signature.signature())
        .unwrap()
}

fn call_parts(parsed: &ParseResult, call: NodeRef) -> (NodeRef, Vec<NodeRef>) {
    let NodeData::CallExpression(data) = &parsed.arena.get(call.node).unwrap().data else {
        panic!("expected the source call")
    };
    (
        node(parsed, FILE, data.expression),
        data.arguments
            .nodes
            .iter()
            .map(|&id| node(parsed, FILE, id))
            .collect(),
    )
}

fn counts(context: &CanonicalCheckerContext<'_>) -> (usize, usize, usize, usize) {
    let store = context.store();
    (
        store.type_len(),
        store.symbol_len(),
        store.signature_len(),
        store.mapper_len(),
    )
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Method {
    formal: TypeId,
    type_: TypeId,
    signature: SignatureId,
    parameters: [NodeRef; 3],
}

fn assert_method(
    fixture: &Fixture,
    context: &mut CanonicalCheckerContext<'_>,
    method_access: NodeRef,
) -> Method {
    let declaration = only(&fixture.source, SyntaxKind::MethodDeclaration);
    let owner = symbol(context, only(&fixture.source, SyntaxKind::ClassDeclaration));
    let formal_symbol = symbol(context, only(&fixture.source, SyntaxKind::TypeParameter));
    let formal = context.get_declared_type_of_symbol(formal_symbol).unwrap();
    assert_eq!(
        context.store().type_payload(formal).unwrap().symbol(),
        Some(formal_symbol)
    );
    assert_eq!(
        context.store().symbol(formal_symbol).unwrap().parent(),
        Some(owner)
    );
    let method_symbol = symbol(context, declaration);
    let member = context.store().symbol(method_symbol).unwrap();
    assert_eq!(member.flags(), SymbolFlags::METHOD);
    assert_eq!(member.parent(), Some(owner));
    assert_eq!(member.value_declaration(), Some(declaration));
    let type_ = context.get_type_at_location(method_access).unwrap();
    assert_eq!(
        context
            .store()
            .value_symbol_links(method_symbol)
            .unwrap()
            .resolved_type,
        Some(type_)
    );
    let signature = signature(context, declaration);
    let record = context.store().signature(signature).unwrap();
    assert!(record.type_parameters().is_empty());
    assert_eq!(record.this_parameter(), None);
    assert!(!record.has_rest_parameter());
    assert_eq!(record.parameters().len(), 3);
    assert_eq!(record.min_argument_count(), 3);
    assert_eq!(record.resolved_return_type(), Some(formal));
    let NodeData::MethodDeclaration(method) =
        &fixture.source.arena.get(declaration.node).unwrap().data
    else {
        unreachable!()
    };
    let parameters: [NodeRef; 3] = method
        .parameters
        .nodes
        .iter()
        .map(|&id| node(&fixture.source, FILE, id))
        .collect::<Vec<_>>()
        .try_into()
        .unwrap();
    let bootstrap = context.store().intrinsic_bootstrap().unwrap();
    for ((&parameter, declaration), expected) in record.parameters().iter().zip(parameters).zip([
        formal,
        bootstrap.string_type,
        bootstrap.number_type,
    ]) {
        assert_eq!(parameter, symbol(context, declaration));
        assert_eq!(
            context
                .store()
                .value_symbol_links(parameter)
                .unwrap()
                .resolved_type,
            Some(expected)
        );
    }
    Method {
        formal,
        type_,
        signature,
        parameters,
    }
}

fn library_bind(fixture: &Fixture) -> (NodeRef, [NodeRef; 2], NodeRef) {
    fixture
        .library
        .arena
        .iter()
        .find_map(|(id, record)| {
            let NodeData::InterfaceDeclaration(interface) = &record.data else {
                return None;
            };
            let NodeData::Identifier(name) = &fixture.library.arena.get(interface.name)?.data
            else {
                return None;
            };
            if name.text != "CallableFunction" {
                return None;
            }
            let declarations: [NodeRef; 2] = interface
                .members
                .nodes
                .iter()
                .filter_map(|&id| {
                    let NodeData::MethodSignatureDeclaration(method) =
                        &fixture.library.arena.get(id)?.data
                    else {
                        return None;
                    };
                    let NodeData::Identifier(name) = &fixture.library.arena.get(method.name)?.data
                    else {
                        return None;
                    };
                    (name.text == "bind").then_some(node(&fixture.library, LIBRARY, id))
                })
                .collect::<Vec<_>>()
                .try_into()
                .unwrap();
            let NodeData::MethodSignatureDeclaration(second) =
                &fixture.library.arena.get(declarations[1].node)?.data
            else {
                unreachable!()
            };
            let returned = node(&fixture.library, LIBRARY, second.type_.unwrap());
            assert_eq!(
                fixture.library.arena.get(returned.node)?.kind,
                SyntaxKind::FunctionType
            );
            Some((node(&fixture.library, LIBRARY, id), declarations, returned))
        })
        .unwrap()
}

fn assert_tuple(
    context: &CanonicalCheckerContext<'_>,
    type_: TypeId,
    elements: &[TypeId],
    labels: Option<&[NodeRef]>,
) {
    let store = context.store();
    let TypeData::TypeReference(reference) = store.type_payload(type_).unwrap().data() else {
        panic!("a nonempty inferred tuple must retain its canonical reference")
    };
    assert_eq!(reference.resolved_type_arguments.as_deref(), Some(elements));
    let TypeData::Tuple(tuple) = store
        .type_payload(reference.object.target.unwrap())
        .unwrap()
        .data()
    else {
        panic!("the inferred arguments must use a tuple target")
    };
    assert_eq!(tuple.metadata.min_length(), elements.len());
    assert_eq!(tuple.metadata.fixed_length(), elements.len());
    assert!(!tuple.metadata.is_readonly());
    assert!(
        tuple
            .metadata
            .element_infos()
            .iter()
            .all(|info| info.flags() == ElementFlags::REQUIRED)
    );
    if let Some(labels) = labels {
        assert_eq!(
            tuple
                .metadata
                .element_infos()
                .iter()
                .map(|info| info.labeled_declaration())
                .collect::<Vec<_>>(),
            labels.iter().copied().map(Some).collect::<Vec<_>>()
        );
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Binding {
    method: Method,
    selected: SignatureId,
    result: TypeId,
    returned: SignatureId,
    prefix: TypeId,
    remaining: TypeId,
}

fn assert_binding(
    fixture: &Fixture,
    context: &mut CanonicalCheckerContext<'_>,
    call: NodeRef,
) -> Binding {
    let (callee, arguments) = call_parts(&fixture.source, call);
    assert_eq!(arguments.len(), 2);
    let NodeData::PropertyAccessExpression(access) =
        &fixture.source.arena.get(callee.node).unwrap().data
    else {
        panic!("expected the actual bind access")
    };
    let method_access = node(&fixture.source, FILE, access.expression);
    let method = assert_method(fixture, context, method_access);
    assert_eq!(
        context.get_type_at_location(arguments[1]),
        Ok(method.formal)
    );
    let (owner, declarations, returned_node) = library_bind(fixture);
    let bind_symbol = symbol(context, declarations[0]);
    assert_eq!(symbol(context, declarations[1]), bind_symbol);
    assert_eq!(
        context.store().symbol(bind_symbol).unwrap().parent(),
        Some(symbol(context, owner))
    );
    assert_eq!(
        context
            .get_symbol_at_location(node(&fixture.source, FILE, access.name))
            .unwrap(),
        Some(bind_symbol)
    );
    assert_eq!(
        context
            .get_declared_type_of_symbol(symbol(context, owner))
            .unwrap(),
        context.global_types().callable_function_type
    );
    let original = signature(context, declarations[1]);
    let formals = context
        .store()
        .signature(original)
        .unwrap()
        .type_parameters()
        .to_vec();
    assert_eq!(formals.len(), 4);
    let selected = signature(context, call);
    let selected_record = context.store().signature(selected).unwrap();
    assert_eq!(selected_record.declaration(), Some(declarations[1]));
    assert_eq!(selected_record.target(), Some(original));
    assert!(selected_record.type_parameters().is_empty());
    assert!(selected_record.this_parameter().is_some());
    let mapper = selected_record.mapper().unwrap();
    let prefix = context.store().map_type(mapper, formals[1]).unwrap();
    let remaining = context.store().map_type(mapper, formals[2]).unwrap();
    assert_eq!(
        context.store().map_type(mapper, formals[3]),
        Some(method.formal)
    );
    let bootstrap = context.store().intrinsic_bootstrap().unwrap();
    assert_tuple(context, prefix, &[method.formal], None);
    assert_tuple(
        context,
        remaining,
        &[bootstrap.string_type, bootstrap.number_type],
        Some(&method.parameters[1..]),
    );
    let result = context.get_type_at_location(call).unwrap();
    assert_eq!(context.get_return_type_of_signature(selected), Ok(result));
    assert_ne!(result, method.type_);
    let returned =
        assert_returned_callable(context, result, returned_node, method, &formals, remaining);
    Binding {
        method,
        selected,
        result,
        returned,
        prefix,
        remaining,
    }
}

fn assert_returned_callable(
    context: &mut CanonicalCheckerContext<'_>,
    result: TypeId,
    returned_node: NodeRef,
    method: Method,
    formals: &[TypeId],
    remaining: TypeId,
) -> SignatureId {
    let TypeData::Object(object) = context.store().type_payload(result).unwrap().data() else {
        panic!("the second bind overload must return an instantiated callable")
    };
    assert_eq!(object.structured.call_signature_count, 1);
    let [returned] = object.structured.signatures.as_deref().unwrap() else {
        panic!("expected one bound call signature")
    };
    let returned = *returned;
    let returned_record = context.store().signature(returned).unwrap();
    assert_ne!(returned, method.signature);
    assert_ne!(returned, signature(context, returned_node));
    assert_eq!(
        returned_record.target(),
        Some(signature(context, returned_node))
    );
    assert_eq!(returned_record.declaration(), Some(returned_node));
    assert!(returned_record.type_parameters().is_empty());
    assert_eq!(returned_record.this_parameter(), None);
    assert!(returned_record.has_rest_parameter());
    assert_eq!(returned_record.parameters().len(), 1);
    assert_eq!(returned_record.min_argument_count(), 0);
    assert_eq!(
        context
            .store()
            .value_symbol_links(returned_record.parameters()[0])
            .unwrap()
            .resolved_type,
        Some(remaining)
    );
    let returned_mapper = returned_record.mapper().unwrap();
    assert_eq!(
        context.store().map_type(returned_mapper, formals[2]),
        Some(remaining)
    );
    assert_eq!(
        context.store().map_type(returned_mapper, formals[3]),
        Some(method.formal)
    );
    assert_eq!(
        context.get_return_type_of_signature(returned),
        Ok(method.formal)
    );
    returned
}

fn assert_calls(
    fixture: &Fixture,
    context: &mut CanonicalCheckerContext<'_>,
    calls: &[NodeRef],
    binding: Binding,
    invalid: bool,
) -> Vec<SignatureId> {
    assert_eq!(calls.len(), if invalid { 3 } else { 1 });
    let selected = calls
        .iter()
        .map(|&call| {
            let (callee, _) = call_parts(&fixture.source, call);
            assert_eq!(context.get_type_at_location(callee), Ok(binding.result));
            assert_eq!(
                context.get_type_at_location(call),
                Ok(binding.method.formal)
            );
            let selected = signature(context, call);
            assert_eq!(
                context.get_return_type_of_signature(selected),
                Ok(binding.method.formal)
            );
            selected
        })
        .collect();
    if invalid {
        let (_, arguments) = call_parts(&fixture.source, calls[1]);
        let (missing, _) = call_parts(&fixture.source, calls[2]);
        let diagnostics = context.diagnostics().as_slice();
        assert_eq!(diagnostics.len(), 2, "{diagnostics:?}");
        assert_eq!(diagnostics[0].diagnostic.code(), 2345);
        assert_eq!(diagnostics[0].diagnostic.arguments, ["number", "string"]);
        assert_eq!(diagnostics[0].node, Some(arguments[0]));
        assert_eq!(diagnostics[1].diagnostic.code(), 2554);
        assert_eq!(diagnostics[1].diagnostic.arguments, ["2", "1"]);
        assert_eq!(diagnostics[1].node, Some(missing));
        for diagnostic in diagnostics {
            assert_eq!(diagnostic.range_override, None);
            assert!(diagnostic.related_information.is_empty());
        }
    } else {
        assert!(
            context.diagnostics().is_empty(),
            "{:?}",
            context.diagnostics()
        );
    }
    selected
}

fn check(source: &str, invalid: bool) {
    let fixture = Fixture::new(source);
    let calls = nodes(&fixture.source, SyntaxKind::CallExpression);
    for query_first in [false, true] {
        let mut context = fixture.context();
        let early = query_first.then(|| context.get_type_at_location(calls[0]).unwrap());
        context.check_source_file(FILE).unwrap();
        let binding = assert_binding(&fixture, &mut context, calls[0]);
        if let Some(early) = early {
            assert_eq!(early, binding.result);
        }
        let selected = assert_calls(&fixture, &mut context, &calls[1..], binding, invalid);
        let diagnostics = context.diagnostics().clone();
        let cached_counts = counts(&context);
        for recheck in [false, true, true] {
            if recheck {
                context.recheck_source_file(FILE).unwrap();
            } else {
                context.check_source_file(FILE).unwrap();
            }
            assert_eq!(assert_binding(&fixture, &mut context, calls[0]), binding);
            assert_eq!(
                assert_calls(&fixture, &mut context, &calls[1..], binding, invalid),
                selected
            );
            assert_eq!(context.diagnostics(), &diagnostics);
            assert_eq!(counts(&context), cached_counts);
            assert!(context.store().type_resolution_is_empty());
        }
    }
}

#[test]
fn variadic_bind_preserves_nonempty_remaining_tuple_and_mapper() {
    check(
        concat!(
            "class Listener<T> {\n",
            "  constructor(value: T) {\n",
            "    const bound = this.combine.bind(this, value);\n",
            "    const result: T = bound('ok', 1);\n",
            "  }\n",
            "  combine(value: T, label: string, count: number): T { return value; }\n",
            "}\n",
        ),
        false,
    );
}

#[test]
fn variadic_bound_calls_check_each_tuple_element_and_argument_count() {
    check(
        concat!(
            "declare const invalid: number;\n",
            "class Listener<T> {\n",
            "  constructor(value: T) {\n",
            "    const bound = this.combine.bind(this, value);\n",
            "    const result: T = bound('ok', 1);\n",
            "    bound(invalid, 1);\n",
            "    bound('ok');\n",
            "  }\n",
            "  combine(value: T, label: string, count: number): T { return value; }\n",
            "}\n",
        ),
        true,
    );
}
