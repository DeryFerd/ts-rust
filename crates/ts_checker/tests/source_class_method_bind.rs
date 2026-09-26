use ts_ast::{FileId, NodeData, NodeId, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId, SymbolFlags,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, IntrinsicBootstrapOptions, SignatureId,
    TypeData, TypeId, types::TypeFlags,
};
use ts_parser::{ParseResult, parse_source_file};

const LIBRARY: FileId = FileId::new(203_120);
const FILE: FileId = FileId::new(203_121);
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

    fn context(&self, strict: bool) -> CanonicalCheckerContext<'_> {
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
                            "\"/project/class-method-bind.ts\""
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
                strict_bind_call_apply: strict,
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

fn only(parsed: &ParseResult, kind: SyntaxKind) -> NodeRef {
    let nodes = parsed
        .arena
        .iter()
        .filter_map(|(id, record)| (record.kind == kind).then_some(node(parsed, FILE, id)))
        .collect::<Vec<_>>();
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
        panic!("expected the actual call")
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

struct BindNodes {
    call: NodeRef,
    callee: NodeRef,
    name: NodeRef,
    method_access: NodeRef,
    arguments: Vec<NodeRef>,
    other_calls: Vec<NodeRef>,
}

fn bind_nodes(parsed: &ParseResult) -> BindNodes {
    let mut calls = parsed
        .arena
        .iter()
        .filter_map(|(id, record)| {
            (record.kind == SyntaxKind::CallExpression).then_some(node(parsed, FILE, id))
        })
        .collect::<Vec<_>>();
    calls.sort_by_key(|call| parsed.arena.get(call.node).unwrap().range.start);
    let call = calls.remove(0);
    let (callee, arguments) = call_parts(parsed, call);
    let NodeData::PropertyAccessExpression(bind) = &parsed.arena.get(callee.node).unwrap().data
    else {
        panic!("expected the actual bind property access")
    };
    let NodeData::Identifier(name) = &parsed.arena.get(bind.name).unwrap().data else {
        unreachable!()
    };
    assert_eq!(name.text, "bind");
    let NodeData::PropertyAccessExpression(method) =
        &parsed.arena.get(bind.expression).unwrap().data
    else {
        panic!("expected the class method receiver")
    };
    assert_eq!(
        parsed.arena.get(method.expression).unwrap().kind,
        SyntaxKind::ThisKeyword
    );
    assert_eq!(
        parsed.arena.get(arguments[0].node).unwrap().kind,
        SyntaxKind::ThisKeyword
    );
    BindNodes {
        call,
        callee,
        name: node(parsed, FILE, bind.name),
        method_access: node(parsed, FILE, bind.expression),
        arguments,
        other_calls: calls,
    }
}

fn library_bind(fixture: &Fixture, strict: bool) -> (NodeRef, Vec<NodeRef>) {
    let owner_name = if strict {
        "CallableFunction"
    } else {
        "Function"
    };
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
            if name.text != owner_name {
                return None;
            }
            let methods = interface
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
                .collect::<Vec<_>>();
            Some((node(&fixture.library, LIBRARY, id), methods))
        })
        .unwrap()
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Binding {
    formal: TypeId,
    method: TypeId,
    source_signature: SignatureId,
    bind_signature: SignatureId,
    result: TypeId,
    result_signature: Option<SignatureId>,
}

fn assert_binding(
    fixture: &Fixture,
    context: &mut CanonicalCheckerContext<'_>,
    nodes: &BindNodes,
    strict: bool,
    prefix: bool,
) -> Binding {
    let class = symbol(context, only(&fixture.source, SyntaxKind::ClassDeclaration));
    let formal_symbol = symbol(context, only(&fixture.source, SyntaxKind::TypeParameter));
    let formal = context
        .store()
        .declared_type_links(formal_symbol)
        .unwrap()
        .declared_type
        .unwrap();
    assert_eq!(
        context.store().symbol(formal_symbol).unwrap().parent(),
        Some(class)
    );
    assert_eq!(
        context.store().type_payload(formal).unwrap().flags(),
        TypeFlags::TYPE_PARAMETER
    );
    assert_eq!(
        context.store().type_payload(formal).unwrap().symbol(),
        Some(formal_symbol)
    );
    let method_node = only(&fixture.source, SyntaxKind::MethodDeclaration);
    let method_symbol = symbol(context, method_node);
    let method = context
        .store()
        .value_symbol_links(method_symbol)
        .unwrap()
        .resolved_type
        .unwrap();
    let member = context.store().symbol(method_symbol).unwrap();
    assert_eq!(member.flags(), SymbolFlags::METHOD);
    assert_eq!(member.parent(), Some(class));
    assert_eq!(member.value_declaration(), Some(method_node));
    let source_signature = signature(context, method_node);
    let source = context.store().signature(source_signature).unwrap();
    assert_eq!(source.declaration(), Some(method_node));
    assert!(source.type_parameters().is_empty());
    assert_eq!(source.this_parameter(), None);
    assert_eq!(source.parameters().len(), 1);
    assert_eq!(source.min_argument_count(), 1);
    assert_eq!(source.resolved_return_type(), Some(formal));
    assert_eq!(
        context
            .store()
            .value_symbol_links(source.parameters()[0])
            .unwrap()
            .resolved_type,
        Some(formal)
    );
    assert_eq!(
        context.get_type_at_location(nodes.method_access),
        Ok(method)
    );
    assert_eq!(nodes.arguments.len(), if prefix { 2 } else { 1 });
    if prefix {
        assert_eq!(context.get_type_at_location(nodes.arguments[1]), Ok(formal));
    }

    let (library_owner, declarations) = library_bind(fixture, strict);
    assert_eq!(declarations.len(), if strict { 2 } else { 1 });
    let library_symbol = symbol(context, declarations[0]);
    for &declaration in &declarations {
        assert_eq!(symbol(context, declaration), library_symbol);
    }
    assert_eq!(
        context.store().symbol(library_symbol).unwrap().parent(),
        Some(symbol(context, library_owner))
    );
    assert_eq!(
        context.get_symbol_at_location(nodes.name).unwrap(),
        Some(library_symbol)
    );
    assert_eq!(
        context
            .store()
            .symbol_node_links(nodes.callee)
            .unwrap()
            .resolved_symbol,
        Some(library_symbol)
    );
    let global = context
        .get_declared_type_of_symbol(symbol(context, library_owner))
        .unwrap();
    assert_eq!(global, context.global_types().callable_function_type);
    assert_eq!(global == context.global_types().function_type, !strict);

    let result = context.get_type_at_location(nodes.call).unwrap();
    let bind_signature = signature(context, nodes.call);
    assert_eq!(
        context.get_return_type_of_signature(bind_signature),
        Ok(result)
    );
    let selected = context.store().signature(bind_signature).unwrap();
    assert_eq!(
        selected.declaration(),
        Some(declarations[usize::from(prefix)])
    );
    assert!(selected.this_parameter().is_some());
    let result_signature = if strict {
        let TypeData::Object(object) = context.store().type_payload(result).unwrap().data() else {
            panic!("the real strict bind overload must return a callable object")
        };
        assert_eq!(object.structured.call_signature_count, 1);
        let [bound] = object.structured.signatures.as_deref().unwrap() else {
            panic!("expected the one bound call signature")
        };
        let bound = *bound;
        assert_eq!(context.get_return_type_of_signature(bound), Ok(formal));
        let bound_record = context.store().signature(bound).unwrap();
        assert_eq!(bound_record.this_parameter(), None);
        assert!(bound_record.type_parameters().is_empty());
        assert_eq!(bound_record.parameters().len(), 1);
        assert_eq!(bound_record.min_argument_count(), i32::from(!prefix));
        let parameter = bound_record.parameters()[0];
        let parameter_type = context
            .store()
            .value_symbol_links(parameter)
            .unwrap()
            .resolved_type
            .unwrap();
        if prefix {
            assert!(bound_record.has_rest_parameter());
            assert_ne!(bound, source_signature);
            assert_ne!(result, method);
            let store = context.store();
            let target = match store.type_payload(parameter_type).unwrap().data() {
                TypeData::Tuple(_) => parameter_type,
                TypeData::TypeReference(reference) => {
                    assert_eq!(reference.resolved_type_arguments.as_deref(), Some(&[][..]));
                    reference.object.target.unwrap()
                }
                _ => panic!("the bound rest parameter must retain the inferred empty tuple"),
            };
            let TypeData::Tuple(tuple) = store.type_payload(target).unwrap().data() else {
                panic!("expected the real tuple target")
            };
            assert!(tuple.metadata.element_infos().is_empty());
            assert_eq!(tuple.metadata.min_length(), 0);
            assert_eq!(tuple.metadata.fixed_length(), 0);
        } else {
            assert!(!bound_record.has_rest_parameter());
            assert_eq!(parameter_type, formal);
        }
        Some(bound)
    } else {
        assert!(!prefix);
        let NodeData::MethodSignatureDeclaration(declaration) = &fixture
            .library
            .arena
            .get(declarations[0].node)
            .unwrap()
            .data
        else {
            unreachable!()
        };
        assert_eq!(
            fixture
                .library
                .arena
                .get(declaration.type_.unwrap())
                .unwrap()
                .kind,
            SyntaxKind::AnyKeyword
        );
        assert_eq!(
            result,
            context.store().intrinsic_bootstrap().unwrap().any_type
        );
        None
    };
    Binding {
        formal,
        method,
        source_signature,
        bind_signature,
        result,
        result_signature,
    }
}

fn assert_calls(
    fixture: &Fixture,
    context: &mut CanonicalCheckerContext<'_>,
    nodes: &BindNodes,
    binding: Binding,
    prefix: bool,
    bad_argument: bool,
) -> Vec<SignatureId> {
    let mut selected = Vec::new();
    for &call in &nodes.other_calls {
        let (callee, arguments) = call_parts(&fixture.source, call);
        assert_eq!(context.get_type_at_location(callee), Ok(binding.result));
        assert_eq!(arguments.len(), usize::from(!prefix));
        assert_eq!(context.get_type_at_location(call), Ok(binding.formal));
        let signature = signature(context, call);
        assert_eq!(
            context.get_return_type_of_signature(signature),
            Ok(binding.formal)
        );
        selected.push(signature);
    }
    if bad_argument {
        assert_eq!(nodes.other_calls.len(), 2);
        let (_, arguments) = call_parts(&fixture.source, nodes.other_calls[1]);
        let number = context.store().intrinsic_bootstrap().unwrap().number_type;
        assert_eq!(context.get_type_at_location(arguments[0]), Ok(number));
        let [diagnostic] = context.diagnostics().as_slice() else {
            panic!(
                "expected one native bad argument diagnostic: {:?}",
                context.diagnostics()
            )
        };
        assert_eq!(diagnostic.node, Some(arguments[0]));
        assert_eq!(diagnostic.diagnostic.code(), 2345);
        assert_eq!(diagnostic.diagnostic.arguments, ["number", "T"]);
        assert_eq!(diagnostic.range_override, None);
        assert!(diagnostic.related_information.is_empty());
    } else {
        assert_eq!(nodes.other_calls.len(), usize::from(prefix));
        assert!(
            context.diagnostics().is_empty(),
            "{:?}",
            context.diagnostics()
        );
    }
    selected
}

#[derive(Clone, Copy, Eq, PartialEq)]
enum BindCase {
    Assignment,
    Prefix,
    BadArgument,
}

fn check(source: &str, strict: bool, case: BindCase) {
    let prefix = case == BindCase::Prefix;
    let bad_argument = case == BindCase::BadArgument;
    let fixture = Fixture::new(source);
    let nodes = bind_nodes(&fixture.source);
    for query_first in [false, true] {
        let mut context = fixture.context(strict);
        let early = query_first.then(|| context.get_type_at_location(nodes.call).unwrap());
        context.check_source_file(FILE).unwrap();
        let binding = assert_binding(&fixture, &mut context, &nodes, strict, prefix);
        if let Some(early) = early {
            assert_eq!(early, binding.result);
        }
        if !prefix && !bad_argument {
            let assignment = only(&fixture.source, SyntaxKind::BinaryExpression);
            let NodeData::BinaryExpression(binary) =
                &fixture.source.arena.get(assignment.node).unwrap().data
            else {
                unreachable!()
            };
            assert_eq!(node(&fixture.source, FILE, binary.right), nodes.call);
            assert_eq!(
                context.get_type_at_location(node(&fixture.source, FILE, binary.left)),
                Ok(binding.method)
            );
            assert_eq!(context.get_type_at_location(assignment), Ok(binding.result));
        }
        let selected = assert_calls(
            &fixture,
            &mut context,
            &nodes,
            binding,
            prefix,
            bad_argument,
        );
        let diagnostics = context.diagnostics().clone();
        for recheck in [false, true, true] {
            if recheck {
                context.recheck_source_file(FILE).unwrap();
            } else {
                context.check_source_file(FILE).unwrap();
            }
            assert_eq!(
                assert_binding(&fixture, &mut context, &nodes, strict, prefix),
                binding
            );
            assert_eq!(
                assert_calls(
                    &fixture,
                    &mut context,
                    &nodes,
                    binding,
                    prefix,
                    bad_argument
                ),
                selected
            );
            assert_eq!(context.diagnostics(), &diagnostics);
            assert!(context.store().type_resolution_is_empty());
        }
    }
}

#[test]
fn generic_class_method_bind_uses_the_real_library_for_each_strict_option() {
    let source = concat!(
        "class Listener<T> {\n",
        "  constructor() { this.subscribe = this.subscribe.bind(this); }\n",
        "  subscribe(value: T): T { return value; }\n",
        "}\n",
    );
    for strict in [true, false] {
        check(source, strict, BindCase::Assignment);
    }
}

#[test]
fn generic_class_method_bind_prefix_removes_the_bound_value_parameter() {
    check(
        concat!(
            "class Listener<T> {\n",
            "  constructor(value: T) {\n",
            "    const bound = this.subscribe.bind(this, value);\n",
            "    const result: T = bound();\n",
            "  }\n",
            "  subscribe(value: T): T { return value; }\n",
            "}\n",
        ),
        true,
        BindCase::Prefix,
    );
}

#[test]
fn generic_class_method_bound_call_keeps_the_native_bad_argument_diagnostic() {
    check(
        concat!(
            "declare const invalid: number;\n",
            "class Listener<T> {\n",
            "  constructor(value: T) {\n",
            "    const bound = this.subscribe.bind(this);\n",
            "    const good: T = bound(value);\n",
            "    bound(invalid);\n",
            "  }\n",
            "  subscribe(value: T): T { return value; }\n",
            "}\n",
        ),
        true,
        BindCase::BadArgument,
    );
}

fn assert_generic_receiver_calls(
    fixture: &Fixture,
    context: &mut CanonicalCheckerContext<'_>,
    calls: &[NodeRef; 3],
) -> (SignatureId, TypeId, [SignatureId; 3]) {
    let function = only(&fixture.source, SyntaxKind::FunctionDeclaration);
    let NodeData::FunctionDeclaration(declaration) =
        &fixture.source.arena.get(function.node).unwrap().data
    else {
        unreachable!()
    };
    let formals = &declaration.type_parameters.as_ref().unwrap().nodes;
    assert_eq!(formals.len(), 1);
    let formal_node = node(&fixture.source, FILE, formals[0]);
    let formal = context
        .get_declared_type_of_symbol(symbol(context, formal_node))
        .unwrap();
    let box_declaration = only(&fixture.source, SyntaxKind::InterfaceDeclaration);
    let box_type = context
        .get_declared_type_of_symbol(symbol(context, box_declaration))
        .unwrap();
    let source_signature = signature(context, function);
    let this_declaration = node(&fixture.source, FILE, declaration.parameters.nodes[0]);
    let source = context.store().signature(source_signature).unwrap();
    assert_eq!(source.declaration(), Some(function));
    assert_eq!(source.type_parameters(), &[formal]);
    assert_eq!(
        source.this_parameter(),
        Some(symbol(context, this_declaration))
    );
    assert_eq!(source.parameters().len(), 1);
    assert_eq!(source.resolved_return_type(), Some(formal));
    let number = context.store().intrinsic_bootstrap().unwrap().number_type;
    let selected = calls.map(|call| {
        assert_eq!(context.get_type_at_location(call), Ok(number));
        let selected = signature(context, call);
        assert_eq!(context.get_return_type_of_signature(selected), Ok(number));
        let record = context.store().signature(selected).unwrap();
        assert_eq!(record.declaration(), Some(function));
        assert_eq!(record.target(), Some(source_signature));
        assert!(record.type_parameters().is_empty());
        assert!(record.this_parameter().is_some());
        assert_eq!(record.parameters().len(), 1);
        assert_eq!(record.min_argument_count(), 1);
        assert_eq!(
            context.store().map_type(record.mapper().unwrap(), formal),
            Some(number)
        );
        selected
    });
    let good_this = context
        .store()
        .signature(selected[0])
        .unwrap()
        .this_parameter()
        .unwrap();
    let expected_this = context
        .store()
        .value_symbol_links(good_this)
        .unwrap()
        .resolved_type
        .unwrap();
    let TypeData::TypeReference(expected_reference) =
        context.store().type_payload(expected_this).unwrap().data()
    else {
        panic!("expected the actual instantiated Box receiver")
    };
    assert_eq!(expected_reference.object.target, Some(box_type));
    assert_eq!(
        expected_reference.resolved_type_arguments.as_deref(),
        Some(&[number][..])
    );
    let expected_text = context.type_to_string(expected_this).unwrap();
    assert_eq!(expected_text, "Box<number>");
    let (bad_callee, _) = call_parts(&fixture.source, calls[1]);
    let NodeData::PropertyAccessExpression(bad_access) =
        &fixture.source.arena.get(bad_callee.node).unwrap().data
    else {
        panic!("expected the actual bad receiver access")
    };
    let bad_receiver = node(&fixture.source, FILE, bad_access.expression);
    let bad_type = context.get_type_at_location(bad_receiver).unwrap();
    let bad_text = context.type_to_string(bad_type).unwrap();
    let diagnostics = context.diagnostics().as_slice();
    assert_eq!(diagnostics.len(), 2, "{diagnostics:?}");
    for (diagnostic, node) in diagnostics.iter().zip([bad_receiver, calls[2]]) {
        assert_eq!(diagnostic.diagnostic.code(), 2684);
        assert_eq!(diagnostic.node, Some(node));
        assert_eq!(diagnostic.range_override, None);
        assert!(diagnostic.related_information.is_empty());
    }
    assert!(diagnostics[0].diagnostic.render().unwrap().starts_with(&format!(
        "The 'this' context of type '{bad_text}' is not assignable to method's 'this' of type '{expected_text}'."
    )));
    assert_eq!(
        diagnostics[1].diagnostic.render().unwrap(),
        format!(
            "The 'this' context of type 'void' is not assignable to method's 'this' of type '{expected_text}'."
        )
    );
    (source_signature, formal, selected)
}

#[test]
fn generic_explicit_this_calls_keep_wrong_and_missing_receiver_diagnostics() {
    let fixture = Fixture::new(concat!(
        "interface Box<T> { value: T; }\n",
        "function read<T>(this: Box<T>, input: T): T { return input; }\n",
        "const receiver = { value: 1, run: read };\n",
        "const wrong = { value: 'bad', run: read };\n",
        "const good: number = receiver.run<number>(1);\n",
        "const mismatch: number = wrong.run<number>(1);\n",
        "const missing: number = read<number>(1);\n",
    ));
    let mut calls = fixture
        .source
        .arena
        .iter()
        .filter_map(|(id, record)| {
            (record.kind == SyntaxKind::CallExpression).then_some(node(&fixture.source, FILE, id))
        })
        .collect::<Vec<_>>();
    calls.sort_by_key(|call| fixture.source.arena.get(call.node).unwrap().range.start);
    let calls: [NodeRef; 3] = calls.try_into().unwrap();
    for query_first in [false, true] {
        let mut context = fixture.context(true);
        if query_first {
            context.get_type_at_location(calls[2]).unwrap();
        }
        context.check_source_file(FILE).unwrap();
        let identity = assert_generic_receiver_calls(&fixture, &mut context, &calls);
        let diagnostics = context.diagnostics().clone();
        for recheck in [false, true, true] {
            if recheck {
                context.recheck_source_file(FILE).unwrap();
            } else {
                context.check_source_file(FILE).unwrap();
            }
            assert_eq!(
                assert_generic_receiver_calls(&fixture, &mut context, &calls),
                identity
            );
            assert_eq!(context.diagnostics(), &diagnostics);
            assert!(context.store().type_resolution_is_empty());
        }
    }
}
