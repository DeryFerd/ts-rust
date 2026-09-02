use ts_ast::{FileId, NodeData, NodeId, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId, SymbolFlags,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, IntrinsicBootstrapOptions, SignatureId,
    TypeData, TypeId,
};
use ts_diagnostics::Category;
use ts_parser::{ParseResult, parse_source_file};

const FILE: FileId = FileId::new(203_272);

fn context(parsed: &ParseResult) -> CanonicalCheckerContext<'_> {
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            FILE,
            CanonicalSourceFileFacts::new(
                EscapedName::source("\"/project/function-expression-locals.ts\""),
                CanonicalSourceLanguage::TypeScript,
                false,
                CanonicalModuleState::Script,
            ),
        )
        .unwrap();
    binder
        .bind_typescript_declaration_slice(&parsed.arena, FILE)
        .unwrap();
    CanonicalCheckerContext::new(
        binder.finish(),
        vec![(FILE, &parsed.arena)],
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
    NodeRef::new(parsed.arena.id(), FILE, id)
}

fn variable(parsed: &ParseResult, expected: &str) -> (NodeRef, NodeRef, NodeRef) {
    parsed
        .arena
        .iter()
        .find_map(|(id, record)| {
            let NodeData::VariableDeclaration(data) = &record.data else {
                return None;
            };
            let NodeData::Identifier(name) = &parsed.arena.get(data.name)?.data else {
                return None;
            };
            (name.text == expected).then(|| {
                (
                    node(parsed, id),
                    node(parsed, data.name),
                    node(parsed, data.initializer.unwrap()),
                )
            })
        })
        .unwrap()
}

#[derive(Clone, Copy)]
struct Nodes {
    binding: NodeRef,
    binding_name: NodeRef,
    function: NodeRef,
    function_name: Option<NodeRef>,
    parameter: NodeRef,
    parameter_name: NodeRef,
    parameter_annotation: NodeRef,
    return_annotation: NodeRef,
    local: NodeRef,
    local_name: NodeRef,
    local_annotation: NodeRef,
    target: NodeRef,
    value: NodeRef,
    returned: NodeRef,
    call: NodeRef,
    callee: NodeRef,
    argument: NodeRef,
    result_name: NodeRef,
}

#[allow(clippy::too_many_lines)] // Keep the declaration, assignment, return, and call nodes together.
fn nodes(parsed: &ParseResult) -> Nodes {
    let (binding, binding_name, function) = variable(parsed, "read");
    let (_, result_name, call) = variable(parsed, "result");
    let record = parsed.arena.get(function.node).unwrap();
    assert_eq!(record.kind, SyntaxKind::FunctionExpression);
    assert_eq!(record.parent, Some(binding.node));
    let NodeData::FunctionExpression(data) = &record.data else {
        unreachable!();
    };
    let function_name = data.name.map(|name| node(parsed, name));
    assert_eq!(data.parameters.nodes.len(), 1);
    let parameter = node(parsed, data.parameters.nodes[0]);
    let parameter_record = parsed.arena.get(parameter.node).unwrap();
    assert_eq!(parameter_record.parent, Some(function.node));
    let NodeData::ParameterDeclaration(parameter_data) = &parameter_record.data else {
        unreachable!();
    };
    let parameter_name = node(parsed, parameter_data.name);
    let parameter_annotation = node(parsed, parameter_data.type_.unwrap());
    let return_annotation = node(parsed, data.type_.unwrap());
    let body_record = parsed.arena.get(data.body).unwrap();
    assert_eq!(body_record.parent, Some(function.node));
    let NodeData::Block(body) = &body_record.data else {
        unreachable!();
    };
    assert_eq!(body.statements.nodes.len(), 3);
    for statement in &body.statements.nodes {
        assert_eq!(
            parsed.arena.get(*statement).unwrap().parent,
            Some(data.body)
        );
    }
    let statement = parsed.arena.get(body.statements.nodes[0]).unwrap();
    let NodeData::VariableStatement(statement_data) = &statement.data else {
        unreachable!();
    };
    let list = parsed.arena.get(statement_data.declaration_list).unwrap();
    assert_eq!(list.parent, Some(body.statements.nodes[0]));
    let NodeData::VariableDeclarationList(list_data) = &list.data else {
        unreachable!();
    };
    assert_eq!(list_data.declarations.nodes.len(), 1);
    let local = node(parsed, list_data.declarations.nodes[0]);
    let local_record = parsed.arena.get(local.node).unwrap();
    assert_eq!(local_record.parent, Some(statement_data.declaration_list));
    let NodeData::VariableDeclaration(local_data) = &local_record.data else {
        unreachable!();
    };
    assert!(local_data.initializer.is_none());
    let local_name = node(parsed, local_data.name);
    let local_annotation = node(parsed, local_data.type_.unwrap());
    let NodeData::ExpressionStatement(statement_data) =
        &parsed.arena.get(body.statements.nodes[1]).unwrap().data
    else {
        unreachable!();
    };
    let assignment = parsed.arena.get(statement_data.expression).unwrap();
    assert_eq!(assignment.parent, Some(body.statements.nodes[1]));
    let NodeData::BinaryExpression(assignment_data) = &assignment.data else {
        unreachable!();
    };
    assert_eq!(
        parsed
            .arena
            .get(assignment_data.operator_token)
            .unwrap()
            .kind,
        SyntaxKind::EqualsToken,
    );
    let target = node(parsed, assignment_data.left);
    let value = node(parsed, assignment_data.right);
    for expression in [target, value] {
        assert_eq!(
            parsed.arena.get(expression.node).unwrap().parent,
            Some(statement_data.expression),
        );
    }
    let NodeData::ReturnStatement(return_statement) =
        &parsed.arena.get(body.statements.nodes[2]).unwrap().data
    else {
        unreachable!();
    };
    let returned = node(parsed, return_statement.expression.unwrap());
    assert_eq!(
        parsed.arena.get(returned.node).unwrap().parent,
        Some(body.statements.nodes[2]),
    );
    let NodeData::CallExpression(call_data) = &parsed.arena.get(call.node).unwrap().data else {
        unreachable!();
    };
    assert_eq!(call_data.arguments.nodes.len(), 1);
    let argument = node(parsed, call_data.arguments.nodes[0]);
    let callee = node(parsed, call_data.expression);
    for expression in [callee, argument] {
        assert_eq!(
            parsed.arena.get(expression.node).unwrap().parent,
            Some(call.node)
        );
    }
    Nodes {
        binding,
        binding_name,
        function,
        function_name,
        parameter,
        parameter_name,
        parameter_annotation,
        return_annotation,
        local,
        local_name,
        local_annotation,
        target,
        value,
        returned,
        call,
        callee,
        argument,
        result_name,
    }
}

fn symbol(checker: &CanonicalCheckerContext<'_>, declaration: NodeRef) -> SemanticSymbolId {
    let raw = checker.file(FILE).unwrap().1.symbol(declaration).unwrap();
    checker.store().get_merged_symbol(raw).unwrap()
}

fn signature(checker: &CanonicalCheckerContext<'_>, declaration: NodeRef) -> SignatureId {
    checker
        .store()
        .signature_links(declaration)
        .and_then(|links| links.resolved_signature.signature())
        .unwrap()
}

#[derive(Debug, Eq, PartialEq)]
struct State {
    owners: [SemanticSymbolId; 4],
    callable: TypeId,
    parameter_type: TypeId,
    returned_type: TypeId,
    argument_type: TypeId,
    signature: SignatureId,
}

#[allow(clippy::too_many_lines)] // Check the real callable and local owners with their queried types.
fn state(checker: &mut CanonicalCheckerContext<'_>, nodes: Nodes, wrong_type: bool) -> State {
    use ts_checker::semantic::type_records::LiteralValue;

    let bootstrap = checker.store().intrinsic_bootstrap().unwrap();
    let string = bootstrap.string_type;
    let parameter_type = if wrong_type {
        bootstrap.number_type
    } else {
        string
    };
    let callable = checker.get_type_at_location(nodes.function).unwrap();
    assert_eq!(
        checker.get_type_at_location(nodes.binding_name),
        Ok(callable)
    );
    for location in [
        nodes.local_name,
        nodes.local_annotation,
        nodes.return_annotation,
        nodes.returned,
        nodes.call,
        nodes.result_name,
    ] {
        assert_eq!(checker.get_type_at_location(location), Ok(string));
    }
    for location in [
        nodes.parameter_name,
        nodes.parameter_annotation,
        nodes.value,
    ] {
        assert_eq!(checker.get_type_at_location(location), Ok(parameter_type));
    }
    let argument_type = checker.get_type_at_location(nodes.argument).unwrap();
    let callable_signature = signature(checker, nodes.function);
    assert_eq!(signature(checker, nodes.call), callable_signature);
    assert_eq!(
        checker.get_return_type_of_signature(callable_signature),
        Ok(string)
    );
    let owner = symbol(checker, nodes.function);
    let binding = symbol(checker, nodes.binding);
    let parameter = symbol(checker, nodes.parameter);
    let local = symbol(checker, nodes.local);
    let owners = [owner, binding, parameter, local];
    if let Some(name) = nodes.function_name {
        assert_eq!(checker.get_symbol_at_location(name), Ok(Some(owner)));
        assert_eq!(checker.get_type_at_location(name), Ok(callable));
    }
    for (index, current) in owners.iter().enumerate() {
        assert!(!owners[..index].contains(current));
    }
    for location in [nodes.local_name, nodes.target, nodes.returned] {
        assert_eq!(checker.get_symbol_at_location(location), Ok(Some(local)));
    }
    for location in [nodes.parameter_name, nodes.value] {
        assert_eq!(
            checker.get_symbol_at_location(location),
            Ok(Some(parameter))
        );
    }
    assert_eq!(
        checker.get_symbol_at_location(nodes.callee),
        Ok(Some(binding))
    );
    let bound = checker.file(FILE).unwrap().1;
    assert_eq!(bound.container(nodes.local), Some(nodes.function));
    assert_eq!(bound.container(nodes.target), Some(nodes.function));
    assert_eq!(bound.flow_container(nodes.returned), Some(nodes.function));
    assert_eq!(
        bound.block_scope_container(nodes.local_name),
        bound.block_scope_container(nodes.local)
    );
    let store = checker.store();
    for (symbol, declaration, type_) in [
        (owner, nodes.function, callable),
        (binding, nodes.binding, callable),
        (parameter, nodes.parameter, parameter_type),
        (local, nodes.local, string),
    ] {
        let record = store.symbol(symbol).unwrap();
        assert_eq!(record.declarations(), Some(&[declaration][..]));
        assert_eq!(record.value_declaration(), Some(declaration));
        assert_eq!(
            store.value_symbol_links(symbol).unwrap().resolved_type,
            Some(type_)
        );
    }
    assert_eq!(store.symbol(owner).unwrap().flags(), SymbolFlags::FUNCTION);
    let record = store.type_payload(callable).unwrap();
    assert_eq!(record.symbol(), Some(owner));
    let TypeData::Object(object) = record.data() else {
        panic!("expected the source function's callable type");
    };
    assert_eq!(object.structured.call_signature_count, 1);
    assert_eq!(
        object.structured.signatures.as_deref(),
        Some(&[callable_signature][..])
    );
    let record = store.signature(callable_signature).unwrap();
    assert_eq!(record.declaration(), Some(nodes.function));
    assert_eq!(record.parameters(), &[parameter]);
    assert_eq!(record.min_argument_count(), 1);
    assert!(record.type_parameters().is_empty());
    assert!(!record.has_rest_parameter());
    assert_eq!(record.this_parameter(), None);
    assert_eq!(record.target(), None);
    assert_eq!(record.mapper(), None);
    assert_eq!(record.resolved_return_type(), Some(string));
    let TypeData::Literal(literal) = store.type_payload(argument_type).unwrap().data() else {
        panic!("expected the real call argument's literal type");
    };
    if wrong_type {
        assert!(matches!(literal.value, LiteralValue::Number(_)));
    } else {
        assert_eq!(literal.value, LiteralValue::String("ok".to_owned()));
    }
    let TypeData::Literal(regular) = store.type_payload(literal.regular_type).unwrap().data()
    else {
        panic!("expected the argument's regular literal type");
    };
    assert_eq!(regular.value, literal.value);
    assert_eq!(regular.regular_type, literal.regular_type);
    State {
        owners,
        callable,
        parameter_type,
        returned_type: string,
        argument_type,
        signature: callable_signature,
    }
}

fn check_assignment(source: &str, wrong_type: bool) {
    let parsed = parse_source_file(source);
    let nodes = nodes(&parsed);
    for first in [None, Some(nodes.function), Some(nodes.call)] {
        let mut checker = context(&parsed);
        let early = first.map(|location| checker.get_type_at_location(location).unwrap());
        checker.check_source_file(FILE).unwrap();
        let mut previous = None;
        for replay in 0..3 {
            if replay != 0 {
                checker.recheck_source_file(FILE).unwrap();
            }
            let state = state(&mut checker, nodes, wrong_type);
            if let Some(early) = early {
                assert_eq!(
                    early,
                    if first == Some(nodes.function) {
                        state.callable
                    } else {
                        state.returned_type
                    }
                );
            }
            let diagnostics = checker.diagnostics().as_slice();
            if wrong_type {
                assert_eq!(diagnostics.len(), 1, "{diagnostics:?}");
                let diagnostic = &diagnostics[0];
                assert_eq!(diagnostic.node, Some(nodes.target));
                assert_eq!(diagnostic.range_override, None);
                assert_eq!(diagnostic.diagnostic.code(), 2322);
                assert_eq!(diagnostic.diagnostic.category(), Category::Error);
                assert_eq!(diagnostic.diagnostic.arguments, ["number", "string"]);
                assert_eq!(
                    diagnostic.diagnostic.render().unwrap(),
                    "Type 'number' is not assignable to type 'string'."
                );
                assert!(diagnostic.diagnostic.details.is_empty());
                assert!(diagnostic.related_information.is_empty());
            } else {
                assert!(diagnostics.is_empty(), "{diagnostics:?}");
            }
            let store = checker.store();
            let current = (
                state,
                [
                    store.type_len(),
                    store.symbol_len(),
                    store.signature_len(),
                    store.mapper_len(),
                ],
                checker.diagnostics().clone(),
            );
            if let Some(previous) = &previous {
                assert_eq!(&current, previous);
            } else {
                previous = Some(current);
            }
        }
    }
}

#[test]
fn function_expression_assigns_annotated_local_before_read() {
    check_assignment(
        concat!(
            "const read = function assigned(value: string): string {\n",
            "  let local: string;\n",
            "  local = value;\n",
            "  return local;\n",
            "};\n",
            "const result = read('ok');\n",
        ),
        false,
    );
}

#[test]
fn function_expression_annotated_local_assignment_reports_type_error() {
    check_assignment(
        concat!(
            "const read = function(value: number): string {\n",
            "  let local: string;\n",
            "  local = value;\n",
            "  return local;\n",
            "};\n",
            "const result = read(1);\n",
        ),
        true,
    );
}
