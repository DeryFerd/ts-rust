use ts_ast::{FileId, NodeData, NodeRef};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId, SymbolFlags,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, IntrinsicBootstrapOptions, SignatureId,
    TypeData, TypeId,
};
use ts_parser::{ParseResult, parse_source_file};

const FILE: FileId = FileId::new(8_280);

fn context(parsed: &ParseResult, no_implicit_any: bool) -> CanonicalCheckerContext<'_> {
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            FILE,
            CanonicalSourceFileFacts::new(
                EscapedName::source("\"/project/function-expressions.ts\""),
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
            no_implicit_any,
            strict_function_types: true,
            ..CanonicalCheckerOptions::default()
        },
    )
    .unwrap()
}

fn variable(parsed: &ParseResult, expected: &str) -> (NodeRef, NodeRef, NodeRef) {
    parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            let NodeData::VariableDeclaration(variable) = &record.data else {
                return None;
            };
            let NodeData::Identifier(name) = &parsed.arena.get(variable.name)?.data else {
                return None;
            };
            (name.text == expected).then(|| {
                (
                    NodeRef::new(parsed.arena.id(), FILE, node),
                    NodeRef::new(parsed.arena.id(), FILE, variable.name),
                    NodeRef::new(parsed.arena.id(), FILE, variable.initializer.unwrap()),
                )
            })
        })
        .unwrap_or_else(|| panic!("missing initialized variable {expected}"))
}

fn symbol(checker: &CanonicalCheckerContext<'_>, declaration: NodeRef) -> SemanticSymbolId {
    let raw = checker.file(FILE).unwrap().1.symbol(declaration).unwrap();
    checker.store().get_merged_symbol(raw).unwrap()
}

fn signature(checker: &CanonicalCheckerContext<'_>, node: NodeRef) -> SignatureId {
    checker
        .store()
        .signature_links(node)
        .and_then(|links| links.resolved_signature.signature())
        .unwrap()
}

fn counts(checker: &CanonicalCheckerContext<'_>) -> [usize; 4] {
    let store = checker.store();
    [
        store.type_len(),
        store.symbol_len(),
        store.signature_len(),
        store.mapper_len(),
    ]
}

#[derive(Debug, Eq, PartialEq)]
struct FunctionState {
    owner: SemanticSymbolId,
    binding: SemanticSymbolId,
    callable: TypeId,
    signature: SignatureId,
    parameters: Vec<(SemanticSymbolId, TypeId)>,
    returned: TypeId,
    body: Option<(NodeRef, TypeId)>,
}

#[allow(clippy::too_many_lines)] // Check the function, signature, and actual parameter owners together.
fn function_state(
    checker: &mut CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    name: &str,
) -> FunctionState {
    let (binding_node, binding_name, declaration) = variable(parsed, name);
    let NodeData::FunctionExpression(function) = &parsed.arena.get(declaration.node).unwrap().data
    else {
        panic!("expected an actual function expression")
    };
    let node_ref = |node| NodeRef::new(parsed.arena.id(), FILE, node);
    let owner = symbol(checker, declaration);
    let binding = symbol(checker, binding_node);
    assert_ne!(owner, binding);
    let owner_record = checker.store().symbol(owner).unwrap();
    assert_eq!(owner_record.flags(), SymbolFlags::FUNCTION);
    assert_eq!(owner_record.declarations(), Some(&[declaration][..]));
    assert_eq!(owner_record.value_declaration(), Some(declaration));
    let callable = checker.get_type_at_location(declaration).unwrap();
    for symbol in [owner, binding] {
        assert_eq!(
            checker
                .store()
                .value_symbol_links(symbol)
                .unwrap()
                .resolved_type,
            Some(callable),
        );
    }
    assert_eq!(checker.get_type_at_location(binding_name), Ok(callable));
    assert_eq!(
        checker.get_symbol_at_location(binding_name),
        Ok(Some(binding))
    );
    if let Some(name) = function.name {
        assert_eq!(checker.get_type_at_location(node_ref(name)), Ok(callable));
        assert_eq!(
            checker.get_symbol_at_location(node_ref(name)),
            Ok(Some(owner))
        );
    }

    let signature = signature(checker, declaration);
    let record = checker.store().type_payload(callable).unwrap();
    assert_eq!(record.symbol(), Some(owner));
    let TypeData::Object(object) = record.data() else {
        panic!("expected the function's callable object")
    };
    assert_eq!(
        object.structured.signatures.as_deref(),
        Some(&[signature][..])
    );
    assert_eq!(object.structured.call_signature_count, 1);
    let parameters = function
        .parameters
        .nodes
        .iter()
        .map(|&node| {
            let NodeData::ParameterDeclaration(parameter) = &parsed.arena.get(node).unwrap().data
            else {
                panic!("expected a parameter declaration")
            };
            let declaration = node_ref(node);
            let symbol = symbol(checker, declaration);
            let record = checker.store().symbol(symbol).unwrap();
            assert_eq!(record.declarations(), Some(&[declaration][..]));
            assert_eq!(record.value_declaration(), Some(declaration));
            let type_ = checker
                .get_type_at_location(node_ref(parameter.name))
                .unwrap();
            if let Some(annotation) = parameter.type_ {
                assert_eq!(
                    checker.get_type_at_location(node_ref(annotation)),
                    Ok(type_)
                );
            }
            assert_eq!(
                checker.get_symbol_at_location(node_ref(parameter.name)),
                Ok(Some(symbol))
            );
            assert_eq!(
                checker
                    .store()
                    .value_symbol_links(symbol)
                    .unwrap()
                    .resolved_type,
                Some(type_),
            );
            (symbol, type_)
        })
        .collect::<Vec<_>>();
    let returned = checker.get_return_type_of_signature(signature).unwrap();
    let record = checker.store().signature(signature).unwrap();
    assert_eq!(record.declaration(), Some(declaration));
    assert_eq!(
        record.parameters(),
        parameters
            .iter()
            .map(|&(symbol, _)| symbol)
            .collect::<Vec<_>>()
    );
    assert!(record.type_parameters().is_empty());
    assert_eq!(record.resolved_return_type(), Some(returned));
    assert_eq!(record.target(), None);
    assert_eq!(record.mapper(), None);
    if let Some(annotation) = function.type_ {
        assert_eq!(
            checker.get_type_at_location(node_ref(annotation)),
            Ok(returned)
        );
    }
    let NodeData::Block(block) = &parsed.arena.get(function.body).unwrap().data else {
        panic!("function expressions must retain their block body")
    };
    let body = match block.statements.nodes.as_slice() {
        [] => None,
        [statement] => {
            let NodeData::ReturnStatement(returned) = &parsed.arena.get(*statement).unwrap().data
            else {
                panic!("expected one return statement")
            };
            let expression = node_ref(returned.expression.unwrap());
            Some((
                expression,
                checker.get_type_at_location(expression).unwrap(),
            ))
        }
        _ => panic!("each control has an empty body or one return statement"),
    };
    FunctionState {
        owner,
        binding,
        callable,
        signature,
        parameters,
        returned,
        body,
    }
}

#[test]
fn function_expressions_preserve_returns_parameters_and_warm_identity() {
    for (source, expected) in [
        (
            "const echo = function(value: number) { return value; }; const result = echo(1);",
            "number",
        ),
        (
            "const echo = function(value: string): string { return value; }; const result = echo('ok');",
            "string",
        ),
        (
            "const echo = function() { return 1; }; const result = echo();",
            "number",
        ),
        ("const echo = function() {}; const result = echo();", "void"),
    ] {
        let parsed = parse_source_file(source);
        let (_, _, expression) = variable(&parsed, "echo");
        let (_, _, call) = variable(&parsed, "result");
        for first in [None, Some(expression), Some(call)] {
            let mut checker = context(&parsed, false);
            let early = first.map(|node| checker.get_type_at_location(node).unwrap());
            checker.check_source_file(FILE).unwrap();
            assert!(
                checker.diagnostics().is_empty(),
                "{:?}",
                checker.diagnostics()
            );
            let cold = function_state(&mut checker, &parsed, "echo");
            assert_eq!(checker.type_to_string(cold.returned).unwrap(), expected);
            assert_eq!(checker.get_type_at_location(call), Ok(cold.returned));
            assert_eq!(signature(&checker, call), cold.signature);
            if let Some(type_) = early {
                assert_eq!(
                    type_,
                    if first == Some(expression) {
                        cold.callable
                    } else {
                        cold.returned
                    }
                );
            }
            if let [(parameter, type_)] = cold.parameters.as_slice() {
                let (body, body_type) = cold.body.unwrap();
                assert_eq!(body_type, *type_);
                assert_eq!(body_type, cold.returned);
                assert_eq!(checker.get_symbol_at_location(body), Ok(Some(*parameter)));
            }

            let warm = counts(&checker);
            checker.recheck_source_file(FILE).unwrap();
            assert_eq!(function_state(&mut checker, &parsed, "echo"), cold);
            assert_eq!(checker.get_type_at_location(call), Ok(cold.returned));
            assert_eq!(signature(&checker, call), cold.signature);
            assert_eq!(counts(&checker), warm);
            assert!(checker.diagnostics().is_empty());
        }
    }
}

#[test]
fn function_expression_body_and_call_errors_keep_exact_sites_on_replay() {
    let parsed = parse_source_file(concat!(
        "const bad = function(value: string): number { return value; };\n",
        "const result = bad(1);\n",
    ));
    let (_, _, expression) = variable(&parsed, "bad");
    let (_, _, call) = variable(&parsed, "result");
    let NodeData::FunctionExpression(function) = &parsed.arena.get(expression.node).unwrap().data
    else {
        unreachable!()
    };
    let NodeData::Block(block) = &parsed.arena.get(function.body).unwrap().data else {
        unreachable!()
    };
    let returned = NodeRef::new(parsed.arena.id(), FILE, block.statements.nodes[0]);
    let NodeData::CallExpression(call_data) = &parsed.arena.get(call.node).unwrap().data else {
        unreachable!()
    };
    let argument = NodeRef::new(parsed.arena.id(), FILE, call_data.arguments.nodes[0]);
    for first in [None, Some(expression), Some(call)] {
        let mut checker = context(&parsed, false);
        if let Some(node) = first {
            checker.get_type_at_location(node).unwrap();
        }
        checker.check_source_file(FILE).unwrap();
        let diagnostics = checker.diagnostics().as_slice();
        assert_eq!(diagnostics.len(), 2, "{diagnostics:?}");
        for (diagnostic, (node, code, message)) in diagnostics.iter().zip([
            (
                returned,
                2322,
                "Type 'string' is not assignable to type 'number'.",
            ),
            (
                argument,
                2345,
                "Argument of type 'number' is not assignable to parameter of type 'string'.",
            ),
        ]) {
            assert_eq!(diagnostic.node, Some(node));
            assert_eq!(diagnostic.range_override, None);
            assert_eq!(diagnostic.diagnostic.code(), code);
            assert_eq!(diagnostic.diagnostic.render().unwrap(), message);
            assert!(diagnostic.related_information.is_empty());
        }
        let cold = function_state(&mut checker, &parsed, "bad");
        let number = checker.store().intrinsic_bootstrap().unwrap().number_type;
        let string = checker.store().intrinsic_bootstrap().unwrap().string_type;
        assert_eq!(cold.returned, number);
        assert_eq!(cold.parameters[0].1, string);
        let (body, body_type) = cold.body.unwrap();
        assert_eq!(body_type, string);
        assert_eq!(
            checker.get_symbol_at_location(body),
            Ok(Some(cold.parameters[0].0))
        );
        assert_eq!(checker.get_type_at_location(call), Ok(number));
        assert_eq!(signature(&checker, call), cold.signature);

        let warm = counts(&checker);
        let diagnostics = checker.diagnostics().clone();
        checker.recheck_source_file(FILE).unwrap();
        assert_eq!(function_state(&mut checker, &parsed, "bad"), cold);
        assert_eq!(checker.get_type_at_location(call), Ok(number));
        assert_eq!(signature(&checker, call), cold.signature);
        assert_eq!(counts(&checker), warm);
        assert_eq!(checker.diagnostics(), &diagnostics);
    }
}

#[test]
fn function_expression_untyped_parameter_respects_no_implicit_any() {
    let parsed = parse_source_file(concat!(
        "const echo = function(value): number { return value; };\n",
        "const result = echo(1);\n",
    ));
    let (_, _, expression) = variable(&parsed, "echo");
    let (_, _, call) = variable(&parsed, "result");
    let NodeData::FunctionExpression(function) = &parsed.arena.get(expression.node).unwrap().data
    else {
        unreachable!()
    };
    let parameter = NodeRef::new(parsed.arena.id(), FILE, function.parameters.nodes[0]);
    for no_implicit_any in [false, true] {
        for first in [None, Some(expression), Some(call)] {
            let mut checker = context(&parsed, no_implicit_any);
            if let Some(node) = first {
                checker.get_type_at_location(node).unwrap();
            }
            checker.check_source_file(FILE).unwrap();
            if no_implicit_any {
                let [diagnostic] = checker.diagnostics().as_slice() else {
                    panic!("expected exactly one implicit-any diagnostic")
                };
                assert_eq!(diagnostic.node, Some(parameter));
                assert_eq!(diagnostic.range_override, None);
                assert_eq!(diagnostic.diagnostic.code(), 7006);
                assert_eq!(
                    diagnostic.diagnostic.render().unwrap(),
                    "Parameter 'value' implicitly has an 'any' type.",
                );
                assert!(diagnostic.related_information.is_empty());
            } else {
                assert!(checker.diagnostics().is_empty());
            }
            let cold = function_state(&mut checker, &parsed, "echo");
            let any = checker.store().intrinsic_bootstrap().unwrap().any_type;
            let number = checker.store().intrinsic_bootstrap().unwrap().number_type;
            assert_eq!(cold.parameters, [(symbol(&checker, parameter), any)]);
            assert_eq!(cold.returned, number);
            let (body, body_type) = cold.body.unwrap();
            assert_eq!(body_type, any);
            assert_eq!(
                checker.get_symbol_at_location(body),
                Ok(Some(cold.parameters[0].0))
            );
            assert_eq!(checker.get_type_at_location(call), Ok(number));
            assert_eq!(signature(&checker, call), cold.signature);

            let warm = counts(&checker);
            let diagnostics = checker.diagnostics().clone();
            checker.recheck_source_file(FILE).unwrap();
            assert_eq!(function_state(&mut checker, &parsed, "echo"), cold);
            assert_eq!(checker.get_type_at_location(call), Ok(number));
            assert_eq!(signature(&checker, call), cold.signature);
            assert_eq!(counts(&checker), warm);
            assert_eq!(checker.diagnostics(), &diagnostics);
        }
    }
}

#[test]
fn named_function_expression_self_name_has_its_own_scope() {
    let parsed = parse_source_file(concat!(
        "const self: string = 'outer';\n",
        "const recurse = function self(value: number): number { return self(value); };\n",
        "const result = recurse(1);\n",
        "const outside = self;\n",
    ));
    let (_, _, expression) = variable(&parsed, "recurse");
    let (_, _, call) = variable(&parsed, "result");
    let (outer, _, _) = variable(&parsed, "self");
    let (_, _, outside) = variable(&parsed, "outside");
    for first in [None, Some(expression), Some(call)] {
        let mut checker = context(&parsed, false);
        if let Some(node) = first {
            checker.get_type_at_location(node).unwrap();
        }
        checker.check_source_file(FILE).unwrap();
        assert!(
            checker.diagnostics().is_empty(),
            "{:?}",
            checker.diagnostics()
        );
        let cold = function_state(&mut checker, &parsed, "recurse");
        let number = checker.store().intrinsic_bootstrap().unwrap().number_type;
        let string = checker.store().intrinsic_bootstrap().unwrap().string_type;
        let outer = symbol(&checker, outer);
        assert_ne!(cold.owner, outer);
        assert_eq!(cold.returned, number);
        assert_eq!(cold.parameters[0].1, number);
        let (recursive_call, body_type) = cold.body.unwrap();
        assert_eq!(body_type, number);
        let NodeData::CallExpression(recursive) =
            &parsed.arena.get(recursive_call.node).unwrap().data
        else {
            panic!("the body must call the self-name")
        };
        let self_read = NodeRef::new(parsed.arena.id(), FILE, recursive.expression);
        let parameter_read = NodeRef::new(parsed.arena.id(), FILE, recursive.arguments.nodes[0]);
        assert_eq!(
            checker.get_symbol_at_location(self_read),
            Ok(Some(cold.owner))
        );
        assert_eq!(checker.get_type_at_location(self_read), Ok(cold.callable));
        assert_eq!(
            checker.get_symbol_at_location(parameter_read),
            Ok(Some(cold.parameters[0].0))
        );
        assert_eq!(checker.get_type_at_location(parameter_read), Ok(number));
        assert_eq!(signature(&checker, recursive_call), cold.signature);
        assert_eq!(signature(&checker, call), cold.signature);
        assert_eq!(checker.get_type_at_location(call), Ok(number));
        assert_eq!(checker.get_symbol_at_location(outside), Ok(Some(outer)));
        assert_eq!(checker.get_type_at_location(outside), Ok(string));
        let source = checker.source_file(FILE).unwrap().node_ref();
        let locals = checker.file(FILE).unwrap().1.locals(source).unwrap();
        assert_eq!(
            checker
                .store()
                .symbol_table(locals)
                .unwrap()
                .get_source("self"),
            Some(outer)
        );

        let warm = counts(&checker);
        checker.recheck_source_file(FILE).unwrap();
        assert_eq!(function_state(&mut checker, &parsed, "recurse"), cold);
        assert_eq!(
            checker.get_symbol_at_location(self_read),
            Ok(Some(cold.owner))
        );
        assert_eq!(checker.get_type_at_location(self_read), Ok(cold.callable));
        assert_eq!(signature(&checker, recursive_call), cold.signature);
        assert_eq!(signature(&checker, call), cold.signature);
        assert_eq!(checker.get_type_at_location(call), Ok(number));
        assert_eq!(checker.get_symbol_at_location(outside), Ok(Some(outer)));
        assert_eq!(checker.get_type_at_location(outside), Ok(string));
        assert_eq!(counts(&checker), warm);
        assert!(checker.diagnostics().is_empty());
    }
}

#[test]
#[allow(clippy::too_many_lines)] // Keep the original source and its separate callable identities together.
fn contextual_function_expression_return_keeps_its_literal_and_source_identity() {
    let parsed = parse_source_file(
        "const echo: (value: number) => 1 = function(value: number) { return 1; };",
    );
    let (binding, binding_name, expression) = variable(&parsed, "echo");
    let NodeData::VariableDeclaration(variable) = &parsed.arena.get(binding.node).unwrap().data
    else {
        unreachable!();
    };
    let annotation = NodeRef::new(parsed.arena.id(), FILE, variable.type_.unwrap());
    let NodeData::FunctionExpression(function) = &parsed.arena.get(expression.node).unwrap().data
    else {
        unreachable!();
    };
    let parameter = NodeRef::new(parsed.arena.id(), FILE, function.parameters.nodes[0]);
    for query_first in [false, true] {
        let mut checker = context(&parsed, false);
        if query_first {
            checker.get_type_at_location(expression).unwrap();
        }
        checker.check_source_file(FILE).unwrap();
        let owner = symbol(&checker, expression);
        let binding = symbol(&checker, binding);
        let parameter_symbol = symbol(&checker, parameter);
        let callable = checker.get_type_at_location(expression).unwrap();
        let target = checker.get_type_at_location(annotation).unwrap();
        let own_signature = signature(&checker, expression);
        let returned = checker.get_return_type_of_signature(own_signature).unwrap();
        let number = checker.store().intrinsic_bootstrap().unwrap().number_type;
        assert_ne!(owner, binding);
        assert_ne!(callable, target);
        assert_ne!(returned, number);
        assert_eq!(checker.type_to_string(returned).unwrap(), "1");
        assert_eq!(
            checker.store().symbol(owner).unwrap().flags(),
            SymbolFlags::FUNCTION
        );
        assert_eq!(
            checker.store().type_payload(callable).unwrap().symbol(),
            Some(owner)
        );
        assert_eq!(
            checker
                .store()
                .value_symbol_links(owner)
                .unwrap()
                .resolved_type,
            Some(callable)
        );
        assert_eq!(
            checker
                .store()
                .value_symbol_links(binding)
                .unwrap()
                .resolved_type,
            Some(target)
        );
        assert_eq!(checker.get_type_at_location(binding_name), Ok(target));
        assert_eq!(checker.get_type_at_location(parameter), Ok(number));
        assert_eq!(
            checker
                .store()
                .symbol(parameter_symbol)
                .unwrap()
                .declarations(),
            Some(&[parameter][..])
        );
        assert_eq!(
            checker
                .store()
                .value_symbol_links(parameter_symbol)
                .unwrap()
                .resolved_type,
            Some(number)
        );
        let record = checker.store().signature(own_signature).unwrap();
        assert_eq!(record.declaration(), Some(expression));
        assert_eq!(record.parameters(), &[parameter_symbol]);
        assert_eq!(record.resolved_return_type(), Some(returned));
        assert!(checker.diagnostics().is_empty());
        let warm = counts(&checker);
        checker.recheck_source_file(FILE).unwrap();
        assert_eq!(checker.get_type_at_location(expression), Ok(callable));
        assert_eq!(checker.get_type_at_location(annotation), Ok(target));
        assert_eq!(checker.get_type_at_location(binding_name), Ok(target));
        assert_eq!(checker.get_type_at_location(parameter), Ok(number));
        assert_eq!(signature(&checker, expression), own_signature);
        assert_eq!(
            checker.get_return_type_of_signature(own_signature),
            Ok(returned),
        );
        assert_eq!(counts(&checker), warm);
        assert!(checker.diagnostics().is_empty());
    }
}
