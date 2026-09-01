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

const PROVIDER: FileId = FileId::new(8_281);

fn module_body_context<'arena>(
    parsed: &'arena ParseResult,
    provider: &'arena ParseResult,
) -> CanonicalCheckerContext<'arena> {
    use ts_checker::semantic::{
        CanonicalModuleResolutionEntry, CanonicalModuleResolutionManifestInput,
        CanonicalModuleResolutionMode, CanonicalResolvedModuleInput,
    };

    let files = [
        (FILE, parsed, "\"/project/function-expressions.ts\""),
        (PROVIDER, provider, "\"/project/provider.ts\""),
    ];
    let mut binder = CanonicalBinder::new();
    for &(file, parsed, name) in &files {
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source(name),
                    CanonicalSourceLanguage::TypeScript,
                    false,
                    CanonicalModuleState::External,
                ),
            )
            .unwrap();
    }
    for &(file, parsed, _) in &files {
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
    }
    let mut imports = parsed.arena.iter().filter_map(|(_, record)| {
        let NodeData::ImportDeclaration(import) = &record.data else {
            return None;
        };
        Some(import.module_specifier)
    });
    let specifier = imports.next().unwrap();
    assert!(imports.next().is_none());
    CanonicalCheckerContext::new_with_module_resolutions(
        binder.finish(),
        files
            .into_iter()
            .map(|(file, parsed, _)| (file, &parsed.arena))
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
        CanonicalModuleResolutionManifestInput::new([CanonicalModuleResolutionEntry::resolved(
            NodeRef::new(parsed.arena.id(), FILE, specifier),
            CanonicalResolvedModuleInput::new(
                PROVIDER,
                CanonicalModuleResolutionMode::Esm,
                CanonicalModuleResolutionMode::Esm,
            ),
        )]),
    )
    .unwrap()
}

fn body_statements(parsed: &ParseResult, name: &str) -> Vec<NodeRef> {
    let (_, _, expression) = variable(parsed, name);
    let NodeData::FunctionExpression(function) = &parsed.arena.get(expression.node).unwrap().data
    else {
        panic!("expected the actual function expression");
    };
    let body = parsed.arena.get(function.body).unwrap();
    assert_eq!(body.parent, Some(expression.node));
    let NodeData::Block(block) = &body.data else {
        panic!("the function must retain its block");
    };
    assert!(block.statements.nodes.len() > 1);
    block
        .statements
        .nodes
        .iter()
        .map(|&statement| {
            assert_eq!(
                parsed.arena.get(statement).unwrap().parent,
                Some(function.body),
            );
            NodeRef::new(parsed.arena.id(), FILE, statement)
        })
        .collect()
}

fn body_return_expression(parsed: &ParseResult, statement: NodeRef) -> NodeRef {
    let NodeData::ReturnStatement(returned) = &parsed.arena.get(statement.node).unwrap().data
    else {
        panic!("expected the actual return statement");
    };
    let expression = returned.expression.unwrap();
    assert_eq!(
        parsed.arena.get(expression).unwrap().parent,
        Some(statement.node),
    );
    NodeRef::new(parsed.arena.id(), FILE, expression)
}

fn body_early_return(parsed: &ParseResult, statement: NodeRef) -> (NodeRef, NodeRef) {
    let NodeData::IfStatement(conditional) = &parsed.arena.get(statement.node).unwrap().data else {
        panic!("expected the early-return condition");
    };
    assert!(conditional.else_statement.is_none());
    let condition = NodeRef::new(parsed.arena.id(), FILE, conditional.expression);
    let returned = NodeRef::new(parsed.arena.id(), FILE, conditional.then_statement);
    assert_eq!(
        parsed.arena.get(returned.node).unwrap().parent,
        Some(statement.node),
    );
    (condition, body_return_expression(parsed, returned))
}

#[derive(Debug, Eq, PartialEq)]
struct BodyFunctionState {
    owner: SemanticSymbolId,
    binding: SemanticSymbolId,
    callable: TypeId,
    binding_type: TypeId,
    signature: SignatureId,
    parameters: Vec<(SemanticSymbolId, TypeId)>,
    returned: TypeId,
}

#[allow(clippy::too_many_lines)] // Check the actual function, binding, signature, and parameters together.
fn body_function_state(
    checker: &mut CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    name: &str,
) -> BodyFunctionState {
    let (binding_node, binding_name, declaration) = variable(parsed, name);
    let NodeData::FunctionExpression(function) = &parsed.arena.get(declaration.node).unwrap().data
    else {
        panic!("expected a function expression");
    };
    body_statements(parsed, name);
    let owner = symbol(checker, declaration);
    let binding = symbol(checker, binding_node);
    assert_ne!(owner, binding);
    let owner_record = checker.store().symbol(owner).unwrap();
    assert_eq!(owner_record.flags(), SymbolFlags::FUNCTION);
    assert_eq!(owner_record.declarations(), Some(&[declaration][..]));
    assert_eq!(owner_record.value_declaration(), Some(declaration));
    assert_eq!(
        checker.store().symbol(binding).unwrap().value_declaration(),
        Some(binding_node),
    );
    let callable = checker.get_type_at_location(declaration).unwrap();
    let binding_type = checker.get_type_at_location(binding_name).unwrap();
    assert_eq!(
        checker
            .store()
            .value_symbol_links(owner)
            .unwrap()
            .resolved_type,
        Some(callable),
    );
    if let Some(name) = function.name {
        let name = NodeRef::new(parsed.arena.id(), FILE, name);
        assert_eq!(checker.get_symbol_at_location(name), Ok(Some(owner)));
        assert_eq!(checker.get_type_at_location(name), Ok(callable));
    }
    let signature = signature(checker, declaration);
    let record = checker.store().type_payload(callable).unwrap();
    assert_eq!(record.symbol(), Some(owner));
    let TypeData::Object(object) = record.data() else {
        panic!("the source function must own its callable object");
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
            assert_eq!(
                parsed.arena.get(node).unwrap().parent,
                Some(declaration.node)
            );
            let NodeData::ParameterDeclaration(parameter) = &parsed.arena.get(node).unwrap().data
            else {
                panic!("expected an ordinary parameter");
            };
            let declaration = NodeRef::new(parsed.arena.id(), FILE, node);
            let name = NodeRef::new(parsed.arena.id(), FILE, parameter.name);
            let annotation = NodeRef::new(parsed.arena.id(), FILE, parameter.type_.unwrap());
            let owner = symbol(checker, declaration);
            let record = checker.store().symbol(owner).unwrap();
            assert_eq!(record.declarations(), Some(&[declaration][..]));
            assert_eq!(record.value_declaration(), Some(declaration));
            let type_ = checker.get_type_at_location(name).unwrap();
            assert_eq!(checker.get_type_at_location(annotation), Ok(type_));
            assert_eq!(checker.get_symbol_at_location(name), Ok(Some(owner)));
            assert_eq!(
                checker
                    .store()
                    .value_symbol_links(owner)
                    .unwrap()
                    .resolved_type,
                Some(type_),
            );
            (owner, type_)
        })
        .collect::<Vec<_>>();
    let returned = checker.get_return_type_of_signature(signature).unwrap();
    let record = checker.store().signature(signature).unwrap();
    assert_eq!(record.declaration(), Some(declaration));
    assert_eq!(
        record.parameters(),
        parameters
            .iter()
            .map(|&(owner, _)| owner)
            .collect::<Vec<_>>(),
    );
    assert!(record.type_parameters().is_empty());
    assert_eq!(record.resolved_return_type(), Some(returned));
    assert_eq!(record.target(), None);
    assert_eq!(record.mapper(), None);
    if let Some(annotation) = function.type_ {
        assert_eq!(
            checker.get_type_at_location(NodeRef::new(parsed.arena.id(), FILE, annotation)),
            Ok(returned),
        );
    }
    BodyFunctionState {
        owner,
        binding,
        callable,
        binding_type,
        signature,
        parameters,
        returned,
    }
}

fn body_literal_type(
    checker: &mut CanonicalCheckerContext<'_>,
    expression: NodeRef,
    expected: ts_checker::semantic::type_records::LiteralValue,
) -> TypeId {
    let type_ = checker.get_type_at_location(expression).unwrap();
    let TypeData::Literal(literal) = checker.store().type_payload(type_).unwrap().data() else {
        panic!("expected the checked literal type");
    };
    assert_eq!(literal.value, expected);
    let regular = literal.regular_type;
    let TypeData::Literal(literal) = checker.store().type_payload(regular).unwrap().data() else {
        panic!("the regular type must keep the same literal");
    };
    assert_eq!(literal.value, expected);
    assert_eq!(literal.regular_type, regular);
    type_
}

#[derive(Debug, PartialEq)]
struct BodySnapshot {
    function: BodyFunctionState,
    types: Vec<TypeId>,
    signatures: Vec<SignatureId>,
    counts: [usize; 4],
    diagnostics: ts_checker::semantic::CanonicalCheckerDiagnostics,
}

fn check_body_replay(
    checker: &CanonicalCheckerContext<'_>,
    function: BodyFunctionState,
    types: Vec<TypeId>,
    signatures: Vec<SignatureId>,
    cold: &mut Option<BodySnapshot>,
) {
    let current = BodySnapshot {
        function,
        types,
        signatures,
        counts: counts(checker),
        diagnostics: checker.diagnostics().clone(),
    };
    if let Some(previous) = cold {
        assert_eq!(&current, previous);
    } else {
        *cold = Some(current);
    }
}

#[test]
#[allow(clippy::too_many_lines)] // Keep the real local, early return, call, and replay checks together.
fn function_expression_statement_list_preserves_locals_and_early_returns() {
    use ts_checker::semantic::type_records::LiteralValue;

    let parsed = parse_source_file(concat!(
        "const echo = function(value: string, early: boolean) {\n",
        "  const local = value;\n",
        "  if (early) return local;\n",
        "  return value;\n",
        "};\n",
        "const result = echo('ok', true);\n",
    ));
    let (_, _, expression) = variable(&parsed, "echo");
    let (_, _, call) = variable(&parsed, "result");
    let (local, local_name, initializer) = variable(&parsed, "local");
    let statements = body_statements(&parsed, "echo");
    assert_eq!(statements.len(), 3);
    let (condition, early_return) = body_early_return(&parsed, statements[1]);
    let later_return = body_return_expression(&parsed, statements[2]);
    let NodeData::CallExpression(call_data) = &parsed.arena.get(call.node).unwrap().data else {
        unreachable!();
    };
    let arguments = call_data
        .arguments
        .nodes
        .iter()
        .map(|&node| NodeRef::new(parsed.arena.id(), FILE, node))
        .collect::<Vec<_>>();
    for first in [None, Some(expression), Some(call)] {
        let mut checker = context(&parsed, true);
        let early = first.map(|node| checker.get_type_at_location(node).unwrap());
        checker.check_source_file(FILE).unwrap();
        let mut cold = None;
        for replay in 0..3 {
            if replay != 0 {
                checker.recheck_source_file(FILE).unwrap();
            }
            let state = body_function_state(&mut checker, &parsed, "echo");
            let string = checker.store().intrinsic_bootstrap().unwrap().string_type;
            let boolean = checker.store().intrinsic_bootstrap().unwrap().boolean_type;
            let local_symbol = symbol(&checker, local);
            assert_eq!(state.binding_type, state.callable);
            assert_eq!(state.returned, string);
            assert_eq!(state.parameters.len(), 2);
            assert_eq!(state.parameters[0].1, string);
            assert_eq!(state.parameters[1].1, boolean);
            for (node, expected_symbol) in [
                (initializer, state.parameters[0].0),
                (local_name, local_symbol),
                (early_return, local_symbol),
                (later_return, state.parameters[0].0),
            ] {
                assert_eq!(checker.get_type_at_location(node), Ok(string));
                assert_eq!(
                    checker.get_symbol_at_location(node),
                    Ok(Some(expected_symbol))
                );
            }
            assert_ne!(local_symbol, state.parameters[0].0);
            assert_eq!(checker.get_type_at_location(condition), Ok(boolean));
            assert_eq!(
                checker.get_symbol_at_location(condition),
                Ok(Some(state.parameters[1].0)),
            );
            let argument = body_literal_type(
                &mut checker,
                arguments[0],
                LiteralValue::String("ok".to_owned()),
            );
            let flag = body_literal_type(&mut checker, arguments[1], LiteralValue::Boolean(true));
            assert_eq!(checker.get_type_at_location(call), Ok(string));
            let called = signature(&checker, call);
            assert_eq!(called, state.signature);
            if let Some(early) = early {
                assert_eq!(
                    early,
                    if first == Some(expression) {
                        state.callable
                    } else {
                        string
                    }
                );
            }
            assert!(
                checker.diagnostics().is_empty(),
                "{:?}",
                checker.diagnostics()
            );
            check_body_replay(
                &checker,
                state,
                vec![string, boolean, argument, flag],
                vec![called],
                &mut cold,
            );
        }
    }
}

#[test]
#[allow(clippy::too_many_lines)] // Check both declared and assigned parameter types across the block.
fn function_expression_statement_list_tracks_its_parameter_write_in_a_block() {
    use ts_checker::semantic::type_records::LiteralValue;

    let parsed = parse_source_file(concat!(
        "const replace = function(value: string | number, replacement: string): string {\n",
        "  { value = replacement; }\n",
        "  const after = value;\n",
        "  return after;\n",
        "};\n",
        "const result = replace(1, 'done');\n",
    ));
    let (_, _, expression) = variable(&parsed, "replace");
    let (_, _, call) = variable(&parsed, "result");
    let (after, after_name, later_read) = variable(&parsed, "after");
    let statements = body_statements(&parsed, "replace");
    assert_eq!(statements.len(), 3);
    let NodeData::Block(block) = &parsed.arena.get(statements[0].node).unwrap().data else {
        panic!("the write must stay in its nested block");
    };
    let [statement] = block.statements.nodes.as_slice() else {
        panic!("expected the one plain assignment");
    };
    let NodeData::ExpressionStatement(statement) = &parsed.arena.get(*statement).unwrap().data
    else {
        unreachable!();
    };
    let assignment = NodeRef::new(parsed.arena.id(), FILE, statement.expression);
    let NodeData::BinaryExpression(write) = &parsed.arena.get(assignment.node).unwrap().data else {
        unreachable!();
    };
    assert_eq!(
        parsed.arena.get(write.operator_token).unwrap().kind,
        ts_ast::SyntaxKind::EqualsToken,
    );
    let left = NodeRef::new(parsed.arena.id(), FILE, write.left);
    let right = NodeRef::new(parsed.arena.id(), FILE, write.right);
    let returned = body_return_expression(&parsed, statements[2]);
    let NodeData::CallExpression(call_data) = &parsed.arena.get(call.node).unwrap().data else {
        unreachable!();
    };
    let arguments = call_data
        .arguments
        .nodes
        .iter()
        .map(|&node| NodeRef::new(parsed.arena.id(), FILE, node))
        .collect::<Vec<_>>();
    for first in [None, Some(expression), Some(call)] {
        let mut checker = context(&parsed, true);
        let early = first.map(|node| checker.get_type_at_location(node).unwrap());
        checker.check_source_file(FILE).unwrap();
        let mut cold = None;
        for replay in 0..3 {
            if replay != 0 {
                checker.recheck_source_file(FILE).unwrap();
            }
            let state = body_function_state(&mut checker, &parsed, "replace");
            let string = checker.store().intrinsic_bootstrap().unwrap().string_type;
            let number = checker.store().intrinsic_bootstrap().unwrap().number_type;
            assert_eq!(state.parameters.len(), 2);
            let TypeData::Union(union) = checker
                .store()
                .type_payload(state.parameters[0].1)
                .unwrap()
                .data()
            else {
                panic!("the written parameter must retain both declared types");
            };
            assert_eq!(union.union.types.len(), 2);
            assert!(union.union.types.contains(&string));
            assert!(union.union.types.contains(&number));
            assert_eq!(state.parameters[1].1, string);
            assert_eq!(state.returned, string);
            assert_eq!(state.binding_type, state.callable);
            assert_eq!(
                checker.get_symbol_at_location(left),
                Ok(Some(state.parameters[0].0))
            );
            assert_eq!(
                checker.get_type_at_location(left),
                Ok(state.parameters[0].1)
            );
            assert_eq!(
                checker.get_symbol_at_location(right),
                Ok(Some(state.parameters[1].0))
            );
            assert_eq!(checker.get_type_at_location(right), Ok(string));
            assert_eq!(checker.get_type_at_location(assignment), Ok(string));
            assert_eq!(
                checker.get_symbol_at_location(later_read),
                Ok(Some(state.parameters[0].0))
            );
            let after_symbol = symbol(&checker, after);
            assert_ne!(after_symbol, state.parameters[0].0);
            for node in [later_read, after_name, returned] {
                assert_eq!(checker.get_type_at_location(node), Ok(string));
            }
            assert_eq!(
                checker.get_symbol_at_location(returned),
                Ok(Some(after_symbol))
            );
            let argument = body_literal_type(
                &mut checker,
                arguments[0],
                LiteralValue::Number(ts_jsnum::Number::new(1.0)),
            );
            let replacement = body_literal_type(
                &mut checker,
                arguments[1],
                LiteralValue::String("done".to_owned()),
            );
            assert_eq!(checker.get_type_at_location(call), Ok(string));
            let called = signature(&checker, call);
            assert_eq!(called, state.signature);
            if let Some(early) = early {
                assert_eq!(
                    early,
                    if first == Some(expression) {
                        state.callable
                    } else {
                        string
                    }
                );
            }
            assert!(
                checker.diagnostics().is_empty(),
                "{:?}",
                checker.diagnostics()
            );
            check_body_replay(
                &checker,
                state,
                vec![string, number, argument, replacement],
                vec![called],
                &mut cold,
            );
        }
    }
}

#[test]
#[allow(clippy::too_many_lines)] // Keep error sites, recovery types, and raw replay diagnostics in one control.
fn function_expression_statement_list_checks_later_return_and_call_errors() {
    use ts_checker::semantic::type_records::LiteralValue;

    let parsed = parse_source_file(concat!(
        "const bad = function(value: string, early: boolean): number {\n",
        "  const local = value;\n",
        "  if (early) return 1;\n",
        "  return local;\n",
        "};\n",
        "const result = bad(1, false);\n",
    ));
    let (_, _, expression) = variable(&parsed, "bad");
    let (_, _, call) = variable(&parsed, "result");
    let (local, local_name, initializer) = variable(&parsed, "local");
    let statements = body_statements(&parsed, "bad");
    assert_eq!(statements.len(), 3);
    let (_, early_return) = body_early_return(&parsed, statements[1]);
    let returned = body_return_expression(&parsed, statements[2]);
    let NodeData::CallExpression(call_data) = &parsed.arena.get(call.node).unwrap().data else {
        unreachable!();
    };
    let arguments = call_data
        .arguments
        .nodes
        .iter()
        .map(|&node| NodeRef::new(parsed.arena.id(), FILE, node))
        .collect::<Vec<_>>();
    for first in [None, Some(expression), Some(call)] {
        let mut checker = context(&parsed, true);
        let early = first.map(|node| checker.get_type_at_location(node).unwrap());
        checker.check_source_file(FILE).unwrap();
        let mut cold = None;
        for replay in 0..3 {
            if replay != 0 {
                checker.recheck_source_file(FILE).unwrap();
            }
            let state = body_function_state(&mut checker, &parsed, "bad");
            let string = checker.store().intrinsic_bootstrap().unwrap().string_type;
            let number = checker.store().intrinsic_bootstrap().unwrap().number_type;
            let boolean = checker.store().intrinsic_bootstrap().unwrap().boolean_type;
            assert_eq!(state.returned, number);
            assert_eq!(state.binding_type, state.callable);
            assert_eq!(state.parameters.len(), 2);
            assert_eq!(state.parameters[0].1, string);
            assert_eq!(state.parameters[1].1, boolean);
            for node in [initializer, local_name, returned] {
                assert_eq!(checker.get_type_at_location(node), Ok(string));
            }
            assert_eq!(
                checker.get_symbol_at_location(initializer),
                Ok(Some(state.parameters[0].0))
            );
            assert_eq!(
                checker.get_symbol_at_location(returned),
                Ok(Some(symbol(&checker, local)))
            );
            let literal_return = body_literal_type(
                &mut checker,
                early_return,
                LiteralValue::Number(ts_jsnum::Number::new(1.0)),
            );
            let bad_argument = body_literal_type(
                &mut checker,
                arguments[0],
                LiteralValue::Number(ts_jsnum::Number::new(1.0)),
            );
            let flag = body_literal_type(&mut checker, arguments[1], LiteralValue::Boolean(false));
            assert_eq!(checker.get_type_at_location(call), Ok(number));
            let called = signature(&checker, call);
            assert_eq!(called, state.signature);
            if let Some(early) = early {
                assert_eq!(
                    early,
                    if first == Some(expression) {
                        state.callable
                    } else {
                        number
                    }
                );
            }
            let diagnostics = checker.diagnostics().as_slice();
            assert_eq!(diagnostics.len(), 2, "{diagnostics:?}");
            for (diagnostic, (node, code, message)) in diagnostics.iter().zip([
                (
                    statements[2],
                    2322,
                    "Type 'string' is not assignable to type 'number'.",
                ),
                (
                    arguments[0],
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
            check_body_replay(
                &checker,
                state,
                vec![string, number, literal_return, bad_argument, flag],
                vec![called],
                &mut cold,
            );
        }
    }
}

#[test]
#[allow(clippy::too_many_lines)] // Compare both source returns with the separate contextual signature.
fn contextual_function_expression_statement_list_keeps_literal_returns() {
    use ts_checker::semantic::type_records::LiteralValue;

    let parsed = parse_source_file(concat!(
        "const one: (value: number) => 1 = function(value: number) {\n",
        "  const local = value;\n",
        "  if (local) return 1;\n",
        "  return 1;\n",
        "};\n",
        "const result = one(5);\n",
    ));
    let (binding, _, expression) = variable(&parsed, "one");
    let (_, _, call) = variable(&parsed, "result");
    let (local, local_name, initializer) = variable(&parsed, "local");
    let NodeData::VariableDeclaration(variable_data) =
        &parsed.arena.get(binding.node).unwrap().data
    else {
        unreachable!();
    };
    let annotation = NodeRef::new(parsed.arena.id(), FILE, variable_data.type_.unwrap());
    let NodeData::FunctionType(target) = &parsed.arena.get(annotation.node).unwrap().data else {
        unreachable!();
    };
    let return_annotation = NodeRef::new(parsed.arena.id(), FILE, target.type_.unwrap());
    let statements = body_statements(&parsed, "one");
    assert_eq!(statements.len(), 3);
    let (condition, early_return) = body_early_return(&parsed, statements[1]);
    let later_return = body_return_expression(&parsed, statements[2]);
    let NodeData::CallExpression(call_data) = &parsed.arena.get(call.node).unwrap().data else {
        unreachable!();
    };
    let argument = NodeRef::new(parsed.arena.id(), FILE, call_data.arguments.nodes[0]);
    for first in [None, Some(expression), Some(call)] {
        let mut checker = context(&parsed, true);
        let early = first.map(|node| checker.get_type_at_location(node).unwrap());
        checker.check_source_file(FILE).unwrap();
        let mut cold = None;
        for replay in 0..3 {
            if replay != 0 {
                checker.recheck_source_file(FILE).unwrap();
            }
            let state = body_function_state(&mut checker, &parsed, "one");
            let number = checker.store().intrinsic_bootstrap().unwrap().number_type;
            assert_eq!(state.parameters.len(), 1);
            assert_eq!(state.parameters[0].1, number);
            assert_ne!(state.callable, state.binding_type);
            assert_eq!(
                checker.get_type_at_location(annotation),
                Ok(state.binding_type)
            );
            assert_eq!(
                checker.get_type_at_location(return_annotation),
                Ok(state.returned)
            );
            assert_ne!(state.returned, number);
            let TypeData::Literal(returned) =
                checker.store().type_payload(state.returned).unwrap().data()
            else {
                panic!("the contextual return must stay a literal");
            };
            assert_eq!(
                returned.value,
                LiteralValue::Number(ts_jsnum::Number::new(1.0))
            );
            assert_eq!(returned.regular_type, state.returned);
            let TypeData::Object(target) = checker
                .store()
                .type_payload(state.binding_type)
                .unwrap()
                .data()
            else {
                unreachable!();
            };
            assert_eq!(target.structured.call_signature_count, 1);
            let target_signature = target.structured.signatures.as_ref().unwrap()[0];
            assert_ne!(target_signature, state.signature);
            assert_eq!(
                checker.get_return_type_of_signature(target_signature),
                Ok(state.returned)
            );
            for node in [initializer, local_name, condition] {
                assert_eq!(checker.get_type_at_location(node), Ok(number));
            }
            assert_eq!(
                checker.get_symbol_at_location(initializer),
                Ok(Some(state.parameters[0].0))
            );
            assert_eq!(
                checker.get_symbol_at_location(condition),
                Ok(Some(symbol(&checker, local)))
            );
            let returned_types = [early_return, later_return].map(|node| {
                let type_ = body_literal_type(
                    &mut checker,
                    node,
                    LiteralValue::Number(ts_jsnum::Number::new(1.0)),
                );
                let TypeData::Literal(literal) =
                    checker.store().type_payload(type_).unwrap().data()
                else {
                    unreachable!();
                };
                assert_eq!(literal.regular_type, state.returned);
                type_
            });
            let argument_type = body_literal_type(
                &mut checker,
                argument,
                LiteralValue::Number(ts_jsnum::Number::new(5.0)),
            );
            assert_eq!(checker.get_type_at_location(call), Ok(state.returned));
            let called = signature(&checker, call);
            assert_eq!(called, target_signature);
            if let Some(early) = early {
                assert_eq!(
                    early,
                    if first == Some(expression) {
                        state.callable
                    } else {
                        state.returned
                    }
                );
            }
            assert!(
                checker.diagnostics().is_empty(),
                "{:?}",
                checker.diagnostics()
            );
            check_body_replay(
                &checker,
                state,
                vec![number, returned_types[0], returned_types[1], argument_type],
                vec![target_signature, called],
                &mut cold,
            );
        }
    }
}

#[test]
#[allow(clippy::too_many_lines)] // Keep the private self-name and outer binding checks in the same scope.
fn named_function_expression_statement_list_keeps_its_self_scope() {
    use ts_checker::semantic::type_records::LiteralValue;

    let parsed = parse_source_file(concat!(
        "const self: string = 'outer';\n",
        "const echo = function self(value: number, early: boolean): number {\n",
        "  const local = value;\n",
        "  if (early) return local;\n",
        "  return self(local, true);\n",
        "};\n",
        "const result = echo(1, false);\n",
        "const outside = self;\n",
    ));
    let (_, _, expression) = variable(&parsed, "echo");
    let (_, _, call) = variable(&parsed, "result");
    let (outer, _, _) = variable(&parsed, "self");
    let (_, _, outside) = variable(&parsed, "outside");
    let (local, local_name, initializer) = variable(&parsed, "local");
    let statements = body_statements(&parsed, "echo");
    assert_eq!(statements.len(), 3);
    let (condition, early_return) = body_early_return(&parsed, statements[1]);
    let recursive_call = body_return_expression(&parsed, statements[2]);
    let NodeData::CallExpression(recursive) = &parsed.arena.get(recursive_call.node).unwrap().data
    else {
        unreachable!();
    };
    let self_read = NodeRef::new(parsed.arena.id(), FILE, recursive.expression);
    let recursive_argument = NodeRef::new(parsed.arena.id(), FILE, recursive.arguments.nodes[0]);
    let recursive_flag = NodeRef::new(parsed.arena.id(), FILE, recursive.arguments.nodes[1]);
    let NodeData::CallExpression(call_data) = &parsed.arena.get(call.node).unwrap().data else {
        unreachable!();
    };
    let argument = NodeRef::new(parsed.arena.id(), FILE, call_data.arguments.nodes[0]);
    let flag = NodeRef::new(parsed.arena.id(), FILE, call_data.arguments.nodes[1]);
    for first in [None, Some(expression), Some(call)] {
        let mut checker = context(&parsed, true);
        let early = first.map(|node| checker.get_type_at_location(node).unwrap());
        checker.check_source_file(FILE).unwrap();
        let mut cold = None;
        for replay in 0..3 {
            if replay != 0 {
                checker.recheck_source_file(FILE).unwrap();
            }
            let state = body_function_state(&mut checker, &parsed, "echo");
            let number = checker.store().intrinsic_bootstrap().unwrap().number_type;
            let string = checker.store().intrinsic_bootstrap().unwrap().string_type;
            let boolean = checker.store().intrinsic_bootstrap().unwrap().boolean_type;
            assert_eq!(state.returned, number);
            assert_eq!(state.binding_type, state.callable);
            assert_eq!(state.parameters.len(), 2);
            assert_eq!(state.parameters[0].1, number);
            assert_eq!(state.parameters[1].1, boolean);
            let outer_symbol = symbol(&checker, outer);
            let local_symbol = symbol(&checker, local);
            assert_ne!(state.owner, outer_symbol);
            assert_eq!(checker.get_type_at_location(self_read), Ok(state.callable));
            assert_eq!(
                checker.get_symbol_at_location(self_read),
                Ok(Some(state.owner))
            );
            assert_eq!(checker.get_type_at_location(outside), Ok(string));
            assert_eq!(
                checker.get_symbol_at_location(outside),
                Ok(Some(outer_symbol))
            );
            for node in [
                initializer,
                local_name,
                early_return,
                recursive_argument,
                recursive_call,
                call,
            ] {
                assert_eq!(checker.get_type_at_location(node), Ok(number));
            }
            assert_eq!(
                checker.get_symbol_at_location(initializer),
                Ok(Some(state.parameters[0].0))
            );
            for node in [early_return, recursive_argument] {
                assert_eq!(checker.get_symbol_at_location(node), Ok(Some(local_symbol)));
            }
            assert_eq!(checker.get_type_at_location(condition), Ok(boolean));
            let source = checker.source_file(FILE).unwrap().node_ref();
            let locals = checker.file(FILE).unwrap().1.locals(source).unwrap();
            assert_eq!(
                checker
                    .store()
                    .symbol_table(locals)
                    .unwrap()
                    .get_source("self"),
                Some(outer_symbol)
            );
            let recursive_signature = signature(&checker, recursive_call);
            let called = signature(&checker, call);
            assert_eq!(recursive_signature, state.signature);
            assert_eq!(called, state.signature);
            let argument_type = body_literal_type(
                &mut checker,
                argument,
                LiteralValue::Number(ts_jsnum::Number::new(1.0)),
            );
            let flag_type = body_literal_type(&mut checker, flag, LiteralValue::Boolean(false));
            let recursive_flag_type =
                body_literal_type(&mut checker, recursive_flag, LiteralValue::Boolean(true));
            if let Some(early) = early {
                assert_eq!(
                    early,
                    if first == Some(expression) {
                        state.callable
                    } else {
                        number
                    }
                );
            }
            assert!(
                checker.diagnostics().is_empty(),
                "{:?}",
                checker.diagnostics()
            );
            check_body_replay(
                &checker,
                state,
                vec![
                    number,
                    string,
                    argument_type,
                    flag_type,
                    recursive_flag_type,
                ],
                vec![recursive_signature, called],
                &mut cold,
            );
        }
    }
}

#[test]
#[allow(clippy::too_many_lines)] // Keep the import, parameter, provider, and source callable owners together.
fn exported_function_expression_statement_list_keeps_import_and_parameter_owners() {
    use ts_checker::semantic::type_records::LiteralValue;

    let parsed = parse_source_file(concat!(
        "import type * as path from './provider';\n",
        "export const normalize: typeof path.normalize = function(path: string) {\n",
        "  const local = path;\n",
        "  if (path) return local;\n",
        "  return path;\n",
        "};\n",
        "const result = normalize('ok');\n",
    ));
    let provider =
        parse_source_file("export function normalize(path: string): string { return path; }");
    let (_, _, expression) = variable(&parsed, "normalize");
    let (_, _, call) = variable(&parsed, "result");
    let (local, local_name, initializer) = variable(&parsed, "local");
    let statements = body_statements(&parsed, "normalize");
    assert_eq!(statements.len(), 3);
    let (condition, early_return) = body_early_return(&parsed, statements[1]);
    let later_return = body_return_expression(&parsed, statements[2]);
    let (import, import_name) = parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            let NodeData::NamespaceImport(import) = &record.data else {
                return None;
            };
            Some((
                NodeRef::new(parsed.arena.id(), FILE, node),
                NodeRef::new(parsed.arena.id(), FILE, import.name),
            ))
        })
        .unwrap();
    let provider_function = provider
        .arena
        .iter()
        .find_map(|(node, record)| {
            matches!(record.data, NodeData::FunctionDeclaration(_)).then_some(NodeRef::new(
                provider.arena.id(),
                PROVIDER,
                node,
            ))
        })
        .unwrap();
    let NodeData::FunctionDeclaration(provider_data) =
        &provider.arena.get(provider_function.node).unwrap().data
    else {
        unreachable!();
    };
    let provider_parameter = NodeRef::new(
        provider.arena.id(),
        PROVIDER,
        provider_data.parameters.nodes[0],
    );
    let NodeData::CallExpression(call_data) = &parsed.arena.get(call.node).unwrap().data else {
        unreachable!();
    };
    let argument = NodeRef::new(parsed.arena.id(), FILE, call_data.arguments.nodes[0]);
    for first in [None, Some(expression), Some(call)] {
        let mut checker = module_body_context(&parsed, &provider);
        let early = first.map(|node| checker.get_type_at_location(node).unwrap());
        checker.check_source_file(FILE).unwrap();
        checker.check_source_file(PROVIDER).unwrap();
        let mut cold = None;
        for replay in 0..3 {
            if replay != 0 {
                checker.recheck_source_file(FILE).unwrap();
                checker.recheck_source_file(PROVIDER).unwrap();
            }
            let state = body_function_state(&mut checker, &parsed, "normalize");
            let string = checker.store().intrinsic_bootstrap().unwrap().string_type;
            assert_eq!(state.parameters.len(), 1);
            assert_eq!(state.parameters[0].1, string);
            assert_eq!(state.returned, string);
            assert_ne!(state.callable, state.binding_type);
            let imported = symbol(&checker, import);
            let raw_provider_parameter = checker
                .file(PROVIDER)
                .unwrap()
                .1
                .symbol(provider_parameter)
                .unwrap();
            let provider_parameter_symbol = checker
                .store()
                .get_merged_symbol(raw_provider_parameter)
                .unwrap();
            assert_ne!(state.parameters[0].0, imported);
            assert_ne!(state.parameters[0].0, provider_parameter_symbol);
            assert_eq!(
                checker.get_symbol_at_location(import_name),
                Ok(Some(imported))
            );
            assert_eq!(
                checker.get_type_at_location(provider_function),
                Ok(state.binding_type)
            );
            let provider_signature = signature(&checker, provider_function);
            assert_ne!(provider_signature, state.signature);
            assert_eq!(
                checker.get_return_type_of_signature(provider_signature),
                Ok(string)
            );
            let record = checker.store().signature(provider_signature).unwrap();
            assert_eq!(record.declaration(), Some(provider_function));
            assert_eq!(record.parameters(), &[provider_parameter_symbol]);
            let local_symbol = symbol(&checker, local);
            for node in [
                initializer,
                local_name,
                condition,
                early_return,
                later_return,
                call,
            ] {
                assert_eq!(checker.get_type_at_location(node), Ok(string));
            }
            for node in [initializer, condition, later_return] {
                assert_eq!(
                    checker.get_symbol_at_location(node),
                    Ok(Some(state.parameters[0].0))
                );
            }
            assert_eq!(
                checker.get_symbol_at_location(early_return),
                Ok(Some(local_symbol))
            );
            let called = signature(&checker, call);
            assert_eq!(called, provider_signature);
            let argument_type = body_literal_type(
                &mut checker,
                argument,
                LiteralValue::String("ok".to_owned()),
            );
            if let Some(early) = early {
                assert_eq!(
                    early,
                    if first == Some(expression) {
                        state.callable
                    } else {
                        string
                    }
                );
            }
            assert!(
                checker.diagnostics().is_empty(),
                "{:?}",
                checker.diagnostics()
            );
            check_body_replay(
                &checker,
                state,
                vec![string, argument_type],
                vec![provider_signature, called],
                &mut cold,
            );
        }
    }
}

#[test]
#[allow(clippy::too_many_lines)] // Keep the empty parameter list, local return, and replay checks together.
fn zero_parameter_function_expression_statement_list_preserves_its_local_return() {
    use ts_checker::semantic::type_records::LiteralValue;

    let parsed = parse_source_file(concat!(
        "const get = function() {\n",
        "  const local = 1;\n",
        "  return local;\n",
        "};\n",
        "const result = get();\n",
    ));
    let (_, _, expression) = variable(&parsed, "get");
    let (_, result_name, call) = variable(&parsed, "result");
    let (local, local_name, initializer) = variable(&parsed, "local");
    let statements = body_statements(&parsed, "get");
    assert_eq!(statements.len(), 2);
    let returned = body_return_expression(&parsed, statements[1]);
    let NodeData::CallExpression(call_data) = &parsed.arena.get(call.node).unwrap().data else {
        unreachable!();
    };
    assert!(call_data.arguments.nodes.is_empty());
    let callee = NodeRef::new(parsed.arena.id(), FILE, call_data.expression);
    for first in [None, Some(expression), Some(call)] {
        let mut checker = context(&parsed, true);
        let early = first.map(|node| checker.get_type_at_location(node).unwrap());
        checker.check_source_file(FILE).unwrap();
        let mut cold = None;
        for replay in 0..3 {
            if replay != 0 {
                checker.recheck_source_file(FILE).unwrap();
            }
            let state = body_function_state(&mut checker, &parsed, "get");
            let number = checker.store().intrinsic_bootstrap().unwrap().number_type;
            assert!(state.parameters.is_empty());
            assert_eq!(state.binding_type, state.callable);
            assert_eq!(state.returned, number);
            let local_symbol = symbol(&checker, local);
            assert_ne!(local_symbol, state.owner);
            assert_ne!(local_symbol, state.binding);
            let local_record = checker.store().symbol(local_symbol).unwrap();
            assert_eq!(local_record.declarations(), Some(&[local][..]));
            assert_eq!(local_record.value_declaration(), Some(local));
            for node in [local_name, returned] {
                assert_eq!(checker.get_symbol_at_location(node), Ok(Some(local_symbol)));
            }
            let local_types = [initializer, local_name, returned].map(|node| {
                body_literal_type(
                    &mut checker,
                    node,
                    LiteralValue::Number(ts_jsnum::Number::new(1.0)),
                )
            });
            let regular_types = local_types.map(|type_| {
                let TypeData::Literal(literal) =
                    checker.store().type_payload(type_).unwrap().data()
                else {
                    unreachable!();
                };
                literal.regular_type
            });
            assert_eq!(regular_types[0], regular_types[1]);
            assert_eq!(regular_types[1], regular_types[2]);
            assert_ne!(local_types[2], number);
            assert_eq!(checker.get_type_at_location(callee), Ok(state.callable));
            assert_eq!(
                checker.get_symbol_at_location(callee),
                Ok(Some(state.binding))
            );
            assert_eq!(checker.get_type_at_location(call), Ok(number));
            assert_eq!(checker.get_type_at_location(result_name), Ok(number));
            let called = signature(&checker, call);
            assert_eq!(called, state.signature);
            if let Some(early) = early {
                assert_eq!(
                    early,
                    if first == Some(expression) {
                        state.callable
                    } else {
                        number
                    }
                );
            }
            assert!(
                checker.diagnostics().is_empty(),
                "{:?}",
                checker.diagnostics()
            );
            let mut types = vec![number];
            types.extend(local_types);
            types.extend(regular_types);
            check_body_replay(&checker, state, types, vec![called], &mut cold);
        }
    }
}

#[test]
#[allow(clippy::too_many_lines)] // Compare an uninitialized local with the same initialized body.
fn function_expression_statement_list_checks_local_assignment_before_read() {
    use ts_checker::semantic::type_records::LiteralValue;

    for (source, initialized) in [
        (
            concat!(
                "const read = function(value: string): string {\n",
                "  let local: string;\n",
                "  return local;\n",
                "};\n",
                "const result = read('ok');\n",
            ),
            false,
        ),
        (
            concat!(
                "const read = function(value: string): string {\n",
                "  let local: string = value;\n",
                "  return local;\n",
                "};\n",
                "const result = read('ok');\n",
            ),
            true,
        ),
    ] {
        let parsed = parse_source_file(source);
        let (_, _, expression) = variable(&parsed, "read");
        let (_, result_name, call) = variable(&parsed, "result");
        let statements = body_statements(&parsed, "read");
        assert_eq!(statements.len(), 2);
        let NodeData::VariableStatement(statement) =
            &parsed.arena.get(statements[0].node).unwrap().data
        else {
            panic!("expected the local variable statement");
        };
        let NodeData::VariableDeclarationList(declarations) =
            &parsed.arena.get(statement.declaration_list).unwrap().data
        else {
            unreachable!();
        };
        assert_eq!(declarations.declarations.nodes.len(), 1);
        let local = NodeRef::new(parsed.arena.id(), FILE, declarations.declarations.nodes[0]);
        let NodeData::VariableDeclaration(declaration) =
            &parsed.arena.get(local.node).unwrap().data
        else {
            unreachable!();
        };
        let local_name = NodeRef::new(parsed.arena.id(), FILE, declaration.name);
        let annotation = NodeRef::new(parsed.arena.id(), FILE, declaration.type_.unwrap());
        let initializer = declaration
            .initializer
            .map(|node| NodeRef::new(parsed.arena.id(), FILE, node));
        assert_eq!(initializer.is_some(), initialized);
        let returned = body_return_expression(&parsed, statements[1]);
        let NodeData::CallExpression(call_data) = &parsed.arena.get(call.node).unwrap().data else {
            unreachable!();
        };
        assert_eq!(call_data.arguments.nodes.len(), 1);
        let argument = NodeRef::new(parsed.arena.id(), FILE, call_data.arguments.nodes[0]);
        for first in [None, Some(expression), Some(call)] {
            let mut checker = context(&parsed, true);
            let early = first.map(|node| checker.get_type_at_location(node).unwrap());
            checker.check_source_file(FILE).unwrap();
            let mut cold = None;
            for replay in 0..3 {
                if replay != 0 {
                    checker.recheck_source_file(FILE).unwrap();
                }
                let state = body_function_state(&mut checker, &parsed, "read");
                let string = checker.store().intrinsic_bootstrap().unwrap().string_type;
                assert_eq!(state.binding_type, state.callable);
                assert_eq!(state.returned, string);
                assert_eq!(state.parameters.len(), 1);
                assert_eq!(state.parameters[0].1, string);
                let local_symbol = symbol(&checker, local);
                assert_ne!(local_symbol, state.owner);
                assert_ne!(local_symbol, state.binding);
                assert_ne!(local_symbol, state.parameters[0].0);
                let local_record = checker.store().symbol(local_symbol).unwrap();
                assert_eq!(local_record.declarations(), Some(&[local][..]));
                assert_eq!(local_record.value_declaration(), Some(local));
                for node in [annotation, local_name, returned, call, result_name] {
                    assert_eq!(checker.get_type_at_location(node), Ok(string));
                }
                for node in [local_name, returned] {
                    assert_eq!(checker.get_symbol_at_location(node), Ok(Some(local_symbol)));
                }
                if let Some(initializer) = initializer {
                    assert_eq!(checker.get_type_at_location(initializer), Ok(string));
                    assert_eq!(
                        checker.get_symbol_at_location(initializer),
                        Ok(Some(state.parameters[0].0)),
                    );
                }
                let argument_type = body_literal_type(
                    &mut checker,
                    argument,
                    LiteralValue::String("ok".to_owned()),
                );
                let called = signature(&checker, call);
                assert_eq!(called, state.signature);
                if let Some(early) = early {
                    assert_eq!(
                        early,
                        if first == Some(expression) {
                            state.callable
                        } else {
                            string
                        }
                    );
                }
                let diagnostics = checker.diagnostics().as_slice();
                if initialized {
                    assert!(diagnostics.is_empty(), "{diagnostics:?}");
                } else {
                    assert_eq!(diagnostics.len(), 1, "{diagnostics:?}");
                    let diagnostic = &diagnostics[0];
                    assert_eq!(diagnostic.node, Some(returned));
                    assert_eq!(diagnostic.range_override, None);
                    assert_eq!(diagnostic.diagnostic.code(), 2454);
                    assert_eq!(
                        diagnostic.diagnostic.render().unwrap(),
                        "Variable 'local' is used before being assigned.",
                    );
                    assert!(diagnostic.related_information.is_empty());
                }
                check_body_replay(
                    &checker,
                    state,
                    vec![string, argument_type],
                    vec![called],
                    &mut cold,
                );
            }
        }
    }
}
