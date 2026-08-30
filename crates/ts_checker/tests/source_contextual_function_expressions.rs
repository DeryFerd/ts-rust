use ts_ast::{FileId, NodeData, NodeRef};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId, SymbolFlags,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerDiagnostics, CanonicalCheckerOptions,
    IntrinsicBootstrapOptions, SignatureId, SignatureLinks, SourceFileLinks, SymbolNodeLinks,
    TypeData, TypeId, TypeNodeLinks, ValueSymbolLinks,
};
use ts_parser::{ParseResult, parse_source_file};

const FILE: FileId = FileId::new(202_730);

fn context(parsed: &ParseResult) -> CanonicalCheckerContext<'_> {
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            FILE,
            CanonicalSourceFileFacts::new(
                EscapedName::source("\"/project/contextual-functions.ts\""),
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

struct Variable {
    declaration: NodeRef,
    name: NodeRef,
    annotation: Option<NodeRef>,
    initializer: NodeRef,
}

fn variable(parsed: &ParseResult, expected: &str) -> Variable {
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
            (name.text == expected).then(|| Variable {
                declaration: NodeRef::new(parsed.arena.id(), FILE, node),
                name: NodeRef::new(parsed.arena.id(), FILE, variable.name),
                annotation: variable
                    .type_
                    .map(|node| NodeRef::new(parsed.arena.id(), FILE, node)),
                initializer: NodeRef::new(parsed.arena.id(), FILE, variable.initializer.unwrap()),
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

fn callable_signature(checker: &CanonicalCheckerContext<'_>, type_: TypeId) -> SignatureId {
    let TypeData::Object(object) = checker.store().type_payload(type_).unwrap().data() else {
        panic!("a function must retain its callable object");
    };
    let [signature] = object.structured.signatures.as_deref().unwrap() else {
        panic!("each control has one call signature");
    };
    assert_eq!(object.structured.call_signature_count, 1);
    *signature
}

#[derive(Debug, Eq, PartialEq)]
struct ParameterState {
    declaration: NodeRef,
    name: NodeRef,
    symbol: SemanticSymbolId,
    type_: TypeId,
    annotated: bool,
}

#[derive(Debug, Eq, PartialEq)]
struct FunctionState {
    owner: SemanticSymbolId,
    binding: SemanticSymbolId,
    callable: TypeId,
    target: TypeId,
    signature: SignatureId,
    target_signature: SignatureId,
    parameters: Vec<ParameterState>,
    returned: TypeId,
    target_return: TypeId,
    returns: Vec<(NodeRef, Option<(NodeRef, TypeId)>)>,
}

#[allow(clippy::too_many_lines)] // Keep source ownership and the separate annotation signature together.
fn function_state(
    checker: &mut CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    name: &str,
) -> FunctionState {
    let binding_node = variable(parsed, name);
    let declaration = binding_node.initializer;
    let NodeData::FunctionExpression(function) = &parsed.arena.get(declaration.node).unwrap().data
    else {
        panic!("the initializer must remain a FunctionExpression");
    };
    let reference = |node| NodeRef::new(parsed.arena.id(), FILE, node);
    let owner = symbol(checker, declaration);
    let binding = symbol(checker, binding_node.declaration);
    assert_ne!(owner, binding);
    let record = checker.store().symbol(owner).unwrap();
    assert_eq!(record.flags(), SymbolFlags::FUNCTION);
    assert_eq!(record.declarations(), Some(&[declaration][..]));
    assert_eq!(record.value_declaration(), Some(declaration));

    let callable = checker.get_type_at_location(declaration).unwrap();
    let target = checker
        .get_type_at_location(binding_node.annotation.unwrap())
        .unwrap();
    assert_ne!(callable, target);
    assert_eq!(checker.get_type_at_location(binding_node.name), Ok(target));
    assert_eq!(
        checker.get_symbol_at_location(binding_node.name),
        Ok(Some(binding))
    );
    for (symbol, type_) in [(owner, callable), (binding, target)] {
        assert_eq!(
            checker
                .store()
                .value_symbol_links(symbol)
                .unwrap()
                .resolved_type,
            Some(type_),
        );
    }
    assert_eq!(
        checker.store().type_payload(callable).unwrap().symbol(),
        Some(owner)
    );
    if let Some(name) = function.name {
        assert_eq!(checker.get_type_at_location(reference(name)), Ok(callable));
        assert_eq!(
            checker.get_symbol_at_location(reference(name)),
            Ok(Some(owner))
        );
    }
    let signature = signature(checker, declaration);
    assert_eq!(callable_signature(checker, callable), signature);
    let target_signature = callable_signature(checker, target);
    assert_ne!(signature, target_signature);

    let parameters = function
        .parameters
        .nodes
        .iter()
        .map(|&node| {
            let NodeData::ParameterDeclaration(parameter) = &parsed.arena.get(node).unwrap().data
            else {
                unreachable!();
            };
            let declaration = reference(node);
            let name = reference(parameter.name);
            let symbol = symbol(checker, declaration);
            let type_ = checker.get_type_at_location(name).unwrap();
            assert_eq!(checker.get_symbol_at_location(name), Ok(Some(symbol)));
            assert_eq!(
                checker
                    .store()
                    .value_symbol_links(symbol)
                    .unwrap()
                    .resolved_type,
                Some(type_),
            );
            assert_eq!(
                checker.store().symbol(symbol).unwrap().declarations(),
                Some(&[declaration][..])
            );
            if let Some(annotation) = parameter.type_ {
                assert_eq!(
                    checker.get_type_at_location(reference(annotation)),
                    Ok(type_)
                );
            }
            ParameterState {
                declaration,
                name,
                symbol,
                type_,
                annotated: parameter.type_.is_some(),
            }
        })
        .collect::<Vec<_>>();
    let returned = checker.get_return_type_of_signature(signature).unwrap();
    let target_return = checker
        .get_return_type_of_signature(target_signature)
        .unwrap();
    let record = checker.store().signature(signature).unwrap();
    assert_eq!(record.declaration(), Some(declaration));
    assert_eq!(
        record.parameters(),
        parameters
            .iter()
            .map(|parameter| parameter.symbol)
            .collect::<Vec<_>>()
    );
    assert_eq!(record.resolved_return_type(), Some(returned));
    assert!(record.type_parameters().is_empty());
    assert!(record.target().is_none());
    assert!(record.mapper().is_none());
    if let Some(annotation) = function.type_ {
        assert_eq!(
            checker.get_type_at_location(reference(annotation)),
            Ok(returned)
        );
    }
    let NodeData::Block(block) = &parsed.arena.get(function.body).unwrap().data else {
        unreachable!();
    };
    let returns = block
        .statements
        .nodes
        .iter()
        .map(|&node| {
            let NodeData::ReturnStatement(statement) = &parsed.arena.get(node).unwrap().data else {
                panic!("each control has an empty body or one return statement");
            };
            let expression = statement.expression.map(|node| {
                let node = reference(node);
                (node, checker.get_type_at_location(node).unwrap())
            });
            (reference(node), expression)
        })
        .collect();
    FunctionState {
        owner,
        binding,
        callable,
        target,
        signature,
        target_signature,
        parameters,
        returned,
        target_return,
        returns,
    }
}

#[derive(Debug, Eq, PartialEq)]
struct Snapshot {
    counts: [usize; 6],
    types: Vec<Option<TypeNodeLinks>>,
    symbols: Vec<Option<SymbolNodeLinks>>,
    signatures: Vec<Option<SignatureLinks>>,
    values: Vec<Option<ValueSymbolLinks>>,
    source: Option<SourceFileLinks>,
    diagnostics: CanonicalCheckerDiagnostics,
}

fn snapshot(checker: &CanonicalCheckerContext<'_>, parsed: &ParseResult) -> Snapshot {
    let store = checker.store();
    let nodes = parsed
        .arena
        .iter()
        .map(|(node, _)| NodeRef::new(parsed.arena.id(), FILE, node))
        .collect::<Vec<_>>();
    Snapshot {
        counts: [
            store.type_len(),
            store.symbol_len(),
            store.signature_len(),
            store.mapper_len(),
            store.type_alias_len(),
            store.symbol_store().symbol_table_len(),
        ],
        types: nodes
            .iter()
            .map(|node| store.type_node_links(*node).cloned())
            .collect(),
        symbols: nodes
            .iter()
            .map(|node| store.symbol_node_links(*node).cloned())
            .collect(),
        signatures: nodes
            .iter()
            .map(|node| store.signature_links(*node).cloned())
            .collect(),
        values: nodes
            .iter()
            .filter_map(|node| checker.file(FILE).unwrap().1.symbol(*node))
            .map(|symbol| {
                store
                    .value_symbol_links(store.get_merged_symbol(symbol).unwrap())
                    .cloned()
            })
            .collect(),
        source: store
            .source_file_links(checker.source_file(FILE).unwrap())
            .cloned(),
        diagnostics: checker.diagnostics().clone(),
    }
}

fn assert_replay(
    checker: &mut CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    names: &[&str],
    queries: &[(NodeRef, TypeId)],
) {
    let states = names
        .iter()
        .map(|name| function_state(checker, parsed, name))
        .collect::<Vec<_>>();
    for &(node, type_) in queries {
        assert_eq!(checker.get_type_at_location(node), Ok(type_));
    }
    let warm = snapshot(checker, parsed);
    for recheck in [false, true] {
        if recheck {
            checker.recheck_source_file(FILE).unwrap();
        } else {
            checker.check_source_file(FILE).unwrap();
        }
        for (name, expected) in names.iter().zip(&states) {
            assert_eq!(&function_state(checker, parsed, name), expected);
        }
        for &(node, type_) in queries {
            assert_eq!(checker.get_type_at_location(node), Ok(type_));
        }
        assert_eq!(snapshot(checker, parsed), warm);
        assert!(checker.store().type_resolution_is_empty());
    }
}

fn assert_diagnostics(checker: &CanonicalCheckerContext<'_>, expected: &[(NodeRef, u32, &str)]) {
    let diagnostics = checker.diagnostics().as_slice();
    assert_eq!(diagnostics.len(), expected.len(), "{diagnostics:?}");
    for (diagnostic, &(node, code, message)) in diagnostics.iter().zip(expected) {
        assert_eq!(diagnostic.node, Some(node));
        assert_eq!(diagnostic.range_override, None);
        assert_eq!(diagnostic.diagnostic.code(), code);
        assert_eq!(diagnostic.diagnostic.render().unwrap(), message);
        assert!(diagnostic.related_information.is_empty());
    }
}

#[test]
fn contextual_function_parameters_and_literal_returns_keep_distinct_source_owners() {
    for (source, number_parameter, annotated_parameter, returned_display) in [
        (
            "const echo: (value: number) => 1 = function(value: number) { return 1; }; const result = echo(1);",
            true,
            true,
            "1",
        ),
        (
            "const echo: (value: number) => 1 = function(value) { return 1; }; const result = echo(1);",
            true,
            false,
            "1",
        ),
        (
            "const echo: (value: string) => string = function(value) { return value; }; const result = echo('ready');",
            false,
            false,
            "string",
        ),
    ] {
        let parsed = parse_source_file(source);
        let expression = variable(&parsed, "echo").initializer;
        let call = variable(&parsed, "result").initializer;
        for first in [None, Some(expression), Some(call)] {
            let mut checker = context(&parsed);
            let early = first.map(|node| checker.get_type_at_location(node).unwrap());
            checker.check_source_file(FILE).unwrap();
            assert!(
                checker.diagnostics().is_empty(),
                "{:?}",
                checker.diagnostics()
            );
            let state = function_state(&mut checker, &parsed, "echo");
            let expected_parameter = if number_parameter {
                checker.store().intrinsic_bootstrap().unwrap().number_type
            } else {
                checker.store().intrinsic_bootstrap().unwrap().string_type
            };
            let [parameter] = state.parameters.as_slice() else {
                panic!("echo must retain its one source parameter");
            };
            assert_eq!(parameter.type_, expected_parameter);
            assert_eq!(parameter.annotated, annotated_parameter);
            let contextual_parameter = checker
                .store()
                .signature(state.target_signature)
                .unwrap()
                .parameters()[0];
            assert_ne!(parameter.symbol, contextual_parameter);
            assert_eq!(
                checker
                    .store()
                    .value_symbol_links(contextual_parameter)
                    .unwrap()
                    .resolved_type,
                Some(expected_parameter),
            );
            assert_eq!(state.returned, state.target_return);
            assert_eq!(
                checker.type_to_string(state.returned).unwrap(),
                returned_display
            );
            let (body, body_type) = state.returns[0].1.unwrap();
            if number_parameter {
                let TypeData::Literal(literal) =
                    checker.store().type_payload(body_type).unwrap().data()
                else {
                    panic!("the numeric return expression must keep its literal type");
                };
                assert_eq!(literal.regular_type, state.returned);
                assert_ne!(state.returned, expected_parameter);
            } else {
                assert_eq!(body_type, expected_parameter);
                assert_eq!(
                    checker.get_symbol_at_location(body),
                    Ok(Some(parameter.symbol))
                );
            }
            assert_eq!(checker.get_type_at_location(call), Ok(state.target_return));
            assert_eq!(signature(&checker, call), state.target_signature);
            if let Some(early) = early {
                assert_eq!(
                    early,
                    if first == Some(expression) {
                        state.callable
                    } else {
                        state.target_return
                    }
                );
            }
            assert_replay(
                &mut checker,
                &parsed,
                &["echo"],
                &[(call, state.target_return)],
            );
        }
    }
}

#[test]
fn contextual_function_inference_keeps_undefined_and_void_returns_separate() {
    for (source, undefined_return, union_target, bare_return) in [
        (
            "const echo: () => undefined = function() {}; const result = echo();",
            true,
            false,
            false,
        ),
        (
            "const echo: () => undefined = function() { return; }; const result = echo();",
            true,
            false,
            true,
        ),
        (
            "const echo: () => number | undefined = function() {}; const result = echo();",
            true,
            true,
            false,
        ),
        (
            "const echo: () => void = function() { return 1; }; const result = echo();",
            false,
            false,
            false,
        ),
    ] {
        let parsed = parse_source_file(source);
        let expression = variable(&parsed, "echo").initializer;
        let call = variable(&parsed, "result").initializer;
        for first in [None, Some(expression), Some(call)] {
            let mut checker = context(&parsed);
            if let Some(node) = first {
                checker.get_type_at_location(node).unwrap();
            }
            checker.check_source_file(FILE).unwrap();
            assert!(
                checker.diagnostics().is_empty(),
                "{:?}",
                checker.diagnostics()
            );
            let state = function_state(&mut checker, &parsed, "echo");
            let bootstrap = checker.store().intrinsic_bootstrap().unwrap();
            assert!(state.parameters.is_empty());
            assert_eq!(
                state.returned,
                if undefined_return {
                    bootstrap.undefined_type
                } else {
                    bootstrap.number_type
                }
            );
            if union_target {
                let TypeData::Union(union) = checker
                    .store()
                    .type_payload(state.target_return)
                    .unwrap()
                    .data()
                else {
                    panic!("the written number | undefined return must remain a union");
                };
                assert_eq!(union.union.types.len(), 2);
                assert!(union.union.types.contains(&bootstrap.undefined_type));
                assert!(union.union.types.contains(&bootstrap.number_type));
            } else {
                assert_eq!(
                    state.target_return,
                    if undefined_return {
                        bootstrap.undefined_type
                    } else {
                        bootstrap.void_type
                    }
                );
            }
            if undefined_return {
                assert_eq!(state.returns.len(), usize::from(bare_return));
                assert!(
                    state
                        .returns
                        .iter()
                        .all(|(_, expression)| expression.is_none())
                );
            } else {
                let (_, body_type) = state.returns[0].1.unwrap();
                assert_ne!(body_type, state.returned);
                assert_ne!(state.returned, state.target_return);
                assert_eq!(checker.type_to_string(body_type).unwrap(), "1");
            }
            assert_eq!(checker.get_type_at_location(call), Ok(state.target_return));
            assert_eq!(signature(&checker, call), state.target_signature);
            assert_replay(
                &mut checker,
                &parsed,
                &["echo"],
                &[(call, state.target_return)],
            );
        }
    }
}

#[test]
#[allow(clippy::too_many_lines)] // Assignment, parameter, body, and call errors retain separate source sites.
fn contextual_function_assignment_and_body_errors_keep_exact_types_and_sites() {
    let parsed = parse_source_file(concat!(
        "const literal: () => 1 = function() { return 2; };\n",
        "const parameter: (value: number) => number = function(value: string): number { return 1; };\n",
        "const body: (value: string) => number = function(value): number { return value; };\n",
        "const literalResult = literal();\n",
        "const bodyResult = body(1);\n",
    ));
    let literal = variable(&parsed, "literal");
    let parameter = variable(&parsed, "parameter");
    let body = variable(&parsed, "body");
    let literal_call = variable(&parsed, "literalResult").initializer;
    let body_call = variable(&parsed, "bodyResult").initializer;
    let NodeData::CallExpression(call) = &parsed.arena.get(body_call.node).unwrap().data else {
        unreachable!();
    };
    let argument = NodeRef::new(parsed.arena.id(), FILE, call.arguments.nodes[0]);
    for first in [None, Some(literal.initializer), Some(body_call)] {
        let mut checker = context(&parsed);
        if let Some(node) = first {
            checker.get_type_at_location(node).unwrap();
        }
        checker.check_source_file(FILE).unwrap();
        let literal_state = function_state(&mut checker, &parsed, "literal");
        let parameter_state = function_state(&mut checker, &parsed, "parameter");
        let body_state = function_state(&mut checker, &parsed, "body");
        assert_diagnostics(
            &checker,
            &[
                (
                    literal.name,
                    2322,
                    concat!(
                        "Type '() => 2' is not assignable to type '() => 1'.\n",
                        "  Type '2' is not assignable to type '1'.",
                    ),
                ),
                (
                    parameter.name,
                    2322,
                    concat!(
                        "Type '(value: string) => number' is not assignable to type '(value: number) => number'.\n",
                        "  Types of parameters 'value' and 'value' are incompatible.\n",
                        "    Type 'number' is not assignable to type 'string'.",
                    ),
                ),
                (
                    body_state.returns[0].0,
                    2322,
                    "Type 'string' is not assignable to type 'number'.",
                ),
                (
                    argument,
                    2345,
                    "Argument of type 'number' is not assignable to parameter of type 'string'.",
                ),
            ],
        );
        let number = checker.store().intrinsic_bootstrap().unwrap().number_type;
        let string = checker.store().intrinsic_bootstrap().unwrap().string_type;
        assert_eq!(checker.type_to_string(literal_state.returned).unwrap(), "2");
        assert_eq!(
            checker.type_to_string(literal_state.target_return).unwrap(),
            "1"
        );
        assert_ne!(literal_state.returned, literal_state.target_return);
        let (_, literal_body) = literal_state.returns[0].1.unwrap();
        let TypeData::Literal(literal_type) =
            checker.store().type_payload(literal_body).unwrap().data()
        else {
            panic!("the mismatched numeric return must retain its actual literal");
        };
        assert_eq!(literal_type.regular_type, literal_state.returned);
        assert_eq!(parameter_state.parameters[0].type_, string);
        assert!(parameter_state.parameters[0].annotated);
        assert_eq!(parameter_state.returned, number);
        let target_parameter = checker
            .store()
            .signature(parameter_state.target_signature)
            .unwrap()
            .parameters()[0];
        assert_eq!(
            checker
                .store()
                .value_symbol_links(target_parameter)
                .unwrap()
                .resolved_type,
            Some(number)
        );
        assert_eq!(body_state.parameters[0].type_, string);
        assert!(!body_state.parameters[0].annotated);
        assert_eq!(body_state.returned, number);
        let (body_read, body_type) = body_state.returns[0].1.unwrap();
        assert_eq!(body_type, string);
        assert_eq!(
            checker.get_symbol_at_location(body_read),
            Ok(Some(body_state.parameters[0].symbol))
        );
        assert_eq!(
            checker.get_type_at_location(literal_call),
            Ok(literal_state.target_return)
        );
        assert_eq!(checker.get_type_at_location(body_call), Ok(number));
        assert_eq!(
            signature(&checker, literal_call),
            literal_state.target_signature
        );
        assert_eq!(signature(&checker, body_call), body_state.target_signature);
        assert_replay(
            &mut checker,
            &parsed,
            &["literal", "parameter", "body"],
            &[
                (literal_call, literal_state.target_return),
                (body_call, number),
                (body_read, string),
            ],
        );
        assert_eq!(
            checker.get_type_at_location(body.initializer),
            Ok(body_state.callable)
        );
    }
}

#[test]
fn named_contextual_function_self_reference_keeps_its_local_owner() {
    let parsed = parse_source_file(concat!(
        "const self: string = 'outer';\n",
        "const recurse: (value: number) => number = function self(value): number { return self(value); };\n",
        "const result = recurse(1);\n",
        "const outside = self;\n",
    ));
    let expression = variable(&parsed, "recurse").initializer;
    let call = variable(&parsed, "result").initializer;
    let outer = variable(&parsed, "self").declaration;
    let outside = variable(&parsed, "outside").initializer;
    for first in [None, Some(expression), Some(call)] {
        let mut checker = context(&parsed);
        if let Some(node) = first {
            checker.get_type_at_location(node).unwrap();
        }
        checker.check_source_file(FILE).unwrap();
        assert!(
            checker.diagnostics().is_empty(),
            "{:?}",
            checker.diagnostics()
        );
        let state = function_state(&mut checker, &parsed, "recurse");
        let number = checker.store().intrinsic_bootstrap().unwrap().number_type;
        let string = checker.store().intrinsic_bootstrap().unwrap().string_type;
        let outer = symbol(&checker, outer);
        assert_ne!(state.owner, outer);
        assert_eq!(state.parameters[0].type_, number);
        assert!(!state.parameters[0].annotated);
        assert_eq!(state.returned, number);
        assert_eq!(state.target_return, number);
        let (recursive_call, body_type) = state.returns[0].1.unwrap();
        assert_eq!(body_type, number);
        let NodeData::CallExpression(recursive) =
            &parsed.arena.get(recursive_call.node).unwrap().data
        else {
            unreachable!();
        };
        let self_read = NodeRef::new(parsed.arena.id(), FILE, recursive.expression);
        let parameter_read = NodeRef::new(parsed.arena.id(), FILE, recursive.arguments.nodes[0]);
        assert_eq!(
            checker.get_symbol_at_location(self_read),
            Ok(Some(state.owner))
        );
        assert_eq!(checker.get_type_at_location(self_read), Ok(state.callable));
        assert_eq!(
            checker.get_symbol_at_location(parameter_read),
            Ok(Some(state.parameters[0].symbol))
        );
        assert_eq!(checker.get_type_at_location(parameter_read), Ok(number));
        assert_eq!(signature(&checker, recursive_call), state.signature);
        assert_eq!(signature(&checker, call), state.target_signature);
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
        assert_replay(
            &mut checker,
            &parsed,
            &["recurse"],
            &[
                (call, number),
                (recursive_call, number),
                (self_read, state.callable),
                (parameter_read, number),
                (outside, string),
            ],
        );
    }
}

#[test]
fn contextual_function_mutable_capture_keeps_the_declared_union() {
    let parsed = parse_source_file(concat!(
        "let captured: string | undefined = 'ready';\n",
        "const read: () => string | undefined = function() { return captured; };\n",
        "captured = undefined;\n",
        "const current = captured;\n",
        "const result = read();\n",
    ));
    let captured = variable(&parsed, "captured");
    let expression = variable(&parsed, "read").initializer;
    let current = variable(&parsed, "current").initializer;
    let call = variable(&parsed, "result").initializer;
    for first in [None, Some(expression), Some(call)] {
        let mut checker = context(&parsed);
        if let Some(node) = first {
            checker.get_type_at_location(node).unwrap();
        }
        checker.check_source_file(FILE).unwrap();
        assert!(
            checker.diagnostics().is_empty(),
            "{:?}",
            checker.diagnostics()
        );
        let state = function_state(&mut checker, &parsed, "read");
        let captured_symbol = symbol(&checker, captured.declaration);
        let declared = checker
            .get_type_at_location(captured.annotation.unwrap())
            .unwrap();
        let string = checker.store().intrinsic_bootstrap().unwrap().string_type;
        let undefined = checker
            .store()
            .intrinsic_bootstrap()
            .unwrap()
            .undefined_type;
        let TypeData::Union(union) = checker.store().type_payload(declared).unwrap().data() else {
            panic!("the captured binding must keep its written string | undefined type");
        };
        assert_eq!(union.union.types.len(), 2);
        assert!(union.union.types.contains(&string));
        assert!(union.union.types.contains(&undefined));
        assert_eq!(state.returned, declared);
        assert_eq!(state.target_return, declared);
        let (body_read, body_type) = state.returns[0].1.unwrap();
        assert_eq!(body_type, declared);
        assert_eq!(
            checker.get_symbol_at_location(body_read),
            Ok(Some(captured_symbol))
        );
        assert_eq!(
            checker.get_symbol_at_location(current),
            Ok(Some(captured_symbol))
        );
        assert_eq!(checker.get_type_at_location(current), Ok(undefined));
        assert_eq!(checker.get_type_at_location(call), Ok(declared));
        assert_eq!(signature(&checker, call), state.target_signature);
        assert_replay(
            &mut checker,
            &parsed,
            &["read"],
            &[
                (body_read, declared),
                (current, undefined),
                (call, declared),
            ],
        );
    }
}
