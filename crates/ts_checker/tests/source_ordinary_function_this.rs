use ts_ast::{FileId, NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId, SymbolFlags,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerDiagnosticRange, CanonicalCheckerDiagnostics,
    CanonicalCheckerOptions, IntrinsicBootstrapOptions, SignatureId, SignatureLinks,
    SourceCheckError, SourceFileLinks, SymbolNodeLinks, TypeData, TypeId, TypeNodeLinks,
    UnsupportedSourceSyntax, ValueSymbolLinks,
};
use ts_parser::{ParseResult, parse_source_file};

const FILE: FileId = FileId::new(202_820);

fn context(parsed: &ParseResult) -> CanonicalCheckerContext<'_> {
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            FILE,
            CanonicalSourceFileFacts::new(
                EscapedName::source("\"/project/ordinary-function-this.ts\""),
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
            no_implicit_this: true,
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

enum FirstQuery {
    Source,
    Type(NodeRef),
    ThisSymbol {
        expression: NodeRef,
        parameter: NodeRef,
    },
}

fn check_in_order(checker: &mut CanonicalCheckerContext<'_>, first: FirstQuery) {
    match first {
        FirstQuery::Source => {}
        FirstQuery::Type(node) => {
            checker.get_type_at_location(node).unwrap();
        }
        FirstQuery::ThisSymbol {
            expression,
            parameter,
        } => {
            let expected = symbol(checker, parameter);
            assert_eq!(
                checker.get_symbol_at_location(expression),
                Ok(Some(expected))
            );
        }
    }
    checker.check_source_file(FILE).unwrap();
}

#[derive(Clone, Copy)]
struct ParameterNodes {
    declaration: NodeRef,
    name: NodeRef,
    annotation: NodeRef,
}

fn parameter_nodes(parsed: &ParseResult, declaration: NodeRef) -> ParameterNodes {
    let NodeData::ParameterDeclaration(parameter) =
        &parsed.arena.get(declaration.node).unwrap().data
    else {
        panic!("expected a real source parameter");
    };
    ParameterNodes {
        declaration,
        name: NodeRef::new(parsed.arena.id(), FILE, parameter.name),
        annotation: NodeRef::new(parsed.arena.id(), FILE, parameter.type_.unwrap()),
    }
}

struct FunctionNodes {
    declaration: NodeRef,
    this_parameter: ParameterNodes,
    parameters: Vec<ParameterNodes>,
    annotation: Option<NodeRef>,
    return_statement: NodeRef,
    body: NodeRef,
}

fn function_nodes(parsed: &ParseResult) -> FunctionNodes {
    let declarations = parsed
        .arena
        .iter()
        .filter_map(|(node, record)| {
            matches!(
                record.kind,
                SyntaxKind::FunctionDeclaration | SyntaxKind::FunctionExpression
            )
            .then_some(NodeRef::new(parsed.arena.id(), FILE, node))
        })
        .collect::<Vec<_>>();
    let [declaration] = declarations.as_slice() else {
        panic!("each control has one ordinary source function");
    };
    let declaration = *declaration;
    let (parameters, body, annotation) = match &parsed.arena.get(declaration.node).unwrap().data {
        NodeData::FunctionDeclaration(function) => (
            &function.parameters.nodes,
            function.body.unwrap(),
            function.type_,
        ),
        NodeData::FunctionExpression(function) => {
            (&function.parameters.nodes, function.body, function.type_)
        }
        _ => unreachable!(),
    };
    let reference = |node| NodeRef::new(parsed.arena.id(), FILE, node);
    let NodeData::Block(block) = &parsed.arena.get(body).unwrap().data else {
        panic!("ordinary functions must retain their block body");
    };
    let [statement] = block.statements.nodes.as_slice() else {
        panic!("each control has one return statement");
    };
    let NodeData::ReturnStatement(returned) = &parsed.arena.get(*statement).unwrap().data else {
        unreachable!();
    };
    FunctionNodes {
        declaration,
        this_parameter: parameter_nodes(parsed, reference(parameters[0])),
        parameters: parameters[1..]
            .iter()
            .map(|&node| parameter_nodes(parsed, reference(node)))
            .collect(),
        annotation: annotation.map(reference),
        return_statement: reference(*statement),
        body: reference(returned.expression.unwrap()),
    }
}

fn property_parts(parsed: &ParseResult, node: NodeRef) -> (NodeRef, NodeRef) {
    let NodeData::PropertyAccessExpression(property) = &parsed.arena.get(node.node).unwrap().data
    else {
        panic!("expected an actual property access");
    };
    (
        NodeRef::new(parsed.arena.id(), FILE, property.expression),
        NodeRef::new(parsed.arena.id(), FILE, property.name),
    )
}

fn call_parts(parsed: &ParseResult, node: NodeRef) -> (NodeRef, Vec<NodeRef>) {
    let NodeData::CallExpression(call) = &parsed.arena.get(node.node).unwrap().data else {
        panic!("expected a call expression");
    };
    (
        NodeRef::new(parsed.arena.id(), FILE, call.expression),
        call.arguments
            .nodes
            .iter()
            .map(|&node| NodeRef::new(parsed.arena.id(), FILE, node))
            .collect(),
    )
}

fn parameter_state(
    checker: &mut CanonicalCheckerContext<'_>,
    parameter: ParameterNodes,
) -> (SemanticSymbolId, TypeId) {
    let owner = symbol(checker, parameter.declaration);
    let type_ = checker.get_type_at_location(parameter.annotation).unwrap();
    let record = checker.store().symbol(owner).unwrap();
    assert_eq!(record.flags(), SymbolFlags::FUNCTION_SCOPED_VARIABLE);
    assert_eq!(record.declarations(), Some(&[parameter.declaration][..]));
    assert_eq!(record.value_declaration(), Some(parameter.declaration));
    assert_eq!(
        checker.get_symbol_at_location(parameter.name),
        Ok(Some(owner))
    );
    assert_eq!(checker.get_type_at_location(parameter.name), Ok(type_));
    assert_eq!(
        checker.get_type_at_location(parameter.declaration),
        Ok(type_)
    );
    assert_eq!(
        checker
            .store()
            .value_symbol_links(owner)
            .unwrap()
            .resolved_type,
        Some(type_)
    );
    (owner, type_)
}

#[derive(Debug, Eq, PartialEq)]
struct FunctionState {
    owner: SemanticSymbolId,
    callable: TypeId,
    signature: SignatureId,
    this_symbol: SemanticSymbolId,
    this_type: TypeId,
    parameters: Vec<(SemanticSymbolId, TypeId)>,
    returned: TypeId,
    body_type: TypeId,
}

fn function_state(
    checker: &mut CanonicalCheckerContext<'_>,
    nodes: &FunctionNodes,
) -> FunctionState {
    let owner = symbol(checker, nodes.declaration);
    let callable = checker.get_type_at_location(nodes.declaration).unwrap();
    let signature = signature(checker, nodes.declaration);
    let record = checker.store().symbol(owner).unwrap();
    assert_eq!(record.flags(), SymbolFlags::FUNCTION);
    assert_eq!(record.declarations(), Some(&[nodes.declaration][..]));
    assert_eq!(record.value_declaration(), Some(nodes.declaration));
    assert_eq!(
        checker
            .store()
            .value_symbol_links(owner)
            .unwrap()
            .resolved_type,
        Some(callable)
    );
    let record = checker.store().type_payload(callable).unwrap();
    assert_eq!(record.symbol(), Some(owner));
    let TypeData::Object(object) = record.data() else {
        panic!("the function must retain its callable object");
    };
    assert_eq!(
        object.structured.signatures.as_deref(),
        Some(&[signature][..])
    );
    assert_eq!(object.structured.call_signature_count, 1);
    let (this_symbol, this_type) = parameter_state(checker, nodes.this_parameter);
    let parameters = nodes
        .parameters
        .iter()
        .map(|&parameter| parameter_state(checker, parameter))
        .collect::<Vec<_>>();
    let returned = checker.get_return_type_of_signature(signature).unwrap();
    let record = checker.store().signature(signature).unwrap();
    assert_eq!(record.declaration(), Some(nodes.declaration));
    assert_eq!(record.this_parameter(), Some(this_symbol));
    assert!(!record.parameters().contains(&this_symbol));
    assert_eq!(
        record.parameters(),
        parameters
            .iter()
            .map(|&(symbol, _)| symbol)
            .collect::<Vec<_>>()
    );
    assert_eq!(
        record.min_argument_count(),
        i32::try_from(parameters.len()).unwrap()
    );
    assert_eq!(record.resolved_return_type(), Some(returned));
    assert!(record.type_parameters().is_empty());
    assert!(record.target().is_none());
    assert!(record.mapper().is_none());
    if let Some(annotation) = nodes.annotation {
        assert_eq!(checker.get_type_at_location(annotation), Ok(returned));
    }
    FunctionState {
        owner,
        callable,
        signature,
        this_symbol,
        this_type,
        parameters,
        returned,
        body_type: checker.get_type_at_location(nodes.body).unwrap(),
    }
}

fn assert_receiver_property(
    checker: &mut CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    nodes: &FunctionNodes,
    state: &FunctionState,
    expected: TypeId,
) {
    let (this, name) = property_parts(parsed, nodes.body);
    assert_eq!(
        parsed.arena.get(this.node).unwrap().kind,
        SyntaxKind::ThisKeyword
    );
    assert_eq!(
        checker.file(FILE).unwrap().1.this_container(this),
        Some(nodes.declaration)
    );
    assert_eq!(checker.get_type_at_location(this), Ok(state.this_type));
    assert_eq!(
        checker.get_symbol_at_location(this),
        Ok(Some(state.this_symbol))
    );
    let NodeData::TypeLiteral(literal) = &parsed
        .arena
        .get(nodes.this_parameter.annotation.node)
        .unwrap()
        .data
    else {
        panic!("the receiver annotation must remain a real type literal");
    };
    let [property] = literal.members.nodes.as_slice() else {
        panic!("the receiver has one written property");
    };
    let property = NodeRef::new(parsed.arena.id(), FILE, *property);
    let property_symbol = symbol(checker, property);
    assert_eq!(
        parsed.arena.get(property.node).unwrap().kind,
        SyntaxKind::PropertySignature
    );
    for node in [nodes.body, name] {
        assert_eq!(
            checker.get_symbol_at_location(node),
            Ok(Some(property_symbol))
        );
        assert_eq!(checker.get_type_at_location(node), Ok(expected));
    }
    assert_eq!(state.body_type, expected);
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
    nodes: &FunctionNodes,
    calls: &[NodeRef],
) {
    let state = function_state(checker, nodes);
    for &call in calls {
        assert_eq!(checker.get_type_at_location(call), Ok(state.returned));
        assert_eq!(signature(checker, call), state.signature);
    }
    let warm = snapshot(checker, parsed);
    for recheck in [false, true] {
        if recheck {
            checker.recheck_source_file(FILE).unwrap();
        } else {
            checker.check_source_file(FILE).unwrap();
        }
        assert_eq!(function_state(checker, nodes), state);
        for &call in calls {
            assert_eq!(checker.get_type_at_location(call), Ok(state.returned));
            assert_eq!(signature(checker, call), state.signature);
        }
        assert_eq!(snapshot(checker, parsed), warm);
        assert!(checker.store().type_resolution_is_empty());
    }
}

#[test]
fn ordinary_this_parameters_keep_source_receiver_identity_and_value_arity() {
    for declaration in [
        "function read(this: { value: number }, input: string): number { return this.value; }",
        "const read = function(this: { value: number }, input: string): number { return this.value; };",
    ] {
        let parsed = parse_source_file(&format!(
            "{declaration}\nconst receiver = {{ value: 1, run: read }};\nconst result = receiver.run('x');"
        ));
        let nodes = function_nodes(&parsed);
        let call = variable(&parsed, "result").2;
        let (callee, _) = call_parts(&parsed, call);
        let (receiver, _) = property_parts(&parsed, callee);
        let (this, _) = property_parts(&parsed, nodes.body);
        for first in [
            FirstQuery::Source,
            FirstQuery::Type(this),
            FirstQuery::ThisSymbol {
                expression: this,
                parameter: nodes.this_parameter.declaration,
            },
            FirstQuery::Type(call),
        ] {
            let mut checker = context(&parsed);
            check_in_order(&mut checker, first);
            assert!(
                checker.diagnostics().is_empty(),
                "{:?}",
                checker.diagnostics()
            );
            let state = function_state(&mut checker, &nodes);
            let number = checker.store().intrinsic_bootstrap().unwrap().number_type;
            let string = checker.store().intrinsic_bootstrap().unwrap().string_type;
            assert_eq!(state.parameters.len(), 1);
            assert_eq!(state.parameters[0].1, string);
            assert_eq!(state.returned, number);
            assert_receiver_property(&mut checker, &parsed, &nodes, &state, number);
            assert_eq!(
                checker.type_to_string(state.callable).unwrap(),
                "(this: { value: number; }, input: string) => number"
            );
            let receiver_type = checker.get_type_at_location(receiver).unwrap();
            assert_ne!(receiver_type, state.this_type);
            assert_eq!(checker.get_type_at_location(callee), Ok(state.callable));
            assert_eq!(checker.get_type_at_location(call), Ok(number));
            assert_eq!(signature(&checker, call), state.signature);
            if parsed.arena.get(nodes.declaration.node).unwrap().kind
                == SyntaxKind::FunctionExpression
            {
                let (binding, name, _) = variable(&parsed, "read");
                assert_ne!(symbol(&checker, binding), state.owner);
                assert_eq!(checker.get_type_at_location(name), Ok(state.callable));
            }
            assert_replay(&mut checker, &parsed, &nodes, &[call]);
        }
    }
}

#[test]
#[allow(clippy::too_many_lines)] // Receiver, value argument, and arity errors have different source sites.
fn ordinary_this_calls_keep_receiver_diagnostics_and_return_identity() {
    let parsed = parse_source_file(concat!(
        "function read(this: { value: number }, input: string): number { return this.value; }\n",
        "const receiver = { value: 1, run: read };\n",
        "const wrong = { value: 'bad', run: read };\n",
        "const missing = read('x');\n",
        "const mismatch = wrong.run('x');\n",
        "const badArgument = receiver.run(1);\n",
        "const tooFew = receiver.run();\n",
        "const tooMany = receiver.run('x',1);\n",
    ));
    let nodes = function_nodes(&parsed);
    let calls = ["missing", "mismatch", "badArgument", "tooFew", "tooMany"]
        .map(|name| variable(&parsed, name).2);
    let (bad_callee, _) = call_parts(&parsed, calls[1]);
    let (wrong_receiver, _) = property_parts(&parsed, bad_callee);
    let (_, bad_arguments) = call_parts(&parsed, calls[2]);
    let (few_callee, _) = call_parts(&parsed, calls[3]);
    let (_, few_name) = property_parts(&parsed, few_callee);
    let (_, extra_arguments) = call_parts(&parsed, calls[4]);
    for first in [
        FirstQuery::Source,
        FirstQuery::Type(nodes.declaration),
        FirstQuery::Type(calls[1]),
    ] {
        let mut checker = context(&parsed);
        check_in_order(&mut checker, first);
        let state = function_state(&mut checker, &nodes);
        let number = checker.store().intrinsic_bootstrap().unwrap().number_type;
        assert_eq!(state.returned, number);
        assert_receiver_property(&mut checker, &parsed, &nodes, &state, number);
        let diagnostics = checker.diagnostics().as_slice();
        assert_eq!(diagnostics.len(), 5, "{diagnostics:?}");
        let expected = [
            (
                calls[0],
                2684,
                "The 'this' context of type 'void' is not assignable to method's 'this' of type '{ value: number; }'.",
            ),
            (
                wrong_receiver,
                2684,
                concat!(
                    "The 'this' context of type '{ value: string; run: (this: { value: number; }, input: string) => number; }' is not assignable to method's 'this' of type '{ value: number; }'.\n",
                    "  Types of property 'value' are incompatible.\n",
                    "    Type 'string' is not assignable to type 'number'.",
                ),
            ),
            (
                bad_arguments[0],
                2345,
                "Argument of type 'number' is not assignable to parameter of type 'string'.",
            ),
            (few_name, 2554, "Expected 1 arguments, but got 0."),
            (calls[4], 2554, "Expected 1 arguments, but got 2."),
        ];
        for (diagnostic, (node, code, message)) in diagnostics.iter().zip(expected) {
            assert_eq!(diagnostic.node, Some(node));
            assert_eq!(diagnostic.diagnostic.code(), code);
            assert_eq!(diagnostic.diagnostic.render().unwrap(), message);
        }
        for diagnostic in &diagnostics[..4] {
            assert_eq!(diagnostic.range_override, None);
        }
        for index in [0, 1, 2, 4] {
            assert!(diagnostics[index].related_information.is_empty());
        }
        let [related] = diagnostics[3].related_information.as_slice() else {
            panic!("the missing value argument must name input, not this");
        };
        assert_eq!(related.node, Some(nodes.parameters[0].declaration));
        assert_eq!(related.diagnostic.code(), 6210);
        assert_eq!(
            related.diagnostic.render().unwrap(),
            "An argument for 'input' was not provided."
        );
        assert_eq!(
            diagnostics[4].range_override,
            Some(CanonicalCheckerDiagnosticRange::new(
                calls[4],
                parsed.arena.get(extra_arguments[1].node).unwrap().range,
            ))
        );
        assert_replay(&mut checker, &parsed, &nodes, &calls);
    }
}

#[test]
fn explicit_void_this_keeps_its_symbol_but_does_not_consume_an_argument() {
    let parsed = parse_source_file(concat!(
        "function read(this: void): void { return this; }\n",
        "const direct = read();\n",
        "const receiver = { run: read };\n",
        "const member = receiver.run();\n",
        "const extra = read(1);\n",
    ));
    let nodes = function_nodes(&parsed);
    let calls = ["direct", "member", "extra"].map(|name| variable(&parsed, name).2);
    let (_, extra_arguments) = call_parts(&parsed, calls[2]);
    for first in [
        FirstQuery::Source,
        FirstQuery::Type(nodes.body),
        FirstQuery::Type(calls[1]),
    ] {
        let mut checker = context(&parsed);
        check_in_order(&mut checker, first);
        let state = function_state(&mut checker, &nodes);
        let void = checker.store().intrinsic_bootstrap().unwrap().void_type;
        assert_eq!(state.this_type, void);
        assert_eq!(state.returned, void);
        assert_eq!(state.body_type, void);
        assert!(state.parameters.is_empty());
        assert_eq!(
            checker.get_symbol_at_location(nodes.body),
            Ok(Some(state.this_symbol))
        );
        assert_eq!(
            checker.type_to_string(state.callable).unwrap(),
            "(this: void) => void"
        );
        let [diagnostic] = checker.diagnostics().as_slice() else {
            panic!("only the extra value argument must be rejected");
        };
        assert_eq!(diagnostic.node, Some(calls[2]));
        assert_eq!(diagnostic.diagnostic.code(), 2554);
        assert_eq!(
            diagnostic.diagnostic.render().unwrap(),
            "Expected 0 arguments, but got 1."
        );
        assert!(diagnostic.related_information.is_empty());
        assert_eq!(
            diagnostic.range_override,
            Some(CanonicalCheckerDiagnosticRange::new(
                calls[2],
                parsed.arena.get(extra_arguments[0].node).unwrap().range,
            ))
        );
        assert_replay(&mut checker, &parsed, &nodes, &calls);
    }
}

#[test]
fn ordinary_this_property_errors_keep_the_body_type_and_return_annotation_separate() {
    let parsed = parse_source_file(concat!(
        "const read = function(this: { value: string }): number { return this.value; };\n",
        "const receiver = { value: 'ready', run: read };\n",
        "const result = receiver.run();\n",
    ));
    let nodes = function_nodes(&parsed);
    let call = variable(&parsed, "result").2;
    for first in [
        FirstQuery::Source,
        FirstQuery::Type(nodes.body),
        FirstQuery::Type(call),
    ] {
        let mut checker = context(&parsed);
        check_in_order(&mut checker, first);
        let state = function_state(&mut checker, &nodes);
        let number = checker.store().intrinsic_bootstrap().unwrap().number_type;
        let string = checker.store().intrinsic_bootstrap().unwrap().string_type;
        assert_eq!(state.returned, number);
        assert!(state.parameters.is_empty());
        assert_receiver_property(&mut checker, &parsed, &nodes, &state, string);
        let [diagnostic] = checker.diagnostics().as_slice() else {
            panic!("the real this.value type must fail the number return annotation");
        };
        assert_eq!(diagnostic.node, Some(nodes.return_statement));
        assert_eq!(diagnostic.range_override, None);
        assert_eq!(diagnostic.diagnostic.code(), 2322);
        assert_eq!(
            diagnostic.diagnostic.render().unwrap(),
            "Type 'string' is not assignable to type 'number'."
        );
        assert!(diagnostic.related_information.is_empty());
        assert_replay(&mut checker, &parsed, &nodes, &[call]);
    }
}

#[test]
fn arrows_do_not_gain_an_owned_this_parameter() {
    let parsed =
        parse_source_file("const read = (this: { value: number }, input: string): number => 1;");
    let arrow = variable(&parsed, "read").2;
    let NodeData::ArrowFunction(function) = &parsed.arena.get(arrow.node).unwrap().data else {
        panic!("this control must remain an arrow");
    };
    let this_parameter = NodeRef::new(parsed.arena.id(), FILE, function.parameters.nodes[0]);
    let mut checker = context(&parsed);
    let this_symbol = symbol(&checker, this_parameter);
    let owner = symbol(&checker, arrow);
    let mut warm = None;
    for recheck in [false, true] {
        let result = if recheck {
            checker.recheck_source_file(FILE)
        } else {
            checker.check_source_file(FILE)
        };
        assert_eq!(
            result,
            Err(SourceCheckError::Unsupported(
                UnsupportedSourceSyntax::Arrow(this_parameter)
            ))
        );
        assert!(checker.diagnostics().is_empty());
        assert!(checker.store().signature_links(arrow).is_none());
        assert!(checker.store().type_node_links(arrow).is_none());
        assert!(checker.store().value_symbol_links(owner).is_none());
        assert!(checker.store().value_symbol_links(this_symbol).is_none());
        let state = snapshot(&checker, &parsed);
        if let Some(warm) = &warm {
            assert_eq!(&state, warm);
        } else {
            warm = Some(state);
        }
        assert!(checker.store().type_resolution_is_empty());
    }
}

#[test]
fn ordinary_this_missing_receiver_properties_keep_exact_sites_and_replay() {
    for (fields, code, message) in [
        (
            "value: number",
            2741,
            "Property 'value' is missing in type '{ run: (this: { value: number; }, input: string) => number; }' but required in type '{ value: number; }'.",
        ),
        (
            "value: number; label: string",
            2739,
            "Type '{ run: (this: { value: number; label: string; }, input: string) => number; }' is missing the following properties from type '{ value: number; label: string; }': value, label",
        ),
    ] {
        let parsed = parse_source_file(&format!(
            "function read(this: {{ {fields} }}, input: string): number {{ return this.value; }}\n\
             const wrong = {{ run: read }};\nconst result = wrong.run('x');"
        ));
        let nodes = function_nodes(&parsed);
        let call = variable(&parsed, "result").2;
        let (callee, _) = call_parts(&parsed, call);
        let (receiver, _) = property_parts(&parsed, callee);
        let (body_this, body_name) = property_parts(&parsed, nodes.body);
        let NodeData::TypeLiteral(literal) = &parsed
            .arena
            .get(nodes.this_parameter.annotation.node)
            .unwrap()
            .data
        else {
            panic!("the required receiver properties must keep their source declarations");
        };
        let property = NodeRef::new(parsed.arena.id(), FILE, literal.members.nodes[0]);
        let NodeData::PropertySignature(property_data) =
            &parsed.arena.get(property.node).unwrap().data
        else {
            panic!("value must remain a PropertySignature");
        };
        let property_name = NodeRef::new(parsed.arena.id(), FILE, property_data.name);
        for first in [
            FirstQuery::Source,
            FirstQuery::ThisSymbol {
                expression: body_this,
                parameter: nodes.this_parameter.declaration,
            },
            FirstQuery::Type(call),
        ] {
            let mut checker = context(&parsed);
            check_in_order(&mut checker, first);
            let state = function_state(&mut checker, &nodes);
            let number = checker.store().intrinsic_bootstrap().unwrap().number_type;
            let property_symbol = symbol(&checker, property);
            assert_eq!(state.returned, number);
            assert_eq!(state.body_type, number);
            assert_eq!(checker.get_type_at_location(body_this), Ok(state.this_type));
            assert_eq!(
                checker.get_symbol_at_location(body_this),
                Ok(Some(state.this_symbol))
            );
            assert_eq!(
                checker.get_symbol_at_location(body_name),
                Ok(Some(property_symbol))
            );
            assert_eq!(checker.get_type_at_location(callee), Ok(state.callable));
            assert_ne!(
                checker.get_type_at_location(receiver).unwrap(),
                state.this_type
            );
            assert_eq!(checker.get_type_at_location(call), Ok(number));
            assert_eq!(signature(&checker, call), state.signature);
            let [diagnostic] = checker.diagnostics().as_slice() else {
                panic!("the missing receiver properties must produce one exact diagnostic");
            };
            assert_eq!(diagnostic.node, Some(receiver));
            assert_eq!(diagnostic.range_override, None);
            assert_eq!(diagnostic.diagnostic.code(), code);
            assert_eq!(diagnostic.diagnostic.render().unwrap(), message);
            if code == 2741 {
                let [related] = diagnostic.related_information.as_slice() else {
                    panic!("one missing property must retain its declaration note");
                };
                assert_eq!(related.node, Some(property_name));
                assert_eq!(related.diagnostic.code(), 2728);
                assert_eq!(
                    related.diagnostic.render().unwrap(),
                    "'value' is declared here."
                );
            } else {
                assert!(diagnostic.related_information.is_empty());
            }
            assert_replay(&mut checker, &parsed, &nodes, &[call]);
        }
    }
}
