use ts_ast::{FileId, NodeData, NodeId, NodeRef, SyntaxKind};
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

const FILE: FileId = FileId::new(202_902);

fn context(parsed: &ParseResult) -> CanonicalCheckerContext<'_> {
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            FILE,
            CanonicalSourceFileFacts::new(
                EscapedName::source("\"/project/callable-variable-callbacks.ts\""),
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
        panic!("expected a source callable object");
    };
    let [signature] = object.structured.signatures.as_deref().unwrap() else {
        panic!("each callback target has one signature");
    };
    assert_eq!(object.structured.call_signature_count, 1);
    *signature
}

fn declaration(parsed: &ParseResult, expected: &str) -> NodeRef {
    parsed
        .arena
        .iter()
        .find_map(|(id, record)| {
            let name = match &record.data {
                NodeData::VariableDeclaration(declaration) => declaration.name,
                NodeData::TypeAliasDeclaration(declaration) => declaration.name,
                _ => return None,
            };
            let NodeData::Identifier(name) = &parsed.arena.get(name)?.data else {
                return None;
            };
            (name.text == expected).then_some(node(parsed, id))
        })
        .unwrap_or_else(|| panic!("missing declaration {expected}"))
}

fn alias_rhs(parsed: &ParseResult, expected: &str) -> NodeRef {
    let declaration = declaration(parsed, expected);
    let NodeData::TypeAliasDeclaration(alias) = &parsed.arena.get(declaration.node).unwrap().data
    else {
        unreachable!();
    };
    node(parsed, alias.type_)
}

#[derive(Clone, Copy)]
enum Expected {
    Number,
    String,
    Void,
    Alias(&'static str),
}

fn expected_type(
    checker: &mut CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    expected: Expected,
) -> TypeId {
    match expected {
        Expected::Number => checker.store().intrinsic_bootstrap().unwrap().number_type,
        Expected::String => checker.store().intrinsic_bootstrap().unwrap().string_type,
        Expected::Void => checker.store().intrinsic_bootstrap().unwrap().void_type,
        Expected::Alias(name) => checker
            .get_type_at_location(alias_rhs(parsed, name))
            .unwrap(),
    }
}

struct Callback {
    arrow: NodeRef,
    parameter: NodeRef,
    name: NodeRef,
    body: NodeRef,
    call: NodeRef,
    argument: usize,
}

fn callbacks(parsed: &ParseResult) -> Vec<Callback> {
    let mut callbacks = parsed
        .arena
        .iter()
        .filter_map(|(id, record)| {
            let NodeData::ArrowFunction(arrow) = &record.data else {
                return None;
            };
            let [parameter_id] = arrow.parameters.nodes.as_slice() else {
                return None;
            };
            let NodeData::ParameterDeclaration(parameter) = &parsed.arena.get(*parameter_id)?.data
            else {
                return None;
            };
            if parameter.type_.is_some() {
                return None;
            }
            let call_id = record.parent.unwrap();
            let NodeData::CallExpression(call) = &parsed.arena.get(call_id)?.data else {
                panic!("each unannotated callback is an actual call argument");
            };
            assert!(arrow.type_parameters.is_none());
            assert!(parameter.initializer.is_none());
            assert!(parameter.question_token.is_none());
            assert!(parameter.dot_dot_dot_token.is_none());
            Some(Callback {
                arrow: node(parsed, id),
                parameter: node(parsed, *parameter_id),
                name: node(parsed, parameter.name),
                body: node(parsed, arrow.body),
                call: node(parsed, call_id),
                argument: call
                    .arguments
                    .nodes
                    .iter()
                    .position(|&node| node == id)
                    .unwrap(),
            })
        })
        .collect::<Vec<_>>();
    callbacks.sort_by_key(|callback| parsed.arena.get(callback.arrow.node).unwrap().range.start);
    callbacks
}

fn inside(parsed: &ParseResult, mut child: NodeId, parent: NodeId) -> bool {
    loop {
        if child == parent {
            return true;
        }
        let Some(next) = parsed.arena.get(child).unwrap().parent else {
            return false;
        };
        child = next;
    }
}

#[derive(Debug, Eq, PartialEq)]
struct CallbackState {
    arrow: NodeRef,
    owner: SemanticSymbolId,
    callable: TypeId,
    signature: SignatureId,
    parameter: SemanticSymbolId,
    parameter_type: TypeId,
    returned: TypeId,
    call: NodeRef,
    call_signature: SignatureId,
    target: TypeId,
    target_signature: SignatureId,
    target_parameter: SemanticSymbolId,
    uses: Vec<NodeRef>,
}

fn callback_state(
    checker: &mut CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    callback: &Callback,
    parameter_type: TypeId,
    returned: TypeId,
) -> CallbackState {
    let owner = symbol(checker, callback.arrow);
    let parameter = symbol(checker, callback.parameter);
    let callable = checker.get_type_at_location(callback.arrow).unwrap();
    let source_signature = signature(checker, callback.arrow);
    let call_signature = signature(checker, callback.call);
    let target_binding = checker
        .store()
        .signature(call_signature)
        .unwrap()
        .parameters()[callback.argument];
    let target = checker
        .store()
        .value_symbol_links(target_binding)
        .unwrap()
        .resolved_type
        .unwrap();
    let target_signature = callable_signature(checker, target);
    let target_parameters = checker
        .store()
        .signature(target_signature)
        .unwrap()
        .parameters();
    assert_eq!(target_parameters.len(), 1);
    let target_parameter = target_parameters[0];
    assert_ne!(parameter, target_parameter);
    assert_ne!(source_signature, target_signature);
    assert_ne!(callable, target);
    assert_eq!(callable_signature(checker, callable), source_signature);
    assert_eq!(
        checker.store().type_payload(callable).unwrap().symbol(),
        Some(owner)
    );
    assert_eq!(
        checker.store().symbol(owner).unwrap().flags(),
        SymbolFlags::FUNCTION
    );
    assert_eq!(
        checker.store().symbol(owner).unwrap().declarations(),
        Some(&[callback.arrow][..])
    );
    assert_eq!(
        checker.store().symbol(owner).unwrap().value_declaration(),
        Some(callback.arrow)
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
        parsed.arena.get(callback.parameter.node).unwrap().parent,
        Some(callback.arrow.node)
    );
    assert_eq!(
        checker.store().symbol(parameter).unwrap().declarations(),
        Some(&[callback.parameter][..])
    );
    assert_eq!(
        checker.get_symbol_at_location(callback.name),
        Ok(Some(parameter))
    );
    assert_eq!(
        checker.get_type_at_location(callback.name),
        Ok(parameter_type)
    );
    for symbol in [parameter, target_parameter] {
        assert_eq!(
            checker
                .store()
                .value_symbol_links(symbol)
                .unwrap()
                .resolved_type,
            Some(parameter_type)
        );
    }
    assert_eq!(
        checker.get_return_type_of_signature(source_signature),
        Ok(returned)
    );
    assert_eq!(
        checker.get_return_type_of_signature(target_signature),
        Ok(returned)
    );
    let record = checker.store().signature(source_signature).unwrap();
    assert_eq!(record.declaration(), Some(callback.arrow));
    assert_eq!(record.parameters(), &[parameter]);
    assert_eq!(record.min_argument_count(), 1);
    assert_eq!(record.resolved_return_type(), Some(returned));
    assert!(record.type_parameters().is_empty());
    assert_eq!(record.target(), None);
    assert_eq!(record.mapper(), None);
    assert_eq!(
        checker.get_type_at_location(callback.call),
        Ok(checker.store().intrinsic_bootstrap().unwrap().void_type)
    );

    let NodeData::Identifier(name) = &parsed.arena.get(callback.name.node).unwrap().data else {
        unreachable!();
    };
    let uses = parsed
        .arena
        .iter()
        .filter_map(|(id, record)| {
            let NodeData::Identifier(identifier) = &record.data else {
                return None;
            };
            (identifier.text == name.text && inside(parsed, id, callback.body.node))
                .then_some(node(parsed, id))
        })
        .collect::<Vec<_>>();
    assert!(
        !uses.is_empty(),
        "the body must use its actual contextual parameter"
    );
    for &usage in &uses {
        assert_eq!(checker.get_symbol_at_location(usage), Ok(Some(parameter)));
        assert_eq!(checker.get_type_at_location(usage), Ok(parameter_type));
    }
    CallbackState {
        arrow: callback.arrow,
        owner,
        callable,
        signature: source_signature,
        parameter,
        parameter_type,
        returned,
        call: callback.call,
        call_signature,
        target,
        target_signature,
        target_parameter,
        uses,
    }
}

#[derive(Debug, Eq, PartialEq)]
struct Snapshot {
    counts: [usize; 7],
    types: Vec<Option<TypeNodeLinks>>,
    symbols: Vec<Option<SymbolNodeLinks>>,
    signatures: Vec<Option<SignatureLinks>>,
    values: Vec<Option<ValueSymbolLinks>>,
    aliases: Vec<Option<TypeId>>,
    source: Option<SourceFileLinks>,
    diagnostics: CanonicalCheckerDiagnostics,
}

fn snapshot(checker: &CanonicalCheckerContext<'_>, parsed: &ParseResult) -> Snapshot {
    let store = checker.store();
    let nodes = parsed
        .arena
        .iter()
        .map(|(id, _)| node(parsed, id))
        .collect::<Vec<_>>();
    let symbols = nodes
        .iter()
        .filter_map(|&node| checker.file(FILE).unwrap().1.symbol(node))
        .map(|symbol| store.get_merged_symbol(symbol).unwrap())
        .collect::<Vec<_>>();
    Snapshot {
        counts: [
            store.type_len(),
            store.symbol_len(),
            store.signature_len(),
            store.mapper_len(),
            store.index_info_len(),
            store.type_alias_len(),
            store.symbol_store().symbol_table_len(),
        ],
        types: nodes
            .iter()
            .map(|&node| store.type_node_links(node).cloned())
            .collect(),
        symbols: nodes
            .iter()
            .map(|&node| store.symbol_node_links(node).cloned())
            .collect(),
        signatures: nodes
            .iter()
            .map(|&node| store.signature_links(node).cloned())
            .collect(),
        values: symbols
            .iter()
            .map(|&symbol| store.value_symbol_links(symbol).cloned())
            .collect(),
        aliases: symbols
            .iter()
            .map(|&symbol| {
                store
                    .type_alias_links(symbol)
                    .and_then(|links| links.declared_type)
            })
            .collect(),
        source: store
            .source_file_links(checker.source_file(FILE).unwrap())
            .cloned(),
        diagnostics: checker.diagnostics().clone(),
    }
}

fn check_program(
    source: &str,
    expected: &[(Expected, Expected)],
    cold_callback: usize,
    bad_argument: bool,
    check_owners: impl Fn(&mut CanonicalCheckerContext<'_>, &ParseResult, &[CallbackState]),
) {
    let parsed = parse_source_file(source);
    let callbacks = callbacks(&parsed);
    assert_eq!(callbacks.len(), expected.len());
    for query_first in [false, true] {
        let mut checker = context(&parsed);
        let root = checker.source_file(FILE).unwrap();
        assert!(
            !checker
                .store()
                .source_file_links(root)
                .is_some_and(|links| links.type_checked)
        );
        let first_type = if query_first {
            Some(
                checker
                    .get_type_at_location(callbacks[cold_callback].name)
                    .unwrap(),
            )
        } else {
            checker.check_source_file(FILE).unwrap();
            None
        };
        if bad_argument {
            let NodeData::CallExpression(call) =
                &parsed.arena.get(callbacks[1].call.node).unwrap().data
            else {
                unreachable!();
            };
            let argument = node(&parsed, call.arguments.nodes[0]);
            let record = parsed.arena.get(argument.node).unwrap();
            assert_eq!(record.kind, SyntaxKind::NumericLiteral);
            assert_eq!(
                &source[record.range.start.get() as usize..record.range.end.get() as usize],
                "123"
            );
            let [diagnostic] = checker.diagnostics().as_slice() else {
                panic!("only the bad nested label must produce a diagnostic");
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
                checker.diagnostics().is_empty(),
                "{:?}",
                checker.diagnostics()
            );
        }
        let initial_diagnostics = checker.diagnostics().clone();
        let observe = |checker: &mut CanonicalCheckerContext<'_>| {
            callbacks
                .iter()
                .zip(expected)
                .map(|(callback, &(parameter, returned))| {
                    let parameter = expected_type(checker, &parsed, parameter);
                    let returned = expected_type(checker, &parsed, returned);
                    callback_state(checker, &parsed, callback, parameter, returned)
                })
                .collect::<Vec<_>>()
        };
        let states = observe(&mut checker);
        if let Some(first_type) = first_type {
            assert_eq!(first_type, states[cold_callback].parameter_type);
        }
        check_owners(&mut checker, &parsed, &states);
        assert!(
            checker
                .store()
                .source_file_links(root)
                .unwrap()
                .type_checked
        );
        assert_eq!(checker.diagnostics(), &initial_diagnostics);
        let before = snapshot(&checker, &parsed);
        for _ in 0..2 {
            checker.recheck_source_file(FILE).unwrap();
            assert_eq!(observe(&mut checker), states);
            check_owners(&mut checker, &parsed, &states);
            assert_eq!(snapshot(&checker, &parsed), before);
            assert!(checker.store().type_resolution_is_empty());
        }
    }
}

fn variable_callee(
    checker: &mut CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    name: &str,
    calls: &[&CallbackState],
) {
    let declaration = declaration(parsed, name);
    let NodeData::VariableDeclaration(variable) = &parsed.arena.get(declaration.node).unwrap().data
    else {
        unreachable!();
    };
    let initializer = node(parsed, variable.initializer.unwrap());
    let binding = symbol(checker, declaration);
    assert_eq!(
        checker.store().symbol(binding).unwrap().flags(),
        SymbolFlags::BLOCK_SCOPED_VARIABLE
    );
    let type_ = checker.get_type_at_location(initializer).unwrap();
    let selected = signature(checker, initializer);
    assert_eq!(callable_signature(checker, type_), selected);
    assert_eq!(
        checker.store().signature(selected).unwrap().declaration(),
        Some(initializer)
    );
    for state in calls {
        let NodeData::CallExpression(call) = &parsed.arena.get(state.call.node).unwrap().data
        else {
            unreachable!();
        };
        let callee = node(parsed, call.expression);
        assert_eq!(checker.get_symbol_at_location(callee), Ok(Some(binding)));
        assert_eq!(checker.get_type_at_location(callee), Ok(type_));
        assert_eq!(state.call_signature, selected);
    }
}

fn check_pathe_owners(
    checker: &mut CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    states: &[CallbackState],
) {
    variable_callee(checker, parsed, "describe", &[&states[0]]);
    let register_rhs = alias_rhs(parsed, "Register");
    let register = checker.get_type_at_location(register_rhs).unwrap();
    assert_eq!(states[0].parameter_type, register);
    let NodeData::IntersectionTypeNode(intersection) =
        &parsed.arena.get(register_rhs.node).unwrap().data
    else {
        unreachable!();
    };
    let [callable_node, properties_node] = intersection.types.nodes.as_slice() else {
        panic!("keep both original Register constituents");
    };
    let callable = checker
        .get_type_at_location(node(parsed, *callable_node))
        .unwrap();
    let properties = checker
        .get_type_at_location(node(parsed, *properties_node))
        .unwrap();
    let TypeData::Intersection(intersection) =
        checker.store().type_payload(register).unwrap().data()
    else {
        panic!("Register must retain its intersection identity");
    };
    assert_eq!(intersection.intersection.types.len(), 2);
    assert!(intersection.intersection.types.contains(&callable));
    assert!(intersection.intersection.types.contains(&properties));
    assert_eq!(
        states[1].call_signature,
        callable_signature(checker, callable)
    );
    let NodeData::CallExpression(call) = &parsed.arena.get(states[1].call.node).unwrap().data
    else {
        unreachable!();
    };
    assert_eq!(
        checker.get_symbol_at_location(node(parsed, call.expression)),
        Ok(Some(states[0].parameter))
    );
    assert_eq!(
        checker.get_type_at_location(node(parsed, call.expression)),
        Ok(register)
    );
    let NodeData::TypeLiteralNode(properties_node) =
        &parsed.arena.get(*properties_node).unwrap().data
    else {
        unreachable!();
    };
    let [skip_node] = properties_node.members.nodes.as_slice() else {
        panic!("keep the actual skip property");
    };
    let NodeData::PropertySignatureDeclaration(skip) = &parsed.arena.get(*skip_node).unwrap().data
    else {
        unreachable!();
    };
    let skip_type = checker
        .get_type_at_location(node(parsed, skip.type_))
        .unwrap();
    assert_eq!(
        states[2].call_signature,
        callable_signature(checker, skip_type)
    );
    let NodeData::CallExpression(call) = &parsed.arena.get(states[2].call.node).unwrap().data
    else {
        unreachable!();
    };
    let NodeData::PropertyAccessExpression(access) =
        &parsed.arena.get(call.expression).unwrap().data
    else {
        unreachable!();
    };
    assert_eq!(
        checker.get_symbol_at_location(node(parsed, access.expression)),
        Ok(Some(states[0].parameter))
    );
    assert_eq!(
        checker.get_type_at_location(node(parsed, access.expression)),
        Ok(register)
    );
    assert_eq!(
        checker.get_symbol_at_location(node(parsed, access.name)),
        Ok(Some(symbol(checker, node(parsed, *skip_node))))
    );
    assert_eq!(
        checker.get_type_at_location(node(parsed, call.expression)),
        Ok(skip_type)
    );

    let assert_rhs = alias_rhs(parsed, "Assert");
    let assert_type = checker.get_type_at_location(assert_rhs).unwrap();
    assert_eq!(states[1].parameter_type, assert_type);
    assert_eq!(states[2].parameter_type, assert_type);
    assert_ne!(states[1].parameter, states[2].parameter);
    assert_ne!(states[1].signature, states[2].signature);
    let NodeData::TypeLiteralNode(assert_node) = &parsed.arena.get(assert_rhs.node).unwrap().data
    else {
        unreachable!();
    };
    assert_eq!(assert_node.members.nodes.len(), 4);
    for &member in &assert_node.members.nodes {
        let NodeData::PropertySignatureDeclaration(property) =
            &parsed.arena.get(member).unwrap().data
        else {
            unreachable!();
        };
        let property_symbol = symbol(checker, node(parsed, member));
        let property_type = checker
            .get_type_at_location(node(parsed, property.type_))
            .unwrap();
        assert_eq!(
            checker
                .store()
                .value_symbol_links(property_symbol)
                .unwrap()
                .resolved_type,
            Some(property_type)
        );
        let property_signature = callable_signature(checker, property_type);
        let record = checker.store().signature(property_signature).unwrap();
        assert_eq!(record.declaration(), Some(node(parsed, property.type_)));
        assert_eq!(
            record.resolved_return_type(),
            Some(checker.store().intrinsic_bootstrap().unwrap().void_type)
        );
        for &parameter in record.parameters() {
            assert_eq!(
                checker
                    .store()
                    .value_symbol_links(parameter)
                    .unwrap()
                    .resolved_type,
                Some(checker.store().intrinsic_bootstrap().unwrap().unknown_type)
            );
        }
        let NodeData::Identifier(name) = &parsed.arena.get(property.name).unwrap().data else {
            unreachable!();
        };
        let body_call = parsed
            .arena
            .iter()
            .find_map(|(id, record)| {
                let NodeData::CallExpression(call) = &record.data else {
                    return None;
                };
                let NodeData::PropertyAccessExpression(access) =
                    &parsed.arena.get(call.expression)?.data
                else {
                    return None;
                };
                let NodeData::Identifier(callee_name) = &parsed.arena.get(access.name)?.data else {
                    return None;
                };
                (callee_name.text == name.text).then_some(node(parsed, id))
            })
            .unwrap();
        assert_eq!(signature(checker, body_call), property_signature);
        assert_eq!(
            checker.get_type_at_location(body_call),
            Ok(checker.store().intrinsic_bootstrap().unwrap().void_type)
        );
    }
}

#[test]
fn const_arrow_callbacks_check_concise_and_statement_bodies() {
    let source = r#"const run = (fn: (value: number) => number): void => {};
run(value => value);
run(value => { return value; });
"#;
    check_program(
        source,
        &[(Expected::Number, Expected::Number); 2],
        1,
        false,
        |checker, parsed, states| {
            variable_callee(checker, parsed, "run", &[&states[0], &states[1]]);
            assert_ne!(states[0].owner, states[1].owner);
            assert_ne!(states[0].parameter, states[1].parameter);
            assert_ne!(states[0].signature, states[1].signature);
            assert_eq!(states[0].target, states[1].target);
            assert_eq!(states[0].target_signature, states[1].target_signature);
        },
    );
}

#[test]
fn pathe_register_callbacks_keep_intersection_owners_and_body_diagnostics() {
    // These aliases are the exact declarations from Pathe's glob.spec.ts.
    let source = r#"type Assert = {
  true: (v: unknown) => void;
  false: (v: unknown) => void;
  is: (a: unknown, b: unknown) => void;
  not: (a: unknown, b: unknown) => void;
};

type Register = ((label: string, body: (t: Assert) => void) => void) & {
  skip: (label: string, body: (t: Assert) => void) => void;
};

const describe = (name: string, fn: (it: Register) => void): void => {};
describe("suite", (it) => {
  it("case", (t) => {
    t.true(true);
    t.is("a", "a");
  });
  it.skip("skip", (t) => {
    t.false(false);
    t.not(1, 2);
  });
});
"#;
    let bad_source = source.replacen("it(\"case\",", "it(123,", 1);
    assert_ne!(bad_source, source);
    for (bad_argument, source) in [(false, source), (true, bad_source.as_str())] {
        check_program(
            source,
            &[
                (Expected::Alias("Register"), Expected::Void),
                (Expected::Alias("Assert"), Expected::Void),
                (Expected::Alias("Assert"), Expected::Void),
            ],
            2,
            bad_argument,
            check_pathe_owners,
        );
    }
}

#[test]
fn callback_callee_uses_the_nearest_lexical_parameter_owner() {
    let source = r#"const run = (fn: (value: string) => string): void => {};
const within = (run: (fn: (value: number) => number) => void): void => {
  run(value => value);
};
run(value => value);
"#;
    check_program(
        source,
        &[
            (Expected::Number, Expected::Number),
            (Expected::String, Expected::String),
        ],
        0,
        false,
        |checker, parsed, states| {
            variable_callee(checker, parsed, "run", &[&states[1]]);
            let within = declaration(parsed, "within");
            let NodeData::VariableDeclaration(variable) =
                &parsed.arena.get(within.node).unwrap().data
            else {
                unreachable!();
            };
            let within_arrow = variable.initializer.unwrap();
            let NodeData::ArrowFunction(arrow) = &parsed.arena.get(within_arrow).unwrap().data
            else {
                unreachable!();
            };
            let [parameter_node] = arrow.parameters.nodes.as_slice() else {
                unreachable!();
            };
            let NodeData::ParameterDeclaration(parameter) =
                &parsed.arena.get(*parameter_node).unwrap().data
            else {
                unreachable!();
            };
            let local = symbol(checker, node(parsed, *parameter_node));
            let global = symbol(checker, declaration(parsed, "run"));
            assert_ne!(local, global);
            let NodeData::CallExpression(call) =
                &parsed.arena.get(states[0].call.node).unwrap().data
            else {
                unreachable!();
            };
            assert!(inside(parsed, states[0].call.node, arrow.body));
            assert_eq!(
                checker.get_symbol_at_location(node(parsed, call.expression)),
                Ok(Some(local))
            );
            let target = checker
                .get_type_at_location(node(parsed, parameter.type_.unwrap()))
                .unwrap();
            assert_eq!(
                checker.get_type_at_location(node(parsed, call.expression)),
                Ok(target)
            );
            assert_eq!(
                states[0].call_signature,
                callable_signature(checker, target)
            );
            assert_eq!(
                checker
                    .store()
                    .signature(states[0].call_signature)
                    .unwrap()
                    .declaration(),
                Some(node(parsed, parameter.type_.unwrap()))
            );
            assert_ne!(states[0].call_signature, states[1].call_signature);
            assert_ne!(states[0].parameter, states[1].parameter);
        },
    );
}
