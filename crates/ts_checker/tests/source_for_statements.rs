use ts_ast::{FileId, NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId, SymbolFlags,
};
use ts_checker::semantic::signatures::TypePredicateKind;
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, IntrinsicBootstrapOptions, SourceCheckError,
    SourceSyntaxRole, TypeId, UnsupportedSourceSyntax,
};
use ts_parser::{ParseResult, parse_source_file};

const FILE: FileId = FileId::new(9_202);

fn context(parsed: &ParseResult) -> CanonicalCheckerContext<'_> {
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            FILE,
            CanonicalSourceFileFacts::new(
                EscapedName::source("\"/project/for-statements.ts\""),
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
        [(FILE, &parsed.arena)].into_iter().collect(),
        CanonicalCheckerOptions {
            intrinsic: IntrinsicBootstrapOptions {
                strict_null_checks: true,
                ..IntrinsicBootstrapOptions::default()
            },
            ..CanonicalCheckerOptions::default()
        },
    )
    .unwrap()
}

#[derive(Clone, Copy)]
struct Variable {
    declaration: NodeRef,
    name: NodeRef,
    initializer: Option<NodeRef>,
}

fn variables(parsed: &ParseResult, expected: &str) -> Vec<Variable> {
    let reference = |node| NodeRef::new(parsed.arena.id(), FILE, node);
    let mut variables = parsed
        .arena
        .iter()
        .filter_map(|(node, record)| {
            let NodeData::VariableDeclaration(variable) = &record.data else {
                return None;
            };
            let NodeData::Identifier(name) = &parsed.arena.get(variable.name)?.data else {
                return None;
            };
            (name.text == expected).then_some(Variable {
                declaration: reference(node),
                name: reference(variable.name),
                initializer: variable.initializer.map(reference),
            })
        })
        .collect::<Vec<_>>();
    variables.sort_unstable_by_key(|variable| {
        parsed
            .arena
            .get(variable.declaration.node)
            .unwrap()
            .range
            .start
    });
    variables
}

fn variable(parsed: &ParseResult, name: &str) -> Variable {
    let variables = variables(parsed, name);
    let [variable] = variables.as_slice() else {
        panic!("expected one variable named {name}")
    };
    *variable
}

fn nodes_of_kind(parsed: &ParseResult, kind: SyntaxKind) -> Vec<NodeRef> {
    let mut nodes = parsed
        .arena
        .iter()
        .filter_map(|(node, record)| {
            (record.kind == kind).then_some(NodeRef::new(parsed.arena.id(), FILE, node))
        })
        .collect::<Vec<_>>();
    nodes.sort_unstable_by_key(|node| parsed.arena.get(node.node).unwrap().range.start);
    nodes
}

fn symbol(checker: &CanonicalCheckerContext<'_>, variable: Variable) -> SemanticSymbolId {
    let symbol = checker
        .file(FILE)
        .unwrap()
        .1
        .symbol(variable.declaration)
        .unwrap();
    checker.store().get_merged_symbol(symbol).unwrap()
}

fn value_type(checker: &CanonicalCheckerContext<'_>, symbol: SemanticSymbolId) -> TypeId {
    checker
        .store()
        .value_symbol_links(symbol)
        .and_then(|links| links.resolved_type)
        .unwrap_or_else(|| panic!("missing value type for {symbol:?}"))
}

fn node_text<'source>(source: &'source str, parsed: &ParseResult, node: NodeRef) -> &'source str {
    let range = parsed.arena.get(node.node).unwrap().range;
    &source[usize::try_from(range.start.get()).unwrap()..usize::try_from(range.end.get()).unwrap()]
}

fn assert_diagnostics(
    checker: &CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    source: &str,
    expected: &[(u32, &str, &[&str])],
) {
    let diagnostics = checker.diagnostics().as_slice();
    assert_eq!(diagnostics.len(), expected.len(), "{diagnostics:?}");
    for (diagnostic, &(code, text, arguments)) in diagnostics.iter().zip(expected) {
        let node = diagnostic.node.expect("expected a source diagnostic");
        assert_eq!(node.file, FILE);
        assert_eq!(diagnostic.diagnostic.code(), code);
        assert_eq!(node_text(source, parsed, node), text);
        assert_eq!(diagnostic.diagnostic.arguments, arguments);
        assert_eq!(diagnostic.range_override, None);
        assert!(diagnostic.related_information.is_empty());
    }
}

fn assert_recheck_stable(checker: &mut CanonicalCheckerContext<'_>, parsed: &ParseResult) {
    let snapshot = |checker: &CanonicalCheckerContext<'_>| {
        let store = checker.store();
        (
            [
                store.type_len(),
                store.type_alias_len(),
                store.symbol_len(),
                store.signature_len(),
                store.mapper_len(),
                store.index_info_len(),
                store.symbol_store().symbol_table_len(),
            ],
            store.relation_state_snapshot(),
            parsed
                .arena
                .iter()
                .map(|(node, _)| {
                    let node = NodeRef::new(parsed.arena.id(), FILE, node);
                    (
                        node,
                        store.node_links(node).cloned(),
                        store.type_node_links(node).cloned(),
                        store.symbol_node_links(node).cloned(),
                        store.signature_links(node).cloned(),
                    )
                })
                .collect::<Vec<_>>(),
            store
                .symbol_store()
                .symbols()
                .map(|(symbol, _)| {
                    (
                        symbol,
                        store.value_symbol_links(symbol).cloned(),
                        store.declared_type_links(symbol).cloned(),
                    )
                })
                .collect::<Vec<_>>(),
            store
                .source_file_links(checker.source_file(FILE).unwrap())
                .cloned(),
            checker.diagnostics().clone(),
        )
    };
    let before = snapshot(checker);
    for _ in 0..2 {
        checker.recheck_source_file(FILE).unwrap();
        assert!(
            checker
                .store()
                .source_file_links(checker.source_file(FILE).unwrap())
                .unwrap()
                .type_checked
        );
        assert_eq!(snapshot(checker), before);
    }
}

#[test]
fn for_let_and_var_bindings_keep_distinct_owners_and_real_types() {
    let parsed = parse_source_file(concat!(
        "let index = 'outside';\n",
        "for (let index = 0, limit: number = 2; index < limit; index++) {\n",
        "  const inside: number = index;\n",
        "  const bound: number = limit;\n",
        "}\n",
        "const outside: string = index;\n",
        "for (var count = 0; count < 2; ++count) {\n",
        "  const current: number = count;\n",
        "}\n",
        "const after: number = count;\n",
    ));
    let mut checker = context(&parsed);
    checker.check_source_file(FILE).unwrap();
    assert!(
        checker.diagnostics().is_empty(),
        "{:?}",
        checker.diagnostics()
    );

    let loops = nodes_of_kind(&parsed, SyntaxKind::ForStatement);
    let [lexical_loop, var_loop] = loops.as_slice() else {
        panic!("expected both original loops")
    };
    let declarations = variables(&parsed, "index");
    let [outer, inner] = declarations.as_slice() else {
        panic!("expected distinct outer and loop declarations")
    };
    let outer_symbol = symbol(&checker, *outer);
    let inner_symbol = symbol(&checker, *inner);
    let limit = variable(&parsed, "limit");
    let limit_symbol = symbol(&checker, limit);
    let count = variable(&parsed, "count");
    let count_symbol = symbol(&checker, count);
    assert_ne!(outer_symbol, inner_symbol);
    assert_ne!(inner_symbol, limit_symbol);

    let bound = checker.file(FILE).unwrap().1;
    let source = bound.source_file();
    let local_symbol = |owner, name| {
        bound
            .locals(owner)
            .and_then(|locals| checker.store().symbol_table(locals))
            .and_then(|locals| locals.get_source(name))
    };
    assert_eq!(bound.container(inner.declaration), Some(source));
    assert_eq!(
        bound.block_scope_container(inner.declaration),
        Some(*lexical_loop)
    );
    assert_eq!(local_symbol(*lexical_loop, "index"), Some(inner_symbol));
    assert_eq!(local_symbol(*lexical_loop, "limit"), Some(limit_symbol));
    assert_eq!(local_symbol(source, "index"), Some(outer_symbol));
    assert_eq!(bound.container(count.declaration), Some(source));
    assert_eq!(local_symbol(source, "count"), Some(count_symbol));
    assert_eq!(local_symbol(*var_loop, "count"), None);
    assert_eq!(
        checker.store().symbol(inner_symbol).unwrap().flags(),
        SymbolFlags::BLOCK_SCOPED_VARIABLE
    );
    assert_eq!(
        checker.store().symbol(count_symbol).unwrap().flags(),
        SymbolFlags::FUNCTION_SCOPED_VARIABLE
    );

    let bootstrap = checker.store().intrinsic_bootstrap().unwrap();
    let number = bootstrap.number_type;
    let string = bootstrap.string_type;
    for (owner, expected) in [
        (outer_symbol, string),
        (inner_symbol, number),
        (limit_symbol, number),
        (count_symbol, number),
    ] {
        assert_eq!(value_type(&checker, owner), expected);
    }
    for (name, expected, owner) in [
        ("inside", number, inner_symbol),
        ("bound", number, limit_symbol),
        ("outside", string, outer_symbol),
        ("current", number, count_symbol),
        ("after", number, count_symbol),
    ] {
        let read = variable(&parsed, name).initializer.unwrap();
        assert_eq!(checker.get_type_at_location(read), Ok(expected));
        assert_eq!(checker.get_symbol_at_location(read), Ok(Some(owner)));
    }
    assert_recheck_stable(&mut checker, &parsed);
}

#[test]
fn for_header_and_body_diagnostics_keep_go_order_and_source_anchors() {
    let source = concat!(
        "declare const gate: void;\n",
        "declare function consume(value: number): void;\n",
        "for (let index: number = 'initial'; gate; consume('increment')) {\n",
        "  const body: string = index;\n",
        "}\n",
    );
    let parsed = parse_source_file(source);
    let mut checker = context(&parsed);
    checker.check_source_file(FILE).unwrap();

    // The pinned Go checker visits the increment before the body.
    assert_diagnostics(
        &checker,
        &parsed,
        source,
        &[
            (2322, "index", &["string", "number"]),
            (1345, "gate", &[]),
            (2345, "'increment'", &["string", "number"]),
            (2322, "body", &["number", "string"]),
        ],
    );
    let bootstrap = checker.store().intrinsic_bootstrap().unwrap();
    let number = bootstrap.number_type;
    let void = bootstrap.void_type;
    let index = variable(&parsed, "index");
    let index_symbol = symbol(&checker, index);
    assert_eq!(value_type(&checker, index_symbol), number);
    let body = variable(&parsed, "body");
    let read = body.initializer.unwrap();
    assert_eq!(checker.get_type_at_location(read), Ok(number));
    assert_eq!(checker.get_symbol_at_location(read), Ok(Some(index_symbol)));
    let calls = nodes_of_kind(&parsed, SyntaxKind::CallExpression);
    let [increment] = calls.as_slice() else {
        panic!("expected one increment call")
    };
    assert_eq!(checker.get_type_at_location(*increment), Ok(void));
    let NodeData::CallExpression(call) = &parsed.arena.get(increment.node).unwrap().data else {
        unreachable!()
    };
    let iteration = nodes_of_kind(&parsed, SyntaxKind::ForStatement)[0];
    let NodeData::ForStatement(iteration) = &parsed.arena.get(iteration.node).unwrap().data else {
        unreachable!()
    };
    let reference = |node| NodeRef::new(parsed.arena.id(), FILE, node);
    assert_eq!(
        checker
            .diagnostics()
            .as_slice()
            .iter()
            .map(|diagnostic| diagnostic.node)
            .collect::<Vec<_>>(),
        [
            Some(index.name),
            iteration.condition.map(reference),
            Some(reference(call.arguments.nodes[0])),
            Some(body.name),
        ]
    );
    assert_recheck_stable(&mut checker, &parsed);
}

#[test]
fn for_const_updates_and_conditional_jumps_keep_literal_diagnostics() {
    let source = concat!(
        "for (const fixed = 0; fixed < 1; ++fixed) {\n",
        "  const current: 0 = fixed;\n",
        "  if (fixed == 1) { break; }\n",
        "  if (fixed == 2) { continue; }\n",
        "}\n",
    );
    let parsed = parse_source_file(source);
    let mut checker = context(&parsed);
    checker.check_source_file(FILE).unwrap();
    assert_diagnostics(
        &checker,
        &parsed,
        source,
        &[
            (2588, "fixed", &["fixed"]),
            (2367, "fixed == 1", &["0", "1"]),
            (2367, "fixed == 2", &["0", "2"]),
        ],
    );

    let fixed = symbol(&checker, variable(&parsed, "fixed"));
    let zero = value_type(&checker, fixed);
    assert_eq!(checker.type_to_string(zero).unwrap(), "0");
    let read = variable(&parsed, "current").initializer.unwrap();
    assert_eq!(checker.get_type_at_location(read), Ok(zero));
    assert_eq!(checker.get_symbol_at_location(read), Ok(Some(fixed)));
    let incrementors = nodes_of_kind(&parsed, SyntaxKind::PrefixUnaryExpression);
    let [incrementor] = incrementors.as_slice() else {
        panic!("expected the const increment expression")
    };
    let NodeData::PrefixUnaryExpression(increment) =
        &parsed.arena.get(incrementor.node).unwrap().data
    else {
        unreachable!()
    };
    let operand = NodeRef::new(parsed.arena.id(), FILE, increment.operand);
    assert_eq!(checker.diagnostics().as_slice()[0].node, Some(operand));
    let bootstrap = checker.store().intrinsic_bootstrap().unwrap();
    let number = bootstrap.number_type;
    let error = bootstrap.error_type;
    assert_eq!(checker.get_type_at_location(operand), Ok(error));
    assert_eq!(checker.get_symbol_at_location(operand), Ok(Some(fixed)));
    assert_eq!(checker.get_type_at_location(*incrementor), Ok(number));
    assert_recheck_stable(&mut checker, &parsed);
}

#[test]
fn for_expression_and_omitted_headers_check_calls_and_terminal_jumps() {
    let parsed = parse_source_file(concat!(
        "declare function begin(): number;\n",
        "declare function step(): number;\n",
        "let count = 0;\n",
        "for (begin(); count < 2; step()) { const copy: number = count; }\n",
    ));
    let mut checker = context(&parsed);
    checker.check_source_file(FILE).unwrap();
    assert!(
        checker.diagnostics().is_empty(),
        "{:?}",
        checker.diagnostics()
    );
    let number = checker.store().intrinsic_bootstrap().unwrap().number_type;
    let calls = nodes_of_kind(&parsed, SyntaxKind::CallExpression);
    assert_eq!(calls.len(), 2);
    for call in calls {
        assert_eq!(checker.get_type_at_location(call), Ok(number));
    }
    let count = symbol(&checker, variable(&parsed, "count"));
    let copy = variable(&parsed, "copy").initializer.unwrap();
    assert_eq!(checker.get_type_at_location(copy), Ok(number));
    assert_eq!(checker.get_symbol_at_location(copy), Ok(Some(count)));
    assert_recheck_stable(&mut checker, &parsed);

    for body in [
        "",
        "const copy: number = count; break;",
        "const copy: number = count; continue;",
    ] {
        let source = format!("let count = 0; for (;;) {{ {body} }}");
        let parsed = parse_source_file(&source);
        let mut checker = context(&parsed);
        checker.check_source_file(FILE).unwrap();
        assert!(
            checker.diagnostics().is_empty(),
            "{:?}",
            checker.diagnostics()
        );
        let number = checker.store().intrinsic_bootstrap().unwrap().number_type;
        let count = symbol(&checker, variable(&parsed, "count"));
        assert_eq!(value_type(&checker, count), number);
        if !body.is_empty() {
            let copy = variable(&parsed, "copy").initializer.unwrap();
            assert_eq!(checker.get_type_at_location(copy), Ok(number));
            assert_eq!(checker.get_symbol_at_location(copy), Ok(Some(count)));
        }
        assert_recheck_stable(&mut checker, &parsed);
    }
}

#[test]
fn for_flow_changing_guards_and_updates_publish_actual_types() {
    for (source, guard_kind) in [
        (
            concat!(
                "declare const value: string | undefined;\n",
                "for (; value;) { const inside: string = value; }\n",
            ),
            SyntaxKind::ForStatement,
        ),
        (
            concat!(
                "declare const stop: boolean;\n",
                "for (;;) {\n",
                "  if (stop) { break; }\n",
                "  const inside: boolean = stop;\n",
                "}\n",
            ),
            SyntaxKind::IfStatement,
        ),
        (
            concat!(
                "for (var count: 0 | 1 = 0; count < 1; ++count) {\n",
                "  const inside: 0 = count;\n",
                "}\n",
            ),
            SyntaxKind::PrefixUnaryExpression,
        ),
    ] {
        let parsed = parse_source_file(source);
        let mut checker = context(&parsed);
        checker.check_source_file(FILE).unwrap();
        let file = checker.source_file(FILE).unwrap();
        let file_links = checker.store().source_file_links(file).unwrap();
        assert!(file_links.type_checked);
        let inside = variable(&parsed, "inside");
        let inside_symbol = symbol(&checker, inside);
        let bootstrap = checker.store().intrinsic_bootstrap().unwrap();
        let boolean = bootstrap.boolean_type;
        let (name, expected_flow, expected_inside) = match guard_kind {
            SyntaxKind::ForStatement => ("value", bootstrap.string_type, "string"),
            SyntaxKind::IfStatement => ("stop", bootstrap.regular_false_type, "boolean"),
            SyntaxKind::PrefixUnaryExpression => ("count", bootstrap.number_type, "0"),
            _ => unreachable!(),
        };
        let input = variable(&parsed, name);
        let owner = symbol(&checker, input);
        let declared = value_type(&checker, owner);
        assert_eq!(checker.get_type_at_location(input.name), Ok(declared));
        if guard_kind == SyntaxKind::IfStatement {
            assert_eq!(declared, boolean);
            assert_eq!(value_type(&checker, inside_symbol), boolean);
        } else {
            let ts_checker::semantic::TypeData::Union(union) =
                checker.store().type_payload(declared).unwrap().data()
            else {
                panic!("expected the original declared union")
            };
            let mut members = union
                .union
                .types
                .iter()
                .map(|&type_| checker.type_to_string(type_).unwrap())
                .collect::<Vec<_>>();
            members.sort_unstable();
            let expected = if guard_kind == SyntaxKind::ForStatement {
                ["string", "undefined"]
            } else {
                ["0", "1"]
            };
            assert_eq!(members, expected);
        }
        let read = inside.initializer.unwrap();
        assert_eq!(checker.get_type_at_location(read), Ok(expected_flow));
        assert_eq!(checker.get_symbol_at_location(read), Ok(Some(owner)));
        let inside_type = value_type(&checker, inside_symbol);
        assert_eq!(
            checker.type_to_string(inside_type).unwrap(),
            expected_inside
        );
        assert_eq!(checker.get_type_at_location(inside.name), Ok(inside_type));
        if guard_kind == SyntaxKind::PrefixUnaryExpression {
            assert_diagnostics(
                &checker,
                &parsed,
                source,
                &[(2322, "inside", &["number", "0"])],
            );
            assert_eq!(checker.diagnostics().as_slice()[0].node, Some(inside.name));
        } else {
            assert_diagnostics(&checker, &parsed, source, &[]);
        }
        checker.check_source_file(FILE).unwrap();
        assert_recheck_stable(&mut checker, &parsed);
        assert_eq!(value_type(&checker, owner), declared);
    }
}

#[test]
fn for_assertion_calls_publish_later_local_types() {
    let parsed = parse_source_file(concat!(
        "declare function assertString(value: unknown): asserts value is string;\n",
        "declare const value: unknown;\n",
        "for (;;) {\n",
        "  assertString(value);\n",
        "  const inside: string = value;\n",
        "  break;\n",
        "}\n",
    ));
    let mut checker = context(&parsed);
    checker.check_source_file(FILE).unwrap();
    let file = checker.source_file(FILE).unwrap();
    let file_links = checker.store().source_file_links(file).unwrap();
    assert!(file_links.type_checked);
    let calls = nodes_of_kind(&parsed, SyntaxKind::CallExpression);
    let [call] = calls.as_slice() else {
        panic!("expected the assertion call")
    };
    let inside = variable(&parsed, "inside");
    let inside_symbol = symbol(&checker, inside);

    let call_links = checker.store().signature_links(*call).cloned().unwrap();
    let signature = checker
        .store()
        .signature(call_links.resolved_signature.signature().unwrap())
        .unwrap();
    let predicate = signature
        .resolved_type_predicate()
        .and_then(|predicate| checker.store().type_predicate(predicate))
        .unwrap();
    let bootstrap = checker.store().intrinsic_bootstrap().unwrap();
    assert_eq!(signature.resolved_return_type(), Some(bootstrap.void_type));
    assert_eq!(predicate.kind(), TypePredicateKind::AssertsIdentifier);
    assert_eq!(predicate.parameter_index(), 0);
    assert_eq!(predicate.parameter_name(), "value");
    assert_eq!(predicate.type_id(), Some(bootstrap.string_type));
    let string = bootstrap.string_type;
    let unknown = bootstrap.unknown_type;
    assert_eq!(
        call_links.effects_signature,
        ts_checker::semantic::EffectsSignatureState::Resolved(
            call_links.resolved_signature.signature().unwrap()
        )
    );
    let value = symbol(&checker, variable(&parsed, "value"));
    assert_eq!(value_type(&checker, value), unknown);
    assert_eq!(value_type(&checker, inside_symbol), string);
    assert_eq!(checker.get_type_at_location(inside.name), Ok(string));
    let read = inside.initializer.unwrap();
    assert_eq!(checker.get_type_at_location(read), Ok(string));
    assert_eq!(checker.get_symbol_at_location(read), Ok(Some(value)));
    assert!(checker.diagnostics().is_empty());

    let counts = (
        checker.store().type_len(),
        checker.store().mapper_len(),
        checker.store().signature_len(),
        checker.store().type_predicate_len(),
        checker.store().relation_state_snapshot(),
    );
    checker.check_source_file(FILE).unwrap();
    assert_recheck_stable(&mut checker, &parsed);
    assert_eq!(
        (
            checker.store().type_len(),
            checker.store().mapper_len(),
            checker.store().signature_len(),
            checker.store().type_predicate_len(),
            checker.store().relation_state_snapshot(),
        ),
        counts
    );
    assert_eq!(checker.store().signature_links(*call), Some(&call_links));
}

#[test]
fn for_destructuring_remains_an_atomic_typed_boundary() {
    let parsed = parse_source_file(concat!(
        "const before: number = 1;\n",
        "for (let [index] = [0]; index < 1; ++index) {}\n",
    ));
    let mut checker = context(&parsed);
    let before = variable(&parsed, "before");
    let before_symbol = symbol(&checker, before);
    let patterns = nodes_of_kind(&parsed, SyntaxKind::ArrayBindingPattern);
    let [pattern] = patterns.as_slice() else {
        panic!("expected the unsupported loop binding")
    };
    let counts = (
        checker.store().type_len(),
        checker.store().mapper_len(),
        checker.store().signature_len(),
        checker.store().relation_state_snapshot(),
    );
    for _ in 0..2 {
        assert_eq!(
            checker.check_source_file(FILE),
            Err(SourceCheckError::Unsupported(
                UnsupportedSourceSyntax::Syntax {
                    node: *pattern,
                    kind: SyntaxKind::ArrayBindingPattern,
                    role: SourceSyntaxRole::Statement,
                }
            ))
        );
        assert_eq!(
            (
                checker.store().type_len(),
                checker.store().mapper_len(),
                checker.store().signature_len(),
                checker.store().relation_state_snapshot(),
            ),
            counts
        );
        assert!(checker.store().value_symbol_links(before_symbol).is_none());
        assert!(checker.store().type_node_links(before.name).is_none());
        assert!(checker.diagnostics().is_empty());
        assert!(
            checker
                .store()
                .source_file_links(checker.source_file(FILE).unwrap())
                .is_none_or(|links| !links.type_checked)
        );
    }
}
