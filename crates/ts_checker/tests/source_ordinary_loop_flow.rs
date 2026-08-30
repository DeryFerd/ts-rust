use ts_ast::{FileId, NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId, SymbolFlags,
};
use ts_checker::semantic::signatures::TypePredicateKind;
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, EffectsSignatureState,
    IntrinsicBootstrapOptions, SignatureId, TypeData, TypeId,
};
use ts_parser::{ParseResult, parse_source_file};

const FILE: FileId = FileId::new(9_205);

fn context(parsed: &ParseResult) -> CanonicalCheckerContext<'_> {
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            FILE,
            CanonicalSourceFileFacts::new(
                EscapedName::source("\"/project/ordinary-loop-flow.ts\""),
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

fn variable(parsed: &ParseResult, expected: &str) -> Variable {
    let reference = |node| NodeRef::new(parsed.arena.id(), FILE, node);
    let variables = parsed
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
    let [variable] = variables.as_slice() else {
        panic!("expected one variable named {expected}")
    };
    *variable
}

fn only_node(parsed: &ParseResult, kind: SyntaxKind) -> NodeRef {
    let nodes = parsed
        .arena
        .iter()
        .filter_map(|(node, record)| {
            (record.kind == kind).then_some(NodeRef::new(parsed.arena.id(), FILE, node))
        })
        .collect::<Vec<_>>();
    let [node] = nodes.as_slice() else {
        panic!("expected one {kind:?}")
    };
    *node
}

fn symbol(checker: &CanonicalCheckerContext<'_>, declaration: NodeRef) -> SemanticSymbolId {
    let bound = checker.file(FILE).unwrap().1;
    checker
        .store()
        .get_merged_symbol(bound.symbol(declaration).unwrap())
        .unwrap()
}

fn value_type(checker: &CanonicalCheckerContext<'_>, symbol: SemanticSymbolId) -> TypeId {
    checker
        .store()
        .value_symbol_links(symbol)
        .and_then(|links| links.resolved_type)
        .unwrap_or_else(|| panic!("missing value type for {symbol:?}"))
}

fn assert_read(
    checker: &mut CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    local: &str,
    owner: SemanticSymbolId,
    expected: &str,
) -> TypeId {
    let read = variable(parsed, local).initializer.unwrap();
    assert_eq!(
        parsed.arena.get(read.node).unwrap().kind,
        SyntaxKind::Identifier
    );
    let type_ = checker.get_type_at_location(read).unwrap();
    assert_eq!(checker.type_to_string(type_).unwrap(), expected, "{local}");
    assert_eq!(
        checker.get_symbol_at_location(read),
        Ok(Some(owner)),
        "{local}"
    );
    type_
}

fn assert_union_members(checker: &CanonicalCheckerContext<'_>, type_: TypeId, expected: &[&str]) {
    let TypeData::Union(union) = checker.store().type_payload(type_).unwrap().data() else {
        panic!("expected the declared union")
    };
    let mut actual = union
        .union
        .types
        .iter()
        .map(|&type_| checker.type_to_string(type_).unwrap())
        .collect::<Vec<_>>();
    let mut expected = expected.to_vec();
    actual.sort_unstable();
    expected.sort_unstable();
    assert_eq!(actual, expected);
}

fn effects_signature(checker: &CanonicalCheckerContext<'_>, call: NodeRef) -> SignatureId {
    let links = checker.store().signature_links(call).unwrap();
    let resolved = links.resolved_signature.signature().unwrap();
    assert_eq!(
        links.effects_signature,
        EffectsSignatureState::Resolved(resolved)
    );
    resolved
}

fn assert_missing_argument(
    checker: &CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    callee: NodeRef,
) {
    let [diagnostic] = checker.diagnostics().as_slice() else {
        panic!("expected only the missing argument diagnostic")
    };
    assert_eq!(diagnostic.diagnostic.code(), 2554);
    assert_eq!(diagnostic.diagnostic.arguments, ["1", "0"]);
    assert_eq!(diagnostic.node, Some(callee));
    assert_eq!(diagnostic.range_override, None);
    let [related] = diagnostic.related_information.as_slice() else {
        panic!("expected the original parameter declaration")
    };
    assert_eq!(related.diagnostic.code(), 6210);
    assert_eq!(related.diagnostic.arguments, ["value"]);
    assert_eq!(related.node, Some(only_node(parsed, SyntaxKind::Parameter)));
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
                store.type_predicate_len(),
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
    checker.check_source_file(FILE).unwrap();
    assert_eq!(snapshot(checker), before);
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
fn for_conditions_narrow_body_and_normal_exit_without_demanding_unrelated_locals() {
    for (source, members, inside_type, after_type) in [
        (
            concat!(
                "declare let value: object | undefined;\n",
                "for (; value;) {\n",
                "  const unrelated = 1;\n",
                "  const inside: object = value;\n",
                "}\n",
                "type Retained = number;\n",
                "class RetainedValue {}\n",
                "const after: undefined = value;\n",
            ),
            ["object", "undefined"],
            "object",
            "undefined",
        ),
        (
            concat!(
                "declare let value: 'open' | 'closed';\n",
                "for (; value === 'open';) {\n",
                "  const unrelated = 1;\n",
                "  const inside: 'open' = value;\n",
                "}\n",
                "interface Retained { value: number; }\n",
                "const after: 'closed' = value;\n",
            ),
            ["\"open\"", "\"closed\""],
            "\"open\"",
            "\"closed\"",
        ),
    ] {
        let parsed = parse_source_file(source);
        let mut checker = context(&parsed);
        checker.check_source_file(FILE).unwrap();
        assert!(
            checker.diagnostics().is_empty(),
            "{:?}",
            checker.diagnostics()
        );
        let value = symbol(&checker, variable(&parsed, "value").declaration);
        let declared = value_type(&checker, value);
        assert_union_members(&checker, declared, &members);
        let inside = assert_read(&mut checker, &parsed, "inside", value, inside_type);
        let after = assert_read(&mut checker, &parsed, "after", value, after_type);
        assert_ne!(inside, after);
        assert_eq!(value_type(&checker, value), declared);
        let unrelated = symbol(&checker, variable(&parsed, "unrelated").declaration);
        assert_ne!(unrelated, value);
        assert_eq!(
            checker
                .type_to_string(value_type(&checker, unrelated))
                .unwrap(),
            "1"
        );
        assert_recheck_stable(&mut checker, &parsed);
    }
}

#[test]
fn for_break_and_continue_joins_keep_the_actual_exit_path() {
    for (conditional_jump, terminal_jump, after_type) in [
        ("break", "continue", "true"),
        ("continue", "break", "false"),
    ] {
        let source = format!(
            "declare const stop: boolean;\n\
             for (;;) {{\n\
               const unrelated = 1;\n\
               if (stop) {{ {conditional_jump}; }}\n\
               const inside: false = stop;\n\
               {terminal_jump};\n\
             }}\n\
             const after: {after_type} = stop;\n"
        );
        let parsed = parse_source_file(&source);
        let mut checker = context(&parsed);
        checker.check_source_file(FILE).unwrap();
        assert!(
            checker.diagnostics().is_empty(),
            "{:?}",
            checker.diagnostics()
        );
        let stop = symbol(&checker, variable(&parsed, "stop").declaration);
        let boolean = checker.store().intrinsic_bootstrap().unwrap().boolean_type;
        assert_eq!(value_type(&checker, stop), boolean);
        assert_read(&mut checker, &parsed, "inside", stop, "false");
        assert_read(&mut checker, &parsed, "after", stop, after_type);
        let iteration = only_node(&parsed, SyntaxKind::ForStatement);
        let inside = variable(&parsed, "inside");
        let NodeData::ForStatement(iteration_data) =
            &parsed.arena.get(iteration.node).unwrap().data
        else {
            unreachable!()
        };
        assert_eq!(
            checker
                .file(FILE)
                .unwrap()
                .1
                .block_scope_container(inside.declaration),
            Some(NodeRef::new(
                parsed.arena.id(),
                FILE,
                iteration_data.statement
            ))
        );
        assert_ne!(symbol(&checker, inside.declaration), stop);
        assert_recheck_stable(&mut checker, &parsed);
    }
}

#[test]
fn for_increment_flow_widens_regular_literals_but_keeps_the_declared_union() {
    for (header, binding, increment_kind) in [
        (
            "for (var count: 0 | 1 = 0; count < 2; ++count)",
            SymbolFlags::FUNCTION_SCOPED_VARIABLE,
            SyntaxKind::PrefixUnaryExpression,
        ),
        (
            "let count: 0 | 1 = 0; for (; count < 2; count++)",
            SymbolFlags::BLOCK_SCOPED_VARIABLE,
            SyntaxKind::PostfixUnaryExpression,
        ),
    ] {
        let source = format!(
            "{header} {{\n\
               const unrelated = true;\n\
               const inside: number = count;\n\
             }}\n\
             const after: number = count;\n\
             const wrong: 0 = count;\n"
        );
        let parsed = parse_source_file(&source);
        let mut checker = context(&parsed);
        checker.check_source_file(FILE).unwrap();
        let count = variable(&parsed, "count");
        let owner = symbol(&checker, count.declaration);
        let declared = value_type(&checker, owner);
        assert_union_members(&checker, declared, &["0", "1"]);
        assert_eq!(checker.store().symbol(owner).unwrap().flags(), binding);
        let bound = checker.file(FILE).unwrap().1;
        let source_locals = bound.locals(bound.source_file()).unwrap();
        assert_eq!(
            checker
                .store()
                .symbol_table(source_locals)
                .unwrap()
                .get_source("count"),
            Some(owner)
        );
        let number = checker.store().intrinsic_bootstrap().unwrap().number_type;
        for local in ["inside", "after", "wrong"] {
            assert_eq!(
                assert_read(&mut checker, &parsed, local, owner, "number"),
                number
            );
        }
        let increment = only_node(&parsed, increment_kind);
        let operand = match &parsed.arena.get(increment.node).unwrap().data {
            NodeData::PrefixUnaryExpression(increment) => increment.operand,
            NodeData::PostfixUnaryExpression(increment) => increment.operand,
            _ => unreachable!(),
        };
        let operand = NodeRef::new(parsed.arena.id(), FILE, operand);
        assert_eq!(checker.get_type_at_location(increment), Ok(number));
        assert_eq!(checker.get_type_at_location(operand), Ok(number));
        assert_eq!(checker.get_symbol_at_location(operand), Ok(Some(owner)));
        assert_eq!(value_type(&checker, owner), declared);
        let diagnostics = checker.diagnostics().as_slice();
        let [diagnostic] = diagnostics else {
            panic!("expected only the later literal assignment error: {diagnostics:?}")
        };
        assert_eq!(diagnostic.diagnostic.code(), 2322);
        assert_eq!(diagnostic.diagnostic.arguments, ["number", "0"]);
        assert_eq!(diagnostic.node, Some(variable(&parsed, "wrong").name));
        assert_eq!(diagnostic.range_override, None);
        assert!(diagnostic.related_information.is_empty());
        assert_recheck_stable(&mut checker, &parsed);
    }
}

#[test]
fn for_uninitialized_declarations_and_unreachable_updates_keep_declared_types() {
    for (source, has_update) in [
        (
            "for (let count: number; false;) { const inside: number = count; }",
            false,
        ),
        (
            "for (let count = 0;; ++count) { const inside: number = count; break; }",
            true,
        ),
    ] {
        let parsed = parse_source_file(source);
        let mut checker = context(&parsed);
        checker.check_source_file(FILE).unwrap();
        assert!(
            checker.diagnostics().is_empty(),
            "{:?}",
            checker.diagnostics()
        );
        let count = symbol(&checker, variable(&parsed, "count").declaration);
        let number = checker.store().intrinsic_bootstrap().unwrap().number_type;
        assert_eq!(value_type(&checker, count), number);
        assert_eq!(
            checker.store().symbol(count).unwrap().flags(),
            SymbolFlags::BLOCK_SCOPED_VARIABLE
        );
        assert_eq!(
            assert_read(&mut checker, &parsed, "inside", count, "number"),
            number
        );
        if has_update {
            let update = only_node(&parsed, SyntaxKind::PrefixUnaryExpression);
            let NodeData::PrefixUnaryExpression(data) =
                &parsed.arena.get(update.node).unwrap().data
            else {
                unreachable!()
            };
            let operand = NodeRef::new(parsed.arena.id(), FILE, data.operand);
            assert_eq!(checker.get_type_at_location(update), Ok(number));
            assert_eq!(checker.get_type_at_location(operand), Ok(number));
            assert_eq!(checker.get_symbol_at_location(operand), Ok(Some(count)));
        }
        assert_recheck_stable(&mut checker, &parsed);
    }

    let parsed = parse_source_file("let count: 0 | 1 = 0; for (;; ++count) { break; }");
    let mut checker = context(&parsed);
    checker.check_source_file(FILE).unwrap();
    assert!(
        checker.diagnostics().is_empty(),
        "{:?}",
        checker.diagnostics()
    );
    let count = symbol(&checker, variable(&parsed, "count").declaration);
    let declared = value_type(&checker, count);
    assert_union_members(&checker, declared, &["0", "1"]);
    let number = checker.store().intrinsic_bootstrap().unwrap().number_type;
    let update = only_node(&parsed, SyntaxKind::PrefixUnaryExpression);
    let NodeData::PrefixUnaryExpression(data) = &parsed.arena.get(update.node).unwrap().data else {
        unreachable!()
    };
    let operand = NodeRef::new(parsed.arena.id(), FILE, data.operand);
    assert_eq!(checker.get_type_at_location(operand), Ok(declared));
    assert_eq!(checker.get_type_at_location(update), Ok(number));
    assert_eq!(checker.get_symbol_at_location(operand), Ok(Some(count)));
    assert_eq!(value_type(&checker, count), declared);
    assert_recheck_stable(&mut checker, &parsed);
}

#[test]
fn for_assertion_effects_narrow_the_body_and_the_terminating_break() {
    let parsed = parse_source_file(concat!(
        "declare function assertString(value: unknown): asserts value is string;\n",
        "declare const value: unknown;\n",
        "for (;;) {\n",
        "  assertString(value);\n",
        "  const inside: string = value;\n",
        "  break;\n",
        "}\n",
        "const after: string = value;\n",
    ));
    let mut checker = context(&parsed);
    checker.check_source_file(FILE).unwrap();
    assert!(
        checker.diagnostics().is_empty(),
        "{:?}",
        checker.diagnostics()
    );
    let value = symbol(&checker, variable(&parsed, "value").declaration);
    let bootstrap = checker.store().intrinsic_bootstrap().unwrap();
    let unknown = bootstrap.unknown_type;
    let string = bootstrap.string_type;
    let void = bootstrap.void_type;
    assert_eq!(value_type(&checker, value), unknown);
    for local in ["inside", "after"] {
        assert_eq!(
            assert_read(&mut checker, &parsed, local, value, "string"),
            string
        );
    }
    let call = only_node(&parsed, SyntaxKind::CallExpression);
    let signature = checker
        .store()
        .signature(effects_signature(&checker, call))
        .unwrap();
    assert_eq!(signature.resolved_return_type(), Some(void));
    let predicate = signature
        .resolved_type_predicate()
        .and_then(|predicate| checker.store().type_predicate(predicate))
        .unwrap();
    assert_eq!(predicate.kind(), TypePredicateKind::AssertsIdentifier);
    assert_eq!(predicate.parameter_index(), 0);
    assert_eq!(predicate.parameter_name(), "value");
    assert_eq!(predicate.type_id(), Some(string));
    let NodeData::CallExpression(call_data) = &parsed.arena.get(call.node).unwrap().data else {
        unreachable!()
    };
    let [argument] = call_data.arguments.nodes.as_slice() else {
        panic!("expected the original assertion argument")
    };
    let argument = NodeRef::new(parsed.arena.id(), FILE, *argument);
    assert_eq!(checker.get_type_at_location(argument), Ok(unknown));
    assert_eq!(checker.get_symbol_at_location(argument), Ok(Some(value)));
    assert_eq!(checker.get_type_at_location(call), Ok(void));
    assert_recheck_stable(&mut checker, &parsed);
}

#[test]
fn for_never_call_removes_the_non_break_path_from_the_exit_type() {
    // The second break must not add undefined to the exit type.
    let parsed = parse_source_file(concat!(
        "declare function fail(): never;\n",
        "declare const value: object | undefined;\n",
        "for (;;) {\n",
        "  if (value) { break; }\n",
        "  const nonBreak: undefined = value;\n",
        "  fail();\n",
        "  break;\n",
        "}\n",
        "const after: object = value;\n",
    ));
    let mut checker = context(&parsed);
    checker.check_source_file(FILE).unwrap();
    assert!(
        checker.diagnostics().is_empty(),
        "{:?}",
        checker.diagnostics()
    );
    let value = symbol(&checker, variable(&parsed, "value").declaration);
    assert_union_members(
        &checker,
        value_type(&checker, value),
        &["object", "undefined"],
    );
    let bootstrap = checker.store().intrinsic_bootstrap().unwrap();
    let undefined = bootstrap.undefined_type;
    let object = bootstrap.non_primitive_type;
    let never = bootstrap.never_type;
    assert_eq!(
        assert_read(&mut checker, &parsed, "nonBreak", value, "undefined"),
        undefined
    );
    assert_eq!(
        assert_read(&mut checker, &parsed, "after", value, "object"),
        object
    );
    let call = only_node(&parsed, SyntaxKind::CallExpression);
    let signature = checker
        .store()
        .signature(effects_signature(&checker, call))
        .unwrap();
    assert_eq!(signature.resolved_return_type(), Some(never));
    assert_eq!(signature.resolved_type_predicate(), None);
    assert_eq!(checker.get_type_at_location(call), Ok(never));
    assert_recheck_stable(&mut checker, &parsed);
}

#[test]
fn for_call_effects_keep_aliases_properties_and_argument_diagnostics() {
    for (source, declaration_kind, assertion, missing) in [
        (
            concat!(
                "declare function act(): void;\n",
                "for (;;) { const call = act; call(); break; }\n",
            ),
            SyntaxKind::VariableDeclaration,
            false,
            false,
        ),
        (
            concat!(
                "declare const runner: { step(): void };\n",
                "for (;;) { runner.step(); break; }\n",
            ),
            SyntaxKind::MethodSignature,
            false,
            false,
        ),
        (
            concat!(
                "declare function assertString(value: unknown): asserts value is string;\n",
                "declare const untouched: unknown;\n",
                "for (;;) { assertString(); const inside: unknown = untouched; break; }\n",
                "const after: unknown = untouched;\n",
            ),
            SyntaxKind::FunctionDeclaration,
            true,
            true,
        ),
        (
            concat!(
                "declare function assertString(value: unknown): asserts value is string;\n",
                "declare const untouched: unknown;\n",
                "for (;;) { assertString('literal'); const inside: unknown = untouched; break; }\n",
                "const after: unknown = untouched;\n",
            ),
            SyntaxKind::FunctionDeclaration,
            true,
            false,
        ),
    ] {
        let parsed = parse_source_file(source);
        let mut checker = context(&parsed);
        checker.check_source_file(FILE).unwrap();
        let call = only_node(&parsed, SyntaxKind::CallExpression);
        let NodeData::CallExpression(data) = &parsed.arena.get(call.node).unwrap().data else {
            unreachable!()
        };
        let callee = NodeRef::new(parsed.arena.id(), FILE, data.expression);
        let owner = symbol(&checker, only_node(&parsed, declaration_kind));
        assert_eq!(checker.get_symbol_at_location(callee), Ok(Some(owner)));
        let void = checker.store().intrinsic_bootstrap().unwrap().void_type;
        assert_eq!(checker.get_type_at_location(call), Ok(void));
        if assertion {
            let signature = effects_signature(&checker, call);
            let predicate = checker
                .store()
                .signature(signature)
                .unwrap()
                .resolved_type_predicate()
                .and_then(|predicate| checker.store().type_predicate(predicate))
                .unwrap();
            assert_eq!(predicate.kind(), TypePredicateKind::AssertsIdentifier);
            let untouched = symbol(&checker, variable(&parsed, "untouched").declaration);
            let unknown = checker.store().intrinsic_bootstrap().unwrap().unknown_type;
            assert_eq!(value_type(&checker, untouched), unknown);
            for local in ["inside", "after"] {
                assert_eq!(
                    assert_read(&mut checker, &parsed, local, untouched, "unknown"),
                    unknown
                );
            }
        } else {
            assert_eq!(
                checker
                    .store()
                    .signature_links(call)
                    .unwrap()
                    .effects_signature,
                EffectsSignatureState::NoEffects
            );
        }
        if missing {
            assert_missing_argument(&checker, &parsed, callee);
        } else {
            assert!(
                checker.diagnostics().is_empty(),
                "{:?}",
                checker.diagnostics()
            );
        }
        assert_recheck_stable(&mut checker, &parsed);
    }
}
