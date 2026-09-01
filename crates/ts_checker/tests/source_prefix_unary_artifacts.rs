use ts_ast::{FileId, NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalNameResolverOptions, CanonicalSourceFileFacts,
    CanonicalSourceLanguage, EscapedName,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, DeclaredTypeLinks, IntrinsicBootstrapOptions,
    NodeLinks, SignatureLinks, SourceFileLinks, SymbolNodeLinks, TypeData, TypeId, TypeNodeLinks,
    ValueSymbolLinks, type_records::LiteralValue,
};
use ts_jsnum::Number;
use ts_options::ScriptTarget;
use ts_parser::{ParseResult, parse_source_file};

const FILE: FileId = FileId::new(202_925);

fn context(parsed: &ParseResult) -> CanonicalCheckerContext<'_> {
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            FILE,
            CanonicalSourceFileFacts::new(
                EscapedName::source("\"/project/prefix-unary.ts\""),
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
                ..IntrinsicBootstrapOptions::default()
            },
            strict_bind_call_apply: true,
            strict_builtin_iterator_return: true,
            strict_function_types: true,
            strict_property_initialization: true,
            use_unknown_in_catch_variables: true,
            no_implicit_any: true,
            no_implicit_this: true,
            no_emit: true,
            name_resolution: CanonicalNameResolverOptions {
                emit_target: ScriptTarget::EsNext,
                ..CanonicalNameResolverOptions::default()
            },
            ..CanonicalCheckerOptions::default()
        },
    )
    .unwrap()
}

fn prefix_operand(parsed: &ParseResult, expression: NodeRef, operator: SyntaxKind) -> NodeRef {
    let NodeData::PrefixUnaryExpression(prefix) = &parsed.arena.get(expression.node).unwrap().data
    else {
        panic!("the source contains the written prefix expression")
    };
    assert_eq!(prefix.operator, operator);
    assert_eq!(
        parsed.arena.get(prefix.operand).unwrap().parent,
        Some(expression.node)
    );
    NodeRef::new(parsed.arena.id(), FILE, prefix.operand)
}

fn initializer(parsed: &ParseResult, expected: &str) -> NodeRef {
    parsed
        .arena
        .iter()
        .find_map(|(_, record)| {
            let NodeData::VariableDeclaration(variable) = &record.data else {
                return None;
            };
            matches!(&parsed.arena.get(variable.name)?.data,
            NodeData::Identifier(name) if name.text == expected)
            .then(|| NodeRef::new(parsed.arena.id(), FILE, variable.initializer.unwrap()))
        })
        .unwrap()
}

#[derive(Clone, Copy)]
enum Expected {
    Boolean(bool),
    Number(i32),
}

fn assert_expression(
    context: &mut CanonicalCheckerContext<'_>,
    node: NodeRef,
    expected: Expected,
) -> TypeId {
    let actual = context.get_type_at_location(node).unwrap();
    let bootstrap = context.store().intrinsic_bootstrap().unwrap();
    let (identity, display) = match expected {
        Expected::Boolean(value) => (
            if value {
                bootstrap.true_type
            } else {
                bootstrap.false_type
            },
            value.to_string(),
        ),
        Expected::Number(value) => {
            let number = Number::new(f64::from(value));
            let regular = bootstrap.cached_number_literal_type(number).unwrap();
            let TypeData::Literal(literal) = context.store().type_payload(regular).unwrap().data()
            else {
                panic!("the source evaluator interns the written number")
            };
            assert_eq!(literal.value, LiteralValue::Number(number));
            let fresh = literal.fresh_type.unwrap();
            assert_ne!(regular, fresh);
            (fresh, value.to_string())
        }
    };
    assert_eq!(actual, identity);
    assert_eq!(context.type_to_string(actual).unwrap(), display);
    assert_eq!(context.get_symbol_at_location(node), Ok(None));
    actual
}

#[derive(Debug, Eq, PartialEq)]
struct Snapshot {
    counts: [usize; 7],
    nodes: Vec<Option<NodeLinks>>,
    types: Vec<Option<TypeNodeLinks>>,
    symbols: Vec<Option<SymbolNodeLinks>>,
    signatures: Vec<Option<SignatureLinks>>,
    values: Vec<Option<ValueSymbolLinks>>,
    declared: Vec<Option<DeclaredTypeLinks>>,
    source: Option<SourceFileLinks>,
    diagnostics: usize,
}

fn snapshot(context: &CanonicalCheckerContext<'_>, parsed: &ParseResult) -> Snapshot {
    let store = context.store();
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
            store.index_info_len(),
            store.symbol_store().symbol_table_len(),
        ],
        nodes: nodes
            .iter()
            .map(|node| store.node_links(*node).cloned())
            .collect(),
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
        values: store
            .symbol_store()
            .symbols()
            .map(|(symbol, _)| store.value_symbol_links(symbol).cloned())
            .collect(),
        declared: store
            .symbol_store()
            .symbols()
            .map(|(symbol, _)| store.declared_type_links(symbol).cloned())
            .collect(),
        source: store
            .source_file_links(context.source_file(FILE).unwrap())
            .cloned(),
        diagnostics: context.diagnostics().len(),
    }
}

fn assert_query_orders(parsed: &ParseResult, queries: &[(NodeRef, Expected)]) {
    let (outer, Expected::Boolean(outer_value)) = queries[0] else {
        panic!("each control starts with its outer boolean expression")
    };
    for source_first in [false, true] {
        for reverse in [false, true] {
            let mut context = context(parsed);
            let mut queries = queries.to_vec();
            if reverse {
                queries.reverse();
            }
            if source_first {
                context.check_source_file(FILE).unwrap();
                let bootstrap = context.store().intrinsic_bootstrap().unwrap();
                assert_eq!(
                    context
                        .store()
                        .type_node_links(outer)
                        .and_then(|links| links.resolved_type),
                    Some(if outer_value {
                        bootstrap.true_type
                    } else {
                        bootstrap.false_type
                    }),
                );
            }
            let observed = queries
                .iter()
                .map(|&(node, expected)| assert_expression(&mut context, node, expected))
                .collect::<Vec<_>>();
            assert!(context.diagnostics().is_empty());
            assert!(
                context
                    .store()
                    .source_file_links(context.source_file(FILE).unwrap())
                    .unwrap()
                    .type_checked
            );
            let warm = snapshot(&context, parsed);
            for _ in 0..2 {
                for (&(node, expected), &identity) in queries.iter().zip(&observed).rev() {
                    assert_eq!(assert_expression(&mut context, node, expected), identity);
                }
                context.check_source_file(FILE).unwrap();
                context.recheck_source_file(FILE).unwrap();
                assert_eq!(snapshot(&context, parsed), warm);
            }
        }
    }
}

#[test]
fn checked_function_prefix_unary_artifacts_keep_exact_expression_types() {
    let parsed = parse_source_file(concat!(
        "function choose() { if (!!true) { return 1; } return 2; }\n",
        "const negative = -2;\n",
    ));
    let outer = parsed
        .arena
        .iter()
        .find_map(|(_, record)| {
            let NodeData::IfStatement(statement) = &record.data else {
                return None;
            };
            Some(NodeRef::new(parsed.arena.id(), FILE, statement.expression))
        })
        .unwrap();
    let inner = prefix_operand(&parsed, outer, SyntaxKind::ExclamationToken);
    let truth = prefix_operand(&parsed, inner, SyntaxKind::ExclamationToken);
    assert_eq!(
        parsed.arena.get(truth.node).unwrap().kind,
        SyntaxKind::TrueKeyword
    );
    let negative = initializer(&parsed, "negative");
    let positive = prefix_operand(&parsed, negative, SyntaxKind::MinusToken);
    assert_query_orders(
        &parsed,
        &[
            (outer, Expected::Boolean(true)),
            (inner, Expected::Boolean(false)),
            (truth, Expected::Boolean(true)),
            (negative, Expected::Number(-2)),
            (positive, Expected::Number(2)),
        ],
    );
}

#[test]
fn parenthesized_prefix_unary_artifacts_keep_operand_identity_on_replay() {
    let parsed = parse_source_file("const disabled = !(!false);");
    let outer = initializer(&parsed, "disabled");
    let parenthesized = prefix_operand(&parsed, outer, SyntaxKind::ExclamationToken);
    let NodeData::ParenthesizedExpression(parenthesized_data) =
        &parsed.arena.get(parenthesized.node).unwrap().data
    else {
        panic!("the source retains the parenthesized operand")
    };
    let inner = NodeRef::new(parsed.arena.id(), FILE, parenthesized_data.expression);
    assert_eq!(
        parsed.arena.get(inner.node).unwrap().parent,
        Some(parenthesized.node)
    );
    let falsity = prefix_operand(&parsed, inner, SyntaxKind::ExclamationToken);
    assert_eq!(
        parsed.arena.get(falsity.node).unwrap().kind,
        SyntaxKind::FalseKeyword
    );
    assert_query_orders(
        &parsed,
        &[
            (outer, Expected::Boolean(false)),
            (parenthesized, Expected::Boolean(true)),
            (inner, Expected::Boolean(true)),
            (falsity, Expected::Boolean(false)),
        ],
    );
}

#[derive(Clone, Copy, Debug)]
enum CheckedType {
    Boolean,
    True,
    False,
    String,
    Undefined,
    Object,
    Void,
    Never,
    Error,
    EmptyObject,
    StringOrUndefined,
    ObjectOrUndefined,
    EmptyObjectOrNull,
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
        panic!("expected one {kind:?}, found {nodes:?}")
    };
    *node
}

fn assert_checked_type(
    context: &mut CanonicalCheckerContext<'_>,
    node: NodeRef,
    expected: CheckedType,
) -> TypeId {
    let actual = context.get_type_at_location(node).unwrap();
    let bootstrap = context.store().intrinsic_bootstrap().unwrap();
    let (identity, display) = match expected {
        CheckedType::Boolean => (Some(bootstrap.boolean_type), "boolean"),
        CheckedType::True => (Some(bootstrap.true_type), "true"),
        CheckedType::False => (Some(bootstrap.false_type), "false"),
        CheckedType::String => (Some(bootstrap.string_type), "string"),
        CheckedType::Undefined => (Some(bootstrap.undefined_type), "undefined"),
        CheckedType::Object => (Some(bootstrap.non_primitive_type), "object"),
        CheckedType::Void => (Some(bootstrap.void_type), "void"),
        CheckedType::Never => (Some(bootstrap.never_type), "never"),
        CheckedType::Error => (Some(bootstrap.error_type), "any"),
        CheckedType::EmptyObject => (Some(bootstrap.empty_type_literal_type), "{}"),
        CheckedType::StringOrUndefined
        | CheckedType::ObjectOrUndefined
        | CheckedType::EmptyObjectOrNull => {
            let (present, absent, display) = match expected {
                CheckedType::StringOrUndefined => (
                    bootstrap.string_type,
                    bootstrap.undefined_type,
                    "string | undefined",
                ),
                CheckedType::ObjectOrUndefined => (
                    bootstrap.non_primitive_type,
                    bootstrap.undefined_type,
                    "object | undefined",
                ),
                CheckedType::EmptyObjectOrNull => (
                    bootstrap.empty_type_literal_type,
                    bootstrap.null_type,
                    "{} | null",
                ),
                _ => unreachable!(),
            };
            let TypeData::Union(union) = context.store().type_payload(actual).unwrap().data()
            else {
                panic!("expected the declared nullable union, got {actual:?}")
            };
            let mut constituents = [present, absent];
            constituents.sort_unstable();
            assert_eq!(union.union.types, constituents);
            (None, display)
        }
    };
    if let Some(identity) = identity {
        assert_eq!(actual, identity, "{node:?}: {expected:?}");
    }
    assert_eq!(context.type_to_string(actual).unwrap(), display);
    assert_eq!(
        context
            .store()
            .type_node_links(node)
            .and_then(|links| links.resolved_type),
        Some(actual),
    );
    actual
}

fn assert_checked_negation_queries(
    parsed: &ParseResult,
    queries: &[(NodeRef, CheckedType)],
    expected_diagnostics: &[(NodeRef, u32, &[&str], &str)],
) {
    let parameter = only_node(parsed, SyntaxKind::Parameter);
    for source_first in [false, true] {
        for reverse in [false, true] {
            let mut context = context(parsed);
            let parameter_symbol = context.file(FILE).unwrap().1.symbol(parameter).unwrap();
            let mut queries = queries.to_vec();
            if reverse {
                queries.reverse();
            }
            if source_first {
                context.check_source_file(FILE).unwrap();
            }
            let observed = queries
                .iter()
                .map(|&(node, expected)| {
                    let type_ = assert_checked_type(&mut context, node, expected);
                    let symbol = if let NodeData::Identifier(name) =
                        &parsed.arena.get(node.node).unwrap().data
                    {
                        assert_eq!(name.text, "value");
                        Some(parameter_symbol)
                    } else {
                        None
                    };
                    assert_eq!(context.get_symbol_at_location(node), Ok(symbol));
                    (type_, symbol)
                })
                .collect::<Vec<_>>();
            context.check_source_file(FILE).unwrap();
            let diagnostics = context.diagnostics().as_slice();
            assert_eq!(
                diagnostics.len(),
                expected_diagnostics.len(),
                "{diagnostics:?}"
            );
            for (diagnostic, &(node, code, arguments, message)) in
                diagnostics.iter().zip(expected_diagnostics)
            {
                assert_eq!(diagnostic.node, Some(node));
                assert_eq!(diagnostic.range_override, None);
                assert_eq!(diagnostic.diagnostic.code(), code);
                assert_eq!(diagnostic.diagnostic.arguments, arguments);
                assert_eq!(diagnostic.diagnostic.render().unwrap(), message);
                assert!(diagnostic.related_information.is_empty());
            }
            assert!(
                context
                    .store()
                    .source_file_links(context.source_file(FILE).unwrap())
                    .unwrap()
                    .type_checked
            );
            let diagnostics = diagnostics.to_vec();
            let warm = snapshot(&context, parsed);
            for _ in 0..2 {
                for (&(node, expected), &(type_, symbol)) in queries.iter().zip(&observed).rev() {
                    assert_eq!(assert_checked_type(&mut context, node, expected), type_);
                    assert_eq!(context.get_symbol_at_location(node), Ok(symbol));
                }
                context.check_source_file(FILE).unwrap();
                context.recheck_source_file(FILE).unwrap();
                assert_eq!(context.diagnostics().as_slice(), diagnostics);
                assert_eq!(snapshot(&context, parsed), warm);
            }
        }
    }
}

#[test]
fn ordinary_boolean_negation_checks_real_operands_and_exact_result_types() {
    for (source, result, operand) in [
        (
            "function absent(value: string | undefined): boolean { return !value; }",
            CheckedType::Boolean,
            CheckedType::StringOrUndefined,
        ),
        (
            "function present(value: object): false { return !value; }",
            CheckedType::False,
            CheckedType::Object,
        ),
        (
            "function absent(value: undefined): true { return !value; }",
            CheckedType::True,
            CheckedType::Undefined,
        ),
        (
            "function empty(value: {}): boolean { return !value; }",
            CheckedType::Boolean,
            CheckedType::EmptyObject,
        ),
        (
            "function empty(value: {} | null): boolean { return !value; }",
            CheckedType::Boolean,
            CheckedType::EmptyObjectOrNull,
        ),
    ] {
        let parsed = parse_source_file(source);
        let negation = only_node(&parsed, SyntaxKind::PrefixUnaryExpression);
        let value = prefix_operand(&parsed, negation, SyntaxKind::ExclamationToken);
        assert_checked_negation_queries(&parsed, &[(negation, result), (value, operand)], &[]);
    }

    let parsed = parse_source_file("function twice(value: boolean): boolean { return !!value; }");
    let returned = only_node(&parsed, SyntaxKind::ReturnStatement);
    let NodeData::ReturnStatement(statement) = &parsed.arena.get(returned.node).unwrap().data
    else {
        unreachable!()
    };
    let outer = NodeRef::new(parsed.arena.id(), FILE, statement.expression.unwrap());
    let inner = prefix_operand(&parsed, outer, SyntaxKind::ExclamationToken);
    let value = prefix_operand(&parsed, inner, SyntaxKind::ExclamationToken);
    assert_checked_negation_queries(
        &parsed,
        &[
            (outer, CheckedType::Boolean),
            (inner, CheckedType::Boolean),
            (value, CheckedType::Boolean),
        ],
        &[],
    );
}

#[test]
fn ordinary_boolean_negation_keeps_return_type_errors_and_replay() {
    let parsed =
        parse_source_file("function absent(value: string | undefined): number { return !value; }");
    let negation = only_node(&parsed, SyntaxKind::PrefixUnaryExpression);
    let value = prefix_operand(&parsed, negation, SyntaxKind::ExclamationToken);
    assert_checked_negation_queries(
        &parsed,
        &[
            (negation, CheckedType::Boolean),
            (value, CheckedType::StringOrUndefined),
        ],
        &[(
            only_node(&parsed, SyntaxKind::ReturnStatement),
            2322,
            &["boolean", "number"],
            "Type 'boolean' is not assignable to type 'number'.",
        )],
    );
}

#[test]
fn ordinary_boolean_negation_inverts_branch_facts_without_losing_empty_strings() {
    for (source, operand, when_true, when_false) in [
        (
            concat!(
                "function choose(value: object | undefined): object | undefined {\n",
                "  if (!value) { const thenValue: undefined = value; return thenValue; }\n",
                "  else { const elseValue: object = value; return elseValue; }\n",
                "}\n",
            ),
            CheckedType::ObjectOrUndefined,
            CheckedType::Undefined,
            CheckedType::Object,
        ),
        (
            concat!(
                "function choose(value: string | undefined): string | undefined {\n",
                "  if (!value) { const thenValue: string | undefined = value; return thenValue; }\n",
                "  else { const elseValue: string = value; return elseValue; }\n",
                "}\n",
            ),
            CheckedType::StringOrUndefined,
            CheckedType::StringOrUndefined,
            CheckedType::String,
        ),
    ] {
        let parsed = parse_source_file(source);
        let negation = only_node(&parsed, SyntaxKind::PrefixUnaryExpression);
        let value = prefix_operand(&parsed, negation, SyntaxKind::ExclamationToken);
        assert_checked_negation_queries(
            &parsed,
            &[
                (negation, CheckedType::Boolean),
                (value, operand),
                (initializer(&parsed, "thenValue"), when_true),
                (initializer(&parsed, "elseValue"), when_false),
            ],
            &[],
        );
    }
}

#[test]
fn ordinary_boolean_negation_keeps_operand_diagnostics_before_its_boolean_result() {
    let parsed = parse_source_file(
        "function invalid(value: { present: string }): boolean { return !value.missing; }",
    );
    let negation = only_node(&parsed, SyntaxKind::PrefixUnaryExpression);
    let access = prefix_operand(&parsed, negation, SyntaxKind::ExclamationToken);
    let NodeData::PropertyAccessExpression(property) = &parsed.arena.get(access.node).unwrap().data
    else {
        panic!("the negation must check the missing property read")
    };
    let name = NodeRef::new(parsed.arena.id(), FILE, property.name);
    assert_checked_negation_queries(
        &parsed,
        &[
            (negation, CheckedType::Boolean),
            (access, CheckedType::Error),
        ],
        &[(
            name,
            2339,
            &["missing", "{ present: string; }"],
            "Property 'missing' does not exist on type '{ present: string; }'.",
        )],
    );

    let parsed = parse_source_file("function invalid(value: void): true { return !value; }");
    let negation = only_node(&parsed, SyntaxKind::PrefixUnaryExpression);
    let value = prefix_operand(&parsed, negation, SyntaxKind::ExclamationToken);
    assert_checked_negation_queries(
        &parsed,
        &[(negation, CheckedType::True), (value, CheckedType::Void)],
        &[(
            value,
            1345,
            &[],
            "An expression of type 'void' cannot be tested for truthiness.",
        )],
    );
}

#[test]
fn ordinary_boolean_negation_combines_opposite_short_circuit_facts() {
    for (source, expected_operand, expected_negation) in [
        (
            concat!(
                "function choose(value: object | undefined): false | undefined {\n",
                "  const combined = (value && !value) && value;\n",
                "  return combined;\n",
                "}\n",
            ),
            CheckedType::Object,
            CheckedType::False,
        ),
        (
            concat!(
                "function choose(value: object | undefined): object | true {\n",
                "  const combined = (value || !value) || value;\n",
                "  return combined;\n",
                "}\n",
            ),
            CheckedType::Undefined,
            CheckedType::True,
        ),
    ] {
        let parsed = parse_source_file(source);
        let combined = initializer(&parsed, "combined");
        let NodeData::BinaryExpression(binary) = &parsed.arena.get(combined.node).unwrap().data
        else {
            panic!("the combined condition must keep both short-circuit operations")
        };
        let final_read = NodeRef::new(parsed.arena.id(), FILE, binary.right);
        let negation = only_node(&parsed, SyntaxKind::PrefixUnaryExpression);
        let operand = prefix_operand(&parsed, negation, SyntaxKind::ExclamationToken);
        assert_checked_negation_queries(
            &parsed,
            &[
                (negation, expected_negation),
                (operand, expected_operand),
                (final_read, CheckedType::Never),
            ],
            &[],
        );
    }
}
