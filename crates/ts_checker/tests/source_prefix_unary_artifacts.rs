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
