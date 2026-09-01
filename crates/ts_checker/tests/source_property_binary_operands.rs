use ts_ast::{FileId, NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerDiagnostics, CanonicalCheckerOptions,
    IntrinsicBootstrapOptions, NodeLinks, SourceFileLinks, SymbolNodeLinks, TypeId, TypeNodeLinks,
    ValueSymbolLinks, types::TypeFlags,
};
use ts_parser::{ParseResult, parse_source_file};

const FILE: FileId = FileId::new(204_203);

// Nullable receiver unions still have a separate equality limit. The optional
// accesses here deliberately use nonnullable receivers and must not add undefined.

fn context(parsed: &ParseResult) -> CanonicalCheckerContext<'_> {
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            FILE,
            CanonicalSourceFileFacts::new(
                EscapedName::source("\"/project/property-binary-operands.ts\""),
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
                exact_optional_property_types: false,
            },
            no_implicit_any: true,
            strict_function_types: true,
            ..CanonicalCheckerOptions::default()
        },
    )
    .unwrap()
}

#[derive(Clone, Copy)]
enum Scalar {
    String,
    Number,
    Boolean,
    Error,
}

fn scalar(checker: &CanonicalCheckerContext<'_>, expected: Scalar) -> TypeId {
    let types = checker.store().intrinsic_bootstrap().unwrap();
    match expected {
        Scalar::String => types.string_type,
        Scalar::Number => types.number_type,
        Scalar::Boolean => types.boolean_type,
        Scalar::Error => types.error_type,
    }
}

fn variable(parsed: &ParseResult, expected: &str) -> (NodeRef, NodeRef, NodeRef) {
    let mut found = parsed.arena.iter().filter_map(|(id, record)| {
        let NodeData::VariableDeclaration(variable) = &record.data else {
            return None;
        };
        let NodeData::Identifier(name) = &parsed.arena.get(variable.name)?.data else {
            return None;
        };
        (name.text == expected).then(|| {
            let node = |id| NodeRef::new(parsed.arena.id(), FILE, id);
            (
                node(id),
                node(variable.name),
                node(variable.initializer.unwrap()),
            )
        })
    });
    let result = found.next().expect("expected the named source variable");
    assert!(found.next().is_none());
    result
}

fn symbol(checker: &CanonicalCheckerContext<'_>, declaration: NodeRef) -> SemanticSymbolId {
    let raw = checker.file(FILE).unwrap().1.symbol(declaration).unwrap();
    checker.store().get_merged_symbol(raw).unwrap()
}

fn text_at<'a>(source: &'a str, parsed: &ParseResult, node: NodeRef) -> &'a str {
    let range = parsed.arena.get(node.node).unwrap().range;
    &source[usize::try_from(range.start.get()).unwrap()..usize::try_from(range.end.get()).unwrap()]
}

#[derive(Clone, Copy)]
struct Property {
    access: NodeRef,
    receiver: NodeRef,
    name: NodeRef,
}

fn properties(parsed: &ParseResult) -> Vec<Property> {
    let node = |id| NodeRef::new(parsed.arena.id(), FILE, id);
    let mut result = parsed
        .arena
        .iter()
        .filter_map(|(id, record)| {
            let NodeData::PropertyAccessExpression(property) = &record.data else {
                return None;
            };
            assert_eq!(record.kind, SyntaxKind::PropertyAccessExpression);
            assert_eq!(
                parsed.arena.get(property.expression).unwrap().parent,
                Some(id)
            );
            assert_eq!(parsed.arena.get(property.name).unwrap().parent, Some(id));
            Some(Property {
                access: node(id),
                receiver: node(property.expression),
                name: node(property.name),
            })
        })
        .collect::<Vec<_>>();
    result.sort_by_key(|property| {
        parsed
            .arena
            .get(property.access.node)
            .unwrap()
            .range
            .start
            .get()
    });
    assert!(!result.is_empty());
    result
}

#[derive(Clone, Copy)]
enum ExpectedError {
    Missing,
    NoOverlap,
    Arithmetic,
}

fn diagnostics(
    checker: &CanonicalCheckerContext<'_>,
    source: &str,
    parsed: &ParseResult,
    property: Property,
    result: NodeRef,
    expected: Option<ExpectedError>,
) {
    let actual = checker.diagnostics().as_slice();
    let Some(expected) = expected else {
        assert!(actual.is_empty(), "unexpected diagnostics: {actual:?}");
        return;
    };
    let [diagnostic] = actual else {
        panic!("expected one native diagnostic: {actual:?}");
    };
    let (code, node, text, arguments): (_, _, _, &[&str]) = match expected {
        ExpectedError::Missing => (
            2339,
            property.name,
            "missing",
            &["missing", "{ value: number; }"],
        ),
        ExpectedError::NoOverlap => (2367, result, "object.value === 1", &["string", "number"]),
        ExpectedError::Arithmetic => (2362, property.access, "object.value", &[]),
    };
    assert_eq!(diagnostic.diagnostic.code(), code);
    assert_eq!(diagnostic.node, Some(node));
    assert_eq!(text_at(source, parsed, node), text);
    assert_eq!(
        diagnostic
            .diagnostic
            .arguments
            .iter()
            .map(String::as_str)
            .collect::<Vec<_>>(),
        arguments
    );
    assert!(diagnostic.diagnostic.details.is_empty());
    assert_eq!(diagnostic.range_override, None);
    assert!(diagnostic.related_information.is_empty());
}

#[derive(Debug, Eq, PartialEq)]
struct Snapshot {
    counts: [usize; 8],
    nodes: Vec<(
        NodeRef,
        Option<NodeLinks>,
        Option<TypeNodeLinks>,
        Option<SymbolNodeLinks>,
    )>,
    values: Vec<(SemanticSymbolId, Option<ValueSymbolLinks>)>,
    diagnostics: CanonicalCheckerDiagnostics,
    source: Option<SourceFileLinks>,
}

fn snapshot(checker: &CanonicalCheckerContext<'_>, parsed: &ParseResult) -> Snapshot {
    let store = checker.store();
    Snapshot {
        counts: [
            store.type_len(),
            store.type_alias_len(),
            store.symbol_len(),
            store.signature_len(),
            store.mapper_len(),
            store.index_info_len(),
            store.symbol_store().symbol_table_len(),
            store.type_resolution_len(),
        ],
        nodes: parsed
            .arena
            .iter()
            .map(|(id, _)| {
                let node = NodeRef::new(parsed.arena.id(), FILE, id);
                (
                    node,
                    store.node_links(node).cloned(),
                    store.type_node_links(node).cloned(),
                    store.symbol_node_links(node).cloned(),
                )
            })
            .collect(),
        values: store
            .symbol_store()
            .symbols()
            .map(|(symbol, _)| (symbol, store.value_symbol_links(symbol).cloned()))
            .collect(),
        diagnostics: checker.diagnostics().clone(),
        source: store
            .source_file_links(checker.source_file(FILE).unwrap())
            .cloned(),
    }
}

fn check_case(
    source: &str,
    results: &[(&str, Scalar)],
    property_type: Scalar,
    error: Option<ExpectedError>,
) {
    let parsed = parse_source_file(source);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let properties = properties(&parsed);
    let (object, object_name, _) = variable(&parsed, "object");
    let results = results
        .iter()
        .map(|&(name, type_)| (variable(&parsed, name), type_))
        .collect::<Vec<_>>();
    let mut members = parsed.arena.iter().filter_map(|(id, record)| {
        (record.kind == SyntaxKind::PropertyAssignment).then_some(NodeRef::new(
            parsed.arena.id(),
            FILE,
            id,
        ))
    });
    let member = members.next().unwrap();
    assert!(members.next().is_none());

    for first in [None, Some(properties[0].access), Some(results[0].0.2)] {
        let mut checker = context(&parsed);
        assert!(
            checker
                .store()
                .source_file_links(checker.source_file(FILE).unwrap())
                .is_none_or(|links| !links.type_checked)
        );
        if let Some(node) = first {
            let expected = scalar(
                &checker,
                if node == properties[0].access {
                    property_type
                } else {
                    results[0].1
                },
            );
            assert_eq!(checker.get_type_at_location(node), Ok(expected));
        }
        checker.check_source_file(FILE).unwrap();
        assert!(
            checker
                .store()
                .source_file_links(checker.source_file(FILE).unwrap())
                .unwrap()
                .type_checked
        );
        let object_symbol = symbol(&checker, object);
        let property_symbol = symbol(&checker, member);
        assert_ne!(property_symbol, object_symbol);
        assert_eq!(
            checker
                .store()
                .symbol(property_symbol)
                .unwrap()
                .value_declaration(),
            Some(member)
        );
        let object_type = checker.get_type_at_location(object_name).unwrap();
        assert!(
            checker
                .store()
                .type_payload(object_type)
                .unwrap()
                .flags()
                .contains(TypeFlags::OBJECT)
        );
        let read_type = scalar(&checker, property_type);
        let mut artifacts = vec![(object_name, object_type, Some(object_symbol))];
        for property in &properties {
            let resolved = if matches!(error, Some(ExpectedError::Missing)) {
                None
            } else {
                Some(property_symbol)
            };
            artifacts.extend([
                (property.receiver, object_type, Some(object_symbol)),
                (property.access, read_type, resolved),
                (property.name, read_type, resolved),
            ]);
        }
        for &((declaration, name, result), type_) in &results {
            let expected = scalar(&checker, type_);
            artifacts.extend([
                (name, expected, Some(symbol(&checker, declaration))),
                (result, expected, None),
            ]);
            let NodeData::BinaryExpression(binary) = &parsed.arena.get(result.node).unwrap().data
            else {
                panic!("expected the actual binary initializer");
            };
            for operand in [binary.left, binary.right] {
                let operand = NodeRef::new(parsed.arena.id(), FILE, operand);
                let record = parsed.arena.get(operand.node).unwrap();
                assert_eq!(record.parent, Some(result.node));
                let actual = checker.get_type_at_location(operand).unwrap();
                match record.kind {
                    SyntaxKind::PropertyAccessExpression | SyntaxKind::ParenthesizedExpression => {
                        assert_eq!(actual, read_type);
                    }
                    SyntaxKind::StringLiteral => assert!(
                        checker
                            .store()
                            .type_payload(actual)
                            .unwrap()
                            .flags()
                            .contains(TypeFlags::STRING_LITERAL)
                    ),
                    SyntaxKind::NumericLiteral => assert!(
                        checker
                            .store()
                            .type_payload(actual)
                            .unwrap()
                            .flags()
                            .contains(TypeFlags::NUMBER_LITERAL)
                    ),
                    _ => panic!("unexpected operand: {:?}", record.kind),
                }
            }
        }
        for &(node, type_, owner) in &artifacts {
            assert_eq!(checker.get_type_at_location(node), Ok(type_));
            assert_eq!(checker.get_symbol_at_location(node), Ok(owner));
        }
        diagnostics(
            &checker,
            source,
            &parsed,
            properties[0],
            results[0].0.2,
            error,
        );
        let before = snapshot(&checker, &parsed);
        for _ in 0..2 {
            checker.check_source_file(FILE).unwrap();
            checker.recheck_source_file(FILE).unwrap();
            for &(node, type_, owner) in artifacts.iter().rev() {
                assert_eq!(checker.get_type_at_location(node), Ok(type_));
                assert_eq!(checker.get_symbol_at_location(node), Ok(owner));
            }
            diagnostics(
                &checker,
                source,
                &parsed,
                properties[0],
                results[0].0.2,
                error,
            );
            assert_eq!(snapshot(&checker, &parsed), before);
        }
    }
}

#[test]
fn property_equality_keeps_real_symbols_in_both_orders_and_nonnullable_optional_reads() {
    check_case(
        concat!(
            "const object = { value: \"win32\" };\n",
            "const left = object.value === \"win32\";\n",
            "const right = \"win32\" === object.value;\n",
            "const optionalLeft = (object?.value) === \"win32\";\n",
            "const optionalRight = \"win32\" === (object?.value);\n",
        ),
        &[
            ("left", Scalar::Boolean),
            ("right", Scalar::Boolean),
            ("optionalLeft", Scalar::Boolean),
            ("optionalRight", Scalar::Boolean),
        ],
        Scalar::String,
        None,
    );
}

#[test]
fn numeric_property_operands_keep_number_arithmetic_and_nonnullable_optional_reads() {
    check_case(
        concat!(
            "const object = { value: 4 };\n",
            "const sum = object.value + 2;\n",
            "const product = 3 * (object?.value);\n",
        ),
        &[("sum", Scalar::Number), ("product", Scalar::Number)],
        Scalar::Number,
        None,
    );
}

#[test]
fn property_binary_errors_keep_native_nodes_types_and_replay_after_cold_queries() {
    for (source, result, property, error) in [
        (
            "const object = { value: 1 }; const bad = object.missing === 1;",
            Scalar::Boolean,
            Scalar::Error,
            ExpectedError::Missing,
        ),
        (
            "const object = { value: \"win32\" }; const bad = object.value === 1;",
            Scalar::Boolean,
            Scalar::String,
            ExpectedError::NoOverlap,
        ),
        (
            "const object = { value: \"win32\" }; const bad = object.value - 1;",
            Scalar::Number,
            Scalar::String,
            ExpectedError::Arithmetic,
        ),
    ] {
        check_case(source, &[("bad", result)], property, Some(error));
    }
}
