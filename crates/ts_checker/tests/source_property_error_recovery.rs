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

const FILE: FileId = FileId::new(204_221);

fn context(parsed: &ParseResult) -> CanonicalCheckerContext<'_> {
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            FILE,
            CanonicalSourceFileFacts::new(
                EscapedName::source("\"/project/property-error-recovery.ts\""),
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

fn bound_symbol(checker: &CanonicalCheckerContext<'_>, node: NodeRef) -> SemanticSymbolId {
    let raw = checker.file(FILE).unwrap().1.symbol(node).unwrap();
    checker.store().get_merged_symbol(raw).unwrap()
}

#[derive(Clone, Copy)]
struct Property {
    access: NodeRef,
    receiver: NodeRef,
    name: NodeRef,
}

fn property(parsed: &ParseResult) -> Property {
    let node = |id| NodeRef::new(parsed.arena.id(), FILE, id);
    let mut found = parsed.arena.iter().filter_map(|(id, record)| {
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
    });
    let result = found.next().expect("expected the source property read");
    assert!(found.next().is_none());
    result
}

#[derive(Clone, Copy, Debug)]
enum Expected {
    MissingEquality,
    MissingArithmetic,
    PresentArithmetic,
}

fn check_diagnostic(
    checker: &CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    source: &str,
    property: Property,
    expected: Expected,
) {
    let actual = checker.diagnostics().as_slice();
    let [diagnostic] = actual else {
        panic!("expected one native diagnostic: {actual:?}");
    };
    let (code, node, text, arguments): (_, _, _, &[&str]) = match expected {
        Expected::MissingEquality | Expected::MissingArithmetic => (
            2339,
            property.name,
            "missing",
            &["missing", "{ value: number; }"],
        ),
        Expected::PresentArithmetic => (2362, property.access, "object.value", &[]),
    };
    assert_eq!(diagnostic.diagnostic.code(), code);
    assert_eq!(diagnostic.node, Some(node));
    let range = parsed.arena.get(node.node).unwrap().range;
    assert_eq!(
        &source[usize::try_from(range.start.get()).unwrap()
            ..usize::try_from(range.end.get()).unwrap()],
        text
    );
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

fn check_case(source: &str, expected: Expected) {
    let parsed = parse_source_file(source);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let property = property(&parsed);
    let (object, object_name, _) = variable(&parsed, "object");
    let (result, result_name, binary_node) = variable(&parsed, "bad");
    let NodeData::BinaryExpression(binary) = &parsed.arena.get(binary_node.node).unwrap().data
    else {
        panic!("expected the actual binary initializer");
    };

    for (query_mode, first) in [
        ("source-first", None),
        ("property-first", Some(property.access)),
        ("binary-first", Some(binary_node)),
    ] {
        let mut checker = context(&parsed);
        let bootstrap = checker.store().intrinsic_bootstrap().unwrap();
        let (read_type, result_type) = match expected {
            Expected::MissingEquality => (bootstrap.error_type, bootstrap.boolean_type),
            Expected::MissingArithmetic => (bootstrap.error_type, bootstrap.number_type),
            Expected::PresentArithmetic => (bootstrap.string_type, bootstrap.number_type),
        };
        assert_ne!(read_type, bootstrap.any_type);
        assert!(
            checker
                .store()
                .source_file_links(checker.source_file(FILE).unwrap())
                .is_none_or(|links| !links.type_checked)
        );
        if let Some(first) = first {
            let expected_type = if first == property.access {
                read_type
            } else {
                result_type
            };
            assert_eq!(
                checker.get_type_at_location(first),
                Ok(expected_type),
                "{expected:?}, {query_mode}"
            );
        }
        checker.check_source_file(FILE).unwrap_or_else(|error| {
            panic!("source check failed for {expected:?}, {query_mode}: {error:?}")
        });
        assert!(
            checker
                .store()
                .source_file_links(checker.source_file(FILE).unwrap())
                .unwrap()
                .type_checked
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
        let selected = checker.get_symbol_at_location(property.access).unwrap();
        match expected {
            Expected::MissingEquality | Expected::MissingArithmetic => assert_eq!(selected, None),
            Expected::PresentArithmetic => assert!(selected.is_some()),
        }
        assert_eq!(checker.get_symbol_at_location(property.name), Ok(selected));
        let object_symbol = bound_symbol(&checker, object);
        let result_symbol = bound_symbol(&checker, result);
        let artifacts = [
            (object_name, object_type, Some(object_symbol)),
            (property.receiver, object_type, Some(object_symbol)),
            (property.access, read_type, selected),
            (property.name, read_type, selected),
            (result_name, result_type, Some(result_symbol)),
            (binary_node, result_type, None),
        ];
        for &(node, type_, symbol) in &artifacts {
            assert_eq!(checker.get_type_at_location(node), Ok(type_));
            assert_eq!(checker.get_symbol_at_location(node), Ok(symbol));
        }
        let operands = [binary.left, binary.right].map(|id| {
            let node = NodeRef::new(parsed.arena.id(), FILE, id);
            let record = parsed.arena.get(id).unwrap();
            assert_eq!(record.parent, Some(binary_node.node));
            let type_ = checker.get_type_at_location(node).unwrap();
            match record.kind {
                SyntaxKind::PropertyAccessExpression | SyntaxKind::ParenthesizedExpression => {
                    assert_eq!(type_, read_type);
                }
                SyntaxKind::NumericLiteral => assert!(
                    checker
                        .store()
                        .type_payload(type_)
                        .unwrap()
                        .flags()
                        .contains(TypeFlags::NUMBER_LITERAL)
                ),
                _ => panic!("unexpected binary operand: {:?}", record.kind),
            }
            (node, type_)
        });
        check_diagnostic(&checker, &parsed, source, property, expected);
        let before = snapshot(&checker, &parsed);
        for _ in 0..2 {
            checker.check_source_file(FILE).unwrap();
            checker.recheck_source_file(FILE).unwrap();
            for &(node, type_, symbol) in artifacts.iter().rev() {
                assert_eq!(checker.get_type_at_location(node), Ok(type_));
                assert_eq!(checker.get_symbol_at_location(node), Ok(symbol));
            }
            for &(node, type_) in operands.iter().rev() {
                assert_eq!(checker.get_type_at_location(node), Ok(type_));
            }
            check_diagnostic(&checker, &parsed, source, property, expected);
            assert_eq!(snapshot(&checker, &parsed), before);
        }
    }
}

#[test]
fn missing_property_reads_keep_error_type_and_native_diagnostics_in_binary_operands() {
    for (source, expected) in [
        (
            "const object = { value: 1 }; const bad = object.missing === 1;",
            Expected::MissingEquality,
        ),
        (
            "const object = { value: 1 }; const bad = 1 === (object.missing);",
            Expected::MissingEquality,
        ),
        (
            "const object = { value: 1 }; const bad = object.missing - 1;",
            Expected::MissingArithmetic,
        ),
    ] {
        check_case(source, expected);
    }
}

#[test]
fn present_property_keeps_its_native_arithmetic_diagnostic_and_replay() {
    check_case(
        "const object = { value: \"win32\" }; const bad = object.value - 1;",
        Expected::PresentArithmetic,
    );
}
