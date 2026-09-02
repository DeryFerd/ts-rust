use ts_ast::{FileId, NodeData, NodeId, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId,
};
use ts_checker::semantic::types::ObjectFlags;
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerDiagnostics, CanonicalCheckerOptions,
    IntrinsicBootstrapOptions, NodeLinks, SignatureLinks, SourceFileLinks, SymbolNodeLinks,
    TypeData, TypeId, TypeNodeLinks, ValueSymbolLinks,
};
use ts_diagnostics::Category;
use ts_parser::{ParseResult, parse_source_file};

const FILE: FileId = FileId::new(64_810);
const LIBRARY: FileId = FileId::new(64_811);
const ARRAY_LIBRARY: &str = concat!(
    "interface Array<T> { [n: number]: T; }\n",
    "interface ReadonlyArray<T> { readonly [n: number]: T; }\n",
);
const OPTIONAL_REST_SOURCE: &str = concat!(
    "declare function suite(label: string, body: () => void): void;\n",
    "declare function takeString(value: string): void;\n",
    "declare const cases: [string, boolean?, ...number[]][];\n",
    "for (const [name, flag, tail] of cases) { suite(name, () => { takeString(name); }); }\n",
);
const OVERFLOW_SOURCE: &str = concat!(
    "declare function suite(label: string, body: () => void): void;\n",
    "declare function strings(value: string[]): void;\n",
    "declare const pairs: [string, string[]][];\n",
    "for (const [name, rows, extra] of pairs) { suite(name, () => { strings(rows); }); }\n",
);

fn context<'a>(
    parsed: &'a ParseResult,
    library: &'a ParseResult,
    strict_null_checks: bool,
    no_unchecked_indexed_access: bool,
) -> CanonicalCheckerContext<'a> {
    let mut binder = CanonicalBinder::new();
    for (file, parsed, default_library, name) in [
        (LIBRARY, library, true, "\"/project/lib.d.ts\""),
        (FILE, parsed, false, "\"/project/tuple-binding-selection.ts\""),
    ] {
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new_with_default_library(
                    EscapedName::source(name),
                    CanonicalSourceLanguage::TypeScript,
                    default_library,
                    default_library,
                    CanonicalModuleState::Script,
                )
                .with_always_strict(true),
            )
            .unwrap();
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
    }
    CanonicalCheckerContext::new(
        binder.finish(),
        vec![(LIBRARY, &library.arena), (FILE, &parsed.arena)],
        CanonicalCheckerOptions {
            intrinsic: IntrinsicBootstrapOptions {
                strict_null_checks,
                exact_optional_property_types: false,
            },
            no_implicit_any: true,
            strict_function_types: true,
            no_unchecked_indexed_access,
            ..CanonicalCheckerOptions::default()
        },
    )
    .unwrap()
}

fn node(parsed: &ParseResult, id: NodeId) -> NodeRef {
    NodeRef::new(parsed.arena.id(), FILE, id)
}

struct CaseNodes {
    names: [NodeRef; 3],
    cold_read: NodeRef,
}

fn case_nodes(
    parsed: &ParseResult,
    source: &str,
    expected_names: [&str; 3],
    cold_call: (&str, &str),
) -> CaseNodes {
    let mut bindings = parsed
        .arena
        .iter()
        .filter_map(|(_, record)| {
            let NodeData::BindingElement(binding) = &record.data else {
                return None;
            };
            assert_eq!(record.kind, SyntaxKind::BindingElement);
            assert!(binding.initializer.is_none());
            assert!(binding.dot_dot_dot_token.is_none());
            let parent = parsed.arena.get(record.parent.unwrap()).unwrap();
            assert_eq!(parent.kind, SyntaxKind::ArrayBindingPattern);
            Some(node(parsed, binding.name.unwrap()))
        })
        .collect::<Vec<_>>();
    bindings.sort_by_key(|name| parsed.arena.get(name.node).unwrap().range.start);
    let names: [NodeRef; 3] = bindings.try_into().unwrap();
    for (name, expected) in names.iter().zip(expected_names) {
        let NodeData::Identifier(identifier) = &parsed.arena.get(name.node).unwrap().data else {
            panic!("expected the actual binding name");
        };
        assert_eq!(identifier.text, expected);
    }
    let (callee, name) = cold_call;
    let call = format!("{callee}({name})");
    let start = source.find(&call).unwrap() + callee.len() + 1;
    let cold_read = parsed
        .arena
        .iter()
        .find_map(|(id, record)| {
            let NodeData::Identifier(identifier) = &record.data else {
                return None;
            };
            (identifier.text == name
                && usize::try_from(record.range.start.get()).unwrap() == start)
                .then_some(node(parsed, id))
        })
        .unwrap();
    CaseNodes { names, cold_read }
}

fn binding_types(checker: &mut CanonicalCheckerContext<'_>, nodes: &CaseNodes) -> [TypeId; 3] {
    nodes.names.map(|name| {
        let type_ = checker.get_type_at_location(name).unwrap();
        let owner = checker.get_symbol_at_location(name).unwrap().unwrap();
        assert_eq!(
            checker.store().value_symbol_links(owner).unwrap().resolved_type,
            Some(type_),
        );
        type_
    })
}

fn assert_union(checker: &CanonicalCheckerContext<'_>, type_: TypeId, expected: &[TypeId]) {
    let TypeData::Union(union) = checker.store().type_payload(type_).unwrap().data() else {
        panic!("expected the selected tuple position to retain its union");
    };
    assert_eq!(union.union.types.len(), expected.len());
    for member in expected {
        assert!(union.union.types.contains(member));
    }
}

#[derive(Debug, Eq, PartialEq)]
struct NodeState {
    node: NodeRef,
    common: Option<NodeLinks>,
    type_: Option<TypeNodeLinks>,
    symbol: Option<SymbolNodeLinks>,
    signature: Option<SignatureLinks>,
}

#[derive(Debug, Eq, PartialEq)]
struct Publication {
    counts: [usize; 8],
    nodes: Vec<NodeState>,
    values: Vec<(SemanticSymbolId, Option<ValueSymbolLinks>)>,
    source: Option<SourceFileLinks>,
    diagnostics: CanonicalCheckerDiagnostics,
}

fn publication(checker: &CanonicalCheckerContext<'_>, parsed: &ParseResult) -> Publication {
    let store = checker.store();
    Publication {
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
                let node = node(parsed, id);
                NodeState {
                    node,
                    common: store.node_links(node).cloned(),
                    type_: store.type_node_links(node).cloned(),
                    symbol: store.symbol_node_links(node).cloned(),
                    signature: store.signature_links(node).cloned(),
                }
            })
            .collect(),
        values: store
            .symbol_store()
            .symbols()
            .map(|(symbol, _)| (symbol, store.value_symbol_links(symbol).cloned()))
            .collect(),
        source: store
            .source_file_links(checker.source_file(FILE).unwrap())
            .cloned(),
        diagnostics: checker.diagnostics().clone(),
    }
}

fn replay(
    checker: &mut CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    nodes: &CaseNodes,
    expected: [TypeId; 3],
    expected_cold: TypeId,
    expected_diagnostics: &CanonicalCheckerDiagnostics,
) {
    assert!(
        checker
            .store()
            .source_file_links(checker.source_file(FILE).unwrap())
            .is_some_and(|links| links.type_checked)
    );
    assert_eq!(checker.store().type_resolution_len(), 0);
    assert_eq!(checker.diagnostics(), expected_diagnostics);
    assert_eq!(checker.get_type_at_location(nodes.cold_read), Ok(expected_cold));
    assert_eq!(checker.diagnostics(), expected_diagnostics);
    let before = publication(checker, parsed);
    for _ in 0..2 {
        checker.check_source_file(FILE).unwrap();
        checker.recheck_source_file(FILE).unwrap();
        assert_eq!(binding_types(checker, nodes), expected);
        assert_eq!(checker.get_type_at_location(nodes.cold_read), Ok(expected_cold));
        assert_eq!(publication(checker, parsed), before);
    }
}

#[test]
fn source_tuple_binding_selection_preserves_optional_and_rest_slots() {
    let parsed = parse_source_file(OPTIONAL_REST_SOURCE);
    let library = parse_source_file(ARRAY_LIBRARY);
    let nodes = case_nodes(
        &parsed,
        OPTIONAL_REST_SOURCE,
        ["name", "flag", "tail"],
        ("takeString", "name"),
    );
    for (strict_null_checks, no_unchecked_indexed_access) in
        [(true, false), (true, true), (false, true)]
    {
        for query_first in [false, true] {
            let mut checker = context(
                &parsed,
                &library,
                strict_null_checks,
                no_unchecked_indexed_access,
            );
            let cold = query_first
                .then(|| checker.get_type_at_location(nodes.cold_read).unwrap());
            checker.check_source_file(FILE).unwrap();
            assert!(checker.diagnostics().is_empty(), "{:?}", checker.diagnostics());
            let expected_diagnostics = checker.diagnostics().clone();
            let actual = binding_types(&mut checker, &nodes);
            assert_eq!(checker.diagnostics(), &expected_diagnostics);
            let bootstrap = checker.store().intrinsic_bootstrap().unwrap();
            assert_eq!(actual[0], bootstrap.string_type);
            if strict_null_checks {
                assert_union(
                    &checker,
                    actual[1],
                    &[
                        bootstrap.regular_false_type,
                        bootstrap.regular_true_type,
                        bootstrap.undefined_type,
                    ],
                );
            } else {
                assert_eq!(actual[1], bootstrap.boolean_type);
            }
            if strict_null_checks && no_unchecked_indexed_access {
                assert_union(
                    &checker,
                    actual[2],
                    &[bootstrap.number_type, bootstrap.undefined_type],
                );
            } else {
                assert_eq!(actual[2], bootstrap.number_type);
            }
            if let Some(cold) = cold {
                assert_eq!(cold, actual[0]);
                assert_eq!(checker.get_type_at_location(nodes.cold_read), Ok(cold));
            }
            replay(
                &mut checker,
                &parsed,
                &nodes,
                actual,
                actual[0],
                &expected_diagnostics,
            );
        }
    }
}

#[test]
fn source_tuple_binding_selection_reports_fixed_tuple_overflow() {
    let parsed = parse_source_file(OVERFLOW_SOURCE);
    let library = parse_source_file(ARRAY_LIBRARY);
    let nodes = case_nodes(
        &parsed,
        OVERFLOW_SOURCE,
        ["name", "rows", "extra"],
        ("strings", "rows"),
    );
    for query_first in [false, true] {
        let mut checker = context(&parsed, &library, true, false);
        let error = checker.store().intrinsic_bootstrap().unwrap().error_type;
        assert!(
            !checker
                .store()
                .type_payload(error)
                .unwrap()
                .object_flags()
                .intersects(ObjectFlags::REQUIRES_WIDENING)
        );
        let cold = query_first.then(|| checker.get_type_at_location(nodes.cold_read).unwrap());
        checker.check_source_file(FILE).unwrap();
        let expected_diagnostics = checker.diagnostics().clone();
        let actual = binding_types(&mut checker, &nodes);
        assert_eq!(checker.diagnostics(), &expected_diagnostics);
        let string = checker.store().intrinsic_bootstrap().unwrap().string_type;
        assert_eq!(actual[0], string);
        assert_eq!(actual[2], error);
        let TypeData::TypeReference(rows) = checker.store().type_payload(actual[1]).unwrap().data()
        else {
            panic!("the valid tuple position must retain its array type");
        };
        assert_eq!(rows.object.target, Some(checker.global_types().array_type));
        assert_eq!(rows.resolved_type_arguments.as_deref(), Some(&[string][..]));
        let [diagnostic] = checker.diagnostics().as_slice() else {
            panic!("expected exactly the out-of-range tuple binding diagnostic");
        };
        assert_eq!(diagnostic.diagnostic.code(), 2493);
        assert_eq!(diagnostic.diagnostic.category(), Category::Error);
        assert_eq!(diagnostic.node, Some(nodes.names[2]));
        assert!(diagnostic.range_override.is_none());
        assert_eq!(
            diagnostic.diagnostic.arguments,
            ["[string, string[]]", "2", "2"],
        );
        assert!(diagnostic.diagnostic.details.is_empty());
        assert!(diagnostic.related_information.is_empty());
        let range = parsed.arena.get(nodes.names[2].node).unwrap().range;
        let expected_start = OVERFLOW_SOURCE.find("extra").unwrap();
        assert_eq!(usize::try_from(range.start.get()).unwrap(), expected_start);
        assert_eq!(usize::try_from(range.end.get()).unwrap(), expected_start + 5);
        if let Some(cold) = cold {
            assert_eq!(cold, actual[1]);
            assert_eq!(checker.get_type_at_location(nodes.cold_read), Ok(cold));
        }
        replay(
            &mut checker,
            &parsed,
            &nodes,
            actual,
            actual[1],
            &expected_diagnostics,
        );
    }
}
