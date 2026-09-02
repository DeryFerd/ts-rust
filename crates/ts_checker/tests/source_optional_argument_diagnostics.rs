use ts_ast::{FileId, NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerDiagnostics, CanonicalCheckerOptions,
    CanonicalTypeMapperStore, IntrinsicBootstrapOptions, NodeLinks, RelationUnavailable,
    SignatureId, SourceFileLinks, SymbolNodeLinks, TypeData, TypeNodeLinks, ValueSymbolLinks,
    type_to_string,
    types::{ObjectFlags, TypeFlags},
};
use ts_diagnostics::Category;
use ts_parser::{ParseResult, parse_source_file};

const FILE: FileId = FileId::new(204_223);
const LIBRARY: FileId = FileId::new(204_224);
const ES5: &str = include_str!("../../ts_bundled/libs/lib.es5.d.ts");

fn context<'a>(parsed: &'a ParseResult, library: &'a ParseResult) -> CanonicalCheckerContext<'a> {
    let files = [
        (LIBRARY, library, "\"/lib/lib.es5.d.ts\""),
        (
            FILE,
            parsed,
            "\"/project/optional-argument-diagnostics.ts\"",
        ),
    ];
    let mut binder = CanonicalBinder::new();
    for (file, parsed, path) in files {
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new_with_default_library(
                    EscapedName::source(path),
                    CanonicalSourceLanguage::TypeScript,
                    file == LIBRARY,
                    file == LIBRARY,
                    if file == LIBRARY {
                        CanonicalModuleState::Script
                    } else {
                        CanonicalModuleState::External
                    },
                )
                .with_always_strict(true),
            )
            .unwrap();
    }
    for (file, parsed, _) in files {
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
    }
    CanonicalCheckerContext::new(
        binder.finish(),
        files
            .into_iter()
            .map(|(file, parsed, _)| (file, &parsed.arena))
            .collect(),
        CanonicalCheckerOptions {
            no_implicit_any: true,
            strict_function_types: true,
            no_unchecked_indexed_access: true,
            intrinsic: IntrinsicBootstrapOptions {
                strict_null_checks: true,
                exact_optional_property_types: false,
            },
            ..CanonicalCheckerOptions::default()
        },
    )
    .unwrap()
}

fn only(parsed: &ParseResult, kind: SyntaxKind) -> NodeRef {
    let mut found = parsed.arena.iter().filter_map(|(id, node)| {
        (node.kind == kind).then_some(NodeRef::new(parsed.arena.id(), FILE, id))
    });
    let node = found.next().expect("expected the actual source node");
    assert!(found.next().is_none());
    node
}

fn signature(checker: &CanonicalCheckerContext<'_>, call: NodeRef) -> SignatureId {
    checker
        .store()
        .signature_links(call)
        .unwrap()
        .resolved_signature
        .signature()
        .unwrap()
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

fn check_case(source: &str, raw_argument: &str, raw_parameter: &str, display: [&str; 2]) {
    let parsed = parse_source_file(source);
    let library = parse_source_file(ES5);
    let call = only(&parsed, SyntaxKind::CallExpression);
    let function = only(&parsed, SyntaxKind::FunctionDeclaration);
    let parameter = only(&parsed, SyntaxKind::Parameter);
    let node = |id| NodeRef::new(parsed.arena.id(), FILE, id);
    let NodeData::CallExpression(call_data) = &parsed.arena.get(call.node).unwrap().data else {
        unreachable!()
    };
    let [argument] = call_data.arguments.nodes.as_slice() else {
        panic!("expected one supplied argument")
    };
    let argument = node(*argument);
    assert_eq!(
        parsed.arena.get(argument.node).unwrap().parent,
        Some(call.node)
    );
    let NodeData::ParameterDeclaration(parameter_data) =
        &parsed.arena.get(parameter.node).unwrap().data
    else {
        unreachable!()
    };
    assert_eq!(
        parsed.arena.get(parameter.node).unwrap().parent,
        Some(function.node)
    );
    let parameter_name = node(parameter_data.name);

    for (query_mode, first) in [
        ("source-first", None),
        ("argument-first", Some(argument)),
        ("call-first", Some(call)),
    ] {
        let mut checker = context(&parsed, &library);
        assert!(checker.global_types().diagnostics().is_empty());
        assert!(
            checker
                .store()
                .source_file_links(checker.source_file(FILE).unwrap())
                .is_none_or(|links| !links.type_checked)
        );
        let cold =
            first.map(|location| (location, checker.get_type_at_location(location).unwrap()));
        checker
            .check_source_file(FILE)
            .unwrap_or_else(|error| panic!("source check failed in {query_mode}: {error:?}"));
        let argument_type = checker.get_type_at_location(argument).unwrap();
        let parameter_type = checker.get_type_at_location(parameter_name).unwrap();
        assert_eq!(
            type_to_string(checker.store(), argument_type).unwrap(),
            raw_argument
        );
        assert_eq!(
            type_to_string(checker.store(), parameter_type).unwrap(),
            raw_parameter
        );
        let bootstrap = checker.store().intrinsic_bootstrap().unwrap();
        let number = bootstrap.number_type;
        let undefined = bootstrap.undefined_type;
        assert_ne!(argument_type, bootstrap.any_type);
        assert_ne!(parameter_type, bootstrap.any_type);
        if raw_argument == "1" {
            assert_ne!(argument_type, number);
            assert!(
                checker
                    .store()
                    .type_payload(argument_type)
                    .unwrap()
                    .flags()
                    .contains(TypeFlags::NUMBER_LITERAL)
            );
        }
        let target = checker.store().type_payload(parameter_type).unwrap();
        let TypeData::Union(union) = target.data() else {
            panic!("the stored parameter must retain its nullable union")
        };
        assert_eq!(union.union.types.len(), 2);
        assert!(union.union.types.contains(&undefined));
        if raw_parameter == "Text" {
            assert!(target.alias().is_some());
        }
        let selected = signature(&checker, call);
        let parameter_symbol = checker.file(FILE).unwrap().1.symbol(parameter).unwrap();
        let parameter_symbol = checker.store().get_merged_symbol(parameter_symbol).unwrap();
        let record = checker.store().signature(selected).unwrap();
        assert_eq!(record.declaration(), Some(function));
        assert_eq!(record.parameters(), [parameter_symbol]);
        assert_eq!(
            record.min_argument_count(),
            i32::from(parameter_data.question_token.is_none())
        );
        assert_eq!(checker.get_return_type_of_signature(selected), Ok(number));
        assert_eq!(checker.get_type_at_location(call), Ok(number));
        if let Some((location, type_)) = cold {
            assert_eq!(checker.get_type_at_location(location), Ok(type_));
        }
        let [diagnostic] = checker.diagnostics().as_slice() else {
            panic!("expected exactly one native argument diagnostic")
        };
        assert_eq!(diagnostic.diagnostic.code(), 2345);
        assert_eq!(diagnostic.diagnostic.category(), Category::Error);
        assert_eq!(diagnostic.node, Some(argument));
        assert_eq!(diagnostic.diagnostic.arguments, display);
        let expected_message = format!(
            "Argument of type '{}' is not assignable to parameter of type '{}'.",
            display[0], display[1]
        );
        let rendered = diagnostic.diagnostic.render().unwrap();
        assert_eq!(rendered.lines().next(), Some(expected_message.as_str()));
        assert!(diagnostic.range_override.is_none());
        assert!(diagnostic.related_information.is_empty());
        if raw_argument == "1" {
            assert!(diagnostic.diagnostic.details.is_empty());
            assert_eq!(rendered, expected_message);
        }
        let before = snapshot(&checker, &parsed);
        for _ in 0..2 {
            checker.check_source_file(FILE).unwrap();
            checker.recheck_source_file(FILE).unwrap();
            assert_eq!(checker.get_type_at_location(argument), Ok(argument_type));
            assert_eq!(
                checker.get_type_at_location(parameter_name),
                Ok(parameter_type)
            );
            assert_eq!(checker.get_type_at_location(call), Ok(number));
            assert_eq!(signature(&checker, call), selected);
            assert_eq!(
                checker.store().signature(selected).unwrap().parameters(),
                [parameter_symbol]
            );
            assert_eq!(snapshot(&checker, &parsed), before);
        }
    }
}

#[test]
fn optional_argument_display_preserves_literal_and_parameter_types() {
    check_case(
        "export {}; declare function take(value?: string): number; const result = take(1);",
        "1",
        "string | undefined",
        ["number", "string"],
    );
    check_case(
        "export {}; declare function take(value?: \"ready\"): number; const result = take(1);",
        "1",
        "\"ready\" | undefined",
        ["1", "\"ready\""],
    );
}

#[test]
fn argument_display_retains_named_and_nullable_types() {
    check_case(
        "export {}; type Text = string | undefined; declare function take(value: Text): number; const result = take(1);",
        "1",
        "Text",
        ["1", "Text"],
    );
    check_case(
        "export {}; declare const value: number | null; declare function take(input?: string): number; const result = take(value);",
        "number | null",
        "string | undefined",
        ["number | null", "string | undefined"],
    );
}

#[test]
fn malformed_nullable_target_keeps_its_typed_relation_error() {
    let mut store = CanonicalTypeMapperStore::new();
    let bootstrap = store
        .initialize_intrinsic_bootstrap(IntrinsicBootstrapOptions {
            strict_null_checks: true,
            exact_optional_property_types: false,
        })
        .unwrap();
    let (number, string, undefined) = (
        bootstrap.number_type,
        bootstrap.string_type,
        bootstrap.undefined_type,
    );
    let malformed = store
        .alloc_union_type(ObjectFlags::NONE, vec![undefined, undefined, string])
        .unwrap();
    let before = (
        store.type_len(),
        store.mapper_len(),
        store.signature_len(),
        store.relation_state_snapshot(),
    );
    for _ in 0..2 {
        assert_eq!(
            store.is_type_assignable_to(number, malformed),
            Err(RelationUnavailable::MalformedUnion(malformed))
        );
        assert_eq!(
            (
                store.type_len(),
                store.mapper_len(),
                store.signature_len(),
                store.relation_state_snapshot()
            ),
            before
        );
    }
}
