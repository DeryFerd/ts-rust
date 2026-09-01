use ts_ast::{FileId, NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, IntrinsicBootstrapOptions, TypeId,
};
use ts_diagnostics::Category;
use ts_parser::{ParseResult, parse_source_file};

const FILE: FileId = FileId::new(202_980);
const ES5_FILE: FileId = FileId::new(202_981);
const CORE_FILE: FileId = FileId::new(202_982);
const ES5: &str = include_str!("../../ts_bundled/libs/lib.es5.d.ts");
const ES2015_CORE: &str = include_str!("../../ts_bundled/libs/lib.es2015.core.d.ts");

const SOURCE: &str = r#"export function inspect(input: string): string {
  const first = input[0];
  if (
    first &&
    input[1] === ":" &&
    input[2] === "/" &&
    first >= "a" &&
    first <= "z"
  ) {
    const value: string = input;
  }
  return input;
}
"#;

fn context<'a>(
    parsed: &'a ParseResult,
    es5: &'a ParseResult,
    core: &'a ParseResult,
) -> CanonicalCheckerContext<'a> {
    let files = [
        (ES5_FILE, es5, "\"/lib/lib.es5.d.ts\""),
        (CORE_FILE, core, "\"/lib/lib.es2015.core.d.ts\""),
        (FILE, parsed, "\"/project/logical-indexed-conditions.ts\""),
    ];
    let mut binder = CanonicalBinder::new();
    for &(file, parsed, path) in &files {
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new_with_default_library(
                    EscapedName::source(path),
                    CanonicalSourceLanguage::TypeScript,
                    file != FILE,
                    file != FILE,
                    if file == FILE {
                        CanonicalModuleState::External
                    } else {
                        CanonicalModuleState::Script
                    },
                )
                .with_always_strict(true),
            )
            .unwrap();
    }
    for &(file, parsed, _) in &files {
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
            intrinsic: IntrinsicBootstrapOptions {
                strict_null_checks: true,
                exact_optional_property_types: false,
            },
            ..CanonicalCheckerOptions::default()
        },
    )
    .unwrap()
}

fn text<'a>(source: &'a str, parsed: &ParseResult, node: NodeRef) -> &'a str {
    assert_eq!(node.arena, parsed.arena.id());
    assert_eq!(node.file, FILE);
    let range = parsed.arena.get(node.node).unwrap().range;
    &source[usize::try_from(range.start.get()).unwrap()..usize::try_from(range.end.get()).unwrap()]
}

fn expression(parsed: &ParseResult, source: &str, kind: SyntaxKind, expected: &str) -> NodeRef {
    let matches = parsed
        .arena
        .iter()
        .filter_map(|(id, record)| {
            let node = NodeRef::new(parsed.arena.id(), FILE, id);
            (record.kind == kind && text(source, parsed, node) == expected).then_some(node)
        })
        .collect::<Vec<_>>();
    assert_eq!(matches.len(), 1, "expected one {expected:?}");
    matches[0]
}

struct Local {
    declaration: NodeRef,
    name: NodeRef,
    initializer: NodeRef,
    annotation: Option<NodeRef>,
}

fn local(parsed: &ParseResult, name: &str) -> Local {
    let matches = parsed
        .arena
        .iter()
        .filter_map(|(id, record)| {
            let NodeData::VariableDeclaration(data) = &record.data else {
                return None;
            };
            let NodeData::Identifier(identifier) = &parsed.arena.get(data.name)?.data else {
                return None;
            };
            (identifier.text == name).then(|| Local {
                declaration: NodeRef::new(parsed.arena.id(), FILE, id),
                name: NodeRef::new(parsed.arena.id(), FILE, data.name),
                initializer: NodeRef::new(parsed.arena.id(), FILE, data.initializer.unwrap()),
                annotation: data
                    .type_
                    .map(|id| NodeRef::new(parsed.arena.id(), FILE, id)),
            })
        })
        .collect::<Vec<_>>();
    assert_eq!(matches.len(), 1, "expected one local {name:?}");
    matches.into_iter().next().unwrap()
}

fn returned(parsed: &ParseResult) -> NodeRef {
    let expressions = parsed
        .arena
        .iter()
        .filter_map(|(_, record)| {
            let NodeData::ReturnStatement(data) = &record.data else {
                return None;
            };
            data.expression
                .map(|id| NodeRef::new(parsed.arena.id(), FILE, id))
        })
        .collect::<Vec<_>>();
    assert_eq!(expressions.len(), 1);
    expressions[0]
}

fn declared_type(checker: &mut CanonicalCheckerContext<'_>, local: &Local) -> TypeId {
    let raw = checker
        .file(FILE)
        .unwrap()
        .1
        .symbol(local.declaration)
        .unwrap();
    let symbol = checker.store().get_merged_symbol(raw).unwrap();
    assert_eq!(checker.get_symbol_at_location(local.name), Ok(Some(symbol)));
    checker
        .store()
        .value_symbol_links(symbol)
        .and_then(|links| links.resolved_type)
        .unwrap()
}

fn assert_diagnostics(
    checker: &CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    source: &str,
    target: NodeRef,
    invalid: bool,
) {
    if !invalid {
        assert!(checker.diagnostics().as_slice().is_empty());
        return;
    }
    let [diagnostic] = checker.diagnostics().as_slice() else {
        panic!("expected one diagnostic: {:?}", checker.diagnostics());
    };
    assert_eq!(diagnostic.diagnostic.code(), 2322);
    assert_eq!(diagnostic.diagnostic.category(), Category::Error);
    assert_eq!(diagnostic.node, Some(target));
    assert_eq!(text(source, parsed, target), "value");
    let start = source.find("value:").unwrap();
    let range = parsed.arena.get(target.node).unwrap().range;
    assert_eq!(usize::try_from(range.start.get()).unwrap(), start);
    assert_eq!(usize::try_from(range.end.get()).unwrap(), start + 5);
    let arguments: &[&str] = &["string", "number"];
    assert_eq!(diagnostic.diagnostic.arguments, arguments);
    assert!(diagnostic.diagnostic.details.is_empty());
    assert!(diagnostic.related_information.is_empty());
    assert!(diagnostic.range_override.is_none());
}

fn snapshot(
    checker: &CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
) -> impl PartialEq + std::fmt::Debug + use<> {
    let store = checker.store();
    (
        [
            store.type_len(),
            store.type_alias_len(),
            store.mapper_len(),
            store.signature_len(),
            store.symbol_len(),
            store.symbol_store().symbol_table_len(),
            store.index_info_len(),
            store.type_resolution_len(),
        ],
        parsed
            .arena
            .iter()
            .map(|(id, _)| {
                let node = NodeRef::new(parsed.arena.id(), FILE, id);
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
            .map(|(symbol, _)| (symbol, store.value_symbol_links(symbol).cloned()))
            .collect::<Vec<_>>(),
        store
            .source_file_links(checker.source_file(FILE).unwrap())
            .cloned(),
        store.relation_state_snapshot(),
        checker.file(FILE).unwrap().1.flow_graph().clone(),
        checker.diagnostics().clone(),
    )
}

fn replay(checker: &mut CanonicalCheckerContext<'_>, parsed: &ParseResult, queries: &[NodeRef]) {
    let types = queries
        .iter()
        .map(|&node| (node, checker.get_type_at_location(node).unwrap()))
        .collect::<Vec<_>>();
    let before = snapshot(checker, parsed);
    for _ in 0..2 {
        checker.check_source_file(FILE).unwrap();
        checker.recheck_source_file(FILE).unwrap();
        for &(node, type_) in &types {
            assert_eq!(checker.get_type_at_location(node), Ok(type_));
        }
        assert_eq!(snapshot(checker, parsed), before);
    }
}

#[test]
fn logical_indexed_conditions_keep_body_checking_and_replay() {
    let es5 = parse_source_file(ES5);
    let core = parse_source_file(ES2015_CORE);
    let invalid_source = SOURCE.replacen("value: string", "value: number", 1);
    assert_ne!(invalid_source, SOURCE);
    for (source, invalid) in [(SOURCE, false), (invalid_source.as_str(), true)] {
        let parsed = parse_source_file(source);
        let first = local(&parsed, "first");
        let value = local(&parsed, "value");
        let returned = returned(&parsed);
        let indexed = ["input[0]", "input[1]", "input[2]"].map(|expected| {
            expression(
                &parsed,
                source,
                SyntaxKind::ElementAccessExpression,
                expected,
            )
        });
        assert_eq!(first.initializer, indexed[0]);
        assert_ne!(indexed[1], indexed[2]);
        let comparisons = [
            "input[1] === \":\"",
            "input[2] === \"/\"",
            "first >= \"a\"",
            "first <= \"z\"",
        ]
        .map(|expected| expression(&parsed, source, SyntaxKind::BinaryExpression, expected));
        assert!(first.annotation.is_none());
        for query_first in [false, true] {
            let mut checker = context(&parsed, &es5, &core);
            let intrinsics = checker.store().intrinsic_bootstrap().unwrap();
            let (string, number, boolean) = (
                intrinsics.string_type,
                intrinsics.number_type,
                intrinsics.boolean_type,
            );
            assert!(
                !checker
                    .store()
                    .source_file_links(checker.source_file(FILE).unwrap())
                    .is_some_and(|links| links.type_checked)
            );
            let cold_type = query_first.then(|| checker.get_type_at_location(returned).unwrap());
            checker.check_source_file(FILE).unwrap();
            // Check body diagnostics before any additional type query can demand the body.
            assert_diagnostics(&checker, &parsed, source, value.name, invalid);
            if let Some(cold_type) = cold_type {
                assert_eq!(cold_type, string);
            }
            assert_eq!(checker.get_type_at_location(returned), Ok(string));
            assert_eq!(declared_type(&mut checker, &first), string);
            for node in indexed {
                assert_eq!(checker.get_type_at_location(node), Ok(string));
            }
            for node in comparisons {
                assert_eq!(checker.get_type_at_location(node), Ok(boolean));
            }
            let body_type = if invalid { number } else { string };
            assert_eq!(
                checker.get_type_from_type_node(value.annotation.unwrap()),
                Ok(body_type)
            );
            assert_eq!(declared_type(&mut checker, &value), body_type);
            assert_eq!(checker.get_type_at_location(value.name), Ok(body_type));
            assert_eq!(checker.get_type_at_location(value.initializer), Ok(string));
            assert_diagnostics(&checker, &parsed, source, value.name, invalid);
            let mut queries = vec![returned, first.name, value.name, value.initializer];
            queries.extend(indexed);
            queries.extend(comparisons);
            replay(&mut checker, &parsed, &queries);
        }
    }
}
