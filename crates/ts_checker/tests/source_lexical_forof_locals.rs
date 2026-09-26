use ts_ast::{FileId, NodeData, NodeId, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId, SymbolFlags,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerDiagnostics, CanonicalCheckerOptions,
    IntrinsicBootstrapOptions, SymbolNodeLinks, TypeId, TypeNodeLinks, ValueSymbolLinks,
};
use ts_diagnostics::Category;
use ts_parser::{ParseResult, parse_source_file};

const FILE: FileId = FileId::new(61_480);
const LIBRARY: FileId = FileId::new(61_481);
const ES5: &str = include_str!("../../ts_bundled/libs/lib.es5.d.ts");

const VALID: &str = r#"declare const pairs: [name: string, count: number][];
for (const [name, count] of pairs) {
  const label: string = name;
  const size: number = count;
  const copy: string = label;
}
"#;

const INVALID: &str = r#"declare const pairs: [name: string, count: number][];
for (const [name, count] of pairs) {
  const label: string = name;
  const size: number = count;
  const copy: string = label;
  const bad: number = name;
}
const escaped = label;
"#;

fn context<'a>(parsed: &'a ParseResult, library: &'a ParseResult) -> CanonicalCheckerContext<'a> {
    let files = [
        (LIBRARY, library, "\"/lib.es5.d.ts\"", true),
        (FILE, parsed, "\"/project/lexical-forof-locals.ts\"", false),
    ];
    let mut binder = CanonicalBinder::new();
    for (file, parsed, path, is_library) in files {
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new_with_default_library(
                    EscapedName::source(path),
                    CanonicalSourceLanguage::TypeScript,
                    is_library,
                    is_library,
                    if is_library {
                        CanonicalModuleState::Script
                    } else {
                        CanonicalModuleState::External
                    },
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
        files
            .into_iter()
            .map(|(file, parsed, _, _)| (file, &parsed.arena))
            .collect(),
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

#[derive(Clone, Copy)]
struct Binding {
    declaration: NodeRef,
    name: NodeRef,
    initializer: Option<NodeRef>,
}

fn binding(parsed: &ParseResult, text: &str) -> Binding {
    let mut matches = parsed.arena.iter().filter_map(|(id, record)| {
        let (name, initializer) = match &record.data {
            NodeData::VariableDeclaration(variable) => (variable.name, variable.initializer),
            NodeData::BindingElement(element) => (element.name?, element.initializer),
            _ => return None,
        };
        let NodeData::Identifier(identifier) = &parsed.arena.get(name)?.data else {
            return None;
        };
        (identifier.text == text).then(|| Binding {
            declaration: node(parsed, id),
            name: node(parsed, name),
            initializer: initializer.map(|id| node(parsed, id)),
        })
    });
    let found = matches.next().expect("expected the named binding");
    assert!(
        matches.next().is_none(),
        "expected one binding named {text}"
    );
    found
}

type Query = (NodeRef, TypeId, SemanticSymbolId);

fn assert_reference(checker: &mut CanonicalCheckerContext<'_>, query: Query) {
    let (location, expected_type, expected_symbol) = query;
    assert_eq!(checker.get_type_at_location(location), Ok(expected_type));
    assert_eq!(
        checker.get_symbol_at_location(location),
        Ok(Some(expected_symbol))
    );
    assert_eq!(
        checker
            .store()
            .type_node_links(location)
            .and_then(|links| links.resolved_type),
        Some(expected_type)
    );
}

fn assert_binding(
    checker: &mut CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    binding: Binding,
    scope: NodeRef,
    expected: TypeId,
) -> SemanticSymbolId {
    let bound = checker.file(FILE).unwrap().1;
    let raw = bound.symbol(binding.declaration).unwrap();
    let owner = checker.store().get_merged_symbol(raw).unwrap();
    assert_eq!(
        bound.container(binding.declaration),
        Some(node(parsed, parsed.source_file))
    );
    assert_eq!(
        bound.block_scope_container(binding.declaration),
        Some(scope)
    );
    let locals = bound
        .locals(scope)
        .expect("the lexical scope owns this binding");
    let NodeData::Identifier(identifier) = &parsed.arena.get(binding.name.node).unwrap().data
    else {
        unreachable!();
    };
    assert_eq!(
        checker
            .store()
            .symbol_table(locals)
            .unwrap()
            .get_source(&identifier.text),
        Some(owner)
    );
    let symbol = checker.store().symbol(owner).unwrap();
    assert_eq!(symbol.flags(), SymbolFlags::BLOCK_SCOPED_VARIABLE);
    assert_eq!(symbol.declarations(), Some(&[binding.declaration][..]));
    assert_eq!(symbol.value_declaration(), Some(binding.declaration));
    assert_eq!(
        checker
            .store()
            .value_symbol_links(owner)
            .and_then(|links| links.resolved_type),
        Some(expected)
    );
    assert_reference(checker, (binding.name, expected, owner));
    owner
}

#[derive(Debug, Eq, PartialEq)]
struct Snapshot {
    counts: [usize; 8],
    nodes: Vec<(NodeRef, Option<TypeNodeLinks>, Option<SymbolNodeLinks>)>,
    values: Vec<(SemanticSymbolId, Option<ValueSymbolLinks>)>,
    diagnostics: CanonicalCheckerDiagnostics,
}

fn snapshot(checker: &CanonicalCheckerContext<'_>, queries: &[Query]) -> Snapshot {
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
        nodes: queries
            .iter()
            .map(|&(location, _, _)| {
                (
                    location,
                    store.type_node_links(location).cloned(),
                    store.symbol_node_links(location).cloned(),
                )
            })
            .collect(),
        values: queries
            .iter()
            .map(|&(_, _, owner)| (owner, store.value_symbol_links(owner).cloned()))
            .collect(),
        diagnostics: checker.diagnostics().clone(),
    }
}

fn assert_diagnostics(
    checker: &CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    source: &str,
    invalid: bool,
) {
    if !invalid {
        assert!(
            checker.diagnostics().is_empty(),
            "{:?}",
            checker.diagnostics()
        );
        return;
    }
    let bad = binding(parsed, "bad");
    let escaped = binding(parsed, "escaped").initializer.unwrap();
    for (location, start, length) in [
        (bad.name, source.find("bad: number").unwrap(), "bad".len()),
        (
            escaped,
            source.find("const escaped = label;").unwrap() + "const escaped = ".len(),
            "label".len(),
        ),
    ] {
        let range = parsed.arena.get(location.node).unwrap().range;
        assert_eq!(usize::try_from(range.start.get()).unwrap(), start);
        assert_eq!(usize::try_from(range.end.get()).unwrap(), start + length);
    }
    let expected = [
        (
            bad.name,
            2322,
            vec!["string", "number"],
            "Type 'string' is not assignable to type 'number'.",
        ),
        (escaped, 2304, vec!["label"], "Cannot find name 'label'."),
    ];
    let diagnostics = checker.diagnostics().as_slice();
    assert_eq!(diagnostics.len(), expected.len(), "{diagnostics:?}");
    for (actual, (location, code, arguments, message)) in diagnostics.iter().zip(expected) {
        assert_eq!(actual.node, Some(location));
        assert_eq!(actual.range_override, None);
        assert_eq!(actual.diagnostic.code(), code);
        assert_eq!(actual.diagnostic.category(), Category::Error);
        assert_eq!(actual.diagnostic.arguments, arguments);
        assert_eq!(actual.diagnostic.render().unwrap(), message);
        assert!(actual.diagnostic.details.is_empty());
        assert!(actual.related_information.is_empty());
    }
}

#[allow(clippy::too_many_lines)]
fn run(source: &str, invalid: bool) {
    let parsed = parse_source_file(source);
    let library = parse_source_file(ES5);
    let mut loops = parsed.arena.iter().filter_map(|(id, record)| {
        (record.kind == SyntaxKind::ForOfStatement).then_some(node(&parsed, id))
    });
    let iteration = loops.next().unwrap();
    assert!(loops.next().is_none());
    let NodeData::ForInOrOfStatement(loop_) = &parsed.arena.get(iteration.node).unwrap().data
    else {
        unreachable!();
    };
    let body = node(&parsed, loop_.statement);
    let name = binding(&parsed, "name");
    let count = binding(&parsed, "count");
    let label = binding(&parsed, "label");
    let size = binding(&parsed, "size");
    let copy = binding(&parsed, "copy");

    for cold in [false, true] {
        let mut checker = context(&parsed, &library);
        let early = cold.then(|| {
            checker
                .get_type_at_location(copy.initializer.unwrap())
                .unwrap()
        });
        checker.check_source_file(FILE).unwrap();
        assert_diagnostics(&checker, &parsed, source, invalid);
        let bootstrap = checker.store().intrinsic_bootstrap().unwrap();
        let string = bootstrap.string_type;
        let number = bootstrap.number_type;
        let name_owner = assert_binding(&mut checker, &parsed, name, iteration, string);
        let count_owner = assert_binding(&mut checker, &parsed, count, iteration, number);
        let label_owner = assert_binding(&mut checker, &parsed, label, body, string);
        let size_owner = assert_binding(&mut checker, &parsed, size, body, number);
        let copy_owner = assert_binding(&mut checker, &parsed, copy, body, string);
        let owners = [name_owner, count_owner, label_owner, size_owner, copy_owner];
        for (index, owner) in owners.iter().enumerate() {
            assert!(!owners[..index].contains(owner));
        }
        let mut queries = vec![
            (name.name, string, name_owner),
            (count.name, number, count_owner),
            (label.name, string, label_owner),
            (label.initializer.unwrap(), string, name_owner),
            (size.name, number, size_owner),
            (size.initializer.unwrap(), number, count_owner),
            (copy.name, string, copy_owner),
            (copy.initializer.unwrap(), string, label_owner),
        ];
        if invalid {
            let bad = binding(&parsed, "bad");
            let bad_owner = assert_binding(&mut checker, &parsed, bad, body, number);
            assert!(!owners.contains(&bad_owner));
            queries.extend([
                (bad.name, number, bad_owner),
                (bad.initializer.unwrap(), string, name_owner),
            ]);
            let escaped = binding(&parsed, "escaped").initializer.unwrap();
            let source = node(&parsed, parsed.source_file);
            let bound = checker.file(FILE).unwrap().1;
            assert_eq!(bound.block_scope_container(escaped), Some(source));
            assert!(
                checker
                    .store()
                    .symbol_table(bound.locals(source).unwrap())
                    .unwrap()
                    .get_source("label")
                    .is_none()
            );
        }
        for &query in &queries {
            assert_reference(&mut checker, query);
        }
        if let Some(early) = early {
            assert_eq!(early, string);
        }
        assert_diagnostics(&checker, &parsed, source, invalid);
        let before = snapshot(&checker, &queries);
        let relation = checker.store().relation_state_snapshot();
        let resolution_start = checker.store().type_resolution_start();
        for _ in 0..2 {
            checker.check_source_file(FILE).unwrap();
            checker.recheck_source_file(FILE).unwrap();
            for &query in &queries {
                assert_reference(&mut checker, query);
            }
            assert_diagnostics(&checker, &parsed, source, invalid);
            assert_eq!(snapshot(&checker, &queries), before);
            assert_eq!(checker.store().relation_state_snapshot(), relation);
            assert_eq!(checker.store().type_resolution_start(), resolution_start);
        }
    }
}

#[test]
fn source_lexical_forof_locals_keep_tuple_bindings_and_replay() {
    run(VALID, false);
}

#[test]
fn source_lexical_forof_locals_report_assignment_and_scope_errors() {
    run(INVALID, true);
}
