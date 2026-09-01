use ts_ast::{FileId, FlowFlags, FlowNodePayload, NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId, SymbolFlags,
};
use ts_checker::semantic::{
    CanonicalArtifactQueryError, CanonicalCheckerContext, CanonicalCheckerDiagnostics,
    CanonicalCheckerOptions, IntrinsicBootstrapOptions, NodeLinks, SignatureLinks,
    SourceCheckError, SourceFileLinks, SymbolNodeLinks, TypeData, TypeId, TypeNodeLinks,
    ValueSymbolLinks,
};
use ts_parser::{ParseResult, parse_source_file};

const FILE: FileId = FileId::new(63_710);
const LIBRARY: FileId = FileId::new(63_711);
const ARRAY_LIBRARY: &str = concat!(
    "interface Array<T> { [n: number]: T; }\n",
    "interface ReadonlyArray<T> { readonly [n: number]: T; }\n",
);
const PAIR_SOURCE: &str = concat!(
    "declare function suite(label: string, body: () => void): void;\n",
    "declare function strings(value: string[]): void;\n",
    "declare function numbers(value: number[]): void;\n",
    "declare const first: [name: string, rows: string[]][];\n",
    "declare const second: [name: string, rows: number[]][];\n",
    "for (const [name, rows] of first) { suite(name, () => { strings(rows); }); }\n",
    "for (const [name, rows] of second) { suite(name, () => { numbers(rows); }); }\n",
);

fn context<'a>(
    parsed: &'a ParseResult,
    library: &'a ParseResult,
    no_unused_locals: bool,
) -> CanonicalCheckerContext<'a> {
    let mut binder = CanonicalBinder::new();
    for (file, parsed, default_library, name) in [
        (LIBRARY, library, true, "\"/project/lib.d.ts\""),
        (
            FILE,
            parsed,
            false,
            "\"/project/source-flat-array-for-of.ts\"",
        ),
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
                strict_null_checks: true,
                exact_optional_property_types: false,
            },
            no_implicit_any: true,
            strict_function_types: true,
            no_unused_locals,
            ..CanonicalCheckerOptions::default()
        },
    )
    .unwrap()
}

fn node(parsed: &ParseResult, id: ts_ast::NodeId) -> NodeRef {
    NodeRef::new(parsed.arena.id(), FILE, id)
}

#[derive(Clone, Copy)]
struct Binding {
    declaration: NodeRef,
    name: NodeRef,
}

struct Loop {
    statement: NodeRef,
    body: NodeRef,
    bindings: Vec<Binding>,
    callee: NodeRef,
    callback: NodeRef,
}

fn loops(parsed: &ParseResult) -> Vec<Loop> {
    let mut result = parsed
        .arena
        .iter()
        .filter_map(|(id, record)| {
            if record.kind != SyntaxKind::ForOfStatement {
                return None;
            }
            let NodeData::ForInOrOfStatement(statement) = &record.data else {
                unreachable!()
            };
            let NodeData::VariableDeclarationList(list) =
                &parsed.arena.get(statement.initializer).unwrap().data
            else {
                panic!("expected the real lexical declaration list")
            };
            let [declaration] = list.declarations.nodes.as_slice() else {
                panic!("expected one pattern declaration")
            };
            let NodeData::VariableDeclaration(variable) =
                &parsed.arena.get(*declaration).unwrap().data
            else {
                unreachable!()
            };
            assert!(variable.type_.is_none());
            assert!(variable.initializer.is_none());
            let pattern = parsed.arena.get(variable.name).unwrap();
            assert_eq!(pattern.kind, SyntaxKind::ArrayBindingPattern);
            let NodeData::BindingPattern(pattern) = &pattern.data else {
                unreachable!()
            };
            let bindings = pattern
                .elements
                .nodes
                .iter()
                .map(|&id| {
                    let NodeData::BindingElement(binding) = &parsed.arena.get(id).unwrap().data
                    else {
                        panic!("expected an actual BindingElement")
                    };
                    assert!(binding.dot_dot_dot_token.is_none());
                    assert!(binding.initializer.is_none());
                    Binding {
                        declaration: node(parsed, id),
                        name: node(parsed, binding.name.unwrap()),
                    }
                })
                .collect();
            let NodeData::Block(body) = &parsed.arena.get(statement.statement).unwrap().data else {
                panic!("expected the actual source loop block")
            };
            let NodeData::ExpressionStatement(expression) =
                &parsed.arena.get(body.statements.nodes[0]).unwrap().data
            else {
                panic!("expected the real two-argument body call")
            };
            let NodeData::CallExpression(call) =
                &parsed.arena.get(expression.expression).unwrap().data
            else {
                unreachable!()
            };
            assert_eq!(call.arguments.nodes.len(), 2);
            Some(Loop {
                statement: node(parsed, id),
                body: node(parsed, statement.statement),
                bindings,
                callee: node(parsed, call.expression),
                callback: node(parsed, call.arguments.nodes[1]),
            })
        })
        .collect::<Vec<_>>();
    result.sort_by_key(|loop_| parsed.arena.get(loop_.statement.node).unwrap().range.start);
    result
}

fn reads(parsed: &ParseResult, body: NodeRef, name: &str) -> Vec<NodeRef> {
    let range = parsed.arena.get(body.node).unwrap().range;
    parsed
        .arena
        .iter()
        .filter_map(|(id, record)| {
            let NodeData::Identifier(identifier) = &record.data else {
                return None;
            };
            (identifier.text == name
                && range.start <= record.range.start
                && record.range.end <= range.end)
                .then_some(node(parsed, id))
        })
        .collect()
}

fn symbol(checker: &CanonicalCheckerContext<'_>, declaration: NodeRef) -> SemanticSymbolId {
    let raw = checker.file(FILE).unwrap().1.symbol(declaration).unwrap();
    checker.store().get_merged_symbol(raw).unwrap()
}

fn value_type(checker: &CanonicalCheckerContext<'_>, symbol: SemanticSymbolId) -> TypeId {
    checker
        .store()
        .value_symbol_links(symbol)
        .and_then(|links| links.resolved_type)
        .expect("the checked binding must retain its type")
}

fn array_element(checker: &CanonicalCheckerContext<'_>, type_: TypeId) -> TypeId {
    let TypeData::TypeReference(array) = checker.store().type_payload(type_).unwrap().data() else {
        panic!("expected a real array reference")
    };
    assert_eq!(array.object.target, Some(checker.global_types().array_type));
    let [element] = array.resolved_type_arguments.as_deref().unwrap() else {
        panic!("expected one array element type")
    };
    *element
}

#[allow(clippy::too_many_lines)] // Check binding ownership, assignment order, and capture together.
fn assert_loop(
    checker: &mut CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    loop_: &Loop,
    row_element: TypeId,
) -> (Vec<SemanticSymbolId>, Vec<NodeRef>) {
    assert_eq!(loop_.bindings.len(), 2);
    let source = node(parsed, parsed.source_file);
    let string = checker.store().intrinsic_bootstrap().unwrap().string_type;
    let void = checker.store().intrinsic_bootstrap().unwrap().void_type;
    let owners = loop_
        .bindings
        .iter()
        .map(|binding| symbol(checker, binding.declaration))
        .collect::<Vec<_>>();
    assert_ne!(owners[0], owners[1]);
    let rows = value_type(checker, owners[1]);
    assert_eq!(array_element(checker, rows), row_element);
    let mut queries = Vec::new();
    for ((binding, owner), expected) in loop_.bindings.iter().zip(&owners).zip([string, rows]) {
        let (_, bound) = checker.file(FILE).unwrap();
        assert_eq!(bound.container(binding.declaration), Some(source));
        assert_eq!(
            bound.block_scope_container(binding.declaration),
            Some(loop_.statement)
        );
        let NodeData::Identifier(name) = &parsed.arena.get(binding.name.node).unwrap().data else {
            unreachable!()
        };
        let locals = bound.locals(loop_.statement).unwrap();
        assert_eq!(
            checker
                .store()
                .symbol_table(locals)
                .unwrap()
                .get_source(&name.text),
            Some(*owner)
        );
        let declaration = checker.store().symbol(*owner).unwrap();
        assert_eq!(declaration.flags(), SymbolFlags::BLOCK_SCOPED_VARIABLE);
        assert_eq!(declaration.declarations(), Some(&[binding.declaration][..]));
        assert_eq!(declaration.value_declaration(), Some(binding.declaration));
        assert_eq!(value_type(checker, *owner), expected);
        for read in std::iter::once(binding.name).chain(reads(parsed, loop_.body, &name.text)) {
            assert_eq!(checker.get_type_at_location(read), Ok(expected));
            assert_eq!(checker.get_symbol_at_location(read), Ok(Some(*owner)));
            queries.push(read);
        }
    }

    let NodeData::ArrowFunction(arrow) = &parsed.arena.get(loop_.callback.node).unwrap().data
    else {
        panic!("the callback must remain its own arrow")
    };
    let callback_owner = symbol(checker, loop_.callback);
    assert!(!owners.contains(&callback_owner));
    let owner = checker.store().symbol(callback_owner).unwrap();
    assert_eq!(owner.flags(), SymbolFlags::FUNCTION);
    assert_eq!(owner.declarations(), Some(&[loop_.callback][..]));
    assert_eq!(owner.value_declaration(), Some(loop_.callback));
    let signature = checker
        .store()
        .signature_links(loop_.callback)
        .and_then(|links| links.resolved_signature.signature())
        .expect("the callback must retain a source signature");
    let signature = checker.store().signature(signature).unwrap();
    assert_eq!(signature.declaration(), Some(loop_.callback));
    assert!(signature.parameters().is_empty());
    assert_eq!(signature.resolved_return_type(), Some(void));
    let (_, bound) = checker.file(FILE).unwrap();
    assert_eq!(
        bound.container(node(parsed, arrow.body)),
        Some(loop_.callback)
    );
    assert_eq!(
        bound.flow_graph().container_is_complete(loop_.callback),
        Some(true)
    );
    for read in reads(parsed, node(parsed, arrow.body), "rows") {
        assert_eq!(bound.flow_container(read), Some(loop_.callback));
    }

    let graph = bound.flow_graph();
    let mut flow = bound.flow_at(loop_.callee).unwrap();
    for binding in loop_.bindings.iter().rev() {
        let assignment = graph.nodes().get(flow).unwrap();
        assert!(assignment.flags.contains(FlowFlags::ASSIGNMENT));
        assert_eq!(
            assignment.payload,
            Some(FlowNodePayload::Ast(binding.declaration))
        );
        flow = assignment.antecedent.unwrap();
    }
    assert!(
        graph
            .nodes()
            .get(flow)
            .unwrap()
            .flags
            .contains(FlowFlags::LOOP_LABEL)
    );
    assert_eq!(bound.flow_container(loop_.callee), Some(source));
    queries.push(loop_.callback);
    (owners, queries)
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
struct Snapshot {
    counts: [usize; 8],
    nodes: Vec<NodeState>,
    values: Vec<(SemanticSymbolId, Option<ValueSymbolLinks>)>,
    source: Option<SourceFileLinks>,
    diagnostics: CanonicalCheckerDiagnostics,
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

fn replay(checker: &mut CanonicalCheckerContext<'_>, parsed: &ParseResult, queries: &[NodeRef]) {
    assert!(
        checker
            .store()
            .source_file_links(checker.source_file(FILE).unwrap())
            .is_some_and(|links| links.type_checked)
    );
    let queries = queries
        .iter()
        .map(|&node| {
            (
                node,
                checker.get_type_at_location(node).unwrap(),
                checker.get_symbol_at_location(node).unwrap(),
            )
        })
        .collect::<Vec<_>>();
    let before = snapshot(checker, parsed);
    for _ in 0..2 {
        checker.check_source_file(FILE).unwrap();
        checker.recheck_source_file(FILE).unwrap();
        for &(node, type_, owner) in &queries {
            assert_eq!(checker.get_type_at_location(node), Ok(type_));
            assert_eq!(checker.get_symbol_at_location(node), Ok(owner));
        }
        assert_eq!(snapshot(checker, parsed), before);
    }
}

#[test]
fn source_flat_array_for_of_keeps_pair_types_callbacks_and_distinct_loop_owners() {
    let parsed = parse_source_file(PAIR_SOURCE);
    let library = parse_source_file(ARRAY_LIBRARY);
    let loops = loops(&parsed);
    assert_eq!(loops.len(), 2);
    let first_read = reads(&parsed, loops[0].body, "rows")[0];
    for no_unused_locals in [false, true] {
        for query_first in [false, true] {
            let mut checker = context(&parsed, &library, no_unused_locals);
            let cold = query_first.then(|| checker.get_type_at_location(first_read).unwrap());
            checker.check_source_file(FILE).unwrap();
            assert!(
                checker.diagnostics().is_empty(),
                "{:?}",
                checker.diagnostics()
            );
            let string = checker.store().intrinsic_bootstrap().unwrap().string_type;
            let number = checker.store().intrinsic_bootstrap().unwrap().number_type;
            let (first, mut queries) = assert_loop(&mut checker, &parsed, &loops[0], string);
            let (second, second_queries) = assert_loop(&mut checker, &parsed, &loops[1], number);
            assert!(first.iter().all(|owner| !second.contains(owner)));
            assert_ne!(
                symbol(&checker, loops[0].callback),
                symbol(&checker, loops[1].callback)
            );
            if let Some(cold) = cold {
                assert_eq!(checker.get_type_at_location(first_read), Ok(cold));
                assert_eq!(array_element(&checker, cold), string);
            }
            queries.extend(second_queries);
            replay(&mut checker, &parsed, &queries);
        }
    }
}

#[test]
fn source_flat_array_for_of_checks_empty_array_body_and_scope_exit() {
    let source = concat!(
        "declare function suite(label: string, body: () => void): void;\n",
        "declare function strings(value: string[]): void;\n",
        "declare function takeNumber(value: number): void;\n",
        "const pairs: [name: string, rows: string[]][] = [];\n",
        "for (const [name, rows] of pairs) { suite(name, () => { strings(rows); takeNumber(name); }); }\n",
        "strings(rows);\n",
        "takeNumber(name);\n",
    );
    let parsed = parse_source_file(source);
    let library = parse_source_file(ARRAY_LIBRARY);
    let loops = loops(&parsed);
    assert_eq!(loops.len(), 1);
    let first_read = reads(&parsed, loops[0].body, "rows")[0];
    for no_unused_locals in [false, true] {
        for query_first in [false, true] {
            let mut checker = context(&parsed, &library, no_unused_locals);
            let cold = query_first.then(|| checker.get_type_at_location(first_read).unwrap());
            checker.check_source_file(FILE).unwrap();
            let string = checker.store().intrinsic_bootstrap().unwrap().string_type;
            let (_, queries) = assert_loop(&mut checker, &parsed, &loops[0], string);
            let mut actual = checker
                .diagnostics()
                .as_slice()
                .iter()
                .map(|diagnostic| {
                    let node = diagnostic.node.unwrap();
                    let range = diagnostic.range_override.map_or_else(
                        || parsed.arena.get(node.node).unwrap().range,
                        |range| range.range(),
                    );
                    assert!(diagnostic.related_information.is_empty());
                    (
                        diagnostic.diagnostic.code(),
                        usize::try_from(range.start.get()).unwrap(),
                        usize::try_from(range.end.get()).unwrap(),
                        diagnostic.diagnostic.arguments.clone(),
                        diagnostic.diagnostic.render().unwrap(),
                    )
                })
                .collect::<Vec<_>>();
            actual.sort_by_key(|diagnostic| diagnostic.1);
            let wrong = source.find("takeNumber(name)").unwrap() + "takeNumber(".len();
            let rows = source.rfind("strings(rows)").unwrap() + "strings(".len();
            let name = source.rfind("takeNumber(name)").unwrap() + "takeNumber(".len();
            assert_eq!(actual, [
                (2345, wrong, wrong + 4, vec!["string".to_owned(), "number".to_owned()],
                    "Argument of type 'string' is not assignable to parameter of type 'number'.".to_owned()),
                (2304, rows, rows + 4, vec!["rows".to_owned()], "Cannot find name 'rows'.".to_owned()),
                (2304, name, name + 4, vec!["name".to_owned()], "Cannot find name 'name'.".to_owned()),
            ]);
            if let Some(cold) = cold {
                assert_eq!(checker.get_type_at_location(first_read), Ok(cold));
                assert_eq!(array_element(&checker, cold), string);
            }
            replay(&mut checker, &parsed, &queries);
        }
    }
}

#[test]
fn source_flat_array_for_of_rejects_unreleased_headers_and_exits_atomically() {
    let library = parse_source_file(ARRAY_LIBRARY);
    for statement in [
        "for await (const [name, rows] of pairs) {}",
        "for (const [name = 'x', rows] of pairs) {}",
        "for (const [name, ...rows] of pairs) {}",
        "for (const [, rows] of pairs) {}",
        "for (const [name, rows] of pairs) { break; }",
        "for (const [name, rows] of pairs) { continue; }",
        "for (const [name, rows] of pairs) { for (const item of rows) {} }",
    ] {
        let source = format!("declare const pairs: [string, string[]][];\n{statement}\n");
        let parsed = parse_source_file(&source);
        let mut checker = context(&parsed, &library, false);
        let before = snapshot(&checker, &parsed);
        let first = checker.check_source_file(FILE).unwrap_err();
        assert!(
            matches!(first, SourceCheckError::Unsupported(_)),
            "{first:?}"
        );
        assert_eq!(snapshot(&checker, &parsed), before);
        assert_eq!(checker.check_source_file(FILE), Err(first));
        assert_eq!(snapshot(&checker, &parsed), before);
    }
}

#[test]
fn source_flat_array_for_of_rejects_foreign_binding_queries_without_publication() {
    let parsed = parse_source_file(PAIR_SOURCE);
    let foreign = parse_source_file(PAIR_SOURCE);
    let library = parse_source_file(ARRAY_LIBRARY);
    let foreign_name = loops(&foreign)[0].bindings[0].name;
    let mut checker = context(&parsed, &library, false);
    let before = snapshot(&checker, &parsed);
    for _ in 0..2 {
        assert_eq!(
            checker.get_type_at_location(foreign_name),
            Err(CanonicalArtifactQueryError::ForeignNode(foreign_name))
        );
        assert_eq!(
            checker.get_symbol_at_location(foreign_name),
            Err(CanonicalArtifactQueryError::ForeignNode(foreign_name))
        );
        assert_eq!(snapshot(&checker, &parsed), before);
    }
    checker.check_source_file(FILE).unwrap();
    assert!(checker.diagnostics().is_empty());
}
