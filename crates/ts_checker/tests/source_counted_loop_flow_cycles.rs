use ts_ast::{FileId, FlowFlags, FlowNodePayload, NodeData, NodeId, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalNameResolverOptions, CanonicalSourceFileFacts,
    CanonicalSourceLanguage, EscapedName, SemanticSymbolId, SymbolFlags,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, IntrinsicBootstrapOptions, TypeData,
};
use ts_options::{ModuleKind, ScriptTarget};
use ts_parser::{ParseResult, parse_source_file};

const FILE: FileId = FileId::new(205_700);
const ES5_FILE: FileId = FileId::new(205_701);
const DECORATORS_FILE: FileId = FileId::new(205_702);
const LEGACY_DECORATORS_FILE: FileId = FileId::new(205_703);
const ES5: &str = include_str!("../../ts_bundled/libs/lib.es5.d.ts");
const DECORATORS: &str = include_str!("../../ts_bundled/libs/lib.decorators.d.ts");
const LEGACY_DECORATORS: &str = include_str!("../../ts_bundled/libs/lib.decorators.legacy.d.ts");

fn context<'a>(
    parsed: &'a ParseResult,
    libraries: &'a [ParseResult; 3],
) -> CanonicalCheckerContext<'a> {
    let files = [
        (ES5_FILE, &libraries[0], "\"/lib/lib.es5.d.ts\""),
        (
            DECORATORS_FILE,
            &libraries[1],
            "\"/lib/lib.decorators.d.ts\"",
        ),
        (
            LEGACY_DECORATORS_FILE,
            &libraries[2],
            "\"/lib/lib.decorators.legacy.d.ts\"",
        ),
        (FILE, parsed, "\"/project/counted-loop-flow-cycles.ts\""),
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
            intrinsic: IntrinsicBootstrapOptions {
                strict_null_checks: true,
                exact_optional_property_types: false,
            },
            strict_bind_call_apply: true,
            strict_builtin_iterator_return: true,
            strict_function_types: true,
            strict_property_initialization: true,
            use_unknown_in_catch_variables: true,
            no_implicit_any: true,
            no_implicit_this: true,
            no_unchecked_indexed_access: true,
            no_unused_locals: true,
            isolated_modules: true,
            module_kind: ModuleKind::EsNext,
            no_emit: true,
            name_resolution: CanonicalNameResolverOptions {
                isolated_modules: true,
                verbatim_module_syntax: true,
                emit_target: ScriptTarget::EsNext,
                ..CanonicalNameResolverOptions::default()
            },
            ..CanonicalCheckerOptions::default()
        },
    )
    .unwrap()
}

fn node(parsed: &ParseResult, id: NodeId) -> NodeRef {
    NodeRef::new(parsed.arena.id(), FILE, id)
}

fn text<'a>(source: &'a str, parsed: &ParseResult, location: NodeRef) -> &'a str {
    assert_eq!(location.arena, parsed.arena.id());
    assert_eq!(location.file, FILE);
    let range = parsed.arena.get(location.node).unwrap().range;
    &source[usize::try_from(range.start.get()).unwrap()..usize::try_from(range.end.get()).unwrap()]
}

fn expression(parsed: &ParseResult, source: &str, kind: SyntaxKind, expected: &str) -> NodeRef {
    let matches = parsed
        .arena
        .iter()
        .filter_map(|(id, record)| {
            let location = node(parsed, id);
            (record.kind == kind && text(source, parsed, location) == expected).then_some(location)
        })
        .collect::<Vec<_>>();
    assert_eq!(matches.len(), 1, "expected one {expected:?}");
    matches[0]
}

fn declaration(parsed: &ParseResult, expected: &str) -> NodeRef {
    let matches = parsed
        .arena
        .iter()
        .filter_map(|(id, record)| {
            let name = match &record.data {
                NodeData::VariableDeclaration(data) => data.name,
                NodeData::ParameterDeclaration(data) => data.name,
                _ => return None,
            };
            let NodeData::Identifier(identifier) = &parsed.arena.get(name)?.data else {
                return None;
            };
            (identifier.text == expected).then_some(node(parsed, id))
        })
        .collect::<Vec<_>>();
    assert_eq!(matches.len(), 1, "expected one declaration of {expected}");
    matches[0]
}

fn symbol(checker: &CanonicalCheckerContext<'_>, declaration: NodeRef) -> SemanticSymbolId {
    let raw = checker.file(FILE).unwrap().1.symbol(declaration).unwrap();
    checker.store().get_merged_symbol(raw).unwrap()
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
                let location = node(parsed, id);
                (
                    location,
                    store.node_links(location).cloned(),
                    store.type_node_links(location).cloned(),
                    store.symbol_node_links(location).cloned(),
                    store.signature_links(location).cloned(),
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
        store.relation_state_snapshot(),
        checker.file(FILE).unwrap().1.flow_graph().clone(),
        checker.diagnostics().clone(),
    )
}

fn check_counted_source(source: &str, loop_names: &[&str], call_text: &str) {
    let parsed = parse_source_file(source);
    let libraries = [ES5, DECORATORS, LEGACY_DECORATORS].map(parse_source_file);
    let call = expression(&parsed, source, SyntaxKind::CallExpression, call_text);
    let arrows = parsed
        .arena
        .iter()
        .filter_map(|(id, record)| {
            (record.kind == SyntaxKind::ArrowFunction).then_some(node(&parsed, id))
        })
        .collect::<Vec<_>>();
    let [callable] = arrows.as_slice() else {
        panic!("expected one source arrow");
    };
    assert_eq!(
        parsed
            .arena
            .iter()
            .filter(|(_, record)| record.kind == SyntaxKind::ForStatement)
            .count(),
        loop_names.len()
    );

    for query_first in [false, true] {
        let mut checker = context(&parsed, &libraries);
        let bound_before = checker.file(FILE).unwrap().1.flow_graph().clone();
        let first_call_type = query_first.then(|| checker.get_type_at_location(call).unwrap());
        checker.check_source_file(FILE).unwrap();
        assert!(
            checker.diagnostics().is_empty(),
            "{:?}",
            checker.diagnostics()
        );
        assert!(
            checker
                .store()
                .source_file_links(checker.source_file(FILE).unwrap())
                .unwrap()
                .type_checked
        );
        let intrinsics = checker.store().intrinsic_bootstrap().unwrap();
        let (number, boolean, void) = (
            intrinsics.number_type,
            intrinsics.boolean_type,
            intrinsics.void_type,
        );
        if let Some(first_call_type) = first_call_type {
            assert_eq!(first_call_type, void);
        }
        assert_eq!(checker.get_type_at_location(call), Ok(void));
        let callable_type = checker.get_type_at_location(*callable).unwrap();
        let TypeData::Object(object) = checker.store().type_payload(callable_type).unwrap().data()
        else {
            panic!("expected the real source callable type");
        };
        assert_eq!(object.structured.call_signature_count, 1);
        let [signature] = object.structured.signatures.as_deref().unwrap() else {
            panic!("expected one call signature");
        };
        let signature = checker.store().signature(*signature).unwrap();
        assert_eq!(signature.declaration(), Some(*callable));
        assert_eq!(
            signature.parameters(),
            &[symbol(&checker, declaration(&parsed, "limit"))]
        );
        assert_eq!(signature.resolved_return_type(), Some(number));
        assert!(signature.type_parameters().is_empty());

        for &name in loop_names {
            let declaration = declaration(&parsed, name);
            let owner = symbol(&checker, declaration);
            let bound = checker.file(FILE).unwrap().1;
            let scope = bound.block_scope_container(declaration).unwrap();
            assert_eq!(bound.container(declaration), Some(*callable));
            assert_eq!(
                parsed.arena.get(scope.node).unwrap().kind,
                SyntaxKind::ForStatement
            );
            assert_eq!(
                bound
                    .locals(scope)
                    .and_then(|table| checker.store().symbol_table(table))
                    .and_then(|table| table.get_source(name)),
                Some(owner)
            );
            assert_eq!(
                checker.store().symbol(owner).unwrap().flags(),
                SymbolFlags::BLOCK_SCOPED_VARIABLE
            );
            for (id, record) in parsed.arena.iter() {
                let location = node(&parsed, id);
                if record.kind == SyntaxKind::Identifier && text(source, &parsed, location) == name
                {
                    assert_eq!(checker.get_symbol_at_location(location), Ok(Some(owner)));
                }
            }
        }

        // The innermost incrementor reads its target at the actual body CALL flow.
        let update_text = format!("{}++", loop_names.last().unwrap());
        let update = expression(
            &parsed,
            source,
            SyntaxKind::PostfixUnaryExpression,
            &update_text,
        );
        let NodeData::PostfixUnaryExpression(unary) = &parsed.arena.get(update.node).unwrap().data
        else {
            panic!("expected the parsed incrementor");
        };
        let bound = checker.file(FILE).unwrap().1;
        let entry = bound.flow_at(node(&parsed, unary.operand)).unwrap();
        let entry_node = bound.flow_graph().nodes().get(entry).unwrap();
        assert_eq!(entry.arena, parsed.arena.id());
        assert_eq!(entry.file, FILE);
        assert!(entry_node.flags.contains(FlowFlags::CALL));
        assert_eq!(entry_node.payload, Some(FlowNodePayload::Ast(call)));

        let mut queries = vec![(*callable, callable_type), (call, void)];
        for (id, record) in parsed.arena.iter() {
            let location = node(&parsed, id);
            let expected = match record.kind {
                SyntaxKind::Identifier
                    if text(source, &parsed, location) == "limit"
                        || loop_names.contains(&text(source, &parsed, location)) =>
                {
                    Some(number)
                }
                SyntaxKind::BinaryExpression => Some(boolean),
                SyntaxKind::PostfixUnaryExpression => Some(number),
                _ => None,
            };
            if let Some(expected) = expected {
                assert_eq!(checker.get_type_at_location(location), Ok(expected));
                queries.push((location, expected));
            }
        }
        assert_eq!(checker.file(FILE).unwrap().1.flow_graph(), &bound_before);
        assert!(checker.diagnostics().is_empty());
        let before = snapshot(&checker, &parsed);
        for _ in 0..2 {
            checker.check_source_file(FILE).unwrap();
            checker.recheck_source_file(FILE).unwrap();
            for &(location, expected) in &queries {
                assert_eq!(checker.get_type_at_location(location), Ok(expected));
            }
            assert_eq!(snapshot(&checker, &parsed), before);
        }
    }
}

#[test]
fn counted_loop_call_backedge_keeps_types_and_replay() {
    let source = r#"declare function visit(index: number): void;
export const count = (limit: number): number => {
  for (let i = 0; i < limit; i++) {
    visit(i);
  }
  return limit;
};
"#;
    check_counted_source(source, &["i"], "visit(i)");
}

#[test]
fn nested_counted_loop_backedges_keep_types_and_replay() {
    let source = r#"declare function visit(outer: number, inner: number): void;
export const count = (limit: number): number => {
  for (let i = 0; i < limit; i++) {
    for (let j = 0; j < limit; j++) {
      visit(i, j);
    }
  }
  return limit;
};
"#;
    check_counted_source(source, &["i", "j"], "visit(i, j)");
}
