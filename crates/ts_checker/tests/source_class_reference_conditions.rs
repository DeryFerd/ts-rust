use ts_ast::{FileId, NodeData, NodeRef};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName,
};
use ts_checker::semantic::type_records::LiteralValue;
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, IntrinsicBootstrapOptions, TypeData, TypeId,
};
use ts_parser::{ParseResult, parse_source_file};

const FILE: FileId = FileId::new(300_491);

fn context(parsed: &ParseResult) -> CanonicalCheckerContext<'_> {
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            FILE,
            CanonicalSourceFileFacts::new(
                EscapedName::source("\"/project/reference-conditions.ts\""),
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
            strict_function_types: true,
            strict_property_initialization: true,
            no_implicit_any: true,
            no_implicit_this: true,
            ..CanonicalCheckerOptions::default()
        },
    )
    .unwrap()
}

fn snapshot(
    checker: &CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
) -> impl std::fmt::Debug + PartialEq + use<> {
    let store = checker.store();
    (
        [
            store.type_len(),
            store.symbol_len(),
            store.signature_len(),
            store.mapper_len(),
            store.type_alias_len(),
            store.index_info_len(),
        ],
        parsed
            .arena
            .iter()
            .map(|(id, _)| {
                let node = NodeRef::new(parsed.arena.id(), FILE, id);
                (
                    store.node_links(node).cloned(),
                    store.type_node_links(node).cloned(),
                    store.symbol_node_links(node).cloned(),
                    store.signature_links(node).cloned(),
                )
            })
            .collect::<Vec<_>>(),
        checker.diagnostics().clone(),
    )
}

fn type_parts(checker: &CanonicalCheckerContext<'_>, type_: TypeId) -> Vec<String> {
    let mut parts = match checker.store().type_payload(type_).unwrap().data() {
        TypeData::Intrinsic(intrinsic) => vec![intrinsic.intrinsic_name.clone()],
        TypeData::Literal(literal) => match &literal.value {
            LiteralValue::String(value) => vec![format!("{value:?}")],
            other => panic!("unexpected literal {other:?}"),
        },
        TypeData::Union(union) => union
            .union
            .types
            .iter()
            .flat_map(|type_| type_parts(checker, *type_))
            .collect(),
        other => panic!("unexpected read type {other:?}"),
    };
    parts.sort();
    parts.dedup();
    parts
}

fn check(source: &str, error_sites: &[&str], reads: &[(&str, &[&str])]) {
    for query_first in [false, true] {
        let parsed = parse_source_file(source);
        let mut checker = context(&parsed);
        let property_nodes = parsed
            .arena
            .iter()
            .filter_map(|(id, record)| {
                matches!(record.data, NodeData::PropertyAccessExpression(_)).then_some((
                    NodeRef::new(parsed.arena.id(), FILE, id),
                    source[record.range.start.get() as usize..record.range.end.get() as usize]
                        .trim(),
                ))
            })
            .collect::<Vec<_>>();
        if query_first {
            let node = property_nodes
                .iter()
                .filter(|(_, text)| *text == reads[0].0)
                .nth(1)
                .unwrap()
                .0;
            checker.get_type_at_location(node).unwrap();
        }
        checker.check_source_file(FILE).unwrap();
        assert!(
            checker
                .store()
                .source_file_links(checker.source_file(FILE).unwrap())
                .unwrap()
                .type_checked
        );
        let errors = checker.diagnostics().as_slice();
        assert_eq!(errors.len(), error_sites.len(), "{errors:?}");
        for (error, expected) in errors.iter().zip(error_sites) {
            assert_eq!(error.diagnostic.code(), 2322, "{error:?}");
            let record = parsed.arena.get(error.node.unwrap().node).unwrap();
            assert!(
                matches!(record.data, NodeData::ReturnStatement(_)),
                "{error:?}"
            );
            assert_eq!(
                source[record.range.start.get() as usize..record.range.end.get() as usize].trim(),
                *expected
            );
            assert_eq!(
                record.range.start.get() as usize,
                source.rfind(expected).unwrap()
            );
        }
        for &(text, expected) in reads {
            let name = text.rsplit('.').next().unwrap();
            let declaration = parsed
                .arena
                .iter()
                .find_map(|(id, record)| {
                    let NodeData::PropertyDeclaration(property) = &record.data else {
                        return None;
                    };
                    let NodeData::Identifier(identifier) = &parsed.arena.get(property.name)?.data
                    else {
                        return None;
                    };
                    (identifier.text == name).then_some(NodeRef::new(parsed.arena.id(), FILE, id))
                })
                .unwrap();
            let raw_member = checker.file(FILE).unwrap().1.symbol(declaration).unwrap();
            let expected_member = checker.store().get_merged_symbol(raw_member).unwrap();
            let nodes = property_nodes
                .iter()
                .filter(|(_, actual)| *actual == text)
                .map(|(node, _)| *node)
                .collect::<Vec<_>>();
            assert_eq!(nodes.len(), expected.len(), "{text}");
            let mut member = None;
            for (node, expected) in nodes.into_iter().zip(expected) {
                let type_ = checker.get_type_at_location(node).unwrap();
                assert_eq!(
                    type_parts(&checker, type_).join(" | "),
                    *expected,
                    "{text} at {node:?}"
                );
                let actual = checker.get_symbol_at_location(node).unwrap().unwrap();
                assert_eq!(actual, expected_member);
                if let Some(member) = member {
                    assert_eq!(actual, member);
                }
                member = Some(actual);
            }
        }
        let queries = parsed
            .arena
            .iter()
            .filter_map(|(id, record)| {
                matches!(record.data, NodeData::PropertyAccessExpression(_))
                    .then_some(NodeRef::new(parsed.arena.id(), FILE, id))
            })
            .filter_map(|node| {
                checker
                    .store()
                    .type_node_links(node)
                    .and_then(|links| links.resolved_type)
                    .map(|type_| (node, type_))
            })
            .collect::<Vec<_>>();
        for &(node, expected) in &queries {
            assert_eq!(checker.get_type_at_location(node), Ok(expected));
        }
        let warm = snapshot(&checker, &parsed);
        for _ in 0..2 {
            checker.recheck_source_file(FILE).unwrap();
            for &(node, expected) in &queries {
                assert_eq!(checker.get_type_at_location(node), Ok(expected));
            }
            assert_eq!(snapshot(&checker, &parsed), warm);
            assert!(checker.store().type_resolution_is_empty());
        }
    }
}

#[test]
fn global_property_comparisons_check_both_branches_and_replay() {
    let source = r#"
interface State { mode: "production" | "development"; value: string | undefined; }
declare const shared: State;
class Reader {
  mode(): string {
    if (shared.mode !== "production") {
      const development: "development" = shared.mode;
      return development;
    } else {
      const production: "production" = shared.mode;
      return production;
    }
  }
  value(): string {
    if (shared.value !== undefined) { return shared.value; }
    return "fallback";
  }
  literal(): string {
    if (shared.value === "production") { return shared.value; }
    return "fallback";
  }
}
"#;
    let reads: &[(&str, &[&str])] = &[
        (
            "shared.mode",
            &[
                "\"development\" | \"production\"",
                "\"development\"",
                "\"production\"",
            ],
        ),
        (
            "shared.value",
            &[
                "string | undefined",
                "string",
                "string | undefined",
                "\"production\"",
            ],
        ),
    ];
    check(source, &[], reads);
    check(
        &source.replace("return development;", "return 42;"),
        &["return 42;"],
        reads,
    );
    let inline = source.replace("interface State { mode: \"production\" | \"development\"; value: string | undefined; }\ndeclare const shared: State;",
        "declare const shared: { mode: \"production\" | \"development\"; value: string | undefined; };");
    check(&inline, &[], reads);
}

#[test]
fn property_facts_keep_receiver_identity_and_short_circuit_order() {
    let source = r#"
interface State { value: string | undefined; }
class Reader {
  read(first: State, second: State): string {
    if (first.value !== undefined && second.value !== undefined) {
      const left: string = first.value;
      const right: string = second.value;
      return left;
    }
    return "fallback";
  }
  separate(first: State, second: State): string {
    if (first.value !== undefined) { return second.value; }
    return "fallback";
  }
}
"#;
    check(
        source,
        &["return second.value;"],
        &[
            (
                "first.value",
                &["string | undefined", "string", "string | undefined"],
            ),
            (
                "second.value",
                &["string | undefined", "string", "string | undefined"],
            ),
        ],
    );
}

#[test]
fn replacing_a_parent_resets_nested_property_facts() {
    let source = r#"
interface State { value: string | undefined; }
class Reader {
  state: State;
  count: number = 0;
  constructor(state: State) { this.state = state; }
  sibling(): string {
    if (this.state.value !== undefined) {
      this.count = 1;
      return this.state.value;
    }
    return "fallback";
  }
  replace(next: State): string {
    if (this.state.value !== undefined) {
      this.state = next;
      return this.state.value;
    }
    return "fallback";
  }
}
"#;
    check(
        source,
        &["return this.state.value;"],
        &[(
            "this.state.value",
            &[
                "string | undefined",
                "string",
                "string | undefined",
                "string | undefined",
            ],
        )],
    );
}
