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

#[derive(Clone, Copy)]
struct DiscriminantVariable {
    name: NodeRef,
    annotation: NodeRef,
    initializer: Option<NodeRef>,
}

fn discriminant_variable(parsed: &ParseResult, name: &str, occurrence: usize) -> DiscriminantVariable {
    let mut matches = parsed.arena.iter().filter_map(|(_, record)| {
        let NodeData::VariableDeclaration(variable) = &record.data else { return None; };
        let NodeData::Identifier(identifier) = &parsed.arena.get(variable.name)?.data else { return None; };
        if identifier.text != name { return None; }
        let node = |id| NodeRef::new(parsed.arena.id(), FILE, id);
        Some((record.range.start, DiscriminantVariable {
            name: node(variable.name),
            annotation: node(variable.type_.unwrap()),
            initializer: variable.initializer.map(node),
        }))
    }).collect::<Vec<_>>();
    matches.sort_by_key(|(start, _)| *start);
    matches[occurrence].1
}

fn expect_discriminant_diagnostics(
    checker: &CanonicalCheckerContext<'_>,
    expected: &[(u32, NodeRef, [&str; 2])],
) {
    let actual = checker.diagnostics().as_slice();
    assert_eq!(actual.len(), expected.len(), "{actual:?}");
    for (actual, (code, node, arguments)) in actual.iter().zip(expected) {
        assert_eq!(actual.diagnostic.code(), *code);
        assert_eq!(actual.diagnostic.arguments, *arguments);
        assert_eq!(actual.node, Some(*node));
        assert!(actual.range_override.is_none());
        assert!(actual.related_information.is_empty());
    }
}

fn check_discriminant_case(
    source: &str,
    cold_variable: &str,
    assertions: impl Fn(&mut CanonicalCheckerContext<'_>, &ParseResult),
) {
    for query_first in [false, true] {
        let parsed = parse_source_file(source);
        let mut checker = context(&parsed);
        let cold = discriminant_variable(&parsed, cold_variable, 0).initializer.unwrap();
        let cold_type = query_first.then(|| checker.get_type_at_location(cold).unwrap());
        checker.check_source_file(FILE).unwrap();
        assertions(&mut checker, &parsed);
        if let Some(cold_type) = cold_type {
            assert_eq!(checker.get_type_at_location(cold), Ok(cold_type));
        }
        let mut initializers = parsed.arena.iter().filter_map(|(_, record)| {
            let NodeData::VariableDeclaration(variable) = &record.data else { return None; };
            variable.initializer.map(|id| (record.range.start, NodeRef::new(parsed.arena.id(), FILE, id)))
        }).collect::<Vec<_>>();
        initializers.sort_by_key(|(start, _)| *start);
        let reads = initializers.into_iter().map(|(_, node)| (
            node,
            checker.get_type_at_location(node).unwrap(),
            checker.get_symbol_at_location(node).unwrap(),
        )).collect::<Vec<_>>();
        let mut parent_symbol = None;
        for (node, _, symbol) in &reads {
            if matches!(parsed.arena.get(node.node).unwrap().data, NodeData::Identifier(_)) {
                let symbol = symbol.expect("the parent reference resolves");
                if let Some(expected) = parent_symbol { assert_eq!(symbol, expected); }
                parent_symbol = Some(symbol);
            }
        }
        let warm = snapshot(&checker, &parsed);
        for _ in 0..2 {
            checker.recheck_source_file(FILE).unwrap();
            assertions(&mut checker, &parsed);
            for &(node, type_, symbol) in &reads {
                assert_eq!(checker.get_type_at_location(node), Ok(type_));
                assert_eq!(checker.get_symbol_at_location(node), Ok(symbol));
            }
            assert_eq!(snapshot(&checker, &parsed), warm);
            assert!(checker.store().type_resolution_is_empty());
            assert!(checker.store().source_file_links(checker.source_file(FILE).unwrap()).unwrap().type_checked);
        }
    }
}

// These exact sources are measured separately from the top-level Go controls.
const CLASS_DECLARED_DISCRIMINANT: &str = r#"interface Left { kind: "left"; }
interface Right { kind: "right"; }
declare const item: Left | Right;
class Reader {
  read(): void {
    if (item.kind === "left") {
      const before: Left = item;
      if (item.kind === "left") {
        const kept: Left = item;
      } else {
        const removed: never = item;
      }
    }
  }
}
"#;

const CLASS_STANDALONE_DISCRIMINANT: &str = r#"interface Whole { kind: "left" | "right"; }
interface LeftView { kind: "left"; }
declare const item: Whole;
class Reader {
  read(): void {
    if (item.kind === "left") {
      const property: "left" = item.kind;
      const parent: Whole = item;
    } else {
      const property: "right" = item.kind;
      const parent: Whole = item;
    }
  }
}
"#;

#[test]
fn class_declared_union_discriminants_keep_former_constituents() {
    for negative in [false, true] {
        let source = if negative {
            CLASS_DECLARED_DISCRIMINANT.replacen("const kept: Left = item;", "const kept: Right = item;", 1)
        } else { CLASS_DECLARED_DISCRIMINANT.to_owned() };
        check_discriminant_case(&source, "removed", |checker, parsed| {
            let before = discriminant_variable(parsed, "before", 0);
            let kept = discriminant_variable(parsed, "kept", 0);
            let removed = discriminant_variable(parsed, "removed", 0);
            if negative {
                expect_discriminant_diagnostics(checker, &[(2322, kept.name, ["Left", "Right"])]);
            } else { expect_discriminant_diagnostics(checker, &[]); }
            let left = checker.get_type_from_type_node(before.annotation).unwrap();
            let never = checker.store().intrinsic_bootstrap().unwrap().never_type;
            assert_ne!(left, never);
            assert_eq!(checker.get_type_at_location(before.initializer.unwrap()), Ok(left));
            assert_eq!(checker.get_type_at_location(kept.initializer.unwrap()), Ok(left));
            assert_eq!(checker.get_type_at_location(removed.initializer.unwrap()), Ok(never));
        });
    }
}

#[test]
fn class_standalone_properties_do_not_rewrite_parents() {
    for negative in [false, true] {
        let source = if negative {
            CLASS_STANDALONE_DISCRIMINANT.replacen("const parent: Whole = item;", "const parent: LeftView = item;", 1)
        } else { CLASS_STANDALONE_DISCRIMINANT.to_owned() };
        check_discriminant_case(&source, "parent", |checker, parsed| {
            let item = discriminant_variable(parsed, "item", 0);
            let first_parent = discriminant_variable(parsed, "parent", 0);
            if negative {
                expect_discriminant_diagnostics(checker, &[(2322, first_parent.name, ["Whole", "LeftView"])]);
            } else { expect_discriminant_diagnostics(checker, &[]); }
            let whole = checker.get_type_from_type_node(item.annotation).unwrap();
            for occurrence in 0..2 {
                let parent = discriminant_variable(parsed, "parent", occurrence);
                let property = discriminant_variable(parsed, "property", occurrence);
                let expected_property = checker.get_type_from_type_node(property.annotation).unwrap();
                assert_eq!(checker.get_type_at_location(parent.initializer.unwrap()), Ok(whole));
                assert_eq!(checker.get_type_at_location(property.initializer.unwrap()), Ok(expected_property));
            }
        });
    }
}

const CLASS_IDENTICAL_REFERENCE_JOIN: &str = r#"interface NumberTable { [name: string]: number; }
interface Holder { table: NumberTable; }
declare const holder: Holder;
declare const condition: boolean;
class Reader {
  flag: boolean = false;
  read(): void {
    if (condition === true) {
      this.flag = true;
    }
    const later: NumberTable = holder.table;
  }
}
"#;

#[test]
fn class_reference_joins_keep_unchanged_indexed_types() {
    for branched in [false, true] {
        for negative in [false, true] {
            let mut source = CLASS_IDENTICAL_REFERENCE_JOIN.to_owned();
            if !branched {
                source = source.replacen(
                    "    if (condition === true) {\n      this.flag = true;\n    }",
                    "    this.flag = true;",
                    1,
                );
            }
            if negative {
                source = source.replacen("const later: NumberTable", "const later: number", 1);
            }
            check_discriminant_case(&source, "later", |checker, parsed| {
                let later = discriminant_variable(parsed, "later", 0);
                let (property_name, annotation) = parsed.arena.iter().find_map(|(_, record)| {
                    let NodeData::PropertyDeclaration(property) = &record.data else { return None; };
                    let NodeData::Identifier(name) = &parsed.arena.get(property.name)?.data else { return None; };
                    if name.text != "table" { return None; }
                    Some((
                        NodeRef::new(parsed.arena.id(), FILE, property.name),
                        NodeRef::new(parsed.arena.id(), FILE, property.type_.unwrap()),
                    ))
                }).expect("the table property has its declared annotation");
                let expected = checker.get_type_from_type_node(annotation).unwrap();
                assert_eq!(checker.get_type_at_location(later.initializer.unwrap()), Ok(expected));
                let property_symbol = checker.get_symbol_at_location(property_name).unwrap().unwrap();
                assert_eq!(checker.get_symbol_at_location(later.initializer.unwrap()), Ok(Some(property_symbol)));
                if negative {
                    expect_discriminant_diagnostics(checker, &[(2322, later.name, ["NumberTable", "number"])]);
                } else {
                    expect_discriminant_diagnostics(checker, &[]);
                }
            });
        }
    }
}

const CLASS_VALUE_CALLS: &str = r#"declare function value(): number;
class Reader {
  flag: boolean = false;
  read(): number {
    if (this.flag === true) {
      this.flag = false;
    }
    const later: number = value();
    return value();
  }
}
"#;

#[test]
fn class_value_calls_keep_types_without_statement_effects() {
    for statement_call in [false, true] {
        for negative in [false, true] {
            let mut source = CLASS_VALUE_CALLS.to_owned();
            if statement_call {
                source = source.replacen("    const later:", "    value();\n    const later:", 1);
            }
            if negative {
                source = source.replacen("  read(): number {", "  read(): string {", 1);
            }
            check_discriminant_case(&source, "later", |checker, parsed| {
                let node = |id| NodeRef::new(parsed.arena.id(), FILE, id);
                let (declaration, name) = parsed.arena.iter().find_map(|(id, record)| {
                    let NodeData::FunctionDeclaration(function) = &record.data else { return None; };
                    let name = function.name?;
                    let NodeData::Identifier(identifier) = &parsed.arena.get(name)?.data else { return None; };
                    (identifier.text == "value").then_some((node(id), node(name)))
                }).expect("the ambient value function exists");
                let symbol = checker.get_symbol_at_location(name).unwrap().unwrap();
                let signature = checker.store().signature_links(declaration).unwrap()
                    .resolved_signature.signature().unwrap();
                let number = checker.store().intrinsic_bootstrap().unwrap().number_type;
                let calls = parsed.arena.iter().filter_map(|(id, record)| {
                    let NodeData::CallExpression(call) = &record.data else { return None; };
                    Some((node(id), node(call.expression)))
                }).collect::<Vec<_>>();
                assert_eq!(calls.len(), if statement_call { 3 } else { 2 });
                for (call, callee) in calls {
                    assert_eq!(checker.get_type_at_location(call), Ok(number));
                    assert_eq!(checker.get_symbol_at_location(callee), Ok(Some(symbol)));
                    assert_eq!(checker.store().signature_links(call).unwrap()
                        .resolved_signature.signature(), Some(signature));
                }
                if negative {
                    let returned = parsed.arena.iter().find_map(|(id, record)| {
                        matches!(record.data, NodeData::ReturnStatement(_)).then_some(node(id))
                    }).expect("the method has one return statement");
                    expect_discriminant_diagnostics(checker, &[(2322, returned, ["number", "string"])]);
                } else {
                    expect_discriminant_diagnostics(checker, &[]);
                }
            });
        }
    }
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
