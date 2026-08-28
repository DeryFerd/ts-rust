use ts_ast::{FileId, NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalNameResolverOptions, CanonicalSourceFileFacts,
    CanonicalSourceLanguage, EscapedName,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, IntrinsicBootstrapOptions,
};
use ts_options::ScriptTarget;
use ts_parser::{ParseResult, parse_source_file};

const FILE: FileId = FileId::new(146_740);
const BOOLEAN_SOURCE: &str = "class BooleanAssignment { value?: number; source?: boolean; constructor(input: string) { const first: number = input; this.value = this.source; const after: number = this.value; } }";
const SCALAR_SOURCE: &str = "class ScalarAssignment { value?: number; constructor(input: string) { this.value = input; const after: number = this.value; } }";

fn context(parsed: &ParseResult, exact: bool) -> CanonicalCheckerContext<'_> {
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            FILE,
            CanonicalSourceFileFacts::new(
                EscapedName::source("\"/project/class-write-final-review.ts\""),
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
                exact_optional_property_types: exact,
            },
            strict_property_initialization: true,
            no_implicit_any: true,
            name_resolution: CanonicalNameResolverOptions {
                emit_target: ScriptTarget::Es2015,
                ..CanonicalNameResolverOptions::default()
            },
            ..CanonicalCheckerOptions::default()
        },
    )
    .unwrap()
}

fn counts(context: &CanonicalCheckerContext<'_>) -> (usize, usize, usize, usize) {
    (
        context.store().type_len(),
        context.store().signature_len(),
        context.store().symbol_len(),
        context.store().mapper_len(),
    )
}

fn initializer(parsed: &ParseResult, name: &str) -> NodeRef {
    parsed
        .arena
        .iter()
        .find_map(|(_, record)| {
            let NodeData::VariableDeclaration(variable) = &record.data else {
                return None;
            };
            let NodeData::Identifier(identifier) = &parsed.arena.get(variable.name)?.data else {
                return None;
            };
            (identifier.text == name).then_some(NodeRef::new(
                parsed.arena.id(),
                FILE,
                variable.initializer?,
            ))
        })
        .unwrap()
}

fn checked_type(
    context: &CanonicalCheckerContext<'_>,
    node: NodeRef,
) -> ts_checker::semantic::TypeId {
    context
        .store()
        .type_node_links(node)
        .unwrap()
        .resolved_type
        .unwrap()
}

fn assert_warm(parsed: &ParseResult, context: &mut CanonicalCheckerContext<'_>) {
    let nodes = parsed
        .arena
        .iter()
        .map(|(node, _)| NodeRef::new(parsed.arena.id(), FILE, node))
        .collect::<Vec<_>>();
    let mut symbols = parsed
        .arena
        .iter()
        .filter_map(|(node, record)| {
            matches!(
                record.data,
                NodeData::PropertyDeclaration(_) | NodeData::ParameterDeclaration(_)
            )
            .then(|| {
                context
                    .file(FILE)
                    .unwrap()
                    .1
                    .symbol(NodeRef::new(parsed.arena.id(), FILE, node))
            })
            .flatten()
        })
        .collect::<Vec<_>>();
    for (node, record) in parsed.arena.iter() {
        if !matches!(record.data, NodeData::ConstructorDeclaration(_)) {
            continue;
        }
        let constructor = NodeRef::new(parsed.arena.id(), FILE, node);
        if let Some(locals) = context.file(FILE).unwrap().1.locals(constructor)
            && let Some(table) = context.store().symbol_table(locals)
        {
            for name in ["value", "input"] {
                if let Some(symbol) = table.get_source(name) {
                    symbols.push(symbol);
                }
            }
        }
    }
    let snapshot = |context: &CanonicalCheckerContext<'_>| {
        (
            counts(context),
            nodes
                .iter()
                .map(|node| {
                    (
                        context.store().type_node_links(*node).cloned(),
                        context.store().symbol_node_links(*node).cloned(),
                    )
                })
                .collect::<Vec<_>>(),
            symbols
                .iter()
                .map(|symbol| {
                    (
                        context.store().value_symbol_links(*symbol).cloned(),
                        context.store().symbol(*symbol).unwrap().check_flags(),
                    )
                })
                .collect::<Vec<_>>(),
        )
    };
    let before = snapshot(context);
    let diagnostics = context.diagnostics().clone();
    for _ in 0..2 {
        context.recheck_source_file(FILE).unwrap();
        assert_eq!(context.diagnostics(), &diagnostics);
        assert_eq!(snapshot(context), before);
    }
}

#[derive(Debug, Eq, PartialEq)]
struct DiagnosticRecord {
    code: u32,
    start: u32,
    end: u32,
    rendered: String,
    details: Vec<String>,
    related: usize,
}

fn diagnostic_records(
    parsed: &ParseResult,
    context: &CanonicalCheckerContext<'_>,
) -> Vec<DiagnosticRecord> {
    context
        .diagnostics()
        .as_slice()
        .iter()
        .map(|entry| {
            let range = entry.range_override.map_or_else(
                || parsed.arena.get(entry.node.unwrap().node).unwrap().range,
                |range| range.range(),
            );
            DiagnosticRecord {
                code: entry.diagnostic.code(),
                start: range.start.get(),
                end: range.end.get(),
                rendered: entry.diagnostic.render().unwrap(),
                details: entry.diagnostic.details.clone(),
                related: entry.related_information.len(),
            }
        })
        .collect()
}

fn expected_diagnostic(
    code: u32,
    start: u32,
    end: u32,
    head: &str,
    details: &[&str],
) -> DiagnosticRecord {
    DiagnosticRecord {
        code,
        start,
        end,
        rendered: std::iter::once(head)
            .chain(details.iter().copied())
            .collect::<Vec<_>>()
            .join("\n"),
        details: details.iter().map(|detail| (*detail).to_owned()).collect(),
        related: 0,
    }
}

#[test]
#[allow(clippy::too_many_lines)] // Each Go case checks types, complete diagnostics, and warm state.
fn final_class_write_diagnostics_preserve_actual_types_ranges_and_order() {
    let mut mismatches = Vec::new();
    for (source, boolean) in [(BOOLEAN_SOURCE, true), (SCALAR_SOURCE, false)] {
        for exact in [false, true] {
            let parsed = parse_source_file(source);
            assert!(parsed.diagnostics.is_empty());
            let mut context = context(&parsed, exact);
            context
                .check_source_file(FILE)
                .unwrap_or_else(|error| panic!("{source}: {error:?}"));
            let (left, right) = parsed
                .arena
                .iter()
                .find_map(|(_, record)| {
                    let NodeData::BinaryExpression(binary) = &record.data else {
                        return None;
                    };
                    Some((
                        NodeRef::new(parsed.arena.id(), FILE, binary.left),
                        NodeRef::new(parsed.arena.id(), FILE, binary.right),
                    ))
                })
                .unwrap();
            let target = checked_type(&context, left);
            assert_eq!(
                context.type_to_string(target).unwrap(),
                if exact {
                    "number"
                } else {
                    "number | undefined"
                }
            );
            assert_eq!(
                context
                    .type_to_string(checked_type(&context, right))
                    .unwrap(),
                if boolean {
                    "boolean | undefined"
                } else {
                    "string"
                },
            );
            assert_eq!(
                context
                    .type_to_string(checked_type(&context, initializer(&parsed, "after")))
                    .unwrap(),
                "number | undefined"
            );
            if boolean {
                assert_eq!(
                    context
                        .type_to_string(checked_type(&context, initializer(&parsed, "first")))
                        .unwrap(),
                    "string"
                );
            }
            let bootstrap = context.store().intrinsic_bootstrap().unwrap();
            for (node, record) in parsed.arena.iter() {
                let NodeData::PropertyDeclaration(property) = &record.data else {
                    continue;
                };
                let declared = match parsed.arena.get(property.type_.unwrap()).unwrap().kind {
                    SyntaxKind::NumberKeyword => bootstrap.number_type,
                    SyntaxKind::BooleanKeyword => bootstrap.boolean_type,
                    _ => panic!("the fixture has only number and boolean fields"),
                };
                let symbol = context
                    .file(FILE)
                    .unwrap()
                    .1
                    .symbol(NodeRef::new(parsed.arena.id(), FILE, node))
                    .unwrap();
                assert_eq!(
                    context
                        .store()
                        .value_symbol_links(symbol)
                        .unwrap()
                        .resolved_type,
                    Some(declared)
                );
            }
            let actual = diagnostic_records(&parsed, &context);
            let mut expected = Vec::new();
            if boolean {
                expected.push(expected_diagnostic(
                    2322,
                    95,
                    100,
                    "Type 'string' is not assignable to type 'number'.",
                    &[],
                ));
                let (code, head, detail) = if exact {
                    (
                        2412,
                        "Type 'boolean | undefined' is not assignable to type 'number' with 'exactOptionalPropertyTypes: true'. Consider adding 'undefined' to the type of the target.",
                        "  Type 'undefined' is not assignable to type 'number'.",
                    )
                } else {
                    (
                        2322,
                        "Type 'boolean | undefined' is not assignable to type 'number | undefined'.",
                        "  Type 'boolean' is not assignable to type 'number'.",
                    )
                };
                expected.push(expected_diagnostic(code, 118, 128, head, &[detail]));
            } else {
                expected.push(expected_diagnostic(
                    2322,
                    70,
                    80,
                    "Type 'string' is not assignable to type 'number'.",
                    &[],
                ));
            }
            let (start, end) = if boolean { (150, 155) } else { (96, 101) };
            expected.push(expected_diagnostic(
                2322,
                start,
                end,
                "Type 'number | undefined' is not assignable to type 'number'.",
                &["  Type 'undefined' is not assignable to type 'number'."],
            ));
            assert_warm(&parsed, &mut context);
            println!("boolean={boolean} exact={exact} records={actual:?}");
            if actual != expected {
                mismatches.push(format!(
                    "boolean={boolean} exact={exact}: actual={actual:?}, expected={expected:?}"
                ));
            }
        }
    }
    assert!(mismatches.is_empty(), "{}", mismatches.join("\n"));
}

#[test]
#[allow(clippy::too_many_lines)] // The unrelated query and class checks share each source context.
fn final_string_optional_constructor_is_independent_of_unrelated_union_queries() {
    for write in ["", "this.value = undefined;"] {
        for exact in [false, true] {
            let source = format!(
                "declare let unrelated: number | undefined; class StringHistory {{ constructor(public readonly value?: string) {{ {write} const parameter = value; const field = this.value; }} }}"
            );
            let parsed = parse_source_file(&source);
            assert!(parsed.diagnostics.is_empty());
            let union = parsed
                .arena
                .iter()
                .find_map(|(node, record)| {
                    (record.kind == SyntaxKind::UnionType).then_some(NodeRef::new(
                        parsed.arena.id(),
                        FILE,
                        node,
                    ))
                })
                .unwrap();
            let mut expected_counts = None;
            for query_first in [false, true] {
                let mut context = context(&parsed, exact);
                if query_first {
                    let unrelated = context.get_type_from_type_node(union).unwrap();
                    assert_eq!(
                        context.type_to_string(unrelated).unwrap(),
                        "number | undefined"
                    );
                }
                context.check_source_file(FILE).unwrap_or_else(|error| {
                    panic!("write={write:?} exact={exact} query_first={query_first}: {error:?}")
                });
                assert!(context.diagnostics().is_empty());
                let parameter = checked_type(&context, initializer(&parsed, "parameter"));
                assert_eq!(
                    context.type_to_string(parameter).unwrap(),
                    "string | undefined"
                );
                let field = checked_type(&context, initializer(&parsed, "field"));
                assert_eq!(
                    context.type_to_string(field).unwrap(),
                    if write.is_empty() {
                        "string | undefined"
                    } else {
                        "undefined"
                    }
                );
                let constructor = parsed
                    .arena
                    .iter()
                    .find_map(|(node, record)| {
                        matches!(record.data, NodeData::ConstructorDeclaration(_))
                            .then_some(NodeRef::new(parsed.arena.id(), FILE, node))
                    })
                    .unwrap();
                let local = context
                    .file(FILE)
                    .unwrap()
                    .1
                    .locals(constructor)
                    .and_then(|locals| context.store().symbol_table(locals))
                    .and_then(|locals| locals.get_source("value"))
                    .unwrap();
                assert_eq!(
                    context
                        .store()
                        .value_symbol_links(local)
                        .unwrap()
                        .resolved_type,
                    Some(parameter)
                );
                let unrelated = context.get_type_from_type_node(union).unwrap();
                assert_eq!(
                    context.type_to_string(unrelated).unwrap(),
                    "number | undefined"
                );
                assert_ne!(unrelated, parameter);
                let ready = counts(&context);
                assert_eq!(*expected_counts.get_or_insert(ready), ready);
                assert_warm(&parsed, &mut context);
                println!(
                    "write={} exact={exact} query_first={query_first}: parameter=string | undefined field={}",
                    !write.is_empty(),
                    context.type_to_string(field).unwrap()
                );
            }
        }
    }
}
