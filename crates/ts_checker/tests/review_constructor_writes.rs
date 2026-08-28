use ts_ast::{FileId, NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalNameResolverOptions, CanonicalSourceFileFacts,
    CanonicalSourceLanguage, EscapedName,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, IntrinsicBootstrapOptions,
    RelationUnavailable, SourceCheckError,
};
use ts_options::ScriptTarget;
use ts_parser::{ParseResult, parse_source_file};

const FILE: FileId = FileId::new(141_740);
const OPTIONAL_NUMBER_ERROR: &str = concat!(
    "Type 'number | undefined' is not assignable to type 'number'.\n",
    "  Type 'undefined' is not assignable to type 'number'.",
);
const BEFORE_SUPER: &str =
    "'super' must be called before accessing 'this' in the constructor of a derived class.";

fn context(parsed: &ParseResult, exact: bool) -> CanonicalCheckerContext<'_> {
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            FILE,
            CanonicalSourceFileFacts::new(
                EscapedName::source("\"/project/constructor-write-review.ts\""),
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

#[allow(clippy::too_many_lines)] // Diagnostics, field types, and replay checks share one source case.
fn assert_case(
    source: &str,
    exact: bool,
    expected_diagnostics: &[(u32, &str, &str)],
    expected_initializers: &[(&str, &str)],
) {
    let parsed = parse_source_file(source);
    assert!(
        parsed.diagnostics.is_empty(),
        "{source}: {:?}",
        parsed.diagnostics
    );
    let mut context = context(&parsed, exact);
    context
        .check_source_file(FILE)
        .unwrap_or_else(|error| panic!("{source}: {error:?}"));

    let mut actual = context
        .diagnostics()
        .as_slice()
        .iter()
        .map(|entry| {
            let start = entry.range_override.map_or_else(
                || {
                    parsed
                        .arena
                        .get(entry.node.unwrap().node)
                        .unwrap()
                        .range
                        .start
                },
                |range| range.range().start,
            );
            (
                entry.diagnostic.code(),
                start.get() as usize,
                entry.diagnostic.render().unwrap(),
            )
        })
        .collect::<Vec<_>>();
    // The Go CLI sorts diagnostics by source position. Keep raw order for warm checks below.
    actual.sort_by_key(|(code, start, _)| (*start, *code));
    let expected = expected_diagnostics
        .iter()
        .map(|(code, marker, message)| (*code, source.find(marker).unwrap(), (*message).to_owned()))
        .collect::<Vec<_>>();
    for (expected_name, expected_type) in expected_initializers {
        let initializer = parsed
            .arena
            .iter()
            .find_map(|(_, record)| {
                let NodeData::VariableDeclaration(variable) = &record.data else {
                    return None;
                };
                let NodeData::Identifier(name) = &parsed.arena.get(variable.name)?.data else {
                    return None;
                };
                (name.text == *expected_name)
                    .then(|| NodeRef::new(parsed.arena.id(), FILE, variable.initializer.unwrap()))
            })
            .unwrap();
        let type_ = context
            .store()
            .type_node_links(initializer)
            .unwrap()
            .resolved_type
            .unwrap();
        assert_eq!(
            context.type_to_string(type_).unwrap(),
            *expected_type,
            "{expected_name}"
        );
    }

    let nodes = parsed
        .arena
        .iter()
        .map(|(node, _)| NodeRef::new(parsed.arena.id(), FILE, node))
        .collect::<Vec<_>>();
    let links = |context: &CanonicalCheckerContext<'_>| {
        nodes
            .iter()
            .map(|node| {
                (
                    context.store().type_node_links(*node).cloned(),
                    context.store().symbol_node_links(*node).cloned(),
                )
            })
            .collect::<Vec<_>>()
    };
    let fields = parsed
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
    let field_links = |context: &CanonicalCheckerContext<'_>| {
        fields
            .iter()
            .map(|symbol| {
                (
                    context.store().value_symbol_links(*symbol).cloned(),
                    context.store().symbol(*symbol).unwrap().check_flags(),
                )
            })
            .collect::<Vec<_>>()
    };
    let counts = |context: &CanonicalCheckerContext<'_>| {
        (
            context.store().type_len(),
            context.store().signature_len(),
            context.store().symbol_len(),
            context.store().mapper_len(),
        )
    };
    let diagnostics = context.diagnostics().clone();
    let warm = (counts(&context), links(&context), field_links(&context));
    for _ in 0..2 {
        context.recheck_source_file(FILE).unwrap();
        assert_eq!(context.diagnostics(), &diagnostics);
        assert_eq!(
            (counts(&context), links(&context), field_links(&context)),
            warm
        );
    }

    let bootstrap = context.store().intrinsic_bootstrap().unwrap();
    for (node, record) in parsed.arena.iter() {
        let NodeData::PropertyDeclaration(property) = &record.data else {
            continue;
        };
        let declared = match property
            .type_
            .and_then(|node| parsed.arena.get(node))
            .map(|record| record.kind)
        {
            Some(SyntaxKind::NumberKeyword) => bootstrap.number_type,
            Some(SyntaxKind::StringKeyword) => bootstrap.string_type,
            Some(SyntaxKind::BooleanKeyword) => bootstrap.boolean_type,
            _ => continue,
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
    assert_eq!(actual, expected, "exact={exact}: {source}");
}

#[test]
fn review_constructor_write_union_messages_match_go() {
    for exact in [false, true] {
        let message = if exact {
            concat!(
                "Type 'string | undefined' is not assignable to type 'number' with ",
                "'exactOptionalPropertyTypes: true'. Consider adding 'undefined' to the type of the target.\n",
                "  Type 'undefined' is not assignable to type 'number'."
            )
        } else {
            concat!(
                "Type 'string | undefined' is not assignable to type 'number | undefined'.\n",
                "  Type 'string' is not assignable to type 'number'."
            )
        };
        assert_case(
            "class UnionSource { value?: number; source?: string; constructor() { this.value = this.source; const after: number = this.value; } }",
            exact,
            &[
                (if exact { 2412 } else { 2322 }, "this.value =", message),
                (2322, "after: number", OPTIONAL_NUMBER_ERROR),
            ],
            &[("after", "number | undefined")],
        );
    }
}

#[test]
fn review_constructor_write_optional_union_messages_match_go() {
    for exact in [false, true] {
        let mut expected = Vec::new();
        if exact {
            expected.push((2412, "this.value =", concat!(
                "Type 'number | undefined' is not assignable to type 'number' with ",
                "'exactOptionalPropertyTypes: true'. Consider adding 'undefined' to the type of the target.\n",
                "  Type 'undefined' is not assignable to type 'number'.")));
        }
        expected.push((2322, "after: number", OPTIONAL_NUMBER_ERROR));
        assert_case(
            "class OptionalUnionSource { value?: number; source?: number; constructor() { this.value = this.source; const after: number = this.value; } }",
            exact,
            &expected,
            &[("after", "number | undefined")],
        );
    }
}

#[test]
fn review_constructor_write_parameter_flow_is_separate_from_member_flow() {
    for source in [
        "class ParameterIsolation { constructor(public readonly value?: number) { this.value = 1; const member: number = this.value; const parameter: number = value; } }",
        "class LocalShadow { value?: number; constructor(value?: number) { this.value = 1; const member: number = this.value; const parameter: number = value; } }",
    ] {
        for exact in [false, true] {
            assert_case(
                source,
                exact,
                &[(2322, "parameter: number", OPTIONAL_NUMBER_ERROR)],
                &[("member", "number"), ("parameter", "number | undefined")],
            );
        }
    }
}

#[test]
fn review_constructor_write_private_and_public_names_are_distinct() {
    assert_case(
        "class PrivateSameName { value?: number; #value: number; constructor() { this.value = 1; const before = this.#value; this.#value = 2; const secret: number = this.#value; const ordinary: number = this.value; } }",
        false,
        &[(
            2565,
            "#value; this.#value",
            "Property '#value' is used before being assigned.",
        )],
        &[
            ("before", "number"),
            ("secret", "number"),
            ("ordinary", "number"),
        ],
    );
}

#[test]
fn review_constructor_write_before_super_keeps_both_receivers() {
    assert_case(
        "class Base {} class BeforeSuperRhs extends Base { left?: number; right: number = 1; constructor() { this.left = this.right; super(); const after: number = this.left; } }",
        false,
        &[
            (
                2376,
                "constructor()",
                "A 'super' call must be the first statement in the constructor to refer to 'super' or 'this' when a derived class contains initialized properties, parameter properties, or private identifiers.",
            ),
            (17009, "this.left =", BEFORE_SUPER),
            (17009, "this.right;", BEFORE_SUPER),
        ],
        &[("after", "number")],
    );
}

#[test]
fn review_constructor_write_plain_parameter_keeps_assignment_check() {
    assert_case(
        "class PlainParameter { value?: number; constructor(input: string) { this.value = input; } }",
        false,
        &[(
            2322,
            "this.value =",
            "Type 'string' is not assignable to type 'number'.",
        )],
        &[],
    );
}

#[test]
fn review_constructor_write_rhs_uses_the_previous_write() {
    for exact in [false, true] {
        assert_case(
            "class SelfReadAfterWrite { value?: number; constructor() { this.value = 1; this.value = this.value; const after: number = this.value; } }",
            exact,
            &[],
            &[("after", "number")],
        );
    }
}

#[test]
fn review_constructor_write_exact_string_union_messages_match_go() {
    assert_case(
        "class UnionSource { value?: number; source?: string; constructor() { this.value = this.source; const after: number = this.value; } }",
        true,
        &[
            (
                2412,
                "this.value =",
                concat!(
                    "Type 'string | undefined' is not assignable to type 'number' with ",
                    "'exactOptionalPropertyTypes: true'. Consider adding 'undefined' to the type of the target.\n",
                    "  Type 'undefined' is not assignable to type 'number'."
                ),
            ),
            (2322, "after: number", OPTIONAL_NUMBER_ERROR),
        ],
        &[("after", "number | undefined")],
    );
}

#[test]
fn review_constructor_write_exact_number_union_messages_match_go() {
    assert_case(
        "class OptionalUnionSource { value?: number; source?: number; constructor() { this.value = this.source; const after: number = this.value; } }",
        true,
        &[
            (
                2412,
                "this.value =",
                concat!(
                    "Type 'number | undefined' is not assignable to type 'number' with ",
                    "'exactOptionalPropertyTypes: true'. Consider adding 'undefined' to the type of the target.\n",
                    "  Type 'undefined' is not assignable to type 'number'."
                ),
            ),
            (2322, "after: number", OPTIONAL_NUMBER_ERROR),
        ],
        &[("after", "number | undefined")],
    );
}

#[test]
fn review_constructor_write_optional_parameter_accepts_undefined() {
    for exact in [false, true] {
        assert_case(
            "class OptionalParameter { constructor(public value?: number) { this.value = undefined; const after: undefined = this.value; } }",
            exact,
            &[],
            &[("after", "undefined")],
        );
    }
}

#[test]
fn review_constructor_write_optional_local_parameter_does_not_follow_member_flow() {
    for exact in [false, true] {
        assert_case(
            "class LocalShadow { value?: number; constructor(value?: number) { this.value = 1; const member: number = this.value; const parameter: number = value; } }",
            exact,
            &[(2322, "parameter: number", OPTIONAL_NUMBER_ERROR)],
            &[("member", "number"), ("parameter", "number | undefined")],
        );
    }
}

#[test]
fn review_constructor_optional_parameter_planning_is_independent_of_query_history() {
    for write in ["", "this.value = 1;"] {
        let source = format!(
            "declare let cachedOptional: number | undefined; \
             class OptionalParameterControl {{ constructor(public readonly value?: number) {{ \
             {write} const parameter = value; }} }}"
        );
        let parsed = parse_source_file(&source);
        assert!(parsed.diagnostics.is_empty());
        let counts = |context: &CanonicalCheckerContext<'_>| {
            (
                context.store().type_len(),
                context.store().signature_len(),
                context.store().symbol_len(),
                context.store().mapper_len(),
            )
        };
        let mut expected_counts = None;
        for query_first in [false, true] {
            let mut context = context(&parsed, false);
            if query_first {
                prepare_optional_union(&mut context, &parsed);
            }
            context
                .check_source_file(FILE)
                .expect("cold optional constructor");
            assert!(context.diagnostics().is_empty());
            let read = parsed
                .arena
                .iter()
                .find_map(|(_, record)| {
                    let NodeData::VariableDeclaration(variable) = &record.data else {
                        return None;
                    };
                    let NodeData::Identifier(name) = &parsed.arena.get(variable.name)?.data else {
                        return None;
                    };
                    (name.text == "parameter").then_some(NodeRef::new(
                        parsed.arena.id(),
                        FILE,
                        variable.initializer?,
                    ))
                })
                .unwrap();
            let type_ = context
                .store()
                .type_node_links(read)
                .unwrap()
                .resolved_type
                .unwrap();
            assert_eq!(context.type_to_string(type_).unwrap(), "number | undefined");
            let warm = counts(&context);
            assert_eq!(*expected_counts.get_or_insert(warm), warm);
            prepare_optional_union(&mut context, &parsed);
            assert_eq!(counts(&context), warm);
            for _ in 0..2 {
                context.recheck_source_file(FILE).unwrap();
                assert!(context.diagnostics().is_empty());
                assert_eq!(counts(&context), warm);
                assert_eq!(
                    context.store().type_node_links(read).unwrap().resolved_type,
                    Some(type_)
                );
            }
        }
    }
}

fn prepare_optional_union(context: &mut CanonicalCheckerContext<'_>, parsed: &ParseResult) {
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
    let type_ = context.get_type_from_type_node(union).unwrap();
    assert_eq!(context.type_to_string(type_).unwrap(), "number | undefined");
}

#[test]
fn review_constructor_write_prepared_optional_parameter_accepts_undefined() {
    let source = concat!(
        "declare let cachedOptional: number | undefined; ",
        "class OptionalParameter { constructor(public value?: number) { ",
        "this.value = undefined; const after: undefined = this.value; } }",
    );
    for exact in [false, true] {
        let parsed = parse_source_file(source);
        assert!(parsed.diagnostics.is_empty());
        let mut context = context(&parsed, exact);
        prepare_optional_union(&mut context, &parsed);
        context
            .check_source_file(FILE)
            .expect("source after unrelated union query");
        assert!(
            context.diagnostics().is_empty(),
            "exact={exact}: {:?}",
            context.diagnostics()
        );
        let after = parsed
            .arena
            .iter()
            .find_map(|(_, record)| {
                let NodeData::VariableDeclaration(variable) = &record.data else {
                    return None;
                };
                let NodeData::Identifier(name) = &parsed.arena.get(variable.name)?.data else {
                    return None;
                };
                (name.text == "after").then_some(NodeRef::new(
                    parsed.arena.id(),
                    FILE,
                    variable.initializer?,
                ))
            })
            .unwrap();
        let after_type = context
            .store()
            .type_node_links(after)
            .unwrap()
            .resolved_type
            .unwrap();
        assert_eq!(context.type_to_string(after_type).unwrap(), "undefined");
        let warm = (
            context.store().type_len(),
            context.store().signature_len(),
            context.store().symbol_len(),
            context.store().mapper_len(),
        );
        for _ in 0..2 {
            context.recheck_source_file(FILE).unwrap();
            assert!(context.diagnostics().is_empty());
            assert_eq!(
                (
                    context.store().type_len(),
                    context.store().signature_len(),
                    context.store().symbol_len(),
                    context.store().mapper_len()
                ),
                warm
            );
            assert_eq!(
                context
                    .store()
                    .type_node_links(after)
                    .unwrap()
                    .resolved_type,
                Some(after_type)
            );
        }
    }
}

#[test]
fn review_constructor_alias_failure_also_occurs_without_a_write() {
    for write in ["", "this.value = 1;"] {
        let source = format!(
            "class AliasControl {{ value?: number; constructor() {{ \
             const self = this; {write} const alias = self.value; }} }}"
        );
        let parsed = parse_source_file(&source);
        assert!(parsed.diagnostics.is_empty());
        let mut context = context(&parsed, false);
        let result = context.check_source_file(FILE);
        assert!(
            matches!(
                result,
                Err(SourceCheckError::RelationUnavailable(
                    RelationUnavailable::UnsupportedStructuredType(_)
                ))
            ),
            "{source}: {result:?}"
        );
        assert!(context.diagnostics().is_empty());
    }
}
