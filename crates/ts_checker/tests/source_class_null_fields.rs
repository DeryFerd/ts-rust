use ts_ast::{FileId, NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalNameResolverOptions, CanonicalSourceFileFacts,
    CanonicalSourceLanguage, CheckFlags, EscapedName, SemanticSymbolId,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, IntrinsicBootstrapOptions, TypeData, TypeId,
};
use ts_options::ScriptTarget;
use ts_parser::{ParseResult, parse_source_file};

const FILE: FileId = FileId::new(202_410);

fn context(
    parsed: &ParseResult,
    strict_null_checks: bool,
    no_implicit_any: bool,
) -> CanonicalCheckerContext<'_> {
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            FILE,
            CanonicalSourceFileFacts::new(
                EscapedName::source("\"/project/class-null-fields.ts\""),
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
                strict_null_checks,
                ..IntrinsicBootstrapOptions::default()
            },
            strict_property_initialization: strict_null_checks,
            no_implicit_any,
            name_resolution: CanonicalNameResolverOptions {
                emit_target: ScriptTarget::Es2022,
                ..CanonicalNameResolverOptions::default()
            },
            ..CanonicalCheckerOptions::default()
        },
    )
    .unwrap()
}

struct Field<'a> {
    name: &'a str,
    declaration: NodeRef,
    name_node: NodeRef,
    initializer: NodeRef,
    annotation: Option<NodeRef>,
    is_static: bool,
    readonly: bool,
}

fn fields(parsed: &ParseResult) -> Vec<Field<'_>> {
    let reference = |node| NodeRef::new(parsed.arena.id(), FILE, node);
    let mut fields = parsed
        .arena
        .iter()
        .filter_map(|(node, record)| {
            let NodeData::PropertyDeclaration(property) = &record.data else {
                return None;
            };
            let NodeData::Identifier(name) = &parsed.arena.get(property.name)?.data else {
                return None;
            };
            let has_modifier = |kind| {
                property.modifiers.as_ref().is_some_and(|modifiers| {
                    modifiers.list.nodes.iter().any(|node| {
                        parsed
                            .arena
                            .get(*node)
                            .is_some_and(|node| node.kind == kind)
                    })
                })
            };
            Some(Field {
                name: &name.text,
                declaration: reference(node),
                name_node: reference(property.name),
                initializer: reference(property.initializer.unwrap()),
                annotation: property.type_.map(reference),
                is_static: has_modifier(SyntaxKind::StaticKeyword),
                readonly: has_modifier(SyntaxKind::ReadonlyKeyword),
            })
        })
        .collect::<Vec<_>>();
    fields.sort_by_key(|field| {
        parsed
            .arena
            .get(field.declaration.node)
            .unwrap()
            .range
            .start
    });
    fields
}

fn assert_fields(
    context: &mut CanonicalCheckerContext<'_>,
    fields: &[Field<'_>],
    expected: &[&str],
) -> Vec<(SemanticSymbolId, TypeId)> {
    assert_eq!(fields.len(), expected.len());
    let owner = context
        .store()
        .symbol_table(context.globals())
        .unwrap()
        .get_source("Model")
        .unwrap();
    let class = context.store().symbol(owner).unwrap();
    let instance_members = class.members().unwrap();
    let static_members = class.exports().unwrap();
    fields
        .iter()
        .zip(expected)
        .map(|(field, expected)| {
            let bound = context
                .file(FILE)
                .unwrap()
                .1
                .symbol(field.declaration)
                .unwrap();
            let symbol = context.store().get_merged_symbol(bound).unwrap();
            let (table, other_table) = if field.is_static {
                (static_members, instance_members)
            } else {
                (instance_members, static_members)
            };
            assert_eq!(
                context
                    .store()
                    .symbol_table(table)
                    .unwrap()
                    .get_source(field.name),
                Some(symbol),
            );
            assert_ne!(
                context
                    .store()
                    .symbol_table(other_table)
                    .unwrap()
                    .get_source(field.name),
                Some(symbol),
            );
            let record = context.store().symbol(symbol).unwrap();
            assert_eq!(record.parent(), Some(owner));
            assert_eq!(record.value_declaration(), Some(field.declaration));
            assert_eq!(
                record.check_flags().contains(CheckFlags::READONLY),
                field.readonly
            );
            assert_eq!(
                context.get_symbol_at_location(field.name_node).unwrap(),
                Some(symbol)
            );
            let type_ = context
                .store()
                .value_symbol_links(symbol)
                .unwrap()
                .resolved_type
                .unwrap();
            assert_eq!(
                context.get_type_at_location(field.name_node).unwrap(),
                type_
            );
            assert_field_types(context, field, type_, expected);
            (symbol, type_)
        })
        .collect()
}

fn assert_field_types(
    context: &mut CanonicalCheckerContext<'_>,
    field: &Field<'_>,
    type_: TypeId,
    expected: &str,
) {
    assert_eq!(
        context.type_to_string(type_).unwrap(),
        expected,
        "{}",
        field.name
    );
    let bootstrap = context.store().intrinsic_bootstrap().unwrap();
    let null_initializer = bootstrap.null_widening_type;
    match expected {
        "null" => assert_eq!(type_, bootstrap.null_type),
        "any" => assert_eq!(type_, bootstrap.any_type),
        "string" => assert_eq!(type_, bootstrap.string_type),
        "number" => assert_eq!(type_, bootstrap.number_type),
        "string | null" => {
            let TypeData::Union(union) = context.store().type_payload(type_).unwrap().data() else {
                panic!("the field annotation must retain its union");
            };
            assert_eq!(
                union.union.types,
                [bootstrap.null_type, bootstrap.string_type]
            );
        }
        _ => panic!("unexpected field type {expected}"),
    }
    assert_eq!(
        context.get_type_at_location(field.initializer).unwrap(),
        null_initializer
    );
    assert_eq!(
        context
            .store()
            .type_node_links(field.initializer)
            .unwrap()
            .resolved_type,
        Some(null_initializer),
    );
    if let Some(annotation) = field.annotation {
        assert_eq!(context.get_type_at_location(annotation).unwrap(), type_);
    }
}

fn assert_diagnostics(
    context: &CanonicalCheckerContext<'_>,
    expected: &[(NodeRef, u32, &str, &str)],
) {
    assert_eq!(
        context.diagnostics().len(),
        expected.len(),
        "{:?}",
        context.diagnostics()
    );
    for (diagnostic, &(node, code, first, second)) in
        context.diagnostics().as_slice().iter().zip(expected)
    {
        assert_eq!(diagnostic.node, Some(node));
        assert!(diagnostic.range_override.is_none());
        assert!(diagnostic.related_information.is_empty());
        assert_eq!(diagnostic.diagnostic.code(), code);
        assert_eq!(diagnostic.diagnostic.arguments, [first, second]);
        let message = match code {
            2322 => format!("Type '{first}' is not assignable to type '{second}'."),
            7008 => format!("Member '{first}' implicitly has an '{second}' type."),
            _ => panic!("unexpected diagnostic code {code}"),
        };
        assert_eq!(diagnostic.diagnostic.render().unwrap(), message);
    }
}

fn allocations(context: &CanonicalCheckerContext<'_>) -> [usize; 7] {
    let store = context.store();
    [
        store.type_len(),
        store.symbol_len(),
        store.signature_len(),
        store.mapper_len(),
        store.type_alias_len(),
        store.index_info_len(),
        store.symbol_store().symbol_table_len(),
    ]
}

fn assert_stable_replay(
    context: &mut CanonicalCheckerContext<'_>,
    fields: &[Field<'_>],
    expected: &[&str],
) {
    let identities = assert_fields(context, fields, expected);
    let warm = (
        allocations(context),
        context.store().relation_state_snapshot(),
        context.diagnostics().clone(),
    );
    for _ in 0..2 {
        context.check_source_file(FILE).unwrap();
        context.recheck_source_file(FILE).unwrap();
        assert_eq!(assert_fields(context, fields, expected), identities);
        assert!(
            context
                .source_file(FILE)
                .and_then(|source| context.store().source_file_links(source))
                .is_some_and(|links| links.type_checked)
        );
        assert_eq!(
            (
                allocations(context),
                context.store().relation_state_snapshot(),
                context.diagnostics().clone()
            ),
            warm,
        );
    }
}

#[test]
fn inferred_null_fields_follow_strict_null_checks_and_no_implicit_any() {
    let parsed = parse_source_file(concat!(
        "class Model {\n",
        "  value = null;\n",
        "  readonly fixed = null;\n",
        "  static value = null;\n",
        "  static readonly fixed = null;\n",
        "}\n",
    ));
    let fields = fields(&parsed);
    for strict_null_checks in [false, true] {
        for no_implicit_any in [false, true] {
            let mut context = context(&parsed, strict_null_checks, no_implicit_any);
            assert_eq!(
                context.options().intrinsic.strict_null_checks,
                strict_null_checks
            );
            context.check_source_file(FILE).unwrap();
            let expected = if strict_null_checks { "null" } else { "any" };
            let diagnostics = if !strict_null_checks && no_implicit_any {
                fields
                    .iter()
                    .map(|field| (field.name_node, 7008, field.name, "any"))
                    .collect::<Vec<_>>()
            } else {
                Vec::new()
            };
            assert_diagnostics(&context, &diagnostics);
            assert_stable_replay(&mut context, &fields, &[expected; 4]);
        }
    }
}

#[test]
fn annotated_null_fields_keep_their_annotations_on_both_class_sides() {
    let parsed = parse_source_file(concat!(
        "class Model {\n",
        "  value: null = null;\n",
        "  label: string | null = null;\n",
        "  static value: null = null;\n",
        "  static label: string | null = null;\n",
        "}\n",
    ));
    let fields = fields(&parsed);
    for strict_null_checks in [false, true] {
        let mut context = context(&parsed, strict_null_checks, true);
        context.check_source_file(FILE).unwrap();
        assert!(
            context.diagnostics().is_empty(),
            "{:?}",
            context.diagnostics()
        );
        let nullable = if strict_null_checks {
            "string | null"
        } else {
            "string"
        };
        assert_stable_replay(&mut context, &fields, &["null", nullable, "null", nullable]);
    }
}

#[test]
fn null_field_initializers_and_later_writes_report_exact_assignment_errors() {
    let parsed = parse_source_file(concat!(
        "declare const text: string;\n",
        "declare const count: number;\n",
        "class Model {\n",
        "  label: string = null;\n",
        "  static total: number = null;\n",
        "  value = null;\n",
        "  static value = null;\n",
        "  exact: null = null;\n",
        "  static exact: null = null;\n",
        "}\n",
        "const model = new Model();\n",
        "model.value = text;\n",
        "Model.value = count;\n",
        "model.exact = text;\n",
        "Model.exact = count;\n",
    ));
    let fields = fields(&parsed);
    let mut targets = parsed
        .arena
        .iter()
        .filter_map(|(_, record)| {
            let NodeData::BinaryExpression(assignment) = &record.data else {
                return None;
            };
            Some(NodeRef::new(parsed.arena.id(), FILE, assignment.left))
        })
        .collect::<Vec<_>>();
    targets.sort_by_key(|node| parsed.arena.get(node.node).unwrap().range.start);
    assert_eq!(targets.len(), 4);
    for strict_null_checks in [false, true] {
        let mut context = context(&parsed, strict_null_checks, false);
        context.check_source_file(FILE).unwrap();
        let mut diagnostics = if strict_null_checks {
            vec![
                (fields[0].name_node, 2322, "null", "string"),
                (fields[1].name_node, 2322, "null", "number"),
                (targets[0], 2322, "string", "null"),
                (targets[1], 2322, "number", "null"),
            ]
        } else {
            Vec::new()
        };
        diagnostics.extend([
            (targets[2], 2322, "string", "null"),
            (targets[3], 2322, "number", "null"),
        ]);
        assert_diagnostics(&context, &diagnostics);
        let inferred = if strict_null_checks { "null" } else { "any" };
        assert_stable_replay(
            &mut context,
            &fields,
            &["string", "number", inferred, inferred, "null", "null"],
        );
    }
}
