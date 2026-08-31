use ts_ast::{FileId, NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalNameResolverOptions, CanonicalSourceFileFacts,
    CanonicalSourceLanguage, CheckFlags, EscapedName, SemanticSymbolId,
};
use ts_checker::semantic::{
    AssignmentSyntaxRole, AssignmentUnsupported, CanonicalCheckerContext,
    CanonicalCheckerDiagnostics, CanonicalCheckerOptions, IntrinsicBootstrapOptions,
    RelationStateSnapshot, SourceCheckError, SourceFileLinks, SymbolNodeLinks, TypeData, TypeId,
    TypeNodeLinks, UnsupportedSourceSyntax, ValueSymbolLinks,
};
use ts_options::ScriptTarget;
use ts_parser::{ParseResult, parse_source_file};

const FILE: FileId = FileId::new(202_610);

fn context(parsed: &ParseResult) -> CanonicalCheckerContext<'_> {
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            FILE,
            CanonicalSourceFileFacts::new(
                EscapedName::source("\"/project/class-property-assignments.ts\""),
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
                exact_optional_property_types: false,
            },
            strict_property_initialization: true,
            no_implicit_any: true,
            name_resolution: CanonicalNameResolverOptions {
                emit_target: ScriptTarget::Es2022,
                ..CanonicalNameResolverOptions::default()
            },
            ..CanonicalCheckerOptions::default()
        },
    )
    .unwrap()
}

fn symbol(context: &CanonicalCheckerContext<'_>, node: NodeRef) -> SemanticSymbolId {
    let raw = context.file(FILE).unwrap().1.symbol(node).unwrap();
    context.store().get_merged_symbol(raw).unwrap()
}

fn class_node(parsed: &ParseResult) -> NodeRef {
    parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            matches!(record.data, NodeData::ClassDeclaration(_)).then_some(NodeRef::new(
                parsed.arena.id(),
                FILE,
                node,
            ))
        })
        .unwrap()
}

fn model_variable(parsed: &ParseResult) -> NodeRef {
    parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            let NodeData::VariableDeclaration(variable) = &record.data else {
                return None;
            };
            let NodeData::Identifier(name) = &parsed.arena.get(variable.name)?.data else {
                return None;
            };
            (name.text == "model").then_some(NodeRef::new(parsed.arena.id(), FILE, node))
        })
        .unwrap()
}

struct Field<'a> {
    name: &'a str,
    declaration: NodeRef,
    name_node: NodeRef,
    is_static: bool,
    readonly: bool,
}

fn fields(parsed: &ParseResult) -> Vec<Field<'_>> {
    let mut result = parsed
        .arena
        .iter()
        .filter_map(|(node, record)| {
            let NodeData::PropertyDeclaration(property) = &record.data else {
                return None;
            };
            let NodeData::Identifier(name) = &parsed.arena.get(property.name)?.data else {
                return None;
            };
            let has_modifier =
                |kind| {
                    property.modifiers.as_ref().is_some_and(|modifiers| {
                        modifiers.list.nodes.iter().any(|&node| {
                            parsed.arena.get(node).is_some_and(|node| node.kind == kind)
                        })
                    })
                };
            Some(Field {
                name: &name.text,
                declaration: NodeRef::new(parsed.arena.id(), FILE, node),
                name_node: NodeRef::new(parsed.arena.id(), FILE, property.name),
                is_static: has_modifier(SyntaxKind::StaticKeyword),
                readonly: has_modifier(SyntaxKind::ReadonlyKeyword),
            })
        })
        .collect::<Vec<_>>();
    result.sort_by_key(|field| {
        parsed
            .arena
            .get(field.declaration.node)
            .unwrap()
            .range
            .start
    });
    result
}

#[derive(Clone, Copy)]
struct AssignmentNodes {
    expression: NodeRef,
    left: NodeRef,
    receiver: NodeRef,
    name: NodeRef,
    right: NodeRef,
}

fn assignments(parsed: &ParseResult) -> Vec<AssignmentNodes> {
    let reference = |node| NodeRef::new(parsed.arena.id(), FILE, node);
    let mut result = parsed
        .arena
        .iter()
        .filter_map(|(node, record)| {
            let NodeData::BinaryExpression(binary) = &record.data else {
                return None;
            };
            let NodeData::PropertyAccessExpression(access) = &parsed.arena.get(binary.left)?.data
            else {
                return None;
            };
            Some(AssignmentNodes {
                expression: reference(node),
                left: reference(binary.left),
                receiver: reference(access.expression),
                name: reference(access.name),
                right: reference(binary.right),
            })
        })
        .collect::<Vec<_>>();
    result.sort_by_key(|assignment| {
        parsed
            .arena
            .get(assignment.expression.node)
            .unwrap()
            .range
            .start
    });
    result
}

fn assert_fields(
    context: &mut CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    fields: &[Field<'_>],
    expected: &[&str],
) -> Vec<(SemanticSymbolId, TypeId)> {
    assert_eq!(fields.len(), expected.len());
    let owner = symbol(context, class_node(parsed));
    let class = context.store().symbol(owner).unwrap();
    let instance_members = class.members().unwrap();
    let static_members = class.exports().unwrap();
    fields
        .iter()
        .zip(expected)
        .map(|(field, expected)| {
            let property = symbol(context, field.declaration);
            let table = if field.is_static {
                static_members
            } else {
                instance_members
            };
            assert_eq!(
                context
                    .store()
                    .symbol_table(table)
                    .unwrap()
                    .get_source(field.name),
                Some(property)
            );
            let record = context.store().symbol(property).unwrap();
            assert_eq!(record.parent(), Some(owner));
            assert_eq!(record.value_declaration(), Some(field.declaration));
            assert_eq!(record.declarations(), Some(&[field.declaration][..]));
            assert_eq!(
                record.check_flags().contains(CheckFlags::READONLY),
                field.readonly
            );
            let type_ = context
                .store()
                .value_symbol_links(property)
                .unwrap()
                .resolved_type
                .unwrap();
            assert_eq!(context.type_to_string(type_).unwrap(), *expected);
            assert_eq!(
                context.get_symbol_at_location(field.name_node).unwrap(),
                Some(property)
            );
            assert_eq!(
                context.get_type_at_location(field.name_node).unwrap(),
                type_
            );
            (property, type_)
        })
        .collect()
}

fn assert_assignments(
    context: &mut CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    fields: &[Field<'_>],
    identities: &[(SemanticSymbolId, TypeId)],
    assignments: &[AssignmentNodes],
    rhs_types: &[TypeId],
) {
    assert_eq!(assignments.len(), rhs_types.len());
    let owner = symbol(context, class_node(parsed));
    let model = symbol(context, model_variable(parsed));
    let instance_type = context
        .store()
        .declared_type_links(owner)
        .unwrap()
        .declared_type
        .unwrap();
    let static_type = context
        .store()
        .value_symbol_links(owner)
        .unwrap()
        .resolved_type
        .unwrap();
    let error_type = context.store().intrinsic_bootstrap().unwrap().error_type;
    assert_eq!(
        context
            .store()
            .value_symbol_links(model)
            .unwrap()
            .resolved_type,
        Some(instance_type)
    );
    assert_ne!(instance_type, static_type);
    for (assignment, &rhs_type) in assignments.iter().zip(rhs_types) {
        let receiver_symbol = context
            .get_symbol_at_location(assignment.receiver)
            .unwrap()
            .unwrap();
        let is_static = receiver_symbol == owner;
        assert_eq!(receiver_symbol, if is_static { owner } else { model });
        assert_eq!(
            context.get_type_at_location(assignment.receiver).unwrap(),
            if is_static {
                static_type
            } else {
                instance_type
            }
        );
        let NodeData::Identifier(name) = &parsed.arena.get(assignment.name.node).unwrap().data
        else {
            panic!("write target must retain its real property name")
        };
        let index = fields
            .iter()
            .position(|field| field.name == name.text && field.is_static == is_static)
            .unwrap();
        let (property, declared_type) = identities[index];
        assert_eq!(
            context.get_symbol_at_location(assignment.name).unwrap(),
            Some(property)
        );
        assert_eq!(
            context
                .store()
                .symbol_node_links(assignment.left)
                .unwrap()
                .resolved_symbol,
            Some(property)
        );
        assert_eq!(
            context.get_type_at_location(assignment.left).unwrap(),
            if fields[index].readonly {
                error_type
            } else {
                declared_type
            }
        );
        assert_eq!(
            context.get_type_at_location(assignment.right).unwrap(),
            rhs_type
        );
        assert_eq!(
            context.get_type_at_location(assignment.expression).unwrap(),
            rhs_type
        );
        assert_eq!(
            context
                .store()
                .value_symbol_links(property)
                .unwrap()
                .resolved_type,
            Some(declared_type)
        );
    }
}

#[derive(Debug, Eq, PartialEq)]
struct Snapshot {
    counts: [usize; 7],
    relations: RelationStateSnapshot,
    diagnostics: CanonicalCheckerDiagnostics,
    source: SourceFileLinks,
    nodes: Vec<(NodeRef, Option<TypeNodeLinks>, Option<SymbolNodeLinks>)>,
    fields: Vec<Option<ValueSymbolLinks>>,
}

fn snapshot(
    context: &CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    fields: &[(SemanticSymbolId, TypeId)],
) -> Snapshot {
    let store = context.store();
    let source = store
        .source_file_links(context.source_file(FILE).unwrap())
        .unwrap()
        .clone();
    assert!(source.type_checked);
    Snapshot {
        counts: [
            store.type_len(),
            store.symbol_len(),
            store.signature_len(),
            store.mapper_len(),
            store.type_alias_len(),
            store.index_info_len(),
            store.symbol_store().symbol_table_len(),
        ],
        relations: store.relation_state_snapshot(),
        diagnostics: context.diagnostics().clone(),
        source,
        nodes: parsed
            .arena
            .iter()
            .map(|(node, _)| {
                let node = NodeRef::new(parsed.arena.id(), FILE, node);
                (
                    node,
                    store.type_node_links(node).cloned(),
                    store.symbol_node_links(node).cloned(),
                )
            })
            .collect(),
        fields: fields
            .iter()
            .map(|&(symbol, _)| store.value_symbol_links(symbol).cloned())
            .collect(),
    }
}

#[test]
fn own_instance_and_static_writes_keep_declared_types_in_both_query_orders() {
    let parsed = parse_source_file(concat!(
        "declare const text: string;\n",
        "declare const count: number;\n",
        "class Model {\n",
        "  value: string | null = null;\n",
        "  static value: string | null = null;\n",
        "  total = 0;\n",
        "  static total = 0;\n",
        "}\n",
        "const model = new Model();\n",
        "model.value = text;\n",
        "Model.value = text;\n",
        "model.value = null;\n",
        "Model.value = null;\n",
        "model.total = count;\n",
        "Model.total = count;\n",
    ));
    let fields = fields(&parsed);
    let assignments = assignments(&parsed);
    assert_eq!(assignments.len(), 6);
    let expected = ["string | null", "string | null", "number", "number"];
    for query_first in [false, true] {
        let mut context = context(&parsed);
        if query_first {
            context
                .get_type_at_location(assignments[0].expression)
                .unwrap();
        } else {
            context.check_source_file(FILE).unwrap();
        }
        assert!(
            context.diagnostics().is_empty(),
            "{:?}",
            context.diagnostics()
        );
        let identities = assert_fields(&mut context, &parsed, &fields, &expected);
        assert_ne!(identities[0].0, identities[1].0);
        assert_ne!(identities[2].0, identities[3].0);
        let bootstrap = context.store().intrinsic_bootstrap().unwrap();
        let rhs = [
            bootstrap.string_type,
            bootstrap.string_type,
            bootstrap.null_widening_type,
            bootstrap.null_widening_type,
            bootstrap.number_type,
            bootstrap.number_type,
        ];
        let TypeData::Union(nullable) = context
            .store()
            .type_payload(identities[0].1)
            .unwrap()
            .data()
        else {
            panic!("the nullable field must keep its declared union")
        };
        assert_eq!(
            nullable.union.types,
            [bootstrap.null_type, bootstrap.string_type]
        );
        assert_assignments(
            &mut context,
            &parsed,
            &fields,
            &identities,
            &assignments,
            &rhs,
        );
        let warm = snapshot(&context, &parsed, &identities);
        context.recheck_source_file(FILE).unwrap();
        assert_eq!(
            assert_fields(&mut context, &parsed, &fields, &expected),
            identities
        );
        assert_assignments(
            &mut context,
            &parsed,
            &fields,
            &identities,
            &assignments,
            &rhs,
        );
        assert_eq!(snapshot(&context, &parsed, &identities), warm);
    }
}

#[test]
fn bad_and_readonly_class_writes_keep_exact_errors_and_expression_types() {
    let parsed = parse_source_file(concat!(
        "declare const count: number;\n",
        "class Model {\n",
        "  value!: string;\n",
        "  static value: string;\n",
        "  readonly fixed: string = '';\n",
        "  static readonly fixed: string = '';\n",
        "}\n",
        "const model = new Model();\n",
        "model.value = count;\n",
        "Model.value = count;\n",
        "model.fixed = count;\n",
        "Model.fixed = count;\n",
    ));
    let fields = fields(&parsed);
    let assignments = assignments(&parsed);
    assert_eq!(assignments.len(), 4);
    for query_first in [false, true] {
        let mut context = context(&parsed);
        if query_first {
            context
                .get_type_at_location(assignments[0].expression)
                .unwrap();
        } else {
            context.check_source_file(FILE).unwrap();
        }
        let diagnostics = context.diagnostics().as_slice();
        assert_eq!(diagnostics.len(), 4, "{diagnostics:?}");
        for (index, diagnostic) in diagnostics.iter().enumerate() {
            assert_eq!(diagnostic.range_override, None);
            assert!(diagnostic.related_information.is_empty());
            if index < 2 {
                assert_eq!(diagnostic.node, Some(assignments[index].left));
                assert_eq!(diagnostic.diagnostic.code(), 2322);
                assert_eq!(diagnostic.diagnostic.arguments, ["number", "string"]);
                assert_eq!(
                    diagnostic.diagnostic.render().unwrap(),
                    "Type 'number' is not assignable to type 'string'."
                );
            } else {
                assert_eq!(diagnostic.node, Some(assignments[index].name));
                assert_eq!(diagnostic.diagnostic.code(), 2540);
                assert_eq!(diagnostic.diagnostic.arguments, ["fixed"]);
                assert_eq!(
                    diagnostic.diagnostic.render().unwrap(),
                    "Cannot assign to 'fixed' because it is a read-only property."
                );
            }
        }
        let identities = assert_fields(&mut context, &parsed, &fields, &["string"; 4]);
        let number = context.store().intrinsic_bootstrap().unwrap().number_type;
        assert_assignments(
            &mut context,
            &parsed,
            &fields,
            &identities,
            &assignments,
            &[number; 4],
        );
        let warm = snapshot(&context, &parsed, &identities);
        context.recheck_source_file(FILE).unwrap();
        assert_eq!(
            assert_fields(&mut context, &parsed, &fields, &["string"; 4]),
            identities
        );
        assert_assignments(
            &mut context,
            &parsed,
            &fields,
            &identities,
            &assignments,
            &[number; 4],
        );
        assert_eq!(snapshot(&context, &parsed, &identities), warm);
    }
}

#[test]
fn other_class_write_forms_keep_their_exact_unsupported_boundary() {
    enum Boundary {
        Assignment,
        Property,
    }
    for (source, boundary) in [
        (
            concat!(
                "class Base { value = 0; }\n",
                "class Derived extends Base {}\n",
                "declare const model: Derived;\n",
                "model.value = 1;\n",
            ),
            Boundary::Assignment,
        ),
        (
            concat!(
                "class Model<T> { value!: T; }\n",
                "declare const model: Model<string>;\n",
                "model.value = 'x';\n",
            ),
            Boundary::Assignment,
        ),
        (
            concat!(
                "class Model { get value(): number { return 1; } }\n",
                "declare const model: Model;\n",
                "model.value = 1;\n",
            ),
            Boundary::Property,
        ),
        (
            concat!(
                "class Model { private value = 0; }\n",
                "declare const model: Model;\n",
                "model.value = 1;\n",
            ),
            Boundary::Property,
        ),
        (
            concat!(
                "class Model { value = 0; }\n",
                "declare const model: Model;\n",
                "model.value += 1;\n",
            ),
            Boundary::Assignment,
        ),
    ] {
        let parsed = parse_source_file(source);
        let mut context = context(&parsed);
        let assignments = assignments(&parsed);
        assert_eq!(assignments.len(), 1);
        let write = assignments[0];
        let expected = SourceCheckError::Unsupported(match boundary {
            Boundary::Assignment => {
                UnsupportedSourceSyntax::Assignment(AssignmentUnsupported::Syntax {
                    node: write.left,
                    kind: SyntaxKind::PropertyAccessExpression,
                    role: AssignmentSyntaxRole::LeftHandSide,
                })
            }
            Boundary::Property => UnsupportedSourceSyntax::Property(write.left),
        });
        for _ in 0..2 {
            assert_eq!(context.check_source_file(FILE), Err(expected), "{source}");
            for node in [write.expression, write.left] {
                assert_eq!(
                    context
                        .store()
                        .type_node_links(node)
                        .and_then(|links| links.resolved_type),
                    None,
                    "{source}"
                );
            }
            assert!(
                context
                    .store()
                    .source_file_links(context.source_file(FILE).unwrap())
                    .is_none_or(|links| !links.type_checked),
                "{source}"
            );
        }
    }
}

#[test]
fn later_read_narrows_without_changing_the_declared_nullable_field() {
    let parsed = parse_source_file(
        "declare const text: string; class Model { value: string | null = null; } const model = new Model(); model.value = text; const after: string = model.value;",
    );
    let fields = fields(&parsed);
    let assignments = assignments(&parsed);
    assert_eq!(fields.len(), 1);
    assert_eq!(assignments.len(), 1);
    let (after, read, name) = parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            let NodeData::VariableDeclaration(variable) = &record.data else {
                return None;
            };
            let NodeData::Identifier(name) = &parsed.arena.get(variable.name)?.data else {
                return None;
            };
            if name.text != "after" {
                return None;
            }
            let read = variable.initializer?;
            let NodeData::PropertyAccessExpression(property) = &parsed.arena.get(read)?.data else {
                return None;
            };
            Some((
                NodeRef::new(parsed.arena.id(), FILE, node),
                NodeRef::new(parsed.arena.id(), FILE, read),
                NodeRef::new(parsed.arena.id(), FILE, property.name),
            ))
        })
        .unwrap();
    let assert_narrowed = |context: &mut CanonicalCheckerContext<'_>| {
        assert!(
            context.diagnostics().is_empty(),
            "{:?}",
            context.diagnostics()
        );
        let identities = assert_fields(context, &parsed, &fields, &["string | null"]);
        let bootstrap = context.store().intrinsic_bootstrap().unwrap();
        let string = bootstrap.string_type;
        let TypeData::Union(nullable) = context
            .store()
            .type_payload(identities[0].1)
            .unwrap()
            .data()
        else {
            panic!("the field declaration must keep its nullable union")
        };
        assert_eq!(nullable.union.types, [bootstrap.null_type, string]);
        assert_assignments(
            context,
            &parsed,
            &fields,
            &identities,
            &assignments,
            &[string],
        );
        assert_eq!(context.get_type_at_location(read).unwrap(), string);
        assert_eq!(
            context.store().type_node_links(read).unwrap().resolved_type,
            Some(string)
        );
        assert_eq!(
            context.get_symbol_at_location(name).unwrap(),
            Some(identities[0].0)
        );
        assert_eq!(
            context
                .store()
                .symbol_node_links(read)
                .unwrap()
                .resolved_symbol,
            Some(identities[0].0)
        );
        assert_eq!(
            context
                .store()
                .value_symbol_links(symbol(context, after))
                .unwrap()
                .resolved_type,
            Some(string)
        );
        identities
    };
    for query_first in [false, true] {
        let mut context = context(&parsed);
        if query_first {
            context.get_type_at_location(read).unwrap();
        } else {
            context.check_source_file(FILE).unwrap();
        }
        let identities = assert_narrowed(&mut context);
        let warm = snapshot(&context, &parsed, &identities);
        context.recheck_source_file(FILE).unwrap();
        assert_eq!(assert_narrowed(&mut context), identities);
        assert_eq!(snapshot(&context, &parsed, &identities), warm);
    }
}
