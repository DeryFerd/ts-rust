use ts_ast::{FileId, NodeData, NodeId, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalNameResolverOptions, CanonicalSourceFileFacts,
    CanonicalSourceLanguage, EscapedName, SemanticSymbolId,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, IntrinsicBootstrapOptions, TypeData, TypeId,
};
use ts_options::ScriptTarget;
use ts_parser::{ParseResult, parse_source_file};

const FILE: FileId = FileId::new(204_002);

fn context(parsed: &ParseResult) -> CanonicalCheckerContext<'_> {
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            FILE,
            CanonicalSourceFileFacts::new(
                EscapedName::source("\"/project/in-operators.ts\""),
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
            no_implicit_any: true,
            no_emit: true,
            name_resolution: CanonicalNameResolverOptions {
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

fn membership(parsed: &ParseResult) -> [NodeRef; 3] {
    let expressions = parsed
        .arena
        .iter()
        .filter_map(|(id, record)| {
            let NodeData::BinaryExpression(binary) = &record.data else {
                return None;
            };
            (parsed.arena.get(binary.operator_token)?.kind == SyntaxKind::InKeyword).then_some([
                node(parsed, id),
                node(parsed, binary.left),
                node(parsed, binary.right),
            ])
        })
        .collect::<Vec<_>>();
    let [expression] = expressions.as_slice() else {
        panic!("each source has one membership expression")
    };
    for operand in &expression[1..] {
        assert_eq!(
            parsed.arena.get(operand.node).unwrap().parent,
            Some(expression[0].node)
        );
    }
    *expression
}

fn declaration_symbol(
    context: &CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    expected: &str,
) -> SemanticSymbolId {
    let declaration = parsed
        .arena
        .iter()
        .find_map(|(id, record)| {
            let name = match &record.data {
                NodeData::ParameterDeclaration(parameter) => parameter.name,
                NodeData::TypeAliasDeclaration(alias) => alias.name,
                _ => return None,
            };
            matches!(&parsed.arena.get(name)?.data,
                NodeData::Identifier(name) if name.text == expected)
            .then_some(node(parsed, id))
        })
        .unwrap_or_else(|| panic!("missing declaration {expected}"));
    let raw = context.file(FILE).unwrap().1.symbol(declaration).unwrap();
    context.store().get_merged_symbol(raw).unwrap()
}

fn checked_type(context: &CanonicalCheckerContext<'_>, node: NodeRef) -> TypeId {
    context
        .store()
        .type_node_links(node)
        .and_then(|links| links.resolved_type)
        .unwrap_or_else(|| panic!("missing checked type for {node:?}"))
}

fn assert_parameter_read(
    context: &mut CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    read: NodeRef,
    name: &str,
) {
    let symbol = declaration_symbol(context, parsed, name);
    assert_eq!(context.get_symbol_at_location(read).unwrap(), Some(symbol));
    assert_eq!(
        Some(checked_type(context, read)),
        context
            .store()
            .value_symbol_links(symbol)
            .unwrap()
            .resolved_type
    );
}

fn counts(context: &CanonicalCheckerContext<'_>) -> [usize; 7] {
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

fn check_query_orders(
    parsed: &ParseResult,
    queries: &[NodeRef],
    inspect: impl Fn(&mut CanonicalCheckerContext<'_>),
) {
    for source_first in [false, true] {
        for reverse in [false, true] {
            let mut context = context(parsed);
            let source = context.source_file(FILE).unwrap();
            assert!(
                !context
                    .store()
                    .source_file_links(source)
                    .is_some_and(|links| links.type_checked)
            );
            let mut queries = queries.to_vec();
            if reverse {
                queries.reverse();
            }
            if source_first {
                context.check_source_file(FILE).unwrap();
            }
            let observed = queries
                .iter()
                .map(|&query| {
                    (
                        context.get_type_at_location(query).unwrap(),
                        context.get_symbol_at_location(query).unwrap(),
                    )
                })
                .collect::<Vec<_>>();
            inspect(&mut context);
            assert!(
                context
                    .store()
                    .source_file_links(source)
                    .unwrap()
                    .type_checked
            );
            let warm_counts = counts(&context);
            let diagnostics = context.diagnostics().clone();
            let links = queries
                .iter()
                .map(|&query| {
                    (
                        context.store().node_links(query).cloned(),
                        context.store().type_node_links(query).cloned(),
                        context.store().symbol_node_links(query).cloned(),
                    )
                })
                .collect::<Vec<_>>();
            for _ in 0..2 {
                context.check_source_file(FILE).unwrap();
                context.recheck_source_file(FILE).unwrap();
                for ((&query, &identity), expected_links) in
                    queries.iter().zip(&observed).zip(&links).rev()
                {
                    assert_eq!(
                        (
                            context.get_type_at_location(query).unwrap(),
                            context.get_symbol_at_location(query).unwrap(),
                        ),
                        identity,
                    );
                    assert_eq!(
                        &(
                            context.store().node_links(query).cloned(),
                            context.store().type_node_links(query).cloned(),
                            context.store().symbol_node_links(query).cloned(),
                        ),
                        expected_links,
                    );
                }
                assert_eq!(counts(&context), warm_counts);
                assert_eq!(context.diagnostics(), &diagnostics);
            }
        }
    }
}

fn assert_diagnostics(context: &CanonicalCheckerContext<'_>, expected: &[(u32, NodeRef, &[&str])]) {
    assert_eq!(context.diagnostics().len(), expected.len());
    for (diagnostic, &(code, node, arguments)) in
        context.diagnostics().as_slice().iter().zip(expected)
    {
        assert_eq!(diagnostic.diagnostic.code(), code);
        assert_eq!(diagnostic.node, Some(node));
        assert!(diagnostic.range_override.is_none());
        assert_eq!(diagnostic.diagnostic.arguments, arguments);
        assert!(diagnostic.diagnostic.details.is_empty());
        assert!(diagnostic.related_information.is_empty());
    }
}

#[test]
fn in_operators_check_literal_and_dynamic_key_types_with_real_receivers() {
    for (source, key_display) in [
        (
            "function hasValue(box: { value?: string }): boolean { return \"value\" in box; }",
            "\"value\"",
        ),
        (
            "function hasValue(key: string, box: { value?: string }): boolean { return key in box; }",
            "string",
        ),
        (
            "function hasValue(key: number, box: { value?: string }): boolean { return key in box; }",
            "number",
        ),
        (
            "function hasValue(key: symbol, box: { value?: string }): boolean { return key in box; }",
            "symbol",
        ),
        (
            "function hasValue(scope: { env: { value?: string } }): boolean { return \"value\" in scope.env; }",
            "\"value\"",
        ),
    ] {
        let parsed = parse_source_file(source);
        let [binary, left, right] = membership(&parsed);
        check_query_orders(&parsed, &[binary, left, right], |context| {
            assert!(context.diagnostics().is_empty());
            let boolean = context.store().intrinsic_bootstrap().unwrap().boolean_type;
            assert_eq!(checked_type(context, binary), boolean);
            assert_eq!(
                context.type_to_string(checked_type(context, left)).unwrap(),
                key_display
            );
            let right_type = checked_type(context, right);
            let TypeData::Object(_) = context.store().type_payload(right_type).unwrap().data()
            else {
                panic!("the checked right operand retains the written object type")
            };
            if key_display != "\"value\"" {
                assert_parameter_read(context, &parsed, left, "key");
            }
            match &parsed.arena.get(right.node).unwrap().data {
                NodeData::Identifier(_) => assert_parameter_read(context, &parsed, right, "box"),
                NodeData::PropertyAccessExpression(access) => {
                    assert_parameter_read(
                        context,
                        &parsed,
                        node(&parsed, access.expression),
                        "scope",
                    );
                    let property = context.get_symbol_at_location(right).unwrap().unwrap();
                    assert_eq!(
                        context
                            .store()
                            .value_symbol_links(property)
                            .unwrap()
                            .resolved_type,
                        Some(right_type)
                    );
                }
                _ => panic!("each receiver is a real parameter or its property"),
            }
        });
    }
}

#[test]
fn in_operators_keep_native_operand_diagnostics_and_boolean_recovery() {
    for (source, invalid_left, invalid_right) in [
        (
            "function hasValue(box: number): boolean { return \"value\" in box; }",
            false,
            true,
        ),
        (
            "function hasValue(key: boolean, box: { value: string }): boolean { return key in box; }",
            true,
            false,
        ),
        (
            "function hasValue(key: boolean, box: number): boolean { return key in box; }",
            true,
            true,
        ),
    ] {
        let parsed = parse_source_file(source);
        let [binary, left, right] = membership(&parsed);
        check_query_orders(&parsed, &[binary, left, right], |context| {
            let bootstrap = context.store().intrinsic_bootstrap().unwrap();
            assert_eq!(checked_type(context, binary), bootstrap.boolean_type);
            let mut expected = Vec::new();
            if invalid_left {
                assert_eq!(checked_type(context, left), bootstrap.boolean_type);
                expected.push((
                    2322,
                    left,
                    ["boolean", "string | number | symbol"].as_slice(),
                ));
            }
            if invalid_right {
                assert_eq!(checked_type(context, right), bootstrap.number_type);
                expected.push((2322, right, ["number", "object"].as_slice()));
            }
            assert_diagnostics(context, &expected);
            assert_parameter_read(context, &parsed, right, "box");
            if invalid_left {
                assert_parameter_read(context, &parsed, left, "key");
            }
        });
    }
}

fn property_reads(parsed: &ParseResult) -> Vec<[NodeRef; 3]> {
    let mut reads = parsed
        .arena
        .iter()
        .filter_map(|(id, record)| {
            let NodeData::PropertyAccessExpression(access) = &record.data else {
                return None;
            };
            Some([
                node(parsed, id),
                node(parsed, access.expression),
                node(parsed, access.name),
            ])
        })
        .collect::<Vec<_>>();
    reads.sort_by_key(|read| parsed.arena.get(read[0].node).unwrap().range.start);
    reads
}

#[test]
fn in_conditions_keep_both_selected_union_members_and_reject_opposite_reads() {
    for valid in [true, false] {
        let (present, absent) = if valid {
            ("value", "other")
        } else {
            ("other", "value")
        };
        let source = format!(
            "type HasValue = {{ value: string }};\n\
             type HasOther = {{ other: number }};\n\
             function read(box: HasValue | HasOther): string | number {{\n\
               if (\"value\" in box) {{ return box.{present}; }}\n\
               else {{ return box.{absent}; }}\n\
             }}\n"
        );
        let parsed = parse_source_file(&source);
        let [binary, left, right] = membership(&parsed);
        let reads = property_reads(&parsed);
        let [present, absent] = reads.as_slice() else {
            panic!("the source retains one member read on each branch")
        };
        let queries = [binary, left, right]
            .into_iter()
            .chain(reads.iter().flat_map(|read| *read))
            .collect::<Vec<_>>();
        check_query_orders(&parsed, &queries, |context| {
            let union = checked_type(context, right);
            let TypeData::Union(data) = context.store().type_payload(union).unwrap().data() else {
                panic!("the condition checks the original union")
            };
            let constituents = data.union.types.clone();
            assert_eq!(constituents.len(), 2);
            assert_parameter_read(context, &parsed, right, "box");
            for (read, alias) in [(present, "HasValue"), (absent, "HasOther")] {
                let symbol = declaration_symbol(context, &parsed, alias);
                let selected = context
                    .store()
                    .type_alias_links(symbol)
                    .unwrap()
                    .declared_type
                    .unwrap();
                assert!(constituents.contains(&selected));
                assert_eq!(checked_type(context, read[1]), selected);
                assert_eq!(
                    context.get_symbol_at_location(read[1]).unwrap(),
                    Some(declaration_symbol(context, &parsed, "box"))
                );
            }
            let (boolean, string, number, error) = {
                let bootstrap = context.store().intrinsic_bootstrap().unwrap();
                (
                    bootstrap.boolean_type,
                    bootstrap.string_type,
                    bootstrap.number_type,
                    bootstrap.error_type,
                )
            };
            assert_eq!(checked_type(context, binary), boolean);
            if valid {
                assert_diagnostics(context, &[]);
                assert_eq!(checked_type(context, present[0]), string);
                assert_eq!(checked_type(context, absent[0]), number);
                for read in reads.iter() {
                    let property = context.get_symbol_at_location(read[0]).unwrap().unwrap();
                    assert_eq!(
                        context.get_symbol_at_location(read[2]).unwrap(),
                        Some(property)
                    );
                    assert_eq!(
                        context
                            .store()
                            .value_symbol_links(property)
                            .unwrap()
                            .resolved_type,
                        Some(checked_type(context, read[0]))
                    );
                }
            } else {
                assert_diagnostics(
                    context,
                    &[
                        (2339, present[2], &["other", "HasValue"]),
                        (2339, absent[2], &["value", "HasOther"]),
                    ],
                );
                for read in reads.iter() {
                    assert_eq!(checked_type(context, read[0]), error);
                    assert_eq!(context.get_symbol_at_location(read[0]).unwrap(), None);
                }
            }
        });
    }
}

#[test]
fn optional_in_properties_keep_the_original_union_on_the_absent_branch() {
    let parsed = parse_source_file(concat!(
        "type MaybeValue = { value?: string; marker: number };\n",
        "type HasOther = { marker: string };\n",
        "function read(box: MaybeValue | HasOther): string | number {\n",
        "  if (\"value\" in box) { return box.marker; }\n",
        "  else { return box.marker; }\n",
        "}\n",
    ));
    let [binary, left, right] = membership(&parsed);
    let reads = property_reads(&parsed);
    let [present, absent] = reads.as_slice() else {
        panic!("the source retains one member read on each branch")
    };
    let queries = [binary, left, right]
        .into_iter()
        .chain(reads.iter().flat_map(|read| *read))
        .collect::<Vec<_>>();
    check_query_orders(&parsed, &queries, |context| {
        assert_diagnostics(context, &[]);
        assert_parameter_read(context, &parsed, right, "box");
        let original = checked_type(context, right);
        let TypeData::Union(data) = context.store().type_payload(original).unwrap().data() else {
            panic!("the condition checks the two original object types")
        };
        assert_eq!(data.union.types.len(), 2);
        let alias = declaration_symbol(context, &parsed, "MaybeValue");
        let selected = context
            .store()
            .type_alias_links(alias)
            .unwrap()
            .declared_type
            .unwrap();
        assert!(data.union.types.contains(&selected));
        assert_eq!(checked_type(context, present[1]), selected);
        assert_eq!(checked_type(context, absent[1]), original);
        let bootstrap = context.store().intrinsic_bootstrap().unwrap();
        assert_eq!(checked_type(context, binary), bootstrap.boolean_type);
        assert_eq!(checked_type(context, present[0]), bootstrap.number_type);
        let mut expected = [bootstrap.string_type, bootstrap.number_type];
        expected.sort_unstable();
        let TypeData::Union(data) = context
            .store()
            .type_payload(checked_type(context, absent[0]))
            .unwrap()
            .data()
        else {
            panic!("an absent optional property does not remove its object type")
        };
        assert_eq!(data.union.types, expected);
        let parameter = declaration_symbol(context, &parsed, "box");
        for read in &reads {
            assert_eq!(
                context.get_symbol_at_location(read[1]).unwrap(),
                Some(parameter)
            );
            let property = context.get_symbol_at_location(read[0]).unwrap().unwrap();
            assert_eq!(
                context.get_symbol_at_location(read[2]).unwrap(),
                Some(property)
            );
        }
    });
}

#[test]
fn in_operands_keep_native_null_and_unknown_errors_without_replacing_input_types() {
    for (source, code, argument) in [
        (
            "function hasValue(box: unknown): boolean { return \"value\" in box; }",
            18_046,
            "box",
        ),
        (
            "function hasValue(box: { value: string } | null): boolean { return \"value\" in box; }",
            18_047,
            "box",
        ),
        (
            "function hasValue(): boolean { return \"value\" in null; }",
            18_050,
            "null",
        ),
        (
            "function hasValue(key: string | undefined, box: { value: string }): boolean { return key in box; }",
            18_048,
            "key",
        ),
    ] {
        let parsed = parse_source_file(source);
        let [binary, left, right] = membership(&parsed);
        check_query_orders(&parsed, &[binary, left, right], |context| {
            let operand = if code == 18_048 { left } else { right };
            assert_diagnostics(context, &[(code, operand, &[argument])]);
            let bootstrap = context.store().intrinsic_bootstrap().unwrap();
            assert_eq!(checked_type(context, binary), bootstrap.boolean_type);
            let original = checked_type(context, operand);
            match code {
                18_046 => assert_eq!(original, bootstrap.unknown_type),
                18_050 => assert_eq!(original, bootstrap.null_type),
                18_047 => {
                    let TypeData::Union(data) =
                        context.store().type_payload(original).unwrap().data()
                    else {
                        panic!("the checked receiver keeps its nullable annotation")
                    };
                    assert_eq!(data.union.types.len(), 2);
                    assert!(data.union.types.contains(&bootstrap.null_type));
                    assert!(data.union.types.iter().any(|&type_| matches!(
                        context.store().type_payload(type_).unwrap().data(),
                        TypeData::Object(_)
                    )));
                }
                18_048 => {
                    let TypeData::Union(data) =
                        context.store().type_payload(original).unwrap().data()
                    else {
                        panic!("the checked key keeps its possibly undefined annotation")
                    };
                    let mut expected = [bootstrap.string_type, bootstrap.undefined_type];
                    expected.sort_unstable();
                    assert_eq!(data.union.types, expected);
                }
                _ => unreachable!(),
            }
            if code != 18_050 {
                assert_parameter_read(context, &parsed, right, "box");
            }
            if code == 18_048 {
                assert_parameter_read(context, &parsed, left, "key");
            }
        });
    }
}

#[test]
fn in_result_is_boolean_even_when_the_declared_return_type_is_number() {
    let parsed = parse_source_file(
        "function hasValue(box: { value?: string }): number { return \"value\" in box; }",
    );
    let [binary, left, right] = membership(&parsed);
    let return_id = parsed.arena.get(binary.node).unwrap().parent.unwrap();
    let return_record = parsed.arena.get(return_id).unwrap();
    assert_eq!(return_record.kind, SyntaxKind::ReturnStatement);
    let NodeData::ReturnStatement(returned) = &return_record.data else {
        panic!("expected parent return statement");
    };
    assert_eq!(returned.expression, Some(binary.node));
    let return_node = node(&parsed, return_id);
    check_query_orders(&parsed, &[binary, left, right], |context| {
        assert_eq!(
            checked_type(context, binary),
            context.store().intrinsic_bootstrap().unwrap().boolean_type
        );
        assert_diagnostics(context, &[(2322, return_node, &["boolean", "number"])]);
    });
}
