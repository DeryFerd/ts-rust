use ts_ast::{FileId, NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, SourceCheckError, TypeData,
};
use ts_parser::{ParseResult, parse_javascript_source_file, parse_source_file};

fn context(
    parsed: &ParseResult,
    file: FileId,
    language: CanonicalSourceLanguage,
) -> CanonicalCheckerContext<'_> {
    context_with_options(parsed, file, language, CanonicalCheckerOptions::default())
}

fn context_with_options(
    parsed: &ParseResult,
    file: FileId,
    language: CanonicalSourceLanguage,
    options: CanonicalCheckerOptions,
) -> CanonicalCheckerContext<'_> {
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            file,
            CanonicalSourceFileFacts::new(
                EscapedName::source(if language == CanonicalSourceLanguage::JavaScript {
                    "\"/project/source.js\""
                } else {
                    "\"/project/source.ts\""
                }),
                language,
                false,
                CanonicalModuleState::Script,
            ),
        )
        .unwrap();
    if language == CanonicalSourceLanguage::JavaScript {
        binder
            .bind_javascript_declaration_slice(&parsed.arena, file)
            .unwrap();
    } else {
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
    }
    CanonicalCheckerContext::new(binder.finish(), vec![(file, &parsed.arena)], options).unwrap()
}

#[derive(Clone, Copy)]
struct ExpectedLexicalBlock {
    name: &'static str,
    read: NodeRef,
    declaration_name: NodeRef,
    symbol: SemanticSymbolId,
}

fn lexical_block_expectations(
    parsed: &ParseResult,
    context: &CanonicalCheckerContext<'_>,
    file: FileId,
) -> ([ExpectedLexicalBlock; 2], SemanticSymbolId) {
    let (_, bound) = context.file(file).unwrap();
    let NodeData::SourceFile(root) = &parsed.arena.get(parsed.source_file).unwrap().data else {
        panic!("the fixture must retain its source statements")
    };
    let expected = [("c1", 0), ("v1", 2)].map(|(name, index)| {
        let NodeData::Block(block) = &parsed.arena.get(root.statements.nodes[index]).unwrap().data
        else {
            panic!("the fixture must retain both lexical blocks")
        };
        let NodeData::ExpressionStatement(read) =
            &parsed.arena.get(block.statements.nodes[0]).unwrap().data
        else {
            panic!("the lexical block must start with its identifier read")
        };
        let NodeData::VariableStatement(statement) =
            &parsed.arena.get(block.statements.nodes[1]).unwrap().data
        else {
            panic!("the lexical block must finish with its const declaration")
        };
        let NodeData::VariableDeclarationList(list) =
            &parsed.arena.get(statement.declaration_list).unwrap().data
        else {
            panic!("the const statement must retain its declaration list")
        };
        let declaration = NodeRef::new(parsed.arena.id(), file, list.declarations.nodes[0]);
        let NodeData::VariableDeclaration(variable) =
            &parsed.arena.get(declaration.node).unwrap().data
        else {
            panic!("the const statement must retain its declaration")
        };
        ExpectedLexicalBlock {
            name,
            read: NodeRef::new(parsed.arena.id(), file, read.expression),
            declaration_name: NodeRef::new(parsed.arena.id(), file, variable.name),
            symbol: bound.symbol(declaration).unwrap(),
        }
    });
    let outer_symbol = bound
        .locals(bound.source_file())
        .and_then(|locals| context.store().symbol_table(locals))
        .and_then(|locals| locals.get_source("v1"))
        .unwrap();
    (expected, outer_symbol)
}

#[test]
fn top_level_empty_statements_are_semantic_noops() {
    let parsed = parse_source_file(";const first = 1;; const second = 2;");
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(8_200);
    let mut context = context(&parsed, file, CanonicalSourceLanguage::TypeScript);

    context.check_source_file(file).unwrap();

    assert!(context.diagnostics().is_empty());
    let warm = (
        context.store().type_len(),
        context.store().symbol_len(),
        context.diagnostics().clone(),
    );
    context.recheck_source_file(file).unwrap();
    assert_eq!(
        (
            context.store().type_len(),
            context.store().symbol_len(),
            context.diagnostics().clone(),
        ),
        warm
    );
}

#[test]
fn top_level_lexical_blocks_report_forward_const_reads_and_shadow_outer_vars() {
    let source = concat!(
        "{\n",
        "    c1;\n",
        "    const c1 = 0;\n",
        "}\n\n",
        "var v1;\n",
        "{\n",
        "    v1;\n",
        "    const v1 = 0;\n",
        "}\n",
    );
    let parsed = parse_source_file(source);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(8_231);
    let mut context = context(&parsed, file, CanonicalSourceLanguage::TypeScript);

    let (expected, outer_symbol) = lexical_block_expectations(&parsed, &context, file);
    assert_ne!(expected[1].symbol, outer_symbol);

    context.check_source_file(file).unwrap();

    let diagnostics = context.diagnostics().as_slice();
    assert_eq!(diagnostics.len(), expected.len(), "{diagnostics:?}");
    for (
        diagnostic,
        ExpectedLexicalBlock {
            name,
            read,
            declaration_name,
            symbol,
        },
    ) in diagnostics.iter().zip(expected)
    {
        assert_eq!(diagnostic.node, Some(read));
        assert_eq!(diagnostic.diagnostic.code(), 2448);
        assert_eq!(
            diagnostic.diagnostic.render().unwrap(),
            format!("Block-scoped variable '{name}' used before its declaration."),
        );
        let [related] = diagnostic.related_information.as_slice() else {
            panic!("the forward const read must identify its declaration")
        };
        assert_eq!(related.node, Some(declaration_name));
        assert_eq!(related.diagnostic.code(), 2728);
        assert_eq!(
            related.diagnostic.render().unwrap(),
            format!("'{name}' is declared here."),
        );
        assert_eq!(
            context
                .store()
                .symbol_node_links(read)
                .and_then(|links| links.resolved_symbol),
            Some(symbol),
        );
        let declared_type = context
            .store()
            .value_symbol_links(symbol)
            .and_then(|links| links.resolved_type)
            .unwrap();
        assert_eq!(context.type_to_string(declared_type).unwrap(), "0");
        assert_eq!(
            context
                .store()
                .type_node_links(read)
                .and_then(|links| links.resolved_type),
            Some(declared_type),
        );
    }
    let outer_type = context
        .store()
        .value_symbol_links(outer_symbol)
        .and_then(|links| links.resolved_type)
        .unwrap();
    assert_eq!(context.type_to_string(outer_type).unwrap(), "any");

    let warm = (
        context.store().type_len(),
        context.store().symbol_len(),
        context.diagnostics().clone(),
    );
    context.recheck_source_file(file).unwrap();
    assert_eq!(
        (
            context.store().type_len(),
            context.store().symbol_len(),
            context.diagnostics().clone(),
        ),
        warm,
    );
}

#[test]
fn unsupported_lexical_blocks_and_implicit_any_shadowing_stay_cold() {
    for (index, source) in [
        "{ value; let value = 0; }",
        "{ value; const value = 0; value; }",
        "{ value; const other = 0; }",
        "var value; { other; const other = 0; }",
        "module; { value; const value = 0; }",
    ]
    .into_iter()
    .enumerate()
    {
        let parsed = parse_source_file(source);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(8_232 + u32::try_from(index).unwrap());
        let mut context = context(&parsed, file, CanonicalSourceLanguage::TypeScript);
        let cold = (
            context.store().type_len(),
            context.store().symbol_len(),
            context.diagnostics().clone(),
        );

        assert!(
            matches!(
                context.check_source_file(file),
                Err(SourceCheckError::Unsupported(_))
            ),
            "source: {source}",
        );
        assert_eq!(
            (
                context.store().type_len(),
                context.store().symbol_len(),
                context.diagnostics().clone(),
            ),
            cold,
            "source: {source}",
        );
    }

    let parsed = parse_source_file("var value; { value; const value = 0; }");
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(8_237);
    let mut context = context_with_options(
        &parsed,
        file,
        CanonicalSourceLanguage::TypeScript,
        CanonicalCheckerOptions {
            no_implicit_any: true,
            ..CanonicalCheckerOptions::default()
        },
    );
    assert!(matches!(
        context.check_source_file(file),
        Err(SourceCheckError::Unsupported(_))
    ));
    assert!(context.diagnostics().is_empty());
}

#[test]
fn top_level_while_breaks_validate_enclosing_labels_and_replay_warm() {
    for (index, (source, expected)) in [
        ("while (true) break;", &[][..]),
        ("while (true) { break; }", &[][..]),
        ("target: while (true) { break target; }", &[][..]),
        ("while (true) { break target; }", &[1116][..]),
    ]
    .into_iter()
    .enumerate()
    {
        let parsed = parse_source_file(source);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(8_210 + u32::try_from(index).unwrap());
        let mut context = context(&parsed, file, CanonicalSourceLanguage::TypeScript);

        context.check_source_file(file).unwrap();

        assert_eq!(
            context
                .diagnostics()
                .as_slice()
                .iter()
                .map(|diagnostic| diagnostic.diagnostic.code())
                .collect::<Vec<_>>(),
            expected,
            "source: {source}",
        );
        let warm = (
            context.store().type_len(),
            context.store().symbol_len(),
            context.diagnostics().clone(),
        );
        context.recheck_source_file(file).unwrap();
        assert_eq!(
            (
                context.store().type_len(),
                context.store().symbol_len(),
                context.diagnostics().clone(),
            ),
            warm,
            "source: {source}",
        );
    }
}

#[test]
fn object_assertions_allow_structurally_overlapping_extra_properties() {
    let parsed = parse_source_file("var value = <{ id: number; }> { id: 4, name: 'extra' };");
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(8_201);
    let mut context = context(&parsed, file, CanonicalSourceLanguage::TypeScript);

    context.check_source_file(file).unwrap();

    assert!(context.diagnostics().is_empty());
}

#[test]
fn object_literals_preserve_shorthand_and_computed_literal_properties() {
    let parsed = parse_source_file(concat!(
        "const value = 1; ",
        "const object = { value, ['label']: 'ready', [2]: true };",
    ));
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(8_205);
    let mut context = context(&parsed, file, CanonicalSourceLanguage::TypeScript);

    context.check_source_file(file).unwrap();

    let object = parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            (record.kind == SyntaxKind::ObjectLiteralExpression).then_some(NodeRef::new(
                parsed.arena.id(),
                file,
                node,
            ))
        })
        .unwrap();
    let object_type = context
        .store()
        .type_node_links(object)
        .and_then(|links| links.resolved_type)
        .unwrap();
    let TypeData::Object(object) = context.store().type_payload(object_type).unwrap().data() else {
        panic!("object literal must publish a canonical object type")
    };
    let names = object
        .structured
        .properties
        .as_ref()
        .unwrap()
        .iter()
        .map(|symbol| {
            context
                .store()
                .symbol(*symbol)
                .unwrap()
                .name()
                .as_utf8()
                .unwrap()
        })
        .collect::<Vec<_>>();
    assert_eq!(names, ["value", "label", "2"]);
    assert!(context.diagnostics().is_empty());

    let warm = (
        context.store().type_len(),
        context.store().symbol_len(),
        context.diagnostics().clone(),
    );
    context.recheck_source_file(file).unwrap();
    assert_eq!(
        (
            context.store().type_len(),
            context.store().symbol_len(),
            context.diagnostics().clone(),
        ),
        warm
    );
}

#[test]
fn object_property_arrows_publish_callable_values_without_changing_siblings() {
    let parsed = parse_source_file(concat!(
        "const handlers = { ",
        "run: (value: any) => value.id, ",
        "label: 'ready' ",
        "};",
    ));
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(8_220);
    let mut context = context(&parsed, file, CanonicalSourceLanguage::TypeScript);

    context.check_source_file(file).unwrap();
    assert!(
        context.diagnostics().is_empty(),
        "{:?}",
        context.diagnostics()
    );

    let arrow = parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            (record.kind == SyntaxKind::ArrowFunction).then_some(NodeRef::new(
                parsed.arena.id(),
                file,
                node,
            ))
        })
        .unwrap();
    let arrow_type = context
        .store()
        .type_node_links(arrow)
        .and_then(|links| links.resolved_type)
        .unwrap();
    assert_eq!(
        context.type_to_string(arrow_type).unwrap(),
        "(value: any) => any"
    );

    let warm = (
        context.store().type_len(),
        context.store().signature_len(),
        context.diagnostics().clone(),
    );
    context.recheck_source_file(file).unwrap();
    assert_eq!(
        (
            context.store().type_len(),
            context.store().signature_len(),
            context.diagnostics().clone(),
        ),
        warm,
    );
}

#[test]
fn direct_unannotated_arrows_report_exact_implicit_any_diagnostics() {
    let source = "var value = parameter => <any>{};";
    let parsed = parse_source_file(source);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(8_224);
    let mut context = context_with_options(
        &parsed,
        file,
        CanonicalSourceLanguage::TypeScript,
        CanonicalCheckerOptions {
            no_implicit_any: true,
            ..CanonicalCheckerOptions::default()
        },
    );

    context.check_source_file(file).unwrap();

    let [diagnostic] = context.diagnostics().as_slice() else {
        panic!("an unannotated direct arrow must report one implicit-any diagnostic")
    };
    assert_eq!(diagnostic.diagnostic.code(), 7006);
    assert_eq!(
        diagnostic.diagnostic.render().unwrap(),
        "Parameter 'parameter' implicitly has an 'any' type."
    );
    let node = parsed.arena.get(diagnostic.node.unwrap().node).unwrap();
    assert_eq!(
        &source[node.range.start.get() as usize..node.range.end.get() as usize],
        "parameter"
    );

    let warm = (
        context.store().type_len(),
        context.store().signature_len(),
        context.diagnostics().clone(),
    );
    context.recheck_source_file(file).unwrap();
    assert_eq!(
        (
            context.store().type_len(),
            context.store().signature_len(),
            context.diagnostics().clone(),
        ),
        warm,
    );
}

#[test]
fn contextual_arrays_accept_nested_object_type_assertions() {
    let parsed = parse_source_file(concat!(
        "interface Array<T> {}\n",
        "interface ReadonlyArray<T> {}\n",
        "const value: { id: number }[] = [<{ id: number }>({})];\n",
    ));
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(8_221);
    let mut context = context(&parsed, file, CanonicalSourceLanguage::TypeScript);

    context.check_source_file(file).unwrap();
    assert!(
        context.diagnostics().is_empty(),
        "{:?}",
        context.diagnostics()
    );

    let warm = (context.store().type_len(), context.diagnostics().clone());
    context.recheck_source_file(file).unwrap();
    assert_eq!(
        (context.store().type_len(), context.diagnostics().clone()),
        warm
    );
}

#[test]
fn object_union_assertions_widen_missing_sibling_properties() {
    let parsed = parse_source_file(concat!(
        "interface Array<T> {}\n",
        "interface ReadonlyArray<T> {}\n",
        "var value = <{ id: number; }[]>[{ foo: 'ready' }, {}];\n",
    ));
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(8_222);
    let mut context = context(&parsed, file, CanonicalSourceLanguage::TypeScript);

    context.check_source_file(file).unwrap();
    assert!(
        context.diagnostics().is_empty(),
        "{:?}",
        context.diagnostics()
    );

    let warm = (
        context.store().type_len(),
        context.store().symbol_len(),
        context.diagnostics().clone(),
    );
    context.recheck_source_file(file).unwrap();
    assert_eq!(
        (
            context.store().type_len(),
            context.store().symbol_len(),
            context.diagnostics().clone(),
        ),
        warm,
    );
}

#[test]
fn labeled_tuple_rest_parameters_name_the_incompatible_parameter() {
    let parsed = parse_source_file(concat!(
        "interface Array<T> {}\n",
        "interface ReadonlyArray<T> {}\n",
        "declare let target: (...args: [value: number]) => void;\n",
        "declare let source: (argument: string) => void;\n",
        "target = source;\n",
    ));
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(8_223);
    let mut context = context_with_options(
        &parsed,
        file,
        CanonicalSourceLanguage::TypeScript,
        CanonicalCheckerOptions {
            strict_function_types: true,
            ..CanonicalCheckerOptions::default()
        },
    );

    context.check_source_file(file).unwrap();

    let [diagnostic] = context.diagnostics().as_slice() else {
        panic!("expected one incompatible function assignment")
    };
    assert_eq!(diagnostic.diagnostic.code(), 2322);
    assert_eq!(
        diagnostic.diagnostic.render().unwrap(),
        concat!(
            "Type '(argument: string) => void' is not assignable to type ",
            "'(value: number) => void'.\n",
            "  Types of parameters 'argument' and 'value' are incompatible.\n",
            "    Type 'number' is not assignable to type 'string'.",
        ),
    );

    let warm = (
        context.store().type_len(),
        context.store().signature_len(),
        context.diagnostics().clone(),
    );
    context.recheck_source_file(file).unwrap();
    assert_eq!(
        (
            context.store().type_len(),
            context.store().signature_len(),
            context.diagnostics().clone(),
        ),
        warm,
    );
}

#[test]
fn numeric_and_quoted_object_keys_keep_distinct_assignment_diagnostics() {
    let parsed = parse_source_file(concat!(
        "const numeric: number = { 0: 1 }; ",
        "const quoted: string = { \"0\": 1 };",
    ));
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(8_206);
    let mut context = context(&parsed, file, CanonicalSourceLanguage::TypeScript);

    context.check_source_file(file).unwrap();

    assert_eq!(
        context
            .diagnostics()
            .as_slice()
            .iter()
            .map(|diagnostic| diagnostic.diagnostic.render().unwrap())
            .collect::<Vec<_>>(),
        [
            "Type '{ 0: number; }' is not assignable to type 'number'.",
            "Type '{ \"0\": number; }' is not assignable to type 'string'.",
        ],
    );

    let warm = (
        context.store().type_len(),
        context.store().symbol_len(),
        context.diagnostics().clone(),
    );
    context.recheck_source_file(file).unwrap();
    assert_eq!(
        (
            context.store().type_len(),
            context.store().symbol_len(),
            context.diagnostics().clone(),
        ),
        warm,
    );
}

#[test]
fn javascript_inferred_variables_report_incompatible_assignments() {
    let parsed = parse_javascript_source_file("var value = 'ready'; value = 1;");
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(8_202);
    let mut context = context(&parsed, file, CanonicalSourceLanguage::JavaScript);

    context.check_source_file(file).unwrap();

    let [diagnostic] = context.diagnostics().as_slice() else {
        panic!("expected one JavaScript assignment diagnostic")
    };
    assert_eq!(diagnostic.diagnostic.code(), 2322);
    assert_eq!(
        diagnostic.diagnostic.render().unwrap(),
        "Type 'number' is not assignable to type 'string'."
    );
}

#[test]
fn javascript_commonjs_exports_preserve_the_local_assignment_type() {
    let parsed = parse_javascript_source_file("const value = 1; module.exports = value;");
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(8_206);
    let mut context = context(&parsed, file, CanonicalSourceLanguage::JavaScript);

    context.check_source_file(file).unwrap();

    assert!(context.diagnostics().is_empty());
    let assignment = parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            (record.kind == SyntaxKind::BinaryExpression).then_some(NodeRef::new(
                parsed.arena.id(),
                file,
                node,
            ))
        })
        .unwrap();
    let assignment_type = context
        .store()
        .type_node_links(assignment)
        .and_then(|links| links.resolved_type)
        .unwrap();
    assert_eq!(context.type_to_string(assignment_type).unwrap(), "1");

    let warm = (
        context.store().type_len(),
        context.store().symbol_len(),
        context.diagnostics().clone(),
    );
    context.recheck_source_file(file).unwrap();
    assert_eq!(
        (
            context.store().type_len(),
            context.store().symbol_len(),
            context.diagnostics().clone(),
        ),
        warm,
    );
}

#[test]
fn javascript_jsdoc_annotations_control_variable_assignment_types() {
    let parsed =
        parse_javascript_source_file("/** @type {number} */\nvar value = 1;\nvalue = 'wrong';");
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(8_203);
    let mut context = context(&parsed, file, CanonicalSourceLanguage::JavaScript);

    context.check_source_file(file).unwrap();

    let [diagnostic] = context.diagnostics().as_slice() else {
        panic!("expected one JSDoc assignment diagnostic")
    };
    assert_eq!(diagnostic.diagnostic.code(), 2322);
    assert_eq!(
        diagnostic.diagnostic.render().unwrap(),
        "Type 'string' is not assignable to type 'number'."
    );
}

#[test]
fn malformed_javascript_jsdoc_types_keep_exact_source_diagnostics() {
    let source = "/** @type {@import(\"a\").Type} */\nlet value;";
    let parsed = parse_javascript_source_file(source);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(8_204);
    let mut context = context(&parsed, file, CanonicalSourceLanguage::JavaScript);

    context.check_source_file(file).unwrap();

    let [diagnostic] = context.diagnostics().as_slice() else {
        panic!("expected one malformed JSDoc type diagnostic")
    };
    assert_eq!(diagnostic.diagnostic.code(), 1110);
    assert_eq!(
        diagnostic.range_override.unwrap().range().start.get() as usize,
        source.find("@import").unwrap()
    );
}

#[test]
fn object_const_assertions_preserve_readonly_literal_property_types() {
    let parsed = parse_source_file(concat!(
        "const value = { ",
        "foo: 'foo', ",
        "new: 'new', ",
        "count: 1, ",
        "enabled: true ",
        "} as const;",
    ));
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(8_230);
    let mut context = context(&parsed, file, CanonicalSourceLanguage::TypeScript);

    context.check_source_file(file).unwrap();
    assert!(
        context.diagnostics().is_empty(),
        "{:?}",
        context.diagnostics()
    );

    let object = parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            (record.kind == SyntaxKind::ObjectLiteralExpression).then_some(NodeRef::new(
                parsed.arena.id(),
                file,
                node,
            ))
        })
        .unwrap();
    let object_type = context
        .store()
        .type_node_links(object)
        .and_then(|links| links.resolved_type)
        .unwrap();
    let TypeData::Object(object) = context.store().type_payload(object_type).unwrap().data() else {
        panic!("const assertion must retain its object type")
    };
    for (property, expected) in object
        .structured
        .properties
        .as_deref()
        .unwrap()
        .iter()
        .zip(["\"foo\"", "\"new\"", "1", "true"])
    {
        let symbol = context.store().symbol(*property).unwrap();
        assert!(
            symbol
                .check_flags()
                .contains(ts_binder::CheckFlags::READONLY)
        );
        let type_ = context
            .store()
            .value_symbol_links(*property)
            .and_then(|links| links.resolved_type)
            .unwrap();
        assert_eq!(context.type_to_string(type_).unwrap(), expected);
    }

    let warm = (context.store().type_len(), context.store().symbol_len());
    context.recheck_source_file(file).unwrap();
    assert_eq!(
        (context.store().type_len(), context.store().symbol_len()),
        warm
    );
}
