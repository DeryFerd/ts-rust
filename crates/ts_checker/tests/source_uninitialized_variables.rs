use ts_ast::{FileId, NodeData, NodeRef};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, IntrinsicBootstrapOptions, SourceCheckError,
    TypeNodeLinks, UnsupportedSourceSyntax, ValueSymbolLinks,
};
use ts_parser::{ParseResult, parse_source_file};

fn checker_context(
    parsed: &ParseResult,
    file: FileId,
    module_state: CanonicalModuleState,
    strict_null_checks: bool,
) -> CanonicalCheckerContext<'_> {
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            file,
            CanonicalSourceFileFacts::new(
                EscapedName::source("\"/project/uninitialized-variables.ts\""),
                CanonicalSourceLanguage::TypeScript,
                false,
                module_state,
            ),
        )
        .unwrap();
    binder
        .bind_typescript_declaration_slice(&parsed.arena, file)
        .unwrap();
    CanonicalCheckerContext::new(
        binder.finish(),
        [(file, &parsed.arena)].into_iter().collect(),
        CanonicalCheckerOptions {
            intrinsic: IntrinsicBootstrapOptions {
                strict_null_checks,
                ..IntrinsicBootstrapOptions::default()
            },
            ..CanonicalCheckerOptions::default()
        },
    )
    .unwrap()
}

fn variable_declaration(parsed: &ParseResult, file: FileId, expected: &str) -> NodeRef {
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
            (name.text == expected).then_some(NodeRef::new(parsed.arena.id(), file, node))
        })
        .unwrap_or_else(|| panic!("missing variable {expected}"))
}

fn variable_symbol(
    parsed: &ParseResult,
    file: FileId,
    context: &CanonicalCheckerContext<'_>,
    expected: &str,
) -> SemanticSymbolId {
    let declaration = variable_declaration(parsed, file, expected);
    let symbol = context.file(file).unwrap().1.symbol(declaration).unwrap();
    context.store().get_merged_symbol(symbol).unwrap()
}

fn variable_type_node(parsed: &ParseResult, file: FileId, expected: &str) -> NodeRef {
    let declaration = variable_declaration(parsed, file, expected);
    let NodeData::VariableDeclaration(variable) = &parsed.arena.get(declaration.node).unwrap().data
    else {
        unreachable!("the helper selected a variable declaration")
    };
    NodeRef::new(
        parsed.arena.id(),
        file,
        variable.type_.expect("fixture variable is annotated"),
    )
}

fn variable_initializer(parsed: &ParseResult, file: FileId, expected: &str) -> NodeRef {
    let declaration = variable_declaration(parsed, file, expected);
    let NodeData::VariableDeclaration(variable) = &parsed.arena.get(declaration.node).unwrap().data
    else {
        unreachable!("the helper selected a variable declaration")
    };
    NodeRef::new(
        parsed.arena.id(),
        file,
        variable
            .initializer
            .expect("fixture variable is initialized"),
    )
}

fn is_type_checked(context: &CanonicalCheckerContext<'_>, file: FileId) -> bool {
    context
        .source_file(file)
        .and_then(|source| context.store().source_file_links(source))
        .is_some_and(|links| links.type_checked)
}

#[test]
fn loose_annotated_variables_support_reads_assignments_and_warm_replay() {
    for (index, (prefix, module_state)) in [
        ("", CanonicalModuleState::Script),
        ("export {};\n", CanonicalModuleState::External),
    ]
    .into_iter()
    .enumerate()
    {
        let source = format!(
            "{prefix}{}",
            concat!(
                "type Count = number;\n",
                "type Label = string;\n",
                "var count: Count;\n",
                "let label: Label;\n",
                "const firstCount: number = count;\n",
                "const firstLabel: string = label;\n",
                "count = 2;\n",
                "label = \"ready\";\n",
                "const lastCount: number = count;\n",
                "const lastLabel: string = label;\n",
            ),
        );
        let parsed = parse_source_file(&source);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(2_200 + u32::try_from(index).unwrap());
        let mut context = checker_context(&parsed, file, module_state, false);
        let count = variable_symbol(&parsed, file, &context, "count");
        let label = variable_symbol(&parsed, file, &context, "label");
        let count_annotation = variable_type_node(&parsed, file, "count");
        let label_annotation = variable_type_node(&parsed, file, "label");
        let number = context.store().intrinsic_bootstrap().unwrap().number_type;
        let string = context.store().intrinsic_bootstrap().unwrap().string_type;

        context.check_source_file(file).unwrap();

        assert!(context.diagnostics().is_empty());
        assert!(is_type_checked(&context, file));
        for (symbol, annotation, expected) in [
            (count, count_annotation, number),
            (label, label_annotation, string),
        ] {
            assert_eq!(
                context.store().value_symbol_links(symbol),
                Some(&ValueSymbolLinks {
                    resolved_type: Some(expected),
                    ..ValueSymbolLinks::default()
                })
            );
            assert_eq!(
                context.store().type_node_links(annotation),
                Some(&TypeNodeLinks {
                    resolved_type: Some(expected),
                    ..TypeNodeLinks::default()
                })
            );
        }

        let warm = (
            context.store().type_len(),
            context.store().mapper_len(),
            context.store().signature_len(),
            context.store().symbol_len(),
            context.store().symbol_store().symbol_table_len(),
            context.store().relation_state_snapshot(),
            [count, label].map(|symbol| context.store().value_symbol_links(symbol).cloned()),
            [count_annotation, label_annotation]
                .map(|node| context.store().type_node_links(node).cloned()),
            context.diagnostics().len(),
        );
        context.recheck_source_file(file).unwrap();
        assert_eq!(
            (
                context.store().type_len(),
                context.store().mapper_len(),
                context.store().signature_len(),
                context.store().symbol_len(),
                context.store().symbol_store().symbol_table_len(),
                context.store().relation_state_snapshot(),
                [count, label].map(|symbol| context.store().value_symbol_links(symbol).cloned()),
                [count_annotation, label_annotation]
                    .map(|node| context.store().type_node_links(node).cloned()),
                context.diagnostics().len(),
            ),
            warm
        );
    }
}

#[test]
fn strict_null_checks_report_reads_before_assignment_and_accept_later_reads() {
    let parsed = parse_source_file(concat!(
        "var count: number;\n",
        "let label: string;\n",
        "const earlyCount: number = count;\n",
        "const earlyLabel: string = label;\n",
        "count = 1;\n",
        "label = \"ready\";\n",
        "const lateCount: number = count;\n",
        "const lateLabel: string = label;\n",
    ));
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(2_202);
    let mut context = checker_context(&parsed, file, CanonicalModuleState::Script, true);
    let reads = ["earlyCount", "earlyLabel"].map(|name| variable_initializer(&parsed, file, name));

    context.check_source_file(file).unwrap();

    let diagnostics = context.diagnostics().as_slice();
    assert_eq!(diagnostics.len(), 2);
    for (diagnostic, (node, name)) in diagnostics
        .iter()
        .zip(reads.into_iter().zip(["count", "label"]))
    {
        assert_eq!(diagnostic.node, Some(node));
        assert_eq!(diagnostic.diagnostic.code(), 2454);
        assert_eq!(diagnostic.diagnostic.arguments, [name]);
        assert_eq!(
            diagnostic.diagnostic.render().unwrap(),
            format!("Variable '{name}' is used before being assigned.")
        );
    }
    assert!(is_type_checked(&context, file));

    context.recheck_source_file(file).unwrap();
    assert_eq!(context.diagnostics().len(), 2);
}

#[test]
fn strict_null_checks_accept_assignment_before_first_read() {
    for (index, binding) in ["var", "let"].into_iter().enumerate() {
        let source = format!("{binding} value: number; value = 1; const result: number = value;");
        let parsed = parse_source_file(&source);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(2_203 + u32::try_from(index).unwrap());
        let mut context = checker_context(&parsed, file, CanonicalModuleState::Script, true);

        context.check_source_file(file).unwrap();

        assert!(context.diagnostics().is_empty());
        assert!(is_type_checked(&context, file));
    }
}

#[test]
fn strict_null_checks_exempt_types_that_permit_uninitialized_values() {
    let parsed = parse_source_file(concat!(
        "let nullable: number | undefined;\n",
        "let anything: any;\n",
        "let unknownValue: unknown;\n",
        "let empty: void;\n",
        "const first: number | undefined = nullable;\n",
        "const second: any = anything;\n",
        "const third: unknown = unknownValue;\n",
        "const fourth: void = empty;\n",
    ));
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(2_205);
    let mut context = checker_context(&parsed, file, CanonicalModuleState::Script, true);

    context.check_source_file(file).unwrap();

    assert!(context.diagnostics().is_empty());
    assert!(is_type_checked(&context, file));
}

#[test]
fn strict_null_checks_do_not_treat_function_captures_as_immediate_reads() {
    let parsed = parse_source_file(concat!(
        "var value: number;\n",
        "function read(): number { return value; }\n",
        "value = 1;\n",
        "const result: number = read();\n",
    ));
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(2_206);
    let mut context = checker_context(&parsed, file, CanonicalModuleState::Script, true);

    context.check_source_file(file).unwrap();

    assert!(context.diagnostics().is_empty());
    assert!(is_type_checked(&context, file));
}

#[test]
fn unannotated_and_exported_uninitialized_variables_remain_typed_boundaries() {
    for (index, (source, module_state)) in [
        ("var missing;", CanonicalModuleState::Script),
        (
            "export let exported: number;",
            CanonicalModuleState::External,
        ),
    ]
    .into_iter()
    .enumerate()
    {
        let parsed = parse_source_file(source);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(2_210 + u32::try_from(index).unwrap());
        let mut context = checker_context(&parsed, file, module_state, false);

        assert!(matches!(
            context.check_source_file(file),
            Err(SourceCheckError::Unsupported(
                UnsupportedSourceSyntax::MissingVariableInitializer(_)
            ))
        ));
        assert!(context.diagnostics().is_empty());
        assert!(!is_type_checked(&context, file));
    }
}

#[test]
fn later_unsupported_variables_keep_admitted_variables_cold_across_retries() {
    let parsed = parse_source_file(concat!(
        "var first: number;\n",
        "let second: string;\n",
        "var missing;\n",
    ));
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(2_220);
    let mut context = checker_context(&parsed, file, CanonicalModuleState::Script, false);
    let first = variable_symbol(&parsed, file, &context, "first");
    let second = variable_symbol(&parsed, file, &context, "second");
    let missing = variable_declaration(&parsed, file, "missing");
    let annotations = ["first", "second"].map(|name| variable_type_node(&parsed, file, name));
    let cold = (
        context.store().type_len(),
        context.store().mapper_len(),
        context.store().signature_len(),
        context.store().relation_state_snapshot(),
    );

    for _ in 0..2 {
        assert_eq!(
            context.check_source_file(file),
            Err(SourceCheckError::Unsupported(
                UnsupportedSourceSyntax::MissingVariableInitializer(missing)
            ))
        );
        assert_eq!(
            (
                context.store().type_len(),
                context.store().mapper_len(),
                context.store().signature_len(),
                context.store().relation_state_snapshot(),
            ),
            cold
        );
        for symbol in [first, second] {
            assert!(context.store().value_symbol_links(symbol).is_none());
        }
        for annotation in annotations {
            assert!(context.store().type_node_links(annotation).is_none());
        }
        assert!(context.diagnostics().is_empty());
        assert!(!is_type_checked(&context, file));
    }
}

#[test]
fn ambient_and_uninitialized_variables_share_assignment_planning() {
    for (index, binding) in ["var", "let"].into_iter().enumerate() {
        let source = format!(
            "declare {binding} ambient: number;\n{binding} local: number;\nambient = 1;\nlocal = 2;\n"
        );
        let parsed = parse_source_file(&source);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(2_230 + u32::try_from(index).unwrap());
        let mut context = checker_context(&parsed, file, CanonicalModuleState::Script, false);
        let number = context.store().intrinsic_bootstrap().unwrap().number_type;
        let symbols =
            ["ambient", "local"].map(|name| variable_symbol(&parsed, file, &context, name));

        context.check_source_file(file).unwrap();

        assert!(context.diagnostics().is_empty());
        for symbol in symbols {
            assert_eq!(
                context.store().value_symbol_links(symbol),
                Some(&ValueSymbolLinks {
                    resolved_type: Some(number),
                    ..ValueSymbolLinks::default()
                })
            );
        }
        assert!(is_type_checked(&context, file));
    }
}

#[test]
fn assignments_to_uninitialized_variables_preserve_exact_type_errors() {
    for (index, binding) in ["var", "let"].into_iter().enumerate() {
        let source = format!("{binding} value: number; value = \"wrong\";");
        let parsed = parse_source_file(&source);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(2_240 + u32::try_from(index).unwrap());
        let mut context = checker_context(&parsed, file, CanonicalModuleState::Script, false);

        context.check_source_file(file).unwrap();

        let diagnostics = context.diagnostics().as_slice();
        assert_eq!(diagnostics.len(), 1);
        assert_eq!(diagnostics[0].diagnostic.code(), 2322);
        assert_eq!(diagnostics[0].diagnostic.arguments, ["string", "number"]);
        assert_eq!(
            diagnostics[0].diagnostic.render().unwrap(),
            "Type 'string' is not assignable to type 'number'."
        );
        assert!(is_type_checked(&context, file));
    }
}
