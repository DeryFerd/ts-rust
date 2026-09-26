use ts_ast::{FileId, NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, SourceCheckError, TypeId,
};
use ts_parser::{ParseResult, parse_source_file};

const SUCCESS_SOURCE: &str = concat!(
    "type PropertyValue = { answer: number }['answer'];\n",
    "type ParenthesizedValue = ({ answer: number })['answer'];\n",
    "type ParenthesizedMemberValue = { answer: (string) }['answer'];\n",
    "type NullMemberValue = { answer: null }['answer'];\n",
    "type StringValue = { [key: string]: boolean }[string];\n",
    "type StringNumberValue = { [key: string]: boolean }[number];\n",
    "type NumberValue = { [key: number]: string }[number];\n",
    "type NumericStringValue = { [key: number]: string }['0'];\n",
    "type NumericPrecedence = { [key: string]: string | number; [key: number]: number }['0'];\n",
    "type ReversedNumericPrecedence = { [key: number]: number; [key: string]: string | number }['0'];\n",
    "type TextPrecedence = { [key: string]: string | number; [key: number]: number }['answer'];\n",
    "type MixedPropertyValue = { answer: string; [key: string]: string | number; [key: number]: number }['answer'];\n",
    "type MixedTextFallback = { answer: string; [key: string]: string | number; [key: number]: number }['missing'];\n",
    "type MixedNumericFallback = { answer: string; [key: string]: string | number; [key: number]: number }['0'];\n",
    "type MixedSeparatedNumberFallback = { answer: string; [key: string]: string | number; [key: number]: number }[1_000];\n",
    "type MixedBroadString = { answer: string; [key: string]: string | number; [key: number]: number }[string];\n",
    "type MixedBroadNumber = { answer: string; [key: string]: string | number; [key: number]: number }[number];\n",
    "type NestedArrayValue = ({ [key: string]: number }[string])[];\n",
    "const property: PropertyValue = 1;\n",
    "const parenthesized: ParenthesizedValue = 2;\n",
    "const parenthesizedMember: ParenthesizedMemberValue = 'member';\n",
    "const nullMember: NullMemberValue = null;\n",
    "const stringValue: StringValue = true;\n",
    "const stringNumberValue: StringNumberValue = false;\n",
    "const numberValue: NumberValue = 'number';\n",
    "const numericStringValue: NumericStringValue = 'numeric';\n",
    "const numericPrecedence: NumericPrecedence = 3;\n",
    "const reversedNumericPrecedence: ReversedNumericPrecedence = 7;\n",
    "const textPrecedence: TextPrecedence = 'text';\n",
    "const mixedPropertyValue: MixedPropertyValue = 'property';\n",
    "const mixedTextFallback: MixedTextFallback = 4;\n",
    "const mixedNumericFallback: MixedNumericFallback = 5;\n",
    "const mixedSeparatedNumberFallback: MixedSeparatedNumberFallback = 1000;\n",
    "const mixedBroadString: MixedBroadString = 'broad';\n",
    "const mixedBroadNumber: MixedBroadNumber = 6;\n",
);

fn context(parsed: &ParseResult, file: FileId) -> CanonicalCheckerContext<'_> {
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            file,
            CanonicalSourceFileFacts::new(
                EscapedName::source("\"/project/indexed-access-types.ts\""),
                CanonicalSourceLanguage::TypeScript,
                false,
                CanonicalModuleState::Script,
            ),
        )
        .unwrap();
    binder
        .bind_typescript_declaration_slice(&parsed.arena, file)
        .unwrap();
    CanonicalCheckerContext::new(
        binder.finish(),
        [(file, &parsed.arena)].into_iter().collect(),
        CanonicalCheckerOptions::default(),
    )
    .unwrap()
}

fn alias_symbol(
    parsed: &ParseResult,
    file: FileId,
    context: &CanonicalCheckerContext<'_>,
    expected: &str,
) -> SemanticSymbolId {
    let declaration = parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            let NodeData::TypeAliasDeclaration(alias) = &record.data else {
                return None;
            };
            let NodeData::Identifier(name) = &parsed.arena.get(alias.name)?.data else {
                return None;
            };
            (name.text == expected).then_some(NodeRef::new(parsed.arena.id(), file, node))
        })
        .unwrap_or_else(|| panic!("missing alias {expected}"));
    let raw = context.file(file).unwrap().1.symbol(declaration).unwrap();
    context.store().get_merged_symbol(raw).unwrap()
}

fn alias_type(context: &CanonicalCheckerContext<'_>, alias: SemanticSymbolId) -> TypeId {
    context
        .store()
        .type_alias_links(alias)
        .and_then(|links| links.declared_type)
        .unwrap_or_else(|| panic!("missing declared type for {alias:?}"))
}

#[test]
fn concrete_inline_indexed_access_types_select_properties_and_applicable_indexes_cold_and_warm() {
    let parsed = parse_source_file(SUCCESS_SOURCE);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(0);
    let mut context = context(&parsed, file);

    context.check_source_file(file).unwrap();
    assert!(context.diagnostics().is_empty());
    for (name, expected) in [
        ("PropertyValue", "number"),
        ("ParenthesizedValue", "number"),
        ("ParenthesizedMemberValue", "string"),
        ("NullMemberValue", "null"),
        ("StringValue", "boolean"),
        ("StringNumberValue", "boolean"),
        ("NumberValue", "string"),
        ("NumericStringValue", "string"),
        ("NumericPrecedence", "number"),
        ("ReversedNumericPrecedence", "number"),
        ("TextPrecedence", "string | number"),
        ("MixedPropertyValue", "string"),
        ("MixedTextFallback", "string | number"),
        ("MixedNumericFallback", "number"),
        ("MixedSeparatedNumberFallback", "number"),
        ("MixedBroadString", "string | number"),
        ("MixedBroadNumber", "number"),
        ("NestedArrayValue", "{}"),
    ] {
        let alias = alias_symbol(&parsed, file, &context, name);
        assert_eq!(
            context.type_to_string(alias_type(&context, alias)).unwrap(),
            expected,
            "alias {name}",
        );
    }

    let warm = (
        context.store().type_len(),
        context.store().index_info_len(),
        context.store().signature_len(),
        context.diagnostics().clone(),
    );
    context.check_source_file(file).unwrap();
    assert_eq!(
        (
            context.store().type_len(),
            context.store().index_info_len(),
            context.store().signature_len(),
            context.diagnostics().clone(),
        ),
        warm,
    );
}

#[test]
fn invalid_tuple_index_on_any_reports_ts2538_and_reuses_the_error_type() {
    for (case, source) in [
        "var value: any[[]];",
        "var value: any[ []];",
        "var value: any [ [ ] ];",
    ]
    .into_iter()
    .enumerate()
    {
        let parsed = parse_source_file(source);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(101 + u32::try_from(case).unwrap());
        let mut context = context(&parsed, file);

        context.check_source_file(file).unwrap();

        let [diagnostic] = context.diagnostics().as_slice() else {
            panic!("expected one invalid-index diagnostic")
        };
        assert_eq!(diagnostic.diagnostic.code(), 2538);
        assert_eq!(
            diagnostic.diagnostic.render().unwrap(),
            "Type '[]' cannot be used as an index type.",
        );
        assert_eq!(diagnostic.range_override, None);

        let index = parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::TupleType).then_some(NodeRef::new(
                    parsed.arena.id(),
                    file,
                    node,
                ))
            })
            .unwrap();
        assert_eq!(diagnostic.node, Some(index));

        let indexed = parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::IndexedAccessType).then_some(NodeRef::new(
                    parsed.arena.id(),
                    file,
                    node,
                ))
            })
            .unwrap();
        let error_type = context.store().intrinsic_bootstrap().unwrap().error_type;
        assert_eq!(
            context
                .store()
                .type_node_links(indexed)
                .and_then(|links| links.resolved_type),
            Some(error_type),
        );
        assert_eq!(context.type_to_string(error_type).unwrap(), "any");

        let warm = (
            context.store().type_len(),
            context.store().index_info_len(),
            context.store().signature_len(),
            context.diagnostics().clone(),
        );
        context.recheck_source_file(file).unwrap();
        assert_eq!(
            (
                context.store().type_len(),
                context.store().index_info_len(),
                context.store().signature_len(),
                context.diagnostics().clone(),
            ),
            warm,
        );
    }
}

#[test]
fn unsupported_concrete_indexed_access_boundaries_are_atomic_and_retryable() {
    for (index, source) in [
        "type Bad = { value?: string }['value']; const bad: Bad = 'x';",
        concat!(
            "type Bad = { value?: string; [key: string]: string | undefined }['value']; ",
            "const bad: Bad = 'x';",
        ),
        "type Bad = { value: string }['missing']; const bad: Bad = 'x';",
        "type Bad = { value: string }[string]; const bad: Bad = 'x';",
        concat!(
            "type Bad = { value: string; [key: number]: string }['missing']; ",
            "const bad: Bad = 'x';",
        ),
        concat!(
            "type Bad = { [left: string]: string; [right: string]: string }['value']; ",
            "const bad: Bad = 'x';",
        ),
        concat!(
            "type Bad = { (): string; value: string; [key: string]: string }['value']; ",
            "const bad: Bad = 'x';",
        ),
        concat!(
            "type Bad = { value: number; [key: string]: string | number }['value' | 'missing']; ",
            "const bad: Bad = 'x';",
        ),
        concat!(
            "type Bad = { value: string; [key: string]: string }[boolean]; ",
            "const bad: Bad = 'x';",
        ),
        concat!(
            "type Bad = { value: boolean; [key: string]: number }['value']; ",
            "const bad: Bad = true;",
        ),
        concat!(
            "type Bad = { [key: string]: string; [key: number]: number }[number]; ",
            "const bad: Bad = 1;",
        ),
        concat!(
            "type Bad = { [key: string]: string | number | boolean | bigint | symbol; ",
            "[key: number]: unknown }[number]; const bad: Bad = 1;",
        ),
        concat!(
            "type Bad<T> = T['value']; ",
            "const bad: Bad<{ value: string }> = 'x';",
        ),
    ]
    .into_iter()
    .enumerate()
    {
        let parsed = parse_source_file(source);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(u32::try_from(index).unwrap());
        let mut context = context(&parsed, file);
        let bad = alias_symbol(&parsed, file, &context, "Bad");
        let before = (
            context.store().type_len(),
            context.store().index_info_len(),
            context.store().signature_len(),
            context.diagnostics().clone(),
        );

        let first = context.check_source_file(file).unwrap_err();
        assert!(matches!(first, SourceCheckError::DeclaredType(_)));
        assert_eq!(
            (
                context.store().type_len(),
                context.store().index_info_len(),
                context.store().signature_len(),
                context.diagnostics().clone(),
            ),
            before,
            "fixture {index}",
        );
        assert!(context.store().type_alias_links(bad).is_none());
        assert_eq!(context.check_source_file(file), Err(first));
        assert_eq!(
            (
                context.store().type_len(),
                context.store().index_info_len(),
                context.store().signature_len(),
                context.diagnostics().clone(),
            ),
            before,
            "warm fixture {index}",
        );
        assert!(context.store().type_alias_links(bad).is_none());
    }
}

#[test]
fn named_indexed_access_boundary_preserves_and_reuses_the_valid_source_prefix() {
    let parsed = parse_source_file(concat!(
        "type Model = { value: string }; ",
        "type Bad = Model['value']; const bad: Bad = 'x';",
    ));
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(100);
    let mut context = context(&parsed, file);
    let model = alias_symbol(&parsed, file, &context, "Model");
    let bad = alias_symbol(&parsed, file, &context, "Bad");
    let declarations = [
        context.get_symbol_declarations(model).unwrap().to_vec(),
        context.get_symbol_declarations(bad).unwrap().to_vec(),
    ];

    assert_eq!(context.check_source_file(file), Ok(()));
    assert!(context.diagnostics().is_empty());
    let model_type = alias_type(&context, model);
    let string_type = context.store().intrinsic_bootstrap().unwrap().string_type;
    assert_eq!(alias_type(&context, bad), string_type);
    let source_file = context.source_file(file).unwrap();
    assert!(context
        .store()
        .source_file_links(source_file)
        .is_some_and(|links| links.type_checked));
    let publications = (
        context.store().type_alias_links(model).unwrap().clone(),
        context.store().type_alias_links(bad).unwrap().clone(),
        context.store().source_file_links(source_file).unwrap().clone(),
    );
    let stable_prefix = (
        context.store().type_len(),
        context.store().index_info_len(),
        context.store().signature_len(),
        context.diagnostics().clone(),
    );

    assert_eq!(context.check_source_file(file), Ok(()));
    assert_eq!(
        (
            context.store().type_len(),
            context.store().index_info_len(),
            context.store().signature_len(),
            context.diagnostics().clone(),
        ),
        stable_prefix,
    );
    assert_eq!(alias_type(&context, model), model_type);
    assert_eq!(alias_type(&context, bad), string_type);
    assert_eq!(
        (
            context.store().type_alias_links(model).unwrap().clone(),
            context.store().type_alias_links(bad).unwrap().clone(),
            context.store().source_file_links(source_file).unwrap().clone(),
        ),
        publications,
    );
    for ((name, symbol), expected) in [("Model", model), ("Bad", bad)]
        .into_iter()
        .zip(&declarations)
    {
        assert_eq!(alias_symbol(&parsed, file, &context, name), symbol);
        assert_eq!(context.get_symbol_declarations(symbol).unwrap(), expected.as_slice());
    }
}

#[test]
fn named_indexed_access_complete_check_diagnosis_preserves_types_symbols_diagnostics_and_replay() {
    use ts_binder::SymbolFlags;
    use ts_checker::semantic::types::TypeFlags;

    for (case, source, valid_assignment) in [
        (
            "valid",
            concat!(
                "type Model = { value: string }; ",
                "type Bad = Model['value']; const bad: Bad = 'x';",
            ),
            true,
        ),
        (
            "invalid assignment copy",
            concat!(
                "type Model = { value: string }; ",
                "type Bad = Model['value']; const bad: Bad = 1;",
            ),
            false,
        ),
    ] {
        let parsed = parse_source_file(source);
        assert!(parsed.diagnostics.is_empty(), "{case} parser diagnostics");
        let file = FileId::new(100);
        let mut checker = context(&parsed, file);
        let node = |id| NodeRef::new(parsed.arena.id(), file, id);
        let resources = |checker: &CanonicalCheckerContext<'_>| {
            (
                checker.store().type_len(),
                checker.store().index_info_len(),
                checker.store().signature_len(),
                checker.diagnostics().clone(),
            )
        };
        let model = alias_symbol(&parsed, file, &checker, "Model");
        let bad = alias_symbol(&parsed, file, &checker, "Bad");
        let &[model_declaration] = checker.get_symbol_declarations(model).unwrap() else {
            panic!("{case} Model must have one source declaration")
        };
        let &[bad_declaration] = checker.get_symbol_declarations(bad).unwrap() else {
            panic!("{case} Bad must have one source declaration")
        };
        let NodeData::TypeAliasDeclaration(model_data) =
            &parsed.arena.get(model_declaration.node).unwrap().data
        else {
            panic!("{case} Model declaration must be a type alias")
        };
        let NodeData::TypeAliasDeclaration(bad_data) =
            &parsed.arena.get(bad_declaration.node).unwrap().data
        else {
            panic!("{case} Bad declaration must be a type alias")
        };
        let model_body = node(model_data.type_);
        let bad_body = node(bad_data.type_);
        let NodeData::IndexedAccessTypeNode(indexed) =
            &parsed.arena.get(bad_body.node).unwrap().data
        else {
            panic!("{case} Bad must use the original indexed access")
        };
        let NodeData::TypeReferenceNode(model_reference) =
            &parsed.arena.get(indexed.object_type).unwrap().data
        else {
            panic!("{case} indexed object must refer to Model")
        };
        let (property_declaration, property_data) = parsed
            .arena
            .iter()
            .find_map(|(id, record)| match &record.data {
                NodeData::PropertyDeclaration(property) => Some((node(id), property)),
                _ => None,
            })
            .unwrap();
        let (variable_declaration, variable_data) = parsed
            .arena
            .iter()
            .find_map(|(id, record)| match &record.data {
                NodeData::VariableDeclaration(variable) => Some((node(id), variable)),
                _ => None,
            })
            .unwrap();
        let variable_name = node(variable_data.name);
        let annotation = node(variable_data.type_.unwrap());
        let initializer = node(variable_data.initializer.unwrap());
        let NodeData::TypeReferenceNode(bad_reference) =
            &parsed.arena.get(annotation.node).unwrap().data
        else {
            panic!("{case} variable annotation must refer to Bad")
        };
        let bound_symbol = |declaration| {
            let raw = checker.file(file).unwrap().1.symbol(declaration).unwrap();
            checker.store().get_merged_symbol(raw).unwrap()
        };
        let property = bound_symbol(property_declaration);
        let variable = bound_symbol(variable_declaration);
        let source_file = checker.source_file(file).unwrap();
        let cold = resources(&checker);
        assert!(checker.store().type_alias_links(model).is_none());
        assert!(checker.store().type_alias_links(bad).is_none());
        assert!(!checker
            .store()
            .source_file_links(source_file)
            .is_some_and(|links| links.type_checked));

        assert_eq!(
            checker.check_source_file(file),
            Ok(()),
            "{case} complete check",
        );
        assert!(checker
            .store()
            .source_file_links(source_file)
            .is_some_and(|links| links.type_checked));
        let model_type = alias_type(&checker, model);
        let bad_type = alias_type(&checker, bad);
        let string_type = checker.store().intrinsic_bootstrap().unwrap().string_type;
        assert_eq!(bad_type, string_type, "{case} published Bad type");
        assert_eq!(
            checker.store().type_payload(model_type).unwrap().flags(),
            TypeFlags::OBJECT,
        );
        assert_eq!(
            checker
                .store()
                .value_symbol_links(property)
                .unwrap()
                .resolved_type,
            Some(string_type),
            "{case} published source property type",
        );
        assert_eq!(
            checker
                .store()
                .value_symbol_links(variable)
                .unwrap()
                .resolved_type,
            Some(string_type),
            "{case} published annotated variable type",
        );
        if valid_assignment {
            assert!(checker.diagnostics().is_empty(), "{case} source diagnostics");
        } else {
            let [diagnostic] = checker.diagnostics().as_slice() else {
                panic!("{case} must report one assignment diagnostic")
            };
            assert_eq!(diagnostic.diagnostic.code(), 2322);
            assert_eq!(diagnostic.node, Some(variable_name));
            assert_eq!(diagnostic.range_override, None);
            assert!(diagnostic.related_information.is_empty());
            assert_eq!(
                diagnostic.diagnostic.render().unwrap(),
                "Type 'number' is not assignable to type 'string'.",
            );
            let range = parsed.arena.get(variable_name.node).unwrap().range;
            let start = usize::try_from(range.start.get()).unwrap();
            let end = usize::try_from(range.end.get()).unwrap();
            assert_eq!(&source[start..end], "bad");
            eprintln!("R33 {case}: TS2322 at {start} length {}", end - start);
        }
        let completed = resources(&checker);
        checker.check_source_file(file).unwrap();
        assert_eq!(
            resources(&checker),
            completed,
            "{case} completed check repeat",
        );

        let symbols = [
            (node(model_data.name), model),
            (node(bad_data.name), bad),
            (node(model_reference.type_name), model),
            (node(bad_reference.type_name), bad),
            (node(property_data.name), property),
            (variable_name, variable),
        ];
        for (symbol, declaration, flags) in [
            (model, model_declaration, SymbolFlags::TYPE_ALIAS),
            (bad, bad_declaration, SymbolFlags::TYPE_ALIAS),
            (property, property_declaration, SymbolFlags::PROPERTY),
            (
                variable,
                variable_declaration,
                SymbolFlags::BLOCK_SCOPED_VARIABLE,
            ),
        ] {
            assert_eq!(checker.store().symbol(symbol).unwrap().flags(), flags);
            assert_eq!(
                checker.get_symbol_declarations(symbol).unwrap(),
                &[declaration],
            );
        }
        assert_eq!(
            checker.store().symbol(variable).unwrap().value_declaration(),
            Some(variable_declaration),
        );
        for (location, symbol) in symbols {
            assert_eq!(
                checker.get_symbol_at_location(location),
                Ok(Some(symbol)),
                "{case}",
            );
        }
        assert_eq!(checker.get_declared_type_of_symbol(model), Ok(model_type));
        assert_eq!(checker.get_declared_type_of_symbol(bad), Ok(string_type));
        for (location, expected) in [
            (model_body, model_type),
            (bad_body, string_type),
            (node(indexed.object_type), model_type),
            (node(property_data.type_.unwrap()), string_type),
            (annotation, string_type),
        ] {
            assert_eq!(
                checker.get_type_from_type_node(location),
                Ok(expected),
                "{case}",
            );
        }
        for location in [variable_declaration, variable_name] {
            assert_eq!(
                checker.get_type_at_location(location),
                Ok(string_type),
                "{case}",
            );
        }
        let initializer_type = checker.get_type_at_location(initializer).unwrap();
        assert_eq!(
            checker.is_type_assignable_to(initializer_type, string_type),
            Ok(valid_assignment),
            "{case} actual initializer assignment",
        );
        assert_eq!(checker.type_to_string(bad_type).unwrap(), "string");
        eprintln!(
            "R33 {case}: complete=true Model={:?} Bad={:?} initializer={} diagnostics={} resources cold={:?} complete={:?}",
            model_type,
            bad_type,
            checker.type_to_string(initializer_type).unwrap(),
            checker.diagnostics().len(),
            (cold.0, cold.1, cold.2),
            (completed.0, completed.1, completed.2),
        );

        let warm = resources(&checker);
        let publications = (
            checker.store().type_alias_links(model).cloned(),
            checker.store().type_alias_links(bad).cloned(),
            checker.store().value_symbol_links(property).cloned(),
            checker.store().value_symbol_links(variable).cloned(),
            checker.store().source_file_links(source_file).cloned(),
        );
        for repeat in 0..3 {
            checker.check_source_file(file).unwrap();
            checker.recheck_source_file(file).unwrap();
            assert_eq!(checker.get_declared_type_of_symbol(model), Ok(model_type));
            assert_eq!(checker.get_declared_type_of_symbol(bad), Ok(string_type));
            assert_eq!(checker.get_type_from_type_node(bad_body), Ok(string_type));
            assert_eq!(checker.get_type_at_location(variable_name), Ok(string_type));
            assert_eq!(checker.get_type_at_location(initializer), Ok(initializer_type));
            for (location, symbol) in symbols {
                assert_eq!(checker.get_symbol_at_location(location), Ok(Some(symbol)));
            }
            assert_eq!(resources(&checker), warm, "{case} repeat {repeat}");
            assert_eq!(
                (
                    checker.store().type_alias_links(model).cloned(),
                    checker.store().type_alias_links(bad).cloned(),
                    checker.store().value_symbol_links(property).cloned(),
                    checker.store().value_symbol_links(variable).cloned(),
                    checker.store().source_file_links(source_file).cloned(),
                ),
                publications,
                "{case} published identity repeat {repeat}",
            );
        }
        eprintln!(
            "R33 {case}: three check/recheck repeats retain types, symbols, diagnostics and resources {:?}",
            (warm.0, warm.1, warm.2),
        );
    }
}
