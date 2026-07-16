use ts_ast::{FileId, NodeData, NodeRef};
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
    "type StringValue = { [key: string]: boolean }[string];\n",
    "type StringNumberValue = { [key: string]: boolean }[number];\n",
    "type NumberValue = { [key: number]: string }[number];\n",
    "type NumericStringValue = { [key: number]: string }['0'];\n",
    "type NumericPrecedence = { [key: string]: string | number; [key: number]: number }['0'];\n",
    "type TextPrecedence = { [key: string]: string | number; [key: number]: number }['answer'];\n",
    "type MixedPropertyValue = { answer: string; [key: string]: string | number; [key: number]: number }['answer'];\n",
    "type MixedTextFallback = { answer: string; [key: string]: string | number; [key: number]: number }['missing'];\n",
    "type MixedNumericFallback = { answer: string; [key: string]: string | number; [key: number]: number }['0'];\n",
    "type MixedSeparatedNumberFallback = { answer: string; [key: string]: string | number; [key: number]: number }[1_000];\n",
    "type MixedBroadString = { answer: string; [key: string]: string | number; [key: number]: number }[string];\n",
    "type MixedBroadNumber = { answer: string; [key: string]: string | number; [key: number]: number }[number];\n",
    "const property: PropertyValue = 1;\n",
    "const parenthesized: ParenthesizedValue = 2;\n",
    "const stringValue: StringValue = true;\n",
    "const stringNumberValue: StringNumberValue = false;\n",
    "const numberValue: NumberValue = 'number';\n",
    "const numericStringValue: NumericStringValue = 'numeric';\n",
    "const numericPrecedence: NumericPrecedence = 3;\n",
    "const textPrecedence: TextPrecedence = 'text';\n",
    "const mixedPropertyValue: MixedPropertyValue = 'property';\n",
    "const mixedTextFallback: MixedTextFallback = 4;\n",
    "const mixedNumericFallback: MixedNumericFallback = 5;\n",
    "const mixedSeparatedNumberFallback: MixedSeparatedNumberFallback = 1000;\n",
    "const mixedBroadString: MixedBroadString = 'broad';\n",
    "const mixedBroadNumber: MixedBroadNumber = 6;\n",
);

fn context<'arena>(parsed: &'arena ParseResult, file: FileId) -> CanonicalCheckerContext<'arena> {
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
        ("StringValue", "boolean"),
        ("StringNumberValue", "boolean"),
        ("NumberValue", "string"),
        ("NumericStringValue", "string"),
        ("NumericPrecedence", "number"),
        ("TextPrecedence", "string | number"),
        ("MixedPropertyValue", "string"),
        ("MixedTextFallback", "string | number"),
        ("MixedNumericFallback", "number"),
        ("MixedSeparatedNumberFallback", "number"),
        ("MixedBroadString", "string | number"),
        ("MixedBroadNumber", "number"),
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
            "type Model = { value: string }; ",
            "type Bad = Model['value']; const bad: Bad = 'x';",
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
