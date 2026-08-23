use ts_ast::{FileId, NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, TypeData, TypeId,
    type_records::TypeCacheState,
};
use ts_parser::{ParseResult, parse_source_file};

fn context(parsed: &ParseResult, file: FileId) -> CanonicalCheckerContext<'_> {
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            file,
            CanonicalSourceFileFacts::new(
                EscapedName::source("\"/project/conditional-types.ts\""),
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
        .unwrap_or_else(|| panic!("missing type alias {expected}"));
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
fn concrete_conditional_types_resolve_assignability_and_preserve_warm_identity() {
    let parsed = parse_source_file(concat!(
        "type TrueResult = string extends string ? number : boolean;\n",
        "type FalseResult = string extends number ? number : boolean;\n",
        "type LiteralResult = 'value' extends string ? string : never;\n",
        "type NeverResult = never extends string ? number : boolean;\n",
        "type AnyResult = any extends string ? number : boolean;\n",
        "type UnknownResult = string extends unknown ? string : never;\n",
        "const correct: TrueResult = 1;\n",
        "const rejected: FalseResult = true;\n",
        "const literal: LiteralResult = 'value';\n",
    ));
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(0);
    let mut context = context(&parsed, file);

    context.check_source_file(file).unwrap();
    assert!(context.diagnostics().is_empty());
    for (name, expected) in [
        ("TrueResult", "number"),
        ("FalseResult", "boolean"),
        ("LiteralResult", "string"),
        ("NeverResult", "number"),
        ("AnyResult", "number | boolean"),
        ("UnknownResult", "string"),
    ] {
        let symbol = alias_symbol(&parsed, file, &context, name);
        assert_eq!(
            context
                .type_to_string(alias_type(&context, symbol))
                .unwrap(),
            expected,
            "alias {name}"
        );
    }

    let warm = (
        context.store().type_len(),
        context.store().conditional_root_len(),
        context.store().mapper_len(),
        context.diagnostics().clone(),
    );
    context.check_source_file(file).unwrap();
    assert_eq!(
        (
            context.store().type_len(),
            context.store().conditional_root_len(),
            context.store().mapper_len(),
            context.diagnostics().clone(),
        ),
        warm
    );
}

#[test]
fn distributive_conditional_aliases_filter_unions_and_keep_canonical_roots() {
    let parsed = parse_source_file(concat!(
        "type Exclude<T, U> = T extends U ? never : T;\n",
        "type Extract<T, U> = T extends U ? T : never;\n",
        "type WithoutStrings = Exclude<string | number, string>;\n",
        "type OnlyStrings = Extract<string | number, string>;\n",
        "type Empty = Extract<never, string>;\n",
        "const numberValue: WithoutStrings = 1;\n",
        "const stringValue: OnlyStrings = 'value';\n",
    ));
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(1);
    let mut context = context(&parsed, file);

    context.check_source_file(file).unwrap();
    assert!(context.diagnostics().is_empty());
    for (name, expected) in [
        ("WithoutStrings", "number"),
        ("OnlyStrings", "string"),
        ("Empty", "never"),
    ] {
        let symbol = alias_symbol(&parsed, file, &context, name);
        assert_eq!(
            context
                .type_to_string(alias_type(&context, symbol))
                .unwrap(),
            expected,
            "alias {name}"
        );
    }

    for name in ["Exclude", "Extract"] {
        let symbol = alias_symbol(&parsed, file, &context, name);
        let declared = alias_type(&context, symbol);
        let TypeData::Conditional(data) = context.store().type_payload(declared).unwrap().data()
        else {
            panic!("generic alias {name} must retain its conditional type identity")
        };
        let root = context.store().conditional_root(data.root).unwrap();
        assert!(root.is_distributive());
        assert_eq!(root.outer_type_parameters().unwrap().len(), 2);
        let TypeCacheState::Allocated(cache) = root.instantiations() else {
            panic!("conditional alias {name} must own an instantiation cache")
        };
        assert!(cache.len() >= 2);
    }
}

#[test]
fn naked_infer_parameters_resolve_only_through_the_true_branch() {
    let parsed = parse_source_file(concat!(
        "type Identity<T> = T extends infer U ? U : never;\n",
        "type Text = Identity<string>;\n",
        "type Number = Identity<number>;\n",
        "const text: Text = 'value';\n",
        "const number: Number = 1;\n",
    ));
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(2);
    let mut context = context(&parsed, file);

    context.check_source_file(file).unwrap();
    assert!(
        context.diagnostics().is_empty(),
        "{:?}",
        context.diagnostics()
    );
    for (name, expected) in [("Text", "string"), ("Number", "number")] {
        let symbol = alias_symbol(&parsed, file, &context, name);
        assert_eq!(
            context
                .type_to_string(alias_type(&context, symbol))
                .unwrap(),
            expected
        );
    }

    let symbol = alias_symbol(&parsed, file, &context, "Identity");
    let TypeData::Conditional(data) = context
        .store()
        .type_payload(alias_type(&context, symbol))
        .unwrap()
        .data()
    else {
        panic!("an infer alias must retain its deferred conditional type")
    };
    let root = context.store().conditional_root(data.root).unwrap();
    assert_eq!(root.infer_type_parameters().unwrap().len(), 1);
    assert_eq!(root.outer_type_parameters().unwrap().len(), 1);
    assert_ne!(
        root.infer_type_parameters().unwrap()[0],
        root.outer_type_parameters().unwrap()[0]
    );

    let infer_nodes = parsed
        .arena
        .iter()
        .filter(|(_, node)| node.kind == SyntaxKind::InferType)
        .count();
    assert_eq!(infer_nodes, 1);
}

#[test]
fn short_variadic_tuple_inference_preserves_warm_tuple_cache_identity() {
    let parsed = parse_source_file(concat!(
        "interface Array<T> {}\n",
        "interface ReadonlyArray<T> {}\n",
        "type Middle<T> = T extends [unknown, ...infer X, unknown] ? X : never;\n",
        "type Example = Middle<[1]>;\n",
    ));
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(3);
    let mut context = context(&parsed, file);

    context.check_source_file(file).unwrap();
    assert!(
        context.diagnostics().is_empty(),
        "{:?}",
        context.diagnostics()
    );

    let example = alias_symbol(&parsed, file, &context, "Example");
    assert_eq!(
        context
            .type_to_string(alias_type(&context, example))
            .unwrap(),
        "never"
    );

    let warm = (
        context.store().type_len(),
        context.store().conditional_root_len(),
        context.store().mapper_len(),
        context.diagnostics().clone(),
    );
    context.check_source_file(file).unwrap();
    assert_eq!(
        (
            context.store().type_len(),
            context.store().conditional_root_len(),
            context.store().mapper_len(),
            context.diagnostics().clone(),
        ),
        warm
    );
}

#[test]
fn conditional_tuple_rest_preserves_its_required_suffix() {
    let parsed = parse_source_file(concat!(
        "interface Array<T> {}\n",
        "interface ReadonlyArray<T> {}\n",
        "type EndsWithText<T> = T extends [...number[], string] ? true : false;\n",
        "type Many = EndsWithText<[number, number, string]>;\n",
        "type Only = EndsWithText<[string]>;\n",
        "type Wrong = EndsWithText<[number, number, number]>;\n",
    ));
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(4);
    let mut context = context(&parsed, file);

    context.check_source_file(file).unwrap();
    assert!(
        context.diagnostics().is_empty(),
        "{:?}",
        context.diagnostics()
    );

    for (name, expected) in [("Many", "true"), ("Only", "true"), ("Wrong", "false")] {
        let alias = alias_symbol(&parsed, file, &context, name);
        assert_eq!(
            context.type_to_string(alias_type(&context, alias)).unwrap(),
            expected,
            "alias {name}"
        );
    }

    let warm = (
        context.store().type_len(),
        context.store().conditional_root_len(),
        context.store().mapper_len(),
        context.diagnostics().clone(),
    );
    context.check_source_file(file).unwrap();
    assert_eq!(
        (
            context.store().type_len(),
            context.store().conditional_root_len(),
            context.store().mapper_len(),
            context.diagnostics().clone(),
        ),
        warm
    );
}

#[test]
fn conditional_template_inference_preserves_unicode_code_points() {
    let parsed = parse_source_file(concat!(
        "type First<T extends string> = T extends `${infer Head}${string}` ? Head : never;\n",
        "type Rest<T extends string> = T extends `${string}${infer Tail}` ? Tail : never;\n",
        "type AsciiFirst = First<\"ABC\">;\n",
        "type AsciiRest = Rest<\"ABC\">;\n",
        "type JapaneseFirst = First<\"\\u3042\\u3044\\u3046\">;\n",
        "type JapaneseRest = Rest<\"\\u3042\\u3044\\u3046\">;\n",
        "type EmojiFirst = First<\"\\u{1F600}abc\">;\n",
    ));
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(5);
    let mut context = context(&parsed, file);

    context.check_source_file(file).unwrap();
    assert!(
        context.diagnostics().is_empty(),
        "{:?}",
        context.diagnostics()
    );

    for (name, expected) in [
        ("AsciiFirst", "\"A\""),
        ("AsciiRest", "\"BC\""),
        ("JapaneseFirst", "\"\u{3042}\""),
        ("JapaneseRest", "\"\u{3044}\u{3046}\""),
        ("EmojiFirst", "\"\u{1f600}\""),
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
        context.store().conditional_root_len(),
        context.store().mapper_len(),
    );
    context.recheck_source_file(file).unwrap();
    assert_eq!(
        (
            context.store().type_len(),
            context.store().conditional_root_len(),
            context.store().mapper_len(),
        ),
        warm,
    );
}
