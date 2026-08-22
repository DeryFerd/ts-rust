use ts_ast::{FileId, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName,
};
use ts_checker::semantic::{CanonicalCheckerContext, CanonicalCheckerOptions, TypeData};
use ts_parser::{ParseResult, parse_javascript_source_file, parse_source_file};

fn context(
    parsed: &ParseResult,
    file: FileId,
    language: CanonicalSourceLanguage,
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
    CanonicalCheckerContext::new(
        binder.finish(),
        vec![(file, &parsed.arena)],
        CanonicalCheckerOptions::default(),
    )
    .unwrap()
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
