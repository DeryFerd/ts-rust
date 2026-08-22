use ts_ast::{FileId, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerDiagnosticRange, CanonicalCheckerDiagnostics,
    CanonicalCheckerOptions, IntrinsicBootstrapOptions,
};
use ts_core::{TextPos, TextRange};
use ts_diagnostics::{Diagnostic, message_by_code};
use ts_parser::parse_source_file;

#[test]
fn node_default_remains_unranged_and_exact_ranges_have_distinct_identity() {
    let parsed = parse_source_file("const target = 1;");
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(0);
    let (identifier, record) = parsed
        .arena
        .iter()
        .find(|(_, record)| record.kind == SyntaxKind::Identifier)
        .unwrap();
    let anchor = NodeRef::new(parsed.arena.id(), file, identifier);
    let first = CanonicalCheckerDiagnosticRange::new(
        anchor,
        TextRange::new(
            record.range.start,
            TextPos::new(record.range.start.get() + 1),
        ),
    );
    let second = CanonicalCheckerDiagnosticRange::new(
        anchor,
        TextRange::new(
            TextPos::new(record.range.start.get() + 1),
            TextPos::new(record.range.start.get() + 2),
        ),
    );
    let diagnostic = Diagnostic::with_arguments(message_by_code(2300).unwrap(), ["target"]);
    let mut diagnostics = CanonicalCheckerDiagnostics::default();

    diagnostics.add(Some(anchor), diagnostic.clone());
    diagnostics.lookup_or_issue_at_range(first, diagnostic.clone());
    diagnostics.lookup_or_issue_at_range(first, diagnostic.clone());
    diagnostics.lookup_or_issue_at_range(second, diagnostic);

    assert_eq!(diagnostics.len(), 3);
    assert_eq!(diagnostics.as_slice()[0].node, Some(anchor));
    assert_eq!(diagnostics.as_slice()[0].range_override, None);
    assert_eq!(diagnostics.as_slice()[1].range_override, Some(first));
    assert_eq!(diagnostics.as_slice()[2].range_override, Some(second));
}

#[test]
fn anchored_range_validation_rejects_empty_outside_and_foreign_ranges() {
    let parsed = parse_source_file("const target = 1;");
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(1);
    let (identifier, record) = parsed
        .arena
        .iter()
        .find(|(_, record)| record.kind == SyntaxKind::Identifier)
        .unwrap();
    let anchor = NodeRef::new(parsed.arena.id(), file, identifier);
    let source_range = parsed.arena.get(parsed.source_file).unwrap().range;
    let valid = CanonicalCheckerDiagnosticRange::new(
        anchor,
        TextRange::new(
            record.range.start,
            TextPos::new(record.range.start.get() + 1),
        ),
    );
    let empty = CanonicalCheckerDiagnosticRange::new(
        anchor,
        TextRange::new(record.range.start, record.range.start),
    );
    let outside_anchor = CanonicalCheckerDiagnosticRange::new(
        anchor,
        TextRange::new(TextPos::new(record.range.start.get() - 1), record.range.end),
    );
    let outside_source = CanonicalCheckerDiagnosticRange::new(
        anchor,
        TextRange::new(source_range.end, TextPos::new(source_range.end.get() + 1)),
    );
    let foreign = CanonicalCheckerDiagnosticRange::new(
        NodeRef::new(parsed.arena.id(), FileId::new(2), identifier),
        valid.range(),
    );

    assert!(valid.is_valid_for(anchor, record.range, source_range));
    assert!(!empty.is_valid_for(anchor, record.range, source_range));
    assert!(!outside_anchor.is_valid_for(anchor, record.range, source_range));
    assert!(!outside_source.is_valid_for(anchor, record.range, source_range));
    assert!(!foreign.is_valid_for(anchor, record.range, source_range));
}

#[test]
fn discriminated_union_excess_properties_keep_exact_names_in_both_orders() {
    let text = concat!(
        "type Item = ",
        "{ kind: \"a\"; subkind: 0; value: string } | ",
        "{ kind: \"a\"; subkind: 1; value: number } | ",
        "{ kind: \"b\" };\n",
        "const first: Item = { subkind: 1, kind: \"b\" };\n",
        "const second: Item = { kind: \"b\", subkind: 1 };\n",
    );
    let parsed = parse_source_file(text);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(3);
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            file,
            CanonicalSourceFileFacts::new(
                EscapedName::source("\"/project/discriminated-union.ts\""),
                CanonicalSourceLanguage::TypeScript,
                false,
                CanonicalModuleState::Script,
            ),
        )
        .unwrap();
    binder
        .bind_typescript_declaration_slice(&parsed.arena, file)
        .unwrap();
    let mut context = CanonicalCheckerContext::new(
        binder.finish(),
        [(file, &parsed.arena)].into_iter().collect(),
        CanonicalCheckerOptions::default(),
    )
    .unwrap();

    context.check_source_file(file).unwrap();

    let diagnostics = context.diagnostics().as_slice();
    assert_eq!(diagnostics.len(), 2, "{diagnostics:?}");
    for diagnostic in diagnostics {
        assert_eq!(diagnostic.diagnostic.code(), 2353);
        assert_eq!(
            diagnostic.diagnostic.render().unwrap(),
            "Object literal may only specify known properties, and 'subkind' does not exist in type '{ kind: \"b\"; }'."
        );
        let node = parsed
            .arena
            .get(diagnostic.node.expect("excess property has a node").node)
            .unwrap();
        let start = usize::try_from(node.range.start.get()).unwrap();
        let end = usize::try_from(node.range.end.get()).unwrap();
        assert_eq!(&text[start..end], "subkind");
        assert_eq!(diagnostic.range_override, None);
        assert!(diagnostic.related_information.is_empty());
    }

    let published = context.diagnostics().clone();
    context.check_source_file(file).unwrap();
    assert_eq!(context.diagnostics(), &published);
}

#[test]
fn exact_optional_assignments_emit_complete_property_relation_chains() {
    let text = concat!(
        "type Optional = { value?: string };\n",
        "declare let uncertain: string | undefined;\n",
        "const direct: Optional = { value: undefined };\n",
        "const union: Optional = { value: uncertain };\n",
    );
    let parsed = parse_source_file(text);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);

    let file = FileId::new(10);
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            file,
            CanonicalSourceFileFacts::new(
                EscapedName::source("\"/project/exact-optional-assignment.ts\""),
                CanonicalSourceLanguage::TypeScript,
                false,
                CanonicalModuleState::Script,
            ),
        )
        .unwrap();
    binder
        .bind_typescript_declaration_slice(&parsed.arena, file)
        .unwrap();
    let mut context = CanonicalCheckerContext::new(
        binder.finish(),
        [(file, &parsed.arena)].into_iter().collect(),
        CanonicalCheckerOptions {
            intrinsic: IntrinsicBootstrapOptions {
                strict_null_checks: true,
                exact_optional_property_types: true,
            },
            ..CanonicalCheckerOptions::default()
        },
    )
    .unwrap();

    context.check_source_file(file).unwrap();

    let diagnostics = context.diagnostics().as_slice();
    assert_eq!(diagnostics.len(), 2, "{diagnostics:?}");
    for (diagnostic, name, expected) in [
        (
            &diagnostics[0],
            "direct",
            concat!(
                "Type '{ value: undefined; }' is not assignable to type 'Optional' ",
                "with 'exactOptionalPropertyTypes: true'. Consider adding 'undefined' ",
                "to the types of the target's properties.\n",
                "  Types of property 'value' are incompatible.\n",
                "    Type 'undefined' is not assignable to type 'string'.",
            ),
        ),
        (
            &diagnostics[1],
            "union",
            concat!(
                "Type '{ value: string | undefined; }' is not assignable to type ",
                "'Optional' with 'exactOptionalPropertyTypes: true'. Consider ",
                "adding 'undefined' to the types of the target's properties.\n",
                "  Types of property 'value' are incompatible.\n",
                "    Type 'string | undefined' is not assignable to type 'string'.\n",
                "      Type 'undefined' is not assignable to type 'string'.",
            ),
        ),
    ] {
        assert_eq!(diagnostic.diagnostic.code(), 2375);
        assert_eq!(diagnostic.diagnostic.render().unwrap(), expected);
        let node = parsed
            .arena
            .get(diagnostic.node.expect("assignment has an anchor").node)
            .unwrap();
        let start = usize::try_from(node.range.start.get()).unwrap();
        let end = usize::try_from(node.range.end.get()).unwrap();
        assert_eq!(&text[start..end], name);
        assert_eq!(diagnostic.range_override, None);
        assert!(diagnostic.related_information.is_empty());
    }

    let published = context.diagnostics().clone();
    context.check_source_file(file).unwrap();
    assert_eq!(context.diagnostics(), &published);
}
