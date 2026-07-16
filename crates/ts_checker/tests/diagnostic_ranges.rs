use ts_ast::{FileId, NodeRef, SyntaxKind};
use ts_checker::semantic::{CanonicalCheckerDiagnosticRange, CanonicalCheckerDiagnostics};
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
