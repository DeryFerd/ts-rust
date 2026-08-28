use ts_ast::{NodeData, SyntaxKind};
use ts_parser::parse_source_file;

#[test]
fn interface_declarations_require_a_same_line_name() {
    for (source, expected) in [
        ("interface I {}", vec![SyntaxKind::InterfaceDeclaration]),
        (
            "interface /* same line */ I {}",
            vec![SyntaxKind::InterfaceDeclaration],
        ),
        (
            "interface\nI\n{}",
            vec![
                SyntaxKind::ExpressionStatement,
                SyntaxKind::ExpressionStatement,
                SyntaxKind::Block,
            ],
        ),
        (
            "interface /*\n*/ I\n{}",
            vec![
                SyntaxKind::ExpressionStatement,
                SyntaxKind::ExpressionStatement,
                SyntaxKind::Block,
            ],
        ),
    ] {
        let parsed = parse_source_file(source);
        assert!(
            parsed.diagnostics.is_empty(),
            "{source}: {:?}",
            parsed.diagnostics
        );
        let NodeData::SourceFile(file) = &parsed.arena.get(parsed.source_file).unwrap().data else {
            panic!("expected a source file");
        };
        let actual = file
            .statements
            .nodes
            .iter()
            .map(|node| parsed.arena.get(*node).unwrap().kind)
            .collect::<Vec<_>>();
        assert_eq!(actual, expected, "{source}");
    }
}
