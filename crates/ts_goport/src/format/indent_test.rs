//! Port of internal/format/indent_test.go.
//!
//! PORT: Go `t.Parallel()` is dropped (cargo runs tests in parallel).

use crate::format::prelude::*;

use crate::frontend::parser::{SourceFileParseOptions, parse_source_file};
use crate::frontend::tspath::Path;

// Go: format/indent_test.go:13 TestGetContainingList_NamedImports
#[test]
fn test_get_containing_list_named_imports() {
    let text = "import type {\n    AAA,\n    BBB,\n} from \"./bar\";";

    let source_file = parse_source_file(
        &SourceFileParseOptions {
            file_name: "/test.ts".to_string(),
            path: Path("/test.ts".to_string()),
            ..Default::default()
        },
        text,
        ScriptKind::TS,
    )
    .root;

    // Find ImportSpecifier nodes (AAA and BBB)
    let mut import_specifiers: Vec<Node> = Vec::new();
    for_each_descendant_of_kind(source_file, SyntaxKind::ImportSpecifier, &mut |node| {
        import_specifiers.push(node);
    });

    assert!(
        import_specifiers.len() == 2,
        "Expected 2 import specifiers, got {}",
        import_specifiers.len()
    );

    // Test GetContainingList for each import specifier
    for &specifier in &import_specifiers {
        let list = get_containing_list(specifier, source_file);
        assert!(
            list.is_some(),
            "GetContainingList should return non-nil for import specifier"
        );
        assert!(
            list.nodes().len() == 2,
            "Expected list with 2 elements, got {}",
            list.nodes().len()
        );
    }
}

// Go: format/indent_test.go:42 forEachDescendantOfKind
fn for_each_descendant_of_kind(node: Node, kind: SyntaxKind, action: &mut dyn FnMut(Node)) {
    node.for_each_child(|child| {
        if child.kind() == kind {
            action(child);
        }
        for_each_descendant_of_kind(child, kind, &mut *action);
        false
    });
}
