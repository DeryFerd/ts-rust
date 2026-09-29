//! Ports of the internal/scanner/scanner_test.go tests that call private
//! scanner functions (tsgo#4839): TestNormalizeJSDocTypeSourceText,
//! TestIsJSDocTypeExpressionOrChild and
//! TestGetTextOfNodeFromJSDocTypePreservesAsteriskType. A child module of
//! `scanner_util`, so it can call the private helpers. The other
//! scanner_test.go tests are in `tests/go_baselines/units_emit/scanner_parser.rs`.

use super::{
    get_text_of_node_from_source_text, is_js_doc_type_expression_or_child,
    normalize_js_doc_type_source_text,
};
use crate::prelude::*;

/// Runs `f` on a new thread and frees the factory nodes it made.
// PORT: Go builds bare `ast.Node` values. The port builds factory nodes,
// which belong to the thread that made them (see `free_synthetic_nodes`).
fn with_factory(f: impl FnOnce(&NodeFactory) + Send + 'static) {
    std::thread::spawn(move || {
        f(&NodeFactory::new());
        free_synthetic_nodes();
    })
    .join()
    .expect("test thread panicked");
}

/// Go `&ast.Node{Kind: kind, Flags: flags, Parent: parent}` for a node that
/// the factory made.
fn with_fields(node: Node, flags: NodeFlags, parent: Node) -> Node {
    set_node_flags(node, flags);
    set_node_parent(node, parent);
    node
}

// Go: scanner/scanner_test.go:25 TestNormalizeJSDocTypeSourceText
#[test]
fn test_normalize_js_doc_type_source_text() {
    let tests: [(&str, &str, &[&str]); 5] = [
        ("single line", " \t* \tFoo", &["Foo"]),
        (
            "ECMAScript line breaks",
            "Foo\r\n * Bar\r\t* Baz\u{2028} * Qux\u{2029}* Quux",
            &["Foo", "Bar", "Baz", "Qux", "Quux"],
        ),
        (
            "blank and trailing lines",
            "Foo\r\n *\r\n",
            &["Foo", "", ""],
        ),
        ("line without marker", "Foo\n  Bar", &["Foo", "Bar"]),
        ("only leading marker", "**Foo", &["*Foo"]),
    ];

    for (name, text, expected_lines) in tests {
        let expected = expected_lines.join(NewLineKind::LF.get_new_line_character());
        assert_eq!(normalize_js_doc_type_source_text(text), expected, "{name}");
    }
}

// Go: scanner/scanner_test.go:49 TestIsJSDocTypeExpressionOrChild
#[test]
fn test_is_js_doc_type_expression_or_child() {
    with_factory(|f| {
        let type_reference = || f.new_type_reference_node(f.new_identifier("T"), NodeList::NIL);

        let js_doc_type = with_fields(type_reference(), NodeFlags::JS_DOC, Node::NIL);
        let js_doc_type_child = with_fields(f.new_identifier("a"), NodeFlags::JS_DOC, js_doc_type);
        let reparsed_type = with_fields(
            f.new_type_literal_node(NodeList::NIL),
            NodeFlags::REPARSED,
            Node::NIL,
        );
        let reparsed_type_child =
            with_fields(f.new_identifier("b"), NodeFlags::REPARSED, reparsed_type);
        let ordinary_type = with_fields(type_reference(), NodeFlags::NONE, Node::NIL);
        let js_doc_tag = with_fields(
            f.new_js_doc_parameter_or_property_tag(
                SyntaxKind::JsDocParameterTag,
                f.new_identifier("param"),
                f.new_identifier("p"),
                false, /*isBracketed*/
                Node::NIL,
                false, /*isNameFirst*/
                NodeList::NIL,
            ),
            NodeFlags::JS_DOC,
            Node::NIL,
        );
        let js_doc_tag_child = with_fields(f.new_identifier("c"), NodeFlags::JS_DOC, js_doc_tag);
        let type_expression = with_fields(
            f.new_js_doc_type_expression(type_reference()),
            NodeFlags::NONE,
            Node::NIL,
        );

        let tests = [
            ("type expression", type_expression, true),
            ("JSDoc type", js_doc_type, true),
            ("JSDoc type child", js_doc_type_child, true),
            ("reparsed type", reparsed_type, true),
            ("reparsed type child", reparsed_type_child, true),
            ("ordinary type", ordinary_type, false),
            ("other JSDoc child", js_doc_tag_child, false),
        ];

        for (name, node, expected) in tests {
            assert_eq!(is_js_doc_type_expression_or_child(node), expected, "{name}");
        }
    });
}

// Go: scanner/scanner_test.go:82 TestGetTextOfNodeFromJSDocTypePreservesAsteriskType
#[test]
fn test_get_text_of_node_from_js_doc_type_preserves_asterisk_type() {
    with_factory(|f| {
        let source_text = ["", " * *"].join(NewLineKind::LF.get_new_line_character());
        let node = with_fields(f.new_js_doc_all_type(), NodeFlags::JS_DOC, Node::NIL);
        set_node_loc(node, TextRange::new(0, source_text.len() as i32));

        assert_eq!(
            get_text_of_node_from_source_text(&source_text, node, false /*includeTrivia*/),
            "*"
        );
    });
}
