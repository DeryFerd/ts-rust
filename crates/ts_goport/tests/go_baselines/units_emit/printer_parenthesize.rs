//! Port of the TestParenthesize* tests of internal/printer/printer_test.go:
//! factory trees that the printer must parenthesize.
//!
//! PORT: Go `var factory ast.NodeFactory` is `NodeFactory::new()` (the
//! synthetic arena). Go `factory.NewSourceFile(ast.SourceFileParseOptions{
//! FileName: "/file.ts", Path: "/file.ts"}, "", statements, eof)` is
//! `new_source_file(&f, statements, eof)`.

use super::emittestutil::check_emit;
use super::parsetestutil::mark_synthetic_recursive;
use super::{Subtests, must, nil};
use ts_goport::prelude::*;

/// Go `factory.NewSourceFile(ast.SourceFileParseOptions{FileName: "/file.ts",
/// Path: "/file.ts"}, "", statements, endOfFileToken)`.
fn new_source_file(f: &NodeFactory, statements: NodeList, end_of_file_token: Node) -> Node {
    f.new_source_file("/file.ts", "/file.ts", "", statements, end_of_file_token)
}

// Go: printer/printer_test.go:592 TestParenthesizeDecorator
#[test]
fn parenthesize_decorator() {
    let f = NodeFactory::new();
    let file = new_source_file(
        &f,
        f.new_node_list(&[f.new_class_declaration(
            f.new_modifier_list(&[f.new_decorator(f.new_binary_expression(
                nil(), /*modifiers*/
                f.new_identifier("a"),
                nil(), /*typeNode*/
                f.new_token(SyntaxKind::PlusToken),
                f.new_identifier("b"),
            ))]),
            f.new_identifier("C"),
            nil(),
            nil(),
            f.new_node_list(&[]),
        )]),
        f.new_token(SyntaxKind::EndOfFile),
    );

    mark_synthetic_recursive(file);
    must(check_emit(None, file, "@(a + b)\nclass C {\n}"));
}

// Go: printer/printer_test.go:624 TestParenthesizeComputedPropertyName
#[test]
fn parenthesize_computed_property_name() {
    let f = NodeFactory::new();
    let file = new_source_file(
        &f,
        f.new_node_list(&[f.new_class_declaration(
            nil(), /*modifiers*/
            f.new_identifier("C"),
            nil(), /*typeParameters*/
            nil(), /*heritageClauses*/
            f.new_node_list(&[f.new_property_declaration(
                nil(), /*modifiers*/
                f.new_computed_property_name(
                    // will be parenthesized on emit:
                    f.new_binary_expression(
                        nil(), /*modifiers*/
                        f.new_identifier("a"),
                        nil(), /*typeNode*/
                        f.new_token(SyntaxKind::CommaToken),
                        f.new_identifier("b"),
                    ),
                ),
                nil(), /*postfixToken*/
                nil(), /*typeNode*/
                nil(), /*initializer*/
            )]),
        )]),
        f.new_token(SyntaxKind::EndOfFile),
    );

    mark_synthetic_recursive(file);
    must(check_emit(None, file, "class C {\n    [(a, b)];\n}"));
}

// Go: printer/printer_test.go:661 TestParenthesizeArrayLiteral
#[test]
fn parenthesize_array_literal() {
    let f = NodeFactory::new();
    let file = new_source_file(
        &f,
        f.new_node_list(&[f.new_expression_statement(f.new_array_literal_expression(
            f.new_node_list(&[
                // will be parenthesized on emit:
                f.new_binary_expression(
                    nil(), /*modifiers*/
                    f.new_identifier("a"),
                    nil(), /*typeNode*/
                    f.new_token(SyntaxKind::CommaToken),
                    f.new_identifier("b"),
                ),
            ]),
            false, /*multiLine*/
        ))]),
        f.new_token(SyntaxKind::EndOfFile),
    );

    mark_synthetic_recursive(file);
    must(check_emit(None, file, "[(a, b)];"));
}

// Go: printer/printer_test.go:691 TestParenthesizePropertyAccess1
#[test]
fn parenthesize_property_access1() {
    let f = NodeFactory::new();
    let file = new_source_file(
        &f,
        f.new_node_list(
            &[f.new_expression_statement(f.new_property_access_expression(
                // will be parenthesized on emit:
                f.new_binary_expression(
                    nil(), /*modifiers*/
                    f.new_identifier("a"),
                    nil(), /*typeNode*/
                    f.new_token(SyntaxKind::CommaToken),
                    f.new_identifier("b"),
                ),
                nil(), /*questionDotToken*/
                f.new_identifier("c"),
                NodeFlags::NONE,
            ))],
        ),
        f.new_token(SyntaxKind::EndOfFile),
    );

    mark_synthetic_recursive(file);
    must(check_emit(None, file, "(a, b).c;"));
}

// Go: printer/printer_test.go:719 TestParenthesizePropertyAccess2
#[test]
fn parenthesize_property_access2() {
    let f = NodeFactory::new();
    let file = new_source_file(
        &f,
        f.new_node_list(
            &[f.new_expression_statement(f.new_property_access_expression(
                // will be parenthesized on emit:
                f.new_property_access_expression(
                    f.new_identifier("a"),
                    f.new_token(SyntaxKind::QuestionDotToken),
                    f.new_identifier("b"),
                    NodeFlags::OPTIONAL_CHAIN,
                ),
                nil(), /*questionDotToken*/
                f.new_identifier("c"),
                NodeFlags::NONE,
            ))],
        ),
        f.new_token(SyntaxKind::EndOfFile),
    );

    mark_synthetic_recursive(file);
    must(check_emit(None, file, "(a?.b).c;"));
}

// Go: printer/printer_test.go:746 TestParenthesizePropertyAccess3
#[test]
fn parenthesize_property_access3() {
    let f = NodeFactory::new();
    let file = new_source_file(
        &f,
        f.new_node_list(
            &[f.new_expression_statement(f.new_property_access_expression(
                // will be parenthesized on emit:
                f.new_new_expression(
                    f.new_identifier("a"),
                    nil(), /*typeArguments*/
                    nil(), /*arguments*/
                ),
                nil(), /*questionDotToken*/
                f.new_identifier("b"),
                NodeFlags::NONE,
            ))],
        ),
        f.new_token(SyntaxKind::EndOfFile),
    );

    mark_synthetic_recursive(file);
    must(check_emit(None, file, "(new a).b;"));
}

// Go: printer/printer_test.go:772 TestParenthesizeElementAccess1
#[test]
fn parenthesize_element_access1() {
    let f = NodeFactory::new();
    let file = new_source_file(
        &f,
        f.new_node_list(
            &[f.new_expression_statement(f.new_element_access_expression(
                // will be parenthesized on emit:
                f.new_binary_expression(
                    nil(), /*modifiers*/
                    f.new_identifier("a"),
                    nil(), /*typeNode*/
                    f.new_token(SyntaxKind::CommaToken),
                    f.new_identifier("b"),
                ),
                nil(), /*questionDotToken*/
                f.new_identifier("c"),
                NodeFlags::NONE,
            ))],
        ),
        f.new_token(SyntaxKind::EndOfFile),
    );

    mark_synthetic_recursive(file);
    must(check_emit(None, file, "(a, b)[c];"));
}

// Go: printer/printer_test.go:800 TestParenthesizeElementAccess2
#[test]
fn parenthesize_element_access2() {
    let f = NodeFactory::new();
    let file = new_source_file(
        &f,
        f.new_node_list(
            &[f.new_expression_statement(f.new_element_access_expression(
                // will be parenthesized on emit:
                f.new_property_access_expression(
                    f.new_identifier("a"),
                    f.new_token(SyntaxKind::QuestionDotToken),
                    f.new_identifier("b"),
                    NodeFlags::OPTIONAL_CHAIN,
                ),
                nil(), /*questionDotToken*/
                f.new_identifier("c"),
                NodeFlags::NONE,
            ))],
        ),
        f.new_token(SyntaxKind::EndOfFile),
    );

    mark_synthetic_recursive(file);
    must(check_emit(None, file, "(a?.b)[c];"));
}

// Go: printer/printer_test.go:827 TestParenthesizeElementAccess3
#[test]
fn parenthesize_element_access3() {
    let f = NodeFactory::new();
    let file = new_source_file(
        &f,
        f.new_node_list(
            &[f.new_expression_statement(f.new_element_access_expression(
                // will be parenthesized on emit:
                f.new_new_expression(
                    f.new_identifier("a"),
                    nil(), /*typeArguments*/
                    nil(), /*arguments*/
                ),
                nil(), /*questionDotToken*/
                f.new_identifier("b"),
                NodeFlags::NONE,
            ))],
        ),
        f.new_token(SyntaxKind::EndOfFile),
    );

    mark_synthetic_recursive(file);
    must(check_emit(None, file, "(new a)[b];"));
}

// Go: printer/printer_test.go:853 TestParenthesizeCall1
#[test]
fn parenthesize_call1() {
    let f = NodeFactory::new();
    let file = new_source_file(
        &f,
        f.new_node_list(&[f.new_expression_statement(f.new_call_expression(
            // will be parenthesized on emit:
            f.new_binary_expression(
                nil(), /*modifiers*/
                f.new_identifier("a"),
                nil(), /*typeNode*/
                f.new_token(SyntaxKind::CommaToken),
                f.new_identifier("b"),
            ),
            nil(), /*questionDotToken*/
            nil(), /*typeArguments*/
            f.new_node_list(&[]),
            NodeFlags::NONE,
        ))]),
        f.new_token(SyntaxKind::EndOfFile),
    );

    mark_synthetic_recursive(file);
    must(check_emit(None, file, "(a, b)();"));
}

// Go: printer/printer_test.go:882 TestParenthesizeCall2
#[test]
fn parenthesize_call2() {
    let f = NodeFactory::new();
    let file = new_source_file(
        &f,
        f.new_node_list(&[f.new_expression_statement(f.new_call_expression(
            // will be parenthesized on emit:
            f.new_property_access_expression(
                f.new_identifier("a"),
                f.new_token(SyntaxKind::QuestionDotToken),
                f.new_identifier("b"),
                NodeFlags::OPTIONAL_CHAIN,
            ),
            nil(), /*questionDotToken*/
            nil(), /*typeArguments*/
            f.new_node_list(&[]),
            NodeFlags::NONE,
        ))]),
        f.new_token(SyntaxKind::EndOfFile),
    );

    mark_synthetic_recursive(file);
    must(check_emit(None, file, "(a?.b)();"));
}

// Go: printer/printer_test.go:910 TestParenthesizeCall3
#[test]
fn parenthesize_call3() {
    let f = NodeFactory::new();
    let file = new_source_file(
        &f,
        f.new_node_list(&[f.new_expression_statement(f.new_call_expression(
            // will be parenthesized on emit:
            f.new_new_expression(
                f.new_identifier("C"),
                nil(), /*typeArguments*/
                nil(), /*arguments*/
            ),
            nil(), /*questionDotToken*/
            nil(), /*typeArguments*/
            f.new_node_list(&[]),
            NodeFlags::NONE,
        ))]),
        f.new_token(SyntaxKind::EndOfFile),
    );

    mark_synthetic_recursive(file);
    must(check_emit(None, file, "(new C)();"));
}

// Go: printer/printer_test.go:937 TestParenthesizeCall4
#[test]
fn parenthesize_call4() {
    let f = NodeFactory::new();
    let file = new_source_file(
        &f,
        f.new_node_list(&[f.new_expression_statement(f.new_call_expression(
            f.new_identifier("a"),
            nil(), /*questionDotToken*/
            nil(), /*typeArguments*/
            f.new_node_list(&[f.new_binary_expression(
                nil(), /*modifiers*/
                f.new_identifier("b"),
                nil(), /*typeNode*/
                f.new_token(SyntaxKind::CommaToken),
                f.new_identifier("c"),
            )]),
            NodeFlags::NONE,
        ))]),
        f.new_token(SyntaxKind::EndOfFile),
    );

    mark_synthetic_recursive(file);
    must(check_emit(None, file, "a((b, c));"));
}

// Go: printer/printer_test.go:967 TestParenthesizeNew1
#[test]
fn parenthesize_new1() {
    let f = NodeFactory::new();
    let file = new_source_file(
        &f,
        f.new_node_list(&[f.new_expression_statement(f.new_new_expression(
            // will be parenthesized on emit:
            f.new_binary_expression(
                nil(), /*modifiers*/
                f.new_identifier("a"),
                nil(), /*typeNode*/
                f.new_token(SyntaxKind::CommaToken),
                f.new_identifier("b"),
            ),
            nil(), /*typeArguments*/
            f.new_node_list(&[]),
        ))]),
        f.new_token(SyntaxKind::EndOfFile),
    );

    mark_synthetic_recursive(file);
    must(check_emit(None, file, "new (a, b)();"));
}

// Go: printer/printer_test.go:994 TestParenthesizeNew2
#[test]
fn parenthesize_new2() {
    let f = NodeFactory::new();
    let file = new_source_file(
        &f,
        f.new_node_list(&[f.new_expression_statement(f.new_new_expression(
            // will be parenthesized on emit:
            f.new_call_expression(
                f.new_identifier("C"),
                nil(), /*questionDotToken*/
                nil(), /*typeArguments*/
                f.new_node_list(&[]),
                NodeFlags::NONE,
            ),
            nil(), /*typeArguments*/
            nil(), /*arguments*/
        ))]),
        f.new_token(SyntaxKind::EndOfFile),
    );

    mark_synthetic_recursive(file);
    must(check_emit(None, file, "new (C());"));
}

// Go: printer/printer_test.go:1021 TestParenthesizeNew3
#[test]
fn parenthesize_new3() {
    let f = NodeFactory::new();
    let file = new_source_file(
        &f,
        f.new_node_list(&[f.new_expression_statement(f.new_new_expression(
            f.new_identifier("C"),
            nil(), /*typeArguments*/
            f.new_node_list(&[f.new_binary_expression(
                nil(), /*modifiers*/
                f.new_identifier("a"),
                nil(), /*typeNode*/
                f.new_token(SyntaxKind::CommaToken),
                f.new_identifier("b"),
            )]),
        ))]),
        f.new_token(SyntaxKind::EndOfFile),
    );

    mark_synthetic_recursive(file);
    must(check_emit(None, file, "new C((a, b));"));
}

// Go: printer/printer_test.go:1049 TestParenthesizeTaggedTemplate1
#[test]
fn parenthesize_tagged_template1() {
    let f = NodeFactory::new();
    let file = new_source_file(
        &f,
        f.new_node_list(
            &[f.new_expression_statement(f.new_tagged_template_expression(
                // will be parenthesized on emit:
                f.new_binary_expression(
                    nil(), /*modifiers*/
                    f.new_identifier("a"),
                    nil(), /*typeNode*/
                    f.new_token(SyntaxKind::CommaToken),
                    f.new_identifier("b"),
                ),
                nil(), /*questionDotToken*/
                nil(), /*typeArguments*/
                f.new_no_substitution_template_literal("", TokenFlags::NONE),
                NodeFlags::NONE,
            ))],
        ),
        f.new_token(SyntaxKind::EndOfFile),
    );

    mark_synthetic_recursive(file);
    must(check_emit(None, file, "(a, b) ``;"));
}

// Go: printer/printer_test.go:1078 TestParenthesizeTaggedTemplate2
#[test]
fn parenthesize_tagged_template2() {
    let f = NodeFactory::new();
    let file = new_source_file(
        &f,
        f.new_node_list(
            &[f.new_expression_statement(f.new_tagged_template_expression(
                // will be parenthesized on emit:
                f.new_property_access_expression(
                    f.new_identifier("a"),
                    f.new_token(SyntaxKind::QuestionDotToken),
                    f.new_identifier("b"),
                    NodeFlags::OPTIONAL_CHAIN,
                ),
                nil(), /*questionDotToken*/
                nil(), /*typeArguments*/
                f.new_no_substitution_template_literal("", TokenFlags::NONE),
                NodeFlags::NONE,
            ))],
        ),
        f.new_token(SyntaxKind::EndOfFile),
    );

    mark_synthetic_recursive(file);
    must(check_emit(None, file, "(a?.b) ``;"));
}

// Go: printer/printer_test.go:1106 TestParenthesizeTypeAssertion1
#[test]
fn parenthesize_type_assertion1() {
    let f = NodeFactory::new();
    let file = new_source_file(
        &f,
        f.new_node_list(&[f.new_expression_statement(f.new_type_assertion(
            f.new_type_reference_node(f.new_identifier("T"), nil() /*typeArguments*/),
            // will be parenthesized on emit:
            f.new_binary_expression(
                nil(), /*modifiers*/
                f.new_identifier("a"),
                nil(), /*typeNode*/
                f.new_token(SyntaxKind::PlusToken),
                f.new_identifier("b"),
            ),
        ))]),
        f.new_token(SyntaxKind::EndOfFile),
    );

    mark_synthetic_recursive(file);
    must(check_emit(None, file, "<T>(a + b);"));
}

// Go: printer/printer_test.go:1135 TestParenthesizeArrowFunction1
#[test]
fn parenthesize_arrow_function1() {
    let f = NodeFactory::new();
    let file = new_source_file(
        &f,
        f.new_node_list(&[f.new_expression_statement(f.new_arrow_function(
            nil(), /*modifiers*/
            nil(), /*typeParameters*/
            f.new_node_list(&[]),
            nil(), /*returnType*/
            nil(), /*fullSignature*/
            f.new_token(SyntaxKind::EqualsGreaterThanToken),
            // will be parenthesized on emit:
            f.new_object_literal_expression(f.new_node_list(&[]), false /*multiLine*/),
        ))]),
        f.new_token(SyntaxKind::EndOfFile),
    );

    mark_synthetic_recursive(file);
    must(check_emit(None, file, "() => ({});"));
}

// Go: printer/printer_test.go:1163 TestParenthesizeArrowFunction2
#[test]
fn parenthesize_arrow_function2() {
    let f = NodeFactory::new();
    let file = new_source_file(
        &f,
        f.new_node_list(&[f.new_expression_statement(f.new_arrow_function(
            nil(), /*modifiers*/
            nil(), /*typeParameters*/
            f.new_node_list(&[]),
            nil(), /*returnType*/
            nil(), /*fullSignature*/
            f.new_token(SyntaxKind::EqualsGreaterThanToken),
            // will be parenthesized on emit:
            f.new_property_access_expression(
                f.new_object_literal_expression(f.new_node_list(&[]), false /*multiLine*/),
                nil(), /*questionDotToken*/
                f.new_identifier("a"),
                NodeFlags::NONE,
            ),
        ))]),
        f.new_token(SyntaxKind::EndOfFile),
    );

    mark_synthetic_recursive(file);
    must(check_emit(None, file, "() => ({}.a);"));
}

// Go: printer/printer_test.go:1196 TestParenthesizeDelete
#[test]
fn parenthesize_delete() {
    let f = NodeFactory::new();
    let file = new_source_file(
        &f,
        f.new_node_list(&[f.new_expression_statement(f.new_delete_expression(
            // will be parenthesized on emit:
            f.new_binary_expression(
                nil(), /*modifiers*/
                f.new_identifier("a"),
                nil(), /*typeNode*/
                f.new_token(SyntaxKind::PlusToken),
                f.new_identifier("b"),
            ),
        ))]),
        f.new_token(SyntaxKind::EndOfFile),
    );

    mark_synthetic_recursive(file);
    must(check_emit(None, file, "delete (a + b);"));
}

// Go: printer/printer_test.go:1221 TestParenthesizeVoid
#[test]
fn parenthesize_void() {
    let f = NodeFactory::new();
    let file = new_source_file(
        &f,
        f.new_node_list(&[f.new_expression_statement(f.new_void_expression(
            // will be parenthesized on emit:
            f.new_binary_expression(
                nil(), /*modifiers*/
                f.new_identifier("a"),
                nil(), /*typeNode*/
                f.new_token(SyntaxKind::PlusToken),
                f.new_identifier("b"),
            ),
        ))]),
        f.new_token(SyntaxKind::EndOfFile),
    );

    mark_synthetic_recursive(file);
    must(check_emit(None, file, "void (a + b);"));
}

// Go: printer/printer_test.go:1246 TestParenthesizeTypeOf
#[test]
fn parenthesize_type_of() {
    let f = NodeFactory::new();
    let file = new_source_file(
        &f,
        f.new_node_list(&[f.new_expression_statement(f.new_type_of_expression(
            // will be parenthesized on emit:
            f.new_binary_expression(
                nil(), /*modifiers*/
                f.new_identifier("a"),
                nil(), /*typeNode*/
                f.new_token(SyntaxKind::PlusToken),
                f.new_identifier("b"),
            ),
        ))]),
        f.new_token(SyntaxKind::EndOfFile),
    );

    mark_synthetic_recursive(file);
    must(check_emit(None, file, "typeof (a + b);"));
}

// Go: printer/printer_test.go:1271 TestParenthesizeAwait
#[test]
fn parenthesize_await() {
    let f = NodeFactory::new();
    let file = new_source_file(
        &f,
        f.new_node_list(&[f.new_expression_statement(f.new_await_expression(
            // will be parenthesized on emit:
            f.new_binary_expression(
                nil(), /*modifiers*/
                f.new_identifier("a"),
                nil(), /*typeNode*/
                f.new_token(SyntaxKind::PlusToken),
                f.new_identifier("b"),
            ),
        ))]),
        f.new_token(SyntaxKind::EndOfFile),
    );

    mark_synthetic_recursive(file);
    must(check_emit(None, file, "await (a + b);"));
}

// Go: printer/printer_test.go:1422 TestParenthesizeConditional1
#[test]
fn parenthesize_conditional1() {
    let f = NodeFactory::new();
    let file = new_source_file(
        &f,
        f.new_node_list(&[f.new_expression_statement(f.new_conditional_expression(
            // will be parenthesized on emit:
            f.new_binary_expression(
                nil(), /*modifiers*/
                f.new_identifier("a"),
                nil(), /*typeNode*/
                f.new_token(SyntaxKind::CommaToken),
                f.new_identifier("b"),
            ),
            f.new_token(SyntaxKind::QuestionToken),
            f.new_identifier("c"),
            f.new_token(SyntaxKind::ColonToken),
            f.new_identifier("d"),
        ))]),
        f.new_token(SyntaxKind::EndOfFile),
    );

    mark_synthetic_recursive(file);
    must(check_emit(None, file, "(a, b) ? c : d;"));
}

// Go: printer/printer_test.go:1451 TestParenthesizeConditional2
#[test]
fn parenthesize_conditional2() {
    let f = NodeFactory::new();
    let file = new_source_file(
        &f,
        f.new_node_list(&[f.new_expression_statement(f.new_conditional_expression(
            // will be parenthesized on emit:
            f.new_binary_expression(
                nil(), /*modifiers*/
                f.new_identifier("a"),
                nil(), /*typeNode*/
                f.new_token(SyntaxKind::EqualsToken),
                f.new_identifier("b"),
            ),
            f.new_token(SyntaxKind::QuestionToken),
            f.new_identifier("c"),
            f.new_token(SyntaxKind::ColonToken),
            f.new_identifier("d"),
        ))]),
        f.new_token(SyntaxKind::EndOfFile),
    );

    mark_synthetic_recursive(file);
    must(check_emit(None, file, "(a = b) ? c : d;"));
}

// Go: printer/printer_test.go:1480 TestParenthesizeConditional3
#[test]
fn parenthesize_conditional3() {
    let f = NodeFactory::new();
    let file = new_source_file(
        &f,
        f.new_node_list(&[f.new_expression_statement(f.new_conditional_expression(
            // will be parenthesized on emit:
            f.new_arrow_function(
                nil(), /*modifiers*/
                nil(), /*typeParameters*/
                f.new_node_list(&[]),
                nil(), /*returnType*/
                nil(), /*fullSignature*/
                f.new_token(SyntaxKind::EqualsGreaterThanToken),
                f.new_block(f.new_node_list(&[]), false /*multiLine*/),
            ),
            f.new_token(SyntaxKind::QuestionToken),
            f.new_identifier("a"),
            f.new_token(SyntaxKind::ColonToken),
            f.new_identifier("b"),
        ))]),
        f.new_token(SyntaxKind::EndOfFile),
    );

    mark_synthetic_recursive(file);
    must(check_emit(None, file, "(() => { }) ? a : b;"));
}

// Go: printer/printer_test.go:1514 TestParenthesizeConditional4
#[test]
fn parenthesize_conditional4() {
    let f = NodeFactory::new();
    let file = new_source_file(
        &f,
        f.new_node_list(&[f.new_expression_statement(f.new_conditional_expression(
            // will be parenthesized on emit:
            f.new_yield_expression(nil(), nil()),
            f.new_token(SyntaxKind::QuestionToken),
            f.new_identifier("a"),
            f.new_token(SyntaxKind::ColonToken),
            f.new_identifier("b"),
        ))]),
        f.new_token(SyntaxKind::EndOfFile),
    );

    mark_synthetic_recursive(file);
    must(check_emit(None, file, "(yield) ? a : b;"));
}

// Go: printer/printer_test.go:1537 TestParenthesizeConditional5
#[test]
fn parenthesize_conditional5() {
    let f = NodeFactory::new();
    let file = new_source_file(
        &f,
        f.new_node_list(&[f.new_expression_statement(f.new_conditional_expression(
            f.new_identifier("a"),
            f.new_token(SyntaxKind::QuestionToken),
            // will be parenthesized on emit:
            f.new_binary_expression(
                nil(), /*modifiers*/
                f.new_identifier("b"),
                nil(), /*typeNode*/
                f.new_token(SyntaxKind::CommaToken),
                f.new_identifier("c"),
            ),
            f.new_token(SyntaxKind::ColonToken),
            f.new_identifier("d"),
        ))]),
        f.new_token(SyntaxKind::EndOfFile),
    );

    mark_synthetic_recursive(file);
    must(check_emit(None, file, "a ? (b, c) : d;"));
}

// Go: printer/printer_test.go:1566 TestParenthesizeConditional6
#[test]
fn parenthesize_conditional6() {
    let f = NodeFactory::new();
    let file = new_source_file(
        &f,
        f.new_node_list(&[f.new_expression_statement(f.new_conditional_expression(
            f.new_identifier("a"),
            f.new_token(SyntaxKind::QuestionToken),
            f.new_identifier("b"),
            f.new_token(SyntaxKind::ColonToken),
            // will be parenthesized on emit:
            f.new_binary_expression(
                nil(), /*modifiers*/
                f.new_identifier("c"),
                nil(), /*typeNode*/
                f.new_token(SyntaxKind::CommaToken),
                f.new_identifier("d"),
            ),
        ))]),
        f.new_token(SyntaxKind::EndOfFile),
    );

    mark_synthetic_recursive(file);
    must(check_emit(None, file, "a ? b : (c, d);"));
}

// Go: printer/printer_test.go:1595 TestParenthesizeYield1
#[test]
fn parenthesize_yield1() {
    let f = NodeFactory::new();
    let file = new_source_file(
        &f,
        f.new_node_list(&[f.new_expression_statement(f.new_yield_expression(
            nil(), /*asteriskToken*/
            // will be parenthesized on emit:
            f.new_binary_expression(
                nil(), /*modifiers*/
                f.new_identifier("a"),
                nil(), /*typeNode*/
                f.new_token(SyntaxKind::CommaToken),
                f.new_identifier("b"),
            ),
        ))]),
        f.new_token(SyntaxKind::EndOfFile),
    );

    mark_synthetic_recursive(file);
    must(check_emit(None, file, "yield (a, b);"));
}

// Go: printer/printer_test.go:1625 TestParenthesizeSpreadElement1
#[test]
fn parenthesize_spread_element1() {
    let f = NodeFactory::new();
    let file = new_source_file(
        &f,
        f.new_node_list(&[f.new_expression_statement(f.new_array_literal_expression(
            f.new_node_list(&[f.new_spread_element(
                // will be parenthesized on emit:
                f.new_binary_expression(
                    nil(), /*modifiers*/
                    f.new_identifier("a"),
                    nil(), /*typeNode*/
                    f.new_token(SyntaxKind::CommaToken),
                    f.new_identifier("b"),
                ),
            )]),
            false, /*multiLine*/
        ))]),
        f.new_token(SyntaxKind::EndOfFile),
    );

    mark_synthetic_recursive(file);
    must(check_emit(None, file, "[...(a, b)];"));
}

// Go: printer/printer_test.go:1657 TestParenthesizeSpreadElement2
#[test]
fn parenthesize_spread_element2() {
    let f = NodeFactory::new();
    let file = new_source_file(
        &f,
        f.new_node_list(&[f.new_expression_statement(f.new_call_expression(
            f.new_identifier("a"),
            nil(), /*questionDotToken*/
            nil(), /*typeArguments*/
            f.new_node_list(&[f.new_spread_element(
                // will be parenthesized on emit:
                f.new_binary_expression(
                    nil(), /*modifiers*/
                    f.new_identifier("b"),
                    nil(), /*typeNode*/
                    f.new_token(SyntaxKind::CommaToken),
                    f.new_identifier("c"),
                ),
            )]),
            NodeFlags::NONE,
        ))]),
        f.new_token(SyntaxKind::EndOfFile),
    );

    mark_synthetic_recursive(file);
    must(check_emit(None, file, "a(...(b, c));"));
}

// Go: printer/printer_test.go:1692 TestParenthesizeSpreadElement3
#[test]
fn parenthesize_spread_element3() {
    let f = NodeFactory::new();
    let file = new_source_file(
        &f,
        f.new_node_list(&[f.new_expression_statement(f.new_new_expression(
            f.new_identifier("a"),
            nil(), /*typeArguments*/
            f.new_node_list(&[f.new_spread_element(
                // will be parenthesized on emit:
                f.new_binary_expression(
                    nil(), /*modifiers*/
                    f.new_identifier("b"),
                    nil(), /*typeNode*/
                    f.new_token(SyntaxKind::CommaToken),
                    f.new_identifier("c"),
                ),
            )]),
        ))]),
        f.new_token(SyntaxKind::EndOfFile),
    );

    mark_synthetic_recursive(file);
    must(check_emit(None, file, "new a(...(b, c));"));
}

// Go: printer/printer_test.go:1725 TestParenthesizeExpressionWithTypeArguments
#[test]
fn parenthesize_expression_with_type_arguments() {
    let f = NodeFactory::new();
    let file = new_source_file(
        &f,
        f.new_node_list(&[
            f.new_expression_statement(f.new_expression_with_type_arguments(
                // will be parenthesized on emit:
                f.new_binary_expression(
                    nil(), /*modifiers*/
                    f.new_identifier("a"),
                    nil(), /*typeNode*/
                    f.new_token(SyntaxKind::CommaToken),
                    f.new_identifier("b"),
                ),
                f.new_node_list(&[f.new_type_reference_node(f.new_identifier("c"), nil())]),
            )),
        ]),
        f.new_token(SyntaxKind::EndOfFile),
    );

    mark_synthetic_recursive(file);
    must(check_emit(None, file, "(a, b)<c>;"));
}

// Go: printer/printer_test.go:1758 TestParenthesizeAsExpression
#[test]
fn parenthesize_as_expression() {
    let f = NodeFactory::new();
    let file = new_source_file(
        &f,
        f.new_node_list(&[f.new_expression_statement(f.new_as_expression(
            // will be parenthesized on emit:
            f.new_binary_expression(
                nil(), /*modifiers*/
                f.new_identifier("a"),
                nil(), /*typeNode*/
                f.new_token(SyntaxKind::CommaToken),
                f.new_identifier("b"),
            ),
            f.new_type_reference_node(f.new_identifier("c"), nil()),
        ))]),
        f.new_token(SyntaxKind::EndOfFile),
    );

    mark_synthetic_recursive(file);
    must(check_emit(None, file, "(a, b) as c;"));
}

// Go: printer/printer_test.go:1787 TestParenthesizeSatisfiesExpression
#[test]
fn parenthesize_satisfies_expression() {
    let f = NodeFactory::new();
    let file = new_source_file(
        &f,
        f.new_node_list(&[f.new_expression_statement(f.new_satisfies_expression(
            // will be parenthesized on emit:
            f.new_binary_expression(
                nil(), /*modifiers*/
                f.new_identifier("a"),
                nil(), /*typeNode*/
                f.new_token(SyntaxKind::CommaToken),
                f.new_identifier("b"),
            ),
            f.new_type_reference_node(f.new_identifier("c"), nil()),
        ))]),
        f.new_token(SyntaxKind::EndOfFile),
    );

    mark_synthetic_recursive(file);
    must(check_emit(None, file, "(a, b) satisfies c;"));
}

// Go: printer/printer_test.go:1816 TestParenthesizeNonNullExpression
#[test]
fn parenthesize_non_null_expression() {
    let f = NodeFactory::new();
    let file = new_source_file(
        &f,
        f.new_node_list(&[f.new_expression_statement(f.new_non_null_expression(
            // will be parenthesized on emit:
            f.new_binary_expression(
                nil(), /*modifiers*/
                f.new_identifier("a"),
                nil(), /*typeNode*/
                f.new_token(SyntaxKind::CommaToken),
                f.new_identifier("b"),
            ),
            NodeFlags::NONE,
        ))]),
        f.new_token(SyntaxKind::EndOfFile),
    );

    mark_synthetic_recursive(file);
    must(check_emit(None, file, "(a, b)!;"));
}

// Go: printer/printer_test.go:1842 TestParenthesizeExpressionStatement1
#[test]
fn parenthesize_expression_statement1() {
    let f = NodeFactory::new();
    let file = new_source_file(
        &f,
        f.new_node_list(&[f.new_expression_statement(
            f.new_object_literal_expression(f.new_node_list(&[]), false /*multiLine*/),
        )]),
        f.new_token(SyntaxKind::EndOfFile),
    );

    mark_synthetic_recursive(file);
    must(check_emit(None, file, "({});"));
}

// Go: printer/printer_test.go:1863 TestParenthesizeExpressionStatement2
#[test]
fn parenthesize_expression_statement2() {
    let f = NodeFactory::new();
    let file = new_source_file(
        &f,
        f.new_node_list(&[f.new_expression_statement(f.new_function_expression(
            nil(), /*modifiers*/
            nil(), /*asteriskToken*/
            nil(), /*name*/
            nil(), /*typeParameters*/
            f.new_node_list(&[]),
            nil(), /*returnType*/
            nil(), /*fullSignature*/
            f.new_block(f.new_node_list(&[]), false /*multiLine*/),
        ))]),
        f.new_token(SyntaxKind::EndOfFile),
    );

    mark_synthetic_recursive(file);
    must(check_emit(None, file, "(function () { });"));
}

// Go: printer/printer_test.go:1893 TestParenthesizeExpressionStatement3
#[test]
fn parenthesize_expression_statement3() {
    let f = NodeFactory::new();
    let file = new_source_file(
        &f,
        f.new_node_list(&[f.new_expression_statement(f.new_class_expression(
            nil(), /*modifiers*/
            nil(), /*name*/
            nil(), /*typeParameters*/
            nil(), /*heritageClauses*/
            f.new_node_list(&[]),
        ))]),
        f.new_token(SyntaxKind::EndOfFile),
    );

    mark_synthetic_recursive(file);
    must(check_emit(None, file, "class {\n};"));
}

// Go: printer/printer_test.go:1917 TestParenthesizeExpressionDefault1
#[test]
fn parenthesize_expression_default1() {
    let f = NodeFactory::new();
    let file = new_source_file(
        &f,
        f.new_node_list(&[f.new_export_assignment(
            nil(), /*modifiers*/
            false, /*isExportEquals*/
            nil(), /*typeNode*/
            // will be parenthesized on emit:
            f.new_class_expression(
                nil(), /*modifiers*/
                nil(), /*name*/
                nil(), /*typeParameters*/
                nil(), /*heritageClauses*/
                f.new_node_list(&[]),
            ),
        )]),
        f.new_token(SyntaxKind::EndOfFile),
    );

    mark_synthetic_recursive(file);
    must(check_emit(None, file, "export default (class {\n});"));
}

// Go: printer/printer_test.go:1945 TestParenthesizeExpressionDefault2
#[test]
fn parenthesize_expression_default2() {
    let f = NodeFactory::new();
    let file = new_source_file(
        &f,
        f.new_node_list(&[f.new_export_assignment(
            nil(), /*modifiers*/
            false, /*isExportEquals*/
            nil(), /*typeNode*/
            // will be parenthesized on emit:
            f.new_function_expression(
                nil(), /*modifiers*/
                nil(), /*asteriskToken*/
                nil(), /*name*/
                nil(), /*typeParameters*/
                f.new_node_list(&[]),
                nil(), /*returnType*/
                nil(), /*fullSignature*/
                f.new_block(f.new_node_list(&[]), false /*multiLine*/),
            ),
        )]),
        f.new_token(SyntaxKind::EndOfFile),
    );

    mark_synthetic_recursive(file);
    must(check_emit(None, file, "export default (function () { });"));
}

// Go: printer/printer_test.go:1981 TestParenthesizeExpressionDefault3
#[test]
fn parenthesize_expression_default3() {
    let f = NodeFactory::new();
    let file = new_source_file(
        &f,
        f.new_node_list(&[f.new_export_assignment(
            nil(), /*modifiers*/
            false, /*isExportEquals*/
            nil(), /*typeNode*/
            // will be parenthesized on emit:
            f.new_binary_expression(
                nil(), /*modifiers*/
                f.new_identifier("a"),
                nil(), /*typeNode*/
                f.new_token(SyntaxKind::CommaToken),
                f.new_identifier("b"),
            ),
        )]),
        f.new_token(SyntaxKind::EndOfFile),
    );

    mark_synthetic_recursive(file);
    must(check_emit(None, file, "export default (a, b);"));
}

// Go: printer/printer_test.go:2007 TestParenthesizeArrayType
#[test]
fn parenthesize_array_type() {
    let f = NodeFactory::new();
    let file = new_source_file(
        &f,
        f.new_node_list(&[f.new_type_alias_declaration(
            nil(),                 /*modifiers*/
            f.new_identifier("_"), /*name*/
            nil(),                 /*typeParameters*/
            f.new_array_type_node(
                // will be parenthesized on emit:
                f.new_union_type_node(f.new_node_list(&[
                    f.new_type_reference_node(f.new_identifier("a"), nil() /*typeArguments*/),
                    f.new_type_reference_node(f.new_identifier("b"), nil() /*typeArguments*/),
                ])),
            ),
        )]),
        f.new_token(SyntaxKind::EndOfFile),
    );

    mark_synthetic_recursive(file);
    must(check_emit(None, file, "type _ = (a | b)[];"));
}

// Go: printer/printer_test.go:2036 TestParenthesizeOptionalType
#[test]
fn parenthesize_optional_type() {
    let f = NodeFactory::new();
    let file = new_source_file(
        &f,
        f.new_node_list(&[f.new_type_alias_declaration(
            nil(),                 /*modifiers*/
            f.new_identifier("_"), /*name*/
            nil(),                 /*typeParameters*/
            f.new_tuple_type_node(f.new_node_list(&[f.new_optional_type_node(
                // will be parenthesized on emit:
                f.new_union_type_node(f.new_node_list(&[
                    f.new_type_reference_node(f.new_identifier("a"), nil() /*typeArguments*/),
                    f.new_type_reference_node(f.new_identifier("b"), nil() /*typeArguments*/),
                ])),
            )])),
        )]),
        f.new_token(SyntaxKind::EndOfFile),
    );

    mark_synthetic_recursive(file);
    must(check_emit(None, file, "type _ = [\n    (a | b)?\n];"));
}

// Go: printer/printer_test.go:2071 TestParenthesizeUnionType1
#[test]
fn parenthesize_union_type1() {
    let f = NodeFactory::new();
    let file = new_source_file(
        &f,
        f.new_node_list(&[f.new_type_alias_declaration(
            nil(),                 /*modifiers*/
            f.new_identifier("_"), /*name*/
            nil(),                 /*typeParameters*/
            f.new_union_type_node(f.new_node_list(&[
                f.new_type_reference_node(f.new_identifier("a"), nil() /*typeArguments*/),
                // will be parenthesized on emit:
                f.new_function_type_node(
                    nil(), /*typeParameters*/
                    f.new_node_list(&[]),
                    f.new_type_reference_node(f.new_identifier("b"), nil() /*typeArguments*/),
                ),
            ])),
        )]),
        f.new_token(SyntaxKind::EndOfFile),
    );

    mark_synthetic_recursive(file);
    must(check_emit(None, file, "type _ = a | (() => b);"));
}

// Go: printer/printer_test.go:2104 TestParenthesizeUnionType2
#[test]
fn parenthesize_union_type2() {
    let f = NodeFactory::new();
    let file = new_source_file(
        &f,
        f.new_node_list(&[f.new_type_alias_declaration(
            nil(),                 /*modifiers*/
            f.new_identifier("_"), /*name*/
            nil(),                 /*typeParameters*/
            f.new_union_type_node(f.new_node_list(&[
                // will be parenthesized on emit:
                f.new_infer_type_node(f.new_type_parameter_declaration(
                    nil(),
                    f.new_identifier("a"),
                    f.new_type_reference_node(f.new_identifier("b"), nil() /*typeArguments*/),
                    nil(), /*expression*/
                    nil(), /*defaultType*/
                )),
                f.new_type_reference_node(f.new_identifier("c"), nil() /*typeArguments*/),
            ])),
        )]),
        f.new_token(SyntaxKind::EndOfFile),
    );

    mark_synthetic_recursive(file);
    must(check_emit(None, file, "type _ = (infer a extends b) | c;"));
}

// Go: printer/printer_test.go:2139 TestParenthesizeIntersectionType
#[test]
fn parenthesize_intersection_type() {
    let f = NodeFactory::new();
    let file = new_source_file(
        &f,
        f.new_node_list(&[f.new_type_alias_declaration(
            nil(),                 /*modifiers*/
            f.new_identifier("_"), /*name*/
            nil(),                 /*typeParameters*/
            f.new_intersection_type_node(f.new_node_list(&[
                f.new_type_reference_node(f.new_identifier("a"), nil() /*typeArguments*/),
                // will be parenthesized on emit:
                f.new_union_type_node(f.new_node_list(&[
                    f.new_type_reference_node(f.new_identifier("b"), nil() /*typeArguments*/),
                    f.new_type_reference_node(f.new_identifier("c"), nil() /*typeArguments*/),
                ])),
            ])),
        )]),
        f.new_token(SyntaxKind::EndOfFile),
    );

    mark_synthetic_recursive(file);
    must(check_emit(None, file, "type _ = a & (b | c);"));
}

// Go: printer/printer_test.go:2173 TestParenthesizeReadonlyTypeOperator1
#[test]
fn parenthesize_readonly_type_operator1() {
    let f = NodeFactory::new();
    let file = new_source_file(
        &f,
        f.new_node_list(&[f.new_type_alias_declaration(
            nil(),                 /*modifiers*/
            f.new_identifier("_"), /*name*/
            nil(),                 /*typeParameters*/
            f.new_type_operator_node(
                SyntaxKind::ReadonlyKeyword,
                // will be parenthesized on emit:
                f.new_union_type_node(f.new_node_list(&[
                    f.new_type_reference_node(f.new_identifier("a"), nil() /*typeArguments*/),
                    f.new_type_reference_node(f.new_identifier("b"), nil() /*typeArguments*/),
                ])),
            ),
        )]),
        f.new_token(SyntaxKind::EndOfFile),
    );

    mark_synthetic_recursive(file);
    must(check_emit(None, file, "type _ = readonly (a | b);"));
}

// Go: printer/printer_test.go:2203 TestParenthesizeReadonlyTypeOperator2
#[test]
fn parenthesize_readonly_type_operator2() {
    let f = NodeFactory::new();
    let file = new_source_file(
        &f,
        f.new_node_list(&[f.new_type_alias_declaration(
            nil(),                 /*modifiers*/
            f.new_identifier("_"), /*name*/
            nil(),                 /*typeParameters*/
            f.new_type_operator_node(
                SyntaxKind::ReadonlyKeyword,
                // will be parenthesized on emit:
                f.new_type_operator_node(
                    SyntaxKind::KeyOfKeyword,
                    f.new_type_reference_node(f.new_identifier("a"), nil() /*typeArguments*/),
                ),
            ),
        )]),
        f.new_token(SyntaxKind::EndOfFile),
    );

    mark_synthetic_recursive(file);
    must(check_emit(None, file, "type _ = readonly (keyof a);"));
}

// Go: printer/printer_test.go:2229 TestParenthesizeKeyofTypeOperator
#[test]
fn parenthesize_keyof_type_operator() {
    let f = NodeFactory::new();
    let file = new_source_file(
        &f,
        f.new_node_list(&[f.new_type_alias_declaration(
            nil(),                 /*modifiers*/
            f.new_identifier("_"), /*name*/
            nil(),                 /*typeParameters*/
            f.new_type_operator_node(
                SyntaxKind::KeyOfKeyword,
                // will be parenthesized on emit:
                f.new_union_type_node(f.new_node_list(&[
                    f.new_type_reference_node(f.new_identifier("a"), nil() /*typeArguments*/),
                    f.new_type_reference_node(f.new_identifier("b"), nil() /*typeArguments*/),
                ])),
            ),
        )]),
        f.new_token(SyntaxKind::EndOfFile),
    );

    mark_synthetic_recursive(file);
    must(check_emit(None, file, "type _ = keyof (a | b);"));
}

// Go: printer/printer_test.go:2259 TestParenthesizeIndexedAccessType
#[test]
fn parenthesize_indexed_access_type() {
    let f = NodeFactory::new();
    let file = new_source_file(
        &f,
        f.new_node_list(&[f.new_type_alias_declaration(
            nil(),                 /*modifiers*/
            f.new_identifier("_"), /*name*/
            nil(),                 /*typeParameters*/
            f.new_indexed_access_type_node(
                // will be parenthesized on emit:
                f.new_union_type_node(f.new_node_list(&[
                    f.new_type_reference_node(f.new_identifier("a"), nil() /*typeArguments*/),
                    f.new_type_reference_node(f.new_identifier("b"), nil() /*typeArguments*/),
                ])),
                f.new_type_reference_node(f.new_identifier("c"), nil() /*typeArguments*/),
            ),
        )]),
        f.new_token(SyntaxKind::EndOfFile),
    );

    mark_synthetic_recursive(file);
    must(check_emit(None, file, "type _ = (a | b)[c];"));
}

// Go: printer/printer_test.go:2289 TestParenthesizeConditionalType1
#[test]
fn parenthesize_conditional_type1() {
    let f = NodeFactory::new();
    let file = new_source_file(
        &f,
        f.new_node_list(&[f.new_type_alias_declaration(
            nil(),                 /*modifiers*/
            f.new_identifier("_"), /*name*/
            nil(),                 /*typeParameters*/
            f.new_conditional_type_node(
                // will be parenthesized on emit:
                f.new_function_type_node(
                    nil(), /*typeParameters*/
                    f.new_node_list(&[]),
                    f.new_type_reference_node(f.new_identifier("a"), nil() /*typeArguments*/),
                ),
                f.new_type_reference_node(f.new_identifier("b"), nil() /*typeArguments*/),
                f.new_type_reference_node(f.new_identifier("c"), nil() /*typeArguments*/),
                f.new_type_reference_node(f.new_identifier("d"), nil() /*typeArguments*/),
            ),
        )]),
        f.new_token(SyntaxKind::EndOfFile),
    );

    mark_synthetic_recursive(file);
    must(check_emit(
        None,
        file,
        "type _ = (() => a) extends b ? c : d;",
    ));
}

// Go: printer/printer_test.go:2320 TestParenthesizeConditionalType2
#[test]
fn parenthesize_conditional_type2() {
    let f = NodeFactory::new();
    let file = new_source_file(
        &f,
        f.new_node_list(&[f.new_type_alias_declaration(
            nil(),                 /*modifiers*/
            f.new_identifier("_"), /*name*/
            nil(),                 /*typeParameters*/
            f.new_conditional_type_node(
                f.new_type_reference_node(f.new_identifier("a"), nil() /*typeArguments*/),
                // will be parenthesized on emit:
                f.new_conditional_type_node(
                    f.new_type_reference_node(f.new_identifier("b"), nil() /*typeArguments*/),
                    f.new_type_reference_node(f.new_identifier("c"), nil() /*typeArguments*/),
                    f.new_type_reference_node(f.new_identifier("d"), nil() /*typeArguments*/),
                    f.new_type_reference_node(f.new_identifier("e"), nil() /*typeArguments*/),
                ),
                f.new_type_reference_node(f.new_identifier("f"), nil() /*typeArguments*/),
                f.new_type_reference_node(f.new_identifier("g"), nil() /*typeArguments*/),
            ),
        )]),
        f.new_token(SyntaxKind::EndOfFile),
    );

    mark_synthetic_recursive(file);
    must(check_emit(
        None,
        file,
        "type _ = a extends (b extends c ? d : e) ? f : g;",
    ));
}

// Go: printer/printer_test.go:2350 TestParenthesizeConditionalType3
#[test]
fn parenthesize_conditional_type3() {
    let f = NodeFactory::new();
    let file = new_source_file(
        &f,
        f.new_node_list(&[f.new_type_alias_declaration(
            nil(),                 /*modifiers*/
            f.new_identifier("_"), /*name*/
            nil(),                 /*typeParameters*/
            f.new_conditional_type_node(
                f.new_type_reference_node(f.new_identifier("a"), nil() /*typeArguments*/),
                f.new_function_type_node(
                    nil(), /*typeParameters*/
                    f.new_node_list(&[]),
                    // will be parenthesized on emit:
                    f.new_infer_type_node(f.new_type_parameter_declaration(
                        nil(),
                        f.new_identifier("b"),
                        f.new_type_reference_node(
                            f.new_identifier("c"),
                            nil(), /*typeArguments*/
                        ),
                        nil(), /*expression*/
                        nil(), /*defaultType*/
                    )),
                ),
                f.new_type_reference_node(f.new_identifier("d"), nil() /*typeArguments*/),
                f.new_type_reference_node(f.new_identifier("e"), nil() /*typeArguments*/),
            ),
        )]),
        f.new_token(SyntaxKind::EndOfFile),
    );

    mark_synthetic_recursive(file);
    must(check_emit(
        None,
        file,
        "type _ = a extends () => (infer b extends c) ? d : e;",
    ));
}

// Go: printer/printer_test.go:2389 TestParenthesizeConditionalType4
#[test]
fn parenthesize_conditional_type4() {
    let f = NodeFactory::new();
    let file = new_source_file(
        &f,
        f.new_node_list(&[f.new_type_alias_declaration(
            nil(),                 /*modifiers*/
            f.new_identifier("_"), /*name*/
            nil(),                 /*typeParameters*/
            f.new_conditional_type_node(
                f.new_type_reference_node(f.new_identifier("a"), nil() /*typeArguments*/),
                f.new_function_type_node(
                    nil(), /*typeParameters*/
                    f.new_node_list(&[]),
                    // will be parenthesized on emit:
                    f.new_union_type_node(f.new_node_list(&[
                        f.new_infer_type_node(f.new_type_parameter_declaration(
                            nil(),
                            f.new_identifier("b"),
                            f.new_type_reference_node(
                                f.new_identifier("c"),
                                nil(), /*typeArguments*/
                            ),
                            nil(), /*expression*/
                            nil(), /*defaultType*/
                        )),
                        f.new_type_reference_node(
                            f.new_identifier("d"),
                            nil(), /*typeArguments*/
                        ),
                    ])),
                ),
                f.new_type_reference_node(f.new_identifier("e"), nil() /*typeArguments*/),
                f.new_type_reference_node(f.new_identifier("f"), nil() /*typeArguments*/),
            ),
        )]),
        f.new_token(SyntaxKind::EndOfFile),
    );

    mark_synthetic_recursive(file);
    must(check_emit(
        None,
        file,
        "type _ = a extends () => (infer b extends c) | d ? e : f;",
    ));
}

// Go: printer/printer_test.go:1296 isBinaryOperator
fn is_binary_operator(token: SyntaxKind) -> bool {
    matches!(
        token,
        SyntaxKind::CommaToken
            | SyntaxKind::LessThanToken
            | SyntaxKind::GreaterThanToken
            | SyntaxKind::LessThanEqualsToken
            | SyntaxKind::GreaterThanEqualsToken
            | SyntaxKind::EqualsEqualsToken
            | SyntaxKind::EqualsEqualsEqualsToken
            | SyntaxKind::ExclamationEqualsToken
            | SyntaxKind::ExclamationEqualsEqualsToken
            | SyntaxKind::PlusToken
            | SyntaxKind::MinusToken
            | SyntaxKind::AsteriskToken
            | SyntaxKind::AsteriskAsteriskToken
            | SyntaxKind::SlashToken
            | SyntaxKind::PercentToken
            | SyntaxKind::LessThanLessThanToken
            | SyntaxKind::GreaterThanGreaterThanToken
            | SyntaxKind::GreaterThanGreaterThanGreaterThanToken
            | SyntaxKind::AmpersandToken
            | SyntaxKind::BarToken
            | SyntaxKind::CaretToken
            | SyntaxKind::AmpersandAmpersandToken
            | SyntaxKind::BarBarToken
            | SyntaxKind::QuestionQuestionToken
            | SyntaxKind::EqualsToken
            | SyntaxKind::PlusEqualsToken
            | SyntaxKind::MinusEqualsToken
            | SyntaxKind::AsteriskEqualsToken
            | SyntaxKind::AsteriskAsteriskEqualsToken
            | SyntaxKind::SlashEqualsToken
            | SyntaxKind::PercentEqualsToken
            | SyntaxKind::LessThanLessThanEqualsToken
            | SyntaxKind::GreaterThanGreaterThanEqualsToken
            | SyntaxKind::GreaterThanGreaterThanGreaterThanEqualsToken
            | SyntaxKind::AmpersandEqualsToken
            | SyntaxKind::BarEqualsToken
            | SyntaxKind::BarBarEqualsToken
            | SyntaxKind::AmpersandAmpersandEqualsToken
            | SyntaxKind::QuestionQuestionEqualsToken
            | SyntaxKind::CaretEqualsToken
            | SyntaxKind::InKeyword
            | SyntaxKind::InstanceOfKeyword
    )
}

// Go: printer/printer_test.go:1345 makeSide
fn make_side(label: &str, kind: SyntaxKind, factory: &NodeFactory) -> Node {
    if kind == SyntaxKind::Identifier || kind == SyntaxKind::Unknown {
        factory.new_identifier(label)
    } else if kind == SyntaxKind::ArrowFunction {
        factory.new_arrow_function(
            nil(), /*modifiers*/
            nil(), /*typeParameters*/
            factory.new_node_list(&[]),
            nil(), /*returnType*/
            nil(), /*fullSignature*/
            factory.new_token(SyntaxKind::EqualsGreaterThanToken),
            factory.new_block(factory.new_node_list(&[]), false /*multiLine*/),
        )
    } else if is_binary_operator(kind) {
        factory.new_binary_expression(
            nil(), /*modifiers*/
            factory.new_identifier(format!("{label}l")),
            nil(), /*typeNode*/
            factory.new_token(kind),
            factory.new_identifier(format!("{label}r")),
        )
    } else {
        panic!("unsupported kind")
    }
}

// Go: printer/printer_test.go:1372 TestParenthesizeBinary
#[test]
fn parenthesize_binary() {
    use SyntaxKind as K;
    // PORT: Go leaves `left` and `right` zero (ast.KindUnknown) when unset.
    // (left, operator, right, output)
    #[rustfmt::skip]
    let data: &[(K, K, K, &str)] = &[
        (K::Unknown, K::CommaToken, K::Unknown, "l, r"),
        (K::PlusToken, K::CommaToken, K::Unknown, "ll + lr, r"),
        (K::PlusToken, K::AsteriskToken, K::Unknown, "(ll + lr) * r"),
        (K::Unknown, K::AsteriskToken, K::PlusToken, "l * (rl + rr)"),
        (K::AsteriskToken, K::PlusToken, K::Unknown, "ll * lr + r"),
        (K::Unknown, K::PlusToken, K::AsteriskToken, "l + rl * rr"),
        (K::AsteriskToken, K::SlashToken, K::Unknown, "ll * lr / r"),
        (K::AsteriskAsteriskToken, K::SlashToken, K::Unknown, "ll ** lr / r"),
        (K::AsteriskToken, K::AsteriskAsteriskToken, K::Unknown, "(ll * lr) ** r"),
        (K::AsteriskAsteriskToken, K::AsteriskAsteriskToken, K::Unknown, "(ll ** lr) ** r"),
        (K::Unknown, K::AsteriskToken, K::AsteriskToken, "l * rl * rr"),
        (K::Unknown, K::BarToken, K::BarToken, "l | rl | rr"),
        (K::Unknown, K::AmpersandToken, K::AmpersandToken, "l & rl & rr"),
        (K::Unknown, K::CaretToken, K::CaretToken, "l ^ rl ^ rr"),
        (K::Unknown, K::AmpersandAmpersandToken, K::ArrowFunction, "l && (() => { })"),
    ];
    let mut t = Subtests::new("TestParenthesizeBinary");
    for &(left, operator, right, output) in data {
        t.run(output, || {
            let factory = NodeFactory::new();
            let file = new_source_file(
                &factory,
                factory.new_node_list(&[factory.new_expression_statement(
                    factory.new_binary_expression(
                        nil(), /*modifiers*/
                        make_side("l", left, &factory),
                        nil(), /*typeNode*/
                        factory.new_token(operator),
                        make_side("r", right, &factory),
                    ),
                )]),
                factory.new_token(SyntaxKind::EndOfFile),
            );

            mark_synthetic_recursive(file);
            check_emit(None, file, &format!("{output};"))
        });
    }
    t.finish();
}

// Go: printer/printer_test.go:2526 TestParenthesizeBinaryExpressionMixingNullishCoalescing
#[test]
fn parenthesize_binary_expression_mixing_nullish_coalescing() {
    use SyntaxKind as K;
    // (title, innerOp, outerOp, side, output)
    #[rustfmt::skip]
    let tests: &[(&str, K, K, &str, &str)] = &[
        // inner ?? on left side of || or &&
        ("BarBarWithLeftQuestionQuestion", K::QuestionQuestionToken, K::BarBarToken, "left", "(a ?? b) || c;"),
        ("AmpersandAmpersandWithLeftQuestionQuestion", K::QuestionQuestionToken, K::AmpersandAmpersandToken, "left", "(a ?? b) && c;"),
        // inner ?? on right side of || or &&
        ("BarBarWithRightQuestionQuestion", K::QuestionQuestionToken, K::BarBarToken, "right", "a || (b ?? c);"),
        ("AmpersandAmpersandWithRightQuestionQuestion", K::QuestionQuestionToken, K::AmpersandAmpersandToken, "right", "a && (b ?? c);"),
        // inner || or && on left side of ??
        ("QuestionQuestionWithLeftBarBar", K::BarBarToken, K::QuestionQuestionToken, "left", "(a || b) ?? c;"),
        ("QuestionQuestionWithLeftAmpersandAmpersand", K::AmpersandAmpersandToken, K::QuestionQuestionToken, "left", "(a && b) ?? c;"),
        // inner || or && on right side of ??
        ("QuestionQuestionWithRightBarBar", K::BarBarToken, K::QuestionQuestionToken, "right", "a ?? (b || c);"),
        ("QuestionQuestionWithRightAmpersandAmpersand", K::AmpersandAmpersandToken, K::QuestionQuestionToken, "right", "a ?? (b && c);"),
    ];
    let mut t = Subtests::new("TestParenthesizeBinaryExpressionMixingNullishCoalescing");
    for &(title, inner_op, outer_op, side, output) in tests {
        t.run(title, || {
            let factory = NodeFactory::new();
            let outer_expr = if side == "left" {
                let inner_expr = factory.new_binary_expression(
                    nil(), /*modifiers*/
                    factory.new_identifier("a"),
                    nil(), /*typeNode*/
                    factory.new_token(inner_op),
                    factory.new_identifier("b"),
                );
                factory.new_binary_expression(
                    nil(),      /*modifiers*/
                    inner_expr, /*left: (a innerOp b)*/
                    nil(),      /*typeNode*/
                    factory.new_token(outer_op),
                    factory.new_identifier("c"),
                )
            } else {
                // PORT: Go makes `innerExpr` with `a` and `b`, then sets its
                // Left and Right to new `b` and `c` identifiers ("adjust
                // identifiers for right side"). A synthetic node's fields
                // are fixed when it is made here, so it is made with `b`
                // and `c`.
                let inner_expr = factory.new_binary_expression(
                    nil(), /*modifiers*/
                    factory.new_identifier("b"),
                    nil(), /*typeNode*/
                    factory.new_token(inner_op),
                    factory.new_identifier("c"),
                );
                factory.new_binary_expression(
                    nil(), /*modifiers*/
                    factory.new_identifier("a"),
                    nil(), /*typeNode*/
                    factory.new_token(outer_op),
                    inner_expr, /*right: (b innerOp c)*/
                )
            };
            let file = new_source_file(
                &factory,
                factory.new_node_list(&[factory.new_expression_statement(outer_expr)]),
                factory.new_token(SyntaxKind::EndOfFile),
            );

            mark_synthetic_recursive(file);
            check_emit(None, file, output)
        });
    }
    t.finish();
}
