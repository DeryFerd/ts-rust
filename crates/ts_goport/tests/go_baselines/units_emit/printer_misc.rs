//! Ports of internal/printer/utilities_test.go and of the printer_test.go
//! tests that are not TestEmit or TestParenthesize*: TestNameGeneration,
//! TestNoTrailingCommaAfterTransform, TestTrailingCommaAfterTransform,
//! TestPartiallyEmittedExpression and TestOmitTrailingSemicolon.
//!
//! Not ported (blocked, see bugs/S3.md): TestEscapeNonAsciiString and
//! TestEscapeJsxAttributeString (`escape_non_ascii_string` and
//! `escape_jsx_attribute_string` are `pub(crate)`).

use super::childprog::in_child;
use super::emittestutil::check_emit;
use super::parsetestutil::{mark_synthetic_recursive, parse_type_script_published};
use super::{Subtests, assert_equal, must, nil};
use ts_goport::prelude::*;
use ts_goport::printer::CommentRange;
use ts_goport::transformers::tstransforms::type_eraser::new_type_eraser_transformer;

/// Go TestEscapeString rows: (s, quoteChar, expected).
#[rustfmt::skip]
const ESCAPE_STRING: &[(&str, QuoteChar, &str)] = &[
    ("", QuoteChar::DOUBLE_QUOTE, ""),
    ("abc", QuoteChar::DOUBLE_QUOTE, "abc"),
    ("ab\"c", QuoteChar::DOUBLE_QUOTE, r#"ab\"c"#),
    ("ab\tc", QuoteChar::DOUBLE_QUOTE, r#"ab\tc"#),
    ("ab\nc", QuoteChar::DOUBLE_QUOTE, r#"ab\nc"#),
    ("ab'c", QuoteChar::DOUBLE_QUOTE, "ab'c"),
    ("ab'c", QuoteChar::SINGLE_QUOTE, r#"ab\'c"#),
    ("ab\"c", QuoteChar::SINGLE_QUOTE, r#"ab"c"#),
    ("ab`c", QuoteChar::BACKTICK, "ab\\`c"),
    ("\u{001f}", QuoteChar::BACKTICK, "\\u001F"),
];

// Go: printer/utilities_test.go:12 TestEscapeString
#[test]
fn test_escape_string() {
    let mut t = Subtests::new("TestEscapeString");
    for (i, &(s, quote_char, expected)) in ESCAPE_STRING.iter().enumerate() {
        t.run(
            &format!("[{i}] escapeString({s:?}, {quote_char:?})"),
            || {
                let actual = escape_string(s, quote_char);
                assert_equal(actual.as_str(), expected, "EscapeString")
            },
        );
    }
    t.finish();
}

/// Go TestIsRecognizedTripleSlashComment rows: (s, commentRange.Kind,
/// expected). `None` is a zero `commentRange`.
#[rustfmt::skip]
const TRIPLE_SLASH: &[(&str, Option<SyntaxKind>, bool)] = &[
    ("", Some(SyntaxKind::MultiLineCommentTrivia), false),
    ("", Some(SyntaxKind::SingleLineCommentTrivia), false),
    ("/a", None, false),
    ("//", None, false),
    ("//a", None, false),
    ("///", None, false),
    ("///a", None, false),
    ("///<reference path=\"foo\" />", None, true),
    ("///<reference types=\"foo\" />", None, true),
    ("///<reference lib=\"foo\" />", None, true),
    ("///<reference no-default-lib=\"foo\" />", None, true),
    ("///<amd-dependency path=\"foo\" />", None, true),
    ("///<amd-module />", None, true),
    ("/// <reference path=\"foo\" />", None, true),
    ("/// <reference types=\"foo\" />", None, true),
    ("/// <reference lib=\"foo\" />", None, true),
    ("/// <reference no-default-lib=\"foo\" />", None, true),
    ("/// <amd-dependency path=\"foo\" />", None, true),
    ("/// <amd-module />", None, true),
    ("/// <reference path=\"foo\"/>", None, true),
    ("/// <reference types=\"foo\"/>", None, true),
    ("/// <reference lib=\"foo\"/>", None, true),
    ("/// <reference no-default-lib=\"foo\"/>", None, true),
    ("/// <amd-dependency path=\"foo\"/>", None, true),
    ("/// <amd-module/>", None, true),
    ("/// <reference path='foo' />", None, true),
    ("/// <reference types='foo' />", None, true),
    ("/// <reference lib='foo' />", None, true),
    ("/// <reference no-default-lib='foo' />", None, true),
    ("/// <amd-dependency path='foo' />", None, true),
    ("/// <reference path=\"foo\" />  ", None, true),
    ("/// <reference types=\"foo\" />  ", None, true),
    ("/// <reference lib=\"foo\" />  ", None, true),
    ("/// <reference no-default-lib=\"foo\" />  ", None, true),
    ("/// <amd-dependency path=\"foo\" />  ", None, true),
    ("/// <amd-module />  ", None, true),
    ("/// <foo />", None, false),
    ("/// <reference />", None, false),
    ("/// <amd-dependency />", None, false),
];

// Go: printer/utilities_test.go:94 TestIsRecognizedTripleSlashComment
#[test]
fn test_is_recognized_triple_slash_comment() {
    let mut t = Subtests::new("TestIsRecognizedTripleSlashComment");
    for (i, &(s, kind, expected)) in TRIPLE_SLASH.iter().enumerate() {
        t.run(&format!("[{i}] isRecognizedTripleSlashComment()"), || {
            let comment_range = match kind {
                Some(kind) => CommentRange {
                    text_range: TextRange::new(0, 0),
                    kind,
                    has_trailing_new_line: false,
                },
                None => CommentRange {
                    text_range: TextRange::new(0, s.len() as i32),
                    kind: SyntaxKind::SingleLineCommentTrivia,
                    has_trailing_new_line: false,
                },
            };
            let actual = is_recognized_triple_slash_comment(s, comment_range);
            assert_equal(actual, expected, "IsRecognizedTripleSlashComment")
        });
    }
    t.finish();
}

// Go: printer/printer_test.go:2433 TestNameGeneration
#[test]
fn test_name_generation() {
    let ec = new_emit_context();
    let f = ec.factory();
    let file = f.new_source_file(
        "/file.ts",
        "/file.ts",
        "",
        f.new_node_list(&[
            f.new_variable_statement(
                nil(),
                f.new_variable_declaration_list(
                    f.new_node_list(&[f.new_variable_declaration(
                        f.new_temp_variable(),
                        nil(),
                        nil(),
                        nil(),
                    )]),
                    NodeFlags::NONE,
                ),
            ),
            f.new_function_declaration(
                nil(),
                nil(),
                f.new_identifier("f"),
                nil(),
                f.new_node_list(&[]),
                nil(),
                nil(),
                f.new_block(
                    f.new_node_list(&[f.new_variable_statement(
                        nil(),
                        f.new_variable_declaration_list(
                            f.new_node_list(&[f.new_variable_declaration(
                                f.new_temp_variable(),
                                nil(),
                                nil(),
                                nil(),
                            )]),
                            NodeFlags::NONE,
                        ),
                    )]),
                    true,
                ),
            ),
        ]),
        f.new_token(SyntaxKind::EndOfFile),
    );

    mark_synthetic_recursive(file);
    must(check_emit(
        Some(Rc::clone(&ec)),
        file,
        "var _a;\nfunction f() {\n    var _a;\n}",
    ));
}

/// The visitor of TestNoTrailingCommaAfterTransform and
/// TestTrailingCommaAfterTransform: it drops each `!` (NonNullExpression).
fn strip_non_null(emit_context: &Rc<EmitContext>, file: Node) -> Node {
    let mut visitor = emit_context.new_node_visitor(
        |node: Node, v: &mut ts_goport::ast::NodeVisitor<'_, ()>| match node.kind() {
            SyntaxKind::NonNullExpression => node.expression(),
            _ => node.visit_each_child(v),
        },
        (),
    );
    visitor.visit_source_file(file)
}

// Go: printer/printer_test.go:2466 TestNoTrailingCommaAfterTransform
// PORT: this test and the two below run in a child process, because the
// printer needs the parsed file published (see
// `parse_type_script_published`).
#[test]
fn test_no_trailing_comma_after_transform() {
    in_child(
        module_path!(),
        "test_no_trailing_comma_after_transform",
        || {
            let file = parse_type_script_published("[a!]", false /*jsx*/);
            let emit_context = new_emit_context();
            let file = strip_non_null(&emit_context, file);

            must(check_emit(Some(emit_context), file, "[a];"));
        },
    );
}

// Go: printer/printer_test.go:2487 TestTrailingCommaAfterTransform
#[test]
fn test_trailing_comma_after_transform() {
    in_child(
        module_path!(),
        "test_trailing_comma_after_transform",
        || {
            let file = parse_type_script_published("[a!,]", false /*jsx*/);
            let emit_context = new_emit_context();
            let file = strip_non_null(&emit_context, file);

            must(check_emit(Some(emit_context), file, "[a,];"));
        },
    );
}

// Go: printer/printer_test.go:2508 TestPartiallyEmittedExpression
#[test]
fn test_partially_emitted_expression() {
    in_child(
        module_path!(),
        "test_partially_emitted_expression",
        partially_emitted_expression,
    );
}

fn partially_emitted_expression() {
    let compiler_options: &'static CompilerOptions = Box::leak(Box::default());

    let file = parse_type_script_published(
        "return ((container.parent
    .left as PropertyAccessExpression)
    .expression as PropertyAccessExpression)
    .expression;",
        false, /*jsx*/
    );

    let emit_context = new_emit_context();
    let file = new_type_eraser_transformer(&super::tstransforms::transform_options(
        compiler_options,
        &emit_context,
    ))
    .expect("type eraser")
    .transform_source_file(file);
    must(check_emit(
        Some(emit_context),
        file,
        "return container.parent
    .left
    .expression
    .expression;",
    ));
}

// Go: printer/printer_test.go:2595 TestOmitTrailingSemicolon
// PORT: runs in a child process, because the printer needs the parsed
// files published (see `parse_type_script_published`).
#[test]
fn test_omit_trailing_semicolon() {
    in_child(
        module_path!(),
        "test_omit_trailing_semicolon",
        omit_trailing_semicolon,
    );
}

fn omit_trailing_semicolon() {
    let factory = NodeFactory::new_with_hooks(NodeFactoryHooks::default());
    let method_signature = factory.new_method_signature_declaration(
        nil(), /*modifiers*/
        factory.new_identifier("m"),
        nil(), /*postfixToken*/
        nil(), /*typeParameters*/
        factory.new_node_list(&[]),
        factory.new_keyword_type_node(SyntaxKind::VoidKeyword),
    );
    let file = parse_type_script_published("interface I {}", false /*jsx*/);

    let mut default_printer = new_printer(
        PrinterOptions {
            new_line: NewLineKind::LF,
            ..Default::default()
        },
        PrintHandlers::default(),
        None,
    );
    let got = default_printer.emit(method_signature, file);
    assert_eq!(got, "m(): void;", "default Emit()");

    let mut omit_printer = new_printer(
        PrinterOptions {
            new_line: NewLineKind::LF,
            omit_trailing_semicolon: true,
            ..Default::default()
        },
        PrintHandlers::default(),
        None,
    );
    let got = omit_printer.emit(method_signature, file);
    assert_eq!(got, "m(): void", "omit Emit()");

    let for_file = parse_type_script_published("for (;;) {}", false /*jsx*/);
    let text = omit_printer.emit_source_file_exported(for_file);
    let got = text.strip_suffix('\n').unwrap_or(&text);
    assert_eq!(got, "for (;;) { }", "omit EmitSourceFile(for)");
}
