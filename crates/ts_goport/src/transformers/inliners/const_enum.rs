//! Port of `transformers/inliners/constenum.go`.

use crate::prelude::*;
use crate::transformers::transformer::{
    TransformOptions, Transformer, TransformerBox, TransformerVisit,
};
use crate::transformers::tstransforms::TxVisit;

// Go: transformers/inliners/constenum.go:15 ConstEnumInliningTransformer
pub struct ConstEnumInliningTransformer {
    emit_context: Rc<EmitContext>,
    compiler_options: &'static CompilerOptions,
    current_source_file: Node,
    emit_resolver: Rc<dyn EmitResolver>,
}

// Go: transformers/inliners/constenum.go:22 NewConstEnumInliningTransformer
// PORT: Go never returns nil here. The result is an `Option` so the
// constructor has the `TransformerFactory` shape.
pub fn new_const_enum_inlining_transformer(opt: &TransformOptions) -> Option<TransformerBox> {
    let compiler_options = opt.compiler_options;
    let emit_context = opt.context.clone();
    if compiler_options.get_isolated_modules() {
        crate::gostd::debug::fail("const enums are not inlined under isolated modules");
    }
    let tx = ConstEnumInliningTransformer {
        emit_context,
        compiler_options,
        current_source_file: Node::NIL,
        emit_resolver: opt.emit_resolver.clone(),
    };
    Some(Box::new(tx))
}

impl Transformer for ConstEnumInliningTransformer {
    fn emit_context(&self) -> &Rc<EmitContext> {
        &self.emit_context
    }

    fn transform_source_file(&mut self, file: Node) -> Node {
        self.visit_source_file_root(file)
    }
}

impl TransformerVisit for ConstEnumInliningTransformer {
    fn emit_context_rc(&self) -> Rc<EmitContext> {
        self.emit_context.clone()
    }

    // Go: transformers/inliners/constenum.go:32 ConstEnumInliningTransformer.visit
    fn visit(&mut self, node: Node) -> Node {
        match node.kind() {
            SyntaxKind::PropertyAccessExpression | SyntaxKind::ElementAccessExpression => {
                let ec = self.emit_context.clone();
                let f = ec.factory();
                let parse = ec.parse_node(node);
                if parse.is_nil() {
                    return self.visit_each_child(node);
                }
                let value = self.emit_resolver.get_constant_value(parse);
                if let Some(value) = value {
                    let replacement = match value {
                        LiteralValue::Number(v) => {
                            if v.is_infinite() {
                                if v.abs() == v {
                                    f.new_identifier("Infinity")
                                } else {
                                    f.new_prefix_unary_expression(
                                        SyntaxKind::MinusToken,
                                        f.new_identifier("Infinity"),
                                    )
                                }
                            } else if v.is_nan() {
                                f.new_identifier("NaN")
                            } else if v.abs() == v {
                                f.new_numeric_literal(v.to_string(), TokenFlags::NONE)
                            } else {
                                f.new_prefix_unary_expression(
                                    SyntaxKind::MinusToken,
                                    f.new_numeric_literal(v.abs().to_string(), TokenFlags::NONE),
                                )
                            }
                        }
                        LiteralValue::String(v) => f.new_string_literal(v, TokenFlags::NONE),
                        // technically not supported by strada, and issues a checker error, handled here for completeness
                        LiteralValue::PseudoBigInt(v) => {
                            if v == crate::jsnum::PseudoBigInt::default() {
                                f.new_big_int_literal("0", TokenFlags::NONE)
                            } else if !v.negative {
                                f.new_big_int_literal(v.base10_value, TokenFlags::NONE)
                            } else {
                                f.new_prefix_unary_expression(
                                    SyntaxKind::MinusToken,
                                    f.new_big_int_literal(v.base10_value, TokenFlags::NONE),
                                )
                            }
                        }
                        // PORT: Go leaves `replacement` nil for any other value.
                        LiteralValue::Bool(_) => Node::NIL,
                    };

                    if self.compiler_options.remove_comments.is_false_or_unknown() {
                        let original = ec.most_original(node);
                        if original.is_some() && !node_is_synthesized(original) {
                            let original_text = get_text_of_node(original);
                            let escaped_text = safe_multi_line_comment(&original_text);
                            ec.add_synthetic_trailing_comment(
                                replacement,
                                SyntaxKind::MultiLineCommentTrivia,
                                &escaped_text,
                                false,
                            );
                        }
                    }
                    return replacement;
                }
                self.visit_each_child(node)
            }
            _ => self.visit_each_child(node),
        }
    }
}

// Go: transformers/inliners/constenum.go:86 safeMultiLineComment
fn safe_multi_line_comment(text: &str) -> String {
    let mut b = String::with_capacity(text.len() + 2);
    b.push(' ');
    let mut text = text;
    loop {
        let Some(i) = text.find("*/") else {
            break;
        };
        b.push_str(&text[..i]);
        b.push_str("*_/");
        text = &text[i + 2..];
    }
    b.push_str(text);
    b.push(' ');
    b
}
