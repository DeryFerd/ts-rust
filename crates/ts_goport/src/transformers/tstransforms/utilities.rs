//! Port of `transformers/tstransforms/utilities.go`.

use crate::prelude::*;
use crate::printer::factory::NodeFactory as PrinterNodeFactory;

// Go: transformers/tstransforms/utilities.go:9 constantExpression
// PORT: Go takes `any`; the values used are `string` and `jsnum.Number`,
// which are `LiteralValue::String` and `LiteralValue::Number`. Any other
// value is Go `nil`.
pub(crate) fn constant_expression(value: &LiteralValue, factory: &PrinterNodeFactory) -> Node {
    match value {
        LiteralValue::String(value) => factory.new_string_literal(value.clone(), TokenFlags::NONE),
        LiteralValue::Number(value) => constant_number_expression(*value, factory),
        _ => Node::NIL,
    }
}

/// The Go `jsnum.Number` case of `constantExpression` (it recurses on `-value`).
fn constant_number_expression(value: crate::jsnum::Number, factory: &PrinterNodeFactory) -> Node {
    if value.is_infinite() {
        if value.0 > 0.0 {
            return factory.new_identifier("Infinity");
        }
        return factory.new_prefix_unary_expression(
            SyntaxKind::MinusToken,
            factory.new_identifier("Infinity"),
        );
    }
    if value.is_nan() {
        return factory.new_identifier("NaN");
    }
    if value.0 < 0.0 {
        return factory.new_prefix_unary_expression(
            SyntaxKind::MinusToken,
            constant_number_expression(-value, factory),
        );
    }
    factory.new_numeric_literal(value.to_string(), TokenFlags::NONE)
}
