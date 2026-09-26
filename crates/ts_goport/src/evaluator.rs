//! Port of Go package `evaluator` (`internal/evaluator/evaluator.go`).
//! Constant evaluation of enum member initializers and template literal types.

use crate::prelude::*;
use ts_jsnum::{Number, PseudoBigInt};

// PORT: Go `evaluator.Result` is named `EvaluatorResult` here. A type named
// `Result` would be glob-exported through the prelude and shadow
// `std::result::Result` in every port file.
// PORT: Go `Value any` is `Option<LiteralValue>`. `None` is Go `nil`. The
// evaluator produces the same dynamic values as `LiteralType.value` (string,
// jsnum.Number, jsnum.PseudoBigInt, bool), and the checker stores these
// values in literal types, so both share `LiteralValue` from `checker/types.rs`.
// Go: evaluator/evaluator.go:11 Result
#[derive(Clone, Default)]
pub struct EvaluatorResult {
    pub value: Option<LiteralValue>,
    pub is_syntactically_string: bool,
    pub resolved_other_files: bool,
    pub has_external_references: bool,
}

// Go: evaluator/evaluator.go:18 NewResult
pub fn new_result(
    value: Option<LiteralValue>,
    is_syntactically_string: bool,
    resolved_other_files: bool,
    has_external_references: bool,
) -> EvaluatorResult {
    EvaluatorResult {
        value,
        is_syntactically_string,
        resolved_other_files,
        has_external_references,
    }
}

// PORT: Go `Evaluator func(expr, location) Result` is a stored closure. The
// only Go caller (the checker) passes `c.evaluateEntity`, so the closure gets
// the checker as its first argument. Call it as
// `let ev = self.evaluate.clone(); ev(self, expr, location)`.
// Go: evaluator/evaluator.go:22 Evaluator
pub type Evaluator = Rc<dyn Fn(&mut Checker, Node, Node) -> EvaluatorResult>;

// Go: evaluator/evaluator.go:24 NewEvaluator
pub fn new_evaluator(
    evaluate_entity: Evaluator,
    outer_expressions_to_skip: OuterExpressionKinds,
) -> Evaluator {
    // PORT: Go builds a self-referencing closure. Here the recursion goes
    // through `evaluate_expression`, which receives the same captured state.
    Rc::new(move |checker: &mut Checker, expr: Node, location: Node| {
        evaluate_expression(
            checker,
            &evaluate_entity,
            outer_expressions_to_skip,
            expr,
            location,
        )
    })
}

// PORT: body of the Go `evaluate` closure created in NewEvaluator.
// Go: evaluator/evaluator.go:26 NewEvaluator.evaluate
fn evaluate_expression(
    checker: &mut Checker,
    evaluate_entity: &Evaluator,
    outer_expressions_to_skip: OuterExpressionKinds,
    expr: Node,
    location: Node,
) -> EvaluatorResult {
    let mut is_syntactically_string = false;
    let mut resolved_other_files = false;
    let mut has_external_references = false;
    // It's unclear when/whether we should consider skipping other kinds of outer expressions.
    // Type assertions intentionally break evaluation when evaluating literal types, such as:
    //     type T = `one ${"two" as any} three`; // string
    // But it's less clear whether such an assertion should break enum member evaluation:
    //     enum E {
    //       A = "one" as any
    //     }
    // SatisfiesExpressions and non-null assertions seem to have even less reason to break
    // emitting enum members as literals. However, these expressions also break Babel's
    // evaluation (but not esbuild's), and the isolatedModules errors we give depend on
    // our evaluation results, so we're currently being conservative so as to issue errors
    // on code that might break Babel.
    let expr = skip_outer_expressions(
        expr,
        outer_expressions_to_skip | OuterExpressionKinds::OEK_PARENTHESES,
    );
    let mut evaluate = |checker: &mut Checker, e: Node, l: Node| {
        evaluate_expression(checker, evaluate_entity, outer_expressions_to_skip, e, l)
    };
    match expr.kind() {
        SyntaxKind::PrefixUnaryExpression => {
            let result = evaluate(checker, expr.operand(), location);
            resolved_other_files = result.resolved_other_files;
            has_external_references = result.has_external_references;
            if let Some(LiteralValue::Number(value)) = result.value {
                match expr.operator() {
                    SyntaxKind::PlusToken => {
                        return new_result(
                            Some(LiteralValue::Number(value)),
                            is_syntactically_string,
                            resolved_other_files,
                            has_external_references,
                        );
                    }
                    SyntaxKind::MinusToken => {
                        return new_result(
                            Some(LiteralValue::Number(-value)),
                            is_syntactically_string,
                            resolved_other_files,
                            has_external_references,
                        );
                    }
                    SyntaxKind::TildeToken => {
                        return new_result(
                            Some(LiteralValue::Number(value.bitwise_not())),
                            is_syntactically_string,
                            resolved_other_files,
                            has_external_references,
                        );
                    }
                    _ => {}
                }
            }
        }
        SyntaxKind::BinaryExpression => {
            let left = evaluate(checker, expr.left(), location);
            let right = evaluate(checker, expr.right(), location);
            let operator = expr.operator_token().kind();
            is_syntactically_string = (left.is_syntactically_string
                || right.is_syntactically_string)
                && expr.operator_token().kind() == SyntaxKind::PlusToken;
            resolved_other_files = left.resolved_other_files || right.resolved_other_files;
            has_external_references = left.has_external_references || right.has_external_references;
            let (left_num, left_is_num) = match &left.value {
                Some(LiteralValue::Number(n)) => (*n, true),
                _ => (Number::default(), false),
            };
            let (right_num, right_is_num) = match &right.value {
                Some(LiteralValue::Number(n)) => (*n, true),
                _ => (Number::default(), false),
            };
            if left_is_num && right_is_num {
                let value = match operator {
                    SyntaxKind::BarToken => Some(left_num.bitwise_or(right_num)),
                    SyntaxKind::AmpersandToken => Some(left_num.bitwise_and(right_num)),
                    SyntaxKind::GreaterThanGreaterThanToken => {
                        Some(left_num.signed_right_shift(right_num))
                    }
                    SyntaxKind::GreaterThanGreaterThanGreaterThanToken => {
                        Some(left_num.unsigned_right_shift(right_num))
                    }
                    SyntaxKind::LessThanLessThanToken => Some(left_num.left_shift(right_num)),
                    SyntaxKind::CaretToken => Some(left_num.bitwise_xor(right_num)),
                    SyntaxKind::AsteriskToken => Some(left_num * right_num),
                    SyntaxKind::SlashToken => Some(left_num / right_num),
                    SyntaxKind::PlusToken => Some(left_num + right_num),
                    SyntaxKind::MinusToken => Some(left_num - right_num),
                    SyntaxKind::PercentToken => Some(left_num.remainder(right_num)),
                    SyntaxKind::AsteriskAsteriskToken => Some(left_num.exponentiate(right_num)),
                    _ => None,
                };
                if let Some(value) = value {
                    return new_result(
                        Some(LiteralValue::Number(value)),
                        is_syntactically_string,
                        resolved_other_files,
                        has_external_references,
                    );
                }
            }
            let (mut left_str, left_is_str) = match &left.value {
                Some(LiteralValue::String(s)) => (s.clone(), true),
                _ => (String::new(), false),
            };
            let (mut right_str, right_is_str) = match &right.value {
                Some(LiteralValue::String(s)) => (s.clone(), true),
                _ => (String::new(), false),
            };
            if (left_is_str || left_is_num)
                && (right_is_str || right_is_num)
                && operator == SyntaxKind::PlusToken
            {
                if left_is_num {
                    left_str = left_num.to_string();
                }
                if right_is_num {
                    right_str = right_num.to_string();
                }
                // PORT: Go joins the bytes; `go_value_owned` gives the port
                // form of the joined Go string (see
                // `scanner_util::GO_STRING_MARKER`).
                return new_result(
                    Some(LiteralValue::String(go_value_owned(left_str + &right_str))),
                    is_syntactically_string,
                    resolved_other_files,
                    has_external_references,
                );
            }
        }
        SyntaxKind::StringLiteral | SyntaxKind::NoSubstitutionTemplateLiteral => {
            return new_result(
                Some(LiteralValue::String(expr.text().to_string())),
                true, /*isSyntacticallyString*/
                false,
                false,
            );
        }
        SyntaxKind::TemplateExpression => {
            return evaluate_template_expression(checker, expr, location, &mut evaluate);
        }
        SyntaxKind::NumericLiteral => {
            return new_result(
                Some(LiteralValue::Number(ts_jsnum::from_string(expr.text()))),
                false,
                false,
                false,
            );
        }
        SyntaxKind::Identifier => {
            return (evaluate_entity.as_ref())(checker, expr, location);
        }
        SyntaxKind::ElementAccessExpression | SyntaxKind::PropertyAccessExpression => {
            if is_entity_name_expression(expr.expression()) {
                return (evaluate_entity.as_ref())(checker, expr, location);
            }
        }
        _ => {}
    }
    new_result(
        None,
        is_syntactically_string,
        resolved_other_files,
        has_external_references,
    )
}

// Go: evaluator/evaluator.go:124 evaluateTemplateExpression
fn evaluate_template_expression(
    checker: &mut Checker,
    expr: Node,
    location: Node,
    evaluate: &mut dyn FnMut(&mut Checker, Node, Node) -> EvaluatorResult,
) -> EvaluatorResult {
    let mut sb = String::new();
    sb.push_str(expr.head().text());
    let mut resolved_other_files = false;
    let mut has_external_references = false;
    for span in expr.template_spans().nodes().iter() {
        let span_result = evaluate(checker, span.expression(), location);
        let Some(value) = &span_result.value else {
            return new_result(None, true, /*isSyntacticallyString*/ false, false);
        };
        sb.push_str(&any_to_string(value));
        sb.push_str(span.literal().text());
        resolved_other_files = resolved_other_files || span_result.resolved_other_files;
        has_external_references = has_external_references || span_result.has_external_references;
    }
    // PORT: see the `+` case in `evaluate`.
    new_result(
        Some(LiteralValue::String(go_value_owned(sb))),
        true,
        resolved_other_files,
        has_external_references,
    )
}

// PORT: Go takes `any`; a nil value panics in Go ("Unhandled case"). Callers
// with an `Option<LiteralValue>` unwrap first, which panics the same way.
// Go: evaluator/evaluator.go:142 AnyToString
pub fn any_to_string(v: &LiteralValue) -> String {
    match v {
        LiteralValue::String(v) => v.clone(),
        LiteralValue::Number(v) => v.to_string(),
        LiteralValue::Bool(v) => if *v { "true" } else { "false" }.to_string(),
        LiteralValue::PseudoBigInt(v) => v.to_string(),
    }
}

// Go: evaluator/evaluator.go:156 IsTruthy
pub fn is_truthy(v: &LiteralValue) -> bool {
    match v {
        LiteralValue::String(v) => !v.is_empty(),
        LiteralValue::Number(v) => v.0 != 0.0 && !v.is_nan(),
        LiteralValue::Bool(v) => *v,
        LiteralValue::PseudoBigInt(v) => *v != PseudoBigInt::default(),
    }
}
