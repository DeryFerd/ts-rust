//! Port of Effect-TS/tsgo `etslshooks/inlay_hints.go` (effect-tsgo 0.51.1):
//! the inlay hint filter. Option `inlays` (default false).

use crate::astnav;
use crate::effect::rulerunner::enabled_options;
use crate::effect::typeparser::TypeParser;
use crate::ls::{lsconv, lsutil};
use crate::lsp::lsproto;
use crate::prelude::*;

// Go: etslshooks/inlay_hints.go:16 afterInlayHints
/// afterInlayHints filters out redundant return-type inlay hints on Effect.gen,
/// Effect.fn, Effect.fnUntraced, and Effect.fnUntracedEager generator functions.
/// `ls/inlay_hints.rs` calls it for each mapped range (Effect-TS/tsgo patch 015).
// PORT: Go also passes the program and the span, and makes the type parser
// before the plugin check. The type parser takes the checker's program, Go
// does not read the span, and the type parser is made after the checks.
pub fn after_inlay_hints(
    c: &mut Checker,
    sf: Node,
    _span: TextRange,
    preferences: &lsutil::InlayHintsPreferences,
    hints: Vec<lsproto::InlayHint>,
    converters: &lsconv::Converters,
) -> Vec<lsproto::InlayHint> {
    let Some(effect_config) = enabled_options(c.compiler_options) else {
        return hints;
    };
    if !effect_config.inlays {
        return hints;
    }

    if !preferences
        .include_inlay_function_like_return_type_hints
        .is_true()
    {
        return hints;
    }

    let program = c.program;
    let mut tp = TypeParser::new(program, c);
    let mut result = Vec::with_capacity(hints.len());
    for hint in hints {
        if should_omit_hint(&mut tp, sf, &hint, converters) {
            continue;
        }
        result.push(hint);
    }
    result
}

// Go: etslshooks/inlay_hints.go:47 shouldOmitHint
/// shouldOmitHint checks whether a single inlay hint should be suppressed
/// because it is a return-type hint on an Effect generator function.
fn should_omit_hint(
    tp: &mut TypeParser<'_>,
    sf: Node,
    hint: &lsproto::InlayHint,
    converters: &lsconv::Converters,
) -> bool {
    if hint.kind != Some(lsproto::InlayHintKind::TYPE) {
        return false;
    }

    // Convert LSP position back to raw text offset
    let offset = lsconv::from_lsp_range_to_original(
        converters,
        &sf,
        lsproto::Range {
            start: hint.position,
            end: hint.position,
        },
    )
    .pos();

    // Find the token at offset-1 (matching the TS reference: findNodeAtPositionIncludingTrivia(sf, position - 1))
    let node = astnav::get_token_at_position(sf, offset - 1);
    if node.is_nil() || node.parent().is_nil() {
        return false;
    }

    // Walk up from the token to find the CallExpression.
    // The token at offset-1 is typically the CloseParenToken of function*().
    // Its parent is the FunctionExpression, and grandparent is the CallExpression
    // (e.g. Effect.gen(function*() { ... })). For curried variants like
    // Effect.fn("name")(function*() { ... }), the outer CallExpression may be
    // one more level up. Try ancestors up to a reasonable depth.
    let mut gen_node = Node::NIL;
    let mut gen_body = Node::NIL;
    let mut ancestor = node.parent();
    while ancestor.is_some() {
        if ancestor.kind() == SyntaxKind::CallExpression {
            (gen_node, gen_body) = match_effect_gen_call(tp, ancestor);
            if gen_node.is_some() && gen_body.is_some() {
                break;
            }
        }
        ancestor = ancestor.parent();
    }
    if gen_node.is_nil() || gen_body.is_nil() {
        return false;
    }

    // Check if the hint position falls between the close paren of the generator
    // function's parameter list and the start of the body
    let close_paren = astnav::find_child_of_kind(gen_node, SyntaxKind::CloseParenToken, sf);
    if close_paren.is_nil() {
        return false;
    }

    let body_start = astnav::get_start_of_node(gen_body, sf, false);
    offset >= close_paren.end() && offset <= body_start
}

// Go: etslshooks/inlay_hints.go:98 matchEffectGenCall
/// matchEffectGenCall tries all four Effect generator call patterns and returns
/// the generator function and body for the first match.
fn match_effect_gen_call(tp: &mut TypeParser<'_>, node: Node) -> (Node, Node) {
    if let Some(result) = tp.effect_gen_call(node) {
        return (result.generator_function, result.body);
    }
    if let Some(result) = tp.effect_fn_call(node)
        && result.is_generator()
    {
        return (result.generator_function(), result.body());
    }
    (Node::NIL, Node::NIL)
}
