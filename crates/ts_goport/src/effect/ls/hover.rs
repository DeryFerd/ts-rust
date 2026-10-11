//! Port of the hover hook of Effect-TS/tsgo `etslshooks/init.go`
//! (effect-tsgo 0.51.1): `afterQuickInfo`, `isDeclarationName` and
//! `formatEffectTypeParams`. Option `quickinfo` (default true).

use crate::effect::rulerunner::enabled_options;
use crate::effect::typeparser::{Effect, EffectContextFlags, TypeParser};
use crate::prelude::*;

// Go: etslshooks/init.go:183 afterQuickInfo
/// Called by `ls/hover.rs` after the quick info and documentation of a hover
/// are built (Effect-TS/tsgo patch 012). It adds the Effect type parameters
/// to the documentation of an Effect-typed node, and answers a hover on
/// `yield*` in an Effect generator. Returns the quick info, the
/// documentation and the node whose range the hover takes (`Node::NIL`:
/// keep the range).
// PORT: Go also passes the program and the symbol. The type parser takes
// the checker's program (the same program), and Go does not read the symbol.
// Go makes the type parser before the plugin check; here it is made after
// it, so a project without the plugin does not touch the checker.
pub fn after_quick_info(
    c: &mut Checker,
    _sf: Node,
    node: Node,
    quick_info: String,
    documentation: String,
    is_markdown: bool,
) -> (String, String, Node) {
    // Check if Effect is enabled
    let Some(effect_config) = enabled_options(c.compiler_options) else {
        return (quick_info, documentation, Node::NIL);
    };
    if !effect_config.get_quickinfo_enabled() {
        return (quick_info, documentation, Node::NIL);
    }
    let program = c.program;
    let mut tp = TypeParser::new(program, c);

    // Yield* hover: normalize positions on yield, *, and the space before the operand.
    let mut yield_node = Node::NIL;
    match node.kind() {
        SyntaxKind::YieldExpression => yield_node = node,
        SyntaxKind::YieldKeyword | SyntaxKind::AsteriskToken => {
            let parent = node.parent();
            if parent.is_some() && parent.kind() == SyntaxKind::YieldExpression {
                yield_node = parent;
            }
        }
        _ => {}
    }
    if yield_node.is_some() {
        let asterisk_token = yield_node.asterisk_token();
        let expression = yield_node.expression();
        if asterisk_token.is_some()
            && expression.is_some()
            && tp
                .get_effect_context_flags(yield_node)
                .intersects(EffectContextFlags::CAN_YIELD_EFFECT)
        {
            let t = tp.get_type_at_location(expression);
            if t.is_some()
                && let Some(effect) = tp.effect_yieldable_type(t)
            {
                let type_str = tp.checker.type_to_string_ex(
                    t,
                    Node::NIL,
                    TypeFormatFlags::NO_TRUNCATION,
                    None,
                );
                let quick_info = "(yield*) ".to_string() + &type_str;
                let documentation = format_effect_type_params(tp.checker, &effect, "", is_markdown);
                return (quick_info, documentation, yield_node);
            }
        }
    }

    // General symbol hover: enrich Effect-typed symbols with type parameters
    let t = tp.get_type_at_location(node);
    if t.is_nil() {
        return (quick_info, documentation, Node::NIL);
    }

    // Layer hover: detect Layer types and show providers/requirers summary.
    // Layer extends Effect in V4, so this check must come before the Effect check.
    // Only activate layer hover enrichment when the cursor is on the name of the declaration,
    // not on arbitrary nodes within the initializer expression.
    // PORT: lane E7 ports Go `formatLayerHover` (the provides/requires
    // summary and the Mermaid links: layergraph format.go, providers.go,
    // mermaidurl.go). Until then the documentation stays as it is here.
    if tp.is_layer_type(t) && is_declaration_name(node) {
        return (quick_info, documentation, Node::NIL);
    }

    let Some(effect) = tp.effect_type(t) else {
        return (quick_info, documentation, Node::NIL);
    };

    let documentation = format_effect_type_params(tp.checker, &effect, &documentation, is_markdown);

    (quick_info, documentation, Node::NIL)
}

// Go: etslshooks/init.go:332 isDeclarationName
/// isDeclarationName checks whether the given node is the name node of a variable or property declaration.
/// This is used to restrict layer hover enrichment to the declaration name only,
/// not to arbitrary nodes within the initializer expression.
#[must_use]
pub fn is_declaration_name(node: Node) -> bool {
    let parent = node.parent();
    if parent.is_nil() {
        return false;
    }
    match parent.kind() {
        SyntaxKind::VariableDeclaration | SyntaxKind::PropertyDeclaration => parent.name() == node,
        _ => false,
    }
}

// Go: etslshooks/init.go:347 formatEffectTypeParams
/// formatEffectTypeParams formats Effect type parameters (A, E, R) and prepends them to documentation.
pub fn format_effect_type_params(
    c: &mut Checker,
    effect: &Effect,
    documentation: &str,
    is_markdown: bool,
) -> String {
    let a_str = c.type_to_string_ex(effect.a, Node::NIL, TypeFormatFlags::NO_TRUNCATION, None);
    let e_str = c.type_to_string_ex(effect.e, Node::NIL, TypeFormatFlags::NO_TRUNCATION, None);
    let r_str = c.type_to_string_ex(effect.r, Node::NIL, TypeFormatFlags::NO_TRUNCATION, None);

    let prefix = if is_markdown {
        format!(
            "```ts\n/* Effect Type Parameters */\ntype Success = {a_str}\ntype Failure = {e_str}\ntype Requirements = {r_str}\n```\n"
        )
    } else {
        format!(
            "Effect Type Parameters:\n  Success = {a_str}\n  Failure = {e_str}\n  Requirements = {r_str}\n"
        )
    };

    let mut b = prefix;
    if !documentation.is_empty() {
        b.push('\n');
        b.push_str(documentation);
    }
    b
}
