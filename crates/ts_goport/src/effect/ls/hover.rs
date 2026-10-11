//! Port of the hover hook of Effect-TS/tsgo `etslshooks/init.go`
//! (effect-tsgo 0.51.1): `afterQuickInfo`, `formatLayerHover`,
//! `isDeclarationName` and `formatEffectTypeParams`. Option `quickinfo`
//! (default true).

use crate::effect::etscore::EffectPluginOptions;
use crate::effect::layergraph;
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
    sf: Node,
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
    if tp.is_layer_type(t) && is_declaration_name(node) {
        let documentation = format_layer_hover(
            &mut tp,
            sf,
            node,
            &documentation,
            is_markdown,
            effect_config,
        );
        return (quick_info, documentation, Node::NIL);
    }

    let Some(effect) = tp.effect_type(t) else {
        return (quick_info, documentation, Node::NIL);
    };

    let documentation = format_effect_type_params(tp.checker, &effect, &documentation, is_markdown);

    (quick_info, documentation, Node::NIL)
}

// Go: etslshooks/init.go:245 formatLayerHover
/// formatLayerHover builds the Layer hover documentation including providers/requirers
/// summary, Mermaid diagram links, and Layer type parameters.
// PORT: Go also takes the checker (the type parser's checker here) and the
// Layer type, which it does not read. Go's comment names Layer type
// parameters, but the function adds none.
fn format_layer_hover(
    tp: &mut TypeParser<'_>,
    sf: Node,
    node: Node,
    documentation: &str,
    is_markdown: bool,
    effect_config: &EffectPluginOptions,
) -> String {
    // Try to resolve the initializer expression for layer graph extraction.
    let mut initializer = Node::NIL;
    let parent = node.parent();
    if parent.is_some()
        && matches!(
            parent.kind(),
            SyntaxKind::VariableDeclaration | SyntaxKind::PropertyDeclaration
        )
    {
        initializer = parent.initializer();
    }

    let mut quick_info_summary = String::new();
    let mut has_graph = false;
    let mut nested_diagram = String::new();
    let mut outline_diagram = String::new();
    if initializer.is_some() {
        // PORT: Go `FollowSymbolsDepth` is an `int`; the port's option is an
        // `i32`, and a larger depth is never reached.
        let opts = layergraph::ExtractLayerGraphOptions {
            follow_symbols_depth: i32::try_from(effect_config.get_layer_graph_follow_depth())
                .unwrap_or(i32::MAX),
            ..Default::default()
        };
        let full_graph = layergraph::extract_layer_graph(tp, &[initializer], sf, opts);
        let info = layergraph::extract_providers_and_requirers(tp.checker, &full_graph);
        quick_info_summary = layergraph::format_quick_info(tp.checker, &info, sf);
        has_graph = true;

        if !effect_config.no_external {
            nested_diagram = layergraph::format_nested_layer_graph(tp.checker, &full_graph, sf);
            let outline_graph = layergraph::extract_outline_graph(tp, &full_graph);
            outline_diagram = layergraph::format_outline_graph(&outline_graph, sf);
        }
    }

    // Build combined documentation: quickinfo summary (provides/requires) and links.
    let mut b = String::new();

    if !quick_info_summary.is_empty() {
        if is_markdown {
            b.push_str("```\n");
            b.push_str(&quick_info_summary);
            b.push_str("\n```\n");
        } else {
            b.push_str(&quick_info_summary);
            b.push('\n');
        }
    }

    // Generate Mermaid diagram links when we have a graph and external links are not suppressed.
    if has_graph && !effect_config.no_external {
        let base_url = effect_config.get_mermaid_base_url();

        let mut nested_url = String::new();
        let mut outline_url = String::new();
        if !nested_diagram.is_empty() {
            nested_url = layergraph::encode_mermaid_url(&base_url, &nested_diagram);
        }
        if !outline_diagram.is_empty() {
            outline_url = layergraph::encode_mermaid_url(&base_url, &outline_diagram);
        }

        if is_markdown {
            match (nested_url.is_empty(), outline_url.is_empty()) {
                (false, false) => b.push_str(&format!(
                    "[Show full graph]({nested_url}) - [Show outline]({outline_url})\n\n"
                )),
                (false, true) => b.push_str(&format!("[Show full graph]({nested_url})\n\n")),
                (true, false) => b.push_str(&format!("[Show outline]({outline_url})\n\n")),
                (true, true) => {}
            }
        } else {
            if !nested_url.is_empty() {
                b.push_str(&format!("{{@link {nested_url} Show full graph}}\n\n"));
            }
            if !outline_url.is_empty() {
                b.push_str(&format!("{{@link {outline_url} Show outline}}\n\n"));
            }
        }
    }

    if !documentation.is_empty() {
        b.push('\n');
        b.push_str(documentation);
    }

    b
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
