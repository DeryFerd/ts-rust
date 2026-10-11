//! Port of Effect-TS/tsgo `internal/fixables/option_match_to_from_option.go`.

use crate::effect::ls::fixable::{Fixable, FixableContext};
use crate::effect::ls::rewriter::{PipingFlowTransformationReplacement, Tracker};
use crate::effect::rules::option_match_to_from_option::{
    OptionMatchToFromOptionMatch, analyze_option_match_to_from_option,
};
use crate::effect::typeparser::find_effect_module_identifier;
use crate::ls::CodeAction;
use crate::prelude::*;

// Go: fixables/option_match_to_from_option.go:13 OptionMatchToFromOptionFix
pub static OPTION_MATCH_TO_FROM_OPTION_FIX: Fixable = Fixable {
    name: "optionMatchToFromOption",
    description: "Replace Option.match or an Option tag conditional with Effect.fromOption",
    // Go: tsdiag.Effect_fromOption_expresses_this_Option_to_Effect_conversion_more_directly_than_Option_match_or_an_Option_tag_conditional_effect_optionMatchToFromOption
    error_codes: &[377118],
    fix_ids: &["optionMatchToFromOption_fix"],
    run: run_option_match_to_from_option_fix,
};

// Go: fixables/option_match_to_from_option.go:23 runOptionMatchToFromOptionFix
fn run_option_match_to_from_option_fix(ctx: &mut FixableContext<'_, '_>) -> Vec<CodeAction> {
    for m in analyze_option_match_to_from_option(ctx.tp, ctx.source_file) {
        if !m.location.intersects(ctx.span) && !ctx.span.contained_by(m.location) {
            continue;
        }
        if !m.can_fix
            || m.transformation.is_none() && (m.replacement_node.is_nil() || m.option_node.is_nil())
        {
            continue;
        }
        let effect_module_name = find_effect_module_identifier(ctx.source_file);

        let sf = ctx.source_file;
        if let Some(action) =
            ctx.new_fix_action("Replace with Effect.fromOption".to_string(), |tracker| {
                let (callee, arguments) =
                    build_from_option_replacement(tracker, &m, &effect_module_name);
                if callee.is_nil() {
                    return;
                }
                if let Some(transformation) = &m.transformation {
                    tracker.replace_piping_flow_transformation(
                        sf,
                        transformation,
                        PipingFlowTransformationReplacement {
                            callee,
                            type_arguments: NodeList::NIL,
                            arguments,
                        },
                    );
                    return;
                }

                let f = tracker.node_factory();
                let mut direct_arguments = vec![f.deep_clone_node(m.option_node)];
                direct_arguments.extend(arguments.nodes().iter());
                let replacement = f.new_call_expression(
                    callee,
                    Node::NIL,
                    NodeList::NIL,
                    f.new_node_list(&direct_arguments),
                    NodeFlags::NONE,
                );
                set_parent_in_children(replacement);
                tracker.replace_node(sf, m.replacement_node, replacement, None);
            })
        {
            return vec![action];
        }
    }
    Vec::new()
}

// Go: fixables/option_match_to_from_option.go:64 buildFromOptionReplacement
fn build_from_option_replacement(
    tracker: &Tracker,
    m: &OptionMatchToFromOptionMatch,
    effect_module_name: &str,
) -> (Node, NodeList) {
    let f = tracker.node_factory();
    let module_node = if m.effect_module_node.is_nil() {
        f.new_identifier(effect_module_name)
    } else {
        f.deep_clone_node(m.effect_module_node)
    };
    let from_option = f.new_property_access_expression(
        module_node,
        Node::NIL,
        f.new_identifier("fromOption"),
        NodeFlags::NONE,
    );

    if m.default_failure {
        return (from_option, NodeList::NIL);
    }

    (
        from_option,
        f.new_node_list(&[f.new_arrow_function(
            ModifierList::NIL,
            NodeList::NIL,
            f.new_node_list(&[]),
            Node::NIL,
            Node::NIL,
            f.new_token(SyntaxKind::EqualsGreaterThanToken),
            f.deep_clone_node(m.failure_node),
        )]),
    )
}
