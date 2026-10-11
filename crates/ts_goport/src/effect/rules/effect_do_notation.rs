// Go: internal/rules/effect_do_notation.go

use crate::effect::diag;
use crate::effect::etscore::*;
use crate::effect::rule::*;
use crate::effect::typeparser::*;
use crate::prelude::*;

/// EffectDoNotation suggests using Effect.gen or Effect.fn instead of Effect.Do.
pub static EFFECT_DO_NOTATION: Rule = Rule {
    name: "effectDoNotation",
    group: "style",
    description: "Suggests using Effect.gen or Effect.fn instead of the Effect.Do notation helpers",
    default_severity: Severity::Off,
    supported_effect: &["v3", "v4"],
    codes: &[377085],
    run: run_effect_do_notation,
};

fn run_effect_do_notation(ctx: &mut RuleContext<'_, '_>) -> Vec<Diagnostic> {
    let matches = analyze_effect_do_notation(ctx.tp, ctx.source_file);
    let mut diags = Vec::with_capacity(matches.len());
    for m in &matches {
        diags.push(ctx.new_diagnostic(
            m.source_file,
            m.location,
            diag::This_uses_the_Effect_do_emulation_Effect_gen_or_Effect_fn_achieve_the_same_result_with_native_JS_scopes_effect_effectDoNotation,
            Vec::new(),
            Vec::new(),
        ));
    }
    diags
}

#[derive(Clone, Debug)]
pub struct EffectDoNotationMatch {
    pub source_file: Node,
    pub location: TextRange,
    pub node: Node,
}

// Go: rules/effect_do_notation.go AnalyzeEffectDoNotation
/// AnalyzeEffectDoNotation finds all references to Effect.Do-style helpers.
pub fn analyze_effect_do_notation(tp: &mut TypeParser<'_>, sf: Node) -> Vec<EffectDoNotationMatch> {
    let mut matches = Vec::new();
    // PERF: Go walks the tree; the node order has the same nodes in the same
    // order (effperf4). A match is not walked into.
    tp.node_order(sf).walk_preorder(|n| {
        if tp.is_node_reference_to_effect_module_api(n, member!("Do")) {
            matches.push(EffectDoNotationMatch {
                source_file: sf,
                location: get_error_range_for_node(sf, n),
                node: n,
            });
            Walk::SkipChildren
        } else {
            Walk::Descend
        }
    });
    matches
}
