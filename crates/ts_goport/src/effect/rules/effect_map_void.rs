//! Port of Effect-TS/tsgo `internal/rules/effect_map_void.go`.

use crate::effect::diag;
use crate::effect::etscore::*;
use crate::effect::rule::*;
use crate::effect::typeparser::*;
use crate::prelude::*;

/// EffectMapVoid suggests using Effect.asVoid instead of Effect.map(() => void 0),
/// Effect.map(() => undefined), or Effect.map(() => {}).
// Go: rules/effect_map_void.go EffectMapVoid
pub static EFFECT_MAP_VOID: Rule = Rule {
    name: "effectMapVoid",
    group: "style",
    description: "Suggests using Effect.asVoid instead of Effect.map(() => void 0), Effect.map(() => undefined), or Effect.map(() => {})",
    default_severity: Severity::Suggestion,
    supported_effect: &["v3", "v4"],
    codes: &[377018],
    run: run_effect_map_void,
};

fn run_effect_map_void(ctx: &mut RuleContext<'_, '_>) -> Vec<Diagnostic> {
    let matches = analyze_effect_map_void(ctx.tp, ctx.source_file);
    let mut diags = Vec::with_capacity(matches.len());
    for m in &matches {
        diags.push(ctx.new_diagnostic(
            m.source_file,
            m.location,
            diag::This_expression_discards_the_success_value_through_mapping_Effect_asVoid_represents_that_form_directly_effect_effectMapVoid,
            Vec::new(),
            vec![],
        ));
    }
    diags
}

/// EffectMapVoidMatch holds the AST nodes needed by both the diagnostic rule
/// and the quick-fix for the effectMapVoid pattern.
// PORT: Go holds a `*PipingFlowTransformation` into the flow; the port keeps
// a copy.
// Go: rules/effect_map_void.go EffectMapVoidMatch
#[derive(Clone, Debug)]
pub struct EffectMapVoidMatch {
    /// The source file where the diagnostic should be reported
    pub source_file: Node,
    /// The pre-computed error range for this match
    pub location: TextRange,
    pub transformation: PipingFlowTransformation,
    /// The Effect module identifier (e.g., "Effect" in Effect.map)
    pub effect_module_node: Node,
}

/// isVoidCallback checks if a callback argument is a "void callback":
/// either an empty function (block body with zero statements) or a lazy void expression
/// (zero-param function returning void 0, undefined, or parenthesized versions).
// Go: rules/effect_map_void.go isVoidCallback
fn is_void_callback(node: Node) -> bool {
    // First try parsing as a lazy expression (thunk=true, requiring zero params)
    let lazy = parse_lazy_expression(node, LazyExpressionFlags::THUNK);
    if let Some(lazy) = lazy {
        // ParseLazyExpression succeeded — check if the expression is a void expression
        return super::effect_succeed_with_void::is_void_expression(lazy.expression);
    }

    // ParseLazyExpression returns nil for empty block bodies (0 statements).
    // Handle that case explicitly: arrow function or function expression with
    // zero parameters, no type parameters, and a block body with zero statements.
    match node.kind() {
        SyntaxKind::ArrowFunction => {
            let fn_ = node;
            if fn_.type_parameter_list().is_some() && !fn_.type_parameter_list().nodes().is_empty()
            {
                return false;
            }
            if fn_.parameter_list().is_some() && !fn_.parameter_list().nodes().is_empty() {
                return false;
            }
            if fn_.body().is_some() && fn_.body().kind() == SyntaxKind::Block {
                let block = fn_.body();
                return block.statement_list().is_nil() || block.statements().is_empty();
            }
        }
        SyntaxKind::FunctionExpression => {
            let fn_ = node;
            if fn_.type_parameter_list().is_some() && !fn_.type_parameter_list().nodes().is_empty()
            {
                return false;
            }
            if fn_.parameter_list().is_some() && !fn_.parameter_list().nodes().is_empty() {
                return false;
            }
            if fn_.body().is_some() && fn_.body().kind() == SyntaxKind::Block {
                let block = fn_.body();
                return block.statement_list().is_nil() || block.statements().is_empty();
            }
        }
        _ => {}
    }

    false
}

/// AnalyzeEffectMapVoid finds data-last and data-first Effect.map calls with void
/// callbacks that can be replaced with Effect.asVoid. Driving detection off the
/// piping-flow transformations (rather than a raw AST walk) normalizes the subject
/// away, so both pipe(self, Effect.map(cb)) / self.pipe(Effect.map(cb)) and the
/// data-first Effect.map(self, cb) are matched uniformly.
// Go: rules/effect_map_void.go AnalyzeEffectMapVoid
pub fn analyze_effect_map_void(tp: &mut TypeParser<'_>, sf: Node) -> Vec<EffectMapVoidMatch> {
    let mut matches: Vec<EffectMapVoidMatch> = Vec::new();

    let flows = tp.piping_flows(sf, true);
    for flow in flows.iter() {
        for index in 0..flow.transformations.len() {
            let transformation = &flow.transformations[index];
            if transformation.args.len() != 1
                || transformation.callee.is_nil()
                || !tp.is_node_reference_to_effect_module_api(transformation.callee, "map")
            {
                continue;
            }
            if !is_void_callback(transformation.args[0]) {
                continue;
            }
            let mut effect_module = Node::NIL;
            if transformation.callee.kind() == SyntaxKind::PropertyAccessExpression {
                effect_module = transformation.callee.expression();
            }
            matches.push(EffectMapVoidMatch {
                source_file: sf,
                location: get_error_range_for_node(sf, transformation.callee),
                transformation: transformation.clone(),
                effect_module_node: effect_module,
            });
        }
    }

    matches
}
