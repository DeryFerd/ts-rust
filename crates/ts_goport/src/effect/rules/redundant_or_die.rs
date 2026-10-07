//! Port of Effect-TS/tsgo `internal/rules/redundant_or_die.go`.

use crate::effect::diag;
use crate::effect::etscore::*;
use crate::effect::rule::*;
use crate::effect::typeparser::*;
use crate::prelude::*;

// Go: rules/redundant_or_die.go RedundantOrDie
pub static REDUNDANT_OR_DIE: Rule = Rule {
    name: "redundantOrDie",
    group: "style",
    description: "Suggests hoisting a repeated trailing Effect.orDie from every yield in an Effect generator",
    default_severity: Severity::Suggestion,
    supported_effect: &["v3", "v4"],
    codes: &[377096, 377097],
    run: run_redundant_or_die,
};

fn run_redundant_or_die(ctx: &mut RuleContext<'_, '_>) -> Vec<Diagnostic> {
    let matches = analyze_redundant_generator_or_die(ctx.tp, ctx.source_file);
    let mut diags = Vec::with_capacity(matches.len());
    for m in &matches {
        let related = redundant_or_die_related_information(ctx, m);
        diags.push(ctx.new_diagnostic(
            m.source_file,
            m.location,
            diag::This_generator_applies_Effect_orDie_to_every_yielded_effect_Hoist_it_once_to_the_generator_result_Colon_Effect_gen_pipe_Effect_orDie_or_Effect_fn_function_Asterisk_Effect_orDie_effect_redundantOrDie,
            related,
            vec![],
        ));
    }
    diags
}

// Go: rules/redundant_or_die.go RedundantGeneratorOrDieMatch
#[derive(Clone, Debug)]
pub struct RedundantGeneratorOrDieMatch {
    pub source_file: Node,
    pub location: TextRange,
    pub generator_call_node: Node,
    pub generator_function: Node,
    pub or_die_nodes: Vec<Node>,
    pub yield_expressions: Vec<Node>,
}

// Go: rules/redundant_or_die.go redundantOrDieCandidate
#[derive(Clone, Copy, Debug, Default)]
pub struct RedundantOrDieCandidate {
    pub yield_expression: Node,
    pub or_die_node: Node,
}

// PORT: Go returns nil for a nil `tp` or checker; the port has neither.
// Go ranges over `candidatesByGenerator` in random map order; the port keeps
// the first-seen order of the generator functions (`IndexMap`).
// Go: rules/redundant_or_die.go AnalyzeRedundantGeneratorOrDie
pub fn analyze_redundant_generator_or_die(
    tp: &mut TypeParser<'_>,
    sf: Node,
) -> Vec<RedundantGeneratorOrDieMatch> {
    if sf.is_nil() {
        return Vec::new();
    }

    let mut generator_calls: FxHashMap<Node, Node> = FxHashMap::default();
    let mut candidates_by_generator: IndexMap<Node, FxHashMap<Node, RedundantOrDieCandidate>> =
        IndexMap::new();

    let flows = tp.piping_flows(sf, true);
    for flow in flows.iter() {
        let (candidate, gen_fn, gen_call_node, ok) =
            analyze_redundant_or_die_flow_candidate(tp, sf, Some(&**flow));
        if !ok {
            continue;
        }
        generator_calls.insert(gen_fn, gen_call_node);
        candidates_by_generator
            .entry(gen_fn)
            .or_default()
            .insert(candidate.yield_expression, candidate);
    }

    let mut matches: Vec<RedundantGeneratorOrDieMatch> = Vec::new();
    for (gen_fn, candidates) in &candidates_by_generator {
        if candidates.len() < 2 {
            continue;
        }
        let gen_call = generator_calls.get(gen_fn).copied().unwrap_or(Node::NIL);
        if let (m, true) =
            analyze_redundant_generator_or_die_candidate(tp, sf, gen_call, *gen_fn, candidates)
        {
            matches.push(m);
        }
    }

    matches
}

// Go: rules/redundant_or_die.go analyzeRedundantOrDieFlowCandidate
fn analyze_redundant_or_die_flow_candidate(
    tp: &mut TypeParser<'_>,
    sf: Node,
    flow: Option<&PipingFlow>,
) -> (RedundantOrDieCandidate, Node, Node, bool) {
    let none = (
        RedundantOrDieCandidate::default(),
        Node::NIL,
        Node::NIL,
        false,
    );
    let Some(flow) = flow else {
        return none;
    };
    if sf.is_nil() || flow.node.is_nil() || flow.transformations.is_empty() {
        return none;
    }

    let last_transform = &flow.transformations[flow.transformations.len() - 1];
    if last_transform.callee.is_nil() {
        return none;
    }
    if !tp.is_node_reference_to_effect_module_api(last_transform.callee, "orDie") {
        return none;
    }

    let yield_expr = super::redundant_map_error::enclosing_yield_expression(flow.node);
    if yield_expr.is_nil()
        || yield_expr.expression().is_nil()
        || yield_expr.expression() != flow.node
        || yield_expr.asterisk_token().is_nil()
    {
        return none;
    }
    if !tp
        .get_effect_context_flags(yield_expr)
        .intersects(EffectContextFlags::CAN_YIELD_EFFECT)
    {
        return none;
    }

    let gen_fn = tp.get_effect_yield_generator_function(yield_expr);
    if gen_fn.is_nil() {
        return none;
    }

    let gen_call_node = super::redundant_map_error::enclosing_generator_call(gen_fn);
    if gen_call_node.is_nil() {
        return none;
    }

    (
        RedundantOrDieCandidate {
            yield_expression: yield_expr,
            or_die_node: last_transform.callee,
        },
        gen_fn,
        gen_call_node,
        true,
    )
}

// Go: rules/redundant_or_die.go analyzeRedundantGeneratorOrDieCandidate
fn analyze_redundant_generator_or_die_candidate(
    tp: &mut TypeParser<'_>,
    sf: Node,
    generator_call_node: Node,
    generator_function: Node,
    candidates: &FxHashMap<Node, RedundantOrDieCandidate>,
) -> (RedundantGeneratorOrDieMatch, bool) {
    let none = || {
        (
            RedundantGeneratorOrDieMatch {
                source_file: Node::NIL,
                location: TextRange::default(),
                generator_call_node: Node::NIL,
                generator_function: Node::NIL,
                or_die_nodes: Vec::new(),
                yield_expressions: Vec::new(),
            },
            false,
        )
    };
    if sf.is_nil() || generator_call_node.is_nil() || generator_function.is_nil() {
        return none();
    }

    let generator_body = generator_function.body();
    if generator_body.is_nil() {
        return none();
    }

    let mut yield_expressions: Vec<Node> = Vec::new();
    let mut or_die_nodes: Vec<Node> = Vec::new();
    let mut valid_yield_count: i32 = 0;

    for_each_yield_expression(generator_body, &mut |expr: Node| -> bool {
        if expr.is_nil() || expr.kind() != SyntaxKind::YieldExpression {
            return false;
        }
        if !tp
            .get_effect_context_flags(expr)
            .intersects(EffectContextFlags::CAN_YIELD_EFFECT)
            || tp.get_effect_yield_generator_function(expr) != generator_function
        {
            return false;
        }

        let yield_expr = expr;
        if yield_expr.is_nil()
            || yield_expr.asterisk_token().is_nil()
            || yield_expr.expression().is_nil()
        {
            return false;
        }

        let Some(candidate) = candidates.get(&expr) else {
            valid_yield_count = -1;
            return true;
        };

        yield_expressions.push(expr);
        or_die_nodes.push(candidate.or_die_node);
        valid_yield_count += 1;
        false
    });

    if valid_yield_count < 2
        || valid_yield_count as usize != candidates.len()
        || or_die_nodes.is_empty()
    {
        return none();
    }

    (
        RedundantGeneratorOrDieMatch {
            source_file: sf,
            location: super::redundant_map_error::generator_function_keyword_range(
                sf,
                generator_function,
            ),
            generator_call_node,
            generator_function,
            or_die_nodes,
            yield_expressions,
        },
        true,
    )
}

// Go: rules/redundant_or_die.go redundantOrDieRelatedInformation
fn redundant_or_die_related_information(
    ctx: &RuleContext<'_, '_>,
    m: &RedundantGeneratorOrDieMatch,
) -> Vec<Diagnostic> {
    if m.or_die_nodes.is_empty() {
        return Vec::new();
    }

    let mut related = Vec::with_capacity(m.or_die_nodes.len());
    for &node in &m.or_die_nodes {
        if node.is_nil() {
            continue;
        }
        related.push(ctx.new_diagnostic(
            m.source_file,
            get_error_range_for_node(m.source_file, node),
            diag::This_repeated_Effect_orDie_site_participates_in_the_hoistable_generator_wide_orDie_effect_redundantOrDie,
            Vec::new(),
            vec![],
        ));
    }
    related
}
