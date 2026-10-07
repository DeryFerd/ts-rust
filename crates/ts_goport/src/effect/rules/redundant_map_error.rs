//! Port of Effect-TS/tsgo `internal/rules/redundant_map_error.go`.

use crate::effect::diag;
use crate::effect::etscore::*;
use crate::effect::rule::*;
use crate::effect::typeparser::*;
use crate::prelude::*;

// Go: rules/redundant_map_error.go RedundantMapError
pub static REDUNDANT_MAP_ERROR: Rule = Rule {
    name: "redundantMapError",
    group: "style",
    description: "Suggests hoisting a repeated trailing Effect.mapError from every yield in an Effect generator",
    default_severity: Severity::Suggestion,
    supported_effect: &["v3", "v4"],
    codes: &[377088, 377089],
    run: run_redundant_map_error,
};

fn run_redundant_map_error(ctx: &mut RuleContext<'_, '_>) -> Vec<Diagnostic> {
    let matches = analyze_redundant_generator_map_error(ctx.tp, ctx.source_file);
    let mut diags = Vec::with_capacity(matches.len());
    for m in &matches {
        let related = redundant_map_error_related_information(ctx, m);
        diags.push(ctx.new_diagnostic(
            m.source_file,
            m.location,
            diag::This_generator_applies_the_same_inline_Effect_mapError_to_every_yielded_effect_Keep_that_Effect_mapError_inline_and_hoist_it_once_to_the_generator_result_Colon_Effect_gen_pipe_Effect_mapError_or_Effect_fn_function_Asterisk_Effect_mapError_effect_redundantMapError,
            related,
            Vec::new(),
        ));
    }
    diags
}

// Go: rules/redundant_map_error.go RedundantGeneratorMapErrorMatch
#[derive(Clone)]
pub struct RedundantGeneratorMapErrorMatch {
    pub source_file: Node,
    pub location: TextRange,
    pub generator_call_node: Node,
    pub generator_function: Node,
    pub map_error_nodes: Vec<Node>,
    pub mapper_node: Node,
    pub yield_expressions: Vec<Node>,
}

// Go: rules/redundant_map_error.go redundantMapErrorCandidate
#[derive(Clone, Default)]
pub struct RedundantMapErrorCandidate {
    pub yield_expression: Node,
    pub map_error_node: Node,
    pub mapper_node: Node,
    pub mapper_text: String,
}

// Go: rules/redundant_map_error.go AnalyzeRedundantGeneratorMapError
pub fn analyze_redundant_generator_map_error(
    tp: &mut TypeParser<'_>,
    sf: Node,
) -> Vec<RedundantGeneratorMapErrorMatch> {
    if sf.is_nil() {
        return Vec::new();
    }

    let mut generator_calls: FxHashMap<Node, Node> = FxHashMap::default();
    // PORT: Go ranges over this map in random order; the port keeps insertion order.
    let mut candidates_by_generator: IndexMap<Node, IndexMap<Node, RedundantMapErrorCandidate>> =
        IndexMap::new();

    for flow in tp.piping_flows(sf, true).iter() {
        let (candidate, gen_fn, gen_call_node, ok) =
            analyze_redundant_map_error_flow_candidate(tp, sf, flow);
        if !ok {
            continue;
        }
        generator_calls.insert(gen_fn, gen_call_node);
        candidates_by_generator
            .entry(gen_fn)
            .or_default()
            .insert(candidate.yield_expression, candidate);
    }

    let mut matches = Vec::new();
    for (gen_fn, candidates) in &candidates_by_generator {
        if candidates.len() < 2 {
            continue;
        }
        let generator_call = generator_calls.get(gen_fn).copied().unwrap_or(Node::NIL);
        let (m, ok) = analyze_redundant_generator_map_error_candidate(
            tp,
            sf,
            generator_call,
            *gen_fn,
            candidates,
        );
        if ok {
            matches.push(m.expect("ok match"));
        }
    }

    matches
}

// Go: rules/redundant_map_error.go analyzeRedundantMapErrorFlowCandidate
fn analyze_redundant_map_error_flow_candidate(
    tp: &mut TypeParser<'_>,
    sf: Node,
    flow: &PipingFlow,
) -> (RedundantMapErrorCandidate, Node, Node, bool) {
    let fail = || {
        (
            RedundantMapErrorCandidate::default(),
            Node::NIL,
            Node::NIL,
            false,
        )
    };
    if sf.is_nil() || flow.node.is_nil() || flow.transformations.is_empty() {
        return fail();
    }

    let last_transform = &flow.transformations[flow.transformations.len() - 1];
    if last_transform.callee.is_nil() || last_transform.args.is_empty() {
        return fail();
    }
    if !tp.is_node_reference_to_effect_module_api(last_transform.callee, "mapError") {
        return fail();
    }

    let yield_expr = enclosing_yield_expression(flow.node);
    if yield_expr.is_nil()
        || yield_expr.expression().is_nil()
        || yield_expr.expression() != flow.node
        || yield_expr.asterisk_token().is_nil()
    {
        return fail();
    }
    if !tp
        .get_effect_context_flags(yield_expr)
        .intersects(EffectContextFlags::CAN_YIELD_EFFECT)
    {
        return fail();
    }

    let gen_fn = tp.get_effect_yield_generator_function(yield_expr);
    if gen_fn.is_nil() {
        return fail();
    }

    let gen_call_node = enclosing_generator_call(gen_fn);
    if gen_call_node.is_nil() {
        return fail();
    }

    let mapper_node = unwrap_transparent_expression(last_transform.args[0]);
    let mapper_text = node_source_text(sf, mapper_node);
    if mapper_node.is_nil() || mapper_text.is_empty() {
        return fail();
    }

    (
        RedundantMapErrorCandidate {
            yield_expression: yield_expr,
            map_error_node: last_transform.callee,
            mapper_node,
            mapper_text,
        },
        gen_fn,
        gen_call_node,
        true,
    )
}

// Go: rules/redundant_map_error.go analyzeRedundantGeneratorMapErrorCandidate
// PORT: Go returns a zero match with `false`; the port returns `None` there.
fn analyze_redundant_generator_map_error_candidate(
    tp: &mut TypeParser<'_>,
    sf: Node,
    generator_call_node: Node,
    generator_function: Node,
    candidates: &IndexMap<Node, RedundantMapErrorCandidate>,
) -> (Option<RedundantGeneratorMapErrorMatch>, bool) {
    if sf.is_nil() || generator_call_node.is_nil() || generator_function.is_nil() {
        return (None, false);
    }

    let generator_body = generator_function.body();
    if generator_body.is_nil() {
        return (None, false);
    }

    let mut yield_expressions: Vec<Node> = Vec::new();
    let mut representative_map_error = Node::NIL;
    let mut map_error_nodes: Vec<Node> = Vec::new();
    let mut representative_mapper = Node::NIL;
    let mut representative_text = String::new();
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
        if yield_expr.asterisk_token().is_nil() || yield_expr.expression().is_nil() {
            return false;
        }

        let Some(candidate) = candidates.get(&expr) else {
            valid_yield_count = -1;
            return true;
        };
        if !mapper_can_be_hoisted(
            tp,
            generator_function,
            generator_call_node,
            candidate.mapper_node,
        ) {
            valid_yield_count = -1;
            return true;
        }

        if representative_map_error.is_nil() {
            representative_map_error = candidate.map_error_node;
            representative_mapper = candidate.mapper_node;
            representative_text = candidate.mapper_text.clone();
        } else if candidate.mapper_text != representative_text {
            valid_yield_count = -1;
            return true;
        }

        yield_expressions.push(expr);
        map_error_nodes.push(candidate.map_error_node);
        valid_yield_count += 1;
        false
    });

    if valid_yield_count < 2
        || valid_yield_count as usize != candidates.len()
        || representative_map_error.is_nil()
        || representative_mapper.is_nil()
    {
        return (None, false);
    }

    (
        Some(RedundantGeneratorMapErrorMatch {
            source_file: sf,
            location: generator_function_keyword_range(sf, generator_function),
            generator_call_node,
            generator_function,
            map_error_nodes,
            mapper_node: representative_mapper,
            yield_expressions,
        }),
        true,
    )
}

// Go: rules/redundant_map_error.go redundantMapErrorRelatedInformation
fn redundant_map_error_related_information(
    ctx: &RuleContext<'_, '_>,
    m: &RedundantGeneratorMapErrorMatch,
) -> Vec<Diagnostic> {
    if m.map_error_nodes.is_empty() {
        return Vec::new();
    }

    let mut related = Vec::with_capacity(m.map_error_nodes.len());
    for &node in &m.map_error_nodes {
        if node.is_nil() {
            continue;
        }
        related.push(ctx.new_diagnostic(
            m.source_file,
            get_error_range_for_node(m.source_file, node),
            diag::This_repeated_Effect_mapError_site_participates_in_the_hoistable_generator_wide_mapping_effect_redundantMapError,
            Vec::new(),
            Vec::new(),
        ));
    }
    related
}

// Go: rules/redundant_map_error.go enclosingYieldExpression
pub fn enclosing_yield_expression(node: Node) -> Node {
    let ancestor = find_ancestor(node, |current| {
        current.is_some() && current.kind() == SyntaxKind::YieldExpression
    });
    if ancestor.is_nil() {
        return Node::NIL;
    }
    ancestor
}

// Go: rules/redundant_map_error.go enclosingGeneratorCall
pub fn enclosing_generator_call(node: Node) -> Node {
    let mut current = node;
    while current.is_some() {
        if current.kind() != SyntaxKind::CallExpression {
            current = current.parent();
            continue;
        }
        return current;
    }
    Node::NIL
}

// Go: rules/redundant_map_error.go mapperCanBeHoisted
fn mapper_can_be_hoisted(
    tp: &mut TypeParser<'_>,
    generator_function_node: Node,
    hoist_location: Node,
    mapper_node: Node,
) -> bool {
    if generator_function_node.is_nil() || hoist_location.is_nil() || mapper_node.is_nil() {
        return false;
    }

    // PORT: Go's recursive `walk` closure; `can_hoist` is its captured variable.
    fn walk(
        tp: &mut TypeParser<'_>,
        generator_function_node: Node,
        hoist_location: Node,
        mapper_node: Node,
        can_hoist: &mut bool,
        node: Node,
    ) -> bool {
        if node.is_nil() || !*can_hoist {
            return *can_hoist;
        }
        if node.kind() == SyntaxKind::Identifier && is_hoist_sensitive_value_reference(node) {
            let symbol = hoist_sensitive_reference_symbol(tp, node);
            if symbol.is_some() {
                if all_symbol_declarations_inside_node(tp.checker, symbol, mapper_node) {
                    node.for_each_child(|child| {
                        walk(
                            tp,
                            generator_function_node,
                            hoist_location,
                            mapper_node,
                            can_hoist,
                            child,
                        )
                    });
                    return !*can_hoist;
                }

                if !all_symbol_declarations_outside_node(
                    tp.checker,
                    symbol,
                    generator_function_node,
                ) {
                    *can_hoist = false;
                    return true;
                }

                if !tp.checker.is_past_last_assignment(symbol, hoist_location) {
                    *can_hoist = false;
                    return true;
                }
            }
        }
        node.for_each_child(|child| {
            walk(
                tp,
                generator_function_node,
                hoist_location,
                mapper_node,
                can_hoist,
                child,
            )
        });
        !*can_hoist
    }

    let mut can_hoist = true;
    walk(
        tp,
        generator_function_node,
        hoist_location,
        mapper_node,
        &mut can_hoist,
        mapper_node,
    );
    can_hoist
}

// Go: rules/redundant_map_error.go allSymbolDeclarationsInsideNode
fn all_symbol_declarations_inside_node(c: &Checker, symbol: SymbolId, node: Node) -> bool {
    if symbol.is_nil() || node.is_nil() || c.sym(symbol).declarations.is_empty() {
        return false;
    }
    for &declaration in c.sym(symbol).declarations.iter() {
        if declaration.is_nil() || !is_node_descendant_of(declaration, node) {
            return false;
        }
    }
    true
}

// Go: rules/redundant_map_error.go allSymbolDeclarationsOutsideNode
fn all_symbol_declarations_outside_node(c: &Checker, symbol: SymbolId, node: Node) -> bool {
    if symbol.is_nil() || node.is_nil() {
        return false;
    }
    for &declaration in c.sym(symbol).declarations.iter() {
        if declaration.is_some() && is_node_descendant_of(declaration, node) {
            return false;
        }
    }
    true
}

// Go: rules/redundant_map_error.go hoistSensitiveReferenceSymbol
fn hoist_sensitive_reference_symbol(tp: &mut TypeParser<'_>, node: Node) -> SymbolId {
    if node.is_nil() {
        return SymbolId::NIL;
    }
    if node.parent().is_some() && node.parent().kind() == SyntaxKind::ShorthandPropertyAssignment {
        let symbol = tp
            .checker
            .get_shorthand_assignment_value_symbol(node.parent());
        if symbol.is_some() {
            return symbol;
        }
    }
    tp.get_symbol_at_location(node)
}

// Go: rules/redundant_map_error.go generatorFunctionKeywordRange
pub fn generator_function_keyword_range(sf: Node, generator_function: Node) -> TextRange {
    if sf.is_nil() || generator_function.is_nil() || generator_function.asterisk_token().is_nil() {
        return get_error_range_for_node(sf, generator_function);
    }
    let start = get_token_pos_of_node(generator_function, sf, false);
    let end = generator_function.asterisk_token().end();
    if start < 0 || end < start {
        return get_error_range_for_node(sf, generator_function);
    }
    TextRange::new(start, end)
}

// Go: rules/redundant_map_error.go isHoistSensitiveValueReference
fn is_hoist_sensitive_value_reference(node: Node) -> bool {
    if node.is_nil()
        || node.kind() != SyntaxKind::Identifier
        || is_declaration_name_or_import_property_name(node)
        || is_valid_type_only_alias_use_site(node)
    {
        return false;
    }

    let parent = node.parent();
    if parent.is_nil() {
        return true;
    }

    match parent.kind() {
        SyntaxKind::PropertyAccessExpression => {
            let prop = parent;
            return prop.is_nil() || prop.name() != node;
        }
        SyntaxKind::QualifiedName => {
            let qn = parent;
            return qn.is_nil() || qn.right() != node;
        }
        SyntaxKind::PropertyAssignment => {
            let assignment = parent;
            if assignment.is_some()
                && assignment.name() == node
                && assignment.initializer().is_some()
                && assignment.initializer() != node
            {
                return false;
            }
        }
        _ => {}
    }

    true
}

// Go: rules/redundant_map_error.go unwrapTransparentExpression
pub fn unwrap_transparent_expression(node: Node) -> Node {
    let mut node = node;
    while node.is_some() {
        match node.kind() {
            SyntaxKind::ParenthesizedExpression
            | SyntaxKind::SatisfiesExpression
            | SyntaxKind::AsExpression
            | SyntaxKind::NonNullExpression
            | SyntaxKind::TypeAssertionExpression => {
                node = node.expression();
            }
            _ => return node,
        }
    }
    Node::NIL
}

// Go: rules/redundant_map_error.go nodeSourceText
fn node_source_text(sf: Node, node: Node) -> String {
    if sf.is_nil() || node.is_nil() {
        return String::new();
    }
    let text = source_file_text(sf);
    let pos = get_token_pos_of_node(node, sf, false);
    let end = node.end();
    if pos < 0 || end < pos || end as usize > text.len() {
        return String::new();
    }
    text[pos as usize..end as usize].to_string()
}
