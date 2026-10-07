//! Port of Effect-TS/tsgo `internal/rules/catch_tag_to_catch_reason.go`.

use crate::effect::diag;
use crate::effect::etscore::*;
use crate::effect::rule::*;
use crate::effect::typeparser::*;
use crate::prelude::*;

use super::redundant_map_error::unwrap_transparent_expression;
use super::result_dispatch::{is_result_dispatch_tag_reference, result_dispatch_tag_value};

pub static CATCH_TAG_TO_CATCH_REASON: Rule = Rule {
    name: "catchTagToCatchReason",
    group: "style",
    description: "Suggests Effect.catchReason or Effect.catchReasons for handlers that re-fail unmatched reason._tag branches",
    default_severity: Severity::Suggestion,
    supported_effect: &["v4"],
    codes: &[377110],
    run: run_catch_tag_to_catch_reason,
};

fn run_catch_tag_to_catch_reason(ctx: &mut RuleContext<'_, '_>) -> Vec<Diagnostic> {
    let matches = analyze_catch_tag_to_catch_reason(ctx.tp, ctx.source_file);
    let mut diagnostics = Vec::with_capacity(matches.len());
    for m in matches {
        diagnostics.push(ctx.new_diagnostic(
            m.source_file,
            m.location,
            diag::Branching_on_0_reason_tag_inside_Effect_1_hand_rolls_reason_dispatch_use_Effect_catchReason_or_Effect_catchReasons_which_re_fail_unmatched_reasons_automatically_effect_catchTagToCatchReason,
            Vec::new(),
            vec![m.parameter_name, m.catch_method_name],
        ));
    }
    diagnostics
}

#[derive(Clone, Debug, Default)]
pub struct CatchTagToCatchReasonBranch {
    pub reason_tag: String,
    pub result: Node,
    pub uses_parameter: bool,
    pub reason_parameter_name: String,
}

#[derive(Clone, Debug)]
pub struct CatchTagToCatchReasonMatch {
    pub source_file: Node,
    pub location: TextRange,
    pub transformation: PipingFlowTransformation,
    pub callee: Node,
    pub outer_tag: Node,
    pub parameter_name: String,
    pub catch_method_name: String,
    pub branches: Vec<CatchTagToCatchReasonBranch>,
    pub can_fix: bool,
}

#[derive(Clone, Debug, Default)]
pub struct CatchTagToCatchReasonHandler {
    pub parameter_name: String,
    pub branches: Vec<CatchTagToCatchReasonBranch>,
    pub can_fix: bool,
}

/// AnalyzeCatchTagToCatchReason finds canonical reason-tag dispatch inside exact
/// Effect.catchTag and Effect.catchTags transformations.
pub fn analyze_catch_tag_to_catch_reason(
    tp: &mut TypeParser<'_>,
    sf: Node,
) -> Vec<CatchTagToCatchReasonMatch> {
    if sf.is_nil() {
        return Vec::new();
    }

    let mut matches = Vec::new();
    let flows = tp.piping_flows(sf, true);
    for flow in flows.iter() {
        for transformation in &flow.transformations {
            if transformation.callee.is_nil() {
                continue;
            }
            if tp.is_node_reference_to_effect_module_api(transformation.callee, "catchTag") {
                if let Some(m) = analyze_catch_tag_transformation(tp, sf, Some(transformation)) {
                    matches.push(m);
                }
            } else if tp.is_node_reference_to_effect_module_api(transformation.callee, "catchTags")
            {
                if let Some(m) = analyze_catch_tags_transformation(tp, sf, Some(transformation)) {
                    matches.push(m);
                }
            }
        }
    }

    matches
}

// PORT: Go returns `(match, ok)`; the port returns `Some(match)` for ok.
fn analyze_catch_tag_transformation(
    tp: &mut TypeParser<'_>,
    sf: Node,
    transformation: Option<&PipingFlowTransformation>,
) -> Option<CatchTagToCatchReasonMatch> {
    let Some(transformation) = transformation else {
        return None;
    };
    if transformation.args.len() != 2 {
        return None;
    }

    let outer_tag = unwrap_transparent_expression(transformation.args[0]);
    if outer_tag.is_nil() || !is_string_literal(outer_tag) {
        return None;
    }

    let (handler, ok) = analyze_catch_tag_to_catch_reason_handler(tp, transformation.args[1]);
    if !ok {
        return None;
    }

    Some(CatchTagToCatchReasonMatch {
        source_file: sf,
        location: get_error_range_for_node(sf, transformation.callee),
        transformation: transformation.clone(),
        callee: transformation.callee,
        outer_tag,
        parameter_name: handler.parameter_name,
        catch_method_name: "catchTag".to_string(),
        branches: handler.branches,
        can_fix: handler.can_fix,
    })
}

fn analyze_catch_tags_transformation(
    tp: &mut TypeParser<'_>,
    sf: Node,
    transformation: Option<&PipingFlowTransformation>,
) -> Option<CatchTagToCatchReasonMatch> {
    let Some(transformation) = transformation else {
        return None;
    };
    if transformation.args.len() != 1 {
        return None;
    }

    let cases_node = unwrap_transparent_expression(transformation.args[0]);
    if cases_node.is_nil() || cases_node.kind() != SyntaxKind::ObjectLiteralExpression {
        return None;
    }
    let cases = cases_node;
    if cases.property_list().is_nil() {
        return None;
    }

    let mut candidate: Option<CatchTagToCatchReasonHandler> = None;
    for property_node in cases.properties().iter() {
        if property_node.is_nil() || property_node.kind() != SyntaxKind::PropertyAssignment {
            continue;
        }
        let property = property_node;
        if property.name().is_nil() || property.initializer().is_nil() {
            continue;
        }
        let (_, ok) = catch_tags_property_name(property.name());
        if !ok {
            continue;
        }

        let (handler, ok) = analyze_catch_tag_to_catch_reason_handler(tp, property.initializer());
        if !ok {
            continue;
        }
        candidate = Some(handler);
        break;
    }
    let Some(candidate) = candidate else {
        return None;
    };

    Some(CatchTagToCatchReasonMatch {
        source_file: sf,
        location: get_error_range_for_node(sf, transformation.callee),
        transformation: transformation.clone(),
        callee: transformation.callee,
        outer_tag: Node::NIL,
        parameter_name: candidate.parameter_name,
        catch_method_name: "catchTags".to_string(),
        branches: candidate.branches,
        can_fix: false,
    })
}

fn analyze_catch_tag_to_catch_reason_handler(
    tp: &mut TypeParser<'_>,
    handler_node: Node,
) -> (CatchTagToCatchReasonHandler, bool) {
    let Some(returning) = parse_returning_dispatch(handler_node) else {
        return (CatchTagToCatchReasonHandler::default(), false);
    };
    if returning.params.len() != 1 {
        return (CatchTagToCatchReasonHandler::default(), false);
    }
    let handler_node = returning.node;
    let body = returning.body;
    let parameter = returning.params[0];
    if parameter.is_nil()
        || parameter.name().is_nil()
        || parameter.name().kind() != SyntaxKind::Identifier
    {
        return (CatchTagToCatchReasonHandler::default(), false);
    }
    let parameter_symbol = tp.get_symbol_at_location(parameter.name());
    if parameter_symbol.is_nil() {
        return (CatchTagToCatchReasonHandler::default(), false);
    }
    let (reason_tags, ok) = catch_reason_literal_tags(tp, parameter.name());
    if !ok {
        return (CatchTagToCatchReasonHandler::default(), false);
    }

    let mut dispatch_refs: FxHashSet<Node> = FxHashSet::default();
    // PORT: Go's `dispatch == nil` cannot happen: the port's
    // `ParsedReturningDispatch.dispatch` is not optional.
    let dispatch = returning.dispatch.clone();
    if dispatch.branches.is_empty() || dispatch.fallback.is_nil() {
        return (CatchTagToCatchReasonHandler::default(), false);
    }
    let tag_subject = dispatch.common_tag_subject(tp);
    if tag_subject.is_nil() || !is_result_dispatch_tag_reference(tp, tag_subject, parameter_symbol)
    {
        return (CatchTagToCatchReasonHandler::default(), false);
    }

    let mut branches: Vec<CatchTagToCatchReasonBranch> =
        vec![CatchTagToCatchReasonBranch::default(); dispatch.branches.len()];
    let mut seen_tags: FxHashSet<String> = FxHashSet::default();
    for (index, branch) in dispatch.branches.iter().enumerate() {
        let (tag, tagged) = result_dispatch_tag_value(branch.condition);
        let (root, exact_reason_chain) =
            catch_reason_tag_reference(tp, branch.condition.tag_subject, parameter_symbol);
        let valid_reason_tag = reason_tags.contains(&tag);
        let duplicate_tag = seen_tags.contains(&tag);
        if !tagged
            || !exact_reason_chain
            || !valid_reason_tag
            || duplicate_tag
            || !is_effect_expression(tp, branch.result)
        {
            return (CatchTagToCatchReasonHandler::default(), false);
        }
        seen_tags.insert(tag.clone());
        dispatch_refs.insert(root);
        branches[index] = CatchTagToCatchReasonBranch {
            reason_tag: tag,
            result: branch.result,
            ..Default::default()
        };
    }

    let (fallback_param, ok) = catch_tag_re_fail_parameter(tp, dispatch.fallback, parameter_symbol);
    if !ok {
        return (CatchTagToCatchReasonHandler::default(), false);
    }

    let (branch_parameter_uses, valid_uses) = validate_catch_tag_parameter_uses(
        tp,
        body,
        parameter_symbol,
        &branches,
        fallback_param,
        &dispatch_refs,
    );
    if !valid_uses {
        return (CatchTagToCatchReasonHandler::default(), false);
    }
    for i in 0..branches.len() {
        branches[i].uses_parameter = branch_parameter_uses[i];
        if branches[i].uses_parameter {
            branches[i].reason_parameter_name =
                unique_catch_reason_parameter_name(tp.checker, branches[i].result);
        }
    }

    (
        CatchTagToCatchReasonHandler {
            parameter_name: parameter.name().text().to_string(),
            branches,
            can_fix: handler_node.kind() == SyntaxKind::ArrowFunction
                && !tp.checker.is_symbol_assigned(parameter_symbol),
        },
        true,
    )
}

fn catch_reason_literal_tags(
    tp: &mut TypeParser<'_>,
    parameter_name: Node,
) -> (FxHashSet<String>, bool) {
    let parameter_type = tp.get_type_at_location(parameter_name);
    if parameter_type.is_nil() {
        return (FxHashSet::default(), false);
    }
    let mut reason_type = tp
        .checker
        .get_type_of_property_of_type_exported(parameter_type, "reason");
    if reason_type.is_nil() {
        reason_type = tp.get_type_of_property_by_name(parameter_type, "reason");
    }
    if reason_type.is_nil() {
        return (FxHashSet::default(), false);
    }
    if !tp
        .checker
        .ty(reason_type)
        .flags()
        .intersects(TypeFlags::UNION)
    {
        return (FxHashSet::default(), false);
    }

    let mut tags: FxHashSet<String> = FxHashSet::default();
    for member in tp.unroll_union_members(reason_type) {
        if member.is_nil() {
            return (FxHashSet::default(), false);
        }
        let mut tag_type = tp
            .checker
            .get_type_of_property_of_type_exported(member, "_tag");
        if tag_type.is_nil() {
            tag_type = tp.get_type_of_property_by_name(member, "_tag");
        }
        if tag_type.is_nil()
            || !tp
                .checker
                .ty(tag_type)
                .flags()
                .intersects(TypeFlags::STRING_LITERAL)
        {
            return (FxHashSet::default(), false);
        }
        let Some(LiteralValue::String(tag)) = tp.checker.ty(tag_type).as_literal_type().value()
        else {
            return (FxHashSet::default(), false);
        };
        tags.insert(tag.clone());
    }
    let ok = !tags.is_empty();
    (tags, ok)
}

fn catch_reason_tag_reference(
    tp: &mut TypeParser<'_>,
    node: Node,
    parameter_symbol: SymbolId,
) -> (Node, bool) {
    let node = unwrap_transparent_expression(node);
    if node.is_nil() || node.kind() != SyntaxKind::PropertyAccessExpression {
        return (Node::NIL, false);
    }
    let reason_access = node;
    if reason_access.expression().is_nil()
        || reason_access.name().is_nil()
        || reason_access.name().text() != "reason"
    {
        return (Node::NIL, false);
    }
    let root = unwrap_transparent_expression(reason_access.expression());
    if root.is_nil()
        || root.kind() != SyntaxKind::Identifier
        || !same_catch_reason_symbol(tp, root, parameter_symbol)
    {
        return (Node::NIL, false);
    }
    (root, true)
}

pub fn catch_tag_re_fail_parameter(
    tp: &mut TypeParser<'_>,
    expression: Node,
    parameter_symbol: SymbolId,
) -> (Node, bool) {
    let expression = unwrap_transparent_expression(expression);
    if expression.is_nil() {
        return (Node::NIL, false);
    }
    if expression.kind() == SyntaxKind::CallExpression {
        let call = expression;
        if call.expression().is_some()
            && call.argument_list().is_some()
            && call.arguments().len() == 1
            && tp.is_node_reference_to_effect_module_api(call.expression(), "fail")
        {
            let argument = unwrap_transparent_expression(call.arguments().get(0));
            if argument.is_some()
                && argument.kind() == SyntaxKind::Identifier
                && same_catch_reason_symbol(tp, argument, parameter_symbol)
            {
                return (argument, true);
            }
        }
    }
    (Node::NIL, false)
}

fn validate_catch_tag_parameter_uses(
    tp: &mut TypeParser<'_>,
    body: Node,
    parameter_symbol: SymbolId,
    branches: &[CatchTagToCatchReasonBranch],
    fallback_param: Node,
    dispatch_refs: &FxHashSet<Node>,
) -> (Vec<bool>, bool) {
    let mut allowed: FxHashSet<Node> = FxHashSet::default();
    for node in dispatch_refs {
        allowed.insert(*node);
    }
    if fallback_param.is_some() {
        allowed.insert(fallback_param);
    }

    let mut branch_uses = vec![false; branches.len()];
    let mut valid = true;

    fn walk_body(
        tp: &mut TypeParser<'_>,
        node: Node,
        parameter_symbol: SymbolId,
        branches: &[CatchTagToCatchReasonBranch],
        allowed: &FxHashSet<Node>,
        branch_uses: &mut [bool],
        valid: &mut bool,
    ) -> bool {
        if node.is_nil() || !*valid {
            return true;
        }
        if node.kind() == SyntaxKind::Identifier
            && same_catch_reason_symbol(tp, node, parameter_symbol)
        {
            if allowed.contains(&node) {
                return false;
            }
            let branch_index = catch_reason_recovery_branch_index(node, branches);
            if branch_index >= 0 {
                branch_uses[branch_index as usize] = true;
                return false;
            }
            *valid = false;
            return true;
        }
        node.for_each_child(|child| {
            walk_body(
                tp,
                child,
                parameter_symbol,
                branches,
                allowed,
                branch_uses,
                valid,
            )
        });
        false
    }

    walk_body(
        tp,
        body,
        parameter_symbol,
        branches,
        &allowed,
        &mut branch_uses,
        &mut valid,
    );
    (branch_uses, valid)
}

fn catch_reason_recovery_branch_index(node: Node, branches: &[CatchTagToCatchReasonBranch]) -> i32 {
    for (i, branch) in branches.iter().enumerate() {
        let expression = branch.result;
        if expression.is_some() && node.pos() >= expression.pos() && node.end() <= expression.end()
        {
            return i as i32;
        }
    }
    -1
}

fn unique_catch_reason_parameter_name(c: &mut Checker, location: Node) -> String {
    let mut used: FxHashSet<String> = FxHashSet::default();
    for symbol in c.get_symbols_in_scope_exported(location, SymbolFlags::VALUE) {
        used.insert(c.symbol_to_string_exported(symbol));
    }
    let mut i: i32 = -1;
    loop {
        let mut name = "_".to_string();
        if i >= 0 {
            name = format!("_{i}");
        }
        if !used.contains(&name) {
            return name;
        }
        i += 1;
    }
}

pub fn is_effect_expression(tp: &mut TypeParser<'_>, expression: Node) -> bool {
    if expression.is_nil() {
        return false;
    }
    let t = tp.get_type_at_location(expression);
    tp.effect_type(t).is_some()
}

fn catch_tags_property_name(name: Node) -> (String, bool) {
    if name.is_nil() {
        return (String::new(), false);
    }
    match name.kind() {
        SyntaxKind::Identifier => (name.text().to_string(), true),
        SyntaxKind::StringLiteral => (name.text().to_string(), true),
        _ => (String::new(), false),
    }
}

pub fn same_catch_reason_symbol(tp: &mut TypeParser<'_>, node: Node, expected: SymbolId) -> bool {
    let actual = tp.get_symbol_at_location(node);
    actual.is_some()
        && expected.is_some()
        && tp
            .checker
            .get_symbol_if_same_reference(actual, expected)
            .is_some()
}
