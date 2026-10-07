//! Port of Effect-TS/tsgo `internal/rules/catch_all_tag_dispatch_to_catch_tag.go`.

use crate::effect::diag;
use crate::effect::etscore::*;
use crate::effect::rule::*;
use crate::effect::typeparser::*;
use crate::prelude::*;

use super::catch_conditional_refail_to_catch_if::conditional_refail_node_contains_parameter;
use super::catch_tag_to_catch_reason::{
    catch_tag_re_fail_parameter, is_effect_expression, same_catch_reason_symbol,
};
use super::redundant_map_error::unwrap_transparent_expression;
use super::result_dispatch::result_dispatch_tag_value;

pub static CATCH_ALL_TAG_DISPATCH_TO_CATCH_TAG: Rule = Rule {
    name: "catchAllTagDispatchToCatchTag",
    group: "style",
    description: "Suggests Effect.catchTag or Effect.catchTags for catch-all handlers that re-fail unmatched tagged errors",
    default_severity: Severity::Suggestion,
    supported_effect: &["v3", "v4"],
    codes: &[377122],
    run: run_catch_all_tag_dispatch_to_catch_tag,
};

fn run_catch_all_tag_dispatch_to_catch_tag(ctx: &mut RuleContext<'_, '_>) -> Vec<Diagnostic> {
    let matches = analyze_catch_all_tag_dispatch_to_catch_tag(ctx.tp, ctx.source_file);
    let mut diagnostics = Vec::with_capacity(matches.len());
    for m in matches {
        diagnostics.push(ctx.new_diagnostic(
            m.source_file,
            m.location,
            diag::Branching_on_0_tag_inside_Effect_1_hand_rolls_tagged_error_dispatch_use_Effect_catchTag_or_Effect_catchTags_which_re_fail_unmatched_errors_automatically_effect_catchAllTagDispatchToCatchTag,
            Vec::new(),
            vec![m.parameter_name, m.catch_method_name],
        ));
    }
    diagnostics
}

#[derive(Clone, Debug, Default)]
pub struct CatchAllTagDispatchBranch {
    pub tag: String,
    pub result: Node,
    pub uses_parameter: bool,
}

#[derive(Clone, Debug)]
pub struct CatchAllTagDispatchMatch {
    pub source_file: Node,
    pub location: TextRange,
    pub transformation: PipingFlowTransformation,
    pub callee: Node,
    pub parameter_name: String,
    pub catch_method_name: String,
    pub branches: Vec<CatchAllTagDispatchBranch>,
    pub can_fix: bool,
}

pub fn analyze_catch_all_tag_dispatch_to_catch_tag(
    tp: &mut TypeParser<'_>,
    sf: Node,
) -> Vec<CatchAllTagDispatchMatch> {
    if sf.is_nil() {
        return Vec::new();
    }

    let mut matches = Vec::new();
    let flows = tp.piping_flows(sf, true);
    for flow in flows.iter() {
        for transformation in &flow.transformations {
            let (catch_method, ok) = catch_all_tag_dispatch_method(tp, transformation.callee);
            if !ok || transformation.args.len() != 1 {
                continue;
            }
            let (parameter_name, branches, can_fix, ok) =
                analyze_catch_all_tag_dispatch_handler(tp, transformation.args[0]);
            if !ok {
                continue;
            }
            matches.push(CatchAllTagDispatchMatch {
                source_file: sf,
                location: get_error_range_for_node(sf, transformation.callee),
                transformation: transformation.clone(),
                callee: transformation.callee,
                parameter_name,
                catch_method_name: catch_method,
                branches,
                can_fix,
            });
        }
    }
    matches
}

fn catch_all_tag_dispatch_method(tp: &mut TypeParser<'_>, callee: Node) -> (String, bool) {
    if tp.is_node_reference_to_effect_module_api(callee, "catch") {
        return ("catch".to_string(), true);
    }
    if tp.is_node_reference_to_effect_module_api(callee, "catchAll") {
        return ("catchAll".to_string(), true);
    }
    (String::new(), false)
}

fn analyze_catch_all_tag_dispatch_handler(
    tp: &mut TypeParser<'_>,
    handler_node: Node,
) -> (String, Vec<CatchAllTagDispatchBranch>, bool, bool) {
    // PORT: Go's `returning.Dispatch == nil` cannot happen: the port's
    // `ParsedReturningDispatch.dispatch` is not optional.
    let Some(returning) = parse_returning_dispatch(handler_node) else {
        return (String::new(), Vec::new(), false, false);
    };
    if returning.params.len() != 1
        || returning.dispatch.branches.is_empty()
        || returning.dispatch.fallback.is_nil()
    {
        return (String::new(), Vec::new(), false, false);
    }
    let parameter = returning.params[0];
    if parameter.is_nil()
        || parameter.name().is_nil()
        || parameter.name().kind() != SyntaxKind::Identifier
    {
        return (String::new(), Vec::new(), false, false);
    }
    let parameter_symbol = tp.get_symbol_at_location(parameter.name());
    if parameter_symbol.is_nil() {
        return (String::new(), Vec::new(), false, false);
    }
    let (tags, ok) = literal_tagged_union_tags(tp, parameter.name());
    if !ok {
        return (String::new(), Vec::new(), false, false);
    }
    let tag_subject = returning.dispatch.common_tag_subject(tp);
    if tag_subject.is_nil() || !is_bare_parameter_tag_reference(tp, tag_subject, parameter_symbol) {
        return (String::new(), Vec::new(), false, false);
    }

    let mut branches: Vec<CatchAllTagDispatchBranch> =
        vec![CatchAllTagDispatchBranch::default(); returning.dispatch.branches.len()];
    let mut seen: FxHashSet<String> = FxHashSet::default();
    for (i, branch) in returning.dispatch.branches.iter().enumerate() {
        let (tag, tagged) = result_dispatch_tag_value(branch.condition);
        let valid_tag = tags.contains(&tag);
        let duplicate = seen.contains(&tag);
        if !tagged || !valid_tag || duplicate || !is_effect_expression(tp, branch.result) {
            return (String::new(), Vec::new(), false, false);
        }
        seen.insert(tag.clone());
        branches[i] = CatchAllTagDispatchBranch {
            tag,
            result: branch.result,
            uses_parameter: conditional_refail_node_contains_parameter(
                tp,
                branch.result,
                parameter_symbol,
            ),
        };
    }
    let (_, ok) = catch_tag_re_fail_parameter(tp, returning.dispatch.fallback, parameter_symbol);
    if !ok {
        return (String::new(), Vec::new(), false, false);
    }
    let can_fix = returning.node.kind() == SyntaxKind::ArrowFunction
        && !tp.checker.is_symbol_assigned(parameter_symbol);
    (parameter.name().text().to_string(), branches, can_fix, true)
}

pub fn literal_tagged_union_tags(tp: &mut TypeParser<'_>, node: Node) -> (FxHashSet<String>, bool) {
    let type_ = tp.get_type_at_location(node);
    if type_.is_nil() || !tp.checker.ty(type_).flags().intersects(TypeFlags::UNION) {
        return (FxHashSet::default(), false);
    }
    let mut tags: FxHashSet<String> = FxHashSet::default();
    for member in tp.unroll_union_members(type_) {
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

pub fn is_bare_parameter_tag_reference(
    tp: &mut TypeParser<'_>,
    node: Node,
    parameter_symbol: SymbolId,
) -> bool {
    let node = unwrap_transparent_expression(node);
    if node.is_nil() || node.kind() != SyntaxKind::Identifier {
        return false;
    }
    same_catch_reason_symbol(tp, node, parameter_symbol)
}
