//! Port of Effect-TS/tsgo `internal/rules/catch_if_tag_to_catch_tag.go`.

use crate::effect::diag;
use crate::effect::etscore::*;
use crate::effect::rule::*;
use crate::effect::typeparser::*;
use crate::prelude::*;

use super::catch_all_tag_dispatch_to_catch_tag::{
    is_bare_parameter_tag_reference, literal_tagged_union_tags,
};

pub static CATCH_IF_TAG_TO_CATCH_TAG: Rule = Rule {
    name: "catchIfTagToCatchTag",
    group: "style",
    description: "Suggests Effect.catchTag instead of Effect.catchIf with a direct _tag equality predicate",
    default_severity: Severity::Suggestion,
    supported_effect: &["v3", "v4"],
    codes: &[377131],
    run: run_catch_if_tag_to_catch_tag,
};

fn run_catch_if_tag_to_catch_tag(ctx: &mut RuleContext<'_, '_>) -> Vec<Diagnostic> {
    let matches = analyze_catch_if_tag_to_catch_tag(ctx.tp, ctx.source_file);
    let mut diagnostics = Vec::with_capacity(matches.len());
    for m in matches {
        diagnostics.push(ctx.new_diagnostic(
            m.source_file,
            m.location,
            diag::Effect_catchTag_expresses_tagged_error_recovery_more_directly_than_Effect_catchIf_with_a_tag_equality_predicate_effect_catchIfTagToCatchTag,
            Vec::new(),
            Vec::new(),
        ));
    }
    diagnostics
}

#[derive(Clone, Debug)]
pub struct CatchIfTagToCatchTagMatch {
    pub source_file: Node,
    pub location: TextRange,
    pub transformation: PipingFlowTransformation,
    pub tag: String,
    pub handler: Node,
    pub can_fix: bool,
}

pub fn analyze_catch_if_tag_to_catch_tag(
    tp: &mut TypeParser<'_>,
    sf: Node,
) -> Vec<CatchIfTagToCatchTagMatch> {
    if sf.is_nil() {
        return Vec::new();
    }

    let mut matches = Vec::new();
    let flows = tp.piping_flows(sf, true);
    for flow in flows.iter() {
        for transformation in &flow.transformations {
            if transformation.callee.is_nil()
                || !tp.is_node_reference_to_effect_module_api(transformation.callee, "catchIf")
                || transformation.args.len() != 2
            {
                continue;
            }
            let (tag, ok) = catch_if_tag_predicate(tp, transformation.args[0]);
            if !ok {
                continue;
            }
            matches.push(CatchIfTagToCatchTagMatch {
                source_file: sf,
                location: get_error_range_for_node(sf, transformation.callee),
                transformation: transformation.clone(),
                tag,
                handler: transformation.args[1],
                can_fix: true,
            });
        }
    }
    matches
}

fn catch_if_tag_predicate(tp: &mut TypeParser<'_>, predicate_node: Node) -> (String, bool) {
    let Some(lazy) = parse_lazy_expression(predicate_node, LazyExpressionFlags::NONE) else {
        return (String::new(), false);
    };
    if lazy.params.len() != 1 {
        return (String::new(), false);
    }
    let parameter = lazy.params[0];
    if parameter.is_nil()
        || parameter.name().is_nil()
        || parameter.name().kind() != SyntaxKind::Identifier
    {
        return (String::new(), false);
    }
    let parameter_symbol = tp.get_symbol_at_location(parameter.name());
    if parameter_symbol.is_nil() || tp.checker.is_symbol_assigned(parameter_symbol) {
        return (String::new(), false);
    }

    let (tag_subject, tag_value) = parse_tag_match(lazy.expression);
    if tag_subject.is_nil()
        || tag_value.is_nil()
        || !is_string_literal(tag_value)
        || !is_bare_parameter_tag_reference(tp, tag_subject, parameter_symbol)
    {
        return (String::new(), false);
    }
    let tag = tag_value.text().to_string();
    let (tags, ok) = literal_tagged_union_tags(tp, parameter.name());
    if !ok {
        return (String::new(), false);
    }
    let ok = tags.contains(&tag);
    (tag, ok)
}
