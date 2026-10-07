//! Port of Effect-TS/tsgo `internal/rules/multiple_catch_tag.go`.

use crate::effect::diag;
use crate::effect::etscore::*;
use crate::effect::rule::*;
use crate::effect::typeparser::*;
use crate::prelude::*;

pub static MULTIPLE_CATCH_TAG: Rule = Rule {
    name: "multipleCatchTag",
    group: "style",
    description: "Suggests collapsing consecutive Effect.catchTag transformations into a single Effect.catchTags call when semantics stay equivalent",
    default_severity: Severity::Suggestion,
    supported_effect: &["v4"],
    codes: &[377092],
    run: run_multiple_catch_tag,
};

fn run_multiple_catch_tag(ctx: &mut RuleContext<'_, '_>) -> Vec<Diagnostic> {
    let matches = analyze_multiple_catch_tag(ctx.tp, ctx.source_file);
    let mut diags = Vec::with_capacity(matches.len());
    for m in &matches {
        diags.push(ctx.new_diagnostic(
            m.source_file,
            m.location,
            diag::These_0_consecutive_catchTag_transformations_can_be_collapsed_into_a_single_catchTags_call_effect_multipleCatchTag,
            multiple_catch_tag_related_information(ctx, m),
            vec![m.catch_nodes.len().to_string()],
        ));
    }
    diags
}

#[derive(Clone, Debug)]
pub struct MultipleCatchTagMatch {
    pub source_file: Node,
    pub location: TextRange,
    pub node: Node,
    pub catch_nodes: Vec<Node>,
}

// PORT: Go keeps a pointer into the flow's transformations; the port keeps
// a copy of the transformation.
#[derive(Clone, Debug)]
struct MultipleCatchTagCandidate {
    transformation: Option<PipingFlowTransformation>,
    handled_tag_type: TypeId,
    introduced_tags: Vec<TypeId>,
}

pub fn analyze_multiple_catch_tag(tp: &mut TypeParser<'_>, sf: Node) -> Vec<MultipleCatchTagMatch> {
    if sf.is_nil() {
        return Vec::new();
    }

    fn flush(
        sf: Node,
        matches: &mut Vec<MultipleCatchTagMatch>,
        chain: &mut Vec<MultipleCatchTagCandidate>,
        introduced_tags: &mut Vec<TypeId>,
    ) {
        if chain.len() >= 2 {
            let callee = chain[0]
                .transformation
                .as_ref()
                .map_or(Node::NIL, |t| t.callee);
            matches.push(MultipleCatchTagMatch {
                source_file: sf,
                location: get_error_range_for_node(sf, callee),
                node: callee,
                catch_nodes: collect_multiple_catch_tag_nodes(chain),
            });
        }
        chain.clear();
        introduced_tags.clear();
    }

    let mut matches = Vec::new();
    let flows = tp.piping_flows(sf, true);
    for flow in flows.iter() {
        let mut chain: Vec<MultipleCatchTagCandidate> = Vec::new();
        let mut introduced_tags: Vec<TypeId> = Vec::new();

        for transformation in &flow.transformations {
            if !tp.is_node_reference_to_effect_package_export(transformation.callee, "catchTag") {
                flush(sf, &mut matches, &mut chain, &mut introduced_tags);
                continue;
            }

            let Some(candidate) = analyze_multiple_catch_tag_candidate(tp, Some(transformation))
            else {
                flush(sf, &mut matches, &mut chain, &mut introduced_tags);
                continue;
            };

            if overlaps_any_tag_type(tp.checker, candidate.handled_tag_type, &introduced_tags) {
                flush(sf, &mut matches, &mut chain, &mut introduced_tags);
            }

            introduced_tags.extend(candidate.introduced_tags.iter().copied());
            chain.push(candidate);
        }

        flush(sf, &mut matches, &mut chain, &mut introduced_tags);
    }

    matches
}

fn analyze_multiple_catch_tag_candidate(
    tp: &mut TypeParser<'_>,
    transformation: Option<&PipingFlowTransformation>,
) -> Option<MultipleCatchTagCandidate> {
    let transformation = transformation?;
    if transformation.callee.is_nil() || transformation.args.len() != 2 {
        return None;
    }

    let tag_arg = super::redundant_map_error::unwrap_transparent_expression(transformation.args[0]);
    if tag_arg.is_nil() || !is_string_literal(tag_arg) {
        return None;
    }

    let handled_tag_type = tp.get_type_at_location(tag_arg);
    if handled_tag_type.is_nil() {
        return None;
    }

    let handler_type = tp.get_type_at_location(transformation.args[1]);
    if handler_type.is_nil() {
        return None;
    }

    let signatures = tp
        .checker
        .get_signatures_of_type_exported(handler_type, SignatureKind::CALL);
    if signatures.len() != 1 {
        return None;
    }

    let return_type = tp
        .checker
        .get_return_type_of_signature_exported(signatures[0]);
    if return_type.is_nil() {
        return None;
    }

    let error_channel = catch_tag_return_error_channel(tp, return_type);
    if error_channel.is_nil() {
        return None;
    }

    Some(MultipleCatchTagCandidate {
        transformation: Some(transformation.clone()),
        handled_tag_type,
        introduced_tags: collect_error_tag_types(tp, error_channel),
    })
}

fn catch_tag_return_error_channel(tp: &mut TypeParser<'_>, return_type: TypeId) -> TypeId {
    if return_type.is_nil() {
        return TypeId::NIL;
    }
    if let Some(effect_type) = tp.effect_type(return_type) {
        return effect_type.e;
    }
    if let Some(stream_type) = tp.stream_type(return_type) {
        return stream_type.e;
    }
    TypeId::NIL
}

fn collect_error_tag_types(tp: &mut TypeParser<'_>, error_type: TypeId) -> Vec<TypeId> {
    let mut tags = Vec::new();
    if error_type.is_nil() {
        return tags;
    }

    for member in tp.unroll_union_members(error_type) {
        if member.is_nil() || tp.checker.ty(member).flags.intersects(TypeFlags::NEVER) {
            continue;
        }

        let mut tag_type = tp
            .checker
            .get_type_of_property_of_type_exported(member, "_tag");
        if tag_type.is_nil() {
            tag_type = tp.get_type_of_property_by_name(member, "_tag");
        }
        if tag_type.is_nil() {
            continue;
        }
        tags.push(tag_type);
    }

    tags
}

fn overlaps_any_tag_type(c: &mut Checker, current: TypeId, previous: &[TypeId]) -> bool {
    if current.is_nil() {
        return false;
    }

    for &prior in previous {
        if prior.is_nil() {
            continue;
        }
        if c.is_type_assignable_to_exported(current, prior)
            && c.is_type_assignable_to_exported(prior, current)
        {
            return true;
        }
    }

    false
}

fn collect_multiple_catch_tag_nodes(chain: &[MultipleCatchTagCandidate]) -> Vec<Node> {
    let mut nodes = Vec::with_capacity(chain.len());
    for candidate in chain {
        let Some(transformation) = &candidate.transformation else {
            continue;
        };
        if transformation.callee.is_nil() {
            continue;
        }
        nodes.push(transformation.callee);
    }
    nodes
}

fn multiple_catch_tag_related_information(
    ctx: &RuleContext<'_, '_>,
    m: &MultipleCatchTagMatch,
) -> Vec<Diagnostic> {
    if m.catch_nodes.len() < 2 {
        return Vec::new();
    }

    let mut related = Vec::with_capacity(m.catch_nodes.len() - 1);
    for &node in &m.catch_nodes[1..] {
        if node.is_nil() {
            continue;
        }
        related.push(ctx.new_diagnostic(
            m.source_file,
            get_error_range_for_node(m.source_file, node),
            diag::This_catchTag_transformation_is_part_of_a_consecutive_chain_that_can_be_collapsed_into_catchTags_effect_multipleCatchTag,
            Vec::new(),
            Vec::new(),
        ));
    }
    related
}
