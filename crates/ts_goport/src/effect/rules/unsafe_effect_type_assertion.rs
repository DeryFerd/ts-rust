// Go: internal/rules/unsafe_effect_type_assertion.go

use crate::effect::diag;
use crate::effect::etscore::*;
use crate::effect::rule::*;
use crate::effect::typeparser::*;
use crate::prelude::*;

pub static UNSAFE_EFFECT_TYPE_ASSERTION: Rule = Rule {
    name: "unsafeEffectTypeAssertion",
    group: "correctness",
    description: "Detects unsafe type assertions that narrow Effect, Stream, or Layer error or requirements channels",
    default_severity: Severity::Off,
    supported_effect: &["v3", "v4"],
    codes: &[377075],
    run: run_unsafe_effect_type_assertion,
};

fn run_unsafe_effect_type_assertion(ctx: &mut RuleContext<'_, '_>) -> Vec<Diagnostic> {
    let matches = analyze_unsafe_effect_type_assertion(ctx.tp, ctx.source_file);
    let mut diags = Vec::with_capacity(matches.len());
    for m in &matches {
        let related = unsafe_effect_type_assertion_related_information(ctx, m);
        diags.push(ctx.new_diagnostic(
            m.source_file,
            m.location,
            diag::This_type_assertion_unsafely_narrows_the_error_or_requirements_channels_effect_unsafeEffectTypeAssertion,
            related,
            Vec::new(),
        ));
    }
    diags
}

#[derive(Clone, Debug)]
pub struct UnsafeEffectTypeAssertionChannel {
    pub name: String,
    pub original: String,
    pub asserted: String,
}

#[derive(Clone, Debug)]
pub struct UnsafeEffectTypeAssertionMatch {
    pub source_file: Node,
    pub location: TextRange,
    pub assertion_node: Node,
    pub expression_node: Node,
    pub location_node: Node,
    pub channels: Vec<UnsafeEffectTypeAssertionChannel>,
}

// Go: rules/unsafe_effect_type_assertion.go AnalyzeUnsafeEffectTypeAssertion
pub fn analyze_unsafe_effect_type_assertion(
    tp: &mut TypeParser<'_>,
    sf: Node,
) -> Vec<UnsafeEffectTypeAssertionMatch> {
    if sf.is_nil() {
        return Vec::new();
    }

    let mut matches = Vec::new();
    fn parse_effect_stream_or_layer(tp: &mut TypeParser<'_>, t: TypeId) -> (TypeId, TypeId, bool) {
        if let Some(effect) = tp.effect_type(t) {
            return (effect.e, effect.r, true);
        }
        if let Some(stream) = tp.stream_type(t) {
            return (stream.e, stream.r, true);
        }
        if let Some(layer) = tp.layer_type(t) {
            return (layer.e, layer.r_in, true);
        }
        (TypeId::NIL, TypeId::NIL, false)
    }
    let mut nodes_to_visit: Vec<Node> = Vec::new();
    sf.for_each_child(|child| {
        nodes_to_visit.push(child);
        false
    });

    while let Some(node) = nodes_to_visit.pop() {
        node.for_each_child(|child| {
            nodes_to_visit.push(child);
            false
        });

        if node.kind() != SyntaxKind::AsExpression
            && node.kind() != SyntaxKind::TypeAssertionExpression
        {
            continue;
        }

        let expr = node.expression();
        if expr.is_nil() {
            continue;
        }

        let original_type = tp.get_type_at_location(expr);
        let asserted_type = tp.get_type_at_location(node);
        if original_type.is_nil() || asserted_type.is_nil() {
            continue;
        }

        let (original_e, original_r, ok) = parse_effect_stream_or_layer(tp, original_type);
        if !ok {
            continue;
        }

        let (asserted_e, asserted_r, ok) = parse_effect_stream_or_layer(tp, asserted_type);
        if !ok {
            continue;
        }

        let c = &mut *tp.checker;
        let mut channels = Vec::with_capacity(2);
        if original_e.is_some()
            && asserted_e.is_some()
            && !is_any_type(c, original_e)
            && !c.is_type_assignable_to(original_e, asserted_e)
        {
            channels.push(UnsafeEffectTypeAssertionChannel {
                name: "error".to_string(),
                original: c.type_to_string_exported(original_e),
                asserted: c.type_to_string_exported(asserted_e),
            });
        }
        if original_r.is_some()
            && asserted_r.is_some()
            && !is_any_type(c, original_r)
            && !c.is_type_assignable_to(original_r, asserted_r)
        {
            channels.push(UnsafeEffectTypeAssertionChannel {
                name: "requirements".to_string(),
                original: c.type_to_string_exported(original_r),
                asserted: c.type_to_string_exported(asserted_r),
            });
        }
        if channels.is_empty() {
            continue;
        }

        let mut location_node = node;
        let type_node = node.type_();
        if type_node.is_some() {
            location_node = type_node;
        }

        matches.push(UnsafeEffectTypeAssertionMatch {
            source_file: sf,
            location: get_error_range_for_node(sf, node),
            assertion_node: node,
            expression_node: expr,
            location_node,
            channels,
        });
    }

    matches
}

// Go: rules/unsafe_effect_type_assertion.go isAnyType
// PORT: takes the checker to read the type flags.
fn is_any_type(c: &Checker, t: TypeId) -> bool {
    t.is_some() && c.ty(t).flags.intersects(TypeFlags::ANY)
}

// Go: rules/unsafe_effect_type_assertion.go unsafeEffectTypeAssertionRelatedInformation
fn unsafe_effect_type_assertion_related_information(
    ctx: &RuleContext<'_, '_>,
    m: &UnsafeEffectTypeAssertionMatch,
) -> Vec<Diagnostic> {
    if m.channels.is_empty() {
        return Vec::new();
    }

    let mut location_node = m.location_node;
    if location_node.is_nil() {
        location_node = m.assertion_node;
    }

    let mut related = Vec::with_capacity(m.channels.len());
    for channel in &m.channels {
        related.push(ctx.new_diagnostic(
            m.source_file,
            get_error_range_for_node(m.source_file, location_node),
            diag::The_0_channel_is_narrowed_from_1_to_2_effect_unsafeEffectTypeAssertion,
            Vec::new(),
            vec![
                channel.name.clone(),
                channel.original.clone(),
                channel.asserted.clone(),
            ],
        ));
    }
    related
}
