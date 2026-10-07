//! Port of Effect-TS/tsgo `internal/rules/schema_sync_in_effect.go`.

use crate::effect::diag;
use crate::effect::etscore::*;
use crate::effect::rule::*;
use crate::effect::typeparser::*;
use crate::prelude::*;

/// syncToEffectMethodV3 maps Schema sync method names to their Effect-based V3 equivalents.
// PORT: Go `map[string]string`; the port keeps the pairs in Go source order.
// Go ranges over the map in random order; every caller matches at most one
// name, so the order does not change a result.
// Go: rules/schema_sync_in_effect.go syncToEffectMethodV3
pub static SYNC_TO_EFFECT_METHOD_V3: &[(&str, &str)] = &[
    ("decodeSync", "decode"),
    ("decodeUnknownSync", "decodeUnknown"),
    ("encodeSync", "encode"),
    ("encodeUnknownSync", "encodeUnknown"),
];

/// syncToEffectMethodV4 maps Schema sync method names to their Effect-based V4 equivalents.
// Go: rules/schema_sync_in_effect.go syncToEffectMethodV4
pub static SYNC_TO_EFFECT_METHOD_V4: &[(&str, &str)] = &[
    ("decodeSync", "decodeEffect"),
    ("decodeUnknownSync", "decodeUnknownEffect"),
    ("encodeSync", "encodeEffect"),
    ("encodeUnknownSync", "encodeUnknownEffect"),
];

/// SchemaSyncInEffect detects Schema sync methods (decodeSync, encodeSync, etc.) used inside
/// Effect generators and suggests using the Effect-based variants instead.
// Go: rules/schema_sync_in_effect.go SchemaSyncInEffect
pub static SCHEMA_SYNC_IN_EFFECT: Rule = Rule {
    name: "schemaSyncInEffect",
    group: "antipattern",
    description: "Suggests using Effect-based Schema methods instead of sync methods inside Effect generators",
    default_severity: Severity::Suggestion,
    supported_effect: &["v3", "v4"],
    codes: &[377037],
    run: run_schema_sync_in_effect,
};

fn run_schema_sync_in_effect(ctx: &mut RuleContext<'_, '_>) -> Vec<Diagnostic> {
    let version = ctx.tp.supported_effect_version();
    let sync_to_effect_method: &'static [(&'static str, &'static str)] =
        if version == EffectMajorVersion::V4 {
            SYNC_TO_EFFECT_METHOD_V4
        } else {
            SYNC_TO_EFFECT_METHOD_V3
        };

    let mut diags = Vec::new();

    fn walk(
        ctx: &mut RuleContext<'_, '_>,
        sync_to_effect_method: &'static [(&'static str, &'static str)],
        diags: &mut Vec<Diagnostic>,
        n: Node,
    ) -> bool {
        if n.is_nil() {
            return false;
        }

        if n.kind() == SyntaxKind::CallExpression
            && let Some(d) = check_schema_sync_in_effect(ctx, n, sync_to_effect_method)
        {
            diags.push(d);
        }

        n.for_each_child(|child| walk(ctx, sync_to_effect_method, diags, child));
        false
    }

    let sf = ctx.source_file;
    walk(ctx, sync_to_effect_method, &mut diags, sf);
    diags
}

/// checkSchemaSyncInEffect checks a single call expression for Schema sync methods inside an Effect generator.
// Go: rules/schema_sync_in_effect.go checkSchemaSyncInEffect
fn check_schema_sync_in_effect(
    ctx: &mut RuleContext<'_, '_>,
    node: Node,
    sync_to_effect_method: &'static [(&'static str, &'static str)],
) -> Option<Diagnostic> {
    if node.kind() != SyntaxKind::CallExpression {
        return None;
    }
    let call = node;

    let callee = call.expression();

    // Check if the callee is one of the Schema sync methods (try both ParseResult and SchemaParser modules)
    let method_name = match_schema_sync_method(ctx.tp, callee, sync_to_effect_method);
    if method_name.is_empty() {
        return None;
    }

    if !ctx
        .tp
        .get_effect_context_flags(node)
        .intersects(EffectContextFlags::IN_EFFECT)
    {
        return None;
    }

    let sf = ctx.source_file;
    let callee_text = get_source_text_of_node_from_source_file(sf, callee, false);
    let effect_method_name = sync_to_effect_method
        .iter()
        .find(|(sync_name, _)| *sync_name == method_name)
        .map_or("", |(_, effect_name)| *effect_name);

    Some(ctx.new_diagnostic(
        sf,
        ctx.get_error_range(callee),
        diag::X_0_is_used_inside_an_Effect_generator_Schema_1_preserves_the_typed_Effect_error_channel_for_this_operation_without_throwing_effect_schemaSyncInEffect,
        Vec::new(),
        vec![callee_text, effect_method_name.to_string()],
    ))
}

/// matchSchemaSyncMethod checks if the node references one of the Schema sync methods via
/// either the ParseResult module (V3) or the SchemaParser module (V4).
// Go: rules/schema_sync_in_effect.go matchSchemaSyncMethod
fn match_schema_sync_method(
    tp: &mut TypeParser<'_>,
    node: Node,
    sync_to_effect_method: &'static [(&'static str, &'static str)],
) -> &'static str {
    for &(method_name, _) in sync_to_effect_method {
        if tp.is_node_reference_to_effect_parse_result_module_api(node, method_name) {
            return method_name;
        }
        if tp.is_node_reference_to_effect_schema_parser_module_api(node, method_name) {
            return method_name;
        }
    }
    ""
}
