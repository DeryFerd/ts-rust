//! Port of Effect-TS/tsgo `internal/rules/prefer_schema_over_json.go`.

use crate::effect::diag;
use crate::effect::etscore::*;
use crate::effect::rule::*;
use crate::effect::typeparser::*;
use crate::prelude::*;

/// PreferSchemaOverJson detects JSON.parse and JSON.stringify call expressions inside
/// Effect contexts (Effect.try or Effect.gen/Effect.fn) and suggests using Effect Schema instead.
/// Both Effect v3 and v4 are supported (no version gating), except the simple Effect.try(() => ...)
/// thunk form which is V3-only.
pub static PREFER_SCHEMA_OVER_JSON: Rule = Rule {
    name: "preferSchemaOverJson",
    group: "effectNative",
    description: "Suggests using Effect Schema for JSON operations instead of JSON.parse/JSON.stringify",
    default_severity: Severity::Off,
    supported_effect: &["v3", "v4"],
    codes: &[377026],
    run: run_prefer_schema_over_json,
};

fn run_prefer_schema_over_json(ctx: &mut RuleContext<'_, '_>) -> Vec<Diagnostic> {
    let mut diags = Vec::new();
    let is_v4 = ctx.tp.supported_effect_version() == EffectMajorVersion::V4;

    fn walk(
        ctx: &mut RuleContext<'_, '_>,
        diags: &mut Vec<Diagnostic>,
        is_v4: bool,
        n: Node,
    ) -> bool {
        if n.is_nil() {
            return false;
        }

        if n.kind() == SyntaxKind::CallExpression {
            if let Some(d) = check_prefer_schema_over_json(ctx, n, is_v4) {
                diags.push(d);
            }
        }

        n.for_each_child(|child| walk(ctx, diags, is_v4, child));
        false
    }

    let sf = ctx.source_file;
    walk(ctx, &mut diags, is_v4, sf);
    diags
}

/// checkPreferSchemaOverJson checks a single call expression for JSON.parse/stringify
/// inside an Effect context (Effect.try or Effect.gen/Effect.fn).
fn check_prefer_schema_over_json(
    ctx: &mut RuleContext<'_, '_>,
    node: Node,
    is_v4: bool,
) -> Option<Diagnostic> {
    let recommendation = prefer_schema_over_json_recommendation(is_v4);

    // Try each pattern in order
    let json_node = check_effect_try_simple(ctx.tp, node, is_v4);
    if json_node.is_some() {
        return Some(ctx.new_diagnostic(
            ctx.source_file,
            ctx.get_error_range(json_node),
            diag::This_code_uses_JSON_parse_or_JSON_stringify_0_effect_preferSchemaOverJson,
            Vec::new(),
            vec![recommendation.to_string()],
        ));
    }
    let json_node = check_effect_try_object(ctx.tp, node);
    if json_node.is_some() {
        return Some(ctx.new_diagnostic(
            ctx.source_file,
            ctx.get_error_range(json_node),
            diag::This_code_uses_JSON_parse_or_JSON_stringify_0_effect_preferSchemaOverJson,
            Vec::new(),
            vec![recommendation.to_string()],
        ));
    }
    let json_node = check_json_method_in_effect_gen(ctx.tp, node);
    if json_node.is_some() {
        return Some(ctx.new_diagnostic(
            ctx.source_file,
            ctx.get_error_range(json_node),
            diag::This_code_uses_JSON_parse_or_JSON_stringify_0_effect_preferSchemaOverJson,
            Vec::new(),
            vec![recommendation.to_string()],
        ));
    }
    None
}

fn prefer_schema_over_json_recommendation(is_v4: bool) -> &'static str {
    if is_v4 {
        return "Use `Schema.UnknownFromJsonString` for unknown shapes, `Schema.fromJsonString(schema)` for known ones, or `Schema.toCodecJson(schema)` when working with JSON values instead of strings.";
    }

    "Use `Schema.parseJson(Schema.Unknown)` for unknown shapes or `Schema.parseJson(schema)` for known ones."
}

/// parseJsonMethod checks if a call expression is JSON.parse or JSON.stringify.
/// Returns the call expression node if it matches, nil otherwise.
fn parse_json_method(node: Node) -> Node {
    if node.is_nil() || node.kind() != SyntaxKind::CallExpression {
        return Node::NIL;
    }

    let call = node;
    if call.expression().is_nil() {
        return Node::NIL;
    }

    let expr = call.expression();
    if expr.kind() != SyntaxKind::PropertyAccessExpression {
        return Node::NIL;
    }

    let prop = expr;
    if prop.expression().is_nil() || prop.name().is_nil() {
        return Node::NIL;
    }

    // Check that the object is an identifier "JSON"
    let object_expr = prop.expression();
    if object_expr.kind() != SyntaxKind::Identifier {
        return Node::NIL;
    }
    if get_text_of_node(object_expr) != "JSON" {
        return Node::NIL;
    }

    // Check that the method is "parse" or "stringify"
    let method_name = get_text_of_node(prop.name());
    if method_name != "parse" && method_name != "stringify" {
        return Node::NIL;
    }

    node
}

/// checkEffectTrySimple matches Effect.try(() => JSON.parse/stringify(...)) - simple thunk form.
/// This pattern is V3-only (the simple thunk form was removed in V4).
fn check_effect_try_simple(tp: &mut TypeParser<'_>, node: Node, is_v4: bool) -> Node {
    if is_v4 {
        return Node::NIL;
    }

    if node.kind() != SyntaxKind::CallExpression {
        return Node::NIL;
    }
    let call = node;

    // Check callee is Effect.try
    if !tp.is_node_reference_to_effect_module_api(call.expression(), "try") {
        return Node::NIL;
    }

    // Must have at least one argument
    if call.argument_list().is_nil() || call.arguments().is_empty() {
        return Node::NIL;
    }

    // Parse the first argument as a lazy expression (thunk=false, like the TS reference)
    let Some(lazy_expr) = parse_lazy_expression(call.arguments().get(0), LazyExpressionFlags::NONE)
    else {
        return Node::NIL;
    };

    parse_json_method(lazy_expr.expression)
}

/// checkEffectTryObject matches Effect.try({ try: () => JSON.parse/stringify(...), ... }) - object form.
fn check_effect_try_object(tp: &mut TypeParser<'_>, node: Node) -> Node {
    if node.kind() != SyntaxKind::CallExpression {
        return Node::NIL;
    }
    let call = node;

    // Check callee is Effect.try
    if !tp.is_node_reference_to_effect_module_api(call.expression(), "try") {
        return Node::NIL;
    }

    // Must have at least one argument
    if call.argument_list().is_nil() || call.arguments().is_empty() {
        return Node::NIL;
    }

    // First argument must be an object literal
    let arg = call.arguments().get(0);
    if arg.is_nil() || arg.kind() != SyntaxKind::ObjectLiteralExpression {
        return Node::NIL;
    }

    let obj_lit = arg;
    if obj_lit.property_list().is_nil() {
        return Node::NIL;
    }

    // Find the "try" property
    let mut try_initializer = Node::NIL;
    for prop in obj_lit.properties().iter() {
        if prop.is_nil() || prop.kind() != SyntaxKind::PropertyAssignment {
            continue;
        }
        let pa = prop;
        if pa.name().is_nil() {
            continue;
        }
        if pa.name().kind() == SyntaxKind::Identifier && get_text_of_node(pa.name()) == "try" {
            try_initializer = pa.initializer();
            break;
        }
    }

    if try_initializer.is_nil() {
        return Node::NIL;
    }

    // Parse the try property initializer as a lazy expression
    let Some(lazy_expr) = parse_lazy_expression(try_initializer, LazyExpressionFlags::NONE) else {
        return Node::NIL;
    };

    parse_json_method(lazy_expr.expression)
}

/// checkJsonMethodInEffectGen matches direct JSON.parse/stringify inside an Effect generator (Effect.gen or Effect.fn).
fn check_json_method_in_effect_gen(tp: &mut TypeParser<'_>, node: Node) -> Node {
    // First check if this is a JSON method call
    let json_node = parse_json_method(node);
    if json_node.is_nil() {
        return Node::NIL;
    }

    if !tp
        .get_effect_context_flags(node)
        .intersects(EffectContextFlags::IN_EFFECT)
    {
        return Node::NIL;
    }

    json_node
}
