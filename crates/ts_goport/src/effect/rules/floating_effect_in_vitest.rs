//! Port of Effect-TS/tsgo `internal/rules/floating_effect_in_vitest.go`.

use crate::effect::diag;
use crate::effect::etscore::*;
use crate::effect::rule::*;
use crate::effect::typeparser::*;
use crate::prelude::*;

// Go: rules/floating_effect_in_vitest.go vitestCallbackKind
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
#[repr(u8)]
enum VitestCallbackKind {
    None = 0,
    Test = 1,
    Hook = 2,
}

// Go: rules/floating_effect_in_vitest.go vitestRoot
#[derive(Clone, Copy, Default, Debug)]
struct VitestRoot {
    name: &'static str,
    effect_vitest: bool,
}

// Go: rules/floating_effect_in_vitest.go vitestTestModifiers
static VITEST_TEST_MODIFIERS: &[&str] = &[
    "concurrent",
    "each",
    "fails",
    "for",
    "only",
    "prop",
    "runIf",
    "sequential",
    "skip",
    "skipIf",
    "todo",
];

// Go: rules/floating_effect_in_vitest.go vitestHookNames
static VITEST_HOOK_NAMES: &[&str] = &["afterAll", "afterEach", "beforeAll", "beforeEach"];

// Go: rules/floating_effect_in_vitest.go effectAwareVitestMethods
static EFFECT_AWARE_VITEST_METHODS: &[&str] = &["effect", "live", "scoped", "scopedLive"];

/// FloatingEffectInVitest detects Effects returned from Vitest callbacks that do
/// not execute returned Effect values.
// Go: rules/floating_effect_in_vitest.go FloatingEffectInVitest
pub static FLOATING_EFFECT_IN_VITEST: Rule = Rule {
    name: "floatingEffectInVitest",
    group: "correctness",
    description: "Detects Effects returned from non-Effect-aware Vitest callbacks",
    default_severity: Severity::Error,
    supported_effect: &["v3", "v4"],
    codes: &[377105],
    run: run_floating_effect_in_vitest,
};

fn run_floating_effect_in_vitest(ctx: &mut RuleContext<'_, '_>) -> Vec<Diagnostic> {
    let mut diags = Vec::new();

    fn walk(ctx: &mut RuleContext<'_, '_>, diags: &mut Vec<Diagnostic>, node: Node) -> bool {
        if node.is_nil() {
            return false;
        }

        if node.kind() == SyntaxKind::CallExpression {
            let callback = floating_effect_vitest_callback(ctx, node);
            if callback.is_some() {
                let mut range_node = callback;
                if let Some(lazy) =
                    parse_lazy_expression(callback, LazyExpressionFlags::ALLOW_ASYNC)
                    && lazy.expression.is_some()
                {
                    range_node = lazy.expression;
                }
                let sf = ctx.source_file;
                diags.push(ctx.new_diagnostic(
                    sf,
                    ctx.get_error_range(range_node),
                    diag::This_Vitest_callback_returns_an_Effect_that_Vitest_does_not_run_Use_an_Effect_aware_test_API_or_run_the_Effect_with_Effect_runPromise_effect_floatingEffectInVitest,
                    Vec::new(),
                    Vec::new(),
                ));
            }
        }

        node.for_each_child(|child| walk(ctx, diags, child));
        false
    }

    let sf = ctx.source_file;
    walk(ctx, &mut diags, sf);
    diags
}

// Go: rules/floating_effect_in_vitest.go floatingEffectVitestCallback
fn floating_effect_vitest_callback(ctx: &mut RuleContext<'_, '_>, call: Node) -> Node {
    if call.is_nil() || call.expression().is_nil() || call.argument_list().is_nil() {
        return Node::NIL;
    }

    let (root, members) = match_vitest_callee(ctx.tp, call.expression());
    let callback_kind = classify_vitest_callback(root, &members);
    if callback_kind == VitestCallbackKind::None {
        return Node::NIL;
    }

    let mut start = 1;
    if callback_kind == VitestCallbackKind::Hook {
        start = 0;
    }
    let args = call.arguments();
    for i in start..args.len() {
        let callback = args.get(i);
        if vitest_callback_returns_effect(ctx.tp, callback) {
            return callback;
        }
    }
    Node::NIL
}

// Go: rules/floating_effect_in_vitest.go matchVitestCallee
fn match_vitest_callee(tp: &mut TypeParser<'_>, mut node: Node) -> (VitestRoot, Vec<String>) {
    let mut reversed_members: Vec<String> = Vec::new();
    while node.is_some() {
        node = skip_parentheses(node);
        let root = match_vitest_root(tp, node);
        if !root.name.is_empty() {
            let members: Vec<String> = reversed_members.iter().rev().cloned().collect();
            return (root, members);
        }
        match node.kind() {
            SyntaxKind::PropertyAccessExpression => {
                let property = node;
                if property.is_nil() || property.name().is_nil() {
                    return (VitestRoot::default(), Vec::new());
                }
                reversed_members.push(property.name().text().to_string());
                node = property.expression();
            }
            SyntaxKind::CallExpression => {
                let call = node;
                if call.is_nil() {
                    return (VitestRoot::default(), Vec::new());
                }
                node = call.expression();
            }
            SyntaxKind::TaggedTemplateExpression => {
                let tagged = node;
                if tagged.is_nil() {
                    return (VitestRoot::default(), Vec::new());
                }
                node = tagged.tag();
            }
            _ => return (VitestRoot::default(), Vec::new()),
        }
    }
    (VitestRoot::default(), Vec::new())
}

// Go: rules/floating_effect_in_vitest.go matchVitestRoot
fn match_vitest_root(tp: &mut TypeParser<'_>, node: Node) -> VitestRoot {
    for name in ["it", "test"] {
        if tp.is_node_reference_to_vitest_api(node, name) {
            return VitestRoot {
                name,
                effect_vitest: false,
            };
        }
    }
    if tp.is_node_reference_to_effect_vitest_api(node, "it") {
        return VitestRoot {
            name: "it",
            effect_vitest: true,
        };
    }
    // PORT: Go ranges over a map (random order); a node references at most
    // one of these exports, so the order does not change the result.
    for &name in VITEST_HOOK_NAMES {
        if tp.is_node_reference_to_vitest_api(node, name) {
            return VitestRoot {
                name,
                effect_vitest: false,
            };
        }
    }
    VitestRoot::default()
}

// Go: rules/floating_effect_in_vitest.go classifyVitestCallback
fn classify_vitest_callback(root: VitestRoot, members: &[String]) -> VitestCallbackKind {
    if root.name.is_empty() {
        return VitestCallbackKind::None;
    }
    if VITEST_HOOK_NAMES.contains(&root.name) {
        if members.is_empty() {
            return VitestCallbackKind::Hook;
        }
        return VitestCallbackKind::None;
    }

    if root.effect_vitest
        && !members.is_empty()
        && EFFECT_AWARE_VITEST_METHODS.contains(&members[0].as_str())
    {
        return VitestCallbackKind::None;
    }
    if members.len() == 1 && VITEST_HOOK_NAMES.contains(&members[0].as_str()) {
        return VitestCallbackKind::Hook;
    }
    for member in members {
        if !VITEST_TEST_MODIFIERS.contains(&member.as_str()) {
            return VitestCallbackKind::None;
        }
    }
    VitestCallbackKind::Test
}

// Go: rules/floating_effect_in_vitest.go vitestCallbackReturnsEffect
fn vitest_callback_returns_effect(tp: &mut TypeParser<'_>, callback: Node) -> bool {
    let callback_type = tp.get_type_at_location(callback);
    if callback_type.is_nil() {
        return false;
    }
    for member in tp.unroll_union_members(callback_type) {
        let signatures = tp
            .checker
            .get_signatures_of_type_exported(member, SignatureKind::CALL);
        for signature in signatures {
            let return_type = tp.checker.get_return_type_of_signature_exported(signature);
            if vitest_return_type_contains_effect(tp, return_type, callback, 0) {
                return true;
            }
        }
    }
    if let Some(lazy) = parse_lazy_expression(callback, LazyExpressionFlags::ALLOW_ASYNC)
        && lazy.expression.is_some()
    {
        let t = tp.get_type_at_location(lazy.expression);
        return vitest_return_type_contains_effect(tp, t, lazy.expression, 0);
    }
    false
}

// Go: rules/floating_effect_in_vitest.go vitestReturnTypeContainsEffect
fn vitest_return_type_contains_effect(
    tp: &mut TypeParser<'_>,
    return_type: TypeId,
    at_location: Node,
    depth: i32,
) -> bool {
    for member in tp.unroll_union_members(return_type) {
        if tp.strict_is_effect_type(member) {
            return true;
        }
        if depth == 0 && tp.promise_type(member).is_some() {
            for type_arg in tp.checker.get_type_arguments_exported(member) {
                if vitest_return_type_contains_effect(tp, type_arg, at_location, depth + 1) {
                    return true;
                }
            }
        }
    }
    false
}
