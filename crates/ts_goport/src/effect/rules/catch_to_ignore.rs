//! Port of Effect-TS/tsgo `internal/rules/catch_to_ignore.go`.

use crate::effect::diag;
use crate::effect::etscore::*;
use crate::effect::rule::*;
use crate::effect::typeparser::*;
use crate::prelude::*;

/// CatchToIgnore suggests using Effect.ignore or Effect.ignoreCause instead of Effect.catch/catchCause + Effect.void.
// Go: rules/catch_to_ignore.go CatchToIgnore
pub static CATCH_TO_IGNORE: Rule = Rule {
    name: "catchToIgnore",
    group: "style",
    description: "Suggests using Effect.ignore or Effect.ignoreCause instead of Effect.catch/catchCause returning Effect.void",
    default_severity: Severity::Suggestion,
    supported_effect: &["v4"],
    codes: &[377099],
    run: run_catch_to_ignore,
};

fn run_catch_to_ignore(ctx: &mut RuleContext<'_, '_>) -> Vec<Diagnostic> {
    let matches = analyze_catch_to_ignore(ctx.tp, ctx.source_file);
    let mut diags = Vec::with_capacity(matches.len());
    for m in &matches {
        diags.push(ctx.new_diagnostic(
            m.source_file,
            m.location,
            diag::Effect_1_expresses_ignored_failure_more_directly_than_Effect_0_returning_Effect_void_effect_catchToIgnore,
            Vec::new(),
            args![m.catch_method_name, m.ignore_method_name],
        ));
    }
    diags
}

/// CatchToIgnoreMatch holds the AST nodes needed by both the diagnostic rule
/// and the quick-fix for the catchToIgnore pattern.
// Go: rules/catch_to_ignore.go CatchToIgnoreMatch
// PORT: Go keeps a pointer into the flow's transformations; the port keeps a copy.
#[derive(Clone)]
pub struct CatchToIgnoreMatch {
    pub source_file: Node,
    pub location: TextRange,
    pub transformation: PipingFlowTransformation,
    pub effect_module_node: Node,
    pub catch_method_name: String,
    pub ignore_method_name: String,
}

/// AnalyzeCatchToIgnore finds Effect.catch/catchCause callbacks that return Effect.void
/// where the resulting success channel is void-like, so Effect.ignore/ignoreCause is equivalent.
// Go: rules/catch_to_ignore.go AnalyzeCatchToIgnore
pub fn analyze_catch_to_ignore(tp: &mut TypeParser<'_>, sf: Node) -> Vec<CatchToIgnoreMatch> {
    if sf.is_nil() || tp.supported_effect_version() != EffectMajorVersion::V4 {
        return Vec::new();
    }

    let mut matches = Vec::new();

    let flows = tp.piping_flows(sf, true);
    for flow in flows.iter() {
        for transformation in &flow.transformations {
            let (catch_method_name, ignore_method_name, effect_module_node, ok) =
                catch_to_ignore_methods(tp, transformation.callee);
            if !ok {
                continue;
            }

            if transformation.args.is_empty() {
                continue;
            }

            let lazy = parse_lazy_expression(transformation.args[0], LazyExpressionFlags::NONE);
            let Some(lazy) = lazy else {
                continue;
            };
            if !is_effect_void_reference(tp, lazy.expression) {
                continue;
            }

            let effect = tp.strict_effect_type(transformation.out_type);
            let Some(effect) = effect else {
                continue;
            };
            if !is_void_like_effect_success(tp.checker, effect.a) {
                continue;
            }

            matches.push(CatchToIgnoreMatch {
                source_file: sf,
                location: get_error_range_for_node(sf, transformation.callee),
                transformation: transformation.clone(),
                effect_module_node,
                catch_method_name: catch_method_name.to_string(),
                ignore_method_name: ignore_method_name.to_string(),
            });
        }
    }

    matches
}

// Go: rules/catch_to_ignore.go catchToIgnoreMethods
fn catch_to_ignore_methods(
    tp: &mut TypeParser<'_>,
    callee: Node,
) -> (&'static str, &'static str, Node, bool) {
    if callee.is_nil() {
        return ("", "", Node::NIL, false);
    }
    let mut effect_module_node = Node::NIL;
    if callee.kind() == SyntaxKind::PropertyAccessExpression {
        let prop = callee;
        effect_module_node = prop.expression();
    }
    if tp.is_node_reference_to_effect_module_api(callee, "catch") {
        ("catch", "ignore", effect_module_node, true)
    } else if tp.is_node_reference_to_effect_module_api(callee, "catchCause") {
        ("catchCause", "ignoreCause", effect_module_node, true)
    } else {
        ("", "", Node::NIL, false)
    }
}

// Go: rules/catch_to_ignore.go isEffectVoidReference
fn is_effect_void_reference(tp: &mut TypeParser<'_>, node: Node) -> bool {
    if node.is_nil() {
        return false;
    }
    tp.is_node_reference_to_effect_module_api(skip_parentheses(node), "void")
}

// Go: rules/catch_to_ignore.go isVoidLikeEffectSuccess
fn is_void_like_effect_success(c: &Checker, t: TypeId) -> bool {
    if t.is_nil() {
        return false;
    }
    let flags = c.ty(t).flags;
    if flags.intersects(TypeFlags::VOID_LIKE | TypeFlags::NEVER) {
        return true;
    }
    if !flags.intersects(TypeFlags::UNION) {
        return false;
    }
    let types = c.ty(t).types();
    if types.is_empty() {
        return false;
    }
    for &member in types {
        if !is_void_like_effect_success(c, member) {
            return false;
        }
    }
    true
}
