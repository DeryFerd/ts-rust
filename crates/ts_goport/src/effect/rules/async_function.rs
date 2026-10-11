//! Port of Effect-TS/tsgo `internal/rules/async_function.go`.

use crate::effect::diag;
use crate::effect::etscore::*;
use crate::effect::rule::*;
use crate::effect::typeparser::*;
use crate::prelude::*;

// Go: rules/async_function.go AsyncFunction
pub static ASYNC_FUNCTION: Rule = Rule {
    name: "asyncFunction",
    group: "effectNative",
    description: "Warns when declaring async functions and suggests using Effect values and Effect.gen for async control flow",
    default_severity: Severity::Off,
    supported_effect: &["v3", "v4"],
    codes: &[377081],
    run: run_async_function,
};

fn run_async_function(ctx: &mut RuleContext<'_, '_>) -> Vec<Diagnostic> {
    let mut diags = Vec::new();

    // PORT: the body of Go's recursive `walk` closure, for one node.
    fn visit(ctx: &mut RuleContext<'_, '_>, diags: &mut Vec<Diagnostic>, node: Node) {
        match node.kind() {
            SyntaxKind::FunctionDeclaration
            | SyntaxKind::FunctionExpression
            | SyntaxKind::ArrowFunction
            | SyntaxKind::MethodDeclaration => {
                if get_combined_modifier_flags(node).intersects(ModifierFlags::ASYNC) {
                    diags.push(ctx.new_diagnostic(
                        ctx.source_file,
                        ctx.get_error_range(node),
                        diag::This_code_declares_an_async_function_consider_representing_this_async_control_flow_with_Effect_values_and_Effect_gen_effect_asyncFunction,
                        Vec::new(),
                        Vec::new(),
                    ));
                }
            }
            _ => {}
        }
    }

    let sf = ctx.source_file;
    // PERF: Go walks the tree; the node order has the same nodes in the same
    // order (effperf4).
    for &n in ctx.tp.node_order(sf).nodes() {
        visit(ctx, &mut diags, n);
    }
    diags
}
