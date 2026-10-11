// Go: internal/rules/new_promise.go

use crate::effect::diag;
use crate::effect::etscore::*;
use crate::effect::rule::*;
use crate::effect::typeparser::*;
use crate::prelude::*;

pub static NEW_PROMISE: Rule = Rule {
    name: "newPromise",
    group: "effectNative",
    description: "Warns when constructing promises with new Promise instead of using Effect APIs",
    default_severity: Severity::Off,
    supported_effect: &["v3", "v4"],
    codes: &[377080],
    run: run_new_promise,
};

fn run_new_promise(ctx: &mut RuleContext<'_, '_>) -> Vec<Diagnostic> {
    let promise_symbol =
        ctx.tp
            .checker
            .resolve_name_exported("Promise", Node::NIL, SymbolFlags::VALUE, false);
    if promise_symbol.is_nil() {
        return Vec::new();
    }

    fn visit(
        ctx: &mut RuleContext<'_, '_>,
        diags: &mut Vec<Diagnostic>,
        promise_symbol: SymbolId,
        node: Node,
    ) {
        if node.kind() == SyntaxKind::NewExpression {
            let new_expr = node;
            let sym = ctx.tp.get_symbol_at_location(new_expr.expression());
            if ctx.tp.resolve_to_global_symbol(sym) == promise_symbol {
                diags.push(ctx.new_diagnostic(
                    ctx.source_file,
                    get_error_range_for_node(ctx.source_file, node),
                    diag::This_code_constructs_new_Promise_prefer_Effect_APIs_such_as_Effect_async_Effect_promise_or_Effect_tryPromise_instead_of_manual_Promise_construction_effect_newPromise,
                    Vec::new(),
                    Vec::new(),
                ));
            }
        }
    }

    let mut diags = Vec::new();
    let sf = ctx.source_file;
    // PERF: Go walks the tree; the node order has the same nodes in the same
    // order (effperf4).
    for &n in ctx.tp.node_order(sf).nodes() {
        visit(ctx, &mut diags, promise_symbol, n);
    }
    diags
}
