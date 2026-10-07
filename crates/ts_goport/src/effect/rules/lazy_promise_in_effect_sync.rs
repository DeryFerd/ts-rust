//! Port of Effect-TS/tsgo `internal/rules/lazy_promise_in_effect_sync.go`.

use crate::effect::diag;
use crate::effect::etscore::*;
use crate::effect::rule::*;
use crate::effect::typeparser::*;
use crate::prelude::*;

pub static LAZY_PROMISE_IN_EFFECT_SYNC: Rule = Rule {
    name: "lazyPromiseInEffectSync",
    group: "antipattern",
    description: "Warns when Effect.sync lazily returns a Promise instead of using an async Effect constructor",
    default_severity: Severity::Warning,
    supported_effect: &["v3", "v4"],
    codes: &[377082],
    run: run_lazy_promise_in_effect_sync,
};

fn run_lazy_promise_in_effect_sync(ctx: &mut RuleContext<'_, '_>) -> Vec<Diagnostic> {
    let mut diags = Vec::new();

    fn walk(ctx: &mut RuleContext<'_, '_>, diags: &mut Vec<Diagnostic>, node: Node) -> bool {
        if node.is_nil() {
            return false;
        }

        if node.kind() == SyntaxKind::CallExpression {
            let call = node;
            if ctx
                .tp
                .is_node_reference_to_effect_module_api(call.expression(), "sync")
                && call.argument_list().is_some()
                && !call.arguments().is_empty()
            {
                let lazy_arg = call.arguments().get(0);
                let lazy_arg_type = ctx.tp.get_type_at_location(lazy_arg);
                if lazy_arg_type.is_some() && thunk_returns_promise(ctx.tp, lazy_arg_type) {
                    diags.push(ctx.new_diagnostic(
                        ctx.source_file,
                        get_error_range_for_node(ctx.source_file, lazy_arg),
                        diag::This_Effect_sync_thunk_returns_a_Promise_Use_Effect_promise_or_Effect_tryPromise_to_represent_async_work_effect_lazyPromiseInEffectSync,
                        Vec::new(),
                        Vec::new(),
                    ));
                }
            }
        }

        node.for_each_child(|child| walk(ctx, diags, child));
        false
    }

    let sf = ctx.source_file;
    walk(ctx, &mut diags, sf);
    diags
}

fn thunk_returns_promise(tp: &mut TypeParser<'_>, lazy_arg_type: TypeId) -> bool {
    for member in tp.unroll_union_members(lazy_arg_type) {
        for signature in tp
            .checker
            .get_signatures_of_type_exported(member, SignatureKind::CALL)
        {
            let return_type = tp.checker.get_return_type_of_signature_exported(signature);
            if tp.promise_type(return_type).is_some() {
                return true;
            }
        }
    }
    false
}
