//! Port of Effect-TS/tsgo `internal/rules/sync_to_succeed.go`.

use crate::effect::diag;
use crate::effect::etscore::*;
use crate::effect::rule::*;
use crate::effect::typeparser::*;
use crate::prelude::*;

/// SyncToSucceed suggests using Effect.succeed when an Effect.sync thunk returns
/// a value that is already constant at Effect construction time.
// Go: rules/sync_to_succeed.go SyncToSucceed
pub static SYNC_TO_SUCCEED: Rule = Rule {
    name: "syncToSucceed",
    group: "style",
    description: "Suggests using Effect.succeed instead of Effect.sync when the thunk returns a constant value",
    default_severity: Severity::Suggestion,
    supported_effect: &["v3", "v4"],
    codes: &[377103],
    run: run_sync_to_succeed,
};

fn run_sync_to_succeed(ctx: &mut RuleContext<'_, '_>) -> Vec<Diagnostic> {
    let matches = analyze_sync_to_succeed(ctx.tp, ctx.source_file);
    let mut diags = Vec::with_capacity(matches.len());
    for m in &matches {
        diags.push(ctx.new_diagnostic(
            m.source_file,
            m.location,
            diag::Effect_succeed_expresses_this_constant_value_more_directly_than_Effect_sync_effect_syncToSucceed,
            Vec::new(),
            Vec::new(),
        ));
    }
    diags
}

/// SyncToSucceedMatch holds the nodes needed by the diagnostic and quick fix.
// Go: rules/sync_to_succeed.go SyncToSucceedMatch
#[derive(Clone, Copy)]
pub struct SyncToSucceedMatch {
    pub source_file: Node,
    pub location: TextRange,
    pub callee: Node,
    /// Replaceable property name; nil for named imports and local aliases.
    pub callee_name: Node,
    pub thunk: Node,
    pub constant_value: Node,
}

/// AnalyzeSyncToSucceed finds Effect.sync thunks whose result is already stable
/// when the Effect is constructed.
// Go: rules/sync_to_succeed.go AnalyzeSyncToSucceed
pub fn analyze_sync_to_succeed(tp: &mut TypeParser<'_>, sf: Node) -> Vec<SyncToSucceedMatch> {
    let mut matches = Vec::new();

    // PORT: Go's recursive `walk` closure.
    fn walk(
        tp: &mut TypeParser<'_>,
        sf: Node,
        matches: &mut Vec<SyncToSucceedMatch>,
        node: Node,
    ) -> bool {
        if node.is_nil() {
            return false;
        }

        if node.kind() == SyntaxKind::CallExpression {
            let call = node;
            if call.expression().is_some()
                && tp.is_node_reference_to_effect_module_api(call.expression(), "sync")
                && call.argument_list().is_some()
                && call.arguments().len() == 1
            {
                let lazy =
                    parse_lazy_expression(call.arguments().get(0), LazyExpressionFlags::THUNK);
                if let Some(lazy) = lazy
                    && tp.is_expression_value_stable_at_location(lazy.expression, node)
                {
                    let mut callee_name = Node::NIL;
                    if call.expression().kind() == SyntaxKind::PropertyAccessExpression {
                        callee_name = call.expression().name();
                    }
                    matches.push(SyncToSucceedMatch {
                        source_file: sf,
                        location: get_error_range_for_node(sf, call.expression()),
                        callee: call.expression(),
                        callee_name,
                        thunk: lazy.node,
                        constant_value: lazy.expression,
                    });
                }
            }
        }

        node.for_each_child(|child| walk(tp, sf, matches, child));
        false
    }

    walk(tp, sf, &mut matches, sf);
    matches
}
