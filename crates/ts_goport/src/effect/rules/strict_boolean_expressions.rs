//! Port of Effect-TS/tsgo `internal/rules/strict_boolean_expressions.go`.

use crate::effect::diag;
use crate::effect::etscore::*;
use crate::effect::rule::*;
use crate::effect::typeparser::*;
use crate::prelude::*;
use std::collections::VecDeque;

/// StrictBooleanExpressions enforces that expressions in conditional positions
/// are strictly boolean-typed, reporting non-boolean types as diagnostics.
// Go: rules/strict_boolean_expressions.go StrictBooleanExpressions
pub static STRICT_BOOLEAN_EXPRESSIONS: Rule = Rule {
    name: "strictBooleanExpressions",
    group: "style",
    description: "Enforces boolean types in conditional expressions for type safety",
    default_severity: Severity::Off,
    supported_effect: &["v3", "v4"],
    codes: &[377029],
    run: run_strict_boolean_expressions,
};

fn run_strict_boolean_expressions(ctx: &mut RuleContext<'_, '_>) -> Vec<Diagnostic> {
    let mut diags = Vec::new();
    let mut condition_checks: FxHashMap<Node, bool> = FxHashMap::default();
    let is_condition_check =
        |checks: &FxHashMap<Node, bool>, n: Node| checks.get(&n).copied().unwrap_or(false);

    // Breadth-first traversal matching the reference implementation
    let mut node_to_visit: VecDeque<Node> = VecDeque::new();
    ctx.source_file.for_each_child(|child| {
        node_to_visit.push_back(child);
        false
    });

    while let Some(node) = node_to_visit.pop_front() {
        // Enqueue children
        node.for_each_child(|child| {
            node_to_visit.push_back(child);
            false
        });

        let mut nodes_to_check: Vec<Node> = Vec::new();

        match node.kind() {
            SyntaxKind::IfStatement => {
                condition_checks.insert(node, true);
                nodes_to_check.push(node.expression());
            }

            SyntaxKind::WhileStatement => {
                condition_checks.insert(node, true);
                nodes_to_check.push(node.expression());
            }

            SyntaxKind::ConditionalExpression => {
                condition_checks.insert(node, true);
                nodes_to_check.push(node.condition());
            }

            SyntaxKind::PrefixUnaryExpression => {
                let prefix = node;
                if prefix.operator() == SyntaxKind::ExclamationToken {
                    condition_checks.insert(node, true);
                    nodes_to_check.push(prefix.operand());
                }
            }

            SyntaxKind::BinaryExpression => {
                let bin_expr = node;
                let op_kind = bin_expr.operator_token().kind();
                if op_kind == SyntaxKind::BarBarToken
                    || op_kind == SyntaxKind::AmpersandAmpersandToken
                {
                    if is_condition_check(&condition_checks, node.parent()) {
                        condition_checks.insert(node, true);
                    }
                    nodes_to_check.push(bin_expr.left());
                    nodes_to_check.push(bin_expr.right());
                }
            }
            _ => {}
        }

        for node_to_check in nodes_to_check {
            if node_to_check.is_nil() {
                continue;
            }
            if !is_condition_check(&condition_checks, node_to_check.parent()) {
                continue;
            }

            let node_type = ctx.tp.get_type_at_location(node_to_check);
            if node_type.is_nil() {
                continue;
            }

            let constrained_type = ctx
                .tp
                .checker
                .get_base_constraint_of_type_exported(node_type);
            let mut types_to_check: Vec<TypeId> = Vec::new();
            if constrained_type.is_some() {
                types_to_check.push(constrained_type);
            } else {
                types_to_check.push(node_type);
            }
            let mut seen_type_names: FxHashSet<String> = FxHashSet::default();

            while let Some(t) = types_to_check.pop() {
                let flags = ctx.tp.checker.ty(t).flags;

                // Unroll union types
                if flags.intersects(TypeFlags::UNION) {
                    types_to_check.extend(ctx.tp.unroll_union_members(t));
                    continue;
                }

                // Skip boolean and never types
                if flags.intersects(TypeFlags::BOOLEAN) {
                    continue;
                }
                if flags.intersects(TypeFlags::BOOLEAN_LITERAL) {
                    continue;
                }
                if flags.intersects(TypeFlags::NEVER) {
                    continue;
                }

                let type_name = ctx.tp.checker.type_to_string_exported(t);
                if seen_type_names.contains(&type_name) {
                    continue;
                }
                seen_type_names.insert(type_name.clone());

                // Report the error
                let sf = ctx.source_file;
                diags.push(ctx.new_diagnostic(
                    sf,
                    ctx.get_error_range(node_to_check),
                    diag::Unexpected_0_type_in_condition_expected_strictly_a_boolean_instead_effect_strictBooleanExpressions,
                    Vec::new(),
                    vec![type_name],
                ));
            }
        }
    }

    diags
}
