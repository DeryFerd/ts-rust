//! Port of Effect-TS/tsgo `internal/rules/schema_opaque_instance_member.go`.

use crate::effect::diag;
use crate::effect::etscore::*;
use crate::effect::rule::*;
use crate::effect::typeparser::*;
use crate::prelude::*;

// Go: rules/schema_opaque_instance_member.go SchemaOpaqueInstanceMember
pub static SCHEMA_OPAQUE_INSTANCE_MEMBER: Rule = Rule {
    name: "schemaOpaqueInstanceMember",
    group: "correctness",
    description: "Disallows instance members in classes extending Schema.Opaque",
    default_severity: Severity::Error,
    supported_effect: &["v4"],
    codes: &[377102],
    run: run_schema_opaque_instance_member,
};

fn run_schema_opaque_instance_member(ctx: &mut RuleContext<'_, '_>) -> Vec<Diagnostic> {
    let mut diagnostics = Vec::new();

    fn visit(ctx: &mut RuleContext<'_, '_>, diagnostics: &mut Vec<Diagnostic>, node: Node) {
        if (node.kind() == SyntaxKind::ClassDeclaration
            || node.kind() == SyntaxKind::ClassExpression)
            && ctx.tp.extends_schema_opaque(node).is_some()
        {
            for member in node.members().iter() {
                if is_schema_opaque_instance_member(member) {
                    let sf = ctx.source_file;
                    diagnostics.push(ctx.new_diagnostic(
                        sf,
                        ctx.get_error_range(member),
                        diag::Classes_extending_Schema_Opaque_must_not_declare_instance_members_effect_schemaOpaqueInstanceMember,
                        Vec::new(),
                        Vec::new(),
                    ));
                }
            }
        }
    }

    let sf = ctx.source_file;
    // PERF: Go walks the tree; the node order has the same nodes in the same
    // order (effperf4).
    for &n in ctx.tp.node_order(sf).nodes() {
        visit(ctx, &mut diagnostics, n);
    }
    diagnostics
}

// Go: rules/schema_opaque_instance_member.go isSchemaOpaqueInstanceMember
fn is_schema_opaque_instance_member(node: Node) -> bool {
    if node.is_nil() || has_syntactic_modifier(node, ModifierFlags::STATIC) {
        return false;
    }
    matches!(
        node.kind(),
        SyntaxKind::PropertyDeclaration
            | SyntaxKind::MethodDeclaration
            | SyntaxKind::GetAccessor
            | SyntaxKind::SetAccessor
            | SyntaxKind::Constructor
    )
}
