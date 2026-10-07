//! Port of Effect-TS/tsgo `internal/rules/schema_sync.go`.

use crate::effect::diag;
use crate::effect::etscore::*;
use crate::effect::rule::*;
use crate::effect::typeparser::*;
use crate::prelude::*;

// SchemaSync discourages synchronous Schema decoding and encoding in any context.
pub static SCHEMA_SYNC: Rule = Rule {
    name: "schemaSync",
    group: "effectNative",
    description: "Suggests Effect-based Schema decoding and encoding instead of synchronous methods",
    default_severity: Severity::Off,
    supported_effect: &["v3", "v4"],
    codes: &[377130],
    run: run_schema_sync,
};

fn run_schema_sync(ctx: &mut RuleContext<'_, '_>) -> Vec<Diagnostic> {
    let mut methods = super::schema_sync_in_effect::SYNC_TO_EFFECT_METHOD_V3;
    if ctx.tp.supported_effect_version() == EffectMajorVersion::V4 {
        methods = super::schema_sync_in_effect::SYNC_TO_EFFECT_METHOD_V4;
    }

    fn walk(
        ctx: &mut RuleContext<'_, '_>,
        diags: &mut Vec<Diagnostic>,
        methods: &[(&str, &str)],
        node: Node,
    ) -> bool {
        if node.is_nil() {
            return false;
        }
        if node.kind() == SyntaxKind::CallExpression {
            let callee = node.expression();
            let mut reference = skip_parentheses(callee);
            if reference.kind() == SyntaxKind::ElementAccessExpression {
                reference = reference.argument_expression();
            }
            // PORT: Go ranges over a map (random order). A reference names one
            // member, so at most one entry matches and the order does not
            // change the result.
            for &(sync_name, effect_name) in methods {
                if ctx
                    .tp
                    .is_node_reference_to_effect_schema_module_api(reference, sync_name)
                    || ctx
                        .tp
                        .is_node_reference_to_effect_parse_result_module_api(reference, sync_name)
                    || ctx
                        .tp
                        .is_node_reference_to_effect_schema_parser_module_api(reference, sync_name)
                {
                    diags.push(ctx.new_diagnostic(
                        ctx.source_file,
                        ctx.get_error_range(callee),
                        diag::X_0_executes_synchronously_Use_Schema_1_to_compose_this_operation_through_Effect_without_throwing_effect_schemaSync,
                        Vec::new(),
                        vec![
                            get_source_text_of_node_from_source_file(ctx.source_file, callee, false),
                            effect_name.to_string(),
                        ],
                    ));
                    break;
                }
            }
        }
        node.for_each_child(|child| walk(ctx, diags, methods, child));
        false
    }

    let mut diags = Vec::new();
    let sf = ctx.source_file;
    walk(ctx, &mut diags, methods, sf);
    diags
}
