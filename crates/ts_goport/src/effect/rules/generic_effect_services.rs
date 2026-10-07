//! Port of Effect-TS/tsgo `internal/rules/generic_effect_services.go`.

use crate::effect::diag;
use crate::effect::etscore::*;
use crate::effect::rule::*;
use crate::effect::typeparser::*;
use crate::prelude::*;

/// GenericEffectServices detects Effect Service class declarations that have type
/// parameters (generics), which cannot be properly discriminated at runtime.
/// This is a V3-only rule.
pub static GENERIC_EFFECT_SERVICES: Rule = Rule {
    name: "genericEffectServices",
    group: "correctness",
    description: "Prevents services with type parameters that cannot be discriminated at runtime",
    default_severity: Severity::Warning,
    supported_effect: &["v3"],
    codes: &[377043],
    run: run_generic_effect_services,
};

fn run_generic_effect_services(ctx: &mut RuleContext<'_, '_>) -> Vec<Diagnostic> {
    // V3-only rule
    if ctx.tp.supported_effect_version() != EffectMajorVersion::V3 {
        return Vec::new();
    }

    let mut diags = Vec::new();

    // Stack-based traversal
    let mut node_to_visit: Vec<Node> = Vec::new();
    ctx.source_file.for_each_child(|child| {
        node_to_visit.push(child);
        false
    });

    while let Some(node) = node_to_visit.pop() {
        if node.kind() == SyntaxKind::ClassDeclaration {
            let class_decl = node;
            if node.name().is_some()
                && class_decl.type_parameter_list().is_some()
                && class_decl.heritage_clauses().is_some()
            {
                let class_sym = ctx.tp.get_symbol_at_location(node.name());
                if class_sym.is_some() {
                    let class_type = ctx
                        .tp
                        .checker
                        .get_type_of_symbol_at_location(class_sym, node);
                    if class_type.is_some() && ctx.tp.is_context_tag(class_type) {
                        diags.push(ctx.new_diagnostic(
                            ctx.source_file,
                            ctx.get_error_range(node.name()),
                            diag::Effect_Services_with_type_parameters_are_not_supported_because_they_cannot_be_properly_discriminated_at_runtime_which_may_cause_unexpected_behavior_effect_genericEffectServices,
                            Vec::new(),
                            Vec::new(),
                        ));
                        continue; // skip children
                    }
                }
            }
        }

        // Enqueue children for further traversal
        node.for_each_child(|child| {
            node_to_visit.push(child);
            false
        });
    }

    diags
}
