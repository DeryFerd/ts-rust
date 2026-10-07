//! Port of Effect-TS/tsgo `internal/rules/non_object_effect_service_type.go`.

use crate::effect::diag;
use crate::effect::etscore::*;
use crate::effect::rule::*;
use crate::effect::typeparser::*;
use crate::prelude::*;

// Go: rules.NonObjectEffectServiceType
/// NonObjectEffectServiceType checks that Effect.Service option properties
/// (succeed, sync, effect, scoped) do not resolve to primitive types.
/// V3-only, default severity error.
pub static NON_OBJECT_EFFECT_SERVICE_TYPE: Rule = Rule {
    name: "nonObjectEffectServiceType",
    group: "correctness",
    description: "Ensures Effect.Service types are objects, not primitives",
    default_severity: Severity::Error,
    supported_effect: &["v3"],
    codes: &[377048],
    run: run_non_object_effect_service_type,
};

fn run_non_object_effect_service_type(ctx: &mut RuleContext<'_, '_>) -> Vec<Diagnostic> {
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
            let d = check_service_property_types(ctx, node);
            if !d.is_empty() {
                diags.extend(d);
                continue; // skip children
            }
        }

        // Enqueue children
        node.for_each_child(|child| {
            node_to_visit.push(child);
            false
        });
    }

    diags
}

// Go: rules.checkServicePropertyTypes
/// checkServicePropertyTypes checks if a class extending Effect.Service has option
/// properties that resolve to primitive types.
fn check_service_property_types(ctx: &mut RuleContext<'_, '_>, node: Node) -> Vec<Diagnostic> {
    let Some(service_result) = ctx.tp.extends_effect_v3_service(node) else {
        return Vec::new();
    };

    let options = service_result.options;
    if options.is_nil() || options.kind() != SyntaxKind::ObjectLiteralExpression {
        return Vec::new();
    }

    let obj_lit = options;

    let mut diags = Vec::new();

    for prop in obj_lit.properties() {
        if prop.is_nil() || prop.kind() != SyntaxKind::PropertyAssignment {
            continue;
        }
        let pa = prop;
        if pa.name().is_nil() || pa.name().kind() != SyntaxKind::Identifier {
            continue;
        }

        let property_name = get_text_of_node(pa.name());
        let initializer = pa.initializer();
        if initializer.is_nil() {
            continue;
        }

        match property_name.as_str() {
            "succeed" => {
                let value_type = ctx.tp.get_type_at_location(initializer);
                if value_type.is_some() && is_primitive_type(ctx.tp, value_type) {
                    diags.push(ctx.new_diagnostic(
                        ctx.source_file,
                        ctx.get_error_range(pa.name()),
                        diag::Effect_Service_is_declared_with_a_primitive_service_type_Effect_Service_models_object_shaped_services_primitive_values_use_Context_Tag_or_Effect_Tag_directly_effect_nonObjectEffectServiceType,
                        Vec::new(),
                        Vec::new(),
                    ));
                }
            }

            "sync" => {
                let value_type = ctx.tp.get_type_at_location(initializer);
                if value_type.is_nil() {
                    continue;
                }
                let signatures = ctx
                    .tp
                    .checker
                    .get_signatures_of_type_exported(value_type, SignatureKind::CALL);
                for sig in signatures {
                    let return_type = ctx.tp.checker.get_return_type_of_signature_exported(sig);
                    if return_type.is_some() && is_primitive_type(ctx.tp, return_type) {
                        diags.push(ctx.new_diagnostic(
                            ctx.source_file,
                            ctx.get_error_range(pa.name()),
                            diag::Effect_Service_is_declared_with_a_primitive_service_type_Effect_Service_models_object_shaped_services_primitive_values_use_Context_Tag_or_Effect_Tag_directly_effect_nonObjectEffectServiceType,
                            Vec::new(),
                            Vec::new(),
                        ));
                        break;
                    }
                }
            }

            "effect" | "scoped" => {
                let value_type = ctx.tp.get_type_at_location(initializer);
                if value_type.is_nil() {
                    continue;
                }

                // Try direct EffectType parse first
                if let Some(effect_result) = ctx.tp.effect_type(value_type) {
                    if is_primitive_type(ctx.tp, effect_result.a) {
                        diags.push(ctx.new_diagnostic(
                            ctx.source_file,
                            ctx.get_error_range(pa.name()),
                            diag::Effect_Service_is_declared_with_a_primitive_service_type_Effect_Service_models_object_shaped_services_primitive_values_use_Context_Tag_or_Effect_Tag_directly_effect_nonObjectEffectServiceType,
                            Vec::new(),
                            Vec::new(),
                        ));
                    }
                    continue;
                }

                // Fall back to call signatures
                let signatures = ctx
                    .tp
                    .checker
                    .get_signatures_of_type_exported(value_type, SignatureKind::CALL);
                for sig in signatures {
                    let return_type = ctx.tp.checker.get_return_type_of_signature_exported(sig);
                    if return_type.is_nil() {
                        continue;
                    }
                    let effect_return_result = ctx.tp.effect_type(return_type);
                    if let Some(effect_return_result) = effect_return_result
                        && is_primitive_type(ctx.tp, effect_return_result.a)
                    {
                        diags.push(ctx.new_diagnostic(
                            ctx.source_file,
                            ctx.get_error_range(pa.name()),
                            diag::Effect_Service_is_declared_with_a_primitive_service_type_Effect_Service_models_object_shaped_services_primitive_values_use_Context_Tag_or_Effect_Tag_directly_effect_nonObjectEffectServiceType,
                            Vec::new(),
                            Vec::new(),
                        ));
                        break;
                    }
                }
            }

            _ => {}
        }
    }

    diags
}

// Go: rules.isPrimitiveType
/// isPrimitiveType checks if a type (or any member of a union type) is a primitive type.
fn is_primitive_type(tp: &mut TypeParser<'_>, t: TypeId) -> bool {
    let primitive_flags = TypeFlags::STRING
        | TypeFlags::NUMBER
        | TypeFlags::BOOLEAN
        | TypeFlags::STRING_LITERAL
        | TypeFlags::NUMBER_LITERAL
        | TypeFlags::BOOLEAN_LITERAL
        | TypeFlags::UNDEFINED
        | TypeFlags::NULL;

    for member in tp.unroll_union_members(t) {
        if tp.checker.ty(member).flags().intersects(primitive_flags) {
            return true;
        }
    }
    false
}
