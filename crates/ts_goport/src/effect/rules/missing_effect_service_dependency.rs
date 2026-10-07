//! Port of Effect-TS/tsgo `internal/rules/missing_effect_service_dependency.go`.

use crate::effect::diag;
use crate::effect::etscore::*;
use crate::effect::rule::*;
use crate::effect::typeparser::*;
use crate::prelude::*;

/// MissingEffectServiceDependency checks that Effect.Service dependencies satisfy
/// all required layer inputs. It detects when a class extending Effect.Service has
/// required services (from the layer's RIn) that are not provided in the dependencies
/// configuration option. V3-only, default severity off.
// Go: rules/missing_effect_service_dependency.go MissingEffectServiceDependency
pub static MISSING_EFFECT_SERVICE_DEPENDENCY: Rule = Rule {
    name: "missingEffectServiceDependency",
    group: "style",
    description: "Checks that Effect.Service dependencies satisfy all required layer inputs",
    default_severity: Severity::Off,
    supported_effect: &["v3"],
    codes: &[377039, 377040],
    run: run_missing_effect_service_dependency,
};

fn run_missing_effect_service_dependency(ctx: &mut RuleContext<'_, '_>) -> Vec<Diagnostic> {
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
            let d = check_service_dependencies(ctx, node);
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

// Go: the `excludeNever` closure of checkServiceDependencies.
fn exclude_never(tp: &mut TypeParser<'_>, t: TypeId) -> bool {
    tp.checker.ty(t).flags.intersects(TypeFlags::NEVER)
}

/// checkServiceDependencies checks if a class extending Effect.Service has all
/// required service dependencies satisfied.
// Go: rules/missing_effect_service_dependency.go checkServiceDependencies
fn check_service_dependencies(ctx: &mut RuleContext<'_, '_>, node: Node) -> Vec<Diagnostic> {
    // Check if this class extends Effect.Service
    let service_result = ctx.tp.extends_effect_v3_service(node);
    let Some(service_result) = service_result else {
        return Vec::new();
    };

    let class_name = service_result.class_name;
    let options = service_result.options;

    // Get the class symbol and type
    let class_sym = ctx.tp.get_symbol_at_location(class_name);
    if class_sym.is_nil() {
        return Vec::new();
    }
    let class_type = ctx
        .tp
        .checker
        .get_type_of_symbol_at_location(class_sym, node);
    if class_type.is_nil() {
        return Vec::new();
    }

    // Try DefaultWithoutDependencies first, then fall back to Default
    let mut default_prop = ctx
        .tp
        .checker
        .get_property_of_type_exported(class_type, "DefaultWithoutDependencies");
    if default_prop.is_nil() {
        default_prop = ctx
            .tp
            .checker
            .get_property_of_type_exported(class_type, "Default");
    }
    if default_prop.is_nil() {
        return Vec::new();
    }

    let default_type = ctx
        .tp
        .checker
        .get_type_of_symbol_at_location(default_prop, node);
    if default_type.is_nil() {
        return Vec::new();
    }

    // Parse as Layer type to get RIn
    let layer = ctx.tp.layer_type(default_type);
    let Some(layer) = layer else {
        return Vec::new();
    };

    // Use a shared memory map for both required and provided services
    let mut services_memory: FxHashMap<String, TypeId> = FxHashMap::default();

    // Get all required service indexes from RIn
    let required_result = ctx.tp.append_to_unique_types_map(
        &mut services_memory,
        layer.r_in,
        Some(&mut exclude_never),
    );
    let required_indexes = required_result.all_indexes;

    if required_indexes.is_empty() {
        return Vec::new();
    }

    // Process dependencies to find provided services
    let mut provided_indexes: FxHashMap<String, bool> = FxHashMap::default();

    if options.is_some() {
        let options_type = ctx.tp.get_type_at_location(options);
        if options_type.is_some() {
            let dependencies_prop = ctx
                .tp
                .checker
                .get_property_of_type_exported(options_type, "dependencies");
            if dependencies_prop.is_some() {
                let dependencies_type = ctx
                    .tp
                    .checker
                    .get_type_of_symbol_at_location(dependencies_prop, options);
                if dependencies_type.is_some() {
                    // Get the number index type to extract individual dependency types
                    let number_index_type = ctx.tp.checker.get_number_index_type(dependencies_type);
                    if number_index_type.is_some() {
                        let dep_types = ctx.tp.unroll_union_members(number_index_type);
                        for dep_type in dep_types {
                            // Parse each dependency as Layer type
                            let dep_layer = ctx.tp.layer_type(dep_type);
                            if let Some(dep_layer) = dep_layer {
                                // Add the ROut of this dependency to provided services
                                let provided_result = ctx.tp.append_to_unique_types_map(
                                    &mut services_memory,
                                    dep_layer.r_out,
                                    Some(&mut exclude_never),
                                );
                                for idx in provided_result.all_indexes {
                                    provided_indexes.insert(idx, true);
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    // Find missing indexes: required but not provided
    let mut missing_indexes: Vec<String> = Vec::new();
    for idx in &required_indexes {
        if !provided_indexes.get(idx).copied().unwrap_or(false) {
            missing_indexes.push(idx.clone());
        }
    }

    if missing_indexes.is_empty() {
        return Vec::new();
    }

    // Build the diagnostic
    let mut missing_type_names: Vec<String> = Vec::new();
    for idx in &missing_indexes {
        let t = services_memory.get(idx).copied().unwrap_or(TypeId::NIL);
        if t.is_some() {
            missing_type_names.push(ctx.tp.checker.type_to_string_exported(t));
        }
    }

    if missing_type_names.is_empty() {
        return Vec::new();
    }

    if missing_type_names.len() == 1 {
        // Singular
        let d = ctx.new_diagnostic(
            ctx.source_file,
            ctx.get_error_range(class_name),
            diag::Service_0_is_required_but_not_provided_by_dependencies_effect_missingEffectServiceDependency,
            Vec::new(),
            args![missing_type_names[0]],
        );
        return vec![d];
    }

    // Plural: format as 'X', 'Y'
    let mut quoted_names: Vec<String> = Vec::new();
    for name in &missing_type_names {
        quoted_names.push(format!("'{name}'"));
    }
    let formatted = quoted_names.join(", ");
    let d = ctx.new_diagnostic(
        ctx.source_file,
        ctx.get_error_range(class_name),
        diag::Services_0_are_required_but_not_provided_by_dependencies_effect_missingEffectServiceDependency,
        Vec::new(),
        args![formatted],
    );
    vec![d]
}
