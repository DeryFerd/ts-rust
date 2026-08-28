//! Object-literal assignability diagnostic elaboration.
//!
//! This is the property-only prefix of the pinned
//! `checkTypeAssignableToAndOptionallyElaborate` / `elaborateObjectLiteral` /
//! `elaborateElement` path at
//! `dc37b5249ab60e2bbce936f71b883e6c8136167e`. Relations remain silent: this
//! module runs only after a failed assignability query and builds complete
//! primary-plus-related records before the caller publishes any of them.
//!
//! TS6500 is suppressed only for declarations retained from a Program-owned
//! default-library source, matching the pinned elaboration path without
//! filename or declaration-shape heuristics.

use std::collections::HashSet;

use ts_ast::{NodeData, NodeRef, SyntaxKind};
use ts_binder::SymbolFlags;
use ts_diagnostics::{Diagnostic, message_by_code};

use super::{
    AssignabilityErrorDisplay, CanonicalCheckerDiagnostic, CanonicalCheckerOptions,
    CanonicalCheckerRelatedInformation, CanonicalGlobalTypes, CanonicalTypeFormatFlags,
    CanonicalTypeMapperStore, DeclaredTypeHost, RelationUnavailable, SignatureId,
    TypeDisplayUnavailable, TypeId,
    array_types::CanonicalArrayTargets,
    callables::{
        StoredSingleCallableValidation, single_callable_display_projection,
        validate_stored_single_callable,
    },
    classes::{
        ClassConstructorVisibility, ClassHeritageMembersValidation, class_member_visibility,
        validate_class_heritage_members, validated_class_derives_from,
    },
    formatter::{
        FunctionTypeDisplayUnavailable,
        get_type_names_for_assignability_error_with_host_global_types_and_flags,
        type_to_string_with_host_global_types_and_flags,
    },
    functions::{
        StoredFunctionTypeValidation, function_type_display_projection,
        validate_stored_function_type,
    },
    indexed_access_types::{is_template_pattern_index_key, template_pattern_index_matches_name},
    instantiate::InstantiationSession,
    object_members::{
        DeclaredPropertyTypeGraphValidation, PropertyObjectPlan,
        validate_resolved_declared_property_type_graph,
    },
    relater::{ResolvedDeclaredProperty, ResolvedDeclaredPropertyObject},
    signatures::ElementFlags,
    source::{
        CheckedExpressionShape, CheckedExpressionTypes, PlannedExpression, PlannedExpressionKind,
        SourceCheckError, SourceCheckProvenanceError,
    },
    spelling::get_spelling_suggestion,
    type_nodes::CanonicalTypeQuery,
    type_records::{StructuredTypeData, TypeCacheState, TypeData},
    types::{ObjectFlags, TypeFlags},
};

/// Builds the complete diagnostic batch for one already-failed assignment.
#[allow(clippy::too_many_arguments)] // Keeps diagnostic inputs explicit and immutable.
pub(super) fn diagnostics_for_failed_assignment(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    global_types: &CanonicalGlobalTypes,
    expression: &PlannedExpression,
    checked: &CheckedExpressionTypes,
    target_type: TypeId,
    fallback_node: NodeRef,
    options: CanonicalCheckerOptions,
    session: &mut InstantiationSession,
) -> Result<Vec<CanonicalCheckerDiagnostic>, SourceCheckError> {
    let mut prerequisite_diagnostics = Vec::new();
    let mut resolved_signatures = HashSet::new();
    loop {
        match diagnostics_for_failed_assignment_once(
            store,
            host,
            global_types,
            expression,
            checked,
            target_type,
            fallback_node,
            options,
            session,
        ) {
            Ok(mut diagnostics) => {
                prerequisite_diagnostics.append(&mut diagnostics);
                return Ok(prerequisite_diagnostics);
            }
            Err(
                error @ SourceCheckError::TypeDisplayUnavailable(
                    TypeDisplayUnavailable::FunctionType {
                        type_id,
                        reason: FunctionTypeDisplayUnavailable::UnresolvedReturn,
                    },
                ),
            ) => {
                let Some(signature) = exact_function_type_signature(store, type_id) else {
                    return Err(error);
                };
                if !resolved_signatures.insert(signature) {
                    return Err(error);
                }
                let mut resolution_diagnostics = super::CanonicalCheckerDiagnostics::default();
                let resolved = CanonicalTypeQuery::new_with_global_types_and_session(
                    store,
                    host,
                    global_types,
                    options,
                    session,
                    &mut resolution_diagnostics,
                )?
                .get_return_type_of_signature(signature);
                prerequisite_diagnostics.extend(resolution_diagnostics.into_vec());
                resolved?;
            }
            Err(SourceCheckError::RelationUnavailable(
                RelationUnavailable::UnresolvedSignatureReturn(signature),
            )) => {
                if !resolved_signatures.insert(signature) {
                    return Err(RelationUnavailable::UnresolvedSignatureReturn(signature).into());
                }
                let mut resolution_diagnostics = super::CanonicalCheckerDiagnostics::default();
                let resolved = CanonicalTypeQuery::new_with_global_types_and_session(
                    store,
                    host,
                    global_types,
                    options,
                    session,
                    &mut resolution_diagnostics,
                )?
                .get_return_type_of_signature(signature);
                prerequisite_diagnostics.extend(resolution_diagnostics.into_vec());
                resolved?;
            }
            Err(error) => return Err(error),
        }
    }
}

#[allow(clippy::too_many_arguments)] // Keeps one diagnostic retry immutable and explicit.
fn diagnostics_for_failed_assignment_once(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    global_types: &CanonicalGlobalTypes,
    expression: &PlannedExpression,
    checked: &CheckedExpressionTypes,
    target_type: TypeId,
    fallback_node: NodeRef,
    options: CanonicalCheckerOptions,
    session: &mut InstantiationSession,
) -> Result<Vec<CanonicalCheckerDiagnostic>, SourceCheckError> {
    validate_checked_expression_shape(expression, checked)?;
    let flags = display_flags(options);
    if options.intrinsic.exact_optional_property_types
        && matches!(
            expression.unparenthesized().kind,
            PlannedExpressionKind::Object { .. }
        )
        && let Some(diagnostic) = exact_optional_assignment_diagnostic(
            store,
            host,
            global_types,
            checked.result,
            target_type,
            fallback_node,
            flags,
        )?
    {
        return Ok(vec![diagnostic]);
    }
    let mut elaborated = elaborate_expression(
        store,
        host,
        global_types,
        expression,
        checked,
        target_type,
        flags,
        options,
        session,
    )?;
    if !elaborated.is_empty() {
        return Ok(elaborated);
    }
    elaborated.push(shape_or_generic_diagnostic(
        store,
        host,
        global_types,
        expression,
        checked.result,
        target_type,
        fallback_node,
        flags,
        options,
    )?);
    Ok(elaborated)
}

fn exact_optional_assignment_diagnostic(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    global_types: &CanonicalGlobalTypes,
    source_type: TypeId,
    target_type: TypeId,
    node: NodeRef,
    flags: CanonicalTypeFormatFlags,
) -> Result<Option<CanonicalCheckerDiagnostic>, SourceCheckError> {
    let details = exact_optional_property_mismatch_details(
        store,
        host,
        global_types,
        source_type,
        target_type,
        flags,
    )?;
    if details.is_empty() {
        return Ok(None);
    }
    let AssignabilityErrorDisplay { source, target } =
        get_type_names_for_assignability_error_with_host_global_types_and_flags(
            store,
            host,
            global_types,
            source_type,
            target_type,
            flags,
        )?;
    let mut diagnostic = primary(2375, node, vec![source, target])?;
    diagnostic.diagnostic.details = details;
    Ok(Some(diagnostic))
}

fn exact_function_type_signature(
    store: &CanonicalTypeMapperStore,
    type_id: TypeId,
) -> Option<SignatureId> {
    if !matches!(
        validate_stored_function_type(store, type_id),
        StoredFunctionTypeValidation::Valid(_)
    ) {
        return None;
    }
    let structured = store.type_payload(type_id)?.data().structured()?;
    let signatures = structured.signatures.as_deref()?;
    (structured.call_signature_count == 1 && signatures.len() == 1).then_some(signatures[0])
}

/// Validates the complete retained execution tree before recursive diagnostic
/// elaboration can run relation queries for any sibling.
fn validate_checked_expression_shape(
    expression: &PlannedExpression,
    checked: &CheckedExpressionTypes,
) -> Result<(), SourceCheckError> {
    let expression = expression.unparenthesized();
    match (&expression.kind, &checked.shape) {
        (
            PlannedExpressionKind::Object { plan, properties },
            CheckedExpressionShape::Object(checked_properties),
        ) => {
            if plan.properties.len() != properties.len()
                || properties.len() != checked_properties.len()
            {
                return Err(invalid_structure(checked.result));
            }
            for (property, checked_property) in properties.iter().zip(checked_properties) {
                validate_checked_expression_shape(property, checked_property)?;
            }
            Ok(())
        }
        (
            PlannedExpressionKind::Array(elements),
            CheckedExpressionShape::Array(checked_elements),
        ) => {
            if elements.len() != checked_elements.len() {
                return Err(invalid_structure(checked.result));
            }
            for (element, checked_element) in elements.iter().zip(checked_elements) {
                validate_checked_expression_shape(element, checked_element)?;
            }
            Ok(())
        }
        (
            PlannedExpressionKind::Object { .. } | PlannedExpressionKind::Array(_),
            CheckedExpressionShape::Leaf,
        )
        | (_, CheckedExpressionShape::Array(_) | CheckedExpressionShape::Object(_)) => {
            Err(invalid_structure(checked.result))
        }
        _ => Ok(()),
    }
}

#[allow(clippy::too_many_arguments)] // Mirrors the pinned recursive elaboration boundary.
fn elaborate_expression(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    global_types: &CanonicalGlobalTypes,
    expression: &PlannedExpression,
    checked: &CheckedExpressionTypes,
    target_type: TypeId,
    flags: CanonicalTypeFormatFlags,
    options: CanonicalCheckerOptions,
    session: &mut InstantiationSession,
) -> Result<Vec<CanonicalCheckerDiagnostic>, SourceCheckError> {
    let expression = expression.unparenthesized();
    match (&expression.kind, &checked.shape) {
        (PlannedExpressionKind::Object { .. }, CheckedExpressionShape::Object(_)) => {
            elaborate_known_properties(
                store,
                host,
                global_types,
                expression,
                checked,
                target_type,
                flags,
                options,
                session,
            )
        }
        (PlannedExpressionKind::Array(_), CheckedExpressionShape::Array(_)) => Ok(
            super::array_diagnostics::diagnostics_for_failed_array_assignment(
                store,
                host,
                global_types,
                expression,
                checked,
                target_type,
                options,
                session,
            )?
            .unwrap_or_default(),
        ),
        (
            PlannedExpressionKind::Object { .. } | PlannedExpressionKind::Array(_),
            CheckedExpressionShape::Leaf,
        )
        | (_, CheckedExpressionShape::Array(_) | CheckedExpressionShape::Object(_)) => {
            Err(invalid_structure(checked.result))
        }
        _ => Ok(Vec::new()),
    }
}

fn display_flags(options: CanonicalCheckerOptions) -> CanonicalTypeFormatFlags {
    let mut flags = CanonicalTypeFormatFlags::TYPE_TO_STRING_DEFAULT;
    if options.no_error_truncation {
        flags |= CanonicalTypeFormatFlags::NO_TRUNCATION;
    }
    flags
}

/// Mirrors `elaborateObjectLiteral`: every incompatible known source property
/// is attempted in source order, and any successful elaboration suppresses all
/// root fallback diagnostics.
#[allow(clippy::too_many_arguments)] // Keeps recursive expression capabilities explicit.
fn elaborate_known_properties(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    global_types: &CanonicalGlobalTypes,
    expression: &PlannedExpression,
    checked: &CheckedExpressionTypes,
    target_type: TypeId,
    flags: CanonicalTypeFormatFlags,
    options: CanonicalCheckerOptions,
    session: &mut InstantiationSession,
) -> Result<Vec<CanonicalCheckerDiagnostic>, SourceCheckError> {
    let expression = expression.unparenthesized();
    let PlannedExpressionKind::Object { plan, properties } = &expression.kind else {
        return Ok(Vec::new());
    };
    let CheckedExpressionShape::Object(checked_properties) = &checked.shape else {
        return Err(invalid_structure(checked.result));
    };
    let Some(target) = store.resolved_declared_property_object(host, target_type)? else {
        return Ok(Vec::new());
    };
    let source_types = resolved_source_property_types(store, plan, checked.result)?;
    if properties.len() != plan.properties.len()
        || source_types.len() != plan.properties.len()
        || checked_properties.len() != plan.properties.len()
    {
        return Err(invalid_structure(checked.result));
    }
    let indexed_target = declared_index_target(store, host, target_type)?;
    if target.properties().is_empty()
        && let Some(index) = indexed_target
    {
        return elaborate_indexed_properties(
            store,
            host,
            global_types,
            plan,
            properties,
            checked_properties,
            &source_types,
            index,
            flags,
            options,
            session,
        );
    }

    let mut diagnostics = Vec::new();
    for (index, ((source_property, source_expression), source_property_type)) in plan
        .properties
        .iter()
        .zip(properties)
        .zip(source_types)
        .enumerate()
    {
        let checked_property = &checked_properties[index];
        if checked_property.result != source_property_type {
            return Err(invalid_structure(checked.result));
        }
        let Some(target_property) = target.get(source_property.name.as_ref()) else {
            if let Some(indexed_target) = indexed_target {
                let name = source_property.name.as_utf8().ok_or(
                    RelationUnavailable::UnsupportedProperty(source_property.symbol),
                )?;
                diagnostics.extend(elaborate_indexed_property(
                    store,
                    host,
                    global_types,
                    source_expression,
                    checked_property,
                    name,
                    source_property.name_node,
                    source_property_type,
                    indexed_target,
                    flags,
                    options,
                    session,
                )?);
            }
            continue;
        };
        if store.is_type_assignable_to_with_global_types(
            source_property_type,
            target_property.type_,
            global_types,
        )? {
            continue;
        }

        if options.intrinsic.exact_optional_property_types
            && matches!(
                source_expression.unparenthesized().kind,
                PlannedExpressionKind::Object { .. }
            )
            && let Some(mut diagnostic) = exact_optional_assignment_diagnostic(
                store,
                host,
                global_types,
                source_property_type,
                target_property.type_,
                source_property.name_node,
                flags,
            )?
        {
            append_expected_property_related(
                &mut diagnostic,
                store,
                host,
                global_types,
                target_type,
                target_property,
                flags,
            )?;
            diagnostics.push(diagnostic);
            continue;
        }

        let nested = elaborate_expression(
            store,
            host,
            global_types,
            source_expression,
            checked_property,
            target_property.type_,
            flags,
            options,
            session,
        )?;
        if !nested.is_empty() {
            diagnostics.extend(nested);
            continue;
        }

        let mut diagnostic = shape_or_generic_diagnostic(
            store,
            host,
            global_types,
            source_expression,
            source_property_type,
            target_property.type_,
            source_property.name_node,
            flags,
            options,
        )?;
        append_expected_property_related(
            &mut diagnostic,
            store,
            host,
            global_types,
            target_type,
            target_property,
            flags,
        )?;
        diagnostics.push(diagnostic);
    }
    Ok(diagnostics)
}

#[derive(Clone, Copy)]
struct DeclaredIndexTarget {
    key_type: TypeId,
    value_type: TypeId,
    declaration: NodeRef,
}

fn declared_index_target(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    target: TypeId,
) -> Result<Option<DeclaredIndexTarget>, SourceCheckError> {
    let record = store
        .type_payload(target)
        .ok_or(RelationUnavailable::Type(target))?;
    let Some(indexes) = record
        .data()
        .structured()
        .and_then(|structured| structured.index_infos.as_deref())
    else {
        return Ok(None);
    };
    let [index] = indexes else {
        return Err(invalid_structure(target));
    };
    let info = store
        .index_info(*index)
        .ok_or_else(|| invalid_structure(target))?;
    let declaration = info
        .declaration()
        .ok_or_else(|| invalid_structure(target))?;
    let node = host
        .node(declaration)
        .ok_or_else(|| invalid_structure(target))?;
    let bootstrap = store
        .intrinsic_bootstrap()
        .ok_or(RelationUnavailable::MissingBootstrap)?;
    let supported_key = info.key_type() == bootstrap.string_type
        || info.key_type() == bootstrap.number_type
        || info.key_type() == bootstrap.es_symbol_type
        || is_template_pattern_index_key(store, info.key_type());
    if node.kind != SyntaxKind::IndexSignature
        || !supported_key
        || store.type_payload(info.value_type()).is_none()
        || info.index_symbol().is_some()
        || !info.components().is_empty()
    {
        return Err(invalid_structure(target));
    }
    Ok(Some(DeclaredIndexTarget {
        key_type: info.key_type(),
        value_type: info.value_type(),
        declaration,
    }))
}

fn declared_index_accepts_name(
    store: &CanonicalTypeMapperStore,
    target: DeclaredIndexTarget,
    name: &str,
) -> Result<bool, SourceCheckError> {
    let bootstrap = store
        .intrinsic_bootstrap()
        .ok_or(RelationUnavailable::MissingBootstrap)?;
    Ok(target.key_type == bootstrap.string_type
        || target.key_type == bootstrap.number_type
            && ts_jsnum::from_string(name).to_string() == name
        || template_pattern_index_matches_name(store, target.key_type, name))
}

#[allow(clippy::too_many_arguments)] // Keeps the retained expression tree and relation context explicit.
fn elaborate_indexed_properties(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    global_types: &CanonicalGlobalTypes,
    plan: &PropertyObjectPlan,
    expressions: &[PlannedExpression],
    checked: &[CheckedExpressionTypes],
    source_types: &[TypeId],
    target: DeclaredIndexTarget,
    flags: CanonicalTypeFormatFlags,
    options: CanonicalCheckerOptions,
    session: &mut InstantiationSession,
) -> Result<Vec<CanonicalCheckerDiagnostic>, SourceCheckError> {
    let mut diagnostics = Vec::new();
    for (index, ((property, expression), source_type)) in plan
        .properties
        .iter()
        .zip(expressions)
        .zip(source_types)
        .enumerate()
    {
        let name = property
            .name
            .as_utf8()
            .ok_or(RelationUnavailable::UnsupportedProperty(property.symbol))?;
        diagnostics.extend(elaborate_indexed_property(
            store,
            host,
            global_types,
            expression,
            &checked[index],
            name,
            property.name_node,
            *source_type,
            target,
            flags,
            options,
            session,
        )?);
    }
    Ok(diagnostics)
}

#[allow(clippy::too_many_arguments)] // Retains exact property position and expression provenance.
fn elaborate_indexed_property(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    global_types: &CanonicalGlobalTypes,
    expression: &PlannedExpression,
    checked: &CheckedExpressionTypes,
    name: &str,
    name_node: NodeRef,
    source_type: TypeId,
    target: DeclaredIndexTarget,
    flags: CanonicalTypeFormatFlags,
    options: CanonicalCheckerOptions,
    session: &mut InstantiationSession,
) -> Result<Vec<CanonicalCheckerDiagnostic>, SourceCheckError> {
    if !declared_index_accepts_name(store, target, name)?
        || store.is_type_assignable_to_with_global_types(
            source_type,
            target.value_type,
            global_types,
        )?
    {
        return Ok(Vec::new());
    }
    let nested = elaborate_expression(
        store,
        host,
        global_types,
        expression,
        checked,
        target.value_type,
        flags,
        options,
        session,
    )?;
    if !nested.is_empty() {
        return Ok(nested);
    }

    let mut diagnostic = generic_assignability_diagnostic(
        store,
        host,
        global_types,
        source_type,
        target.value_type,
        name_node,
        flags,
        options,
    )?;
    let (_, bound) = host
        .source(target.declaration)
        .ok_or_else(|| invalid_structure(target.value_type))?;
    let facts = bound.source_facts().ok_or(SourceCheckError::Provenance(
        SourceCheckProvenanceError::MissingSourceFacts(target.declaration.file),
    ))?;
    if !facts.is_default_library() {
        diagnostic
            .related_information
            .push(related(6501, target.declaration, Vec::new())?);
    }
    Ok(vec![diagnostic])
}

#[allow(clippy::too_many_arguments)] // Mirrors the pinned elaboration boundary.
fn shape_or_generic_diagnostic(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    global_types: &CanonicalGlobalTypes,
    expression: &PlannedExpression,
    source_type: TypeId,
    target_type: TypeId,
    fallback_node: NodeRef,
    flags: CanonicalTypeFormatFlags,
    options: CanonicalCheckerOptions,
) -> Result<CanonicalCheckerDiagnostic, SourceCheckError> {
    let expression = expression.unparenthesized();
    let PlannedExpressionKind::Object { plan, properties } = &expression.kind else {
        return generic_assignability_diagnostic(
            store,
            host,
            global_types,
            source_type,
            target_type,
            fallback_node,
            flags,
            options,
        );
    };
    if let Some(diagnostic) = discriminated_union_excess_property_diagnostic(
        store,
        host,
        global_types,
        plan,
        properties,
        target_type,
        flags,
    )? {
        return Ok(diagnostic);
    }
    let Some(target) = store.resolved_declared_property_object(host, target_type)? else {
        return generic_assignability_diagnostic(
            store,
            host,
            global_types,
            source_type,
            target_type,
            fallback_node,
            flags,
            options,
        );
    };

    if let Some(excess) = first_excess_property(store, host, plan, &target, target_type)? {
        return excess_property_diagnostic(
            store,
            host,
            global_types,
            &target,
            target_type,
            excess,
            flags,
        );
    }

    let source_names = plan
        .properties
        .iter()
        .map(|property| property.name.as_ref())
        .collect::<HashSet<_>>();
    let mut missing = Vec::new();
    let mut prototype_properties = Vec::new();
    for property in target.properties() {
        if !property.optional && !source_names.contains(&property.name.as_ref()) {
            if let Some(source_property) =
                store.global_object_property_symbol(property.name.as_ref())?
            {
                prototype_properties.push((source_property, property));
            } else {
                missing.push(property);
            }
        }
    }
    if !missing.is_empty() {
        return missing_property_diagnostic(
            store,
            host,
            global_types,
            source_type,
            target_type,
            fallback_node,
            &missing,
            flags,
        );
    }

    let mut diagnostic = generic_assignability_diagnostic(
        store,
        host,
        global_types,
        source_type,
        target_type,
        fallback_node,
        flags,
        options,
    )?;
    if diagnostic.diagnostic.details.is_empty() {
        for (source_property, target_property) in prototype_properties {
            let details = prototype_method_return_details(
                store,
                host,
                global_types,
                source_property,
                target_property,
                flags,
                options,
            )?;
            if !details.is_empty() {
                diagnostic.diagnostic.details = details;
                break;
            }
        }
    }
    Ok(diagnostic)
}

fn prototype_method_return_details(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    global_types: &CanonicalGlobalTypes,
    source_property: ts_binder::semantic::SemanticSymbolId,
    target_property: &ResolvedDeclaredProperty,
    flags: CanonicalTypeFormatFlags,
    options: CanonicalCheckerOptions,
) -> Result<Vec<String>, SourceCheckError> {
    for symbol in [source_property, target_property.symbol] {
        if !store
            .symbol(symbol)
            .ok_or(RelationUnavailable::Symbol(symbol))?
            .flags()
            .contains(SymbolFlags::METHOD)
        {
            return Ok(Vec::new());
        }
    }
    let source_type = store
        .value_symbol_links(source_property)
        .and_then(|links| links.resolved_type)
        .ok_or(RelationUnavailable::UnresolvedPropertyType(source_property))?;
    let mut return_types = Vec::with_capacity(2);
    for type_ in [source_type, target_property.type_] {
        let callable = match validate_stored_single_callable(store, type_) {
            StoredSingleCallableValidation::Valid { callable, .. } => callable,
            StoredSingleCallableValidation::NotCallable
            | StoredSingleCallableValidation::Pending { .. } => return Ok(Vec::new()),
            StoredSingleCallableValidation::Malformed { .. } => {
                return Err(invalid_structure(type_));
            }
        };
        if !callable.parameters.is_empty()
            || store
                .signature(callable.signature)
                .is_none_or(|signature| !signature.type_parameters().is_empty())
        {
            return Ok(Vec::new());
        }
        return_types.push(callable.return_type.ok_or(
            RelationUnavailable::UnresolvedSignatureReturn(callable.signature),
        )?);
    }
    let [source_return, target_return] = return_types.as_slice() else {
        unreachable!("a prototype method comparison has exactly two signatures")
    };
    // Methods that return a value can match methods that return void.
    if store.is_type_assignable_to_with_global_types_and_strict_function_types(
        source_type,
        target_property.type_,
        global_types,
        options.strict_function_types,
    )? || store.is_type_assignable_to_with_global_types_and_strict_function_types(
        *source_return,
        *target_return,
        global_types,
        options.strict_function_types,
    )? {
        return Ok(Vec::new());
    }
    let message = Diagnostic::with_arguments(
        message_by_code(2201).ok_or(SourceCheckError::MissingDiagnostic(2201))?,
        [format!("{}()", property_name(target_property)?)],
    )
    .render()
    .expect("TS2201 has one property-call argument");
    Ok(vec![
        format!("  {message}"),
        nested_assignability_message(
            store,
            host,
            global_types,
            *source_return,
            *target_return,
            flags,
            2,
        )?,
    ])
}

fn first_excess_property<'source>(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    source: &'source PropertyObjectPlan,
    target: &ResolvedDeclaredPropertyObject,
    target_type: TypeId,
) -> Result<Option<&'source super::object_members::PlannedProperty>, SourceCheckError> {
    let index = declared_index_target(store, host, target_type)?;
    for property in &source.properties {
        if target.get(property.name.as_ref()).is_some() {
            continue;
        }
        if let Some(index) = index
            && let Some(name) = property.name.as_utf8()
            && declared_index_accepts_name(store, index, name)?
        {
            continue;
        }
        return Ok(Some(property));
    }
    Ok(None)
}

#[allow(clippy::too_many_arguments)] // Preserve the existing immutable diagnostic inputs.
fn discriminated_union_excess_property_diagnostic(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    global_types: &CanonicalGlobalTypes,
    plan: &PropertyObjectPlan,
    properties: &[PlannedExpression],
    target_type: TypeId,
    flags: CanonicalTypeFormatFlags,
) -> Result<Option<CanonicalCheckerDiagnostic>, SourceCheckError> {
    let Some(record) = store.type_payload(target_type) else {
        return Err(RelationUnavailable::Type(target_type).into());
    };
    let TypeData::Union(union) = record.data() else {
        return Ok(None);
    };
    let constituents = union.union.types.clone();
    let mut targets = Vec::with_capacity(constituents.len());
    for constituent in constituents {
        match validate_resolved_declared_property_type_graph(store, constituent) {
            DeclaredPropertyTypeGraphValidation::Traversable(_) => {}
            DeclaredPropertyTypeGraphValidation::Opaque => return Ok(None),
            DeclaredPropertyTypeGraphValidation::Malformed => {
                return Err(invalid_structure(constituent));
            }
        }
        let Some(target) = store.resolved_declared_property_object(host, constituent)? else {
            return Ok(None);
        };
        targets.push((constituent, target));
    }
    if targets.len() < 2 {
        return Ok(None);
    }

    let mut included = vec![true; targets.len()];
    for (source_property, expression) in plan.properties.iter().zip(properties) {
        let Some(source_type) = literal_discriminant_type(store, expression) else {
            continue;
        };
        let name =
            source_property
                .name
                .as_utf8()
                .ok_or(RelationUnavailable::UnsupportedProperty(
                    source_property.symbol,
                ))?;
        if !is_discriminant_property(store, &targets, name)? {
            continue;
        }

        let mut matched = false;
        let mut mismatched = Vec::new();
        for (index, (_, target)) in targets.iter().enumerate() {
            if !included[index] {
                continue;
            }
            let Some(property) = target.get(source_property.name.as_ref()) else {
                continue;
            };
            if store.is_type_assignable_to_with_global_types(
                source_type,
                property.type_,
                global_types,
            )? {
                matched = true;
            } else {
                mismatched.push(index);
            }
        }
        if matched {
            for index in mismatched {
                included[index] = false;
            }
        }
    }

    let mut selected = targets
        .iter()
        .zip(included)
        .filter_map(|(target, included)| included.then_some(target));
    let Some((selected_type, selected_target)) = selected.next() else {
        return Ok(None);
    };
    if selected.next().is_some() {
        return Ok(None);
    }
    let Some(excess) = first_excess_property(store, host, plan, selected_target, *selected_type)?
    else {
        return Ok(None);
    };

    excess_property_diagnostic(
        store,
        host,
        global_types,
        selected_target,
        *selected_type,
        excess,
        flags,
    )
    .map(Some)
}

fn literal_discriminant_type(
    store: &CanonicalTypeMapperStore,
    expression: &PlannedExpression,
) -> Option<TypeId> {
    let expression = expression.unparenthesized();
    if !matches!(
        expression.kind,
        PlannedExpressionKind::String(_)
            | PlannedExpressionKind::Number { .. }
            | PlannedExpressionKind::BigInt { .. }
            | PlannedExpressionKind::Boolean(_)
            | PlannedExpressionKind::Null
            | PlannedExpressionKind::GlobalUndefined
    ) {
        return None;
    }
    let type_ = store.type_node_links(expression.node)?.resolved_type?;
    store
        .type_payload(type_)
        .filter(|record| record.flags().intersects(TypeFlags::UNIT))
        .map(|_| type_)
}

fn is_discriminant_property(
    store: &CanonicalTypeMapperStore,
    targets: &[(TypeId, ResolvedDeclaredPropertyObject)],
    name: &str,
) -> Result<bool, SourceCheckError> {
    let mut first_type = None;
    let mut first_symbol = None;
    let mut non_uniform = false;
    let mut distinct_symbols = false;
    let mut literal = false;
    for (_, target) in targets {
        let Some(property) = target.get_source(name) else {
            continue;
        };
        let record = store
            .type_payload(property.type_)
            .ok_or(RelationUnavailable::Type(property.type_))?;
        literal |= record
            .flags()
            .intersects(TypeFlags::UNIT | TypeFlags::BOOLEAN);
        if let Some(first) = first_type {
            non_uniform |= first != property.type_;
        } else {
            first_type = Some(property.type_);
        }
        if let Some(first) = first_symbol {
            distinct_symbols |= first != property.symbol;
        } else {
            first_symbol = Some(property.symbol);
        }
    }
    Ok(non_uniform && distinct_symbols && literal)
}

fn excess_property_diagnostic(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    global_types: &CanonicalGlobalTypes,
    target: &ResolvedDeclaredPropertyObject,
    target_type: TypeId,
    excess: &super::object_members::PlannedProperty,
    flags: CanonicalTypeFormatFlags,
) -> Result<CanonicalCheckerDiagnostic, SourceCheckError> {
    let target_display = type_to_string_with_host_global_types_and_flags(
        store,
        host,
        global_types,
        target_type,
        flags,
    )?;
    let name = excess
        .name
        .as_utf8()
        .ok_or(RelationUnavailable::UnsupportedProperty(excess.symbol))?;
    let suggestion = get_spelling_suggestion(
        name,
        target.properties().iter().enumerate(),
        |candidate| candidate.1.name.as_utf8(),
        |left, right| left.0.cmp(&right.0),
    )
    .and_then(|(_, property)| property.name.as_utf8())
    .map(str::to_owned);
    match suggestion {
        Some(suggestion) => primary(
            2561,
            excess.name_node,
            vec![name.to_owned(), target_display, suggestion],
        ),
        None => primary(
            2353,
            excess.name_node,
            vec![name.to_owned(), target_display],
        ),
    }
}

/// Builds an excess-property diagnostic for an authenticated fresh call argument.
pub(super) fn excess_object_argument_diagnostic(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    global_types: &CanonicalGlobalTypes,
    argument: &PlannedExpression,
    source_type: TypeId,
    target_type: TypeId,
    flags: CanonicalTypeFormatFlags,
) -> Result<Option<CanonicalCheckerDiagnostic>, SourceCheckError> {
    let argument = argument.unparenthesized();
    let PlannedExpressionKind::Object { plan, properties } = &argument.kind else {
        return Ok(None);
    };
    if argument.node != plan.node
        || !plan.spreads.is_empty()
        || properties.len() != plan.properties.len()
        || properties
            .iter()
            .zip(&plan.properties)
            .any(|(expression, property)| expression.node != property.type_node)
    {
        return Err(invalid_structure(source_type));
    }
    let state = super::object_members::object_literal_state(store, plan)
        .map_err(|_| invalid_structure(source_type))?
        .ok_or_else(|| invalid_structure(source_type))?;
    if state.type_id() != source_type || !state.is_resolved() {
        return Err(invalid_structure(source_type));
    }
    let Some(target) = store.resolved_declared_property_object(host, target_type)? else {
        return Ok(None);
    };
    let Some(excess) = first_excess_property(store, host, plan, &target, target_type)? else {
        return Ok(None);
    };
    excess_property_diagnostic(
        store,
        host,
        global_types,
        &target,
        target_type,
        excess,
        flags,
    )
    .map(Some)
}

/// Reports the missing string index of the canonical unknown-derived empty object.
pub(super) fn missing_mapped_index_signature_details(
    store: &CanonicalTypeMapperStore,
    source_type: TypeId,
    target_type: TypeId,
) -> Result<Vec<String>, SourceCheckError> {
    let bootstrap = store
        .intrinsic_bootstrap()
        .ok_or(RelationUnavailable::MissingBootstrap)?;
    if source_type != bootstrap.unknown_empty_object_type {
        return Ok(Vec::new());
    }

    let source = store
        .type_payload(source_type)
        .ok_or_else(|| invalid_structure(source_type))?;
    let TypeData::Object(object) = source.data() else {
        return Err(invalid_structure(source_type));
    };
    if source.flags() != TypeFlags::OBJECT
        || source.object_flags() != ObjectFlags::ANONYMOUS | ObjectFlags::MEMBERS_RESOLVED
        || source.symbol().is_some()
        || source.alias().is_some()
        || object.target.is_some()
        || object.mapper.is_some()
        || object.instantiations != TypeCacheState::Unallocated
        || object.structured != StructuredTypeData::default()
    {
        return Err(invalid_structure(source_type));
    }

    let target = store
        .type_payload(target_type)
        .ok_or_else(|| invalid_structure(target_type))?;
    let TypeData::Mapped(mapped) = target.data() else {
        return Ok(Vec::new());
    };
    let Some(identity) = target.alias().and_then(|alias| store.type_alias(alias)) else {
        return Ok(Vec::new());
    };
    let Some(alias) = identity.symbol() else {
        return Err(invalid_structure(target_type));
    };
    let global_alias = store
        .symbol_table(bootstrap.globals)
        .and_then(|globals| globals.get_source("Record"))
        .and_then(|global| store.get_merged_symbol(global));
    if global_alias != Some(alias) {
        return Ok(Vec::new());
    }
    if store
        .symbol(alias)
        .is_none_or(|record| record.flags() != SymbolFlags::TYPE_ALIAS)
    {
        return Err(invalid_structure(target_type));
    }
    let Some(arguments) = identity.type_arguments() else {
        return Err(invalid_structure(target_type));
    };
    if arguments != [bootstrap.string_type, bootstrap.string_type] {
        return Ok(Vec::new());
    }

    let links = store
        .type_alias_links(alias)
        .ok_or_else(|| invalid_structure(target_type))?;
    let declared = links
        .declared_type
        .ok_or_else(|| invalid_structure(target_type))?;
    let parameters = links
        .type_parameters
        .as_deref()
        .ok_or_else(|| invalid_structure(target_type))?;
    store
        .validate_record_mapped_alias_instantiation(
            alias,
            declared,
            parameters,
            arguments,
            target_type,
        )
        .map_err(|_| invalid_structure(target_type))?;

    let structured = &mapped.object.structured;
    let Some(members) = structured.members else {
        return Err(invalid_structure(target_type));
    };
    let Some(table) = store.symbol_table(members) else {
        return Err(invalid_structure(target_type));
    };
    let Some([index]) = structured.index_infos.as_deref() else {
        return Err(invalid_structure(target_type));
    };
    let Some(index) = store.index_info(*index) else {
        return Err(invalid_structure(target_type));
    };
    if !target
        .object_flags()
        .contains(ObjectFlags::MEMBERS_RESOLVED)
        || !table.is_empty()
        || structured.properties.is_some()
        || structured.signatures.is_some()
        || structured.call_signature_count != 0
        || structured
            .object_type_without_abstract_construct_signatures
            .is_some()
        || index.key_type() != bootstrap.string_type
        || index.value_type() != bootstrap.string_type
        || index.is_readonly()
        || index.declaration().is_some()
        || index.index_symbol().is_some()
        || !index.components().is_empty()
    {
        return Err(invalid_structure(target_type));
    }

    let detail = Diagnostic::with_arguments(
        message_by_code(2329).ok_or(SourceCheckError::MissingDiagnostic(2329))?,
        ["string", "{}"],
    )
    .render()
    .expect("TS2329 has two formatting arguments");
    Ok(vec![format!("  {detail}")])
}

/// Explains required constructor arguments from authenticated signature records.
fn constructor_assignability_details(
    store: &CanonicalTypeMapperStore,
    source_type: TypeId,
    target_type: TypeId,
    strict_function_types: bool,
) -> Result<Vec<String>, SourceCheckError> {
    let Some((required, available)) =
        store.constructor_arity_mismatch(source_type, target_type, strict_function_types)?
    else {
        return Ok(Vec::new());
    };
    let detail = Diagnostic::with_arguments(
        message_by_code(2849).ok_or(SourceCheckError::MissingDiagnostic(2849))?,
        [required.to_string(), available.to_string()],
    )
    .render()
    .expect("TS2849 has two formatting arguments");
    Ok(vec![format!("  {detail}")])
}

/// Explains incompatible required callable parameters, arity, or return types.
pub(super) fn callable_assignability_details(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    global_types: &CanonicalGlobalTypes,
    source_type: TypeId,
    target_type: TypeId,
    flags: CanonicalTypeFormatFlags,
    options: CanonicalCheckerOptions,
) -> Result<Vec<String>, SourceCheckError> {
    let source_callable = match validate_stored_single_callable(store, source_type) {
        StoredSingleCallableValidation::Valid { callable, .. } => callable,
        StoredSingleCallableValidation::NotCallable
        | StoredSingleCallableValidation::Pending { .. } => return Ok(Vec::new()),
        StoredSingleCallableValidation::Malformed { .. } => {
            return Err(invalid_structure(source_type));
        }
    };
    let target_callable = match validate_stored_single_callable(store, target_type) {
        StoredSingleCallableValidation::Valid { callable, .. } => callable,
        StoredSingleCallableValidation::NotCallable
        | StoredSingleCallableValidation::Pending { .. } => return Ok(Vec::new()),
        StoredSingleCallableValidation::Malformed { .. } => {
            return Err(invalid_structure(target_type));
        }
    };
    let source = single_callable_display_projection(store, host, source_type, Some(global_types))
        .map_err(|_| invalid_structure(source_type))?;
    let target = single_callable_display_projection(store, host, target_type, Some(global_types))
        .map_err(|_| invalid_structure(target_type))?;
    let (Some(source), Some(target)) = (source, target) else {
        return Ok(Vec::new());
    };
    if source_callable.owner != source_type
        || target_callable.owner != target_type
        || source.owner != source_type
        || target.owner != target_type
        || source_callable.rest_parameter.is_some()
        || target_callable.rest_parameter.is_some()
        || source_callable.parameters.len() != source.parameters.len()
        || target_callable.parameters.len() != target.parameters.len()
        || source
            .parameters
            .iter()
            .zip(&source_callable.parameters)
            .any(|(display, semantic)| display.optional || display.value_type != *semantic)
        || target
            .parameters
            .iter()
            .zip(&target_callable.parameters)
            .any(|(display, semantic)| display.optional || display.value_type != *semantic)
        || source_callable.min_argument_count > source.parameters.len()
        || target_callable.min_argument_count > target.parameters.len()
        || source.return_type != source_callable.return_type
        || target.return_type != target_callable.return_type
    {
        return Ok(Vec::new());
    }

    match (source.parameters.as_slice(), target.parameters.as_slice()) {
        (source_parameters, []) if target_callable.min_argument_count == 0 => {
            if source_callable.min_argument_count > 0 {
                let detail = Diagnostic::with_arguments(
                    message_by_code(2849).ok_or(SourceCheckError::MissingDiagnostic(2849))?,
                    [
                        source_callable.min_argument_count.to_string(),
                        target_callable.parameters.len().to_string(),
                    ],
                )
                .render()
                .expect("TS2849 has two formatting arguments");
                return Ok(vec![format!("  {detail}")]);
            }
            if !source_parameters.is_empty() {
                return Ok(Vec::new());
            }
        }
        ([source_parameter], [target_parameter])
            if source_callable.min_argument_count == 1
                && target_callable.min_argument_count == 1 =>
        {
            let contravariant = store
                .is_type_assignable_to_with_global_types_and_strict_function_types(
                    target_parameter.value_type,
                    source_parameter.value_type,
                    global_types,
                    options.strict_function_types,
                )?;
            let parameter_compatible = contravariant
                || !options.strict_function_types
                    && store.is_type_assignable_to_with_global_types_and_strict_function_types(
                        source_parameter.value_type,
                        target_parameter.value_type,
                        global_types,
                        options.strict_function_types,
                    )?;
            if !parameter_compatible {
                let detail = Diagnostic::with_arguments(
                    message_by_code(2328).ok_or(SourceCheckError::MissingDiagnostic(2328))?,
                    [
                        source_parameter.name.as_str(),
                        target_parameter.name.as_str(),
                    ],
                )
                .render()
                .expect("TS2328 has two formatting arguments");
                return Ok(vec![
                    format!("  {detail}"),
                    nested_assignability_message(
                        store,
                        host,
                        global_types,
                        target_parameter.value_type,
                        source_parameter.value_type,
                        flags,
                        2,
                    )?,
                ]);
            }
        }
        _ => return Ok(Vec::new()),
    }

    let source_return =
        source_callable
            .return_type
            .ok_or(RelationUnavailable::UnresolvedSignatureReturn(
                source_callable.signature,
            ))?;
    let target_return =
        target_callable
            .return_type
            .ok_or(RelationUnavailable::UnresolvedSignatureReturn(
                target_callable.signature,
            ))?;
    if store.is_type_assignable_to_with_global_types_and_strict_function_types(
        source_return,
        target_return,
        global_types,
        options.strict_function_types,
    )? {
        return Ok(Vec::new());
    }

    Ok(vec![nested_assignability_message(
        store,
        host,
        global_types,
        source_return,
        target_return,
        flags,
        1,
    )?])
}

#[allow(clippy::too_many_arguments)] // The complete diagnostic record is built transactionally.
fn missing_property_diagnostic(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    global_types: &CanonicalGlobalTypes,
    source_type: TypeId,
    target_type: TypeId,
    fallback_node: NodeRef,
    missing: &[&ResolvedDeclaredProperty],
    flags: CanonicalTypeFormatFlags,
) -> Result<CanonicalCheckerDiagnostic, SourceCheckError> {
    let AssignabilityErrorDisplay { source, target } =
        get_type_names_for_assignability_error_with_host_global_types_and_flags(
            store,
            host,
            global_types,
            source_type,
            target_type,
            flags,
        )?;
    if let [property] = missing {
        let name = property_name(property)?.to_owned();
        let mut diagnostic = primary(2741, fallback_node, vec![name.clone(), source, target])?;
        diagnostic.related_information.push(related(
            2728,
            declared_property_name_node(host, target_type, property)?,
            vec![name],
        )?);
        return Ok(diagnostic);
    }

    let names = missing
        .iter()
        .map(|property| property_name(property))
        .collect::<Result<Vec<_>, _>>()?;
    if names.len() > 5 {
        primary(
            2740,
            fallback_node,
            vec![
                source,
                target,
                names[..4].join(", "),
                (names.len() - 4).to_string(),
            ],
        )
    } else {
        primary(2739, fallback_node, vec![source, target, names.join(", ")])
    }
}

/// Reports required target properties absent from another declared object.
pub(super) fn missing_declared_property_diagnostic(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    global_types: &CanonicalGlobalTypes,
    source_type: TypeId,
    target_type: TypeId,
    fallback_node: NodeRef,
    flags: CanonicalTypeFormatFlags,
) -> Result<Option<CanonicalCheckerDiagnostic>, SourceCheckError> {
    for type_ in [source_type, target_type] {
        match validate_resolved_declared_property_type_graph(store, type_) {
            DeclaredPropertyTypeGraphValidation::Traversable(_) => {}
            DeclaredPropertyTypeGraphValidation::Opaque => return Ok(None),
            DeclaredPropertyTypeGraphValidation::Malformed => {
                return Err(invalid_structure(type_));
            }
        }
    }

    let source = store
        .resolved_declared_property_object(host, source_type)?
        .ok_or_else(|| invalid_structure(source_type))?;
    let target = store
        .resolved_declared_property_object(host, target_type)?
        .ok_or_else(|| invalid_structure(target_type))?;
    let mut missing = Vec::new();
    for property in target.properties() {
        if !property.optional && source.get_source(property_name(property)?).is_none() {
            missing.push(property);
        }
    }
    if missing.is_empty() {
        return Ok(None);
    }

    missing_property_diagnostic(
        store,
        host,
        global_types,
        source_type,
        target_type,
        fallback_node,
        &missing,
        flags,
    )
    .map(Some)
}

#[allow(clippy::too_many_arguments)]
fn generic_assignability_diagnostic(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    global_types: &CanonicalGlobalTypes,
    source_type: TypeId,
    target_type: TypeId,
    node: NodeRef,
    flags: CanonicalTypeFormatFlags,
    options: CanonicalCheckerOptions,
) -> Result<CanonicalCheckerDiagnostic, SourceCheckError> {
    let AssignabilityErrorDisplay { source, target } =
        get_type_names_for_assignability_error_with_host_global_types_and_flags(
            store,
            host,
            global_types,
            source_type,
            target_type,
            flags,
        )?;
    let mut diagnostic = primary(2322, node, vec![source, target])?;
    diagnostic.diagnostic.details = if let Some(details) = tuple_rest_parameter_mismatch_details(
        store,
        host,
        global_types,
        source_type,
        target_type,
        flags,
        options,
    )? {
        details
    } else {
        declared_property_mismatch_details(
            store,
            host,
            global_types,
            source_type,
            target_type,
            flags,
            options,
        )?
    };
    if diagnostic.diagnostic.details.is_empty() {
        diagnostic.diagnostic.details = constructor_assignability_details(
            store,
            source_type,
            target_type,
            options.strict_function_types,
        )?;
    }
    Ok(diagnostic)
}

fn tuple_rest_parameter_mismatch_details(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    global_types: &CanonicalGlobalTypes,
    source_type: TypeId,
    target_type: TypeId,
    flags: CanonicalTypeFormatFlags,
    options: CanonicalCheckerOptions,
) -> Result<Option<Vec<String>>, SourceCheckError> {
    if !options.strict_function_types
        || !matches!(
            validate_stored_function_type(store, source_type),
            StoredFunctionTypeValidation::Valid(_)
        )
        || !matches!(
            validate_stored_function_type(store, target_type),
            StoredFunctionTypeValidation::Valid(_)
        )
    {
        return Ok(None);
    }

    let array_targets = Some(CanonicalArrayTargets::from_global_types(global_types));
    let source = function_type_display_projection(store, host, source_type, array_targets)
        .map_err(|_| invalid_structure(source_type))?;
    let target = function_type_display_projection(store, host, target_type, array_targets)
        .map_err(|_| invalid_structure(target_type))?;
    let [source_parameter] = source.parameters.as_slice() else {
        return Ok(None);
    };
    let [target_parameter] = target.parameters.as_slice() else {
        return Ok(None);
    };
    if source_parameter.optional
        || target_parameter.optional
        || !is_terminal_scalar_relation_leaf(store, source_parameter.value_type)
        || !is_terminal_scalar_relation_leaf(store, target_parameter.value_type)
        || !valid_labeled_tuple_rest_parameter(
            store,
            host,
            target_type,
            &target_parameter.name,
            target_parameter.value_type,
        )?
        || store.is_type_assignable_to_with_global_types_and_strict_function_types(
            target_parameter.value_type,
            source_parameter.value_type,
            global_types,
            options.strict_function_types,
        )?
    {
        return Ok(None);
    }

    let parameter_message = Diagnostic::with_arguments(
        message_by_code(2328).ok_or(SourceCheckError::MissingDiagnostic(2328))?,
        [
            source_parameter.name.as_str(),
            target_parameter.name.as_str(),
        ],
    )
    .render()
    .expect("TS2328 has two formatting arguments");
    let AssignabilityErrorDisplay { source, target } =
        get_type_names_for_assignability_error_with_host_global_types_and_flags(
            store,
            host,
            global_types,
            target_parameter.value_type,
            source_parameter.value_type,
            flags,
        )?;
    let type_message = Diagnostic::with_arguments(
        message_by_code(2322).ok_or(SourceCheckError::MissingDiagnostic(2322))?,
        [source, target],
    )
    .render()
    .expect("TS2322 has two formatting arguments");
    Ok(Some(vec![
        format!("  {parameter_message}"),
        format!("    {type_message}"),
    ]))
}

fn valid_labeled_tuple_rest_parameter(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    type_id: TypeId,
    expected_name: &str,
    expected_type: TypeId,
) -> Result<bool, SourceCheckError> {
    let signature =
        exact_function_type_signature(store, type_id).ok_or_else(|| invalid_structure(type_id))?;
    let signature = store
        .signature(signature)
        .ok_or_else(|| invalid_structure(type_id))?;
    let declaration = signature
        .declaration()
        .ok_or_else(|| invalid_structure(type_id))?;
    let function = host
        .node(declaration)
        .ok_or_else(|| invalid_structure(type_id))?;
    let NodeData::FunctionTypeNode(function) = &function.data else {
        return Err(invalid_structure(type_id));
    };
    let [parameter] = function.parameters.nodes.as_slice() else {
        return Ok(false);
    };
    let parameter = NodeRef::new(declaration.arena, declaration.file, *parameter);
    let parameter_node = host
        .node(parameter)
        .ok_or_else(|| invalid_structure(type_id))?;
    let NodeData::ParameterDeclaration(parameter_data) = &parameter_node.data else {
        return Err(invalid_structure(type_id));
    };
    if parameter_data.dot_dot_dot_token.is_none() {
        return Ok(false);
    }
    let tuple = parameter_data
        .type_
        .map(|node| NodeRef::new(parameter.arena, parameter.file, node))
        .ok_or_else(|| invalid_structure(type_id))?;
    let tuple_node = host.node(tuple).ok_or_else(|| invalid_structure(type_id))?;
    let NodeData::TupleTypeNode(tuple_data) = &tuple_node.data else {
        return Err(invalid_structure(type_id));
    };
    let [element] = tuple_data.elements.nodes.as_slice() else {
        return Err(invalid_structure(type_id));
    };
    let element = NodeRef::new(tuple.arena, tuple.file, *element);
    let element_node = host
        .node(element)
        .ok_or_else(|| invalid_structure(type_id))?;
    let NodeData::NamedTupleMember(member) = &element_node.data else {
        return Err(invalid_structure(type_id));
    };
    let name = NodeRef::new(element.arena, element.file, member.name);
    let name_node = host.node(name).ok_or_else(|| invalid_structure(type_id))?;
    let NodeData::Identifier(name) = &name_node.data else {
        return Err(invalid_structure(type_id));
    };
    let annotation = NodeRef::new(element.arena, element.file, member.type_);
    if parameter_node.parent != Some(declaration.node)
        || tuple_node.parent != Some(parameter.node)
        || element_node.parent != Some(tuple.node)
        || name_node.parent != Some(element.node)
        || name.text != expected_name
        || store
            .type_node_links(annotation)
            .and_then(|links| links.resolved_type)
            .is_some_and(|cached| cached != expected_type)
    {
        return Err(invalid_structure(type_id));
    }
    Ok(true)
}

pub(super) fn declared_property_mismatch_details(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    global_types: &CanonicalGlobalTypes,
    source_type: TypeId,
    target_type: TypeId,
    flags: CanonicalTypeFormatFlags,
    options: CanonicalCheckerOptions,
) -> Result<Vec<String>, SourceCheckError> {
    recursive_declared_property_mismatch_details(
        store,
        host,
        global_types,
        source_type,
        target_type,
        flags,
        options,
        1,
        &mut HashSet::new(),
    )
    .map(Option::unwrap_or_default)
}

fn diagnostic_properties(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    type_: TypeId,
) -> Result<Option<Vec<ResolvedDeclaredProperty>>, SourceCheckError> {
    match validate_class_heritage_members(store, type_) {
        ClassHeritageMembersValidation::Malformed => return Err(invalid_structure(type_)),
        ClassHeritageMembersValidation::Valid => {
            let properties = store
                .type_payload(type_)
                .and_then(|record| record.data().structured())
                .ok_or_else(|| invalid_structure(type_))?
                .properties
                .as_deref()
                .unwrap_or_default();
            let mut result = Vec::with_capacity(properties.len());
            for property in properties {
                let record = store
                    .symbol(*property)
                    .ok_or_else(|| invalid_structure(type_))?;
                if record.name().is_private_identifier() {
                    return Ok(None);
                }
                result.push(ResolvedDeclaredProperty {
                    symbol: *property,
                    name: record.name().to_owned(),
                    type_: store
                        .value_symbol_links(*property)
                        .and_then(|links| links.resolved_type)
                        .ok_or_else(|| invalid_structure(type_))?,
                    optional: record.flags().contains(SymbolFlags::OPTIONAL),
                    declaration: record
                        .value_declaration()
                        .ok_or_else(|| invalid_structure(type_))?,
                });
            }
            return Ok(Some(result));
        }
        ClassHeritageMembersValidation::NotClass => {}
    }
    match validate_resolved_declared_property_type_graph(store, type_) {
        DeclaredPropertyTypeGraphValidation::Traversable(_) => {}
        DeclaredPropertyTypeGraphValidation::Opaque => return Ok(None),
        DeclaredPropertyTypeGraphValidation::Malformed => return Err(invalid_structure(type_)),
    }
    store
        .resolved_declared_property_object(host, type_)?
        .map(|properties| properties.properties().to_vec())
        .ok_or_else(|| invalid_structure(type_))
        .map(Some)
}

fn diagnostic_property_visibility(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
    property: &ResolvedDeclaredProperty,
) -> Result<(ClassConstructorVisibility, Option<TypeId>), SourceCheckError> {
    if validate_class_heritage_members(store, type_) != ClassHeritageMembersValidation::Valid {
        return Ok((ClassConstructorVisibility::Public, None));
    }
    let declaring_class = store
        .symbol(property.symbol)
        .and_then(ts_binder::semantic::Symbol::parent)
        .and_then(|owner| store.declared_type_links(owner))
        .and_then(|links| links.declared_type)
        .ok_or_else(|| invalid_structure(type_))?;
    Ok((
        class_member_visibility(store, property.declaration),
        Some(declaring_class),
    ))
}

#[allow(clippy::too_many_arguments)] // Keeps property and containing-type identities separate.
pub(super) fn property_visibility_mismatch_detail(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    global_types: &CanonicalGlobalTypes,
    source_type: TypeId,
    target_type: TypeId,
    source_property: &ResolvedDeclaredProperty,
    target_property: &ResolvedDeclaredProperty,
    flags: CanonicalTypeFormatFlags,
    indentation: usize,
) -> Result<Option<String>, SourceCheckError> {
    let (source_visibility, source_class) =
        diagnostic_property_visibility(store, source_type, source_property)?;
    let (target_visibility, target_class) =
        diagnostic_property_visibility(store, target_type, target_property)?;
    let name = property_name(target_property)?.to_owned();
    let display = |type_| {
        type_to_string_with_host_global_types_and_flags(store, host, global_types, type_, flags)
    };
    let (code, arguments) = if source_visibility == ClassConstructorVisibility::Private
        || target_visibility == ClassConstructorVisibility::Private
    {
        if source_property.declaration == target_property.declaration {
            return Ok(None);
        }
        if source_visibility == ClassConstructorVisibility::Private
            && target_visibility == ClassConstructorVisibility::Private
        {
            (2442, vec![name])
        } else {
            let (private_type, other_type) =
                if source_visibility == ClassConstructorVisibility::Private {
                    (source_type, target_type)
                } else {
                    (target_type, source_type)
                };
            (
                2325,
                vec![name, display(private_type)?, display(other_type)?],
            )
        }
    } else if target_visibility == ClassConstructorVisibility::Protected {
        if let (Some(source_class), Some(target_class)) = (source_class, target_class)
            && validated_class_derives_from(store, source_class, target_class)
                .ok_or_else(|| invalid_structure(source_class))?
        {
            return Ok(None);
        }
        (
            2443,
            vec![
                name,
                display(source_class.unwrap_or(source_type))?,
                display(target_class.unwrap_or(target_type))?,
            ],
        )
    } else if source_visibility == ClassConstructorVisibility::Protected {
        (
            2444,
            vec![name, display(source_type)?, display(target_type)?],
        )
    } else {
        return Ok(None);
    };
    let detail = Diagnostic::with_arguments(
        message_by_code(code).ok_or(SourceCheckError::MissingDiagnostic(code))?,
        arguments,
    )
    .render()
    .expect("visibility diagnostics retain their catalog arguments");
    Ok(Some(format!("{}{detail}", "  ".repeat(indentation))))
}

#[allow(clippy::too_many_arguments)] // Keep recursive relation identity and formatting explicit.
fn recursive_declared_property_mismatch_details(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    global_types: &CanonicalGlobalTypes,
    source_type: TypeId,
    target_type: TypeId,
    flags: CanonicalTypeFormatFlags,
    options: CanonicalCheckerOptions,
    indentation: usize,
    active: &mut HashSet<(TypeId, TypeId)>,
) -> Result<Option<Vec<String>>, SourceCheckError> {
    if active.len() >= 64 || !active.insert((source_type, target_type)) {
        return Ok(None);
    }

    let result = recursive_declared_property_mismatch_details_inner(
        store,
        host,
        global_types,
        source_type,
        target_type,
        flags,
        options,
        indentation,
        active,
    );
    assert!(active.remove(&(source_type, target_type)));
    result
}

#[allow(clippy::too_many_arguments)] // Keep recursive relation identity and formatting explicit.
fn recursive_declared_property_mismatch_details_inner(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    global_types: &CanonicalGlobalTypes,
    source_type: TypeId,
    target_type: TypeId,
    flags: CanonicalTypeFormatFlags,
    options: CanonicalCheckerOptions,
    indentation: usize,
    active: &mut HashSet<(TypeId, TypeId)>,
) -> Result<Option<Vec<String>>, SourceCheckError> {
    let Some(source) = diagnostic_properties(store, host, source_type)? else {
        return Ok(None);
    };
    let Some(target) = diagnostic_properties(store, host, target_type)? else {
        return Ok(None);
    };
    if target
        .iter()
        .any(|target| !target.optional && !source.iter().any(|source| source.name == target.name))
    {
        return Ok(None);
    }
    for target_property in &target {
        let name = property_name(target_property)?;
        let Some(source_property) = source
            .iter()
            .find(|source| source.name == target_property.name)
        else {
            continue;
        };
        if let Some(detail) = property_visibility_mismatch_detail(
            store,
            host,
            global_types,
            source_type,
            target_type,
            source_property,
            target_property,
            flags,
            indentation,
        )? {
            return Ok(Some(vec![detail]));
        }
        if store.is_type_assignable_to_with_global_types_and_strict_function_types(
            source_property.type_,
            target_property.type_,
            global_types,
            options.strict_function_types,
        )? {
            continue;
        }
        return recursive_property_mismatch_details(
            store,
            host,
            global_types,
            name,
            source_property.type_,
            target_property.type_,
            flags,
            options,
            indentation,
            active,
        );
    }
    Ok(None)
}

#[allow(clippy::too_many_arguments)] // Each recursive edge retains its exact source and target.
fn recursive_property_mismatch_details(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    global_types: &CanonicalGlobalTypes,
    name: &str,
    source_type: TypeId,
    target_type: TypeId,
    flags: CanonicalTypeFormatFlags,
    options: CanonicalCheckerOptions,
    indentation: usize,
    active: &mut HashSet<(TypeId, TypeId)>,
) -> Result<Option<Vec<String>>, SourceCheckError> {
    let nested = if is_terminal_scalar_relation_leaf(store, source_type)
        && is_terminal_scalar_relation_leaf(store, target_type)
    {
        Vec::new()
    } else if let Some((source_element, target_element)) =
        nested_collection_element_types(store, global_types, source_type, target_type)?
    {
        if store.is_type_assignable_to_with_global_types_and_strict_function_types(
            source_element,
            target_element,
            global_types,
            options.strict_function_types,
        )? {
            return Ok(None);
        }

        let tail = if is_terminal_scalar_relation_leaf(store, source_element)
            && is_terminal_scalar_relation_leaf(store, target_element)
        {
            Vec::new()
        } else {
            let Some(nested) = recursive_declared_property_mismatch_details(
                store,
                host,
                global_types,
                source_element,
                target_element,
                flags,
                options,
                indentation + 3,
                active,
            )?
            else {
                return Ok(None);
            };
            nested
        };

        let mut nested = vec![nested_assignability_message(
            store,
            host,
            global_types,
            source_element,
            target_element,
            flags,
            indentation + 2,
        )?];
        nested.extend(tail);
        nested
    } else {
        let Some(nested) = recursive_declared_property_mismatch_details(
            store,
            host,
            global_types,
            source_type,
            target_type,
            flags,
            options,
            indentation + 2,
            active,
        )?
        else {
            return Ok(None);
        };
        nested
    };

    let property_message = Diagnostic::with_arguments(
        message_by_code(2326).ok_or(SourceCheckError::MissingDiagnostic(2326))?,
        [name],
    )
    .render()
    .expect("TS2326 has one formatting argument");
    let mut details = vec![format!("{}{property_message}", "  ".repeat(indentation))];
    details.push(nested_assignability_message(
        store,
        host,
        global_types,
        source_type,
        target_type,
        flags,
        indentation + 1,
    )?);
    details.extend(nested);
    Ok(Some(details))
}

fn nested_collection_element_types(
    store: &CanonicalTypeMapperStore,
    global_types: &CanonicalGlobalTypes,
    source_type: TypeId,
    target_type: TypeId,
) -> Result<Option<(TypeId, TypeId)>, SourceCheckError> {
    let source_array = store.canonical_array_reference(global_types, source_type)?;
    let target_array = store.canonical_array_reference(global_types, target_type)?;
    match (source_array, target_array) {
        (Some(source), Some(target)) => {
            return Ok((source.readonly == target.readonly)
                .then_some((source.element_type, target.element_type)));
        }
        (Some(_), None) | (None, Some(_)) => return Ok(None),
        (None, None) => {}
    }

    let source_tuple = store
        .canonical_tuple_shape(source_type)
        .map_err(|_| invalid_structure(source_type))?;
    let target_tuple = store
        .canonical_tuple_shape(target_type)
        .map_err(|_| invalid_structure(target_type))?;
    let (Some(source), Some(target)) = (source_tuple, target_tuple) else {
        return Ok(None);
    };
    let ([source_element], [target_element], [source_info], [target_info]) = (
        source.element_types(),
        target.element_types(),
        source.element_infos(),
        target.element_infos(),
    ) else {
        return Ok(None);
    };
    if source.min_length() != 1
        || target.min_length() != 1
        || source.fixed_length() != 1
        || target.fixed_length() != 1
        || source.is_readonly() != target.is_readonly()
        || source_info.flags() != ElementFlags::REQUIRED
        || target_info.flags() != ElementFlags::REQUIRED
    {
        return Ok(None);
    }
    Ok(Some((*source_element, *target_element)))
}

#[allow(clippy::too_many_arguments)] // Preserve the exact source, target, and diagnostic depth.
fn nested_assignability_message(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    global_types: &CanonicalGlobalTypes,
    source_type: TypeId,
    target_type: TypeId,
    flags: CanonicalTypeFormatFlags,
    indentation: usize,
) -> Result<String, SourceCheckError> {
    let AssignabilityErrorDisplay { source, target } =
        get_type_names_for_assignability_error_with_host_global_types_and_flags(
            store,
            host,
            global_types,
            source_type,
            target_type,
            flags,
        )?;
    let message = Diagnostic::with_arguments(
        message_by_code(2322).ok_or(SourceCheckError::MissingDiagnostic(2322))?,
        [source, target],
    )
    .render()
    .expect("TS2322 has two formatting arguments");
    Ok(format!("{}{message}", "  ".repeat(indentation)))
}

/// Returns the exact property relation chain for an optional value that
/// contains `undefined` when its target property does not permit it.
#[allow(clippy::too_many_arguments)] // Call and assignment diagnostics share these exact inputs.
pub(super) fn exact_optional_property_mismatch_details(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    global_types: &CanonicalGlobalTypes,
    source_type: TypeId,
    target_type: TypeId,
    flags: CanonicalTypeFormatFlags,
) -> Result<Vec<String>, SourceCheckError> {
    let undefined = store
        .intrinsic_bootstrap()
        .map(|bootstrap| bootstrap.undefined_type)
        .ok_or(RelationUnavailable::MissingBootstrap)?;
    let source_record = store
        .type_payload(source_type)
        .ok_or(RelationUnavailable::Type(source_type))?;
    let Some(source_members) = source_record
        .data()
        .structured()
        .and_then(|structured| structured.members)
        .and_then(|members| store.symbol_table(members))
    else {
        return Ok(Vec::new());
    };
    let target_record = store
        .type_payload(target_type)
        .ok_or(RelationUnavailable::Type(target_type))?;
    let Some(target_properties) = target_record
        .data()
        .structured()
        .and_then(|structured| structured.properties.as_deref())
    else {
        return Ok(Vec::new());
    };

    for target_property in target_properties {
        let target_symbol = store
            .symbol(*target_property)
            .ok_or_else(|| invalid_structure(target_type))?;
        if !target_symbol.flags().contains(SymbolFlags::OPTIONAL) {
            continue;
        }
        let Some(source_property) = source_members.get(target_symbol.name()) else {
            continue;
        };
        let source_property_type = store
            .value_symbol_links(source_property)
            .and_then(|links| links.resolved_type)
            .ok_or_else(|| invalid_structure(source_type))?;
        let target_property_type = store
            .value_symbol_links(*target_property)
            .and_then(|links| links.resolved_type)
            .ok_or_else(|| invalid_structure(target_type))?;
        if !contains_undefined(store, source_property_type, undefined)?
            || contains_undefined(store, target_property_type, undefined)?
            || !is_terminal_scalar_relation_leaf(store, target_property_type)
        {
            continue;
        }

        let name = target_symbol
            .name()
            .as_utf8()
            .ok_or(RelationUnavailable::UnsupportedProperty(*target_property))?;
        let nested = (source_property_type != undefined).then_some(undefined);
        return scalar_property_mismatch_details(
            store,
            host,
            global_types,
            name,
            source_property_type,
            target_property_type,
            nested,
            flags,
        );
    }
    Ok(Vec::new())
}

fn contains_undefined(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
    undefined: TypeId,
) -> Result<bool, SourceCheckError> {
    if type_ == undefined {
        return Ok(true);
    }
    let record = store
        .type_payload(type_)
        .ok_or(RelationUnavailable::Type(type_))?;
    Ok(matches!(record.data(), TypeData::Union(union) if union.union.types.contains(&undefined)))
}

#[allow(clippy::too_many_arguments)] // Preserve the source, target, and nested relation identities.
fn scalar_property_mismatch_details(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    global_types: &CanonicalGlobalTypes,
    name: &str,
    source_type: TypeId,
    target_type: TypeId,
    nested_source: Option<TypeId>,
    flags: CanonicalTypeFormatFlags,
) -> Result<Vec<String>, SourceCheckError> {
    let property_message = Diagnostic::with_arguments(
        message_by_code(2326).ok_or(SourceCheckError::MissingDiagnostic(2326))?,
        [name],
    )
    .render()
    .expect("TS2326 has one formatting argument");
    let mut details = vec![format!("  {property_message}")];
    for (source, indentation) in [(source_type, "    ")]
        .into_iter()
        .chain(nested_source.map(|source| (source, "      ")))
    {
        let AssignabilityErrorDisplay { source, target } =
            get_type_names_for_assignability_error_with_host_global_types_and_flags(
                store,
                host,
                global_types,
                source,
                target_type,
                flags,
            )?;
        let message = Diagnostic::with_arguments(
            message_by_code(2322).ok_or(SourceCheckError::MissingDiagnostic(2322))?,
            [source, target],
        )
        .render()
        .expect("TS2322 has two formatting arguments");
        details.push(format!("{indentation}{message}"));
    }
    Ok(details)
}

fn is_terminal_scalar_relation_leaf(store: &CanonicalTypeMapperStore, type_: TypeId) -> bool {
    let Some(record) = store.type_payload(type_) else {
        return false;
    };
    if record.alias().is_some() || record.symbol().is_some() || !record.object_flags().is_empty() {
        return false;
    }
    match record.data() {
        TypeData::Intrinsic(_) => matches!(
            record.flags(),
            TypeFlags::STRING
                | TypeFlags::NUMBER
                | TypeFlags::BIG_INT
                | TypeFlags::BOOLEAN
                | TypeFlags::ES_SYMBOL
                | TypeFlags::NULL
                | TypeFlags::UNDEFINED
                | TypeFlags::VOID
        ),
        TypeData::Literal(_) => matches!(
            record.flags(),
            TypeFlags::STRING_LITERAL
                | TypeFlags::NUMBER_LITERAL
                | TypeFlags::BIG_INT_LITERAL
                | TypeFlags::BOOLEAN_LITERAL
        ),
        _ => false,
    }
}

#[allow(clippy::too_many_arguments)]
fn append_expected_property_related(
    diagnostic: &mut CanonicalCheckerDiagnostic,
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    global_types: &CanonicalGlobalTypes,
    target_type: TypeId,
    property: &ResolvedDeclaredProperty,
    flags: CanonicalTypeFormatFlags,
) -> Result<(), SourceCheckError> {
    let (_, bound) = host
        .source(property.declaration)
        .ok_or_else(|| invalid_structure(target_type))?;
    let facts = bound.source_facts().ok_or(SourceCheckError::Provenance(
        SourceCheckProvenanceError::MissingSourceFacts(property.declaration.file),
    ))?;
    if facts.is_default_library() {
        return Ok(());
    }
    let property_name = property_name(property)?.to_owned();
    let target_display = type_to_string_with_host_global_types_and_flags(
        store,
        host,
        global_types,
        target_type,
        flags,
    )?;
    diagnostic.related_information.push(related(
        6500,
        declared_property_name_node(host, target_type, property)?,
        vec![property_name, target_display],
    )?);
    Ok(())
}

fn primary(
    code: u32,
    node: NodeRef,
    arguments: Vec<String>,
) -> Result<CanonicalCheckerDiagnostic, SourceCheckError> {
    let message = message_by_code(code).ok_or(SourceCheckError::MissingDiagnostic(code))?;
    Ok(CanonicalCheckerDiagnostic {
        node: Some(node),
        range_override: None,
        diagnostic: Diagnostic::with_arguments(message, arguments),
        related_information: Vec::new(),
    })
}

fn related(
    code: u32,
    node: NodeRef,
    arguments: Vec<String>,
) -> Result<CanonicalCheckerRelatedInformation, SourceCheckError> {
    let message = message_by_code(code).ok_or(SourceCheckError::MissingDiagnostic(code))?;
    Ok(CanonicalCheckerRelatedInformation {
        node: Some(node),
        diagnostic: Diagnostic::with_arguments(message, arguments),
    })
}

fn property_name(property: &ResolvedDeclaredProperty) -> Result<&str, SourceCheckError> {
    property
        .name
        .as_utf8()
        .ok_or_else(|| RelationUnavailable::UnsupportedProperty(property.symbol).into())
}

fn declared_property_name_node(
    host: &DeclaredTypeHost<'_>,
    target_type: TypeId,
    property: &ResolvedDeclaredProperty,
) -> Result<NodeRef, SourceCheckError> {
    let declaration = host
        .node(property.declaration)
        .ok_or_else(|| invalid_structure(target_type))?;
    let name = match &declaration.data {
        NodeData::PropertyDeclaration(property) => property.name,
        NodeData::PropertySignatureDeclaration(property) => property.name,
        NodeData::MethodDeclaration(method) => method.name,
        NodeData::MethodSignatureDeclaration(method) => method.name,
        _ => return Err(invalid_structure(target_type)),
    };
    let name = NodeRef::new(property.declaration.arena, property.declaration.file, name);
    if host.node(name).is_some_and(|node| {
        node.kind == SyntaxKind::Identifier && matches!(node.data, NodeData::Identifier(_))
    }) {
        Ok(name)
    } else {
        Err(invalid_structure(target_type))
    }
}

fn resolved_source_property_types(
    store: &CanonicalTypeMapperStore,
    plan: &PropertyObjectPlan,
    source_type: TypeId,
) -> Result<Vec<TypeId>, SourceCheckError> {
    let state = super::object_members::object_literal_state(store, plan)
        .map_err(|_| invalid_structure(source_type))?
        .ok_or_else(|| invalid_structure(source_type))?;
    if state.type_id() != source_type {
        return Err(invalid_structure(source_type));
    }
    let (members, property_symbols) = {
        let record = store
            .type_payload(source_type)
            .ok_or(RelationUnavailable::Type(source_type))?;
        let TypeData::Object(object) = record.data() else {
            return Err(invalid_structure(source_type));
        };
        let symbols = object
            .structured
            .properties
            .as_deref()
            .unwrap_or_default()
            .to_vec();
        (object.structured.members, symbols)
    };
    if property_symbols.len() != plan.properties.len() {
        return Err(invalid_structure(source_type));
    }
    let table = members
        .and_then(|members| store.symbol_table(members))
        .ok_or_else(|| invalid_structure(source_type))?;
    let mut property_types = Vec::with_capacity(property_symbols.len());
    for (planned, symbol) in plan.properties.iter().zip(property_symbols) {
        if table.get(planned.name.as_ref()) != Some(symbol) {
            return Err(invalid_structure(source_type));
        }
        let links = store
            .value_symbol_links(symbol)
            .ok_or(RelationUnavailable::UnsupportedProperty(symbol))?;
        if links.target != Some(planned.symbol) {
            return Err(invalid_structure(source_type));
        }
        property_types.push(
            links
                .resolved_type
                .ok_or(RelationUnavailable::UnresolvedPropertyType(symbol))?,
        );
    }
    Ok(property_types)
}

fn invalid_structure(type_id: TypeId) -> SourceCheckError {
    RelationUnavailable::InvalidStructuredMembers(type_id).into()
}

#[cfg(test)]
mod tests {
    use ts_ast::FileId;
    use ts_binder::{
        CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
        EscapedName,
    };
    use ts_parser::{ParseResult, parse_source_file};

    use super::*;
    use crate::semantic::{
        CanonicalCheckerContext, IntrinsicBootstrapOptions, MappedTypeModifiers,
    };

    fn diagnostic_context(parsed: &ParseResult, file: FileId) -> CanonicalCheckerContext<'_> {
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source("\"/project/assignability-diagnostic.ts\""),
                    CanonicalSourceLanguage::TypeScript,
                    false,
                    CanonicalModuleState::Script,
                ),
            )
            .unwrap();
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
        CanonicalCheckerContext::new(
            binder.finish(),
            [(file, &parsed.arena)].into_iter().collect(),
            CanonicalCheckerOptions::default(),
        )
        .unwrap()
    }

    #[test]
    fn object_diagnostic_display_flags_preserve_type_to_string_defaults() {
        let ordinary = display_flags(CanonicalCheckerOptions::default());
        assert!(ordinary.contains(CanonicalTypeFormatFlags::TYPE_TO_STRING_DEFAULT));
        assert!(!ordinary.contains(CanonicalTypeFormatFlags::NO_TRUNCATION));

        let complete = display_flags(CanonicalCheckerOptions {
            no_error_truncation: true,
            ..CanonicalCheckerOptions::default()
        });
        assert!(complete.contains(CanonicalTypeFormatFlags::TYPE_TO_STRING_DEFAULT));
        assert!(complete.contains(CanonicalTypeFormatFlags::NO_TRUNCATION));
    }

    #[test]
    fn unknown_empty_object_reports_only_an_authenticated_record_string_index() {
        let parsed = parse_source_file(concat!(
            "type Record<K extends keyof any, T> = { [P in K]: T }; ",
            "declare let value: Record<string, string>;",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(216);
        let mut context = diagnostic_context(&parsed, file);
        context.check_source_file(file).unwrap();
        let annotation = parsed
            .arena
            .iter()
            .find_map(|(_, record)| {
                let NodeData::VariableDeclaration(variable) = &record.data else {
                    return None;
                };
                Some(NodeRef::new(parsed.arena.id(), file, variable.type_?))
            })
            .unwrap();
        let target = context.get_type_from_type_node(annotation).unwrap();
        context
            .store_mut_for_test()
            .resolve_mapped_type_members(target, MappedTypeModifiers::NONE)
            .unwrap();
        let bootstrap = context.store().intrinsic_bootstrap().unwrap();
        let source = bootstrap.unknown_empty_object_type;
        let ordinary = bootstrap.empty_object_type;

        let before = (
            context.store().type_len(),
            context.store().index_info_len(),
            context.store().relation_state_snapshot(),
        );
        assert_eq!(
            missing_mapped_index_signature_details(context.store(), source, target),
            Ok(vec![
                "  Index signature for type 'string' is missing in type '{}'.".to_owned()
            ]),
        );
        assert_eq!(
            missing_mapped_index_signature_details(context.store(), ordinary, target),
            Ok(Vec::new()),
        );
        assert_eq!(
            (
                context.store().type_len(),
                context.store().index_info_len(),
                context.store().relation_state_snapshot(),
            ),
            before,
        );

        let index = context
            .store()
            .type_payload(target)
            .and_then(|record| record.data().structured())
            .and_then(|structured| structured.index_infos.as_deref())
            .and_then(|indexes| indexes.first().copied())
            .unwrap();
        let alias = context
            .store()
            .type_payload(target)
            .and_then(super::super::type_records::TypeRecord::alias)
            .and_then(|alias| context.store().type_alias(alias))
            .and_then(super::super::type_records::TypeAlias::symbol)
            .unwrap();
        assert!(
            context
                .store_mut_for_test()
                .set_index_info_symbol(index, Some(alias))
        );
        let poisoned = context.store().relation_state_snapshot();
        assert!(matches!(
            missing_mapped_index_signature_details(context.store(), source, target),
            Err(SourceCheckError::RelationUnavailable(
                RelationUnavailable::InvalidStructuredMembers(actual)
            )) if actual == target
        ));
        assert_eq!(context.store().relation_state_snapshot(), poisoned);
    }

    #[test]
    fn callable_argument_details_distinguish_parameter_and_return_mismatches() {
        let parsed = parse_source_file(concat!(
            "const wrongParameter = (s: string) => {}; ",
            "const wrongReturn = (n: number) => {}; ",
            "declare let target: (n: number) => number;",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(217);
        let mut context = diagnostic_context(&parsed, file);
        context.check_source_file(file).unwrap();
        assert!(context.diagnostics().is_empty());
        let bound = context.file(file).unwrap().1.clone();
        let host = DeclaredTypeHost::new([(&parsed.arena, &bound)]).unwrap();
        let global_types = context.global_types().clone();
        let variable_type = |expected: &str| {
            let declaration = parsed
                .arena
                .iter()
                .find_map(|(node, record)| {
                    let NodeData::VariableDeclaration(variable) = &record.data else {
                        return None;
                    };
                    let NodeData::Identifier(name) = &parsed.arena.get(variable.name)?.data else {
                        return None;
                    };
                    (name.text == expected).then_some(NodeRef::new(parsed.arena.id(), file, node))
                })
                .unwrap();
            let symbol = bound.symbol(declaration).unwrap();
            context
                .store()
                .value_symbol_links(symbol)
                .and_then(|links| links.resolved_type)
                .unwrap()
        };
        let wrong_parameter = variable_type("wrongParameter");
        let wrong_return = variable_type("wrongReturn");
        let target = variable_type("target");
        let void = context.store().intrinsic_bootstrap().unwrap().void_type;
        for callable in [wrong_parameter, wrong_return] {
            let StoredSingleCallableValidation::Valid { callable, .. } =
                validate_stored_single_callable(context.store(), callable)
            else {
                panic!("an inferred callback must be fully published before diagnostics")
            };
            assert_eq!(callable.return_type, Some(void));
        }
        let StoredSingleCallableValidation::Valid {
            callable: target_callable,
            ..
        } = validate_stored_single_callable(context.store(), target)
        else {
            panic!("the target must retain one authenticated function signature")
        };
        let flags = CanonicalTypeFormatFlags::TYPE_TO_STRING_DEFAULT;
        let options = CanonicalCheckerOptions::default();

        assert_eq!(
            callable_assignability_details(
                context.store_mut_for_test(),
                &host,
                &global_types,
                wrong_parameter,
                target,
                flags,
                options,
            )
            .unwrap(),
            [
                "  Types of parameters 's' and 'n' are incompatible.",
                "    Type 'number' is not assignable to type 'string'.",
            ],
        );
        assert!(matches!(
            callable_assignability_details(
                context.store_mut_for_test(),
                &host,
                &global_types,
                wrong_return,
                target,
                flags,
                options,
            ),
            Err(SourceCheckError::RelationUnavailable(
                RelationUnavailable::UnresolvedSignatureReturn(signature)
            )) if signature == target_callable.signature
        ));
        let expected_return = context.store().intrinsic_bootstrap().unwrap().number_type;
        assert_eq!(
            context.get_return_type_of_signature(target_callable.signature),
            Ok(expected_return),
        );
        assert_eq!(
            callable_assignability_details(
                context.store_mut_for_test(),
                &host,
                &global_types,
                wrong_return,
                target,
                flags,
                options,
            )
            .unwrap(),
            ["  Type 'void' is not assignable to type 'number'."],
        );
        let warmed = context.store().relation_state_snapshot();
        assert!(
            callable_assignability_details(
                context.store_mut_for_test(),
                &host,
                &global_types,
                target,
                target,
                flags,
                options,
            )
            .unwrap()
            .is_empty()
        );
        assert_eq!(context.store().relation_state_snapshot(), warmed);
        assert!(context.diagnostics().is_empty());
    }

    #[test]
    fn zero_parameter_callable_targets_report_return_and_required_arity_details() {
        let parsed = parse_source_file(concat!(
            "const wrongReturn = (): void => {}; ",
            "const oneExtra = (value: any): void => {}; ",
            "const fourExtra = (a: any, b: any, c: any, d: any): void => {}; ",
            "const compatible = (): number => 1; ",
            "declare let target: () => number;",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(219);
        let mut context = diagnostic_context(&parsed, file);
        context.check_source_file(file).unwrap();
        assert!(context.diagnostics().is_empty());
        let bound = context.file(file).unwrap().1.clone();
        let host = DeclaredTypeHost::new([(&parsed.arena, &bound)]).unwrap();
        let global_types = context.global_types().clone();
        let variable_type = |expected: &str| {
            let declaration = parsed
                .arena
                .iter()
                .find_map(|(node, record)| {
                    let NodeData::VariableDeclaration(variable) = &record.data else {
                        return None;
                    };
                    let NodeData::Identifier(name) = &parsed.arena.get(variable.name)?.data else {
                        return None;
                    };
                    (name.text == expected).then_some(NodeRef::new(parsed.arena.id(), file, node))
                })
                .unwrap();
            let symbol = bound.symbol(declaration).unwrap();
            context
                .store()
                .value_symbol_links(symbol)
                .and_then(|links| links.resolved_type)
                .unwrap()
        };
        let wrong_return = variable_type("wrongReturn");
        let one_extra = variable_type("oneExtra");
        let four_extra = variable_type("fourExtra");
        let compatible = variable_type("compatible");
        let target = variable_type("target");
        let StoredSingleCallableValidation::Valid {
            callable: target_callable,
            ..
        } = validate_stored_single_callable(context.store(), target)
        else {
            panic!("the target must retain one authenticated function signature")
        };
        let flags = CanonicalTypeFormatFlags::TYPE_TO_STRING_DEFAULT;
        let options = CanonicalCheckerOptions::default();

        assert_eq!(
            callable_assignability_details(
                context.store_mut_for_test(),
                &host,
                &global_types,
                one_extra,
                target,
                flags,
                options,
            )
            .unwrap(),
            ["  Target signature provides too few arguments. Expected 1 or more, but got 0."],
        );
        assert_eq!(
            callable_assignability_details(
                context.store_mut_for_test(),
                &host,
                &global_types,
                four_extra,
                target,
                flags,
                options,
            )
            .unwrap(),
            ["  Target signature provides too few arguments. Expected 4 or more, but got 0."],
        );
        assert!(matches!(
            callable_assignability_details(
                context.store_mut_for_test(),
                &host,
                &global_types,
                wrong_return,
                target,
                flags,
                options,
            ),
            Err(SourceCheckError::RelationUnavailable(
                RelationUnavailable::UnresolvedSignatureReturn(signature)
            )) if signature == target_callable.signature
        ));
        let number = context.store().intrinsic_bootstrap().unwrap().number_type;
        assert_eq!(
            context.get_return_type_of_signature(target_callable.signature),
            Ok(number),
        );
        assert_eq!(
            callable_assignability_details(
                context.store_mut_for_test(),
                &host,
                &global_types,
                wrong_return,
                target,
                flags,
                options,
            )
            .unwrap(),
            ["  Type 'void' is not assignable to type 'number'."],
        );
        assert!(
            callable_assignability_details(
                context.store_mut_for_test(),
                &host,
                &global_types,
                compatible,
                target,
                flags,
                options,
            )
            .unwrap()
            .is_empty()
        );
        assert!(context.diagnostics().is_empty());
    }

    #[test]
    fn excess_object_call_argument_retains_its_source_property_location() {
        let parsed = parse_source_file(concat!(
            "const value = { b: 5 }; ",
            "declare let target: { a: number };",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(218);
        let mut context = diagnostic_context(&parsed, file);
        context.check_source_file(file).unwrap();
        assert!(context.diagnostics().is_empty());

        let bound = context.file(file).unwrap().1.clone();
        let host = DeclaredTypeHost::new([(&parsed.arena, &bound)]).unwrap();
        let global_types = context.global_types().clone();
        let object = parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::ObjectLiteralExpression).then_some(NodeRef::new(
                    parsed.arena.id(),
                    file,
                    node,
                ))
            })
            .unwrap();
        let source_type = context
            .store()
            .type_node_links(object)
            .and_then(|links| links.resolved_type)
            .unwrap();
        let target_node = parsed
            .arena
            .iter()
            .find_map(|(_, record)| {
                let NodeData::VariableDeclaration(variable) = &record.data else {
                    return None;
                };
                let NodeData::Identifier(name) = &parsed.arena.get(variable.name)?.data else {
                    return None;
                };
                (name.text == "target").then_some(NodeRef::new(
                    parsed.arena.id(),
                    file,
                    variable.type_?,
                ))
            })
            .unwrap();
        let target_type = context.get_type_from_type_node(target_node).unwrap();
        let plan =
            super::super::object_members::plan_object_literal(context.store(), &host, object)
                .unwrap();
        let [property] = plan.properties.as_slice() else {
            panic!("the fresh object must retain its one source property")
        };
        let name_node = property.name_node;
        let value_node = property.type_node;
        let argument = PlannedExpression::new(
            object,
            PlannedExpressionKind::Object {
                plan,
                properties: vec![PlannedExpression::new(
                    value_node,
                    PlannedExpressionKind::Number {
                        value: ts_jsnum::Number::new(5.0),
                        unary_operand: None,
                    },
                )],
            },
        );

        let diagnostic = excess_object_argument_diagnostic(
            context.store_mut_for_test(),
            &host,
            &global_types,
            &argument,
            source_type,
            target_type,
            CanonicalTypeFormatFlags::TYPE_TO_STRING_DEFAULT,
        )
        .unwrap()
        .unwrap();

        assert_eq!(diagnostic.node, Some(name_node));
        assert_eq!(diagnostic.diagnostic.code(), 2353);
        assert_eq!(diagnostic.diagnostic.arguments, ["b", "{ a: number; }"]);
        assert!(diagnostic.related_information.is_empty());
        assert!(context.diagnostics().is_empty());
    }

    #[test]
    fn declared_object_missing_property_keeps_argument_and_declaration_locations() {
        let parsed = parse_source_file(concat!(
            "interface Target { required: number; optional?: string } ",
            "interface Source { provided: string } ",
            "declare let argument: Source;",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(213);
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source("\"/project/declared-missing-property.ts\""),
                    CanonicalSourceLanguage::TypeScript,
                    false,
                    CanonicalModuleState::Script,
                ),
            )
            .unwrap();
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
        let mut context = CanonicalCheckerContext::new(
            binder.finish(),
            [(file, &parsed.arena)].into_iter().collect(),
            CanonicalCheckerOptions::default(),
        )
        .unwrap();
        context.check_source_file(file).unwrap();
        assert!(context.diagnostics().is_empty());

        let bound = context.file(file).unwrap().1.clone();
        let host = DeclaredTypeHost::new([(&parsed.arena, &bound)]).unwrap();
        let global_types = context.global_types().clone();
        let interface_type = |name: &str| {
            let declaration = parsed
                .arena
                .iter()
                .find_map(|(node, record)| {
                    let NodeData::InterfaceDeclaration(interface) = &record.data else {
                        return None;
                    };
                    let NodeData::Identifier(identifier) = &parsed.arena.get(interface.name)?.data
                    else {
                        return None;
                    };
                    (identifier.text == name).then_some(NodeRef::new(parsed.arena.id(), file, node))
                })
                .unwrap();
            let symbol = bound.symbol(declaration).unwrap();
            context
                .store()
                .declared_type_links(symbol)
                .and_then(|links| links.declared_type)
                .unwrap()
        };
        let source_type = interface_type("Source");
        let target_type = interface_type("Target");
        let argument = parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::TypeReference).then_some(NodeRef::new(
                    parsed.arena.id(),
                    file,
                    node,
                ))
            })
            .unwrap();

        let diagnostic = missing_declared_property_diagnostic(
            context.store_mut_for_test(),
            &host,
            &global_types,
            source_type,
            target_type,
            argument,
            CanonicalTypeFormatFlags::TYPE_TO_STRING_DEFAULT,
        )
        .unwrap()
        .unwrap();

        assert_eq!(diagnostic.node, Some(argument));
        assert_eq!(diagnostic.diagnostic.code(), 2741);
        assert_eq!(
            diagnostic.diagnostic.arguments,
            ["required", "Source", "Target"],
        );
        let [related] = diagnostic.related_information.as_slice() else {
            panic!("the missing property must retain its declaration")
        };
        assert_eq!(related.diagnostic.code(), 2728);
        assert_eq!(related.diagnostic.arguments, ["required"]);
        let declaration = parsed
            .arena
            .get(
                related
                    .node
                    .expect("the related declaration has a node")
                    .node,
            )
            .unwrap();
        let NodeData::Identifier(identifier) = &declaration.data else {
            panic!("the related declaration must point at the property name")
        };
        assert_eq!(identifier.text, "required");
        assert!(context.diagnostics().is_empty());
    }

    fn assert_nested_declared_property_details(tuple: bool) {
        let element = |name: &str| {
            if tuple {
                format!("[{name}]")
            } else {
                format!("{name}[]")
            }
        };
        let text = format!(
            concat!(
                "interface Array<T> {{}} ",
                "interface ReadonlyArray<T> {{}} ",
                "namespace A {{ ",
                "export type Leaf = {{ id: string }}; ",
                "export type Mid = {{ leaves: {} }}; ",
                "export type Inner = {{ mids: {} }}; ",
                "export type Outer = {{ inners: {} }}; ",
                "}} ",
                "namespace B {{ ",
                "export type Leaf = {{ id: number }}; ",
                "export type Mid = {{ leaves: {} }}; ",
                "export type Inner = {{ mids: {} }}; ",
                "export type Outer = {{ inners: {} }}; ",
                "}} ",
                "declare let source: B.Outer; ",
                "declare let target: A.Outer;",
            ),
            element("Leaf"),
            element("Mid"),
            element("Inner"),
            element("Leaf"),
            element("Mid"),
            element("Inner"),
        );
        let parsed = parse_source_file(&text);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(if tuple { 215 } else { 214 });
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source("\"/project/nested-property-diagnostic.ts\""),
                    CanonicalSourceLanguage::TypeScript,
                    false,
                    CanonicalModuleState::Script,
                ),
            )
            .unwrap();
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
        let mut context = CanonicalCheckerContext::new(
            binder.finish(),
            [(file, &parsed.arena)].into_iter().collect(),
            CanonicalCheckerOptions::default(),
        )
        .unwrap();
        context.check_source_file(file).unwrap();
        assert!(context.diagnostics().is_empty());

        let annotation = |expected: &str| {
            parsed
                .arena
                .iter()
                .find_map(|(_, record)| {
                    let NodeData::VariableDeclaration(variable) = &record.data else {
                        return None;
                    };
                    let NodeData::Identifier(name) = &parsed.arena.get(variable.name)?.data else {
                        return None;
                    };
                    (name.text == expected).then_some(NodeRef::new(
                        parsed.arena.id(),
                        file,
                        variable.type_?,
                    ))
                })
                .unwrap()
        };
        let source_type = context
            .get_type_from_type_node(annotation("source"))
            .unwrap();
        let target_type = context
            .get_type_from_type_node(annotation("target"))
            .unwrap();
        assert!(
            !context
                .is_type_assignable_to(source_type, target_type)
                .unwrap()
        );

        let bound = context.file(file).unwrap().1.clone();
        let host = DeclaredTypeHost::new([(&parsed.arena, &bound)]).unwrap();
        let global_types = context.global_types().clone();
        let details = declared_property_mismatch_details(
            context.store_mut_for_test(),
            &host,
            &global_types,
            source_type,
            target_type,
            CanonicalTypeFormatFlags::TYPE_TO_STRING_DEFAULT,
            CanonicalCheckerOptions::default(),
        )
        .unwrap();

        let collection = |source: &str, target: &str| {
            format!(
                "Type '{}' is not assignable to type '{}'.",
                element(source),
                element(target),
            )
        };
        assert_eq!(
            details,
            [
                "  Types of property 'inners' are incompatible.".to_owned(),
                format!("    {}", collection("B.Inner", "A.Inner")),
                "      Type 'B.Inner' is not assignable to type 'A.Inner'.".to_owned(),
                "        Types of property 'mids' are incompatible.".to_owned(),
                format!("          {}", collection("B.Mid", "A.Mid")),
                "            Type 'B.Mid' is not assignable to type 'A.Mid'.".to_owned(),
                "              Types of property 'leaves' are incompatible.".to_owned(),
                format!("                {}", collection("B.Leaf", "A.Leaf")),
                "                  Type 'B.Leaf' is not assignable to type 'A.Leaf'.".to_owned(),
                "                    Types of property 'id' are incompatible.".to_owned(),
                "                      Type 'number' is not assignable to type 'string'."
                    .to_owned(),
            ],
        );

        let warmed_relations = context.store().relation_state_snapshot();
        let mut active = HashSet::from([(source_type, target_type)]);
        assert_eq!(
            recursive_declared_property_mismatch_details(
                context.store_mut_for_test(),
                &host,
                &global_types,
                source_type,
                target_type,
                CanonicalTypeFormatFlags::TYPE_TO_STRING_DEFAULT,
                CanonicalCheckerOptions::default(),
                1,
                &mut active,
            )
            .unwrap(),
            None,
        );
        assert_eq!(active, HashSet::from([(source_type, target_type)]));
        assert_eq!(context.store().relation_state_snapshot(), warmed_relations);
        assert_eq!(
            declared_property_mismatch_details(
                context.store_mut_for_test(),
                &host,
                &global_types,
                source_type,
                target_type,
                CanonicalTypeFormatFlags::TYPE_TO_STRING_DEFAULT,
                CanonicalCheckerOptions::default(),
            )
            .unwrap(),
            details,
        );
        assert_eq!(context.store().relation_state_snapshot(), warmed_relations);
        assert!(context.diagnostics().is_empty());
    }

    #[test]
    fn nested_declared_array_properties_keep_the_complete_assignability_chain() {
        assert_nested_declared_property_details(false);
    }

    #[test]
    fn nested_declared_tuple_properties_keep_the_complete_assignability_chain() {
        assert_nested_declared_property_details(true);
    }

    #[test]
    fn tuple_rest_parameter_mismatch_preserves_labels_and_contravariant_types() {
        let parsed = parse_source_file(concat!(
            "declare let target: (...args: [x: number]) => void; ",
            "declare let source: (a: string) => void; ",
            "target = source;",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(212);
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source("\"/project/tuple-rest-diagnostic.ts\""),
                    CanonicalSourceLanguage::TypeScript,
                    false,
                    CanonicalModuleState::Script,
                ),
            )
            .unwrap();
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
        let mut context = CanonicalCheckerContext::new(
            binder.finish(),
            [(file, &parsed.arena)].into_iter().collect(),
            CanonicalCheckerOptions {
                strict_function_types: true,
                ..CanonicalCheckerOptions::default()
            },
        )
        .unwrap();

        context.check_source_file(file).unwrap();

        let [diagnostic] = context.diagnostics().as_slice() else {
            panic!("expected one tuple-rest parameter mismatch")
        };
        assert_eq!(diagnostic.diagnostic.code(), 2322);
        assert_eq!(
            diagnostic.diagnostic.arguments,
            ["(a: string) => void", "(x: number) => void"],
        );
        assert_eq!(
            diagnostic.diagnostic.render().unwrap(),
            concat!(
                "Type '(a: string) => void' is not assignable to type '(x: number) => void'.\n",
                "  Types of parameters 'a' and 'x' are incompatible.\n",
                "    Type 'number' is not assignable to type 'string'.",
            ),
        );
        assert!(diagnostic.related_information.is_empty());

        let published = context.diagnostics().clone();
        context.recheck_source_file(file).unwrap();
        assert_eq!(context.diagnostics(), &published);
    }

    #[test]
    fn indexed_object_mismatches_point_at_the_property_and_index_declaration() {
        let text = concat!(
            "var dynamic: any;\n",
            "var values: { [name: string]: number } = { bad: \"\", okay: dynamic };\n",
        );
        let parsed = parse_source_file(text);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(209);
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source("\"/project/index-diagnostic.ts\""),
                    CanonicalSourceLanguage::TypeScript,
                    false,
                    CanonicalModuleState::Script,
                ),
            )
            .unwrap();
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
        let mut context = CanonicalCheckerContext::new(
            binder.finish(),
            [(file, &parsed.arena)].into_iter().collect(),
            CanonicalCheckerOptions::default(),
        )
        .unwrap();

        context.check_source_file(file).unwrap();

        let [diagnostic] = context.diagnostics().as_slice() else {
            panic!("expected one index value mismatch")
        };
        assert_eq!(diagnostic.diagnostic.code(), 2322);
        assert_eq!(diagnostic.diagnostic.arguments, ["string", "number"]);
        let property = parsed
            .arena
            .get(
                diagnostic
                    .node
                    .expect("property has a diagnostic node")
                    .node,
            )
            .unwrap();
        let NodeData::Identifier(name) = &property.data else {
            panic!("the index mismatch must point at the property name")
        };
        assert_eq!(name.text, "bad");
        let [index] = diagnostic.related_information.as_slice() else {
            panic!("an index mismatch must retain its index declaration")
        };
        assert_eq!(index.diagnostic.code(), 6501);
        assert!(index.diagnostic.arguments.is_empty());
        assert_eq!(
            parsed
                .arena
                .get(index.node.expect("index has a related node").node)
                .unwrap()
                .kind,
            SyntaxKind::IndexSignature
        );

        let published = context.diagnostics().clone();
        context.recheck_source_file(file).unwrap();
        assert_eq!(context.diagnostics(), &published);
    }

    #[test]
    fn mixed_template_index_mismatches_keep_the_index_property_and_related_declaration() {
        let parsed = parse_source_file(concat!(
            "var values: { required: string; [name: `do-${string}`]: number } = ",
            "{ required: \"ok\", \"do-save\": \"invalid\" };",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(210);
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source("\"/project/template-index-diagnostic.ts\""),
                    CanonicalSourceLanguage::TypeScript,
                    false,
                    CanonicalModuleState::Script,
                ),
            )
            .unwrap();
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
        let mut context = CanonicalCheckerContext::new(
            binder.finish(),
            [(file, &parsed.arena)].into_iter().collect(),
            CanonicalCheckerOptions::default(),
        )
        .unwrap();

        context.check_source_file(file).unwrap();

        let [diagnostic] = context.diagnostics().as_slice() else {
            panic!("expected one template index value mismatch")
        };
        assert_eq!(diagnostic.diagnostic.code(), 2322);
        assert_eq!(diagnostic.diagnostic.arguments, ["string", "number"]);
        let property = parsed
            .arena
            .get(
                diagnostic
                    .node
                    .expect("property has a diagnostic node")
                    .node,
            )
            .unwrap();
        let NodeData::StringLiteral(name) = &property.data else {
            panic!("the template index mismatch must point at its quoted property")
        };
        assert_eq!(name.text, "do-save");
        let [index] = diagnostic.related_information.as_slice() else {
            panic!("a template index mismatch must retain its index declaration")
        };
        assert_eq!(index.diagnostic.code(), 6501);
        assert_eq!(
            parsed
                .arena
                .get(index.node.expect("index has a related node").node)
                .unwrap()
                .kind,
            SyntaxKind::IndexSignature
        );
    }

    #[test]
    fn indexed_properties_do_not_hide_a_different_missing_required_property() {
        let parsed = parse_source_file(concat!(
            "type Options = { required: string; [name: `do-${string}`]: number }; ",
            "var missing: Options = { \"do-save\": 1 }; ",
            "var excess: Options = { \"unknown\": 1 };",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(211);
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source("\"/project/indexed-missing-property.ts\""),
                    CanonicalSourceLanguage::TypeScript,
                    false,
                    CanonicalModuleState::Script,
                ),
            )
            .unwrap();
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
        let mut context = CanonicalCheckerContext::new(
            binder.finish(),
            [(file, &parsed.arena)].into_iter().collect(),
            CanonicalCheckerOptions::default(),
        )
        .unwrap();

        context.check_source_file(file).unwrap();

        let [missing, excess] = context.diagnostics().as_slice() else {
            panic!("expected one missing property and one actual excess property")
        };
        assert_eq!(missing.diagnostic.code(), 2741);
        assert_eq!(missing.diagnostic.arguments[0], "required");
        let missing_name = parsed
            .arena
            .get(missing.node.expect("missing property has a location").node)
            .unwrap();
        let NodeData::Identifier(name) = &missing_name.data else {
            panic!("the missing-property diagnostic must point at its variable")
        };
        assert_eq!(name.text, "missing");
        let [declaration] = missing.related_information.as_slice() else {
            panic!("the required member must retain its declaration")
        };
        assert_eq!(declaration.diagnostic.code(), 2728);
        assert_eq!(declaration.diagnostic.arguments, ["required"]);

        assert_eq!(excess.diagnostic.code(), 2353);
        let excess_name = parsed
            .arena
            .get(excess.node.expect("excess property has a location").node)
            .unwrap();
        let NodeData::StringLiteral(name) = &excess_name.data else {
            panic!("a nonmatching property must keep its original quoted name")
        };
        assert_eq!(name.text, "unknown");

        let published = context.diagnostics().clone();
        context.recheck_source_file(file).unwrap();
        assert_eq!(context.diagnostics(), &published);
    }

    #[test]
    fn nested_exact_optional_mismatches_keep_property_spans_and_related_info() {
        let text = concat!(
            "type Optional = { value?: string };\n",
            "type Nested = { child: Optional };\n",
            "type Outer = { middle: Nested };\n",
            "declare let uncertain: string | undefined;\n",
            "const direct: Nested = { child: { value: undefined } };\n",
            "const union: Nested = { child: { value: uncertain } };\n",
            "const deep: Outer = { middle: { child: { value: undefined } } };\n",
        );
        let parsed = parse_source_file(text);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(208);
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source("\"/project/nested-exact-optional.ts\""),
                    CanonicalSourceLanguage::TypeScript,
                    false,
                    CanonicalModuleState::Script,
                ),
            )
            .unwrap();
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
        let mut context = CanonicalCheckerContext::new(
            binder.finish(),
            [(file, &parsed.arena)].into_iter().collect(),
            CanonicalCheckerOptions {
                intrinsic: IntrinsicBootstrapOptions {
                    strict_null_checks: true,
                    exact_optional_property_types: true,
                },
                ..CanonicalCheckerOptions::default()
            },
        )
        .unwrap();

        context.check_source_file(file).unwrap();

        let diagnostics = context.diagnostics().as_slice();
        assert_eq!(diagnostics.len(), 3, "{diagnostics:?}");
        for (diagnostic, union) in diagnostics.iter().zip([false, true, false]) {
            assert_eq!(diagnostic.diagnostic.code(), 2375);
            let range = parsed
                .arena
                .get(diagnostic.node.expect("property has an anchor").node)
                .unwrap()
                .range;
            assert_eq!(
                &text[usize::try_from(range.start.get()).unwrap()
                    ..usize::try_from(range.end.get()).unwrap()],
                "child"
            );
            let expected = if union {
                concat!(
                    "Type '{ value: string | undefined; }' is not assignable to type ",
                    "'Optional' with 'exactOptionalPropertyTypes: true'. Consider ",
                    "adding 'undefined' to the types of the target's properties.\n",
                    "  Types of property 'value' are incompatible.\n",
                    "    Type 'string | undefined' is not assignable to type 'string'.\n",
                    "      Type 'undefined' is not assignable to type 'string'.",
                )
            } else {
                concat!(
                    "Type '{ value: undefined; }' is not assignable to type 'Optional' ",
                    "with 'exactOptionalPropertyTypes: true'. Consider adding ",
                    "'undefined' to the types of the target's properties.\n",
                    "  Types of property 'value' are incompatible.\n",
                    "    Type 'undefined' is not assignable to type 'string'.",
                )
            };
            assert_eq!(diagnostic.diagnostic.render().unwrap(), expected);
            let [related] = diagnostic.related_information.as_slice() else {
                panic!("a nested mismatch must retain its immediate expected property")
            };
            assert_eq!(related.diagnostic.code(), 6500);
            assert_eq!(related.diagnostic.arguments, ["child", "Nested"]);
        }

        let published = context.diagnostics().clone();
        context.check_source_file(file).unwrap();
        assert_eq!(context.diagnostics(), &published);
    }
}
