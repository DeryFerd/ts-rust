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
use ts_diagnostics::{Diagnostic, message_by_code};

use super::{
    AssignabilityErrorDisplay, CanonicalCheckerDiagnostic, CanonicalCheckerOptions,
    CanonicalCheckerRelatedInformation, CanonicalGlobalTypes, CanonicalTypeFormatFlags,
    CanonicalTypeMapperStore, DeclaredTypeHost, RelationUnavailable, SignatureId,
    TypeDisplayUnavailable, TypeId,
    formatter::{
        FunctionTypeDisplayUnavailable,
        get_type_names_for_assignability_error_with_host_global_types_and_flags,
        type_to_string_with_host_global_types_and_flags,
    },
    functions::{StoredFunctionTypeValidation, validate_stored_function_type},
    instantiate::InstantiationSession,
    object_members::{
        DeclaredPropertyTypeGraphValidation, PropertyObjectPlan,
        validate_resolved_declared_property_type_graph,
    },
    relater::{ResolvedDeclaredProperty, ResolvedDeclaredPropertyObject},
    source::{
        CheckedExpressionShape, CheckedExpressionTypes, PlannedExpression, PlannedExpressionKind,
        SourceCheckError, SourceCheckProvenanceError,
    },
    spelling::get_spelling_suggestion,
    type_nodes::CanonicalTypeQuery,
    type_records::TypeData,
    types::TypeFlags,
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
        let Some(target_property) = target.get_source(&source_property.name) else {
            continue;
        };
        if store.is_type_assignable_to_with_global_types(
            source_property_type,
            target_property.type_,
            global_types,
        )? {
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
    let PlannedExpressionKind::Object { plan, .. } = &expression.kind else {
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

    if let Some(excess) = plan
        .properties
        .iter()
        .find(|property| target.get_source(&property.name).is_none())
    {
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
        .map(|property| property.name.as_str())
        .collect::<HashSet<_>>();
    let mut missing = Vec::new();
    for property in target.properties() {
        let name = property_name(property)?;
        if !property.optional && !source_names.contains(name) {
            missing.push(property);
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

    generic_assignability_diagnostic(
        store,
        host,
        global_types,
        source_type,
        target_type,
        fallback_node,
        flags,
        options,
    )
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
    let suggestion = get_spelling_suggestion(
        &excess.name,
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
            vec![excess.name.clone(), target_display, suggestion],
        ),
        None => primary(
            2353,
            excess.name_node,
            vec![excess.name.clone(), target_display],
        ),
    }
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
    diagnostic.diagnostic.details = declared_property_mismatch_details(
        store,
        host,
        global_types,
        source_type,
        target_type,
        flags,
        options,
    )?;
    Ok(diagnostic)
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
    for type_ in [source_type, target_type] {
        match validate_resolved_declared_property_type_graph(store, type_) {
            DeclaredPropertyTypeGraphValidation::Traversable(_) => {}
            DeclaredPropertyTypeGraphValidation::Opaque => return Ok(Vec::new()),
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
    for target_property in target.properties() {
        let name = property_name(target_property)?;
        let Some(source_property) = source.get_source(name) else {
            continue;
        };
        if store.is_type_assignable_to_with_global_types_and_strict_function_types(
            source_property.type_,
            target_property.type_,
            global_types,
            options.strict_function_types,
        )? {
            continue;
        }
        // The complete upstream relation chain is recursive. Until those
        // nested object, array, callable, and type-variable messages are
        // ported, only elaborate a child pair whose terminal scalar shape is
        // independently proven. Falling back to the root TS2322 is preferable
        // to publishing a plausible but truncated diagnostic chain.
        if !is_terminal_scalar_relation_leaf(store, source_property.type_)
            || !is_terminal_scalar_relation_leaf(store, target_property.type_)
        {
            return Ok(Vec::new());
        }
        let property_message = Diagnostic::with_arguments(
            message_by_code(2326).ok_or(SourceCheckError::MissingDiagnostic(2326))?,
            [name],
        )
        .render()
        .expect("TS2326 has one formatting argument");
        let AssignabilityErrorDisplay { source, target } =
            get_type_names_for_assignability_error_with_host_global_types_and_flags(
                store,
                host,
                global_types,
                source_property.type_,
                target_property.type_,
                flags,
            )?;
        let nested_message = Diagnostic::with_arguments(
            message_by_code(2322).ok_or(SourceCheckError::MissingDiagnostic(2322))?,
            [source, target],
        )
        .render()
        .expect("TS2322 has two formatting arguments");
        return Ok(vec![
            format!("  {property_message}"),
            format!("    {nested_message}"),
        ]);
    }
    Ok(Vec::new())
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
        if table.get_source(&planned.name) != Some(symbol) {
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
    use super::*;

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
}
