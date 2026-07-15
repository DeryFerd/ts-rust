//! Object-literal assignability diagnostic elaboration.
//!
//! This is the property-only prefix of the pinned
//! `checkTypeAssignableToAndOptionallyElaborate` / `elaborateObjectLiteral` /
//! `elaborateElement` path at
//! `dc37b5249ab60e2bbce936f71b883e6c8136167e`. Relations remain silent: this
//! module runs only after a failed assignability query and builds complete
//! primary-plus-related records before the caller publishes any of them.
//!
//! The canonical checker does not yet carry the Program's default-library
//! classification into this path. Until that exact fact is threaded through,
//! TS6500 uses a temporary conservative current-source rule: it is emitted
//! only when the target declaration is in the source currently being checked.
//! This intentionally suppresses cross-file TS6500, but it is not an exact
//! default-library test.

use std::collections::HashSet;

use ts_ast::{FileId, NodeData, NodeRef, SyntaxKind};
use ts_diagnostics::{Diagnostic, message_by_code};

use super::{
    AssignabilityErrorDisplay, CanonicalCheckerDiagnostic, CanonicalCheckerOptions,
    CanonicalCheckerRelatedInformation, CanonicalTypeFormatFlags, CanonicalTypeMapperStore,
    DeclaredTypeHost, RelationUnavailable, TypeId,
    formatter::{
        get_type_names_for_assignability_error_with_host_and_flags,
        type_to_string_with_host_and_flags,
    },
    object_members::PropertyObjectPlan,
    relater::{ResolvedDeclaredProperty, ResolvedDeclaredPropertyObject},
    source::{PlannedExpression, SourceCheckError},
    spelling::get_spelling_suggestion,
    type_records::TypeData,
};

/// Builds the complete diagnostic batch for one already-failed assignment.
pub(super) fn diagnostics_for_failed_assignment(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    expression: &PlannedExpression,
    source_type: TypeId,
    target_type: TypeId,
    fallback_node: NodeRef,
    options: CanonicalCheckerOptions,
) -> Result<Vec<CanonicalCheckerDiagnostic>, SourceCheckError> {
    let flags = display_flags(options);
    let mut elaborated = elaborate_known_properties(
        store,
        host,
        expression,
        source_type,
        target_type,
        fallback_node.file,
        flags,
    )?;
    if !elaborated.is_empty() {
        return Ok(elaborated);
    }
    elaborated.push(shape_or_generic_diagnostic(
        store,
        host,
        expression,
        source_type,
        target_type,
        fallback_node,
        flags,
    )?);
    Ok(elaborated)
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
fn elaborate_known_properties(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    expression: &PlannedExpression,
    source_type: TypeId,
    target_type: TypeId,
    checked_file: FileId,
    flags: CanonicalTypeFormatFlags,
) -> Result<Vec<CanonicalCheckerDiagnostic>, SourceCheckError> {
    let PlannedExpression::Object { plan, properties } = expression else {
        return Ok(Vec::new());
    };
    let Some(target) = store.resolved_declared_property_object(host, target_type)? else {
        return Ok(Vec::new());
    };
    let source_types = resolved_source_property_types(store, plan, source_type)?;
    if properties.len() != plan.properties.len() || source_types.len() != plan.properties.len() {
        return Err(invalid_structure(source_type));
    }

    let mut diagnostics = Vec::new();
    for ((source_property, source_expression), source_property_type) in
        plan.properties.iter().zip(properties).zip(source_types)
    {
        let Some(target_property) = target.get_source(&source_property.name) else {
            continue;
        };
        if store.is_type_assignable_to(source_property_type, target_property.type_)? {
            continue;
        }

        if matches!(source_expression, PlannedExpression::Object { .. }) {
            let nested = elaborate_known_properties(
                store,
                host,
                source_expression,
                source_property_type,
                target_property.type_,
                checked_file,
                flags,
            )?;
            if !nested.is_empty() {
                diagnostics.extend(nested);
                continue;
            }

            let mut diagnostic = shape_or_generic_diagnostic(
                store,
                host,
                source_expression,
                source_property_type,
                target_property.type_,
                source_property.name_node,
                flags,
            )?;
            append_expected_property_related(
                &mut diagnostic,
                store,
                host,
                checked_file,
                target_type,
                target_property,
                flags,
            )?;
            diagnostics.push(diagnostic);
            continue;
        }

        let mut diagnostic = generic_assignability_diagnostic(
            store,
            host,
            source_property_type,
            target_property.type_,
            source_property.name_node,
            flags,
        )?;
        append_expected_property_related(
            &mut diagnostic,
            store,
            host,
            checked_file,
            target_type,
            target_property,
            flags,
        )?;
        diagnostics.push(diagnostic);
    }
    Ok(diagnostics)
}

fn shape_or_generic_diagnostic(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    expression: &PlannedExpression,
    source_type: TypeId,
    target_type: TypeId,
    fallback_node: NodeRef,
    flags: CanonicalTypeFormatFlags,
) -> Result<CanonicalCheckerDiagnostic, SourceCheckError> {
    let PlannedExpression::Object { plan, .. } = expression else {
        return generic_assignability_diagnostic(
            store,
            host,
            source_type,
            target_type,
            fallback_node,
            flags,
        );
    };
    let Some(target) = store.resolved_declared_property_object(host, target_type)? else {
        return generic_assignability_diagnostic(
            store,
            host,
            source_type,
            target_type,
            fallback_node,
            flags,
        );
    };

    if let Some(excess) = plan
        .properties
        .iter()
        .find(|property| target.get_source(&property.name).is_none())
    {
        return excess_property_diagnostic(store, host, &target, target_type, excess, flags);
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
            source_type,
            target_type,
            fallback_node,
            &missing,
            flags,
        );
    }

    generic_assignability_diagnostic(store, host, source_type, target_type, fallback_node, flags)
}

fn excess_property_diagnostic(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    target: &ResolvedDeclaredPropertyObject,
    target_type: TypeId,
    excess: &super::object_members::PlannedProperty,
    flags: CanonicalTypeFormatFlags,
) -> Result<CanonicalCheckerDiagnostic, SourceCheckError> {
    let target_display = type_to_string_with_host_and_flags(store, host, target_type, flags)?;
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

fn missing_property_diagnostic(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    source_type: TypeId,
    target_type: TypeId,
    fallback_node: NodeRef,
    missing: &[&ResolvedDeclaredProperty],
    flags: CanonicalTypeFormatFlags,
) -> Result<CanonicalCheckerDiagnostic, SourceCheckError> {
    let AssignabilityErrorDisplay { source, target } =
        get_type_names_for_assignability_error_with_host_and_flags(
            store,
            host,
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

fn generic_assignability_diagnostic(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    source_type: TypeId,
    target_type: TypeId,
    node: NodeRef,
    flags: CanonicalTypeFormatFlags,
) -> Result<CanonicalCheckerDiagnostic, SourceCheckError> {
    let AssignabilityErrorDisplay { source, target } =
        get_type_names_for_assignability_error_with_host_and_flags(
            store,
            host,
            source_type,
            target_type,
            flags,
        )?;
    primary(2322, node, vec![source, target])
}

#[allow(clippy::too_many_arguments)]
fn append_expected_property_related(
    diagnostic: &mut CanonicalCheckerDiagnostic,
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    checked_file: FileId,
    target_type: TypeId,
    property: &ResolvedDeclaredProperty,
    flags: CanonicalTypeFormatFlags,
) -> Result<(), SourceCheckError> {
    if property.declaration.file != checked_file {
        return Ok(());
    }
    let property_name = property_name(property)?.to_owned();
    let target_display = type_to_string_with_host_and_flags(store, host, target_type, flags)?;
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
