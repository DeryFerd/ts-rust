//! Ordinary-array assignment diagnostic elaboration.
//!
//! This is the no-spread positional prefix of pinned `elaborateArrayLiteral`
//! and `elaborateElement`. The source checker retains each effective element
//! result type before union reduction, so diagnostics never attempt to map a
//! reduced union back onto syntax.

use ts_ast::NodeRef;

use super::{
    CanonicalCheckerDiagnostic, CanonicalCheckerOptions, CanonicalGlobalTypes,
    CanonicalTypeMapperStore, DeclaredTypeHost, RelationUnavailable, TypeId,
    source::{PlannedExpression, PlannedExpressionKind, SourceCheckError},
};

/// Elaborates one failed ordinary-array assignment positionally.
///
/// `Ok(None)` means either operand is outside the canonical ordinary-array
/// domain. `Ok(Some(_))` means both shapes were validated; a nonempty batch
/// suppresses the root array diagnostic.
#[allow(clippy::too_many_arguments)] // Mirrors positional array elaboration inputs.
pub(super) fn diagnostics_for_failed_array_assignment(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    global_types: &CanonicalGlobalTypes,
    expression: &PlannedExpression,
    element_types: &[TypeId],
    source_type: TypeId,
    target_type: TypeId,
    options: CanonicalCheckerOptions,
) -> Result<Option<Vec<CanonicalCheckerDiagnostic>>, SourceCheckError> {
    let expression = expression.unparenthesized();
    let PlannedExpressionKind::Array(elements) = &expression.kind else {
        return Ok(None);
    };
    if store
        .canonical_array_reference(global_types, source_type)?
        .is_none()
    {
        return Ok(None);
    }
    let Some(target_element) = store.canonical_array_element_type(global_types, target_type)?
    else {
        return Ok(None);
    };
    if elements.len() != element_types.len() {
        return Err(RelationUnavailable::MalformedStructuredType(source_type).into());
    }

    let mut diagnostics = Vec::new();
    for (element, element_type) in elements.iter().zip(element_types.iter().copied()) {
        if store.is_type_assignable_to_with_global_types(
            element_type,
            target_element,
            global_types,
        )? {
            continue;
        }
        diagnostics.extend(
            super::object_diagnostics::diagnostics_for_failed_assignment(
                store,
                host,
                global_types,
                element,
                element_type,
                target_element,
                diagnostic_node(element),
                options,
            )?,
        );
    }
    Ok(Some(diagnostics))
}

fn diagnostic_node(expression: &PlannedExpression) -> NodeRef {
    expression.unparenthesized().node
}
