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
    instantiate::InstantiationSession,
    source::{
        CheckedExpressionShape, CheckedExpressionTypes, PlannedExpression, PlannedExpressionKind,
        SourceCheckError,
    },
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
    checked: &CheckedExpressionTypes,
    target_type: TypeId,
    options: CanonicalCheckerOptions,
    session: &mut InstantiationSession,
) -> Result<Option<Vec<CanonicalCheckerDiagnostic>>, SourceCheckError> {
    let Some(elements) = checked_array_elements(expression, checked)? else {
        return Ok(None);
    };
    if store
        .canonical_array_reference(global_types, checked.result)?
        .is_none()
    {
        return Ok(None);
    }
    let Some(target_element) = store.canonical_array_element_type(global_types, target_type)?
    else {
        return Ok(None);
    };

    let mut diagnostics = Vec::new();
    for (element, checked_element) in elements.planned.iter().zip(elements.checked) {
        if store.is_type_assignable_to_with_global_types(
            checked_element.result,
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
                checked_element,
                target_element,
                diagnostic_node(element),
                options,
                session,
            )?,
        );
    }
    Ok(Some(diagnostics))
}

pub(super) struct CheckedArrayElements<'a> {
    pub(super) planned: &'a [PlannedExpression],
    pub(super) checked: &'a [CheckedExpressionTypes],
}

/// Validates the retained execution tree before diagnostic elaboration can
/// mutate relation caches or publish a partial diagnostic batch.
pub(super) fn checked_array_elements<'a>(
    expression: &'a PlannedExpression,
    checked: &'a CheckedExpressionTypes,
) -> Result<Option<CheckedArrayElements<'a>>, SourceCheckError> {
    let expression = expression.unparenthesized();
    let PlannedExpressionKind::Array(planned) = &expression.kind else {
        return Ok(None);
    };
    let CheckedExpressionShape::Array(checked_elements) = &checked.shape else {
        return Err(RelationUnavailable::MalformedStructuredType(checked.result).into());
    };
    if planned.len() != checked_elements.len() {
        return Err(RelationUnavailable::MalformedStructuredType(checked.result).into());
    }
    Ok(Some(CheckedArrayElements {
        planned,
        checked: checked_elements,
    }))
}

fn diagnostic_node(expression: &PlannedExpression) -> NodeRef {
    expression.unparenthesized().node
}
