//! Overload selection for published, uninstantiated method signatures.
//!
//! The ordinary and generic call engines check each real candidate. This module
//! owns declaration-group order, the two relation passes, and failure selection.
//! A diagnostic candidate can differ from the signature used for recovery.

use super::{
    CanonicalGlobalTypes, CanonicalTypeMapperStore, MinArgumentCountFlags, RelationUnavailable,
    SignatureId, TypeId,
    array_types::CanonicalArrayTargets,
    callable_sets::{StoredCallableSetValidation, validate_stored_callable_set_with_array_targets},
    callables::ValidatedSingleCallable,
    calls::{
        DirectCallApplicability, DirectCallError, DirectCallForm, DirectCallRequest,
        DirectCallResolution, DirectCallUnsupported, check_argument_applicability,
        get_min_argument_count, get_parameter_count, has_effective_rest_parameter,
        project_validated_direct_call, reorder_direct_call_candidates,
    },
    generic_calls::{
        GenericCallArgumentRelation, GenericCallVectorApplicability, GenericCallVectorCandidate,
        GenericCallVectorError, GenericCallVectorRequest, GenericCallVectorResolution,
        check_generic_call_candidate_with_session, finish_generic_call_candidate_with_session,
        validate_generic_call_vector_request,
    },
    instantiate::InstantiationSession,
    type_records::TypeData,
};

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) enum GenericMethodCallSelection {
    Fixed {
        signature: SignatureId,
        return_type: TypeId,
    },
    Generic(GenericCallVectorResolution),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) enum GenericMethodCallDiagnostic {
    Fixed(DirectCallResolution),
    Generic {
        signature: SignatureId,
        applicability: GenericCallVectorApplicability,
    },
    TypeArgumentArity {
        expected: usize,
        actual: usize,
    },
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct GenericMethodCallResolution {
    pub(super) selected: GenericMethodCallSelection,
    pub(super) diagnostic: Option<GenericMethodCallDiagnostic>,
}

#[derive(Debug, PartialEq)]
pub(super) enum GenericMethodCallError {
    Direct(DirectCallError),
    Generic(GenericCallVectorError),
    Relation(RelationUnavailable),
    Unsupported(TypeId),
    Invalid(TypeId),
}

impl From<DirectCallError> for GenericMethodCallError {
    fn from(error: DirectCallError) -> Self {
        Self::Direct(error)
    }
}

impl From<GenericCallVectorError> for GenericMethodCallError {
    fn from(error: GenericCallVectorError) -> Self {
        Self::Generic(error)
    }
}

impl From<RelationUnavailable> for GenericMethodCallError {
    fn from(error: RelationUnavailable) -> Self {
        Self::Relation(error)
    }
}

enum CheckedMethodCandidate {
    Fixed(DirectCallResolution),
    Generic(GenericCallVectorCandidate),
}

impl CheckedMethodCandidate {
    fn applicable(&self) -> bool {
        match self {
            Self::Fixed(candidate) => {
                candidate.applicability == DirectCallApplicability::Applicable
            }
            Self::Generic(candidate) => {
                candidate.applicability() == GenericCallVectorApplicability::Applicable
            }
        }
    }

    fn diagnostic(&self) -> GenericMethodCallDiagnostic {
        match self {
            Self::Fixed(candidate) => GenericMethodCallDiagnostic::Fixed(candidate.clone()),
            Self::Generic(candidate) => GenericMethodCallDiagnostic::Generic {
                signature: candidate.signature(),
                applicability: candidate.applicability(),
            },
        }
    }

    fn argument_error(&self) -> bool {
        match self {
            Self::Fixed(candidate) => matches!(
                candidate.applicability,
                DirectCallApplicability::ArgumentNotAssignable { .. }
                    | DirectCallApplicability::RestArgumentsNotAssignable { .. }
            ),
            Self::Generic(candidate) => matches!(
                candidate.applicability(),
                GenericCallVectorApplicability::ArgumentNotAssignable { .. }
            ),
        }
    }

    fn constraint_error(&self) -> bool {
        matches!(self, Self::Generic(candidate) if matches!(candidate.applicability(),
            GenericCallVectorApplicability::ExplicitTypeArgumentConstraint { .. }))
    }
}

/// The default cache has already been authenticated by the method provider.
fn type_argument_bounds(
    store: &CanonicalTypeMapperStore,
    callable: &ValidatedSingleCallable,
) -> Result<(usize, usize), GenericMethodCallError> {
    let signature = store
        .signature(callable.signature)
        .ok_or(GenericMethodCallError::Invalid(callable.owner))?;
    let no_constraint = store
        .intrinsic_bootstrap()
        .ok_or(GenericMethodCallError::Invalid(callable.owner))?
        .no_constraint_type;
    let mut minimum = 0;
    for (index, parameter) in signature.type_parameters().iter().enumerate() {
        let Some(TypeData::TypeParameter(parameter)) =
            store.type_payload(*parameter).map(|record| record.data())
        else {
            return Err(GenericMethodCallError::Invalid(callable.owner));
        };
        match parameter.resolved_default_type {
            Some(default) if default != no_constraint => {}
            Some(_) => minimum = index + 1,
            None => return Err(GenericMethodCallError::Invalid(callable.owner)),
        }
    }
    Ok((minimum, signature.type_parameters().len()))
}

fn has_type_argument_arity(bounds: (usize, usize), explicit: Option<&[TypeId]>) -> bool {
    explicit.is_none_or(|arguments| {
        arguments.is_empty() || (bounds.0..=bounds.1).contains(&arguments.len())
    })
}

#[allow(clippy::too_many_arguments)]
fn check_candidate(
    store: &mut CanonicalTypeMapperStore,
    globals: &CanonicalGlobalTypes,
    strict_function_types: bool,
    request: GenericCallVectorRequest<'_>,
    callable: &ValidatedSingleCallable,
    relation: GenericCallArgumentRelation,
    session: &mut InstantiationSession,
) -> Result<CheckedMethodCandidate, GenericMethodCallError> {
    if !store
        .signature(callable.signature)
        .ok_or(GenericMethodCallError::Invalid(request.callee))?
        .type_parameters()
        .is_empty()
    {
        return check_generic_call_candidate_with_session(
            store,
            globals,
            strict_function_types,
            request,
            callable,
            relation,
            session,
        )
        .map(CheckedMethodCandidate::Generic)
        .map_err(Into::into);
    }
    let mut candidate = project_validated_direct_call(
        store,
        Some(globals),
        DirectCallRequest {
            form: request.form,
            optional_chain: request.optional_chain,
            type_argument_count: 0,
            has_spread_argument: request.has_spread_argument,
            callee: request.callee,
            arguments: request.arguments,
        },
        callable,
    )?;
    if candidate.applicability == DirectCallApplicability::Applicable {
        candidate.applicability =
            check_argument_applicability(&candidate.projection, |source, target| match relation {
                GenericCallArgumentRelation::Assignable => store
                    .is_type_assignable_to_with_global_types_and_strict_function_types(
                        source,
                        target,
                        globals,
                        strict_function_types,
                    ),
                GenericCallArgumentRelation::Subtype {
                    strict_function_types,
                } => store.is_type_subtype_of_with_global_types_and_strict_function_types(
                    source,
                    target,
                    globals,
                    strict_function_types,
                ),
            })?;
    }
    Ok(CheckedMethodCandidate::Fixed(candidate))
}

#[allow(clippy::too_many_arguments)]
fn finish_candidate(
    store: &mut CanonicalTypeMapperStore,
    globals: &CanonicalGlobalTypes,
    strict_function_types: bool,
    request: GenericCallVectorRequest<'_>,
    candidate: CheckedMethodCandidate,
    existing_call_signature: Option<SignatureId>,
    session: &mut InstantiationSession,
) -> Result<GenericMethodCallSelection, GenericMethodCallError> {
    match candidate {
        CheckedMethodCandidate::Fixed(candidate) => fixed_selection(
            request.callee,
            candidate.projection.signature,
            candidate.projection.return_type,
            existing_call_signature,
        ),
        CheckedMethodCandidate::Generic(candidate) => finish_generic_call_candidate_with_session(
            store,
            globals,
            strict_function_types,
            request,
            candidate,
            existing_call_signature,
            session,
        )
        .map(GenericMethodCallSelection::Generic)
        .map_err(Into::into),
    }
}

fn fixed_selection(
    callee: TypeId,
    signature: SignatureId,
    return_type: TypeId,
    existing: Option<SignatureId>,
) -> Result<GenericMethodCallSelection, GenericMethodCallError> {
    if existing.is_some_and(|existing| existing != signature) {
        return Err(GenericMethodCallError::Invalid(callee));
    }
    Ok(GenericMethodCallSelection::Fixed {
        signature,
        return_type,
    })
}

/// Uses Go's first signature with enough parameters, or the longest signature.
fn recovery_candidate<'a>(
    store: &CanonicalTypeMapperStore,
    globals: &CanonicalGlobalTypes,
    callee: TypeId,
    candidates: &[&'a ValidatedSingleCallable],
    argument_count: usize,
) -> Result<&'a ValidatedSingleCallable, GenericMethodCallError> {
    let mut longest = None;
    let mut maximum = 0;
    for &candidate in candidates {
        let count = get_parameter_count(store, Some(globals), candidate)?;
        if has_effective_rest_parameter(store, Some(globals), candidate)? || count >= argument_count
        {
            return Ok(candidate);
        }
        if longest.is_none() || count > maximum {
            longest = Some(candidate);
            maximum = count;
        }
    }
    longest.ok_or(GenericMethodCallError::Invalid(callee))
}

/// Call syntax and contextual arguments remain owned by the source caller.
#[allow(clippy::too_many_arguments, clippy::too_many_lines)]
pub(super) fn resolve_generic_method_call(
    store: &mut CanonicalTypeMapperStore,
    globals: &CanonicalGlobalTypes,
    strict_function_types: bool,
    request: GenericCallVectorRequest<'_>,
    existing_call_signature: Option<SignatureId>,
    session: &mut InstantiationSession,
) -> Result<Option<GenericMethodCallResolution>, GenericMethodCallError> {
    if request.form != DirectCallForm::Call || request.optional_chain || request.has_spread_argument
    {
        return Ok(None);
    }
    let Some(structured) = store
        .type_payload(request.callee)
        .and_then(|record| record.data().structured())
    else {
        return Ok(None);
    };
    let Some(signatures) = structured.signatures.as_deref() else {
        return Ok(None);
    };
    if signatures.is_empty()
        || !signatures.iter().any(|signature| {
            store
                .signature(*signature)
                .is_some_and(|signature| !signature.type_parameters().is_empty())
        })
        || signatures.iter().any(|signature| {
            store
                .interface_method_linked_type(*signature)
                .or_else(|| store.type_literal_method_linked_type(*signature))
                != Some(request.callee)
        })
    {
        return Ok(None);
    }
    validate_generic_call_vector_request(store, request)?;
    let projection = match validate_stored_callable_set_with_array_targets(
        store,
        request.callee,
        Some(CanonicalArrayTargets::from_global_types(globals)),
    ) {
        StoredCallableSetValidation::Valid { projection, .. }
            if projection.construct_signatures.is_empty()
                && !projection.call_signatures.is_empty() =>
        {
            projection
        }
        StoredCallableSetValidation::Malformed { .. } => {
            return Err(GenericMethodCallError::Invalid(request.callee));
        }
        _ => return Err(GenericMethodCallError::Unsupported(request.callee)),
    };
    let ordered =
        reorder_direct_call_candidates(store, request.callee, &projection.call_signatures)?;
    let bounds = ordered
        .iter()
        .map(|candidate| type_argument_bounds(store, candidate))
        .collect::<Result<Vec<_>, _>>()?;
    let passes = [
        GenericCallArgumentRelation::Subtype {
            strict_function_types,
        },
        GenericCallArgumentRelation::Assignable,
    ];
    let mut argument_errors = Vec::new();
    let mut constraint_error = None;
    for relation in passes.into_iter().skip(usize::from(ordered.len() == 1)) {
        argument_errors.clear();
        constraint_error = None;
        for (&callable, &bounds) in ordered.iter().zip(&bounds) {
            if !has_type_argument_arity(bounds, request.explicit_type_arguments) {
                continue;
            }
            // Reuse the fixed, optional, and omitted-void bounds from ordinary calls.
            if bounds.1 != 0
                && (request.arguments.len()
                    < get_min_argument_count(
                        store,
                        Some(globals),
                        callable,
                        MinArgumentCountFlags::NONE,
                    )?
                    || callable.rest_parameter.is_none()
                        && request.arguments.len() > callable.parameters.len())
            {
                continue;
            }
            let candidate = check_candidate(
                store,
                globals,
                strict_function_types,
                request,
                callable,
                relation,
                session,
            )?;
            if candidate.applicable() {
                return finish_candidate(
                    store,
                    globals,
                    strict_function_types,
                    request,
                    candidate,
                    existing_call_signature,
                    session,
                )
                .map(|selected| {
                    Some(GenericMethodCallResolution {
                        selected,
                        diagnostic: None,
                    })
                });
            }
            if candidate.argument_error() {
                argument_errors.push(candidate.diagnostic());
            } else if candidate.constraint_error() {
                constraint_error = Some(candidate.diagnostic());
            }
        }
    }
    let diagnostic = if argument_errors.len() == 1 {
        argument_errors
            .pop()
            .expect("the sole argument error is present")
    } else if !argument_errors.is_empty() {
        // TS2769 chains and overload implementation notes remain a separate boundary.
        return Err(GenericMethodCallError::Unsupported(request.callee));
    } else if let Some(diagnostic) = constraint_error {
        diagnostic
    } else {
        // Arity notes use the original declaration order, not overload search order.
        let mut eligible = Vec::new();
        for candidate in &projection.call_signatures {
            if has_type_argument_arity(
                type_argument_bounds(store, candidate)?,
                request.explicit_type_arguments,
            ) {
                eligible.push(candidate);
            }
        }
        if eligible.is_empty() && ordered.len() == 1 {
            check_candidate(
                store,
                globals,
                strict_function_types,
                request,
                ordered[0],
                GenericCallArgumentRelation::Assignable,
                session,
            )?
            .diagnostic()
        } else if eligible.is_empty() {
            let actual = request
                .explicit_type_arguments
                .ok_or(GenericMethodCallError::Invalid(request.callee))?
                .len();
            let below = bounds
                .iter()
                .filter_map(|&(_, maximum)| (maximum < actual).then_some(maximum))
                .max();
            let above = bounds
                .iter()
                .filter_map(|&(minimum, _)| (minimum > actual).then_some(minimum))
                .min();
            let expected = match (below, above) {
                (Some(expected), None) | (None, Some(expected)) => expected,
                _ => return Err(GenericMethodCallError::Unsupported(request.callee)),
            };
            GenericMethodCallDiagnostic::TypeArgumentArity { expected, actual }
        } else {
            let first = eligible[0];
            let minimum =
                get_min_argument_count(store, Some(globals), first, MinArgumentCountFlags::NONE)?;
            let maximum = get_parameter_count(store, Some(globals), first)?;
            let rest = has_effective_rest_parameter(store, Some(globals), first)?;
            for candidate in &eligible {
                if get_min_argument_count(
                    store,
                    Some(globals),
                    candidate,
                    MinArgumentCountFlags::NONE,
                )? != minimum
                    || get_parameter_count(store, Some(globals), candidate)? != maximum
                    || has_effective_rest_parameter(store, Some(globals), candidate)? != rest
                {
                    return Err(GenericMethodCallError::Unsupported(request.callee));
                }
            }
            let candidate = check_candidate(
                store,
                globals,
                strict_function_types,
                request,
                first,
                GenericCallArgumentRelation::Assignable,
                session,
            )?;
            if candidate.applicable() {
                return Err(GenericMethodCallError::Invalid(request.callee));
            }
            candidate.diagnostic()
        }
    };
    let recovery = recovery_candidate(
        store,
        globals,
        request.callee,
        &ordered,
        request.arguments.len(),
    )?;
    let selected = if store
        .signature(recovery.signature)
        .ok_or(GenericMethodCallError::Invalid(request.callee))?
        .type_parameters()
        .is_empty()
    {
        // Go returns this signature without checking its argument relation again.
        let return_type = recovery.return_type.ok_or(GenericMethodCallError::Direct(
            DirectCallError::Unsupported(DirectCallUnsupported::UnresolvedReturnType(
                recovery.signature,
            )),
        ))?;
        fixed_selection(
            request.callee,
            recovery.signature,
            return_type,
            existing_call_signature,
        )?
    } else {
        let candidate = check_candidate(
            store,
            globals,
            strict_function_types,
            request,
            recovery,
            GenericCallArgumentRelation::Assignable,
            session,
        )?;
        finish_candidate(
            store,
            globals,
            strict_function_types,
            request,
            candidate,
            existing_call_signature,
            session,
        )?
    };
    Ok(Some(GenericMethodCallResolution {
        selected,
        diagnostic: Some(diagnostic),
    }))
}
