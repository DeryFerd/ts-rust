//! Overload selection for methods, source functions, and completed class constructors.
//!
//! The ordinary and generic call engines check each real candidate. This module
//! owns declaration-group order, the two relation passes, and failure selection.
//! A diagnostic candidate can differ from the signature used for recovery.

use super::{
    CanonicalGlobalTypes, CanonicalTypeMapperStore, MinArgumentCountFlags, RelationUnavailable,
    SignatureId, TypeId,
    array_types::CanonicalArrayTargets,
    callable_sets::{StoredCallableSetValidation, validate_stored_callable_set_with_array_targets},
    callables::{CallableFamily, ValidatedSingleCallable},
    calls::{
        DirectCallApplicability, DirectCallError, DirectCallForm, DirectCallRequest,
        DirectCallResolution, DirectCallUnsupported, check_argument_applicability,
        get_min_argument_count, get_parameter_count, has_effective_rest_parameter,
        project_validated_direct_call, reorder_direct_call_candidates,
    },
    conditional_types::ConditionalBranchSource,
    generic_calls::{
        GenericCallArgumentRelation, GenericCallVectorApplicability, GenericCallVectorCandidate,
        GenericCallVectorError, GenericCallVectorRequest, GenericCallVectorResolution,
        GenericConstructorContextMethod, PreparedGenericConstructorContext,
        check_generic_call_candidate_with_context,
        check_generic_call_candidate_with_receiver_context,
        demand_generic_call_vector_return_with_source, finish_generic_call_candidate_with_source,
        generic_class_constructor_candidates, generic_class_constructor_type_argument_bounds,
        generic_method_signature_callee, generic_method_type_argument_bounds,
        generic_named_constructor_candidates, preflight_generic_class_constructor_signature,
        prepare_generic_constructor_context_with_session, validate_generic_call_vector_request,
        validate_generic_class_constructor_request,
    },
    instantiate::InstantiationSession,
    relation::RelationKind,
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
    ConstructorOverload(Box<GenericMethodCallDiagnostic>),
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

#[derive(Clone, Copy)]
enum GenericCandidateFamily {
    Call(CallableFamily),
    ClassConstruct,
    NamedConstruct,
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
                    | GenericCallVectorApplicability::ThisArgumentNotAssignable { .. }
            ),
        }
    }

    fn constraint_error(&self) -> bool {
        matches!(self, Self::Generic(candidate) if matches!(candidate.applicability(),
            GenericCallVectorApplicability::ExplicitTypeArgumentConstraint { .. }))
    }
}

/// Methods use source absence. Source overloads keep their validated sentinel caches.
fn type_argument_bounds(
    store: &CanonicalTypeMapperStore,
    callable: &ValidatedSingleCallable,
    family: CallableFamily,
    array_targets: Option<CanonicalArrayTargets>,
) -> Result<(usize, usize), GenericMethodCallError> {
    if family != CallableFamily::SourceFunctionOverloads {
        return generic_method_type_argument_bounds(store, callable, array_targets)
            .map_err(GenericMethodCallError::from);
    }
    let signature = store
        .signature(callable.signature)
        .ok_or(GenericMethodCallError::Invalid(callable.owner))?;
    let no_constraint = store
        .intrinsic_bootstrap()
        .ok_or(GenericMethodCallError::Invalid(callable.owner))?
        .no_constraint_type;
    let mut minimum = 0;
    for (index, parameter) in signature.type_parameters().iter().enumerate() {
        let Some(TypeData::TypeParameter(parameter)) = store
            .type_payload(*parameter)
            .map(super::type_records::TypeRecord::data)
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

fn candidate_type_argument_bounds(
    store: &CanonicalTypeMapperStore,
    callable: &ValidatedSingleCallable,
    family: GenericCandidateFamily,
    array_targets: Option<CanonicalArrayTargets>,
) -> Result<(usize, usize), GenericMethodCallError> {
    match family {
        GenericCandidateFamily::Call(family) => {
            type_argument_bounds(store, callable, family, array_targets)
        }
        GenericCandidateFamily::ClassConstruct => {
            generic_class_constructor_type_argument_bounds(store, callable, array_targets)
                .map_err(Into::into)
        }
        GenericCandidateFamily::NamedConstruct => {
            generic_method_type_argument_bounds(store, callable, array_targets).map_err(Into::into)
        }
    }
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
    this_argument: Option<TypeId>,
    source: &mut Option<&mut dyn ConditionalBranchSource>,
) -> Result<CheckedMethodCandidate, GenericMethodCallError> {
    if !store
        .signature(callable.signature)
        .ok_or(GenericMethodCallError::Invalid(request.callee))?
        .type_parameters()
        .is_empty()
    {
        return check_generic_call_candidate_with_receiver_context(
            store,
            globals,
            strict_function_types,
            request,
            callable,
            relation,
            None,
            session,
            this_argument,
            source,
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
        let (relation, strict_function_types) = match relation {
            GenericCallArgumentRelation::Assignable => {
                (RelationKind::Assignable, strict_function_types)
            }
            GenericCallArgumentRelation::Subtype {
                strict_function_types,
            } => (RelationKind::Subtype, strict_function_types),
        };
        candidate.applicability =
            check_argument_applicability(&candidate.projection, |source, target| {
                store.is_type_related_to_with_session(
                    source,
                    target,
                    relation,
                    Some(globals),
                    Some(strict_function_types),
                    session,
                )
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
    source: &mut Option<&mut dyn ConditionalBranchSource>,
) -> Result<GenericMethodCallSelection, GenericMethodCallError> {
    match candidate {
        CheckedMethodCandidate::Fixed(candidate) => fixed_selection(
            request.callee,
            candidate.projection.signature,
            candidate.projection.return_type,
            existing_call_signature,
        ),
        CheckedMethodCandidate::Generic(candidate) => {
            let resolution = finish_generic_call_candidate_with_source(
                store,
                globals,
                strict_function_types,
                request,
                candidate,
                existing_call_signature,
                session,
                source,
            )?;
            if source.is_some() {
                demand_generic_call_vector_return_with_source(
                    store,
                    &resolution,
                    globals,
                    session,
                    source,
                )?;
            }
            Ok(GenericMethodCallSelection::Generic(resolution))
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn check_candidate_with_context(
    store: &mut CanonicalTypeMapperStore,
    globals: &CanonicalGlobalTypes,
    strict_function_types: bool,
    request: GenericCallVectorRequest<'_>,
    callable: &ValidatedSingleCallable,
    relation: GenericCallArgumentRelation,
    session: &mut InstantiationSession,
    context: Option<&PreparedGenericConstructorContext>,
    this_argument: Option<TypeId>,
    source: &mut Option<&mut dyn ConditionalBranchSource>,
) -> Result<CheckedMethodCandidate, GenericMethodCallError> {
    match context {
        None => check_candidate(
            store,
            globals,
            strict_function_types,
            request,
            callable,
            relation,
            session,
            this_argument,
            source,
        ),
        Some(context) => check_generic_call_candidate_with_context(
            store,
            globals,
            strict_function_types,
            request,
            callable,
            relation,
            Some(context),
            session,
        )
        .map(CheckedMethodCandidate::Generic)
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
    resolve_generic_method_call_worker(
        store,
        globals,
        strict_function_types,
        request,
        existing_call_signature,
        session,
        None,
        &mut None,
    )
}

#[allow(clippy::too_many_arguments)]
pub(super) fn resolve_generic_method_call_with_source(
    store: &mut CanonicalTypeMapperStore,
    globals: &CanonicalGlobalTypes,
    strict_function_types: bool,
    request: GenericCallVectorRequest<'_>,
    existing_call_signature: Option<SignatureId>,
    session: &mut InstantiationSession,
    this_argument: Option<TypeId>,
    source: &mut dyn ConditionalBranchSource,
) -> Result<Option<GenericMethodCallResolution>, GenericMethodCallError> {
    resolve_generic_method_call_worker(
        store,
        globals,
        strict_function_types,
        request,
        existing_call_signature,
        session,
        this_argument,
        &mut Some(source),
    )
}

#[allow(clippy::too_many_arguments)]
fn resolve_generic_method_call_worker(
    store: &mut CanonicalTypeMapperStore,
    globals: &CanonicalGlobalTypes,
    strict_function_types: bool,
    request: GenericCallVectorRequest<'_>,
    existing_call_signature: Option<SignatureId>,
    session: &mut InstantiationSession,
    this_argument: Option<TypeId>,
    source: &mut Option<&mut dyn ConditionalBranchSource>,
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
    {
        return Ok(None);
    }
    let array_targets = Some(CanonicalArrayTargets::from_global_types(globals));
    let source_overloads = store.source_overload_provenance(request.callee).is_some();
    if !source_overloads {
        for &signature in signatures {
            if generic_method_signature_callee(store, signature, array_targets)?
                != Some(request.callee)
            {
                return Ok(None);
            }
        }
    }
    validate_generic_call_vector_request(store, request)?;
    let (family, projection) =
        match validate_stored_callable_set_with_array_targets(store, request.callee, array_targets)
        {
            StoredCallableSetValidation::Valid {
                family, projection, ..
            } if projection.construct_signatures.is_empty()
                && !projection.call_signatures.is_empty()
                && (!source_overloads || family == CallableFamily::SourceFunctionOverloads) =>
            {
                (family, projection)
            }
            StoredCallableSetValidation::Malformed { .. } => {
                return Err(GenericMethodCallError::Invalid(request.callee));
            }
            _ => return Err(GenericMethodCallError::Unsupported(request.callee)),
        };
    resolve_generic_candidates_with_context(
        store,
        globals,
        strict_function_types,
        request,
        &projection.call_signatures,
        GenericCandidateFamily::Call(family),
        existing_call_signature,
        session,
        None,
        this_argument,
        source,
    )
}

/// New uses real class construct rows and forwards its exact retained signature.
pub(super) fn resolve_generic_class_constructor(
    store: &mut CanonicalTypeMapperStore,
    globals: &CanonicalGlobalTypes,
    strict_function_types: bool,
    request: GenericCallVectorRequest<'_>,
    existing_new_signature: Option<SignatureId>,
    session: &mut InstantiationSession,
) -> Result<Option<GenericMethodCallResolution>, GenericMethodCallError> {
    resolve_generic_class_constructor_with_context(
        store,
        globals,
        strict_function_types,
        request,
        existing_new_signature,
        session,
        None,
    )
}

#[allow(clippy::too_many_arguments)]
pub(super) fn resolve_generic_class_constructor_with_context(
    store: &mut CanonicalTypeMapperStore,
    globals: &CanonicalGlobalTypes,
    strict_function_types: bool,
    request: GenericCallVectorRequest<'_>,
    existing_new_signature: Option<SignatureId>,
    session: &mut InstantiationSession,
    context: Option<&PreparedGenericConstructorContext>,
) -> Result<Option<GenericMethodCallResolution>, GenericMethodCallError> {
    if request.form != DirectCallForm::New || request.optional_chain || request.has_spread_argument
    {
        return Ok(None);
    }
    let array_targets = Some(CanonicalArrayTargets::from_global_types(globals));
    let class = generic_class_constructor_candidates(store, request.callee, array_targets)?;
    let named = if class.is_none() {
        generic_named_constructor_candidates(store, request.callee, array_targets)?
    } else {
        None
    };
    let (candidates, family) = if let Some(class) = &class {
        if class.type_parameters().is_empty() {
            return Ok(None);
        }
        (class.signatures(), GenericCandidateFamily::ClassConstruct)
    } else if let Some(named) = &named {
        (named.as_ref(), GenericCandidateFamily::NamedConstruct)
    } else {
        return Ok(None);
    };
    if let Some(context) = context {
        if !matches!(family, GenericCandidateFamily::NamedConstruct)
            || candidates.len() != 1
            || context.callee() != request.callee
            || context.signature() != candidates[0].signature
        {
            return Err(GenericMethodCallError::Invalid(request.callee));
        }
    }
    validate_generic_class_constructor_request(store, request, array_targets)?;
    if let Some(signature) = existing_new_signature {
        preflight_generic_class_constructor_signature(
            store,
            request.callee,
            signature,
            array_targets,
        )?;
    }
    let limit_mark = session.limit_event_mark();
    let selected = resolve_generic_candidates_with_context(
        store,
        globals,
        strict_function_types,
        request,
        candidates,
        family,
        existing_new_signature,
        session,
        context,
        None,
        &mut None,
    )?;
    if session.limit_event_occurred_since(limit_mark) {
        return Err(GenericMethodCallError::Unsupported(request.callee));
    }
    Ok(selected)
}

#[allow(clippy::too_many_arguments)]
pub(super) fn prepare_generic_constructor_context(
    store: &mut CanonicalTypeMapperStore,
    globals: &CanonicalGlobalTypes,
    strict_function_types: bool,
    request: GenericCallVectorRequest<'_>,
    existing_new_signature: Option<SignatureId>,
    methods: &[GenericConstructorContextMethod],
    session: &mut InstantiationSession,
) -> Result<PreparedGenericConstructorContext, GenericMethodCallError> {
    let array_targets = Some(CanonicalArrayTargets::from_global_types(globals));
    validate_generic_class_constructor_request(store, request, array_targets)?;
    let candidates = generic_named_constructor_candidates(store, request.callee, array_targets)?
        .ok_or(GenericMethodCallError::Unsupported(request.callee))?;
    if candidates.len() != 1 {
        return Err(GenericMethodCallError::Unsupported(request.callee));
    }
    if let Some(signature) = existing_new_signature {
        preflight_generic_class_constructor_signature(
            store,
            request.callee,
            signature,
            array_targets,
        )?;
    }
    let ordered = reorder_direct_call_candidates(store, request.callee, &candidates)?;
    let [callable] = ordered.as_slice() else {
        return Err(GenericMethodCallError::Invalid(request.callee));
    };
    prepare_generic_constructor_context_with_session(
        store,
        globals,
        strict_function_types,
        request,
        callable,
        methods,
        session,
    )
    .map_err(Into::into)
}

#[allow(clippy::too_many_arguments, clippy::too_many_lines)]
fn resolve_generic_candidates(
    store: &mut CanonicalTypeMapperStore,
    globals: &CanonicalGlobalTypes,
    strict_function_types: bool,
    request: GenericCallVectorRequest<'_>,
    candidates: &[ValidatedSingleCallable],
    family: GenericCandidateFamily,
    existing_call_signature: Option<SignatureId>,
    session: &mut InstantiationSession,
) -> Result<Option<GenericMethodCallResolution>, GenericMethodCallError> {
    resolve_generic_candidates_with_context(
        store,
        globals,
        strict_function_types,
        request,
        candidates,
        family,
        existing_call_signature,
        session,
        None,
        None,
        &mut None,
    )
}

#[allow(clippy::too_many_arguments, clippy::too_many_lines)]
fn resolve_generic_candidates_with_context(
    store: &mut CanonicalTypeMapperStore,
    globals: &CanonicalGlobalTypes,
    strict_function_types: bool,
    request: GenericCallVectorRequest<'_>,
    candidates: &[ValidatedSingleCallable],
    family: GenericCandidateFamily,
    existing_call_signature: Option<SignatureId>,
    session: &mut InstantiationSession,
    context: Option<&PreparedGenericConstructorContext>,
    this_argument: Option<TypeId>,
    source: &mut Option<&mut dyn ConditionalBranchSource>,
) -> Result<Option<GenericMethodCallResolution>, GenericMethodCallError> {
    let array_targets = Some(CanonicalArrayTargets::from_global_types(globals));
    let ordered = reorder_direct_call_candidates(store, request.callee, candidates)?;
    let bounds = ordered
        .iter()
        .map(|candidate| candidate_type_argument_bounds(store, candidate, family, array_targets))
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
            let candidate = check_candidate_with_context(
                store,
                globals,
                strict_function_types,
                request,
                callable,
                relation,
                session,
                context,
                this_argument,
                source,
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
                    source,
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
    } else if !argument_errors.is_empty()
        && matches!(family, GenericCandidateFamily::NamedConstruct)
    {
        // Go reports the last failed overload, but chooses recovery independently.
        GenericMethodCallDiagnostic::ConstructorOverload(Box::new(
            argument_errors
                .pop()
                .expect("the last overload error is present"),
        ))
    } else if !argument_errors.is_empty() {
        // TS2769 chains and overload implementation notes remain a separate boundary.
        return Err(GenericMethodCallError::Unsupported(request.callee));
    } else if let Some(diagnostic) = constraint_error {
        diagnostic
    } else {
        // Arity notes use the original declaration order, not overload search order.
        let mut eligible = Vec::new();
        for candidate in candidates {
            if has_type_argument_arity(
                candidate_type_argument_bounds(store, candidate, family, array_targets)?,
                request.explicit_type_arguments,
            ) {
                eligible.push(candidate);
            }
        }
        if eligible.is_empty() && ordered.len() == 1 {
            check_candidate_with_context(
                store,
                globals,
                strict_function_types,
                request,
                ordered[0],
                GenericCallArgumentRelation::Assignable,
                session,
                context,
                this_argument,
                source,
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
            let ((Some(expected), None) | (None, Some(expected))) = (below, above) else {
                return Err(GenericMethodCallError::Unsupported(request.callee));
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
            let candidate = check_candidate_with_context(
                store,
                globals,
                strict_function_types,
                request,
                first,
                GenericCallArgumentRelation::Assignable,
                session,
                context,
                this_argument,
                source,
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
        let candidate = check_candidate_with_context(
            store,
            globals,
            strict_function_types,
            request,
            recovery,
            GenericCallArgumentRelation::Assignable,
            session,
            context,
            this_argument,
            source,
        )?;
        finish_candidate(
            store,
            globals,
            strict_function_types,
            request,
            candidate,
            existing_call_signature,
            session,
            source,
        )?
    };
    Ok(Some(GenericMethodCallResolution {
        selected,
        diagnostic: Some(diagnostic),
    }))
}

#[cfg(test)]
mod tests {
    use ts_ast::{FileId, NodeData, NodeRef};
    use ts_binder::{
        CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
        EscapedName, SemanticSymbolId,
    };
    use ts_parser::{ParseResult, parse_source_file};

    use super::*;
    use crate::semantic::{
        CanonicalCheckerContext, CanonicalCheckerOptions, ValueSymbolLinks,
        bootstrap::{LiteralTypeCacheError, UnionReduction},
        callables::{StoredSingleCallableValidation, validate_stored_single_callable},
        declared::type_list_key,
        derived_types::DerivedTypeError,
        generic_calls::demand_generic_call_vector_selected_return,
        inference::NakedTypeCandidateError,
        instantiate::{InstantiationError, InstantiationLimits, instantiate_type_with_session},
        instantiated_members::validate_generic_interface_members,
        store::CachedSignatureLookup,
        structured_members::{
            InterfaceHeritageMembersValidation, validate_interface_heritage_members,
        },
        types::ObjectFlags,
    };

    const LIBRARY: FileId = FileId::new(163_100);
    const SOURCE: FileId = FileId::new(163_101);

    mod constructors {
        use super::*;
        use crate::semantic::{
            classes::CompletedSourceClassConstructors,
            generic_calls::{
                GenericCallVectorInvariant, GenericCallVectorUnsupported,
                demand_generic_call_signature_return_with_session,
                preflight_generic_call_signature_return_target,
            },
            reference_types::validate_direct_generic_reference,
            signatures::SignatureFlags,
        };

        const ARRAY_LIBRARY: &str = "interface Array<T> {} interface ReadonlyArray<T> {}";

        fn source_value(store: &CanonicalTypeMapperStore, name: &str) -> TypeId {
            let symbol = store
                .symbol_table(store.intrinsic_bootstrap().unwrap().globals)
                .and_then(|globals| globals.get_source(name))
                .and_then(|symbol| store.get_merged_symbol(symbol))
                .unwrap();
            store
                .value_symbol_links(symbol)
                .unwrap()
                .resolved_type
                .unwrap()
        }

        fn constructors(
            context: &CanonicalCheckerContext<'_>,
            name: &str,
        ) -> CompletedSourceClassConstructors {
            generic_class_constructor_candidates(
                context.store(),
                source_value(context.store(), name),
                Some(CanonicalArrayTargets::from_global_types(
                    context.global_types(),
                )),
            )
            .unwrap()
            .unwrap()
        }

        fn applicable_generic(
            resolution: GenericMethodCallResolution,
        ) -> GenericCallVectorResolution {
            assert_eq!(resolution.diagnostic, None);
            let GenericMethodCallSelection::Generic(generic) = resolution.selected else {
                panic!("a generic class must retain its instantiated constructor")
            };
            generic
        }

        fn assert_class_return(
            store: &mut CanonicalTypeMapperStore,
            generic: &GenericCallVectorResolution,
            origin: TypeId,
            session: &mut InstantiationSession,
        ) -> SignatureId {
            let projection = generic.projection();
            let selected = projection.instantiation.signature;
            let return_type = demand_generic_call_vector_selected_return(store, generic, session)
                .unwrap()
                .0;
            let reference = validate_direct_generic_reference(store, return_type).unwrap();
            assert_eq!(reference.target, origin);
            assert_eq!(
                reference.type_arguments,
                projection.instantiation.type_arguments
            );
            let signature = store.signature(selected).unwrap();
            assert!(signature.flags().contains(SignatureFlags::CONSTRUCT));
            assert_eq!(signature.target(), Some(projection.generic_signature));
            assert_eq!(signature.mapper(), Some(projection.instantiation.mapper));
            assert!(signature.type_parameters().is_empty());
            assert_eq!(signature.resolved_return_type(), Some(return_type));
            selected
        }

        #[test]
        #[allow(clippy::too_many_lines)] // The same source formals cover explicit, defaulted, and inferred requests.
        fn class_constructor_vectors_keep_real_formals_defaults_and_canonical_returns() {
            let library = parse_source_file(ARRAY_LIBRARY);
            let source = parse_source_file(concat!(
                "class Pair<T, U = T> { constructor(first: T, second: U) {} } ",
                "class Defaults<T = string, U = T[]> {} ",
                "class Unused<T> {} class Model<T extends string> {}",
            ));
            let mut context = relation_context(&library, &source);
            context.check_source_file(SOURCE).unwrap();
            assert!(context.diagnostics().is_empty());
            let pair = constructors(&context, "Pair");
            let defaults = constructors(&context, "Defaults");
            let unused = constructors(&context, "Unused");
            let model = constructors(&context, "Model");
            let globals = context.global_types().clone();
            let arrays = CanonicalArrayTargets::from_global_types(&globals);
            let store = context.store_mut_for_test();
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            let (number, string, unknown) = (
                bootstrap.number_type,
                bootstrap.string_type,
                bootstrap.unknown_type,
            );
            let pair_formals = pair
                .type_parameters()
                .iter()
                .map(|parameter| parameter.type_parameter())
                .collect::<Vec<_>>();
            assert_eq!(
                pair.type_parameters()[1].default_type(),
                Some(pair_formals[0])
            );
            let mut session = InstantiationSession::new(InstantiationLimits::default());
            let full = [number, string];
            let prefix = [number];
            let equal = [number, number];
            let mut full_signature = None;
            for (explicit, arguments, expected) in [
                (Some(full.as_slice()), full.as_slice(), full.as_slice()),
                (Some(prefix.as_slice()), equal.as_slice(), equal.as_slice()),
                (None, full.as_slice(), full.as_slice()),
                (Some(&[][..]), full.as_slice(), full.as_slice()),
            ] {
                let request = GenericCallVectorRequest {
                    form: DirectCallForm::New,
                    optional_chain: false,
                    explicit_type_arguments: explicit,
                    has_spread_argument: false,
                    callee: pair.members().shells().value_type(),
                    arguments,
                };
                let generic = applicable_generic(
                    resolve_generic_class_constructor(
                        store,
                        &globals,
                        false,
                        request,
                        None,
                        &mut session,
                    )
                    .unwrap()
                    .unwrap(),
                );
                assert_eq!(generic.projection().type_parameters, pair_formals);
                assert_eq!(generic.projection().instantiation.type_arguments, expected);
                let signature = assert_class_return(
                    store,
                    &generic,
                    pair.members().shells().instance_type(),
                    &mut session,
                );
                if expected == full {
                    assert!(
                        full_signature
                            .replace(signature)
                            .is_none_or(|old| old == signature)
                    );
                }
                assert_eq!(
                    preflight_generic_class_constructor_signature(
                        store,
                        request.callee,
                        signature,
                        Some(arrays),
                    ),
                    Ok(pair.signatures()[0].signature)
                );
            }
            for explicit in [None, Some(prefix.as_slice())] {
                let generic = applicable_generic(
                    resolve_generic_class_constructor(
                        store,
                        &globals,
                        false,
                        GenericCallVectorRequest {
                            form: DirectCallForm::New,
                            optional_chain: false,
                            explicit_type_arguments: explicit,
                            has_spread_argument: false,
                            callee: defaults.members().shells().value_type(),
                            arguments: &[],
                        },
                        None,
                        &mut session,
                    )
                    .unwrap()
                    .unwrap(),
                );
                let expected = if explicit.is_some() { number } else { string };
                let arguments = &generic.projection().instantiation.type_arguments;
                assert_eq!(arguments[0], expected);
                assert_eq!(
                    store
                        .canonical_array_reference_with_targets(arrays, arguments[1])
                        .unwrap()
                        .unwrap()
                        .element_type,
                    expected
                );
                let signature = assert_class_return(
                    store,
                    &generic,
                    defaults.members().shells().instance_type(),
                    &mut session,
                );
                let before = cache_counts(store);
                assert!(
                    preflight_generic_class_constructor_signature(
                        store,
                        defaults.members().shells().value_type(),
                        signature,
                        None,
                    )
                    .is_err()
                );
                assert_eq!(cache_counts(store), before);
                assert_eq!(
                    preflight_generic_class_constructor_signature(
                        store,
                        defaults.members().shells().value_type(),
                        signature,
                        Some(arrays),
                    ),
                    Ok(defaults.signatures()[0].signature)
                );
            }
            for (constructors, expected) in [(&unused, unknown), (&model, string)] {
                let generic = applicable_generic(
                    resolve_generic_class_constructor(
                        store,
                        &globals,
                        false,
                        GenericCallVectorRequest {
                            form: DirectCallForm::New,
                            optional_chain: false,
                            explicit_type_arguments: None,
                            has_spread_argument: false,
                            callee: constructors.members().shells().value_type(),
                            arguments: &[],
                        },
                        None,
                        &mut session,
                    )
                    .unwrap()
                    .unwrap(),
                );
                assert_eq!(
                    generic.projection().instantiation.type_arguments,
                    [expected]
                );
                assert_class_return(
                    store,
                    &generic,
                    constructors.members().shells().instance_type(),
                    &mut session,
                );
            }
            assert_eq!(
                store
                    .signature(pair.signatures()[0].signature)
                    .unwrap()
                    .type_parameters(),
                pair_formals
            );
            assert_eq!(
                pair.type_parameters()[1].default_type(),
                Some(pair_formals[0])
            );
        }

        #[test]
        fn class_constructor_candidates_keep_overload_order_and_exclude_call_owners() {
            let library = parse_source_file(ARRAY_LIBRARY);
            let source = parse_source_file(concat!(
                "class Ordered<T> { constructor(value: T); ",
                "constructor(value: T, count: number); ",
                "constructor(value: T, count?: number) {} } ",
                "declare function identity<T>(value: T): T;",
            ));
            let mut context = relation_context(&library, &source);
            context.check_source_file(SOURCE).unwrap();
            assert!(context.diagnostics().is_empty());
            let constructors = constructors(&context, "Ordered");
            let function = source_function(&mut context, &source, "identity");
            let globals = context.global_types().clone();
            let arrays = CanonicalArrayTargets::from_global_types(&globals);
            let store = context.store_mut_for_test();
            let number = store.intrinsic_bootstrap().unwrap().number_type;
            let explicit = [number];
            let both = [number, number];
            let request = GenericCallVectorRequest {
                form: DirectCallForm::New,
                optional_chain: false,
                explicit_type_arguments: Some(&explicit),
                has_spread_argument: false,
                callee: constructors.members().shells().value_type(),
                arguments: &explicit,
            };
            assert_eq!(constructors.signatures().len(), 2);
            let hidden = constructors.implementation().unwrap().signature;
            let mut session = InstantiationSession::new(InstantiationLimits::default());
            for (index, arguments) in [explicit.as_slice(), both.as_slice()]
                .into_iter()
                .enumerate()
            {
                let generic = applicable_generic(
                    resolve_generic_class_constructor(
                        store,
                        &globals,
                        false,
                        GenericCallVectorRequest {
                            arguments,
                            ..request
                        },
                        None,
                        &mut session,
                    )
                    .unwrap()
                    .unwrap(),
                );
                assert_eq!(
                    generic.projection().generic_signature,
                    constructors.signatures()[index].signature
                );
                assert_ne!(generic.projection().generic_signature, hidden);
                assert_class_return(
                    store,
                    &generic,
                    constructors.members().shells().instance_type(),
                    &mut session,
                );
            }
            let before = cache_counts(store);
            assert!(
                preflight_generic_class_constructor_signature(
                    store,
                    request.callee,
                    hidden,
                    Some(arrays)
                )
                .is_err()
            );
            assert_eq!(
                resolve_generic_method_call(
                    store,
                    &globals,
                    false,
                    GenericCallVectorRequest {
                        form: DirectCallForm::Call,
                        ..request
                    },
                    None,
                    &mut session,
                ),
                Ok(None)
            );
            assert_eq!(
                resolve_generic_class_constructor(
                    store,
                    &globals,
                    false,
                    GenericCallVectorRequest {
                        callee: function.owner,
                        ..request
                    },
                    None,
                    &mut session,
                ),
                Ok(None)
            );
            assert_eq!(cache_counts(store), before);
        }

        #[test]
        #[allow(clippy::too_many_lines)] // Checked and recovery shells must reject damage before the next selection.
        fn class_constructor_warm_signatures_reject_damage_before_allocation() {
            let library = parse_source_file(ARRAY_LIBRARY);
            let source = parse_source_file("class Box<T> { constructor(value: T) {} }");
            let mut context = relation_context(&library, &source);
            context.check_source_file(SOURCE).unwrap();
            assert!(context.diagnostics().is_empty());
            let constructors = constructors(&context, "Box");
            let original = constructors.signatures()[0].signature;
            let origin = constructors.members().shells().instance_type();
            let globals = context.global_types().clone();
            let arrays = CanonicalArrayTargets::from_global_types(&globals);
            let store = context.store_mut_for_test();
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            let (number, string, error_type) = (
                bootstrap.number_type,
                bootstrap.string_type,
                bootstrap.error_type,
            );
            let numbers = [number];
            let strings = [string];
            let request = GenericCallVectorRequest {
                form: DirectCallForm::New,
                optional_chain: false,
                explicit_type_arguments: Some(&numbers),
                has_spread_argument: false,
                callee: constructors.members().shells().value_type(),
                arguments: &numbers,
            };
            let failed_request = GenericCallVectorRequest {
                arguments: &strings,
                ..request
            };
            let mut session = InstantiationSession::new(InstantiationLimits::default());
            let checked = applicable_generic(
                resolve_generic_class_constructor(
                    store,
                    &globals,
                    false,
                    request,
                    None,
                    &mut session,
                )
                .unwrap()
                .unwrap(),
            );
            let checked_signature = assert_class_return(store, &checked, origin, &mut session);
            let failed = resolve_generic_class_constructor(
                store,
                &globals,
                false,
                failed_request,
                None,
                &mut session,
            )
            .unwrap()
            .unwrap();
            assert!(matches!(
                failed.diagnostic,
                Some(GenericMethodCallDiagnostic::Generic {
                    applicability: GenericCallVectorApplicability::ArgumentNotAssignable { .. },
                    ..
                })
            ));
            let GenericMethodCallSelection::Generic(recovery) = failed.selected else {
                panic!("the erroneous New must keep a generic recovery signature")
            };
            let recovery_signature = assert_class_return(store, &recovery, origin, &mut session);
            assert_ne!(checked_signature, recovery_signature);
            assert_eq!(
                store.cached_signatures_contain(checked_signature),
                Some(true)
            );
            assert_eq!(
                store.cached_signatures_contain(recovery_signature),
                Some(false)
            );
            for (signature, request) in [
                (checked_signature, request),
                (recovery_signature, failed_request),
            ] {
                let mapper = store.signature(signature).unwrap().mapper().unwrap();
                let return_type = store.signature(signature).unwrap().resolved_return_type();
                for damage in 0..4 {
                    match damage {
                        0 => assert!(store.set_signature_target_and_mapper(
                            signature,
                            Some(original),
                            None
                        )),
                        1 => assert!(store.set_signature_target_and_mapper(
                            signature,
                            Some(signature),
                            Some(mapper)
                        )),
                        2 => assert!(
                            store.set_signature_resolved_return_type(signature, Some(origin))
                        ),
                        _ => assert!(
                            store.set_signature_resolved_return_type(signature, Some(error_type))
                        ),
                    }
                    let before = cache_counts(store);
                    let count = session.total_count();
                    assert!(
                        preflight_generic_class_constructor_signature(
                            store,
                            request.callee,
                            signature,
                            Some(arrays)
                        )
                        .is_err()
                    );
                    assert!(
                        resolve_generic_class_constructor(
                            store,
                            &globals,
                            false,
                            request,
                            Some(signature),
                            &mut session,
                        )
                        .is_err()
                    );
                    assert_eq!(cache_counts(store), before);
                    assert_eq!(session.total_count(), count);
                    assert!(store.set_signature_target_and_mapper(
                        signature,
                        Some(original),
                        Some(mapper)
                    ));
                    assert!(store.set_signature_resolved_return_type(signature, return_type));
                    assert_eq!(
                        preflight_generic_class_constructor_signature(
                            store,
                            request.callee,
                            signature,
                            Some(arrays)
                        ),
                        Ok(original)
                    );
                }
            }
            let before = cache_counts(store);
            for (request, signature) in [
                (request, recovery_signature),
                (failed_request, checked_signature),
            ] {
                assert_eq!(
                    resolve_generic_class_constructor(
                        store,
                        &globals,
                        false,
                        request,
                        Some(signature),
                        &mut session,
                    ),
                    Err(GenericMethodCallError::Generic(
                        GenericCallVectorError::Invariant(
                            GenericCallVectorInvariant::InvalidCallInstantiation {
                                target: original,
                                signature
                            },
                        )
                    ))
                );
                assert_eq!(cache_counts(store), before);
            }
            let warm = applicable_generic(
                resolve_generic_class_constructor(
                    store,
                    &globals,
                    false,
                    request,
                    Some(checked_signature),
                    &mut session,
                )
                .unwrap()
                .unwrap(),
            );
            assert_eq!(warm, checked);
            let replay = resolve_generic_class_constructor(
                store,
                &globals,
                false,
                failed_request,
                Some(recovery_signature),
                &mut session,
            )
            .unwrap()
            .unwrap();
            assert_eq!(
                replay.selected,
                GenericMethodCallSelection::Generic(recovery)
            );
            assert_eq!(cache_counts(store), before);
        }

        #[test]
        #[allow(clippy::too_many_lines)] // The only Array edge is the actual argument, not the class declaration.
        fn class_constructor_return_queries_prove_vector_authority_and_exact_cache_entries() {
            let library = parse_source_file(ARRAY_LIBRARY);
            let source = parse_source_file(concat!(
                "class Carrier<T> {} ",
                "function inputs(value: ReadonlyArray<string>): void {}",
            ));
            let mut context = relation_context(&library, &source);
            context.check_source_file(SOURCE).unwrap();
            assert!(context.diagnostics().is_empty());
            let constructors = constructors(&context, "Carrier");
            let input = source_function(&mut context, &source, "inputs");
            let globals = context.global_types().clone();
            let arrays = CanonicalArrayTargets::from_global_types(&globals);
            let wrong_arrays =
                CanonicalArrayTargets::for_test(arrays.readonly_array_type(), arrays.array_type());
            let mut wrong_globals = globals.clone();
            std::mem::swap(
                &mut wrong_globals.array_type,
                &mut wrong_globals.readonly_array_type,
            );
            let store = context.store_mut_for_test();
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            let (number, string, error_type) = (
                bootstrap.number_type,
                bootstrap.string_type,
                bootstrap.error_type,
            );
            let original = constructors.signatures()[0].signature;
            let callee = constructors.members().shells().value_type();
            let readonly = [input.parameters[0]];
            let request = GenericCallVectorRequest {
                form: DirectCallForm::New,
                optional_chain: false,
                explicit_type_arguments: Some(&readonly),
                has_spread_argument: false,
                callee,
                arguments: &[],
            };
            assert!(
                generic_class_constructor_candidates(store, callee, None)
                    .unwrap()
                    .is_some()
            );
            let mut session = InstantiationSession::new(InstantiationLimits::default());
            let before = cache_counts(store);
            assert_eq!(
                resolve_generic_class_constructor(
                    store,
                    &wrong_globals,
                    false,
                    request,
                    None,
                    &mut session,
                ),
                Err(GenericMethodCallError::Generic(
                    GenericCallVectorError::Invariant(
                        GenericCallVectorInvariant::InvalidTypeArgument {
                            index: 0,
                            type_: readonly[0]
                        },
                    )
                ))
            );
            assert_eq!(cache_counts(store), before);
            assert_eq!(session.total_count(), 0);
            let generic = applicable_generic(
                resolve_generic_class_constructor(
                    store,
                    &globals,
                    false,
                    request,
                    None,
                    &mut session,
                )
                .unwrap()
                .unwrap(),
            );
            let signature = assert_class_return(
                store,
                &generic,
                constructors.members().shells().instance_type(),
                &mut session,
            );
            for targets in [None, Some(wrong_arrays)] {
                let before = cache_counts(store);
                let count = session.total_count();
                assert!(
                    preflight_generic_call_signature_return_target(store, targets, signature)
                        .is_err()
                );
                assert!(
                    demand_generic_call_signature_return_with_session(
                        store,
                        targets,
                        signature,
                        &mut session
                    )
                    .is_err()
                );
                assert!(
                    preflight_generic_class_constructor_signature(
                        store, callee, signature, targets
                    )
                    .is_err()
                );
                assert_eq!(cache_counts(store), before);
                assert_eq!(session.total_count(), count);
            }
            assert_eq!(
                preflight_generic_call_signature_return_target(store, Some(arrays), signature),
                Ok(original)
            );

            let mut scalars = Vec::new();
            for type_ in [number, string] {
                let arguments = [type_];
                let generic = applicable_generic(
                    resolve_generic_class_constructor(
                        store,
                        &globals,
                        false,
                        GenericCallVectorRequest {
                            explicit_type_arguments: Some(&arguments),
                            ..request
                        },
                        None,
                        &mut session,
                    )
                    .unwrap()
                    .unwrap(),
                );
                assert_class_return(
                    store,
                    &generic,
                    constructors.members().shells().instance_type(),
                    &mut session,
                );
                scalars.push(generic);
            }
            let number_signature = scalars[0].projection().instantiation.signature;
            let number_mapper = scalars[0].projection().instantiation.mapper;
            let number_return = store
                .signature(number_signature)
                .unwrap()
                .resolved_return_type();
            let string_signature = scalars[1].projection().instantiation.signature;
            let string_mapper = scalars[1].projection().instantiation.mapper;
            let string_return = store
                .signature(string_signature)
                .unwrap()
                .resolved_return_type();
            // The shell is internally valid for string, but remains cached under number.
            assert!(store.set_signature_target_and_mapper(
                number_signature,
                Some(original),
                Some(string_mapper)
            ));
            assert!(store.set_signature_resolved_return_type(number_signature, string_return));
            let before = cache_counts(store);
            let count = session.total_count();
            assert!(
                preflight_generic_call_signature_return_target(
                    store,
                    Some(arrays),
                    number_signature
                )
                .is_err()
            );
            assert!(
                demand_generic_call_signature_return_with_session(
                    store,
                    Some(arrays),
                    number_signature,
                    &mut session
                )
                .is_err()
            );
            assert!(
                preflight_generic_class_constructor_signature(
                    store,
                    callee,
                    number_signature,
                    Some(arrays)
                )
                .is_err()
            );
            assert_eq!(cache_counts(store), before);
            assert_eq!(session.total_count(), count);
            assert!(store.set_signature_target_and_mapper(
                number_signature,
                Some(original),
                Some(number_mapper)
            ));
            assert!(store.set_signature_resolved_return_type(number_signature, number_return));
            assert_eq!(
                preflight_generic_call_signature_return_target(
                    store,
                    Some(arrays),
                    number_signature
                ),
                Ok(original)
            );

            assert!(store.set_signature_resolved_return_type(number_signature, None));
            let mut recovering = InstantiationSession::new_recovering(
                store,
                InstantiationLimits {
                    max_count: 0,
                    ..InstantiationLimits::default()
                },
                error_type,
            )
            .unwrap();
            let before = cache_counts(store);
            assert_eq!(
                demand_generic_call_signature_return_with_session(
                    store,
                    Some(arrays),
                    number_signature,
                    &mut recovering,
                ),
                Ok(error_type)
            );
            assert_eq!(
                (recovering.total_count(), recovering.limit_event_count()),
                (0, 1)
            );
            assert_eq!(
                store
                    .signature(number_signature)
                    .unwrap()
                    .resolved_return_type(),
                None
            );
            assert_eq!(cache_counts(store), before);
            assert_eq!(
                demand_generic_call_signature_return_with_session(
                    store,
                    Some(arrays),
                    number_signature,
                    &mut session,
                ),
                Ok(number_return.unwrap())
            );
        }

        #[test]
        #[allow(clippy::too_many_lines)] // A real constructor parameter spends and then reuses the same caller budget.
        fn class_constructor_mapping_keeps_the_callers_spent_budget() {
            let library = parse_source_file(ARRAY_LIBRARY);
            let source = parse_source_file(concat!(
                "class Box<T> { constructor(value: T) {} } ",
                "class Defaults<T = string, U = T[]> {}",
            ));
            let mut context = relation_context(&library, &source);
            context.check_source_file(SOURCE).unwrap();
            assert!(context.diagnostics().is_empty());
            let defaults = constructors(&context, "Defaults");
            let constructors = constructors(&context, "Box");
            let original = constructors.signatures()[0].signature;
            let formal = constructors.type_parameters()[0].type_parameter();
            let globals = context.global_types().clone();
            let arrays = CanonicalArrayTargets::from_global_types(&globals);
            let store = context.store_mut_for_test();
            let number = store.intrinsic_bootstrap().unwrap().number_type;
            let error_type = store.intrinsic_bootstrap().unwrap().error_type;
            let arguments = [number];
            let mapper = store.new_type_mapper(vec![formal], vec![number]).unwrap();
            let mut limited = InstantiationSession::new(InstantiationLimits {
                max_count: 1,
                ..InstantiationLimits::default()
            });
            assert_eq!(
                instantiate_type_with_session(store, formal, mapper, Some(arrays), &mut limited),
                Ok(number)
            );
            assert_eq!(
                (
                    limited.query_count(),
                    limited.total_count(),
                    limited.limit_event_count()
                ),
                (1, 1, 0)
            );
            let caller = std::ptr::from_ref(&limited);
            let request = GenericCallVectorRequest {
                form: DirectCallForm::New,
                optional_chain: false,
                explicit_type_arguments: Some(&arguments),
                has_spread_argument: false,
                callee: constructors.members().shells().value_type(),
                arguments: &arguments,
            };
            let before = cache_counts(store);
            let mut failed_counts = None;
            for events in 1..=2 {
                assert_eq!(
                    resolve_generic_class_constructor(
                        store,
                        &globals,
                        false,
                        request,
                        None,
                        &mut limited,
                    ),
                    Err(GenericMethodCallError::Generic(
                        GenericCallVectorError::Instantiation(InstantiationError::CountLimit {
                            count: 1,
                            limit: 1
                        },)
                    ))
                );
                assert_eq!(std::ptr::from_ref(&limited), caller);
                assert_eq!(
                    (
                        limited.query_count(),
                        limited.total_count(),
                        limited.limit_event_count()
                    ),
                    (1, 1, events)
                );
                if let Some(counts) = failed_counts {
                    assert_eq!(cache_counts(store), counts);
                } else {
                    failed_counts = Some(cache_counts(store));
                }
            }
            let CachedSignatureLookup::Hit(signature) =
                store.cached_signature(original, type_list_key(&arguments), &arguments)
            else {
                panic!("the failed demand must retain its checked constructor shell")
            };
            let parameter = store.signature(signature).unwrap().parameters()[0];
            assert_eq!(
                store.value_symbol_links(parameter).unwrap().resolved_type,
                None
            );
            assert_eq!(
                store.signature(signature).unwrap().resolved_return_type(),
                None
            );
            assert_eq!(cache_counts(store).3, before.3 + 1);
            assert_eq!(cache_counts(store).4, before.4 + 1);
            let mut recovering = InstantiationSession::new_recovering(
                store,
                InstantiationLimits {
                    max_count: 0,
                    ..InstantiationLimits::default()
                },
                error_type,
            )
            .unwrap();
            let before_recovery = cache_counts(store);
            assert_eq!(
                resolve_generic_class_constructor(
                    store,
                    &globals,
                    false,
                    request,
                    None,
                    &mut recovering,
                ),
                Err(GenericMethodCallError::Generic(
                    GenericCallVectorError::Unsupported(
                        GenericCallVectorUnsupported::InstantiationLimitRecovery(original),
                    )
                ))
            );
            assert_eq!(
                (recovering.total_count(), recovering.limit_event_count()),
                (0, 1)
            );
            assert_eq!(
                store.value_symbol_links(parameter).unwrap().resolved_type,
                None
            );
            assert_eq!(
                store.signature(signature).unwrap().resolved_return_type(),
                None
            );
            assert_eq!(cache_counts(store), before_recovery);

            // A dependent default must stop before either checked or arity-recovery allocation.
            for values in [&[][..], arguments.as_slice()] {
                let mut recovering = InstantiationSession::new_recovering(
                    store,
                    InstantiationLimits {
                        max_count: 0,
                        ..InstantiationLimits::default()
                    },
                    error_type,
                )
                .unwrap();
                let before_recovery = cache_counts(store);
                assert_eq!(
                    resolve_generic_class_constructor(
                        store,
                        &globals,
                        false,
                        GenericCallVectorRequest {
                            callee: defaults.members().shells().value_type(),
                            explicit_type_arguments: None,
                            arguments: values,
                            ..request
                        },
                        None,
                        &mut recovering,
                    ),
                    Err(GenericMethodCallError::Generic(
                        GenericCallVectorError::Unsupported(
                            GenericCallVectorUnsupported::InstantiationLimitRecovery(
                                defaults.signatures()[0].signature
                            ),
                        )
                    ))
                );
                assert_eq!(
                    (recovering.total_count(), recovering.limit_event_count()),
                    (0, 1)
                );
                assert_eq!(cache_counts(store), before_recovery);
            }
            let mut adequate = InstantiationSession::new(InstantiationLimits::default());
            let selected = resolve_generic_class_constructor(
                store,
                &globals,
                false,
                request,
                None,
                &mut adequate,
            )
            .unwrap()
            .unwrap();
            let generic = applicable_generic(selected.clone());
            assert_eq!(generic.projection().instantiation.signature, signature);
            assert_eq!(
                store.value_symbol_links(parameter).unwrap().resolved_type,
                Some(number)
            );
            assert_class_return(
                store,
                &generic,
                constructors.members().shells().instance_type(),
                &mut adequate,
            );
            assert_eq!(adequate.limit_event_count(), 0);
            let warm = cache_counts(store);
            let count = adequate.total_count();
            assert_eq!(
                resolve_generic_class_constructor(
                    store,
                    &globals,
                    false,
                    request,
                    Some(signature),
                    &mut adequate,
                ),
                Ok(Some(selected))
            );
            assert_eq!(adequate.total_count(), count);
            assert_eq!(cache_counts(store), warm);
        }

        #[test]
        #[allow(clippy::too_many_lines)] // Wrong arity must use the same unsupported-pair check as ordinary inference.
        fn class_constructor_unproved_inference_pairs_stop_before_fallback() {
            let library = parse_source_file(concat!(
                "interface Array<T> {} interface ReadonlyArray<T> {} ",
                "interface Holder<T> { value: T; } interface Other<T> { value: T; }",
            ));
            let source = parse_source_file(concat!(
                "class FromHolder<T> { constructor(value: Holder<T>) {} } ",
                "class FromArray<T> { constructor(value: T[]) {} } ",
                "function inputs(value: Holder<number>, other: Other<number>, ",
                "numbers: number[], strings: string[]): void {} ",
                "const fresh = { value: 1 };",
            ));
            let mut context = relation_context(&library, &source);
            context.check_source_file(SOURCE).unwrap();
            assert!(context.diagnostics().is_empty());
            let holder = constructors(&context, "FromHolder");
            let array = constructors(&context, "FromArray");
            let inputs = source_function(&mut context, &source, "inputs");
            let fresh = source_value(context.store(), "fresh");
            let globals = context.global_types().clone();
            let store = context.store_mut_for_test();
            let number = store.intrinsic_bootstrap().unwrap().number_type;
            let mut session = InstantiationSession::new(InstantiationLimits::default());
            let union = store
                .expression_union_type_with_global_types_and_session(
                    &globals,
                    &inputs.parameters[2..],
                    UnionReduction::Literal,
                    &mut session,
                )
                .unwrap();
            for (constructors, argument) in [
                (&holder, inputs.parameters[0]),
                (&array, inputs.parameters[2]),
            ] {
                let arguments = [argument];
                let generic = applicable_generic(
                    resolve_generic_class_constructor(
                        store,
                        &globals,
                        false,
                        GenericCallVectorRequest {
                            form: DirectCallForm::New,
                            optional_chain: false,
                            explicit_type_arguments: None,
                            has_spread_argument: false,
                            callee: constructors.members().shells().value_type(),
                            arguments: &arguments,
                        },
                        None,
                        &mut session,
                    )
                    .unwrap()
                    .unwrap(),
                );
                assert_eq!(generic.projection().instantiation.type_arguments, [number]);
            }
            for (constructors, argument) in [
                (&holder, fresh),
                (&holder, inputs.parameters[1]),
                (&array, union),
            ] {
                let arguments = [argument, number];
                for arguments in [&arguments[..1], arguments.as_slice()] {
                    let before = cache_counts(store);
                    assert_eq!(
                        resolve_generic_class_constructor(
                            store,
                            &globals,
                            false,
                            GenericCallVectorRequest {
                                form: DirectCallForm::New,
                                optional_chain: false,
                                explicit_type_arguments: None,
                                has_spread_argument: false,
                                callee: constructors.members().shells().value_type(),
                                arguments,
                            },
                            None,
                            &mut session,
                        ),
                        Err(GenericMethodCallError::Generic(
                            GenericCallVectorError::Unsupported(
                                GenericCallVectorUnsupported::InferencePair {
                                    signature: constructors.signatures()[0].signature,
                                    source: argument,
                                    target: constructors.signatures()[0].parameters[0],
                                },
                            )
                        ))
                    );
                    assert_eq!(cache_counts(store), before);
                }
            }
        }
    }

    fn relation_context<'arena>(
        library: &'arena ParseResult,
        source: &'arena ParseResult,
    ) -> CanonicalCheckerContext<'arena> {
        let mut binder = CanonicalBinder::new();
        for (file, parsed, declaration, path) in [
            (LIBRARY, library, true, "\"/method-relation-library.d.ts\""),
            (SOURCE, source, false, "\"/method-relation.ts\""),
        ] {
            assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
            binder
                .bind_source_file_with_facts(
                    &parsed.arena,
                    parsed.source_file,
                    file,
                    CanonicalSourceFileFacts::new(
                        EscapedName::source(path),
                        CanonicalSourceLanguage::TypeScript,
                        declaration,
                        CanonicalModuleState::Script,
                    ),
                )
                .unwrap();
            binder
                .bind_typescript_declaration_slice(&parsed.arena, file)
                .unwrap();
        }
        CanonicalCheckerContext::new(
            binder.finish(),
            [(LIBRARY, &library.arena), (SOURCE, &source.arena)]
                .into_iter()
                .collect(),
            CanonicalCheckerOptions::default(),
        )
        .unwrap()
    }

    fn global_interface(store: &CanonicalTypeMapperStore, name: &str) -> TypeId {
        let owner = store
            .symbol_table(store.intrinsic_bootstrap().unwrap().globals)
            .and_then(|globals| globals.get_source(name))
            .and_then(|owner| store.get_merged_symbol(owner))
            .unwrap();
        store
            .declared_type_links(owner)
            .unwrap()
            .declared_type
            .unwrap()
    }

    fn inherited_value(store: &CanonicalTypeMapperStore) -> SemanticSymbolId {
        let derived = global_interface(store, "Derived");
        let TypeData::Interface(data) = store.type_payload(derived).unwrap().data() else {
            panic!("Derived must retain its interface identity")
        };
        store
            .symbol_table(data.reference.object.structured.members.unwrap())
            .and_then(|members| members.get_source("value"))
            .unwrap()
    }

    fn source_function(
        context: &mut CanonicalCheckerContext<'_>,
        parsed: &ParseResult,
        name: &str,
    ) -> ValidatedSingleCallable {
        let name = parsed
            .arena
            .iter()
            .find_map(|(_, record)| {
                let NodeData::FunctionDeclaration(function) = &record.data else {
                    return None;
                };
                let node = function.name?;
                let NodeData::Identifier(identifier) = &parsed.arena.get(node)?.data else {
                    return None;
                };
                (identifier.text == name).then_some(NodeRef::new(parsed.arena.id(), SOURCE, node))
            })
            .unwrap();
        let type_ = context.get_type_at_location(name).unwrap();
        match validate_stored_single_callable(context.store(), type_) {
            StoredSingleCallableValidation::Valid { callable, .. } => callable,
            other => panic!("expected the real source function: {other:?}"),
        }
    }

    fn source_method(
        context: &mut CanonicalCheckerContext<'_>,
        parsed: &ParseResult,
    ) -> (TypeId, SignatureId) {
        let (declaration, name) = parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                let NodeData::MethodSignatureDeclaration(method) = &record.data else {
                    return None;
                };
                Some((
                    NodeRef::new(parsed.arena.id(), SOURCE, node),
                    NodeRef::new(parsed.arena.id(), SOURCE, method.name),
                ))
            })
            .unwrap();
        let callee = context.get_type_at_location(name).unwrap();
        let targets = CanonicalArrayTargets::from_global_types(context.global_types());
        let StoredCallableSetValidation::Valid { projection, .. } =
            validate_stored_callable_set_with_array_targets(context.store(), callee, Some(targets))
        else {
            panic!("the source method overload group must be published")
        };
        assert_eq!(projection.call_signatures.len(), 2);
        let original = projection.call_signatures[0].signature;
        assert_eq!(
            context.store().signature(original).unwrap().declaration(),
            Some(declaration)
        );
        (callee, original)
    }

    fn spent_inherited_budget(
        store: &mut CanonicalTypeMapperStore,
        targets: CanonicalArrayTargets,
        proxy: SemanticSymbolId,
    ) -> InstantiationSession {
        let links = store.value_symbol_links(proxy).unwrap();
        assert_eq!(links.resolved_type, None);
        let mapper = links.mapper.unwrap();
        let template = store
            .value_symbol_links(links.target.unwrap())
            .unwrap()
            .resolved_type
            .unwrap();
        assert!(matches!(
            store.type_payload(template).unwrap().data(),
            TypeData::TypeParameter(_)
        ));
        let number = store.intrinsic_bootstrap().unwrap().number_type;
        let mut limited = InstantiationSession::new(InstantiationLimits {
            max_count: 1,
            ..InstantiationLimits::default()
        });
        // Spend the caller's budget on the real inherited mapper, without publishing its value.
        assert_eq!(
            instantiate_type_with_session(store, template, mapper, Some(targets), &mut limited),
            Ok(number)
        );
        assert_eq!((limited.query_count(), limited.total_count()), (1, 1));
        assert_eq!(limited.limit_event_count(), 0);
        assert_eq!(store.value_symbol_links(proxy).unwrap().resolved_type, None);
        limited
    }

    fn cache_counts(store: &CanonicalTypeMapperStore) -> (usize, usize, usize, usize, usize) {
        (
            store.type_len(),
            store.symbol_len(),
            store.mapper_len(),
            store.signature_len(),
            store.cached_signature_len(),
        )
    }

    #[derive(Clone, Copy)]
    enum MethodRelationInput {
        FixedProperty,
        GenericProperty,
        GenericCallback,
    }

    #[allow(clippy::too_many_lines)] // One source graph checks spent limits, retry, and warm reuse.
    fn assert_spent_method_relation_budget(input: MethodRelationInput, assignable_pass: bool) {
        let library = parse_source_file(concat!(
            "interface Array<T> {} interface ReadonlyArray<T> {} ",
            "interface Base<T> { value: T; [index: number]: Array<number>; } ",
            "interface Box<T> { value: T; }",
        ));
        let declarations = match input {
            MethodRelationInput::FixedProperty => concat!(
                "interface Methods { m(tag: string, value: Plain): number; ",
                "m<T>(a: T, b: T, c: T): T; }",
            ),
            MethodRelationInput::GenericProperty => concat!(
                "interface Methods { m<U>(tag: string, value: Box<U>): number; ",
                "m(tag: string, value: number, extra: number): number; } ",
                "function warm(value: Box<number>): number { return value.value; }",
            ),
            MethodRelationInput::GenericCallback => concat!(
                "interface Callback { (...values: string[]): string; } ",
                "declare function choose<First, Second>(first?: First, second?: Second): Second; ",
                "interface Methods { m(tag: string, callback: Callback): number; ",
                "m<T>(a: T, b: T, c: T): T; }",
            ),
        };
        let parsed = parse_source_file(&format!(
            "interface Derived extends Base<number> {{}} \
             interface Plain {{ value: number; }} {declarations} \
             function keep(methods: Methods, derived: Derived): number {{ return 1; }}",
        ));
        let mut context = relation_context(&library, &parsed);
        context.check_source_file(SOURCE).unwrap();
        assert!(context.diagnostics().is_empty());
        let (callee, original) = source_method(&mut context, &parsed);
        let globals = context.global_types().clone();
        let targets = CanonicalArrayTargets::from_global_types(&globals);
        let derived = global_interface(context.store(), "Derived");
        let proxy = inherited_value(context.store());
        let (argument, parameter) = match input {
            MethodRelationInput::FixedProperty => {
                (derived, global_interface(context.store(), "Plain"))
            }
            MethodRelationInput::GenericProperty => (
                derived,
                source_function(&mut context, &parsed, "warm").parameters[0],
            ),
            MethodRelationInput::GenericCallback => (
                source_function(&mut context, &parsed, "choose").owner,
                global_interface(context.store(), "Callback"),
            ),
        };
        let store = context.store_mut_for_test();
        let bootstrap = store.intrinsic_bootstrap().unwrap();
        let (string, number, any) = (
            bootstrap.string_type,
            bootstrap.number_type,
            bootstrap.any_type,
        );
        let explicit = [number];
        let arguments = [if assignable_pass { any } else { string }, argument];
        let request = GenericCallVectorRequest {
            form: DirectCallForm::Call,
            optional_chain: false,
            explicit_type_arguments: matches!(input, MethodRelationInput::GenericProperty)
                .then_some(explicit.as_slice()),
            has_spread_argument: false,
            callee,
            arguments: &arguments,
        };
        let prewarmed = if matches!(input, MethodRelationInput::GenericProperty) {
            // This resolves the checked parameter mapper without reading Derived.value.
            let warm_arguments = [string, parameter];
            let mut setup = InstantiationSession::new(InstantiationLimits::default());
            let selected = resolve_generic_method_call(
                store,
                &globals,
                false,
                GenericCallVectorRequest {
                    arguments: &warm_arguments,
                    ..request
                },
                None,
                &mut setup,
            )
            .unwrap()
            .unwrap();
            let GenericMethodCallSelection::Generic(generic) = &selected.selected else {
                panic!("the explicit call must select its generic method")
            };
            assert_eq!(generic.projection().generic_signature, original);
            assert_eq!(generic.projection().instantiation.type_arguments, [number]);
            assert_eq!(
                store
                    .signature(generic.projection().instantiation.signature)
                    .unwrap()
                    .parameters()
                    .iter()
                    .map(|parameter| store.value_symbol_links(*parameter).unwrap().resolved_type)
                    .collect::<Vec<_>>(),
                [Some(string), Some(parameter)]
            );
            Some(selected)
        } else {
            None
        };
        let mut limited = spent_inherited_budget(store, targets, proxy);
        let expected = match input {
            MethodRelationInput::FixedProperty => {
                GenericMethodCallError::Relation(RelationUnavailable::UnsupportedProperty(proxy))
            }
            MethodRelationInput::GenericProperty => GenericMethodCallError::Generic(
                GenericCallVectorError::Relation(RelationUnavailable::UnsupportedProperty(proxy)),
            ),
            MethodRelationInput::GenericCallback => {
                GenericMethodCallError::Relation(RelationUnavailable::StructuralRelation {
                    source: argument,
                    target: parameter,
                    relation: if assignable_pass {
                        RelationKind::Assignable
                    } else {
                        RelationKind::Subtype
                    },
                })
            }
        };
        let mut failed_counts = None;
        for events in 1..=2 {
            let mark = limited.limit_event_mark();
            assert_eq!(
                resolve_generic_method_call(store, &globals, false, request, None, &mut limited)
                    .unwrap_err(),
                expected
            );
            assert_eq!((limited.query_count(), limited.total_count()), (1, 1));
            assert!(limited.limit_event_occurred_since(mark));
            assert_eq!(limited.limit_event_count(), events);
            assert_eq!(store.value_symbol_links(proxy).unwrap().resolved_type, None);
            if let Some(failed_counts) = failed_counts {
                assert_eq!(cache_counts(store), failed_counts);
            } else {
                failed_counts = Some(cache_counts(store));
            }
        }

        let mut adequate = InstantiationSession::new(InstantiationLimits::default());
        let selected =
            resolve_generic_method_call(store, &globals, false, request, None, &mut adequate)
                .unwrap()
                .unwrap();
        assert_eq!(selected.diagnostic, None);
        assert!(prewarmed.as_ref().is_none_or(|warm| *warm == selected));
        let signature = match &selected.selected {
            GenericMethodCallSelection::Fixed {
                signature,
                return_type,
            } => {
                assert_eq!(*signature, original);
                assert_eq!(*return_type, number);
                *signature
            }
            GenericMethodCallSelection::Generic(generic) => {
                assert_eq!(generic.projection().generic_signature, original);
                assert_eq!(
                    demand_generic_call_vector_selected_return(store, generic, &mut adequate)
                        .unwrap()
                        .0,
                    number
                );
                generic.projection().instantiation.signature
            }
        };
        assert!(adequate.total_count() > 0);
        assert_eq!(adequate.limit_event_count(), 0);
        assert_eq!(
            store.value_symbol_links(proxy).unwrap().resolved_type,
            (!matches!(input, MethodRelationInput::GenericCallback)).then_some(number)
        );
        let warm = cache_counts(store);
        let count = adequate.total_count();
        for _ in 0..2 {
            assert_eq!(
                resolve_generic_method_call(
                    store,
                    &globals,
                    false,
                    request,
                    Some(signature),
                    &mut adequate
                ),
                Ok(Some(selected.clone()))
            );
            assert_eq!(adequate.total_count(), count);
            assert_eq!(adequate.limit_event_count(), 0);
            assert_eq!(cache_counts(store), warm);
        }
        assert!(context.diagnostics().is_empty());
    }

    #[test]
    fn fixed_method_candidates_preserve_the_callers_spent_relation_budget() {
        for assignable_pass in [false, true] {
            assert_spent_method_relation_budget(
                MethodRelationInput::FixedProperty,
                assignable_pass,
            );
        }
    }

    #[test]
    fn generic_method_candidates_preserve_the_callers_spent_relation_budget() {
        for assignable_pass in [false, true] {
            assert_spent_method_relation_budget(
                MethodRelationInput::GenericProperty,
                assignable_pass,
            );
        }
    }

    #[test]
    fn method_callback_inference_preserves_the_callers_spent_relation_budget() {
        for assignable_pass in [false, true] {
            assert_spent_method_relation_budget(
                MethodRelationInput::GenericCallback,
                assignable_pass,
            );
        }
    }

    #[test]
    #[allow(clippy::too_many_lines)] // The cold literal union must fail before parameter mapping.
    fn method_literal_candidate_unions_preserve_the_callers_spent_relation_budget() {
        let library = parse_source_file(concat!(
            "interface Array<T> {} interface ReadonlyArray<T> {} ",
            "interface Base<T> { value: T; [index: number]: Array<number>; }",
        ));
        let parsed = parse_source_file(concat!(
            "interface Derived extends Base<number> {} ",
            "interface Plain { value: number; } ",
            "interface Methods { m<T>(first: T, second: T): T; ",
            "m(first: number, second: number, third: number): number; } ",
            "declare const derived: Derived; declare const plain: Plain; ",
            "const left = { child: derived }; const right = { child: plain };",
        ));
        let mut context = relation_context(&library, &parsed);
        context.check_source_file(SOURCE).unwrap();
        assert!(context.diagnostics().is_empty());
        let (callee, original) = source_method(&mut context, &parsed);
        let literals = ["left", "right"].map(|name| {
            let node = parsed
                .arena
                .iter()
                .find_map(|(_, record)| {
                    let NodeData::VariableDeclaration(variable) = &record.data else {
                        return None;
                    };
                    let NodeData::Identifier(identifier) = &parsed.arena.get(variable.name)?.data
                    else {
                        return None;
                    };
                    (identifier.text == name).then(|| {
                        NodeRef::new(parsed.arena.id(), SOURCE, variable.initializer.unwrap())
                    })
                })
                .unwrap();
            let type_ = context.get_type_at_location(node).unwrap();
            assert!(
                context
                    .store()
                    .type_payload(type_)
                    .unwrap()
                    .object_flags()
                    .intersects(ObjectFlags::OBJECT_LITERAL)
            );
            type_
        });
        assert_ne!(literals[0], literals[1]);
        let globals = context.global_types().clone();
        let targets = CanonicalArrayTargets::from_global_types(&globals);
        let proxy = inherited_value(context.store());
        let store = context.store_mut_for_test();
        let request = GenericCallVectorRequest {
            form: DirectCallForm::Call,
            optional_chain: false,
            explicit_type_arguments: None,
            has_spread_argument: false,
            callee,
            arguments: &literals,
        };
        let warm_arguments = [literals[1]; 2];
        let mut setup = InstantiationSession::new(InstantiationLimits::default());
        let prewarmed = resolve_generic_method_call(
            store,
            &globals,
            false,
            GenericCallVectorRequest {
                arguments: &warm_arguments,
                ..request
            },
            None,
            &mut setup,
        )
        .unwrap()
        .unwrap();
        let GenericMethodCallSelection::Generic(generic) = &prewarmed.selected else {
            panic!("the two-argument call must select its generic method")
        };
        let signature = generic.projection().instantiation.signature;
        assert_eq!(generic.projection().generic_signature, original);
        let inferred = generic.projection().instantiation.type_arguments[0];
        assert_eq!(
            store.get_widened_type_with_global_types(literals[1], &globals),
            Ok(inferred)
        );
        assert!(
            store
                .signature(signature)
                .unwrap()
                .parameters()
                .iter()
                .all(|parameter| {
                    store.value_symbol_links(*parameter).unwrap().resolved_type == Some(inferred)
                })
        );
        let mut limited = spent_inherited_budget(store, targets, proxy);
        let before = cache_counts(store);
        // Subtype reduction visits the canonical type order in reverse.
        let failed_constituent = literals[0].max(literals[1]);
        for events in 1..=2 {
            assert_eq!(
                resolve_generic_method_call(store, &globals, false, request, None, &mut limited),
                Err(GenericMethodCallError::Generic(
                    GenericCallVectorError::Inference(NakedTypeCandidateError::Union(
                        LiteralTypeCacheError::UnsupportedUnionConstituent(failed_constituent)
                    ))
                ))
            );
            assert_eq!((limited.query_count(), limited.total_count()), (1, 1));
            assert_eq!(limited.limit_event_count(), events);
            assert_eq!(store.value_symbol_links(proxy).unwrap().resolved_type, None);
            assert_eq!(cache_counts(store), before);
        }

        let mut adequate = InstantiationSession::new(InstantiationLimits::default());
        let selected =
            resolve_generic_method_call(store, &globals, false, request, None, &mut adequate)
                .unwrap()
                .unwrap();
        assert_eq!(selected, prewarmed);
        assert_eq!(selected.diagnostic, None);
        let GenericMethodCallSelection::Generic(generic) = &selected.selected else {
            panic!("literal inference must retain the selected generic signature")
        };
        assert_eq!(
            demand_generic_call_vector_selected_return(store, generic, &mut adequate)
                .unwrap()
                .0,
            inferred
        );
        assert_eq!(
            store.value_symbol_links(proxy).unwrap().resolved_type,
            Some(store.intrinsic_bootstrap().unwrap().number_type)
        );
        assert!(adequate.total_count() > 0);
        assert_eq!(adequate.limit_event_count(), 0);
        let warm = cache_counts(store);
        let count = adequate.total_count();
        for _ in 0..2 {
            assert_eq!(
                resolve_generic_method_call(
                    store,
                    &globals,
                    false,
                    request,
                    Some(signature),
                    &mut adequate
                ),
                Ok(Some(selected.clone()))
            );
            assert_eq!(adequate.total_count(), count);
            assert_eq!(adequate.limit_event_count(), 0);
            assert_eq!(cache_counts(store), warm);
        }
    }

    #[allow(clippy::too_many_lines)] // Restoring one lazy link forces the real cached union scan.
    fn assert_dirty_method_inference_budget(widening: bool) {
        let library = parse_source_file(concat!(
            "interface Array<T> {} interface ReadonlyArray<T> {} ",
            "interface Base<T> { value: T; [index: number]: Array<number>; }",
        ));
        let parsed = parse_source_file(concat!(
            "interface Derived extends Base<number> {} ",
            "interface Plain { value: number; } ",
            "interface Methods { m<T>(first: T, second: T): T; m(value: number): number; } ",
            "declare const first: 'one'; declare const second: 'two'; ",
            "const left = { one: 1 }; const right = { two: 'two' };",
        ));
        let mut context = relation_context(&library, &parsed);
        context.check_source_file(SOURCE).unwrap();
        assert!(context.diagnostics().is_empty());
        let (callee, original) = source_method(&mut context, &parsed);
        let arguments = ["first", "second"].map(|name| {
            let node = parsed
                .arena
                .iter()
                .find_map(|(_, record)| {
                    let NodeData::VariableDeclaration(variable) = &record.data else {
                        return None;
                    };
                    let NodeData::Identifier(identifier) = &parsed.arena.get(variable.name)?.data
                    else {
                        return None;
                    };
                    (identifier.text == name)
                        .then(|| NodeRef::new(parsed.arena.id(), SOURCE, variable.type_.unwrap()))
                })
                .unwrap();
            context.get_type_at_location(node).unwrap()
        });
        let object_literals = widening.then(|| {
            ["left", "right"].map(|name| {
                let node = parsed
                    .arena
                    .iter()
                    .find_map(|(_, record)| {
                        let NodeData::VariableDeclaration(variable) = &record.data else {
                            return None;
                        };
                        let NodeData::Identifier(identifier) =
                            &parsed.arena.get(variable.name)?.data
                        else {
                            return None;
                        };
                        (identifier.text == name).then(|| {
                            NodeRef::new(parsed.arena.id(), SOURCE, variable.initializer.unwrap())
                        })
                    })
                    .unwrap();
                context.get_type_at_location(node).unwrap()
            })
        });
        let globals = context.global_types().clone();
        let targets = CanonicalArrayTargets::from_global_types(&globals);
        let derived = global_interface(context.store(), "Derived");
        let plain = global_interface(context.store(), "Plain");
        let proxy = inherited_value(context.store());
        let store = context.store_mut_for_test();
        let number = store.intrinsic_bootstrap().unwrap().number_type;
        let mut setup = InstantiationSession::new(InstantiationLimits::default());
        let arguments = if let Some(object_literals) = object_literals {
            let union = store
                .expression_union_type_with_global_types_and_session(
                    &globals,
                    &object_literals,
                    UnionReduction::Literal,
                    &mut setup,
                )
                .unwrap();
            assert!(
                store
                    .type_payload(union)
                    .unwrap()
                    .object_flags()
                    .intersects(ObjectFlags::REQUIRES_WIDENING)
            );
            [union; 2]
        } else {
            arguments
        };
        let source_union = store
            .expression_union_type_with_global_types_and_session(
                &globals,
                &[number, derived],
                UnionReduction::Literal,
                &mut setup,
            )
            .unwrap();
        let rows = store
            .intrinsic_bootstrap()
            .unwrap()
            .union_of_union_cache_len();
        store
            .expression_union_type_with_global_types_and_session(
                &globals,
                &[source_union, plain],
                UnionReduction::Subtype,
                &mut setup,
            )
            .unwrap();
        assert_eq!(
            store
                .intrinsic_bootstrap()
                .unwrap()
                .union_of_union_cache_len(),
            rows + 1
        );
        let original_links = store.value_symbol_links(proxy).unwrap().clone();
        assert_eq!(original_links.resolved_type, Some(number));
        // Keep the source target and mapper. Only restore their supported lazy value state.
        assert!(store.set_value_symbol_links(
            proxy,
            ValueSymbolLinks {
                resolved_type: None,
                ..original_links
            }
        ));
        store.mark_union_cache_validation_dirty();
        let mut limited = spent_inherited_budget(store, targets, proxy);
        let request = GenericCallVectorRequest {
            form: DirectCallForm::Call,
            optional_chain: false,
            explicit_type_arguments: None,
            has_spread_argument: false,
            callee,
            arguments: &arguments,
        };
        let before = cache_counts(store);
        let scans = store.union_cache_validation_scan_count();
        let expected_error =
            GenericMethodCallError::Generic(GenericCallVectorError::Inference(if widening {
                NakedTypeCandidateError::Widening(DerivedTypeError::UnsupportedWideningType(
                    derived.max(plain),
                ))
            } else {
                NakedTypeCandidateError::Union(LiteralTypeCacheError::UnsupportedUnionConstituent(
                    derived.max(plain),
                ))
            }));
        for events in 1..=2 {
            assert_eq!(
                resolve_generic_method_call(store, &globals, false, request, None, &mut limited)
                    .unwrap_err(),
                expected_error
            );
            assert_eq!((limited.query_count(), limited.total_count()), (1, 1));
            assert_eq!(limited.limit_event_count(), events);
            assert_eq!(store.value_symbol_links(proxy).unwrap().resolved_type, None);
            assert_eq!(cache_counts(store), before);
            assert_eq!(
                store.union_cache_validation_scan_count(),
                scans + usize::try_from(events).unwrap()
            );
        }

        let mut adequate = InstantiationSession::new(InstantiationLimits::default());
        let selected =
            resolve_generic_method_call(store, &globals, false, request, None, &mut adequate)
                .unwrap()
                .unwrap();
        assert_eq!(selected.diagnostic, None);
        let GenericMethodCallSelection::Generic(generic) = &selected.selected else {
            panic!("the two literal arguments must select their generic method")
        };
        assert_eq!(generic.projection().generic_signature, original);
        let expected = if widening {
            store
                .get_widened_type_with_global_types_and_session(
                    arguments[0],
                    &globals,
                    &mut adequate,
                )
                .unwrap()
        } else {
            store
                .expression_union_type_with_global_types_and_session(
                    &globals,
                    &arguments,
                    UnionReduction::Literal,
                    &mut adequate,
                )
                .unwrap()
        };
        assert_eq!(
            generic.projection().instantiation.type_arguments,
            [expected]
        );
        assert_eq!(
            demand_generic_call_vector_selected_return(store, generic, &mut adequate)
                .unwrap()
                .0,
            expected
        );
        assert_eq!(
            store.value_symbol_links(proxy).unwrap().resolved_type,
            Some(number)
        );
        assert!(adequate.total_count() > 0);
        assert_eq!(adequate.limit_event_count(), 0);
        let signature = generic.projection().instantiation.signature;
        let warm = cache_counts(store);
        let count = adequate.total_count();
        for _ in 0..2 {
            assert_eq!(
                resolve_generic_method_call(
                    store,
                    &globals,
                    false,
                    request,
                    Some(signature),
                    &mut adequate
                ),
                Ok(Some(selected.clone()))
            );
            assert_eq!(adequate.total_count(), count);
            assert_eq!(adequate.limit_event_count(), 0);
            assert_eq!(cache_counts(store), warm);
        }
    }

    #[test]
    fn method_literal_inference_revalidates_dirty_unions_with_the_callers_spent_budget() {
        assert_dirty_method_inference_budget(false);
    }

    #[test]
    fn method_inference_widening_revalidates_dirty_unions_with_the_callers_spent_budget() {
        assert_dirty_method_inference_budget(true);
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Mapping and cache validation must share one count limit.
    fn method_union_parameter_mapping_revalidates_dirty_unions_with_the_caller() {
        let library = parse_source_file(concat!(
            "interface Array<T> {} interface ReadonlyArray<T> {} ",
            "interface Base<T> { value: T; [index: number]: number; }",
        ));
        let parsed = parse_source_file(concat!(
            "interface Derived extends Base<number> {} ",
            "interface Plain { value: number; } ",
            "interface Methods { m<T>(value: T | string): T; m(a: number, b: number): number; }",
        ));
        let mut context = relation_context(&library, &parsed);
        context.check_source_file(SOURCE).unwrap();
        assert!(context.diagnostics().is_empty());
        let (callee, original) = source_method(&mut context, &parsed);
        let globals = context.global_types().clone();
        let derived = global_interface(context.store(), "Derived");
        let plain = global_interface(context.store(), "Plain");
        let proxy = inherited_value(context.store());
        let TypeData::Interface(data) = context.store().type_payload(derived).unwrap().data()
        else {
            panic!("Derived must retain its source interface")
        };
        let base = data.resolved_base_types.as_ref().unwrap()[0];
        let store = context.store_mut_for_test();
        let number = store.intrinsic_bootstrap().unwrap().number_type;
        let mut setup = InstantiationSession::new(InstantiationLimits::default());
        let source_union = store
            .expression_union_type_with_global_types_and_session(
                &globals,
                &[number, derived],
                UnionReduction::Literal,
                &mut setup,
            )
            .unwrap();
        store
            .expression_union_type_with_global_types_and_session(
                &globals,
                &[source_union, plain],
                UnionReduction::Subtype,
                &mut setup,
            )
            .unwrap();
        let original_links = store.value_symbol_links(proxy).unwrap().clone();
        assert_eq!(original_links.resolved_type, Some(number));
        assert!(store.set_value_symbol_links(
            proxy,
            ValueSymbolLinks {
                resolved_type: None,
                ..original_links
            }
        ));
        store.mark_union_cache_validation_dirty();
        assert_eq!(
            validate_interface_heritage_members(store, derived),
            InterfaceHeritageMembersValidation::Valid
        );
        assert!(
            validate_generic_interface_members(store, base, None)
                .unwrap()
                .is_some()
        );
        let arguments = [number];
        let request = GenericCallVectorRequest {
            form: DirectCallForm::Call,
            optional_chain: false,
            explicit_type_arguments: Some(&arguments),
            has_spread_argument: false,
            callee,
            arguments: &arguments,
        };
        let mut limited = InstantiationSession::new(InstantiationLimits {
            max_count: 2,
            ..InstantiationLimits::default()
        });
        let before = cache_counts(store);
        // The real union frame and T substitution spend both available instantiations.
        assert_eq!(
            resolve_generic_method_call(store, &globals, false, request, None, &mut limited),
            Err(GenericMethodCallError::Generic(
                GenericCallVectorError::Instantiation(InstantiationError::Union(
                    LiteralTypeCacheError::UnsupportedUnionConstituent(derived.max(plain))
                ))
            ))
        );
        assert_eq!((limited.query_count(), limited.total_count()), (2, 2));
        assert_eq!(limited.limit_event_count(), 1);
        assert_eq!(store.value_symbol_links(proxy).unwrap().resolved_type, None);
        let CachedSignatureLookup::Hit(signature) =
            store.cached_signature(original, type_list_key(&arguments), &arguments)
        else {
            panic!("the failed parameter demand must retain its checked shell")
        };
        assert_eq!(store.signature(signature).unwrap().target(), Some(original));
        let parameter = store.signature(signature).unwrap().parameters()[0];
        assert_eq!(
            store.value_symbol_links(parameter).unwrap().resolved_type,
            None
        );
        assert_eq!(
            store.value_symbol_links(parameter).unwrap().target,
            Some(store.signature(original).unwrap().parameters()[0])
        );
        let failed = cache_counts(store);
        assert_eq!(failed.3, before.3 + 1);
        assert_eq!(failed.4, before.4 + 1);
        let scans = store.union_cache_validation_scan_count();
        // A second request in the same query stops before mapping. The resolver cannot reset it.
        assert_eq!(
            resolve_generic_method_call(store, &globals, false, request, None, &mut limited),
            Err(GenericMethodCallError::Generic(
                GenericCallVectorError::Instantiation(InstantiationError::CountLimit {
                    count: 2,
                    limit: 2
                })
            ))
        );
        assert_eq!((limited.query_count(), limited.total_count()), (2, 2));
        assert_eq!(limited.limit_event_count(), 2);
        assert_eq!(store.value_symbol_links(proxy).unwrap().resolved_type, None);
        assert_eq!(
            store.value_symbol_links(parameter).unwrap().resolved_type,
            None
        );
        assert_eq!(store.union_cache_validation_scan_count(), scans);
        assert_eq!(cache_counts(store), failed);

        let mut adequate = InstantiationSession::new(InstantiationLimits::default());
        let selected =
            resolve_generic_method_call(store, &globals, false, request, None, &mut adequate)
                .unwrap()
                .unwrap();
        assert_eq!(selected.diagnostic, None);
        let GenericMethodCallSelection::Generic(generic) = &selected.selected else {
            panic!("the explicit call must select its generic method")
        };
        assert_eq!(generic.projection().generic_signature, original);
        assert_eq!(generic.projection().instantiation.signature, signature);
        assert_eq!(generic.projection().instantiation.type_arguments, arguments);
        assert_eq!(
            store.value_symbol_links(parameter).unwrap().resolved_type,
            Some(store.intrinsic_bootstrap().unwrap().string_or_number_type)
        );
        assert_eq!(
            demand_generic_call_vector_selected_return(store, generic, &mut adequate)
                .unwrap()
                .0,
            number
        );
        assert_eq!(
            store.value_symbol_links(proxy).unwrap().resolved_type,
            Some(number)
        );
        assert!(adequate.total_count() > 0);
        assert_eq!(adequate.limit_event_count(), 0);
        let warm = cache_counts(store);
        let count = adequate.total_count();
        for _ in 0..2 {
            assert_eq!(
                resolve_generic_method_call(
                    store,
                    &globals,
                    false,
                    request,
                    Some(signature),
                    &mut adequate
                ),
                Ok(Some(selected.clone()))
            );
            assert_eq!(adequate.total_count(), count);
            assert_eq!(adequate.limit_event_count(), 0);
            assert_eq!(cache_counts(store), warm);
        }
    }
}
