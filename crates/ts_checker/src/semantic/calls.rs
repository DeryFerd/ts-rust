//! Exact semantic kernel for direct calls and authenticated tagged templates.
//!
//! This is the dependency-closed fixed-signature branch of pinned
//! typescript-go `checkCallExpression`, `resolveCallExpression`, `resolveCall`,
//! `chooseOverload`, and `hasCorrectArity`. Syntax planning and expression
//! typing remain with the source checker. This module accepts an already-typed
//! callee and arguments, proves an ordered set of stored non-generic call
//! signatures, selects the first applicable fixed-arity candidate, and
//! projects its resolved return type. It never substitutes `any` for an
//! unsupported or malformed call.

use ts_binder::SymbolFlags;

use super::{
    CanonicalGlobalTypes, CanonicalTypeMapperStore, RelationUnavailable, SignatureId, TypeId,
    callable_sets::{StoredCallableSetValidation, validate_stored_callable_set},
    callables::ValidatedSingleCallable,
    signatures::{Signature, SignatureFlags},
    type_records::{TypeData, TypeRecord},
    types::TypeFlags,
};

/// Call-like syntax presented to the direct-call semantic kernel.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum DirectCallForm {
    Call,
    #[allow(dead_code)] // Retained as an explicit typed rejection seam.
    New,
    #[allow(dead_code)] // Source syntax integration is staged separately.
    TaggedTemplate,
}

/// Syntax-neutral input after the source checker has typed the callee and every
/// argument expression.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct DirectCallRequest<'a> {
    pub(super) form: DirectCallForm,
    pub(super) optional_chain: bool,
    pub(super) type_argument_count: usize,
    pub(super) has_spread_argument: bool,
    pub(super) callee: TypeId,
    pub(super) arguments: &'a [TypeId],
}

/// Valid TypeScript semantics outside the first direct-call slice.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum DirectCallUnsupported {
    Form(DirectCallForm),
    OptionalChain,
    TypeArguments { count: usize },
    SpreadArgument,
    NotExactSingleCallable(TypeId),
    PendingCallable(TypeId),
    GenericSignature(SignatureId),
    ExplicitThisParameter(SignatureId),
    RestSignature(SignatureId),
    UnresolvedReturnType(SignatureId),
    OverloadFailureRecovery(TypeId),
}

/// Malformed callable storage or foreign semantic identities.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum DirectCallInvariant {
    InvalidCalleeType(TypeId),
    MalformedCallable(TypeId),
    InvalidArgumentType {
        index: usize,
        type_: TypeId,
    },
    CallableOwnerMismatch {
        callee: TypeId,
        owner: TypeId,
    },
    InvalidSignature(SignatureId),
    SignatureParameterCountMismatch {
        signature: SignatureId,
        stored: usize,
        projected: usize,
    },
    SignatureMinimumMismatch {
        signature: SignatureId,
        stored: i32,
        projected: usize,
    },
    InvalidMinimumArgumentCount {
        signature: SignatureId,
        minimum: usize,
        maximum: usize,
    },
    InvalidParameterType {
        signature: SignatureId,
        index: usize,
        type_: TypeId,
    },
    InvalidRestParameterType {
        signature: SignatureId,
        type_: TypeId,
    },
    MalformedParameterUnion {
        signature: SignatureId,
        index: usize,
        type_: TypeId,
    },
    SignatureReturnMismatch(SignatureId),
    InvalidReturnType {
        signature: SignatureId,
        type_: TypeId,
    },
}

/// A capability, provenance, or relation failure. Ordinary call diagnostics
/// are represented by [`DirectCallApplicability`] instead.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum DirectCallError {
    Unsupported(DirectCallUnsupported),
    Invariant(DirectCallInvariant),
    Relation(RelationUnavailable),
}

impl From<DirectCallUnsupported> for DirectCallError {
    fn from(error: DirectCallUnsupported) -> Self {
        Self::Unsupported(error)
    }
}

impl From<DirectCallInvariant> for DirectCallError {
    fn from(error: DirectCallInvariant) -> Self {
        Self::Invariant(error)
    }
}

impl From<RelationUnavailable> for DirectCallError {
    fn from(error: RelationUnavailable) -> Self {
        Self::Relation(error)
    }
}

/// Whether the selected signature's resolved return is exactly void-like for
/// `checkCallExpression`'s direct `TypeFlags::VOID` branch.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum DirectCallReturnKind {
    Void,
    Value,
}

/// The contextual target paired with one already-typed argument.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct DirectCallArgumentTarget {
    pub(super) index: usize,
    pub(super) argument_type: TypeId,
    pub(super) parameter_type: TypeId,
}

/// Exact signature and return projection retained even when the call has an
/// ordinary arity or assignability error. Pinned overload-failure recovery
/// still selects this sole candidate, so the erroneous call keeps its return
/// type rather than becoming `any`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct DirectCallProjection {
    pub(super) callee: TypeId,
    pub(super) signature: SignatureId,
    pub(super) minimum_argument_count: usize,
    pub(super) maximum_argument_count: usize,
    pub(super) has_effective_rest: bool,
    pub(super) argument_targets: Vec<DirectCallArgumentTarget>,
    pub(super) return_type: TypeId,
    pub(super) return_kind: DirectCallReturnKind,
}

/// Ordinary applicability outcome for the one selected candidate.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum DirectCallApplicability {
    Applicable,
    TooFewArguments {
        expected_at_least: usize,
        actual: usize,
    },
    TooManyArguments {
        expected_at_most: usize,
        actual: usize,
    },
    ArgumentNotAssignable {
        index: usize,
        argument_type: TypeId,
        parameter_type: TypeId,
    },
}

/// Complete result of the first direct-call semantic cut.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct DirectCallResolution {
    pub(super) projection: DirectCallProjection,
    pub(super) applicability: DirectCallApplicability,
}

/// Resolves the dependency-closed non-generic direct-call branch.
///
/// The source caller must pass the context's immutable `strictFunctionTypes`
/// option and authoritative global identities. Relation caches may be written;
/// callable validation and projection themselves are read-only.
pub(super) fn resolve_direct_call(
    store: &mut CanonicalTypeMapperStore,
    global_types: &CanonicalGlobalTypes,
    strict_function_types: bool,
    request: DirectCallRequest<'_>,
) -> Result<DirectCallResolution, DirectCallError> {
    validate_direct_call_form(request)?;
    if store.type_payload(request.callee).is_none() {
        return Err(DirectCallInvariant::InvalidCalleeType(request.callee).into());
    }
    validate_argument_types(store, request.arguments)?;
    validate_tagged_template_argument(store, request)?;

    let projection = match validate_stored_callable_set(store, request.callee) {
        StoredCallableSetValidation::NotCallable => {
            return Err(DirectCallUnsupported::NotExactSingleCallable(request.callee).into());
        }
        StoredCallableSetValidation::Pending { .. } => {
            return Err(DirectCallUnsupported::PendingCallable(request.callee).into());
        }
        StoredCallableSetValidation::Malformed { .. } => {
            return Err(DirectCallInvariant::MalformedCallable(request.callee).into());
        }
        StoredCallableSetValidation::Valid { projection, .. } => projection,
    };
    if projection.owner != request.callee
        || !projection.construct_signatures.is_empty()
        || projection.call_signatures.is_empty()
    {
        return Err(DirectCallUnsupported::NotExactSingleCallable(request.callee).into());
    }
    let callables =
        reorder_direct_call_candidates(store, request.callee, &projection.call_signatures)?;
    let candidate_count = callables.len();
    let mut candidates = Vec::with_capacity(candidate_count);
    for callable in callables {
        match project_validated_direct_call(store, Some(global_types), request, callable) {
            Ok(candidate) => candidates.push(candidate),
            Err(DirectCallError::Unsupported(DirectCallUnsupported::Form(
                DirectCallForm::TaggedTemplate,
            ))) if candidate_count > 1 => {}
            Err(error) => return Err(error),
        }
    }
    if candidates.is_empty() {
        return Err(DirectCallUnsupported::Form(request.form).into());
    }
    if candidate_count == 1 {
        let mut resolution = candidates
            .into_iter()
            .next()
            .expect("the exact-single candidate count was checked");
        if resolution.applicability != DirectCallApplicability::Applicable {
            return Ok(resolution);
        }
        resolution.applicability =
            check_argument_applicability(&resolution.projection, |source, target| {
                store.is_type_assignable_to_with_global_types_and_strict_function_types(
                    source,
                    target,
                    global_types,
                    strict_function_types,
                )
            })?;
        return Ok(resolution);
    }

    if let Some(candidate) = choose_applicable_overload(&candidates, |source, target| {
        store.is_type_subtype_of_with_global_types_and_strict_function_types(
            source,
            target,
            global_types,
            strict_function_types,
        )
    })? {
        return Ok(candidate);
    }
    if let Some(candidate) = choose_applicable_overload(&candidates, |source, target| {
        store.is_type_assignable_to_with_global_types_and_strict_function_types(
            source,
            target,
            global_types,
            strict_function_types,
        )
    })? {
        return Ok(candidate);
    }

    if let Some(candidate) = recover_direct_call_overload(
        store,
        global_types,
        strict_function_types,
        request,
        &candidates,
    )? {
        return Ok(candidate);
    }
    Err(DirectCallUnsupported::OverloadFailureRecovery(request.callee).into())
}

/// Keeps specialized overloads first and reverses merged declaration groups.
fn reorder_direct_call_candidates<'a>(
    store: &CanonicalTypeMapperStore,
    callee: TypeId,
    callables: &'a [ValidatedSingleCallable],
) -> Result<Vec<&'a ValidatedSingleCallable>, DirectCallError> {
    let shared_declaration_owner = store
        .type_payload(callee)
        .and_then(TypeRecord::symbol)
        .and_then(|owner| store.symbol(owner))
        .and_then(|owner| owner.declarations())
        .is_some_and(|declarations| {
            callables.iter().all(|callable| {
                store
                    .signature(callable.signature)
                    .and_then(Signature::declaration)
                    .is_some_and(|declaration| declarations.contains(&declaration))
            })
        });
    let mut ordered = Vec::with_capacity(callables.len());
    let mut previous_parent = None;
    let mut declaration_index = 0;
    let mut cutoff_index = 0;
    let mut specialized_count = 0;

    for callable in callables {
        let signature = store
            .signature(callable.signature)
            .ok_or(DirectCallInvariant::InvalidSignature(callable.signature))?;
        if shared_declaration_owner {
            let parent = signature
                .declaration()
                .and_then(|declaration| store.source_node_parent(declaration));
            if previous_parent.is_some() && previous_parent == parent {
                declaration_index += 1;
            } else {
                previous_parent = parent;
                declaration_index = cutoff_index;
            }
        } else {
            declaration_index = ordered.len();
        }

        let insertion_index = if signature
            .flags()
            .contains(SignatureFlags::HAS_LITERAL_TYPES)
        {
            let index = specialized_count;
            specialized_count += 1;
            cutoff_index += 1;
            index
        } else {
            declaration_index
        };
        ordered.insert(insertion_index, callable);
    }

    Ok(ordered)
}

fn choose_applicable_overload(
    candidates: &[DirectCallResolution],
    mut is_related: impl FnMut(TypeId, TypeId) -> Result<bool, RelationUnavailable>,
) -> Result<Option<DirectCallResolution>, DirectCallError> {
    for candidate in candidates {
        if candidate.applicability != DirectCallApplicability::Applicable {
            continue;
        }
        let applicability = check_argument_applicability(&candidate.projection, &mut is_related)?;
        if applicability == DirectCallApplicability::Applicable {
            let mut selected = candidate.clone();
            selected.applicability = applicability;
            return Ok(Some(selected));
        }
    }
    Ok(None)
}

/// Class implementations can add diagnostic notes that this recovery cannot reproduce.
fn recover_direct_call_overload(
    store: &mut CanonicalTypeMapperStore,
    global_types: &CanonicalGlobalTypes,
    strict_function_types: bool,
    request: DirectCallRequest<'_>,
    candidates: &[DirectCallResolution],
) -> Result<Option<DirectCallResolution>, DirectCallError> {
    let class_method = store
        .type_payload(request.callee)
        .and_then(TypeRecord::symbol)
        .and_then(|symbol| store.symbol(symbol))
        .is_some_and(|method| {
            method.flags().contains(SymbolFlags::METHOD)
                && method
                    .parent()
                    .and_then(|owner| store.symbol(owner))
                    .is_some_and(|owner| owner.flags().contains(SymbolFlags::CLASS))
        });
    if request.form != DirectCallForm::Call || class_method {
        return Ok(None);
    }
    if let Some(candidate) = recover_uniform_overload_arity_error(candidates) {
        return Ok(Some(candidate));
    }
    recover_single_overload_argument_error(candidates, |source, target| {
        store.is_type_assignable_to_with_global_types_and_strict_function_types(
            source,
            target,
            global_types,
            strict_function_types,
        )
    })
}

/// Keeps TS2554 exact when every fixed overload has the same bounds and return.
fn recover_uniform_overload_arity_error(
    candidates: &[DirectCallResolution],
) -> Option<DirectCallResolution> {
    let first = candidates.first()?;
    if first.projection.has_effective_rest
        || !matches!(
            first.applicability,
            DirectCallApplicability::TooFewArguments { .. }
                | DirectCallApplicability::TooManyArguments { .. }
        )
        || candidates.iter().skip(1).any(|candidate| {
            candidate.applicability != first.applicability
                || candidate.projection.has_effective_rest
                || candidate.projection.minimum_argument_count
                    != first.projection.minimum_argument_count
                || candidate.projection.maximum_argument_count
                    != first.projection.maximum_argument_count
                || candidate.projection.return_type != first.projection.return_type
        })
    {
        return None;
    }
    Some(first.clone())
}

/// Recovers TS2345 only when overload synthesis cannot change the return type.
fn recover_single_overload_argument_error(
    candidates: &[DirectCallResolution],
    mut is_assignable: impl FnMut(TypeId, TypeId) -> Result<bool, RelationUnavailable>,
) -> Result<Option<DirectCallResolution>, DirectCallError> {
    let mut eligible = candidates
        .iter()
        .filter(|candidate| candidate.applicability == DirectCallApplicability::Applicable);
    let Some(candidate) = eligible.next() else {
        return Ok(None);
    };
    if eligible.next().is_some()
        || candidates
            .iter()
            .any(|other| other.projection.return_type != candidate.projection.return_type)
    {
        return Ok(None);
    }

    let applicability = check_argument_applicability(&candidate.projection, &mut is_assignable)?;
    if !matches!(
        applicability,
        DirectCallApplicability::ArgumentNotAssignable { .. }
    ) {
        return Ok(None);
    }
    let mut selected = candidate.clone();
    selected.applicability = applicability;
    Ok(Some(selected))
}

fn validate_direct_call_form(request: DirectCallRequest<'_>) -> Result<(), DirectCallError> {
    if !matches!(
        request.form,
        DirectCallForm::Call | DirectCallForm::TaggedTemplate
    ) || request.form == DirectCallForm::TaggedTemplate && request.arguments.is_empty()
    {
        return Err(DirectCallUnsupported::Form(request.form).into());
    }
    if request.optional_chain {
        return Err(DirectCallUnsupported::OptionalChain.into());
    }
    if request.type_argument_count != 0 {
        return Err(DirectCallUnsupported::TypeArguments {
            count: request.type_argument_count,
        }
        .into());
    }
    if request.has_spread_argument {
        return Err(DirectCallUnsupported::SpreadArgument.into());
    }
    Ok(())
}

fn validate_tagged_template_argument(
    store: &CanonicalTypeMapperStore,
    request: DirectCallRequest<'_>,
) -> Result<(), DirectCallError> {
    if request.form != DirectCallForm::TaggedTemplate {
        return Ok(());
    }

    let expected = store
        .intrinsic_bootstrap()
        .and_then(|bootstrap| store.symbol_table(bootstrap.globals))
        .and_then(|globals| globals.get_source("TemplateStringsArray"))
        .and_then(|symbol| store.get_merged_symbol(symbol))
        .filter(|symbol| {
            store
                .symbol(*symbol)
                .is_some_and(|record| record.flags().contains(SymbolFlags::INTERFACE))
        })
        .and_then(|symbol| {
            let type_ = store.declared_type_links(symbol)?.declared_type?;
            let record = store.type_payload(type_)?;
            (matches!(record.data(), TypeData::Interface(_))
                && record
                    .symbol()
                    .and_then(|owner| store.get_merged_symbol(owner))
                    == Some(symbol))
            .then_some(type_)
        });

    if expected.is_none() || request.arguments.first().copied() != expected {
        return Err(DirectCallUnsupported::Form(DirectCallForm::TaggedTemplate).into());
    }
    Ok(())
}

fn validate_argument_types(
    store: &CanonicalTypeMapperStore,
    arguments: &[TypeId],
) -> Result<(), DirectCallError> {
    for (index, type_) in arguments.iter().copied().enumerate() {
        if store.type_payload(type_).is_none() {
            return Err(DirectCallInvariant::InvalidArgumentType { index, type_ }.into());
        }
    }
    Ok(())
}

fn project_validated_direct_call(
    store: &CanonicalTypeMapperStore,
    global_types: Option<&CanonicalGlobalTypes>,
    request: DirectCallRequest<'_>,
    callable: &ValidatedSingleCallable,
) -> Result<DirectCallResolution, DirectCallError> {
    if callable.owner != request.callee {
        return Err(DirectCallInvariant::CallableOwnerMismatch {
            callee: request.callee,
            owner: callable.owner,
        }
        .into());
    }
    let signature = store
        .signature(callable.signature)
        .ok_or(DirectCallInvariant::InvalidSignature(callable.signature))?;
    if !signature.type_parameters().is_empty() {
        return Err(DirectCallUnsupported::GenericSignature(callable.signature).into());
    }
    if signature.this_parameter().is_some() {
        return Err(DirectCallUnsupported::ExplicitThisParameter(callable.signature).into());
    }
    let has_rest_parameter = signature
        .flags()
        .contains(SignatureFlags::HAS_REST_PARAMETER);
    if has_rest_parameter != callable.rest_parameter.is_some() {
        return Err(DirectCallInvariant::SignatureParameterCountMismatch {
            signature: callable.signature,
            stored: signature.parameters().len(),
            projected: callable.parameters.len() + usize::from(callable.rest_parameter.is_some()),
        }
        .into());
    }
    let projected_parameter_count =
        callable.parameters.len() + usize::from(callable.rest_parameter.is_some());
    if signature.parameters().len() != projected_parameter_count {
        return Err(DirectCallInvariant::SignatureParameterCountMismatch {
            signature: callable.signature,
            stored: signature.parameters().len(),
            projected: projected_parameter_count,
        }
        .into());
    }
    if usize::try_from(signature.min_argument_count()).ok() != Some(callable.min_argument_count) {
        return Err(DirectCallInvariant::SignatureMinimumMismatch {
            signature: callable.signature,
            stored: signature.min_argument_count(),
            projected: callable.min_argument_count,
        }
        .into());
    }
    let maximum_argument_count = callable.parameters.len();
    if callable.min_argument_count > maximum_argument_count {
        return Err(DirectCallInvariant::InvalidMinimumArgumentCount {
            signature: callable.signature,
            minimum: callable.min_argument_count,
            maximum: maximum_argument_count,
        }
        .into());
    }
    for (index, parameter) in callable.parameters.iter().copied().enumerate() {
        if store.type_payload(parameter).is_none() {
            return Err(DirectCallInvariant::InvalidParameterType {
                signature: callable.signature,
                index,
                type_: parameter,
            }
            .into());
        }
    }
    let rest_element_type = match callable.rest_parameter {
        None => None,
        Some(rest) if store.validate_canonical_empty_tuple_type(rest).is_ok() => None,
        Some(rest) => {
            let Some(global_types) = global_types else {
                return Err(DirectCallUnsupported::RestSignature(callable.signature).into());
            };
            match store.canonical_array_element_type(global_types, rest) {
                Ok(Some(element)) => Some(element),
                Ok(None) => {
                    return Err(DirectCallUnsupported::RestSignature(callable.signature).into());
                }
                Err(_) => {
                    return Err(DirectCallInvariant::InvalidRestParameterType {
                        signature: callable.signature,
                        type_: rest,
                    }
                    .into());
                }
            }
        }
    };
    let has_effective_rest = rest_element_type.is_some();
    if request.form == DirectCallForm::TaggedTemplate {
        let first_parameter = callable.parameters.first().copied();
        let has_required_template_parameter = callable.min_argument_count != 0
            && (first_parameter == request.arguments.first().copied()
                || store
                    .intrinsic_bootstrap()
                    .is_some_and(|bootstrap| first_parameter == Some(bootstrap.any_type)));
        let has_canonical_any_rest = callable.parameters.is_empty()
            && callable.min_argument_count == 0
            && global_types.is_some_and(|global_types| {
                callable.rest_parameter == Some(global_types.any_array_type)
                    && store
                        .intrinsic_bootstrap()
                        .is_some_and(|bootstrap| rest_element_type == Some(bootstrap.any_type))
            });
        if !has_required_template_parameter && !has_canonical_any_rest {
            return Err(DirectCallUnsupported::Form(DirectCallForm::TaggedTemplate).into());
        }
    }

    let Some(return_type) = callable.return_type else {
        return Err(DirectCallUnsupported::UnresolvedReturnType(callable.signature).into());
    };
    if signature.resolved_return_type() != Some(return_type) {
        return Err(DirectCallInvariant::SignatureReturnMismatch(callable.signature).into());
    }
    let return_record =
        store
            .type_payload(return_type)
            .ok_or(DirectCallInvariant::InvalidReturnType {
                signature: callable.signature,
                type_: return_type,
            })?;
    let return_kind = if return_record.flags().intersects(TypeFlags::VOID) {
        DirectCallReturnKind::Void
    } else {
        DirectCallReturnKind::Value
    };

    let minimum_argument_count = effective_minimum_argument_count(store, callable)?;
    let argument_targets = request
        .arguments
        .iter()
        .copied()
        .enumerate()
        .filter_map(|(index, argument_type)| {
            callable
                .parameters
                .get(index)
                .copied()
                .or(rest_element_type)
                .map(|parameter_type| DirectCallArgumentTarget {
                    index,
                    argument_type,
                    parameter_type,
                })
        })
        .collect();
    let applicability = match request.arguments.len() {
        actual if actual < minimum_argument_count => DirectCallApplicability::TooFewArguments {
            expected_at_least: minimum_argument_count,
            actual,
        },
        actual if !has_effective_rest && actual > maximum_argument_count => {
            DirectCallApplicability::TooManyArguments {
                expected_at_most: maximum_argument_count,
                actual,
            }
        }
        _ => DirectCallApplicability::Applicable,
    };
    Ok(DirectCallResolution {
        projection: DirectCallProjection {
            callee: request.callee,
            signature: callable.signature,
            minimum_argument_count,
            maximum_argument_count,
            has_effective_rest,
            argument_targets,
            return_type,
            return_kind,
        },
        applicability,
    })
}

fn effective_minimum_argument_count(
    store: &CanonicalTypeMapperStore,
    callable: &ValidatedSingleCallable,
) -> Result<usize, DirectCallError> {
    if store
        .signature(callable.signature)
        .ok_or(DirectCallInvariant::InvalidSignature(callable.signature))?
        .flags()
        .contains(SignatureFlags::IS_UNTYPED_SIGNATURE_IN_JS_FILE)
    {
        return Ok(0);
    }

    let mut minimum = callable.min_argument_count;
    while minimum != 0
        && type_contains_void(
            store,
            callable.signature,
            minimum - 1,
            callable.parameters[minimum - 1],
        )?
    {
        minimum -= 1;
    }
    Ok(minimum)
}

fn type_contains_void(
    store: &CanonicalTypeMapperStore,
    signature: SignatureId,
    index: usize,
    type_: TypeId,
) -> Result<bool, DirectCallError> {
    let record = store
        .type_payload(type_)
        .ok_or(DirectCallInvariant::InvalidParameterType {
            signature,
            index,
            type_,
        })?;
    if record.flags().intersects(TypeFlags::VOID) {
        return Ok(true);
    }
    let data_is_union = matches!(record.data(), TypeData::Union(_));
    if !record.flags().intersects(TypeFlags::UNION) {
        return if data_is_union {
            Err(DirectCallInvariant::MalformedParameterUnion {
                signature,
                index,
                type_,
            }
            .into())
        } else {
            Ok(false)
        };
    }
    let TypeData::Union(union) = record.data() else {
        return Err(DirectCallInvariant::MalformedParameterUnion {
            signature,
            index,
            type_,
        }
        .into());
    };
    if union.union.types.is_empty() {
        return Err(DirectCallInvariant::MalformedParameterUnion {
            signature,
            index,
            type_,
        }
        .into());
    }
    for constituent in &union.union.types {
        let Some(constituent_record) = store.type_payload(*constituent) else {
            return Err(DirectCallInvariant::MalformedParameterUnion {
                signature,
                index,
                type_,
            }
            .into());
        };
        if constituent_record.flags().intersects(TypeFlags::VOID) {
            return Ok(true);
        }
    }
    Ok(false)
}

fn check_argument_applicability(
    projection: &DirectCallProjection,
    mut is_assignable: impl FnMut(TypeId, TypeId) -> Result<bool, RelationUnavailable>,
) -> Result<DirectCallApplicability, RelationUnavailable> {
    for target in &projection.argument_targets {
        if !is_assignable(target.argument_type, target.parameter_type)? {
            return Ok(DirectCallApplicability::ArgumentNotAssignable {
                index: target.index,
                argument_type: target.argument_type,
                parameter_type: target.parameter_type,
            });
        }
    }
    Ok(DirectCallApplicability::Applicable)
}

#[cfg(test)]
mod tests {
    use ts_ast::{FileId, NodeRef, SyntaxKind};
    use ts_binder::{
        CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
        EscapedName, SemanticSymbolId, SymbolData, SymbolFlags,
    };
    use ts_parser::{ParseResult, parse_source_file};

    use super::*;
    use crate::semantic::{
        CanonicalCheckerContext, CanonicalCheckerOptions, DeclaredTypeLinks,
        IntrinsicBootstrapOptions, SemanticStore, TypeRecord, mapper::TypeMapper,
        types::ObjectFlags,
    };

    fn initialized_store() -> CanonicalTypeMapperStore {
        let mut store = SemanticStore::<TypeRecord, TypeMapper>::new();
        store
            .initialize_intrinsic_bootstrap(IntrinsicBootstrapOptions::default())
            .unwrap();
        store
    }

    fn array_context(parsed: &ParseResult) -> CanonicalCheckerContext<'_> {
        let file = FileId::new(9_411);
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source("\"/tagged-template-calls.ts\""),
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
            vec![(file, &parsed.arena)],
            CanonicalCheckerOptions::default(),
        )
        .unwrap()
    }

    fn context_template_strings_array(context: &mut CanonicalCheckerContext<'_>) -> TypeId {
        let symbol = context
            .store()
            .symbol_table(context.globals())
            .and_then(|globals| globals.get_source("TemplateStringsArray"))
            .unwrap();
        context.get_declared_type_of_symbol(symbol).unwrap()
    }

    fn parameter(store: &mut CanonicalTypeMapperStore, name: &str) -> SemanticSymbolId {
        store
            .alloc_symbol(SymbolData::new(
                SymbolFlags::FUNCTION_SCOPED_VARIABLE,
                EscapedName::source(name),
            ))
            .unwrap()
    }

    fn template_strings_array(store: &mut CanonicalTypeMapperStore) -> TypeId {
        let symbol = store
            .alloc_symbol(SymbolData::new(
                SymbolFlags::INTERFACE,
                EscapedName::source("TemplateStringsArray"),
            ))
            .unwrap();
        let type_ = store
            .alloc_interface_type(ObjectFlags::INTERFACE, Some(symbol))
            .unwrap();
        let globals = store.intrinsic_bootstrap().unwrap().globals;
        assert_eq!(
            store.insert_symbol(globals, EscapedName::source("TemplateStringsArray"), symbol),
            Some(None)
        );
        assert!(store.set_declared_type_links(
            symbol,
            DeclaredTypeLinks {
                declared_type: Some(type_),
                ..DeclaredTypeLinks::default()
            },
        ));
        type_
    }

    fn callable(
        store: &mut CanonicalTypeMapperStore,
        flags: SignatureFlags,
        parameters: &[TypeId],
        minimum: i32,
        return_type: Option<TypeId>,
    ) -> ValidatedSingleCallable {
        let mut projected_parameters = parameters.to_vec();
        let rest_parameter = if flags.contains(SignatureFlags::HAS_REST_PARAMETER) {
            projected_parameters.pop()
        } else {
            None
        };
        let symbols = parameters
            .iter()
            .enumerate()
            .map(|(index, _)| parameter(store, &format!("p{index}")))
            .collect();
        let signature = store
            .alloc_signature(
                flags,
                None,
                Vec::new(),
                None,
                symbols,
                return_type,
                None,
                minimum,
            )
            .unwrap();
        let owner = store.intrinsic_bootstrap().unwrap().any_function_type;
        ValidatedSingleCallable {
            owner,
            signature,
            parameters: projected_parameters,
            rest_parameter,
            min_argument_count: usize::try_from(minimum).unwrap(),
            return_type,
            strict_variance_exempt: false,
        }
    }

    fn request(callee: TypeId, arguments: &[TypeId]) -> DirectCallRequest<'_> {
        DirectCallRequest {
            form: DirectCallForm::Call,
            optional_chain: false,
            type_argument_count: 0,
            has_spread_argument: false,
            callee,
            arguments,
        }
    }

    #[test]
    fn syntax_capability_boundaries_are_explicit() {
        let store = initialized_store();
        let callee = store.intrinsic_bootstrap().unwrap().any_function_type;
        for (request, expected) in [
            (
                DirectCallRequest {
                    form: DirectCallForm::New,
                    ..request(callee, &[])
                },
                DirectCallUnsupported::Form(DirectCallForm::New),
            ),
            (
                DirectCallRequest {
                    optional_chain: true,
                    ..request(callee, &[])
                },
                DirectCallUnsupported::OptionalChain,
            ),
            (
                DirectCallRequest {
                    type_argument_count: 1,
                    ..request(callee, &[])
                },
                DirectCallUnsupported::TypeArguments { count: 1 },
            ),
            (
                DirectCallRequest {
                    has_spread_argument: true,
                    ..request(callee, &[])
                },
                DirectCallUnsupported::SpreadArgument,
            ),
        ] {
            assert_eq!(
                validate_direct_call_form(request),
                Err(DirectCallError::Unsupported(expected))
            );
        }
    }

    #[test]
    fn literal_overloads_stay_first_without_changing_their_relative_order() {
        let mut store = initialized_store();
        let number = store.intrinsic_bootstrap().unwrap().number_type;
        let broad_first = callable(&mut store, SignatureFlags::NONE, &[number], 1, Some(number));
        let literal_first = callable(
            &mut store,
            SignatureFlags::HAS_LITERAL_TYPES,
            &[number],
            1,
            Some(number),
        );
        let broad_second = callable(&mut store, SignatureFlags::NONE, &[number], 1, Some(number));
        let literal_second = callable(
            &mut store,
            SignatureFlags::HAS_LITERAL_TYPES,
            &[number],
            1,
            Some(number),
        );
        let expected = [
            literal_first.signature,
            literal_second.signature,
            broad_first.signature,
            broad_second.signature,
        ];
        let callee = broad_first.owner;
        let callables = [broad_first, literal_first, broad_second, literal_second];

        let actual = reorder_direct_call_candidates(&store, callee, &callables)
            .unwrap()
            .into_iter()
            .map(|callable| callable.signature)
            .collect::<Vec<_>>();

        assert_eq!(actual, expected);
    }

    #[test]
    fn merged_interface_method_overloads_prefer_later_declaration_groups() {
        let parsed = parse_source_file(concat!(
            "interface Array<T> {} ",
            "interface ReadonlyArray<T> {} ",
            "interface API { ",
            "run(value: string): number; ",
            "run(value: number): number; ",
            "} ",
            "interface API { ",
            "run(value: string): string; ",
            "run(value: number): string; ",
            "}",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(9_411);
        let mut context = array_context(&parsed);
        let owner = context
            .store()
            .symbol_table(context.globals())
            .and_then(|globals| globals.get_source("API"))
            .unwrap();
        context.get_declared_type_of_symbol(owner).unwrap();
        let mut declarations = parsed
            .arena
            .iter()
            .filter_map(|(node, record)| {
                (record.kind == SyntaxKind::MethodSignature).then_some((
                    record.range.start,
                    NodeRef::new(parsed.arena.id(), file, node),
                ))
            })
            .collect::<Vec<_>>();
        declarations.sort_by_key(|(start, _)| *start);
        let [first, second, third, fourth] = declarations.as_slice() else {
            panic!("expected two overloads in each merged declaration")
        };
        let signatures = [third.1, fourth.1, first.1, second.1].map(|declaration| {
            context
                .store()
                .signature_links(declaration)
                .and_then(|links| links.resolved_signature.signature())
                .unwrap()
        });
        let method = context
            .store()
            .symbol(owner)
            .and_then(ts_binder::semantic::Symbol::members)
            .and_then(|members| context.store().symbol_table(members))
            .and_then(|members| members.get_source("run"))
            .unwrap();
        let callee = context
            .store()
            .value_symbol_links(method)
            .and_then(|links| links.resolved_type)
            .unwrap();
        let StoredCallableSetValidation::Valid { projection, .. } =
            validate_stored_callable_set(context.store(), callee)
        else {
            panic!("expected an authenticated merged interface method")
        };
        let ordered =
            reorder_direct_call_candidates(context.store(), callee, &projection.call_signatures)
                .unwrap()
                .into_iter()
                .map(|callable| callable.signature)
                .collect::<Vec<_>>();
        assert_eq!(ordered, signatures);

        let string = context.store().intrinsic_bootstrap().unwrap().string_type;
        let arguments = [string];
        let globals = context.global_types().clone();
        let warm = (
            context.store().type_len(),
            context.store().mapper_len(),
            context.store().signature_len(),
        );

        for _ in 0..2 {
            let resolution = resolve_direct_call(
                context.store_mut_for_test(),
                &globals,
                false,
                request(callee, &arguments),
            )
            .unwrap();
            assert_eq!(resolution.projection.signature, signatures[0]);
            assert_eq!(resolution.projection.return_type, string);
        }

        assert!(context.diagnostics().is_empty());
        assert_eq!(
            (
                context.store().type_len(),
                context.store().mapper_len(),
                context.store().signature_len(),
            ),
            warm,
        );
    }

    #[test]
    fn tagged_templates_skip_overloads_with_incompatible_first_parameters() {
        for declarations in [
            "(template: string): number; (template: TemplateStringsArray): string;",
            "(template: TemplateStringsArray): string; (template: string): number;",
        ] {
            let parsed = parse_source_file(&format!(
                "interface Array<T> {{}} \
                 interface ReadonlyArray<T> {{}} \
                 interface TemplateStringsArray {{}} \
                 interface Tag {{ {declarations} }}",
            ));
            assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
            let mut context = array_context(&parsed);
            let template = context_template_strings_array(&mut context);
            let owner = context
                .store()
                .symbol_table(context.globals())
                .and_then(|globals| globals.get_source("Tag"))
                .unwrap();
            let callee = context.get_declared_type_of_symbol(owner).unwrap();
            let globals = context.global_types().clone();
            let string = context.store().intrinsic_bootstrap().unwrap().string_type;
            let expected = match validate_stored_callable_set(context.store(), callee) {
                StoredCallableSetValidation::Valid { projection, .. } => {
                    projection
                        .call_signatures
                        .iter()
                        .find(|callable| callable.return_type == Some(string))
                        .unwrap()
                        .signature
                }
                _ => panic!("expected two authenticated tag overloads"),
            };
            let arguments = [template];
            let tagged = DirectCallRequest {
                form: DirectCallForm::TaggedTemplate,
                ..request(callee, &arguments)
            };
            let before = (
                context.store().type_len(),
                context.store().mapper_len(),
                context.store().signature_len(),
            );

            for _ in 0..2 {
                let resolution =
                    resolve_direct_call(context.store_mut_for_test(), &globals, false, tagged)
                        .unwrap();
                assert_eq!(resolution.projection.signature, expected);
                assert_eq!(resolution.projection.return_type, string);
                assert_eq!(
                    resolution.applicability,
                    DirectCallApplicability::Applicable
                );
            }

            assert_eq!(
                (
                    context.store().type_len(),
                    context.store().mapper_len(),
                    context.store().signature_len(),
                ),
                before,
            );
        }
    }

    #[test]
    fn incompatible_tagged_template_overloads_keep_their_unsupported_boundary() {
        let parsed = parse_source_file(concat!(
            "interface Array<T> {} ",
            "interface ReadonlyArray<T> {} ",
            "interface TemplateStringsArray {} ",
            "interface Tag { ",
            "(template: string): number; ",
            "(template: number): string; ",
            "}",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let mut context = array_context(&parsed);
        let template = context_template_strings_array(&mut context);
        let owner = context
            .store()
            .symbol_table(context.globals())
            .and_then(|globals| globals.get_source("Tag"))
            .unwrap();
        let callee = context.get_declared_type_of_symbol(owner).unwrap();
        let globals = context.global_types().clone();
        let arguments = [template];
        let tagged = DirectCallRequest {
            form: DirectCallForm::TaggedTemplate,
            ..request(callee, &arguments)
        };

        assert_eq!(
            resolve_direct_call(context.store_mut_for_test(), &globals, false, tagged),
            Err(DirectCallError::Unsupported(DirectCallUnsupported::Form(
                DirectCallForm::TaggedTemplate,
            ))),
        );
    }

    #[test]
    fn tagged_templates_authenticate_the_global_first_argument_and_signature() {
        let mut store = initialized_store();
        let template = template_strings_array(&mut store);
        let bootstrap = store.intrinsic_bootstrap().unwrap();
        let number = bootstrap.number_type;
        let string = bootstrap.string_type;
        let callable = callable(
            &mut store,
            SignatureFlags::NONE,
            &[template, number],
            1,
            Some(string),
        );
        let arguments = [template, number];
        let tagged = DirectCallRequest {
            form: DirectCallForm::TaggedTemplate,
            ..request(callable.owner, &arguments)
        };

        assert_eq!(validate_direct_call_form(tagged), Ok(()));
        assert_eq!(validate_tagged_template_argument(&store, tagged), Ok(()));

        let resolution = project_validated_direct_call(&store, None, tagged, &callable).unwrap();
        assert_eq!(
            resolution.applicability,
            DirectCallApplicability::Applicable
        );
        assert_eq!(resolution.projection.signature, callable.signature);
        assert_eq!(resolution.projection.return_type, string);
        assert_eq!(
            resolution.projection.argument_targets,
            vec![
                DirectCallArgumentTarget {
                    index: 0,
                    argument_type: template,
                    parameter_type: template,
                },
                DirectCallArgumentTarget {
                    index: 1,
                    argument_type: number,
                    parameter_type: number,
                },
            ]
        );
    }

    #[test]
    fn tagged_templates_reject_missing_or_forged_template_arguments() {
        let mut store = initialized_store();
        let callee = store.intrinsic_bootstrap().unwrap().any_function_type;
        let bootstrap = store.intrinsic_bootstrap().unwrap();
        let number = bootstrap.number_type;
        let any = bootstrap.any_type;
        let unknown = bootstrap.unknown_type;
        let unsupported = DirectCallError::Unsupported(DirectCallUnsupported::Form(
            DirectCallForm::TaggedTemplate,
        ));
        let missing = DirectCallRequest {
            form: DirectCallForm::TaggedTemplate,
            ..request(callee, &[])
        };
        assert_eq!(validate_direct_call_form(missing), Err(unsupported));

        let arguments = [number];
        let forged = DirectCallRequest {
            form: DirectCallForm::TaggedTemplate,
            ..request(callee, &arguments)
        };
        assert_eq!(
            validate_tagged_template_argument(&store, forged),
            Err(unsupported)
        );

        let template = template_strings_array(&mut store);
        assert_eq!(
            validate_tagged_template_argument(&store, forged),
            Err(unsupported)
        );

        let wrong_signature =
            callable(&mut store, SignatureFlags::NONE, &[number], 1, Some(number));
        let arguments = [template];
        let tagged = DirectCallRequest {
            form: DirectCallForm::TaggedTemplate,
            ..request(wrong_signature.owner, &arguments)
        };
        assert_eq!(validate_tagged_template_argument(&store, tagged), Ok(()));
        assert_eq!(
            project_validated_direct_call(&store, None, tagged, &wrong_signature),
            Err(unsupported)
        );

        let optional_template = callable(
            &mut store,
            SignatureFlags::NONE,
            &[template],
            0,
            Some(number),
        );
        assert_eq!(
            project_validated_direct_call(&store, None, tagged, &optional_template),
            Err(unsupported)
        );

        let optional_any = callable(&mut store, SignatureFlags::NONE, &[any], 0, Some(number));
        assert_eq!(
            project_validated_direct_call(&store, None, tagged, &optional_any),
            Err(unsupported)
        );

        let unknown_signature = callable(
            &mut store,
            SignatureFlags::NONE,
            &[unknown],
            1,
            Some(number),
        );
        assert_eq!(
            project_validated_direct_call(&store, None, tagged, &unknown_signature),
            Err(unsupported)
        );
    }

    #[test]
    fn tagged_templates_accept_required_intrinsic_any_first_parameters() {
        let parsed = parse_source_file(concat!(
            "interface Array<T> {} ",
            "interface ReadonlyArray<T> {} ",
            "interface TemplateStringsArray {}",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let mut context = array_context(&parsed);
        let template = context_template_strings_array(&mut context);
        let global_types = context.global_types().clone();
        let bootstrap = context.store().intrinsic_bootstrap().unwrap();
        let any = bootstrap.any_type;
        let number = bootstrap.number_type;
        let string = bootstrap.string_type;

        let fixed = callable(
            context.store_mut_for_test(),
            SignatureFlags::NONE,
            &[any],
            1,
            Some(string),
        );
        let fixed_arguments = [template];
        let fixed_tag = DirectCallRequest {
            form: DirectCallForm::TaggedTemplate,
            ..request(fixed.owner, &fixed_arguments)
        };
        assert_eq!(
            validate_tagged_template_argument(context.store(), fixed_tag),
            Ok(())
        );
        let fixed_resolution =
            project_validated_direct_call(context.store(), None, fixed_tag, &fixed).unwrap();
        assert_eq!(
            fixed_resolution.projection.argument_targets,
            vec![DirectCallArgumentTarget {
                index: 0,
                argument_type: template,
                parameter_type: any,
            }],
        );
        assert_eq!(fixed_resolution.projection.minimum_argument_count, 1);
        assert_eq!(fixed_resolution.projection.maximum_argument_count, 1);
        assert!(!fixed_resolution.projection.has_effective_rest);

        let with_rest = callable(
            context.store_mut_for_test(),
            SignatureFlags::HAS_REST_PARAMETER,
            &[any, global_types.any_array_type],
            1,
            Some(string),
        );
        let arguments = [template, number];
        let tagged = DirectCallRequest {
            form: DirectCallForm::TaggedTemplate,
            ..request(with_rest.owner, &arguments)
        };
        assert_eq!(
            validate_tagged_template_argument(context.store(), tagged),
            Ok(())
        );
        let resolution =
            project_validated_direct_call(context.store(), Some(&global_types), tagged, &with_rest)
                .unwrap();
        assert_eq!(
            resolution.applicability,
            DirectCallApplicability::Applicable
        );
        assert_eq!(resolution.projection.minimum_argument_count, 1);
        assert_eq!(resolution.projection.maximum_argument_count, 1);
        assert!(resolution.projection.has_effective_rest);
        assert_eq!(resolution.projection.return_type, string);
        assert_eq!(
            resolution.projection.argument_targets,
            vec![
                DirectCallArgumentTarget {
                    index: 0,
                    argument_type: template,
                    parameter_type: any,
                },
                DirectCallArgumentTarget {
                    index: 1,
                    argument_type: number,
                    parameter_type: any,
                },
            ],
        );
    }

    #[test]
    fn tagged_templates_keep_substitution_argument_diagnostics() {
        let mut store = initialized_store();
        let template = template_strings_array(&mut store);
        let bootstrap = store.intrinsic_bootstrap().unwrap();
        let number = bootstrap.number_type;
        let string = bootstrap.string_type;
        let callable = callable(
            &mut store,
            SignatureFlags::NONE,
            &[template, number],
            2,
            Some(string),
        );
        let arguments = [template, string];
        let tagged = DirectCallRequest {
            form: DirectCallForm::TaggedTemplate,
            ..request(callable.owner, &arguments)
        };
        let resolution = project_validated_direct_call(&store, None, tagged, &callable).unwrap();
        let applicability =
            check_argument_applicability(&resolution.projection, |source, target| {
                Ok(source == target)
            })
            .unwrap();

        assert_eq!(
            applicability,
            DirectCallApplicability::ArgumentNotAssignable {
                index: 1,
                argument_type: string,
                parameter_type: number,
            }
        );
        assert_eq!(resolution.projection.return_type, string);
    }

    #[test]
    fn tagged_templates_accept_canonical_any_rest_signatures() {
        let parsed = parse_source_file(concat!(
            "interface Array<T> {} ",
            "interface ReadonlyArray<T> {} ",
            "interface TemplateStringsArray {}",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let mut context = array_context(&parsed);
        let template = context_template_strings_array(&mut context);
        let global_types = context.global_types().clone();
        let bootstrap = context.store().intrinsic_bootstrap().unwrap();
        let any = bootstrap.any_type;
        let number = bootstrap.number_type;
        let string = bootstrap.string_type;
        let callable = callable(
            context.store_mut_for_test(),
            SignatureFlags::HAS_REST_PARAMETER,
            &[global_types.any_array_type],
            0,
            Some(string),
        );

        for arguments in [&[template][..], &[template, number, string][..]] {
            let tagged = DirectCallRequest {
                form: DirectCallForm::TaggedTemplate,
                ..request(callable.owner, arguments)
            };
            assert_eq!(
                validate_tagged_template_argument(context.store(), tagged),
                Ok(())
            );
            let before = (
                context.store().type_len(),
                context.store().signature_len(),
                context.store().checker_link_allocated_lengths(),
            );
            let resolution = project_validated_direct_call(
                context.store(),
                Some(&global_types),
                tagged,
                &callable,
            )
            .unwrap();

            assert_eq!(
                resolution.applicability,
                DirectCallApplicability::Applicable
            );
            assert_eq!(resolution.projection.minimum_argument_count, 0);
            assert_eq!(resolution.projection.maximum_argument_count, 0);
            assert!(resolution.projection.has_effective_rest);
            assert_eq!(resolution.projection.return_type, string);
            assert_eq!(
                resolution.projection.argument_targets.len(),
                arguments.len()
            );
            assert!(
                resolution
                    .projection
                    .argument_targets
                    .iter()
                    .enumerate()
                    .all(|(index, target)| {
                        target.index == index
                            && target.argument_type == arguments[index]
                            && target.parameter_type == any
                    })
            );
            assert_eq!(
                (
                    context.store().type_len(),
                    context.store().signature_len(),
                    context.store().checker_link_allocated_lengths(),
                ),
                before,
            );
        }
    }

    #[test]
    fn tagged_templates_reject_noncanonical_rest_only_signatures() {
        let parsed = parse_source_file(concat!(
            "interface Array<T> {} ",
            "interface ReadonlyArray<T> {} ",
            "interface TemplateStringsArray {}",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let mut context = array_context(&parsed);
        let template = context_template_strings_array(&mut context);
        let global_types = context.global_types().clone();
        let bootstrap = context.store().intrinsic_bootstrap().unwrap();
        let number = bootstrap.number_type;
        let string = bootstrap.string_type;
        let number_array = context
            .store_mut_for_test()
            .create_canonical_array_type(&global_types, number, false)
            .unwrap();
        let unsupported = DirectCallError::Unsupported(DirectCallUnsupported::Form(
            DirectCallForm::TaggedTemplate,
        ));

        for rest in [number_array, global_types.any_readonly_array_type] {
            let callable = callable(
                context.store_mut_for_test(),
                SignatureFlags::HAS_REST_PARAMETER,
                &[rest],
                0,
                Some(string),
            );
            let arguments = [template];
            let tagged = DirectCallRequest {
                form: DirectCallForm::TaggedTemplate,
                ..request(callable.owner, &arguments)
            };
            let before = (
                context.store().type_len(),
                context.store().signature_len(),
                context.store().checker_link_allocated_lengths(),
            );

            assert_eq!(
                project_validated_direct_call(
                    context.store(),
                    Some(&global_types),
                    tagged,
                    &callable,
                ),
                Err(unsupported),
            );
            assert_eq!(
                (
                    context.store().type_len(),
                    context.store().signature_len(),
                    context.store().checker_link_allocated_lengths(),
                ),
                before,
            );
        }

        let callable = callable(
            context.store_mut_for_test(),
            SignatureFlags::HAS_REST_PARAMETER,
            &[global_types.any_array_type],
            0,
            Some(string),
        );
        let forged_arguments = [number];
        let forged = DirectCallRequest {
            form: DirectCallForm::TaggedTemplate,
            ..request(callable.owner, &forged_arguments)
        };
        assert_eq!(
            validate_tagged_template_argument(context.store(), forged),
            Err(unsupported),
        );

        let arguments = [template];
        let tagged = DirectCallRequest {
            form: DirectCallForm::TaggedTemplate,
            ..request(callable.owner, &arguments)
        };
        assert_eq!(
            project_validated_direct_call(context.store(), None, tagged, &callable),
            Err(DirectCallError::Unsupported(
                DirectCallUnsupported::RestSignature(callable.signature),
            )),
        );
    }

    #[test]
    fn fixed_signature_projects_exact_targets_and_value_return() {
        let mut store = initialized_store();
        let bootstrap = store.intrinsic_bootstrap().unwrap();
        let number = bootstrap.number_type;
        let string = bootstrap.string_type;
        let callable = callable(
            &mut store,
            SignatureFlags::NONE,
            &[number, string],
            1,
            Some(string),
        );
        let arguments = [number];
        let resolution = project_validated_direct_call(
            &store,
            None,
            request(callable.owner, &arguments),
            &callable,
        )
        .unwrap();

        assert_eq!(
            resolution.applicability,
            DirectCallApplicability::Applicable
        );
        assert_eq!(resolution.projection.signature, callable.signature);
        assert_eq!(resolution.projection.minimum_argument_count, 1);
        assert_eq!(resolution.projection.maximum_argument_count, 2);
        assert_eq!(resolution.projection.return_type, string);
        assert_eq!(
            resolution.projection.return_kind,
            DirectCallReturnKind::Value
        );
        assert_eq!(
            resolution.projection.argument_targets,
            vec![DirectCallArgumentTarget {
                index: 0,
                argument_type: number,
                parameter_type: number,
            }]
        );
    }

    #[test]
    fn arity_is_checked_before_argument_applicability() {
        let mut store = initialized_store();
        let bootstrap = store.intrinsic_bootstrap().unwrap();
        let number = bootstrap.number_type;
        let string = bootstrap.string_type;
        let callable = callable(
            &mut store,
            SignatureFlags::NONE,
            &[number, string],
            2,
            Some(string),
        );

        let too_few = project_validated_direct_call(
            &store,
            None,
            request(callable.owner, &[number]),
            &callable,
        )
        .unwrap();
        assert_eq!(
            too_few.applicability,
            DirectCallApplicability::TooFewArguments {
                expected_at_least: 2,
                actual: 1,
            }
        );

        let too_many = project_validated_direct_call(
            &store,
            None,
            request(callable.owner, &[number, string, number]),
            &callable,
        )
        .unwrap();
        assert_eq!(
            too_many.applicability,
            DirectCallApplicability::TooManyArguments {
                expected_at_most: 2,
                actual: 3,
            }
        );
        assert_eq!(too_many.projection.argument_targets.len(), 2);
    }

    #[test]
    fn trailing_void_parameters_reduce_the_effective_minimum() {
        let mut store = initialized_store();
        let bootstrap = store.intrinsic_bootstrap().unwrap();
        let number = bootstrap.number_type;
        let void = bootstrap.void_type;
        let callable = callable(
            &mut store,
            SignatureFlags::NONE,
            &[number, void],
            2,
            Some(void),
        );
        let resolution = project_validated_direct_call(
            &store,
            None,
            request(callable.owner, &[number]),
            &callable,
        )
        .unwrap();

        assert_eq!(resolution.projection.minimum_argument_count, 1);
        assert_eq!(
            resolution.projection.return_kind,
            DirectCallReturnKind::Void
        );
        assert_eq!(
            resolution.applicability,
            DirectCallApplicability::Applicable
        );
    }

    #[test]
    fn untyped_javascript_signatures_use_zero_effective_minimum_without_changing_metadata() {
        let mut store = initialized_store();
        let bootstrap = store.intrinsic_bootstrap().unwrap();
        let any = bootstrap.any_type;
        let number = bootstrap.number_type;
        let void = bootstrap.void_type;
        let javascript = callable(
            &mut store,
            SignatureFlags::IS_UNTYPED_SIGNATURE_IN_JS_FILE,
            &[any],
            1,
            Some(void),
        );

        let missing = project_validated_direct_call(
            &store,
            None,
            request(javascript.owner, &[]),
            &javascript,
        )
        .unwrap();
        assert_eq!(missing.projection.minimum_argument_count, 0);
        assert_eq!(missing.projection.maximum_argument_count, 1);
        assert_eq!(missing.applicability, DirectCallApplicability::Applicable);

        let extra = project_validated_direct_call(
            &store,
            None,
            request(javascript.owner, &[number, number, number]),
            &javascript,
        )
        .unwrap();
        assert_eq!(extra.projection.minimum_argument_count, 0);
        assert_eq!(extra.projection.maximum_argument_count, 1);
        assert_eq!(
            extra.applicability,
            DirectCallApplicability::TooManyArguments {
                expected_at_most: 1,
                actual: 3,
            },
        );

        let stored = store.signature(javascript.signature).unwrap();
        assert_eq!(stored.min_argument_count(), 1);
        assert_eq!(stored.resolved_min_argument_count(), -1);

        let typescript = callable(&mut store, SignatureFlags::NONE, &[any], 1, Some(void));
        let missing = project_validated_direct_call(
            &store,
            None,
            request(typescript.owner, &[]),
            &typescript,
        )
        .unwrap();
        assert_eq!(missing.projection.minimum_argument_count, 1);
        assert_eq!(missing.projection.maximum_argument_count, 1);
        assert_eq!(
            missing.applicability,
            DirectCallApplicability::TooFewArguments {
                expected_at_least: 1,
                actual: 0,
            },
        );
    }

    #[test]
    fn first_argument_relation_failure_is_retained_without_any_fallback() {
        let mut store = initialized_store();
        let bootstrap = store.intrinsic_bootstrap().unwrap();
        let number = bootstrap.number_type;
        let string = bootstrap.string_type;
        let callable = callable(
            &mut store,
            SignatureFlags::NONE,
            &[number, number],
            2,
            Some(string),
        );
        let resolution = project_validated_direct_call(
            &store,
            None,
            request(callable.owner, &[number, string]),
            &callable,
        )
        .unwrap();
        let applicability =
            check_argument_applicability(&resolution.projection, |source, target| {
                Ok(source == target)
            })
            .unwrap();

        assert_eq!(
            applicability,
            DirectCallApplicability::ArgumentNotAssignable {
                index: 1,
                argument_type: string,
                parameter_type: number,
            }
        );
        assert_eq!(resolution.projection.return_type, string);
    }

    #[test]
    fn unresolved_return_and_rest_signature_stop_at_typed_seams() {
        let mut store = initialized_store();
        let bootstrap = store.intrinsic_bootstrap().unwrap();
        let number = bootstrap.number_type;
        let unresolved = callable(&mut store, SignatureFlags::NONE, &[number], 1, None);
        assert_eq!(
            project_validated_direct_call(
                &store,
                None,
                request(unresolved.owner, &[number]),
                &unresolved,
            ),
            Err(DirectCallError::Unsupported(
                DirectCallUnsupported::UnresolvedReturnType(unresolved.signature)
            ))
        );

        let rest = callable(
            &mut store,
            SignatureFlags::HAS_REST_PARAMETER,
            &[number],
            0,
            Some(number),
        );
        assert_eq!(
            project_validated_direct_call(&store, None, request(rest.owner, &[number]), &rest,),
            Err(DirectCallError::Unsupported(
                DirectCallUnsupported::RestSignature(rest.signature)
            ))
        );
    }
}
