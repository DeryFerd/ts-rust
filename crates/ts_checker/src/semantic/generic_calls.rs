//! Exact semantic kernel for the first generic direct-call vertical.
//!
//! The admitted signature is exactly `<T>(value: T): T`: one stored call
//! signature, one naked unconstrained/default-free type parameter, one required
//! parameter, and a naked return. Calls may infer `T` from one leaf argument or
//! supply one explicit leaf type argument. Overloads, missing/extra value or
//! type arguments, constraints, defaults, contextual/structured inference,
//! spreads, `this`, and rest signatures remain typed boundaries.

#![allow(dead_code)] // Installed ahead of the source-call dispatch consumer.

use ts_binder::{CheckFlags, SymbolData, SymbolFlags};

use super::{
    CanonicalGlobalTypes, CanonicalTypeMapperStore, RelationUnavailable, SemanticSymbolId,
    SignatureId, TypeId, TypeMapperId, ValueSymbolLinks,
    callables::{
        StoredSingleCallableValidation, ValidatedSingleCallable, validate_stored_single_callable,
    },
    calls::{
        DirectCallApplicability, DirectCallArgumentTarget, DirectCallForm, DirectCallReturnKind,
    },
    declared::{cached_ordinary_type_parameter_owner, type_list_key},
    inference::{NakedTypeInferenceError, infer_naked_type_parameter, validate_inference_leaf},
    signatures::SignatureFlags,
    source_callables::{StoredSourceCallableValidation, validate_stored_source_callable},
    store::CachedSignatureLookup,
    type_records::TypeData,
    types::{ObjectFlags, TypeFlags},
};

/// Syntax-neutral input after the source checker has typed the callee,
/// explicit type argument (if any), and sole value argument.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct IdentityGenericCallRequest<'a> {
    pub(super) form: DirectCallForm,
    pub(super) optional_chain: bool,
    /// `None` requests inference; `Some` preserves explicit arity, including
    /// invalid zero/many slices, for a fail-closed TS2558 integration seam.
    pub(super) explicit_type_arguments: Option<&'a [TypeId]>,
    pub(super) has_spread_argument: bool,
    pub(super) callee: TypeId,
    pub(super) arguments: &'a [TypeId],
}

/// Valid TypeScript behavior outside the first identity-generic slice.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum IdentityGenericCallUnsupported {
    Form(DirectCallForm),
    OptionalChain,
    SpreadArgument,
    TypeArgumentArity {
        expected: usize,
        actual: usize,
    },
    ValueArgumentArity {
        expected: usize,
        actual: usize,
    },
    NotExactSingleCallable(TypeId),
    PendingCallable(TypeId),
    SignatureTypeParameterCount {
        signature: SignatureId,
        actual: usize,
    },
    SignatureParameterCount {
        signature: SignatureId,
        actual: usize,
    },
    SignatureFlags(SignatureId),
    ExplicitThisParameter(SignatureId),
    RestSignature(SignatureId),
    NonRequiredParameter(SignatureId),
    NonNakedParameter(SignatureId),
    NonNakedReturn(SignatureId),
    UnresolvedReturnType(SignatureId),
    UnresolvedTypeParameterConstraint(TypeId),
    ConstrainedTypeParameter(TypeId),
    UnresolvedTypeParameterDefault(TypeId),
    DefaultedTypeParameter(TypeId),
    InstantiatedTypeParameter(TypeId),
    ArgumentLeaf(TypeId),
    TypeArgumentLeaf(TypeId),
}

/// Malformed storage or foreign semantic identities.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum IdentityGenericCallInvariant {
    InvalidCalleeType(TypeId),
    MalformedCallable(TypeId),
    InvalidSignature(SignatureId),
    CallableOwnerMismatch {
        callee: TypeId,
        owner: TypeId,
    },
    CallableSignatureMismatch(SignatureId),
    InvalidTypeParameter(TypeId),
    InvalidParameterSymbol(SemanticSymbolId),
    InvalidArgumentType(TypeId),
    InvalidTypeArgument(TypeId),
    InvalidInstantiation {
        source: TypeId,
        expected: TypeId,
        actual: TypeId,
    },
    InvalidCachedInstantiation {
        target: SignatureId,
        type_argument: TypeId,
        signature: SignatureId,
    },
    InstantiationCacheHashCollision {
        target: SignatureId,
        type_argument: TypeId,
        cached: SignatureId,
    },
    Capacity(SignatureId),
}

/// Capability, provenance, inference, instantiation, or relation failure.
#[derive(Debug, PartialEq)]
pub(super) enum IdentityGenericCallError {
    Unsupported(IdentityGenericCallUnsupported),
    Invariant(IdentityGenericCallInvariant),
    Inference(NakedTypeInferenceError),
    Relation(RelationUnavailable),
}

impl From<IdentityGenericCallUnsupported> for IdentityGenericCallError {
    fn from(error: IdentityGenericCallUnsupported) -> Self {
        Self::Unsupported(error)
    }
}

impl From<IdentityGenericCallInvariant> for IdentityGenericCallError {
    fn from(error: IdentityGenericCallInvariant) -> Self {
        Self::Invariant(error)
    }
}

impl From<NakedTypeInferenceError> for IdentityGenericCallError {
    fn from(error: NakedTypeInferenceError) -> Self {
        Self::Inference(error)
    }
}

impl From<RelationUnavailable> for IdentityGenericCallError {
    fn from(error: RelationUnavailable) -> Self {
        Self::Relation(error)
    }
}

/// Exact instantiated signature and type-argument projection.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct IdentityGenericCallProjection {
    pub(super) callee: TypeId,
    pub(super) generic_signature: SignatureId,
    pub(super) signature: SignatureId,
    pub(super) mapper: TypeMapperId,
    pub(super) type_parameter: TypeId,
    pub(super) type_argument: TypeId,
    pub(super) argument_target: DirectCallArgumentTarget,
    pub(super) return_type: TypeId,
    pub(super) return_kind: DirectCallReturnKind,
}

/// Complete result for one applicable or argument-inapplicable identity call.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct IdentityGenericCallResolution {
    pub(super) projection: IdentityGenericCallProjection,
    pub(super) applicability: DirectCallApplicability,
}

#[derive(Clone, Copy, Debug)]
struct IdentitySignatureShape {
    signature: SignatureId,
    type_parameter: TypeId,
    parameter_symbol: SemanticSymbolId,
}

#[derive(Clone, Copy, Debug)]
struct PreparedIdentityGenericCall {
    callee: TypeId,
    shape: IdentitySignatureShape,
    argument: TypeId,
    type_argument: TypeId,
    return_kind: DirectCallReturnKind,
}

/// Proof carried from the exact callable provider into type-parameter cache
/// validation. Only source syntax validation can prove that cold constraint
/// and default caches mean "declared absent"; every other provider must have
/// published the canonical no-constraint sentinels.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum IdentityTypeParameterCacheProvenance {
    RequireResolvedCaches,
    ExactDefaultFreeSource,
}

/// Resolves the first generic call branch through the store's callable
/// provider and authoritative relation context.
pub(super) fn resolve_identity_generic_call(
    store: &mut CanonicalTypeMapperStore,
    global_types: &CanonicalGlobalTypes,
    strict_function_types: bool,
    request: IdentityGenericCallRequest<'_>,
) -> Result<IdentityGenericCallResolution, IdentityGenericCallError> {
    validate_request_form(store, request)?;
    let callable = match validate_stored_single_callable(store, request.callee) {
        StoredSingleCallableValidation::NotCallable => {
            return Err(
                IdentityGenericCallUnsupported::NotExactSingleCallable(request.callee).into(),
            );
        }
        StoredSingleCallableValidation::Pending { .. } => {
            return Err(IdentityGenericCallUnsupported::PendingCallable(request.callee).into());
        }
        StoredSingleCallableValidation::Malformed { .. } => {
            return Err(IdentityGenericCallInvariant::MalformedCallable(request.callee).into());
        }
        StoredSingleCallableValidation::Valid { callable, .. } => callable,
    };
    let cache_provenance =
        identity_type_parameter_cache_provenance(store, request.callee, &callable);
    resolve_validated_identity_call(
        store,
        request,
        &callable,
        cache_provenance,
        |store, source, target| {
            store.is_type_assignable_to_with_global_types_and_strict_function_types(
                source,
                target,
                global_types,
                strict_function_types,
            )
        },
    )
}

fn identity_type_parameter_cache_provenance(
    store: &CanonicalTypeMapperStore,
    callee: TypeId,
    callable: &ValidatedSingleCallable,
) -> IdentityTypeParameterCacheProvenance {
    let Some(provenance) = store.source_callable_provenance(callee) else {
        return IdentityTypeParameterCacheProvenance::RequireResolvedCaches;
    };
    let Some(default_free_declaration) = provenance.default_free_type_parameter else {
        return IdentityTypeParameterCacheProvenance::RequireResolvedCaches;
    };
    let Some(signature) = store.signature(callable.signature) else {
        return IdentityTypeParameterCacheProvenance::RequireResolvedCaches;
    };
    let [type_parameter] = signature.type_parameters() else {
        return IdentityTypeParameterCacheProvenance::RequireResolvedCaches;
    };
    let Some(type_parameter_owner) = cached_ordinary_type_parameter_owner(store, *type_parameter)
    else {
        return IdentityTypeParameterCacheProvenance::RequireResolvedCaches;
    };
    if provenance.signature != callable.signature
        || store.source_callable_type_for_signature(callable.signature) != Some(callee)
        || store
            .symbol(type_parameter_owner)
            .and_then(|symbol| symbol.declarations())
            != Some(&[default_free_declaration])
    {
        return IdentityTypeParameterCacheProvenance::RequireResolvedCaches;
    }
    match validate_stored_source_callable(store, callee) {
        StoredSourceCallableValidation::Valid(edges)
            if edges.first().copied() == Some(*type_parameter) =>
        {
            IdentityTypeParameterCacheProvenance::ExactDefaultFreeSource
        }
        _ => IdentityTypeParameterCacheProvenance::RequireResolvedCaches,
    }
}

fn validate_request_form(
    store: &CanonicalTypeMapperStore,
    request: IdentityGenericCallRequest<'_>,
) -> Result<(), IdentityGenericCallError> {
    if request.form != DirectCallForm::Call {
        return Err(IdentityGenericCallUnsupported::Form(request.form).into());
    }
    if store.type_payload(request.callee).is_none() {
        return Err(IdentityGenericCallInvariant::InvalidCalleeType(request.callee).into());
    }
    if request.optional_chain {
        return Err(IdentityGenericCallUnsupported::OptionalChain.into());
    }
    if request.has_spread_argument {
        return Err(IdentityGenericCallUnsupported::SpreadArgument.into());
    }
    if let Some(type_arguments) = request.explicit_type_arguments
        && type_arguments.len() != 1
    {
        return Err(IdentityGenericCallUnsupported::TypeArgumentArity {
            expected: 1,
            actual: type_arguments.len(),
        }
        .into());
    }
    if request.arguments.len() != 1 {
        return Err(IdentityGenericCallUnsupported::ValueArgumentArity {
            expected: 1,
            actual: request.arguments.len(),
        }
        .into());
    }
    let argument = request.arguments[0];
    if store.type_payload(argument).is_none() {
        return Err(IdentityGenericCallInvariant::InvalidArgumentType(argument).into());
    }
    if let Some(type_argument) = request
        .explicit_type_arguments
        .and_then(|arguments| arguments.first())
        .copied()
        && store.type_payload(type_argument).is_none()
    {
        return Err(IdentityGenericCallInvariant::InvalidTypeArgument(type_argument).into());
    }
    Ok(())
}

/// Projects a provider-validated callable. Kept separate so focused tests can
/// exercise the kernel before every callable family admits generic records.
fn project_validated_identity_call(
    store: &mut CanonicalTypeMapperStore,
    request: IdentityGenericCallRequest<'_>,
    callable: &ValidatedSingleCallable,
    cache_provenance: IdentityTypeParameterCacheProvenance,
) -> Result<IdentityGenericCallResolution, IdentityGenericCallError> {
    resolve_validated_identity_call(store, request, callable, cache_provenance, |_, _, _| {
        Ok(true)
    })
}

fn resolve_validated_identity_call(
    store: &mut CanonicalTypeMapperStore,
    request: IdentityGenericCallRequest<'_>,
    callable: &ValidatedSingleCallable,
    cache_provenance: IdentityTypeParameterCacheProvenance,
    mut is_assignable: impl FnMut(
        &mut CanonicalTypeMapperStore,
        TypeId,
        TypeId,
    ) -> Result<bool, RelationUnavailable>,
) -> Result<IdentityGenericCallResolution, IdentityGenericCallError> {
    let prepared = prepare_validated_identity_call(store, request, callable, cache_provenance)?;
    // A poisoned existing cache is an invariant even when relation work would
    // otherwise fail. Cache validation is read-only and must precede it.
    let cached = cached_identity_instantiation(store, prepared.shape, prepared.type_argument)?;
    // Relation/global-type resolution is fallible and may mutate only its own
    // caches. Complete it before publishing a cold mapper/signature graph.
    let applicability = check_identity_argument_applicability(
        prepared.argument,
        prepared.type_argument,
        |source, target| is_assignable(store, source, target),
    )?;
    project_prepared_identity_call(store, prepared, cached, applicability)
}

fn prepare_validated_identity_call(
    store: &CanonicalTypeMapperStore,
    request: IdentityGenericCallRequest<'_>,
    callable: &ValidatedSingleCallable,
    cache_provenance: IdentityTypeParameterCacheProvenance,
) -> Result<PreparedIdentityGenericCall, IdentityGenericCallError> {
    validate_request_form(store, request)?;
    let shape =
        validate_identity_signature_shape(store, request.callee, callable, cache_provenance)?;
    let argument = request.arguments[0];
    let type_argument = match request.explicit_type_arguments {
        Some(type_arguments) => {
            let type_argument = type_arguments[0];
            validate_inference_leaf(store, type_argument)
                .map_err(|error| map_inference_leaf_error(error, type_argument, true))?;
            type_argument
        }
        None => infer_naked_type_parameter(store, argument)
            .map_err(|error| map_inference_leaf_error(error, argument, false))?,
    };
    validate_inference_leaf(store, argument)
        .map_err(|error| map_inference_leaf_error(error, argument, false))?;

    let return_record = store.type_payload(type_argument).ok_or(
        IdentityGenericCallInvariant::InvalidInstantiation {
            source: shape.type_parameter,
            expected: type_argument,
            actual: type_argument,
        },
    )?;
    let return_kind = if return_record.flags().intersects(TypeFlags::VOID) {
        DirectCallReturnKind::Void
    } else {
        DirectCallReturnKind::Value
    };
    Ok(PreparedIdentityGenericCall {
        callee: request.callee,
        shape,
        argument,
        type_argument,
        return_kind,
    })
}

fn project_prepared_identity_call(
    store: &mut CanonicalTypeMapperStore,
    prepared: PreparedIdentityGenericCall,
    cached: Option<(SignatureId, TypeMapperId)>,
    applicability: DirectCallApplicability,
) -> Result<IdentityGenericCallResolution, IdentityGenericCallError> {
    let (signature, mapper, parameter_type, return_type) = get_or_create_identity_instantiation(
        store,
        prepared.shape,
        prepared.type_argument,
        cached,
    )?;
    let projection = IdentityGenericCallProjection {
        callee: prepared.callee,
        generic_signature: prepared.shape.signature,
        signature,
        mapper,
        type_parameter: prepared.shape.type_parameter,
        type_argument: prepared.type_argument,
        argument_target: DirectCallArgumentTarget {
            index: 0,
            argument_type: prepared.argument,
            parameter_type,
        },
        return_type,
        return_kind: prepared.return_kind,
    };
    Ok(IdentityGenericCallResolution {
        projection,
        applicability,
    })
}

fn map_inference_leaf_error(
    error: NakedTypeInferenceError,
    candidate: TypeId,
    type_argument: bool,
) -> IdentityGenericCallError {
    if matches!(
        error,
        NakedTypeInferenceError::InvalidCandidate(_)
            | NakedTypeInferenceError::InvalidCanonicalCandidate { .. }
    ) {
        return IdentityGenericCallError::Inference(error);
    }
    if type_argument {
        IdentityGenericCallUnsupported::TypeArgumentLeaf(candidate).into()
    } else {
        IdentityGenericCallUnsupported::ArgumentLeaf(candidate).into()
    }
}

fn validate_identity_signature_shape(
    store: &CanonicalTypeMapperStore,
    callee: TypeId,
    callable: &ValidatedSingleCallable,
    cache_provenance: IdentityTypeParameterCacheProvenance,
) -> Result<IdentitySignatureShape, IdentityGenericCallError> {
    if callable.owner != callee {
        return Err(IdentityGenericCallInvariant::CallableOwnerMismatch {
            callee,
            owner: callable.owner,
        }
        .into());
    }
    let signature = store.signature(callable.signature).ok_or(
        IdentityGenericCallInvariant::InvalidSignature(callable.signature),
    )?;
    let [type_parameter] = signature.type_parameters() else {
        return Err(
            IdentityGenericCallUnsupported::SignatureTypeParameterCount {
                signature: callable.signature,
                actual: signature.type_parameters().len(),
            }
            .into(),
        );
    };
    let type_parameter = *type_parameter;
    let [parameter_symbol] = signature.parameters() else {
        return Err(IdentityGenericCallUnsupported::SignatureParameterCount {
            signature: callable.signature,
            actual: signature.parameters().len(),
        }
        .into());
    };
    let parameter_symbol = *parameter_symbol;
    if signature.flags() != SignatureFlags::NONE {
        return Err(IdentityGenericCallUnsupported::SignatureFlags(callable.signature).into());
    }
    if signature.this_parameter().is_some() {
        return Err(
            IdentityGenericCallUnsupported::ExplicitThisParameter(callable.signature).into(),
        );
    }
    if signature.has_rest_parameter() {
        return Err(IdentityGenericCallUnsupported::RestSignature(callable.signature).into());
    }
    if signature.min_argument_count() != 1 || callable.min_argument_count != 1 {
        return Err(
            IdentityGenericCallUnsupported::NonRequiredParameter(callable.signature).into(),
        );
    }
    if signature.resolved_min_argument_count() != -1
        || signature.resolved_type_predicate().is_some()
        || signature.target().is_some()
        || signature.mapper().is_some()
        || signature.isolated_signature_type().is_some()
        || signature.composite().is_some()
        || callable.strict_variance_exempt
    {
        return Err(
            IdentityGenericCallInvariant::CallableSignatureMismatch(callable.signature).into(),
        );
    }
    if callable.parameters.as_slice() != [type_parameter] {
        return Err(IdentityGenericCallUnsupported::NonNakedParameter(callable.signature).into());
    }
    let Some(return_type) = callable.return_type else {
        return Err(
            IdentityGenericCallUnsupported::UnresolvedReturnType(callable.signature).into(),
        );
    };
    if return_type != type_parameter || signature.resolved_return_type() != Some(type_parameter) {
        return Err(IdentityGenericCallUnsupported::NonNakedReturn(callable.signature).into());
    }
    let parameter_record = store.symbol(parameter_symbol).ok_or(
        IdentityGenericCallInvariant::InvalidParameterSymbol(parameter_symbol),
    )?;
    if parameter_record.flags() != SymbolFlags::FUNCTION_SCOPED_VARIABLE
        || parameter_record.check_flags() != CheckFlags::NONE
        || store.value_symbol_links(parameter_symbol)
            != Some(&ValueSymbolLinks {
                resolved_type: Some(type_parameter),
                ..ValueSymbolLinks::default()
            })
    {
        return Err(IdentityGenericCallInvariant::InvalidParameterSymbol(parameter_symbol).into());
    }
    validate_unconstrained_default_free_parameter(store, type_parameter, cache_provenance)?;
    Ok(IdentitySignatureShape {
        signature: callable.signature,
        type_parameter,
        parameter_symbol,
    })
}

fn validate_unconstrained_default_free_parameter(
    store: &CanonicalTypeMapperStore,
    type_parameter: TypeId,
    cache_provenance: IdentityTypeParameterCacheProvenance,
) -> Result<(), IdentityGenericCallError> {
    let record = store.type_payload(type_parameter).ok_or(
        IdentityGenericCallInvariant::InvalidTypeParameter(type_parameter),
    )?;
    let TypeData::TypeParameter(data) = record.data() else {
        return Err(IdentityGenericCallInvariant::InvalidTypeParameter(type_parameter).into());
    };
    let symbol = record
        .symbol()
        .ok_or(IdentityGenericCallInvariant::InvalidTypeParameter(
            type_parameter,
        ))?;
    let symbol_record =
        store
            .symbol(symbol)
            .ok_or(IdentityGenericCallInvariant::InvalidTypeParameter(
                type_parameter,
            ))?;
    let computed_type_variable_flags = ObjectFlags::COULD_CONTAIN_TYPE_VARIABLES_COMPUTED
        | ObjectFlags::COULD_CONTAIN_TYPE_VARIABLES;
    if record.flags() != TypeFlags::TYPE_PARAMETER
        || (record.object_flags() != ObjectFlags::NONE
            && record.object_flags() != computed_type_variable_flags)
        || record.alias().is_some()
        || symbol_record.flags() != SymbolFlags::TYPE_PARAMETER
        || symbol_record.check_flags() != CheckFlags::NONE
        || store.get_merged_symbol(symbol) != Some(symbol)
        || cached_ordinary_type_parameter_owner(store, type_parameter) != Some(symbol)
        || data.is_this_type
    {
        return Err(IdentityGenericCallInvariant::InvalidTypeParameter(type_parameter).into());
    }
    if data.target.is_some() || data.mapper.is_some() {
        return Err(
            IdentityGenericCallUnsupported::InstantiatedTypeParameter(type_parameter).into(),
        );
    }
    let no_constraint = store
        .intrinsic_bootstrap()
        .map(|bootstrap| bootstrap.no_constraint_type)
        .ok_or(IdentityGenericCallInvariant::InvalidTypeParameter(
            type_parameter,
        ))?;
    match data.constraint {
        // The exact callable provider has already proved that the source
        // declaration has no constraint. A cold cache is therefore valid, but
        // only for the canonical declared type-parameter identity proved
        // above. This must not admit an arbitrary synthetic TypeParameter.
        None if cache_provenance
            == IdentityTypeParameterCacheProvenance::ExactDefaultFreeSource => {}
        None => {
            return Err(
                IdentityGenericCallUnsupported::UnresolvedTypeParameterConstraint(type_parameter)
                    .into(),
            );
        }
        Some(constraint) if constraint != no_constraint => {
            return Err(
                IdentityGenericCallUnsupported::ConstrainedTypeParameter(type_parameter).into(),
            );
        }
        Some(_) => {}
    }
    if data
        .constrained
        .resolved_base_constraint
        .is_some_and(|base| base != no_constraint)
    {
        return Err(IdentityGenericCallInvariant::InvalidTypeParameter(type_parameter).into());
    }
    match data.resolved_default_type {
        // As with the constraint, absence is the untouched cache state for an
        // exact default-free declaration, not evidence of a default.
        None if cache_provenance
            == IdentityTypeParameterCacheProvenance::ExactDefaultFreeSource =>
        {
            Ok(())
        }
        None => Err(
            IdentityGenericCallUnsupported::UnresolvedTypeParameterDefault(type_parameter).into(),
        ),
        Some(default) if default != no_constraint => {
            Err(IdentityGenericCallUnsupported::DefaultedTypeParameter(type_parameter).into())
        }
        Some(_) => Ok(()),
    }
}

fn get_or_create_identity_instantiation(
    store: &mut CanonicalTypeMapperStore,
    shape: IdentitySignatureShape,
    type_argument: TypeId,
    cached: Option<(SignatureId, TypeMapperId)>,
) -> Result<(SignatureId, TypeMapperId, TypeId, TypeId), IdentityGenericCallError> {
    if let Some((signature, mapper)) = cached {
        return Ok((signature, mapper, type_argument, type_argument));
    }

    let exact_type_arguments: Box<[TypeId]> = Box::new([type_argument]);
    let type_arguments_key = type_list_key(&exact_type_arguments);
    let (mut parameter_data, name_type) = {
        let parameter = store.symbol(shape.parameter_symbol).ok_or(
            IdentityGenericCallInvariant::InvalidParameterSymbol(shape.parameter_symbol),
        )?;
        let mut data = SymbolData::new(
            parameter.flags() | SymbolFlags::TRANSIENT,
            parameter.name().to_owned(),
        );
        data.check_flags = CheckFlags::INSTANTIATED;
        data.declarations = parameter.declarations().map(<[_]>::to_vec);
        data.value_declaration = parameter.value_declaration();
        data.parent = parameter.parent();
        let name_type = store
            .value_symbol_links(shape.parameter_symbol)
            .and_then(|links| links.name_type);
        (data, name_type)
    };
    let (signature_flags, declaration, min_argument_count) = {
        let original = store.signature(shape.signature).ok_or(
            IdentityGenericCallInvariant::InvalidSignature(shape.signature),
        )?;
        (
            original.flags() & SignatureFlags::PROPAGATING_FLAGS,
            original.declaration(),
            original.min_argument_count(),
        )
    };
    parameter_data.members = None;
    parameter_data.exports = None;
    parameter_data.export_symbol = None;
    let mut instantiated_parameters = Vec::with_capacity(1);

    if !store.try_reserve_mappers(1)
        || !store.try_reserve_checker_symbol_allocations(1, 0)
        || !store.try_reserve_value_symbol_links(1)
        || !store.try_reserve_signatures(1)
        || !store.try_reserve_cached_signatures(1)
    {
        return Err(IdentityGenericCallInvariant::Capacity(shape.signature).into());
    }

    // Every validation and fallible reservation precedes this point. The
    // remaining writes form one dependency-ordered publication suffix, with
    // the authoritative cachedSignatures entry committed last.
    let mapper = store
        .new_simple_type_mapper(shape.type_parameter, type_argument)
        .expect("preflighted simple mapper endpoints belong to the store");
    assert_eq!(
        store.simple_type_mapper_endpoints(mapper),
        Some((shape.type_parameter, type_argument)),
        "newSimpleTypeMapper must preserve its exact endpoints"
    );
    let instantiated_parameter = store
        .alloc_symbol(parameter_data)
        .expect("reserved transient parameter allocation must succeed");
    instantiated_parameters.push(instantiated_parameter);
    assert!(store.set_value_symbol_links(
        instantiated_parameter,
        ValueSymbolLinks {
            resolved_type: Some(type_argument),
            target: Some(shape.parameter_symbol),
            mapper: Some(mapper),
            name_type,
            ..ValueSymbolLinks::default()
        },
    ));
    let signature = store
        .alloc_signature(
            signature_flags,
            declaration,
            Vec::new(),
            None,
            instantiated_parameters,
            Some(type_argument),
            None,
            min_argument_count,
        )
        .expect("reserved instantiated signature allocation must succeed");
    assert!(store.set_signature_target_and_mapper(signature, Some(shape.signature), Some(mapper)));
    assert_eq!(
        valid_cached_identity_instantiation(
            store,
            shape,
            type_argument,
            store
                .signature(shape.signature)
                .expect("validated generic signature must remain present"),
            store
                .signature(signature)
                .expect("published instantiated signature must remain present"),
        ),
        Some(mapper),
        "the publication suffix must build an exact cache entry"
    );
    assert!(store.set_cached_signature(
        shape.signature,
        type_arguments_key,
        exact_type_arguments,
        signature
    ));
    Ok((signature, mapper, type_argument, type_argument))
}

fn cached_identity_instantiation(
    store: &CanonicalTypeMapperStore,
    shape: IdentitySignatureShape,
    type_argument: TypeId,
) -> Result<Option<(SignatureId, TypeMapperId)>, IdentityGenericCallError> {
    let original =
        store
            .signature(shape.signature)
            .ok_or(IdentityGenericCallInvariant::InvalidSignature(
                shape.signature,
            ))?;
    let type_arguments_key = type_list_key(&[type_argument]);
    let cached = match store.cached_signature(shape.signature, type_arguments_key, &[type_argument])
    {
        CachedSignatureLookup::Missing => return Ok(None),
        CachedSignatureLookup::Hit(signature) => signature,
        CachedSignatureLookup::HashCollision(cached) => {
            return Err(
                IdentityGenericCallInvariant::InstantiationCacheHashCollision {
                    target: shape.signature,
                    type_argument,
                    cached,
                }
                .into(),
            );
        }
        CachedSignatureLookup::Invalid => {
            return Err(IdentityGenericCallInvariant::InvalidSignature(shape.signature).into());
        }
    };
    let signature = store.signature(cached).ok_or(
        IdentityGenericCallInvariant::InvalidCachedInstantiation {
            target: shape.signature,
            type_argument,
            signature: cached,
        },
    )?;
    let mapper =
        valid_cached_identity_instantiation(store, shape, type_argument, original, signature)
            .ok_or(IdentityGenericCallInvariant::InvalidCachedInstantiation {
                target: shape.signature,
                type_argument,
                signature: cached,
            })?;
    Ok(Some((cached, mapper)))
}

fn valid_cached_identity_instantiation(
    store: &CanonicalTypeMapperStore,
    shape: IdentitySignatureShape,
    type_argument: TypeId,
    original: &super::signatures::Signature,
    signature: &super::signatures::Signature,
) -> Option<TypeMapperId> {
    let mapper = signature.mapper()?;
    let [parameter] = signature.parameters() else {
        return None;
    };
    if signature.flags() != original.flags() & SignatureFlags::PROPAGATING_FLAGS
        || signature.declaration() != original.declaration()
        || !signature.type_parameters().is_empty()
        || signature.this_parameter().is_some()
        || signature.resolved_return_type() != Some(type_argument)
        || signature.resolved_type_predicate().is_some()
        || signature.min_argument_count() != original.min_argument_count()
        || signature.resolved_min_argument_count() != -1
        || signature.target() != Some(shape.signature)
        || store.simple_type_mapper_endpoints(mapper) != Some((shape.type_parameter, type_argument))
        || signature.isolated_signature_type().is_some()
        || signature.composite().is_some()
        || !cached_instantiated_parameter(
            store,
            *parameter,
            shape.parameter_symbol,
            mapper,
            type_argument,
        )
    {
        return None;
    }
    Some(mapper)
}

fn cached_instantiated_parameter(
    store: &CanonicalTypeMapperStore,
    parameter: SemanticSymbolId,
    target: SemanticSymbolId,
    mapper: TypeMapperId,
    type_argument: TypeId,
) -> bool {
    let Some(record) = store.symbol(parameter) else {
        return false;
    };
    let Some(target_record) = store.symbol(target) else {
        return false;
    };
    let name_type = store
        .value_symbol_links(target)
        .and_then(|links| links.name_type);
    record.flags() == target_record.flags() | SymbolFlags::TRANSIENT
        && record.check_flags() == CheckFlags::INSTANTIATED
        && record.name() == target_record.name()
        && record.declarations() == target_record.declarations()
        && record.value_declaration() == target_record.value_declaration()
        && record.parent() == target_record.parent()
        && record.members().is_none()
        && record.exports().is_none()
        && record.export_symbol().is_none()
        && store.get_merged_symbol(parameter) == Some(parameter)
        && store.value_symbol_links(parameter)
            == Some(&ValueSymbolLinks {
                resolved_type: Some(type_argument),
                target: Some(target),
                mapper: Some(mapper),
                name_type,
                ..ValueSymbolLinks::default()
            })
}

fn check_identity_argument_applicability(
    argument_type: TypeId,
    parameter_type: TypeId,
    mut is_assignable: impl FnMut(TypeId, TypeId) -> Result<bool, RelationUnavailable>,
) -> Result<DirectCallApplicability, RelationUnavailable> {
    if is_assignable(argument_type, parameter_type)? {
        Ok(DirectCallApplicability::Applicable)
    } else {
        Ok(DirectCallApplicability::ArgumentNotAssignable {
            index: 0,
            argument_type,
            parameter_type,
        })
    }
}

#[cfg(test)]
mod tests {
    use ts_binder::{EscapedName, SymbolData};
    use ts_jsnum::Number;

    use super::*;
    use crate::semantic::{
        DeclaredTypeLinks, IntrinsicBootstrapOptions, SemanticStore, mapper::TypeMapper,
        type_records::TypeRecord, types::ObjectFlags,
    };

    const EXACT_SOURCE: IdentityTypeParameterCacheProvenance =
        IdentityTypeParameterCacheProvenance::ExactDefaultFreeSource;

    fn initialized_store() -> CanonicalTypeMapperStore {
        let mut store = SemanticStore::<TypeRecord, TypeMapper>::new();
        store
            .initialize_intrinsic_bootstrap(IntrinsicBootstrapOptions::default())
            .unwrap();
        store
    }

    fn identity_callable(
        store: &mut CanonicalTypeMapperStore,
    ) -> (ValidatedSingleCallable, TypeId) {
        let type_parameter_symbol = store
            .alloc_symbol(SymbolData::new(
                SymbolFlags::TYPE_PARAMETER,
                EscapedName::source("T"),
            ))
            .unwrap();
        let type_parameter = store
            .alloc_type_parameter(Some(type_parameter_symbol))
            .unwrap();
        assert!(store.set_declared_type_links(
            type_parameter_symbol,
            DeclaredTypeLinks {
                declared_type: Some(type_parameter),
                ..DeclaredTypeLinks::default()
            },
        ));
        let parameter = store
            .alloc_symbol(SymbolData::new(
                SymbolFlags::FUNCTION_SCOPED_VARIABLE,
                EscapedName::source("value"),
            ))
            .unwrap();
        assert!(store.set_value_symbol_links(
            parameter,
            ValueSymbolLinks {
                resolved_type: Some(type_parameter),
                ..ValueSymbolLinks::default()
            },
        ));
        let signature = store
            .alloc_signature(
                SignatureFlags::NONE,
                None,
                vec![type_parameter],
                None,
                vec![parameter],
                Some(type_parameter),
                None,
                1,
            )
            .unwrap();
        let owner = store.intrinsic_bootstrap().unwrap().any_function_type;
        (
            ValidatedSingleCallable {
                owner,
                signature,
                parameters: vec![type_parameter],
                min_argument_count: 1,
                return_type: Some(type_parameter),
                strict_variance_exempt: false,
            },
            type_parameter,
        )
    }

    fn inferred_request(callee: TypeId, arguments: &[TypeId]) -> IdentityGenericCallRequest<'_> {
        IdentityGenericCallRequest {
            form: DirectCallForm::Call,
            optional_chain: false,
            explicit_type_arguments: None,
            has_spread_argument: false,
            callee,
            arguments,
        }
    }

    #[test]
    fn inferred_identity_preserves_string_number_and_boolean_literals() {
        // Pinned oracle declaration emit:
        // identity("x") -> "x", identity(1) -> 1, identity(true) -> true.
        let mut store = initialized_store();
        let (callable, type_parameter) = identity_callable(&mut store);
        let regular_string = store.regular_string_literal_type("x".into()).unwrap();
        let string = store.fresh_type_of_literal_type(regular_string).unwrap();
        let regular_number = store.regular_number_literal_type(Number::new(1.0)).unwrap();
        let number = store.fresh_type_of_literal_type(regular_number).unwrap();
        let regular_true = store.intrinsic_bootstrap().unwrap().regular_true_type;
        let true_ = store.fresh_type_of_literal_type(regular_true).unwrap();

        for candidate in [string, number, true_] {
            let resolution = project_validated_identity_call(
                &mut store,
                inferred_request(callable.owner, &[candidate]),
                &callable,
                EXACT_SOURCE,
            )
            .unwrap();
            assert_eq!(resolution.projection.type_parameter, type_parameter);
            assert_eq!(resolution.projection.type_argument, candidate);
            assert_eq!(resolution.projection.return_type, candidate);
            assert_eq!(
                resolution.projection.argument_target.parameter_type,
                candidate
            );
            assert_eq!(
                check_identity_argument_applicability(candidate, candidate, |source, target| {
                    Ok(source == target)
                }),
                Ok(DirectCallApplicability::Applicable)
            );
        }
    }

    #[test]
    fn explicit_primitive_argument_controls_return_and_applicability() {
        // Pinned oracle declaration emit: identity<string>("x") -> string.
        let mut store = initialized_store();
        let (callable, _) = identity_callable(&mut store);
        let bootstrap = store.intrinsic_bootstrap().unwrap();
        let string = bootstrap.string_type;
        let number = bootstrap.number_type;
        let resolution = project_validated_identity_call(
            &mut store,
            IdentityGenericCallRequest {
                explicit_type_arguments: Some(&[string]),
                ..inferred_request(callable.owner, &[number])
            },
            &callable,
            EXACT_SOURCE,
        )
        .unwrap();

        assert_eq!(resolution.projection.type_argument, string);
        assert_eq!(resolution.projection.return_type, string);
        assert_eq!(
            check_identity_argument_applicability(number, string, |source, target| {
                Ok(source == target)
            }),
            Ok(DirectCallApplicability::ArgumentNotAssignable {
                index: 0,
                argument_type: number,
                parameter_type: string,
            })
        );
    }

    #[test]
    fn instantiated_signature_is_cached_by_target_and_type_argument() {
        let mut store = initialized_store();
        let (callable, _) = identity_callable(&mut store);
        let string = store.intrinsic_bootstrap().unwrap().string_type;
        let arguments = [string];
        let first = project_validated_identity_call(
            &mut store,
            inferred_request(callable.owner, &arguments),
            &callable,
            EXACT_SOURCE,
        )
        .unwrap();
        let counts = (
            store.signature_len(),
            store.mapper_len(),
            store.symbol_len(),
        );
        let second = project_validated_identity_call(
            &mut store,
            inferred_request(callable.owner, &arguments),
            &callable,
            EXACT_SOURCE,
        )
        .unwrap();

        assert_eq!(second.projection.signature, first.projection.signature);
        assert_eq!(second.projection.mapper, first.projection.mapper);
        assert_eq!(
            (
                store.signature_len(),
                store.mapper_len(),
                store.symbol_len()
            ),
            counts
        );
    }

    #[test]
    fn cached_instantiation_requires_exact_simple_mapper_endpoints() {
        let mut store = initialized_store();
        let (callable, _) = identity_callable(&mut store);
        let bootstrap = store.intrinsic_bootstrap().unwrap();
        let string = bootstrap.string_type;
        let number = bootstrap.number_type;
        let first = project_validated_identity_call(
            &mut store,
            inferred_request(callable.owner, &[string]),
            &callable,
            EXACT_SOURCE,
        )
        .unwrap();
        let wrong_mapper = store.new_simple_type_mapper(number, string).unwrap();
        assert_eq!(
            store.simple_type_mapper_endpoints(wrong_mapper),
            Some((number, string))
        );
        assert!(store.set_signature_target_and_mapper(
            first.projection.signature,
            Some(first.projection.generic_signature),
            Some(wrong_mapper)
        ));
        let counts = (
            store.mapper_len(),
            store.symbol_len(),
            store.signature_len(),
            store.cached_signature_len(),
        );

        assert_eq!(
            project_validated_identity_call(
                &mut store,
                inferred_request(callable.owner, &[string]),
                &callable,
                EXACT_SOURCE,
            ),
            Err(IdentityGenericCallError::Invariant(
                IdentityGenericCallInvariant::InvalidCachedInstantiation {
                    target: first.projection.generic_signature,
                    type_argument: string,
                    signature: first.projection.signature,
                }
            ))
        );
        assert_eq!(
            (
                store.mapper_len(),
                store.symbol_len(),
                store.signature_len(),
                store.cached_signature_len(),
            ),
            counts
        );

        assert!(store.set_signature_target_and_mapper(
            first.projection.signature,
            Some(first.projection.generic_signature),
            Some(first.projection.mapper)
        ));
        let repaired = project_validated_identity_call(
            &mut store,
            inferred_request(callable.owner, &[string]),
            &callable,
            EXACT_SOURCE,
        )
        .unwrap();
        assert_eq!(repaired.projection.signature, first.projection.signature);
        assert_eq!(repaired.projection.mapper, first.projection.mapper);
    }

    #[test]
    fn cold_parameter_caches_require_exact_provenance_and_accept_computed_state() {
        let mut store = initialized_store();
        let (callable, type_parameter) = identity_callable(&mut store);
        let string = store.intrinsic_bootstrap().unwrap().string_type;
        let record = store.type_payload(type_parameter).unwrap();
        let TypeData::TypeParameter(data) = record.data() else {
            panic!("expected type parameter")
        };
        let symbol = record.symbol().unwrap();
        assert_eq!(data.constraint, None);
        assert_eq!(data.resolved_default_type, None);
        assert_eq!(
            cached_ordinary_type_parameter_owner(&store, type_parameter),
            Some(symbol)
        );
        assert_eq!(
            project_validated_identity_call(
                &mut store,
                inferred_request(callable.owner, &[string]),
                &callable,
                IdentityTypeParameterCacheProvenance::RequireResolvedCaches,
            ),
            Err(IdentityGenericCallError::Unsupported(
                IdentityGenericCallUnsupported::UnresolvedTypeParameterConstraint(type_parameter)
            ))
        );

        let computed = ObjectFlags::COULD_CONTAIN_TYPE_VARIABLES_COMPUTED
            | ObjectFlags::COULD_CONTAIN_TYPE_VARIABLES;
        assert!(store.set_type_object_flags(type_parameter, computed));
        let resolution = project_validated_identity_call(
            &mut store,
            inferred_request(callable.owner, &[string]),
            &callable,
            EXACT_SOURCE,
        )
        .unwrap();
        assert_eq!(resolution.projection.type_argument, string);

        assert!(store.set_type_object_flags(
            type_parameter,
            ObjectFlags::COULD_CONTAIN_TYPE_VARIABLES_COMPUTED
        ));
        assert_eq!(
            project_validated_identity_call(
                &mut store,
                inferred_request(callable.owner, &[string]),
                &callable,
                EXACT_SOURCE,
            ),
            Err(IdentityGenericCallError::Invariant(
                IdentityGenericCallInvariant::InvalidTypeParameter(type_parameter)
            ))
        );
        assert!(store.set_type_object_flags(type_parameter, computed));
        assert!(store.set_declared_type_links(symbol, DeclaredTypeLinks::default()));
        assert_eq!(
            project_validated_identity_call(
                &mut store,
                inferred_request(callable.owner, &[string]),
                &callable,
                EXACT_SOURCE,
            ),
            Err(IdentityGenericCallError::Invariant(
                IdentityGenericCallInvariant::InvalidTypeParameter(type_parameter)
            ))
        );
    }

    #[test]
    fn source_parameter_warm_base_constraint_accepts_both_cache_orders() {
        for base_constraint_first in [false, true] {
            let mut store = initialized_store();
            let (callable, type_parameter) = identity_callable(&mut store);
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            let no_constraint = bootstrap.no_constraint_type;
            let string = bootstrap.string_type;

            if base_constraint_first {
                assert!(store.set_resolved_base_constraint(type_parameter, Some(no_constraint)));
            }
            assert!(store.set_type_parameter_resolution(
                type_parameter,
                Some(no_constraint),
                None,
                None,
                Some(no_constraint),
            ));
            if !base_constraint_first {
                assert!(store.set_resolved_base_constraint(type_parameter, Some(no_constraint)));
            }

            let resolution = project_validated_identity_call(
                &mut store,
                inferred_request(callable.owner, &[string]),
                &callable,
                EXACT_SOURCE,
            )
            .unwrap();
            assert_eq!(resolution.projection.type_argument, string);
        }
    }

    #[test]
    fn poisoned_base_constraint_is_an_invariant() {
        let mut store = initialized_store();
        let (callable, type_parameter) = identity_callable(&mut store);
        let string = store.intrinsic_bootstrap().unwrap().string_type;
        assert!(store.set_resolved_base_constraint(type_parameter, Some(string)));

        assert_eq!(
            project_validated_identity_call(
                &mut store,
                inferred_request(callable.owner, &[string]),
                &callable,
                EXACT_SOURCE,
            ),
            Err(IdentityGenericCallError::Invariant(
                IdentityGenericCallInvariant::InvalidTypeParameter(type_parameter)
            ))
        );
    }

    #[test]
    fn malformed_inference_leaf_is_atomic_and_repairable() {
        let mut store = initialized_store();
        let (callable, _) = identity_callable(&mut store);
        let regular = store.regular_string_literal_type("x".into()).unwrap();
        let fresh = store.fresh_type_of_literal_type(regular).unwrap();
        assert!(store.set_literal_links(fresh, None, regular));
        let counts = (
            store.mapper_len(),
            store.symbol_len(),
            store.signature_len(),
            store.cached_signature_len(),
        );

        assert_eq!(
            project_validated_identity_call(
                &mut store,
                inferred_request(callable.owner, &[fresh]),
                &callable,
                EXACT_SOURCE,
            ),
            Err(IdentityGenericCallError::Inference(
                NakedTypeInferenceError::InvalidCanonicalCandidate {
                    candidate: fresh,
                    error: super::super::bootstrap::LiteralTypeCacheError::InvalidCachedLiteral(
                        fresh
                    ),
                }
            ))
        );
        assert_eq!(
            (
                store.mapper_len(),
                store.symbol_len(),
                store.signature_len(),
                store.cached_signature_len(),
            ),
            counts
        );

        assert!(store.set_literal_links(fresh, Some(fresh), regular));
        let repaired = project_validated_identity_call(
            &mut store,
            inferred_request(callable.owner, &[fresh]),
            &callable,
            EXACT_SOURCE,
        )
        .unwrap();
        assert_eq!(repaired.projection.type_argument, fresh);
        assert_eq!(store.cached_signature_len(), counts.3 + 1);
    }

    #[test]
    fn relation_unavailable_precedes_cold_instantiation_publication() {
        let mut store = initialized_store();
        let (callable, _) = identity_callable(&mut store);
        let string = store.intrinsic_bootstrap().unwrap().string_type;
        let counts = (
            store.mapper_len(),
            store.symbol_len(),
            store.signature_len(),
            store.cached_signature_len(),
            store.checker_link_allocated_lengths(),
        );

        assert_eq!(
            resolve_validated_identity_call(
                &mut store,
                inferred_request(callable.owner, &[string]),
                &callable,
                EXACT_SOURCE,
                |_, _, _| Err(RelationUnavailable::MissingBootstrap),
            ),
            Err(IdentityGenericCallError::Relation(
                RelationUnavailable::MissingBootstrap
            ))
        );
        assert_eq!(
            (
                store.mapper_len(),
                store.symbol_len(),
                store.signature_len(),
                store.cached_signature_len(),
                store.checker_link_allocated_lengths(),
            ),
            counts
        );

        let repaired = project_validated_identity_call(
            &mut store,
            inferred_request(callable.owner, &[string]),
            &callable,
            EXACT_SOURCE,
        )
        .unwrap();
        assert_eq!(repaired.projection.type_argument, string);
        assert_eq!(store.cached_signature_len(), counts.3 + 1);
    }

    #[test]
    fn cached_instantiation_rejects_redirected_transient_parameter() {
        let mut store = initialized_store();
        let (callable, _) = identity_callable(&mut store);
        let string = store.intrinsic_bootstrap().unwrap().string_type;
        let first = project_validated_identity_call(
            &mut store,
            inferred_request(callable.owner, &[string]),
            &callable,
            EXACT_SOURCE,
        )
        .unwrap();
        let [parameter] = store
            .signature(first.projection.signature)
            .unwrap()
            .parameters()
        else {
            panic!("expected one instantiated parameter")
        };
        let target = store
            .value_symbol_links(*parameter)
            .and_then(|links| links.target)
            .unwrap();
        assert_eq!(store.record_merged_symbol(target, *parameter), Ok(None));
        let counts = (
            store.mapper_len(),
            store.symbol_len(),
            store.signature_len(),
            store.cached_signature_len(),
            store.merged_symbol_len(),
            store.checker_link_allocated_lengths(),
        );

        assert_eq!(
            project_validated_identity_call(
                &mut store,
                inferred_request(callable.owner, &[string]),
                &callable,
                EXACT_SOURCE,
            ),
            Err(IdentityGenericCallError::Invariant(
                IdentityGenericCallInvariant::InvalidCachedInstantiation {
                    target: first.projection.generic_signature,
                    type_argument: string,
                    signature: first.projection.signature,
                }
            ))
        );
        assert_eq!(
            (
                store.mapper_len(),
                store.symbol_len(),
                store.signature_len(),
                store.cached_signature_len(),
                store.merged_symbol_len(),
                store.checker_link_allocated_lengths(),
            ),
            counts
        );
    }

    #[test]
    fn explicit_arity_constraints_defaults_and_non_identity_shapes_reject() {
        let mut store = initialized_store();
        let (callable, type_parameter) = identity_callable(&mut store);
        let bootstrap = store.intrinsic_bootstrap().unwrap();
        let string = bootstrap.string_type;
        let number = bootstrap.number_type;
        let no_constraint = bootstrap.no_constraint_type;
        assert_eq!(
            project_validated_identity_call(
                &mut store,
                IdentityGenericCallRequest {
                    explicit_type_arguments: Some(&[string, number]),
                    ..inferred_request(callable.owner, &[string])
                },
                &callable,
                EXACT_SOURCE,
            ),
            Err(IdentityGenericCallError::Unsupported(
                IdentityGenericCallUnsupported::TypeArgumentArity {
                    expected: 1,
                    actual: 2,
                }
            ))
        );

        assert!(store.set_type_parameter_resolution(
            type_parameter,
            Some(string),
            None,
            None,
            Some(no_constraint),
        ));
        assert_eq!(
            project_validated_identity_call(
                &mut store,
                inferred_request(callable.owner, &[string]),
                &callable,
                EXACT_SOURCE,
            ),
            Err(IdentityGenericCallError::Unsupported(
                IdentityGenericCallUnsupported::ConstrainedTypeParameter(type_parameter)
            ))
        );

        assert!(store.set_type_parameter_resolution(
            type_parameter,
            Some(no_constraint),
            None,
            None,
            Some(string),
        ));
        assert_eq!(
            project_validated_identity_call(
                &mut store,
                inferred_request(callable.owner, &[string]),
                &callable,
                EXACT_SOURCE,
            ),
            Err(IdentityGenericCallError::Unsupported(
                IdentityGenericCallUnsupported::DefaultedTypeParameter(type_parameter)
            ))
        );

        assert!(store.set_type_parameter_resolution(
            type_parameter,
            Some(no_constraint),
            None,
            None,
            Some(no_constraint),
        ));
        let mut non_identity = callable.clone();
        non_identity.return_type = Some(number);
        assert_eq!(
            project_validated_identity_call(
                &mut store,
                inferred_request(callable.owner, &[string]),
                &non_identity,
                EXACT_SOURCE,
            ),
            Err(IdentityGenericCallError::Unsupported(
                IdentityGenericCallUnsupported::NonNakedReturn(callable.signature)
            ))
        );
    }
}
