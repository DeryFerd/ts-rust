//! Exact semantic kernels for bounded generic direct-call verticals.
//!
//! The full-vector branch admits one stored signature with ordered type
//! parameters, fixed or optional parameters whose targets are naked type
//! parameters, canonical nested Array/interface references, or authenticated
//! fixed primitives and callbacks, homogeneous Array rest parameters, and a
//! mapper-supported return. It owns
//! declaration-order
//! inference/default/constraint finalization, overload-failure projection, and
//! exact checked-instantiation cache publication. Recovery signatures remain a
//! separate call-node concern and never enter the global signature cache. The
//! original exact `<T>(value: T): T` entry points remain available for
//! compatibility with the installed identity-call source path, but now share
//! the same lazy shell, demand, recovery, and cache protocol.

#![allow(dead_code)] // Installed ahead of the source-call dispatch consumer.

use ts_ast::{NodeRef, SyntaxKind};
use ts_binder::{CheckFlags, SymbolData, SymbolFlags};

use super::{
    CanonicalGlobalTypes, CanonicalTypeMapperStore, DeclaredTypeHost, RelationUnavailable,
    SemanticSymbolId, SignatureId, TypeId, TypeMapperId, ValueSymbolLinks,
    array_types::{ArrayTypeError, CanonicalArrayTargets},
    callables::{
        StoredSingleCallableValidation, ValidatedSingleCallable, validate_stored_single_callable,
    },
    calls::{
        DirectCallApplicability, DirectCallArgumentTarget, DirectCallForm, DirectCallReturnKind,
    },
    declared::{cached_ordinary_type_parameter_owner, type_list_key},
    inference::{
        InferenceLiteralTreatment, NakedTypeCandidateError, NakedTypeInferenceError,
        infer_naked_type_parameter, infer_naked_type_parameter_candidates,
        infer_naked_type_parameter_candidates_with_array_targets,
        infer_naked_type_parameter_variance_candidates, is_non_inferrable_inference_source,
        validate_inference_leaf, validate_inference_leaf_with_array_targets,
    },
    instantiate::{
        InstantiationError, InstantiationLimits, InstantiationSession, canonical_anonymous_union,
        instantiate_type_with_session, instantiate_type_with_vector_and_session,
    },
    keyof_types::{cached_nongeneric_keyof_type, plan_nongeneric_keyof_type},
    reference_types::{DirectGenericReference, validate_direct_generic_reference},
    signatures::{IndexFlags, SignatureFlags},
    source_callables::{
        StoredSourceCallableValidation, valid_fixed_generic_source_parameter_type,
        validate_stored_source_callable,
    },
    store::CachedSignatureLookup,
    type_records::TypeData,
    types::{ObjectFlags, TypeFlags, VarianceFlags},
};

/// Syntax-neutral input for the declaration-order generic-call kernel.
///
/// `Some` preserves the distinction between explicit syntax and inference.
/// An empty explicit list is normalized back to inference because the source
/// grammar consumer owns TS1099 while overload resolution observes zero type
/// arguments.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct GenericCallVectorRequest<'a> {
    pub(super) form: DirectCallForm,
    pub(super) optional_chain: bool,
    pub(super) explicit_type_arguments: Option<&'a [TypeId]>,
    pub(super) has_spread_argument: bool,
    pub(super) callee: TypeId,
    pub(super) arguments: &'a [TypeId],
}

/// Valid semantics intentionally outside this first full-vector cut.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum GenericCallVectorUnsupported {
    Form(DirectCallForm),
    OptionalChain,
    SpreadArgument,
    NotExactSingleCallable(TypeId),
    PendingCallable(TypeId),
    SignatureTypeParameterCount(SignatureId),
    SignatureFlags(SignatureId),
    ExplicitThisParameter(SignatureId),
    RestSignature(SignatureId),
    NonRequiredParameter(SignatureId),
    NonNakedParameter {
        signature: SignatureId,
        index: usize,
        type_: TypeId,
    },
    ContextualSignature(SignatureId),
    UnresolvedReturnType(SignatureId),
    InstantiationType {
        signature: SignatureId,
        type_: TypeId,
    },
    TypeParameterDependency {
        type_parameter: TypeId,
        dependency: TypeId,
    },
}

/// Malformed stored callable state or foreign semantic identities.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum GenericCallVectorInvariant {
    InvalidCalleeType(TypeId),
    MalformedCallable(TypeId),
    CallableOwnerMismatch {
        callee: TypeId,
        owner: TypeId,
    },
    InvalidSignature(SignatureId),
    CallableSignatureMismatch(SignatureId),
    InvalidTypeParameter(TypeId),
    DuplicateTypeParameter(TypeId),
    InvalidParameterSymbol {
        signature: SignatureId,
        index: usize,
        symbol: SemanticSymbolId,
    },
    InvalidArgumentType {
        index: usize,
        type_: TypeId,
    },
    InvalidTypeArgument {
        index: usize,
        type_: TypeId,
    },
    InvalidCheckedInstantiation(SignatureId),
    InvalidCachedInstantiation {
        target: SignatureId,
        signature: SignatureId,
    },
    MissingCachedInstantiation(SignatureId),
    InvalidCallInstantiation {
        target: SignatureId,
        signature: SignatureId,
    },
    InstantiationCacheHashCollision {
        target: SignatureId,
        cached: SignatureId,
    },
    Capacity(SignatureId),
    MissingBootstrap,
    InvalidArrayType {
        signature: SignatureId,
        type_: TypeId,
        error: ArrayTypeError,
    },
    InvalidUnionParameter {
        signature: SignatureId,
        type_: TypeId,
    },
    InvalidInterfaceReference {
        signature: SignatureId,
        type_: TypeId,
    },
    InvalidInterfaceVariance {
        signature: SignatureId,
        type_: TypeId,
    },
}

/// Capability, inference, instantiation, or relation failure. Ordinary call
/// diagnostics are represented by [`GenericCallVectorApplicability`].
#[derive(Debug, PartialEq)]
pub(super) enum GenericCallVectorError {
    Unsupported(GenericCallVectorUnsupported),
    Invariant(GenericCallVectorInvariant),
    Inference(NakedTypeCandidateError),
    Instantiation(InstantiationError),
    Relation(RelationUnavailable),
}

impl From<GenericCallVectorUnsupported> for GenericCallVectorError {
    fn from(error: GenericCallVectorUnsupported) -> Self {
        Self::Unsupported(error)
    }
}

impl From<GenericCallVectorInvariant> for GenericCallVectorError {
    fn from(error: GenericCallVectorInvariant) -> Self {
        Self::Invariant(error)
    }
}

impl From<NakedTypeCandidateError> for GenericCallVectorError {
    fn from(error: NakedTypeCandidateError) -> Self {
        Self::Inference(error)
    }
}

impl From<InstantiationError> for GenericCallVectorError {
    fn from(error: InstantiationError) -> Self {
        Self::Instantiation(error)
    }
}

impl From<RelationUnavailable> for GenericCallVectorError {
    fn from(error: RelationUnavailable) -> Self {
        Self::Relation(error)
    }
}

/// One exact mapper-backed instantiated-signature shell.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct GenericCallVectorInstantiation {
    pub(super) type_arguments: Vec<TypeId>,
    pub(super) signature: SignatureId,
    pub(super) mapper: TypeMapperId,
}

/// Final selected signature view. On an erroneous sole-candidate call this is
/// the exact overload-failure recovery projection exposed by TypeScript-Go.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct GenericCallVectorProjection {
    pub(super) callee: TypeId,
    pub(super) generic_signature: SignatureId,
    pub(super) type_parameters: Vec<TypeId>,
    pub(super) instantiation: GenericCallVectorInstantiation,
    pub(super) recovery: bool,
}

/// Single diagnostic class produced by the bounded one-candidate resolver.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum GenericCallVectorApplicability {
    Applicable,
    TypeArgumentArity {
        minimum: usize,
        maximum: usize,
        actual: usize,
    },
    TooFewArguments {
        expected: usize,
        actual: usize,
    },
    TooManyArguments {
        expected: usize,
        actual: usize,
    },
    ExplicitTypeArgumentConstraint {
        index: usize,
        type_argument: TypeId,
        constraint: TypeId,
    },
    ArgumentNotAssignable {
        index: usize,
        argument_type: TypeId,
        parameter_type: TypeId,
    },
}

impl GenericCallVectorApplicability {
    /// Stable TypeScript diagnostic category for source-dispatch integration.
    pub(super) const fn diagnostic_code(self) -> Option<u32> {
        match self {
            Self::Applicable => None,
            Self::TypeArgumentArity { .. } => Some(2558),
            Self::TooFewArguments { .. } | Self::TooManyArguments { .. } => Some(2554),
            Self::ExplicitTypeArgumentConstraint { .. } => Some(2344),
            Self::ArgumentNotAssignable { .. } => Some(2345),
        }
    }
}

/// Complete resolver result, including any checked/recovery shells published
/// in pinned overload-resolution order.
///
/// `checked_instantiation` retains the normal inference/default vector used by
/// checked applicability and TS2345. Arity and TS2344 failures never create
/// one. `projection` may instead contain the raw overload-failure vector used
/// for the call expression's final return type.
/// Fields are private so sibling consumers receive an immutable resolver-minted
/// capability; cache publication never needs to recompute and potentially
/// intern a forged union merely to validate it. The boxed capability keeps the
/// resolver compact while proving both the raw return and retained Array targets.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct GenericCallVectorResolution {
    projection: GenericCallVectorProjection,
    checked_instantiation: Option<GenericCallVectorInstantiation>,
    applicability: GenericCallVectorApplicability,
    capability: Box<GenericCallVectorCapability>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct GenericCallVectorCapability {
    checked_return_source: TypeId,
    array_targets: Option<CanonicalArrayTargets>,
}

impl GenericCallVectorResolution {
    pub(super) const fn projection(&self) -> &GenericCallVectorProjection {
        &self.projection
    }

    pub(super) fn checked_instantiation(&self) -> Option<&GenericCallVectorInstantiation> {
        self.checked_instantiation.as_ref()
    }

    pub(super) const fn applicability(&self) -> GenericCallVectorApplicability {
        self.applicability
    }
}

/// One dependency-closed global checked-signature cache result.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct GenericCallVectorCachedInstantiation {
    pub(super) signature: SignatureId,
    pub(super) mapper: TypeMapperId,
}

/// Outcome of checked-shell validation after resolution.
///
/// Type/value arity and explicit-constraint failures never reach pinned
/// `getSignatureInstantiation`, so they are explicitly left unmaterialized.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum GenericCallVectorMaterialization {
    Unmaterialized {
        applicability: GenericCallVectorApplicability,
    },
    Reused(GenericCallVectorCachedInstantiation),
}

/// The signature selected for one source call, together with the globally
/// cached checked signature when pinned overload resolution creates one.
///
/// Erroneous calls always select an uncached recovery signature. For TS2345,
/// `checked_instantiation` therefore differs from `call_signature`; an
/// applicable call exposes the same authoritative signature in both fields.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct GenericCallVectorSourceMaterialization {
    pub(super) call_signature: SignatureId,
    pub(super) call_mapper: TypeMapperId,
    pub(super) checked_instantiation: Option<GenericCallVectorCachedInstantiation>,
}

#[derive(Clone, Copy, Debug)]
struct GenericCallTypeParameter {
    type_: TypeId,
    constraint: Option<TypeId>,
    default_type: Option<TypeId>,
    base_constraint: TypeId,
}

#[derive(Clone, Debug)]
struct GenericCallSignatureShape {
    signature: SignatureId,
    type_parameters: Vec<GenericCallTypeParameter>,
    parameter_templates: Vec<TypeId>,
    rest_element_template: Option<TypeId>,
    minimum_argument_count: usize,
    return_type: TypeId,
    array_targets: Option<CanonicalArrayTargets>,
}

#[derive(Clone, Debug)]
struct GenericUnionInferenceTemplate {
    parameter: TypeId,
    fixed: Vec<TypeId>,
}

#[derive(Debug)]
struct GenericCallVectorParameterPlan {
    target: SemanticSymbolId,
    data: SymbolData,
    name_type: Option<TypeId>,
}

#[derive(Debug)]
struct PreparedGenericCallVectorSignature {
    mapper_sources: Vec<TypeId>,
    mapper_targets: Vec<TypeId>,
    parameter_plans: Vec<GenericCallVectorParameterPlan>,
    instantiated_parameters: Vec<SemanticSymbolId>,
    flags: SignatureFlags,
    declaration: Option<NodeRef>,
    min_argument_count: i32,
}

/// Resolves the bounded full-vector generic branch through the canonical
/// callable provider. Checked and recovery signature shells are published
/// during resolution, while parameter and return types remain lazy. The source
/// provider must reject `const` type-parameter declarations before publication
/// because stored type-parameter records do not retain that bit.
pub(super) fn resolve_generic_call_vector(
    store: &mut CanonicalTypeMapperStore,
    global_types: &CanonicalGlobalTypes,
    strict_function_types: bool,
    request: GenericCallVectorRequest<'_>,
) -> Result<GenericCallVectorResolution, GenericCallVectorError> {
    let mut session = InstantiationSession::new(InstantiationLimits::default());
    resolve_generic_call_vector_with_session(
        store,
        global_types,
        strict_function_types,
        request,
        None,
        &mut session,
    )
}

pub(super) fn resolve_generic_call_vector_with_session(
    store: &mut CanonicalTypeMapperStore,
    global_types: &CanonicalGlobalTypes,
    strict_function_types: bool,
    request: GenericCallVectorRequest<'_>,
    existing_call_signature: Option<SignatureId>,
    session: &mut InstantiationSession,
) -> Result<GenericCallVectorResolution, GenericCallVectorError> {
    validate_generic_call_vector_request(store, request)?;
    let callable = match validate_stored_single_callable(store, request.callee) {
        StoredSingleCallableValidation::NotCallable => {
            return Err(
                GenericCallVectorUnsupported::NotExactSingleCallable(request.callee).into(),
            );
        }
        StoredSingleCallableValidation::Pending { .. } => {
            return Err(GenericCallVectorUnsupported::PendingCallable(request.callee).into());
        }
        StoredSingleCallableValidation::Malformed { .. } => {
            return Err(GenericCallVectorInvariant::MalformedCallable(request.callee).into());
        }
        StoredSingleCallableValidation::Valid { callable, .. } => callable,
    };
    project_validated_generic_call_vector_with_session(
        store,
        request,
        &callable,
        Some(CanonicalArrayTargets::from_global_types(global_types)),
        existing_call_signature,
        session,
        |store, source, target| {
            store.is_type_assignable_to_with_global_types_and_strict_function_types(
                source,
                target,
                global_types,
                strict_function_types,
            )
        },
        |store, source, target| {
            store.is_type_strict_subtype_of_with_global_types(source, target, global_types)
        },
        |store, source, target| {
            store.is_type_subtype_of_with_global_types(source, target, global_types)
        },
    )
}

/// Instantiates one generic signature against an authenticated rest signature.
///
/// Relation comparison already owns the active relation observation, so this
/// bounded inference path cannot start another relation query. Every inferred
/// candidate is therefore the same canonical contextual rest element.
#[allow(clippy::too_many_lines)] // Validate both callable graphs before publishing one signature.
pub(super) fn instantiate_generic_signature_in_context_of(
    store: &mut CanonicalTypeMapperStore,
    source: &ValidatedSingleCallable,
    contextual: &ValidatedSingleCallable,
    array_targets: Option<CanonicalArrayTargets>,
) -> Result<ValidatedSingleCallable, GenericCallVectorError> {
    for candidate in [source, contextual] {
        match validate_stored_single_callable(store, candidate.owner) {
            StoredSingleCallableValidation::NotCallable => {
                return Err(
                    GenericCallVectorUnsupported::NotExactSingleCallable(candidate.owner).into(),
                );
            }
            StoredSingleCallableValidation::Pending { .. } => {
                return Err(GenericCallVectorUnsupported::PendingCallable(candidate.owner).into());
            }
            StoredSingleCallableValidation::Malformed { .. } => {
                return Err(GenericCallVectorInvariant::MalformedCallable(candidate.owner).into());
            }
            StoredSingleCallableValidation::Valid { callable, .. } if callable == *candidate => {}
            StoredSingleCallableValidation::Valid { .. } => {
                return Err(GenericCallVectorInvariant::CallableSignatureMismatch(
                    candidate.signature,
                )
                .into());
            }
        }
    }

    let contextual_record = store.signature(contextual.signature).ok_or(
        GenericCallVectorInvariant::InvalidSignature(contextual.signature),
    )?;
    if !contextual_record.type_parameters().is_empty()
        || contextual_record.this_parameter().is_some()
        || contextual_record.flags() != SignatureFlags::HAS_REST_PARAMETER
        || !contextual.parameters.is_empty()
        || contextual.min_argument_count != 0
    {
        return Err(GenericCallVectorUnsupported::ContextualSignature(contextual.signature).into());
    }
    let (Some(array_targets), Some(rest)) = (array_targets, contextual.rest_parameter) else {
        return Err(GenericCallVectorUnsupported::ContextualSignature(contextual.signature).into());
    };
    let reference = store
        .canonical_array_reference_with_targets(array_targets, rest)
        .map_err(|error| GenericCallVectorInvariant::InvalidArrayType {
            signature: contextual.signature,
            type_: rest,
            error,
        })?;
    let Some(reference) = reference else {
        return Err(GenericCallVectorUnsupported::ContextualSignature(contextual.signature).into());
    };
    if reference.readonly
        || reference.array_literal
        || contextual.return_type != Some(reference.element_type)
        || contextual_record.resolved_return_type() != contextual.return_type
    {
        return Err(GenericCallVectorUnsupported::ContextualSignature(contextual.signature).into());
    }

    let shape =
        validate_generic_call_signature_shape(store, source.owner, source, Some(array_targets))?;
    let sources = shape
        .type_parameters
        .iter()
        .map(|parameter| parameter.type_)
        .collect::<Vec<_>>();
    for parameter in &shape.type_parameters {
        if let Some(constraint) = parameter.constraint {
            return Err(GenericCallVectorUnsupported::TypeParameterDependency {
                type_parameter: parameter.type_,
                dependency: constraint,
            }
            .into());
        }
    }
    for (index, template) in shape.parameter_templates.iter().copied().enumerate() {
        let template = if index >= shape.minimum_argument_count {
            optional_generic_parameter_template(
                store,
                template,
                &sources,
                Some(array_targets),
                shape.signature,
            )?
            .unwrap_or(template)
        } else {
            template
        };
        if !sources.contains(&template) {
            return Err(GenericCallVectorUnsupported::NonNakedParameter {
                signature: shape.signature,
                index,
                type_: template,
            }
            .into());
        }
    }

    let mut inference_shape = shape.clone();
    let mut contextual_arguments = vec![reference.element_type; shape.parameter_templates.len()];
    if sources.contains(&shape.return_type) {
        inference_shape.parameter_templates.push(shape.return_type);
        contextual_arguments.push(reference.element_type);
    }
    let mut session = InstantiationSession::new(InstantiationLimits::default());
    let type_arguments = infer_generic_call_type_arguments(
        store,
        &inference_shape,
        &contextual_arguments,
        &mut |_, left, right| Ok(left == right),
        &mut |_, left, right| Ok(left == right),
        &mut |_, left, right| Ok(left == right),
        &mut session,
    )?;
    let (instantiation, _) =
        get_or_create_checked_generic_call_vector_shell(store, &shape, &sources, &type_arguments)?;
    let mut parameters = Vec::with_capacity(shape.parameter_templates.len());
    for index in 0..shape.parameter_templates.len() {
        parameters.push(demand_generic_call_vector_parameter(
            store,
            &shape,
            &sources,
            &type_arguments,
            instantiation.signature,
            index,
            &mut session,
        )?);
    }
    let return_type = demand_generic_call_vector_return(
        store,
        &shape,
        &sources,
        &type_arguments,
        instantiation.signature,
        &mut session,
    )?;
    Ok(ValidatedSingleCallable {
        owner: source.owner,
        signature: instantiation.signature,
        parameters,
        rest_parameter: None,
        min_argument_count: source.min_argument_count,
        return_type: Some(return_type),
        strict_variance_exempt: source.strict_variance_exempt,
    })
}

/// Materializes the exact checked signature globally cached by pinned
/// `getSignatureInstantiation`. Applicable calls and TS2345 candidates use the
/// checked vector; every recovery-only diagnostic class remains untouched.
pub(super) fn materialize_generic_call_vector_checked_instantiation(
    store: &mut CanonicalTypeMapperStore,
    resolution: &GenericCallVectorResolution,
) -> Result<GenericCallVectorMaterialization, GenericCallVectorError> {
    if !generic_call_vector_caches_checked_instantiation(resolution.applicability) {
        return Ok(GenericCallVectorMaterialization::Unmaterialized {
            applicability: resolution.applicability,
        });
    }
    let callee = resolution.projection.callee;
    let callable = match validate_stored_single_callable(store, callee) {
        StoredSingleCallableValidation::NotCallable => {
            return Err(GenericCallVectorUnsupported::NotExactSingleCallable(callee).into());
        }
        StoredSingleCallableValidation::Pending { .. } => {
            return Err(GenericCallVectorUnsupported::PendingCallable(callee).into());
        }
        StoredSingleCallableValidation::Malformed { .. } => {
            return Err(GenericCallVectorInvariant::MalformedCallable(callee).into());
        }
        StoredSingleCallableValidation::Valid { callable, .. } => callable,
    };
    materialize_validated_generic_call_vector_checked_instantiation(store, resolution, &callable)
}

/// Validates and exposes the signature shell selected during resolution.
/// `existing_call_signature` is the call node's previously published
/// signature, if any.
///
/// Applicable calls use the authoritative global checked-signature cache.
/// Every erroneous cold call receives a distinct uncached recovery signature.
/// TS2345 additionally creates or reuses its checked signature before
/// applicability, while the recovery shell remains call-local.
pub(super) fn materialize_generic_call_vector_source(
    store: &mut CanonicalTypeMapperStore,
    resolution: &GenericCallVectorResolution,
    existing_call_signature: Option<SignatureId>,
) -> Result<GenericCallVectorSourceMaterialization, GenericCallVectorError> {
    let callee = resolution.projection.callee;
    let callable = match validate_stored_single_callable(store, callee) {
        StoredSingleCallableValidation::NotCallable => {
            return Err(GenericCallVectorUnsupported::NotExactSingleCallable(callee).into());
        }
        StoredSingleCallableValidation::Pending { .. } => {
            return Err(GenericCallVectorUnsupported::PendingCallable(callee).into());
        }
        StoredSingleCallableValidation::Malformed { .. } => {
            return Err(GenericCallVectorInvariant::MalformedCallable(callee).into());
        }
        StoredSingleCallableValidation::Valid { callable, .. } => callable,
    };
    materialize_validated_generic_call_vector_source(
        store,
        resolution,
        &callable,
        existing_call_signature,
    )
}

/// Resolves only the return of the signature selected for this call. Checked
/// returns stay cold through applicability, and erroneous calls resolve the
/// uncached recovery return rather than the retained checked candidate.
pub(super) fn demand_generic_call_vector_selected_return(
    store: &mut CanonicalTypeMapperStore,
    resolution: &GenericCallVectorResolution,
    session: &mut InstantiationSession,
) -> Result<(TypeId, DirectCallReturnKind), GenericCallVectorError> {
    let callee = resolution.projection.callee;
    let callable = match validate_stored_single_callable(store, callee) {
        StoredSingleCallableValidation::NotCallable => {
            return Err(GenericCallVectorUnsupported::NotExactSingleCallable(callee).into());
        }
        StoredSingleCallableValidation::Pending { .. } => {
            return Err(GenericCallVectorUnsupported::PendingCallable(callee).into());
        }
        StoredSingleCallableValidation::Malformed { .. } => {
            return Err(GenericCallVectorInvariant::MalformedCallable(callee).into());
        }
        StoredSingleCallableValidation::Valid { callable, .. } => callable,
    };
    let shape = validate_generic_call_signature_shape(
        store,
        callee,
        &callable,
        resolution.capability.array_targets,
    )?;
    let sources = validate_generic_call_vector_resolution(store, resolution, &shape)?;
    let selected = &resolution.projection.instantiation;
    let return_type = demand_generic_call_vector_return(
        store,
        &shape,
        &sources,
        &selected.type_arguments,
        selected.signature,
        session,
    )?;
    let return_kind = if store
        .type_payload(return_type)
        .is_some_and(|record| record.flags().intersects(TypeFlags::VOID))
    {
        DirectCallReturnKind::Void
    } else {
        DirectCallReturnKind::Value
    };
    Ok((return_type, return_kind))
}

pub(super) fn demand_generic_call_vector_return_with_session(
    store: &mut CanonicalTypeMapperStore,
    resolution: &GenericCallVectorResolution,
    session: &mut InstantiationSession,
) -> Result<TypeId, GenericCallVectorError> {
    demand_generic_call_vector_selected_return(store, resolution, session)
        .map(|(return_type, _)| return_type)
}

/// Proves that a mapper-backed signature is an exact lazy generic-call shell
/// before its original target return is recursively resolved. This keeps a
/// malformed outer shell from causing partial publication in an otherwise
/// valid target signature.
pub(super) fn preflight_generic_call_signature_return_target(
    store: &CanonicalTypeMapperStore,
    array_targets: Option<CanonicalArrayTargets>,
    signature: SignatureId,
) -> Result<SignatureId, GenericCallVectorError> {
    let instantiated = store.signature(signature).ok_or(
        GenericCallVectorInvariant::InvalidCachedInstantiation {
            target: signature,
            signature,
        },
    )?;
    let target =
        instantiated
            .target()
            .ok_or(GenericCallVectorInvariant::InvalidCachedInstantiation {
                target: signature,
                signature,
            })?;
    let mapper = instantiated
        .mapper()
        .ok_or(GenericCallVectorInvariant::InvalidCachedInstantiation { target, signature })?;
    let callee = store
        .source_callable_type_for_signature(target)
        .ok_or(GenericCallVectorInvariant::InvalidCachedInstantiation { target, signature })?;
    let callable = match validate_stored_single_callable(store, callee) {
        StoredSingleCallableValidation::NotCallable => {
            return Err(GenericCallVectorUnsupported::NotExactSingleCallable(callee).into());
        }
        StoredSingleCallableValidation::Pending { .. } => {
            return Err(GenericCallVectorUnsupported::PendingCallable(callee).into());
        }
        StoredSingleCallableValidation::Malformed { .. } => {
            return Err(GenericCallVectorInvariant::MalformedCallable(callee).into());
        }
        StoredSingleCallableValidation::Valid { callable, .. } => callable,
    };
    if callable.signature != target
        || store
            .signature(target)
            .is_none_or(|target| target.target().is_some() || target.mapper().is_some())
        || callable.return_type.is_none() && instantiated.resolved_return_type().is_some()
    {
        return Err(
            GenericCallVectorInvariant::InvalidCachedInstantiation { target, signature }.into(),
        );
    }
    let shape = match validate_generic_call_signature_shape_with_unresolved_return(
        store,
        callee,
        &callable,
        array_targets,
        true,
    ) {
        Ok(shape) => shape,
        Err(vector_error) => {
            let provenance = identity_type_parameter_cache_provenance(store, callee, &callable);
            match validate_identity_signature_shape(store, callee, &callable, provenance)
                .ok()
                .and_then(|identity| identity_generic_call_vector_shape(store, identity).ok())
            {
                Some(shape) => shape,
                None => return Err(vector_error),
            }
        }
    };
    let sources = shape
        .type_parameters
        .iter()
        .map(|parameter| parameter.type_)
        .collect::<Vec<_>>();
    let type_arguments = sources
        .iter()
        .map(|source| {
            store
                .map_type(mapper, *source)
                .ok_or(GenericCallVectorInvariant::InvalidCachedInstantiation { target, signature })
        })
        .collect::<Result<Vec<_>, _>>()?;
    if store.type_mapper_has_exact_endpoints(mapper, &sources, &type_arguments) != Some(true)
        || validate_generic_call_vector_shell(store, &shape, &sources, &type_arguments, signature)?
            != mapper
    {
        return Err(
            GenericCallVectorInvariant::InvalidCachedInstantiation { target, signature }.into(),
        );
    }
    Ok(target)
}

/// Demands the return of a mapper-backed generic-call shell when only the
/// instantiated signature is available (for example from a type node).
///
/// This remains fail-closed to the bounded generic-call domain: it
/// reconstructs the original source callable, recovers the mapper targets,
/// and runs the same exact warm-shell validator before filling the return.
pub(super) fn demand_generic_call_signature_return_with_session(
    store: &mut CanonicalTypeMapperStore,
    array_targets: Option<CanonicalArrayTargets>,
    signature: SignatureId,
    session: &mut InstantiationSession,
) -> Result<TypeId, GenericCallVectorError> {
    let instantiated = store.signature(signature).ok_or(
        GenericCallVectorInvariant::InvalidCachedInstantiation {
            target: signature,
            signature,
        },
    )?;
    let target =
        instantiated
            .target()
            .ok_or(GenericCallVectorInvariant::InvalidCachedInstantiation {
                target: signature,
                signature,
            })?;
    let mapper = instantiated
        .mapper()
        .ok_or(GenericCallVectorInvariant::InvalidCachedInstantiation { target, signature })?;
    let callee = store
        .source_callable_type_for_signature(target)
        .ok_or(GenericCallVectorInvariant::InvalidCachedInstantiation { target, signature })?;
    let callable = match validate_stored_single_callable(store, callee) {
        StoredSingleCallableValidation::NotCallable => {
            return Err(GenericCallVectorUnsupported::NotExactSingleCallable(callee).into());
        }
        StoredSingleCallableValidation::Pending { .. } => {
            return Err(GenericCallVectorUnsupported::PendingCallable(callee).into());
        }
        StoredSingleCallableValidation::Malformed { .. } => {
            return Err(GenericCallVectorInvariant::MalformedCallable(callee).into());
        }
        StoredSingleCallableValidation::Valid { callable, .. } => callable,
    };
    if callable.signature != target {
        return Err(
            GenericCallVectorInvariant::InvalidCachedInstantiation { target, signature }.into(),
        );
    }
    let shape = match validate_generic_call_signature_shape(store, callee, &callable, array_targets)
    {
        Ok(shape) => shape,
        Err(vector_error) => {
            let provenance = identity_type_parameter_cache_provenance(store, callee, &callable);
            match validate_identity_signature_shape(store, callee, &callable, provenance)
                .ok()
                .and_then(|identity| identity_generic_call_vector_shape(store, identity).ok())
            {
                Some(shape) => shape,
                None => return Err(vector_error),
            }
        }
    };
    let sources = shape
        .type_parameters
        .iter()
        .map(|parameter| parameter.type_)
        .collect::<Vec<_>>();
    let type_arguments = sources
        .iter()
        .map(|source| {
            store
                .map_type(mapper, *source)
                .ok_or(GenericCallVectorInvariant::InvalidCachedInstantiation { target, signature })
        })
        .collect::<Result<Vec<_>, _>>()?;
    if store.type_mapper_has_exact_endpoints(mapper, &sources, &type_arguments) != Some(true) {
        return Err(
            GenericCallVectorInvariant::InvalidCachedInstantiation { target, signature }.into(),
        );
    }
    demand_generic_call_vector_return(store, &shape, &sources, &type_arguments, signature, session)
}

fn generic_call_vector_resolution(
    projection: GenericCallVectorProjection,
    checked_instantiation: Option<GenericCallVectorInstantiation>,
    applicability: GenericCallVectorApplicability,
    checked_return_source: TypeId,
    array_targets: Option<CanonicalArrayTargets>,
) -> GenericCallVectorResolution {
    GenericCallVectorResolution {
        projection,
        checked_instantiation,
        applicability,
        capability: Box::new(GenericCallVectorCapability {
            checked_return_source,
            array_targets,
        }),
    }
}

fn project_validated_generic_call_vector(
    store: &mut CanonicalTypeMapperStore,
    request: GenericCallVectorRequest<'_>,
    callable: &ValidatedSingleCallable,
    array_targets: Option<CanonicalArrayTargets>,
    is_assignable: impl FnMut(
        &mut CanonicalTypeMapperStore,
        TypeId,
        TypeId,
    ) -> Result<bool, RelationUnavailable>,
    is_strict_subtype: impl FnMut(
        &mut CanonicalTypeMapperStore,
        TypeId,
        TypeId,
    ) -> Result<bool, RelationUnavailable>,
    is_subtype: impl FnMut(
        &mut CanonicalTypeMapperStore,
        TypeId,
        TypeId,
    ) -> Result<bool, RelationUnavailable>,
) -> Result<GenericCallVectorResolution, GenericCallVectorError> {
    let mut session = InstantiationSession::new(InstantiationLimits::default());
    project_validated_generic_call_vector_with_session(
        store,
        request,
        callable,
        array_targets,
        None,
        &mut session,
        is_assignable,
        is_strict_subtype,
        is_subtype,
    )
}

#[allow(clippy::too_many_arguments)]
fn project_validated_generic_call_vector_with_session(
    store: &mut CanonicalTypeMapperStore,
    request: GenericCallVectorRequest<'_>,
    callable: &ValidatedSingleCallable,
    array_targets: Option<CanonicalArrayTargets>,
    existing_call_signature: Option<SignatureId>,
    session: &mut InstantiationSession,
    mut is_assignable: impl FnMut(
        &mut CanonicalTypeMapperStore,
        TypeId,
        TypeId,
    ) -> Result<bool, RelationUnavailable>,
    mut is_strict_subtype: impl FnMut(
        &mut CanonicalTypeMapperStore,
        TypeId,
        TypeId,
    ) -> Result<bool, RelationUnavailable>,
    mut is_subtype: impl FnMut(
        &mut CanonicalTypeMapperStore,
        TypeId,
        TypeId,
    ) -> Result<bool, RelationUnavailable>,
) -> Result<GenericCallVectorResolution, GenericCallVectorError> {
    validate_generic_call_vector_request(store, request)?;
    let request = GenericCallVectorRequest {
        explicit_type_arguments: request
            .explicit_type_arguments
            .filter(|arguments| !arguments.is_empty()),
        ..request
    };
    let shape =
        validate_generic_call_signature_shape(store, request.callee, callable, array_targets)?;
    let sources = shape
        .type_parameters
        .iter()
        .map(|parameter| parameter.type_)
        .collect::<Vec<_>>();
    let minimum_type_arguments = minimum_type_argument_count(&shape.type_parameters);
    if let Some(explicit) = request.explicit_type_arguments
        && (explicit.len() < minimum_type_arguments || explicit.len() > shape.type_parameters.len())
    {
        let recovery = explicit_recovery_type_arguments(store, &shape, explicit)?;
        let shell = get_or_create_generic_call_vector_recovery_shell(
            store,
            &shape,
            &sources,
            &recovery,
            existing_call_signature,
            None,
        )?;
        return Ok(generic_call_vector_resolution(
            generic_call_projection(request.callee, &shape, recovery, shell, true),
            None,
            GenericCallVectorApplicability::TypeArgumentArity {
                minimum: minimum_type_arguments,
                maximum: shape.type_parameters.len(),
                actual: explicit.len(),
            },
            shape.return_type,
            shape.array_targets,
        ));
    }

    let maximum_arguments = shape.parameter_templates.len();
    if request.arguments.len() < shape.minimum_argument_count
        || shape.rest_element_template.is_none() && request.arguments.len() > maximum_arguments
    {
        let recovery = failure_type_arguments(
            store,
            &shape,
            request,
            &mut is_assignable,
            &mut is_strict_subtype,
            &mut is_subtype,
            session,
        )?;
        let shell = get_or_create_generic_call_vector_recovery_shell(
            store,
            &shape,
            &sources,
            &recovery,
            existing_call_signature,
            None,
        )?;
        let applicability = if request.arguments.len() < shape.minimum_argument_count {
            GenericCallVectorApplicability::TooFewArguments {
                expected: shape.minimum_argument_count,
                actual: request.arguments.len(),
            }
        } else {
            GenericCallVectorApplicability::TooManyArguments {
                expected: maximum_arguments,
                actual: request.arguments.len(),
            }
        };
        return Ok(generic_call_vector_resolution(
            generic_call_projection(request.callee, &shape, recovery, shell, true),
            None,
            applicability,
            shape.return_type,
            shape.array_targets,
        ));
    }

    let selected_type_arguments = match request.explicit_type_arguments {
        Some(explicit) => explicit_checked_type_arguments(store, &shape, explicit, session)?,
        None => infer_generic_call_type_arguments(
            store,
            &shape,
            request.arguments,
            &mut is_assignable,
            &mut is_strict_subtype,
            &mut is_subtype,
            session,
        )?,
    };

    if let Some(explicit) = request.explicit_type_arguments
        && let Some(applicability) = check_explicit_type_argument_constraints(
            store,
            &shape,
            explicit,
            &selected_type_arguments,
            &mut is_assignable,
            session,
        )?
    {
        let recovery = explicit_recovery_type_arguments(store, &shape, explicit)?;
        let shell = get_or_create_generic_call_vector_recovery_shell(
            store,
            &shape,
            &sources,
            &recovery,
            existing_call_signature,
            None,
        )?;
        return Ok(generic_call_vector_resolution(
            generic_call_projection(request.callee, &shape, recovery, shell, true),
            None,
            applicability,
            shape.return_type,
            shape.array_targets,
        ));
    }

    let (checked_shell, _) = get_or_create_checked_generic_call_vector_shell(
        store,
        &shape,
        &sources,
        &selected_type_arguments,
    )?;
    let checked = GenericCallVectorInstantiation {
        type_arguments: selected_type_arguments.clone(),
        signature: checked_shell.signature,
        mapper: checked_shell.mapper,
    };
    if let Some(applicability) = check_generic_call_arguments(
        store,
        request.arguments,
        &shape,
        &sources,
        &checked,
        session,
        &mut is_assignable,
    )? {
        let recovery = match request.explicit_type_arguments {
            Some(explicit) => explicit_recovery_type_arguments(store, &shape, explicit)?,
            None => selected_type_arguments,
        };
        let shell = get_or_create_generic_call_vector_recovery_shell(
            store,
            &shape,
            &sources,
            &recovery,
            existing_call_signature,
            Some(checked_shell),
        )?;
        return Ok(generic_call_vector_resolution(
            generic_call_projection(request.callee, &shape, recovery, shell, true),
            Some(checked),
            applicability,
            shape.return_type,
            shape.array_targets,
        ));
    }

    if existing_call_signature.is_some_and(|existing| existing != checked.signature) {
        return Err(GenericCallVectorInvariant::InvalidCallInstantiation {
            target: shape.signature,
            signature: existing_call_signature
                .expect("the mismatching existing signature is present"),
        }
        .into());
    }
    Ok(generic_call_vector_resolution(
        generic_call_projection(
            request.callee,
            &shape,
            selected_type_arguments,
            checked_shell,
            false,
        ),
        Some(checked),
        GenericCallVectorApplicability::Applicable,
        shape.return_type,
        shape.array_targets,
    ))
}

fn validate_generic_call_vector_request(
    store: &CanonicalTypeMapperStore,
    request: GenericCallVectorRequest<'_>,
) -> Result<(), GenericCallVectorError> {
    if request.form != DirectCallForm::Call {
        return Err(GenericCallVectorUnsupported::Form(request.form).into());
    }
    if request.optional_chain {
        return Err(GenericCallVectorUnsupported::OptionalChain.into());
    }
    if request.has_spread_argument {
        return Err(GenericCallVectorUnsupported::SpreadArgument.into());
    }
    if store.type_payload(request.callee).is_none() {
        return Err(GenericCallVectorInvariant::InvalidCalleeType(request.callee).into());
    }
    for (index, type_) in request.arguments.iter().copied().enumerate() {
        if store.type_payload(type_).is_none() {
            return Err(GenericCallVectorInvariant::InvalidArgumentType { index, type_ }.into());
        }
    }
    for (index, type_) in request
        .explicit_type_arguments
        .unwrap_or_default()
        .iter()
        .copied()
        .enumerate()
    {
        if store.type_payload(type_).is_none() {
            return Err(GenericCallVectorInvariant::InvalidTypeArgument { index, type_ }.into());
        }
    }
    Ok(())
}

fn validate_generic_call_signature_shape(
    store: &CanonicalTypeMapperStore,
    callee: TypeId,
    callable: &ValidatedSingleCallable,
    array_targets: Option<CanonicalArrayTargets>,
) -> Result<GenericCallSignatureShape, GenericCallVectorError> {
    validate_generic_call_signature_shape_with_unresolved_return(
        store,
        callee,
        callable,
        array_targets,
        false,
    )
}

fn validate_generic_call_signature_shape_with_unresolved_return(
    store: &CanonicalTypeMapperStore,
    callee: TypeId,
    callable: &ValidatedSingleCallable,
    array_targets: Option<CanonicalArrayTargets>,
    allow_unresolved_return: bool,
) -> Result<GenericCallSignatureShape, GenericCallVectorError> {
    if callable.owner != callee {
        return Err(GenericCallVectorInvariant::CallableOwnerMismatch {
            callee,
            owner: callable.owner,
        }
        .into());
    }
    let signature =
        store
            .signature(callable.signature)
            .ok_or(GenericCallVectorInvariant::InvalidSignature(
                callable.signature,
            ))?;
    if signature.type_parameters().is_empty() {
        return Err(
            GenericCallVectorUnsupported::SignatureTypeParameterCount(callable.signature).into(),
        );
    }
    let has_rest_parameter = signature.has_rest_parameter();
    let expected_flags = if has_rest_parameter {
        SignatureFlags::HAS_REST_PARAMETER
    } else {
        SignatureFlags::NONE
    };
    if signature.flags() != expected_flags {
        return Err(GenericCallVectorUnsupported::SignatureFlags(callable.signature).into());
    }
    if signature.this_parameter().is_some() {
        return Err(GenericCallVectorUnsupported::ExplicitThisParameter(callable.signature).into());
    }
    let parameter_count = signature.parameters().len();
    let fixed_parameter_count = callable.parameters.len();
    let minimum_argument_count = usize::try_from(signature.min_argument_count())
        .map_err(|_| GenericCallVectorInvariant::CallableSignatureMismatch(callable.signature))?;
    if minimum_argument_count > fixed_parameter_count
        || callable.min_argument_count != minimum_argument_count
    {
        return Err(
            GenericCallVectorInvariant::CallableSignatureMismatch(callable.signature).into(),
        );
    }
    if has_rest_parameter != callable.rest_parameter.is_some()
        || fixed_parameter_count + usize::from(has_rest_parameter) != parameter_count
        || signature.resolved_min_argument_count() != -1
        || signature.resolved_type_predicate().is_some()
        || signature.target().is_some()
        || signature.mapper().is_some()
        || signature.isolated_signature_type().is_some()
        || signature.composite().is_some()
        || callable.strict_variance_exempt
    {
        return Err(
            GenericCallVectorInvariant::CallableSignatureMismatch(callable.signature).into(),
        );
    }
    let return_type = match (callable.return_type, signature.resolved_return_type()) {
        (Some(callable), Some(signature)) if callable == signature => Some(callable),
        (None, None) if allow_unresolved_return => None,
        (None, None) => {
            return Err(
                GenericCallVectorUnsupported::UnresolvedReturnType(callable.signature).into(),
            );
        }
        _ => {
            return Err(
                GenericCallVectorInvariant::CallableSignatureMismatch(callable.signature).into(),
            );
        }
    };

    let no_constraint = store
        .intrinsic_bootstrap()
        .map(|bootstrap| bootstrap.no_constraint_type)
        .ok_or(GenericCallVectorInvariant::MissingBootstrap)?;
    let mut type_parameters = Vec::with_capacity(signature.type_parameters().len());
    for type_parameter in signature.type_parameters().iter().copied() {
        if type_parameters
            .iter()
            .any(|parameter: &GenericCallTypeParameter| parameter.type_ == type_parameter)
        {
            return Err(GenericCallVectorInvariant::DuplicateTypeParameter(type_parameter).into());
        }
        let (constraint, default_type, base_constraint) = validate_generic_call_type_parameter(
            store,
            type_parameter,
            &type_parameters,
            no_constraint,
        )?;
        type_parameters.push(GenericCallTypeParameter {
            type_: type_parameter,
            constraint,
            default_type,
            base_constraint,
        });
    }
    let type_parameter_ids = type_parameters
        .iter()
        .map(|parameter| parameter.type_)
        .collect::<Vec<_>>();
    let rest_element_template = match callable.rest_parameter {
        None => None,
        Some(rest) => {
            let targets = array_targets.ok_or(GenericCallVectorUnsupported::RestSignature(
                callable.signature,
            ))?;
            let reference = store
                .canonical_array_reference_with_targets(targets, rest)
                .map_err(|error| GenericCallVectorInvariant::InvalidArrayType {
                    signature: callable.signature,
                    type_: rest,
                    error,
                })?
                .ok_or(GenericCallVectorUnsupported::RestSignature(
                    callable.signature,
                ))?;
            if reference.readonly || reference.array_literal {
                return Err(GenericCallVectorUnsupported::RestSignature(callable.signature).into());
            }
            Some(reference.element_type)
        }
    };
    let mut parameter_templates = callable.parameters.clone();
    if let Some(rest) = callable.rest_parameter {
        parameter_templates.push(rest);
    }
    for (index, (symbol, projected)) in signature
        .parameters()
        .iter()
        .copied()
        .zip(parameter_templates.iter().copied())
        .enumerate()
    {
        let valid_template = validate_generic_parameter_template(
            store,
            projected,
            &type_parameter_ids,
            array_targets,
            callable.signature,
            &mut Vec::new(),
        )?;
        if !valid_template
            && (index >= fixed_parameter_count
                || !valid_fixed_generic_source_parameter_type(store, projected))
            && (index < minimum_argument_count
                || optional_generic_parameter_template(
                    store,
                    projected,
                    &type_parameter_ids,
                    array_targets,
                    callable.signature,
                )?
                .is_none())
        {
            return Err(GenericCallVectorUnsupported::NonNakedParameter {
                signature: callable.signature,
                index,
                type_: projected,
            }
            .into());
        }
        let valid_symbol = store.symbol(symbol).is_some_and(|record| {
            record.flags() == SymbolFlags::FUNCTION_SCOPED_VARIABLE
                && record.check_flags() == CheckFlags::NONE
        }) && store.value_symbol_links(symbol)
            == Some(&ValueSymbolLinks {
                resolved_type: Some(projected),
                ..ValueSymbolLinks::default()
            });
        if !valid_symbol {
            return Err(GenericCallVectorInvariant::InvalidParameterSymbol {
                signature: callable.signature,
                index,
                symbol,
            }
            .into());
        }
    }
    if let Some(return_type) = return_type {
        validate_generic_mapper_type(
            store,
            return_type,
            &type_parameter_ids,
            array_targets,
            callable.signature,
            &mut Vec::new(),
        )?;
    }
    Ok(GenericCallSignatureShape {
        signature: callable.signature,
        type_parameters,
        parameter_templates,
        rest_element_template,
        minimum_argument_count,
        return_type: return_type.unwrap_or(no_constraint),
        array_targets,
    })
}

fn validate_generic_parameter_template(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
    type_parameters: &[TypeId],
    array_targets: Option<CanonicalArrayTargets>,
    signature: SignatureId,
    active_types: &mut Vec<TypeId>,
) -> Result<bool, GenericCallVectorError> {
    if type_parameters.contains(&type_) {
        return Ok(true);
    }

    if validated_generic_union_inference_template(
        store,
        type_,
        type_parameters,
        array_targets,
        signature,
    )?
    .is_some()
    {
        return Ok(true);
    }

    if let Some(array_targets) = array_targets {
        let reference = store
            .canonical_array_reference_with_targets(array_targets, type_)
            .map_err(|error| GenericCallVectorInvariant::InvalidArrayType {
                signature,
                type_,
                error,
            })?;
        if let Some(reference) = reference {
            if reference.array_literal || active_types.contains(&type_) {
                return Err(GenericCallVectorInvariant::InvalidArrayType {
                    signature,
                    type_,
                    error: ArrayTypeError::InvalidReference(type_),
                }
                .into());
            }
            active_types.push(type_);
            let contains_type_parameter = validate_generic_parameter_template(
                store,
                reference.element_type,
                type_parameters,
                Some(array_targets),
                signature,
                active_types,
            )?;
            active_types.pop();
            return Ok(contains_type_parameter);
        }
    }

    let Some(reference) = validate_generic_interface_reference(store, type_, signature)? else {
        return Ok(false);
    };
    if active_types.contains(&type_) {
        return Err(
            GenericCallVectorInvariant::InvalidInterfaceReference { signature, type_ }.into(),
        );
    }
    active_types.push(type_);
    let mut contains_type_parameter = true;
    for argument in reference.type_arguments {
        contains_type_parameter &= validate_generic_parameter_template(
            store,
            argument,
            type_parameters,
            array_targets,
            signature,
            active_types,
        )?;
    }
    active_types.pop();
    Ok(contains_type_parameter)
}

/// Authenticates `T | fixed` before inference removes the fixed constituents.
fn validated_generic_union_inference_template(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
    type_parameters: &[TypeId],
    array_targets: Option<CanonicalArrayTargets>,
    signature: SignatureId,
) -> Result<Option<GenericUnionInferenceTemplate>, GenericCallVectorError> {
    let Some(record) = store.type_payload(type_) else {
        return Err(GenericCallVectorInvariant::InvalidUnionParameter { signature, type_ }.into());
    };
    let TypeData::Union(union) = record.data() else {
        return Ok(None);
    };
    if union
        .union
        .types
        .iter()
        .filter(|constituent| type_parameters.contains(constituent))
        .count()
        != 1
    {
        return Ok(None);
    }
    let invalid = || GenericCallVectorInvariant::InvalidUnionParameter { signature, type_ };
    if record.flags() != TypeFlags::UNION
        || record.alias().is_some()
        || union.origin.is_some()
        || union.union.types.len() < 2
        || store
            .intrinsic_bootstrap()
            .and_then(|bootstrap| bootstrap.cached_union_type(&union.union.types))
            .is_some_and(|cached| cached != type_)
    {
        return Err(invalid().into());
    }

    let mut parameter = None;
    let mut fixed = Vec::with_capacity(union.union.types.len() - 1);
    let mut seen = Vec::with_capacity(union.union.types.len());
    for constituent in &union.union.types {
        if seen.contains(constituent) {
            return Err(invalid().into());
        }
        seen.push(*constituent);
        if type_parameters.contains(constituent) {
            if parameter.replace(*constituent).is_some() {
                return Ok(None);
            }
            continue;
        }
        let Some(record) = store.type_payload(*constituent) else {
            return Err(invalid().into());
        };
        if matches!(record.data(), TypeData::Union(_))
            || record
                .flags()
                .intersects(TypeFlags::ANY_OR_UNKNOWN | TypeFlags::NEVER)
        {
            return Err(invalid().into());
        }
        if !matches!(
            record.data(),
            TypeData::Intrinsic(_) | TypeData::Literal(_) | TypeData::UniqueEsSymbol(_)
        ) {
            return Ok(None);
        }
        match array_targets {
            Some(targets) => {
                validate_inference_leaf_with_array_targets(store, *constituent, targets)
            }
            None => validate_inference_leaf(store, *constituent),
        }
        .map_err(|_| invalid())?;
        fixed.push(*constituent);
    }
    Ok(parameter.map(|parameter| GenericUnionInferenceTemplate { parameter, fixed }))
}

/// Authenticates a direct generic interface without treating classes as wrappers.
fn validate_generic_interface_reference(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
    signature: SignatureId,
) -> Result<Option<DirectGenericReference>, GenericCallVectorError> {
    let invalid = || GenericCallVectorInvariant::InvalidInterfaceReference { signature, type_ };
    let Some(record) = store.type_payload(type_) else {
        return Err(invalid().into());
    };
    let target = match record.data() {
        TypeData::TypeReference(reference) => reference.object.target.ok_or_else(invalid)?,
        TypeData::Interface(interface) => {
            let Some(target) = interface.reference.object.target else {
                return Ok(None);
            };
            target
        }
        _ => return Ok(None),
    };
    let target_record = store.type_payload(target).ok_or_else(invalid)?;
    let TypeData::Interface(interface) = target_record.data() else {
        return Ok(None);
    };
    if interface
        .reference
        .resolved_type_arguments
        .as_ref()
        .is_none_or(Vec::is_empty)
        || target_record.object_flags() & ObjectFlags::CLASS_OR_INTERFACE != ObjectFlags::INTERFACE
    {
        return Ok(None);
    }

    let reference = validate_direct_generic_reference(store, type_).map_err(|_| invalid())?;
    let owner = target_record.symbol().ok_or_else(invalid)?;
    let owner_record = store.symbol(owner).ok_or_else(invalid)?;
    if !owner_record.flags().contains(SymbolFlags::INTERFACE)
        || owner_record
            .flags()
            .without(SymbolFlags::INTERFACE | SymbolFlags::TRANSIENT)
            != SymbolFlags::NONE
        || owner_record.check_flags() != CheckFlags::NONE
        || store.get_merged_symbol(owner) != Some(owner)
        || store
            .declared_type_links(owner)
            .and_then(|links| links.declared_type)
            != Some(reference.target)
    {
        return Err(invalid().into());
    }

    if let Some(variances) = store
        .variance_links(owner)
        .and_then(|links| links.variances.as_deref())
    {
        if variances.len() != reference.type_arguments.len() {
            return Err(
                GenericCallVectorInvariant::InvalidInterfaceVariance { signature, type_ }.into(),
            );
        }
        let allowed = VarianceFlags::VARIANCE_MASK | VarianceFlags::ALLOWS_STRUCTURAL_FALLBACK;
        for variance in variances.iter().copied() {
            let kind = variance & VarianceFlags::VARIANCE_MASK;
            if variance.bits() & !allowed.bits() != 0
                || !matches!(
                    kind,
                    VarianceFlags::INVARIANT
                        | VarianceFlags::COVARIANT
                        | VarianceFlags::CONTRAVARIANT
                        | VarianceFlags::BIVARIANT
                        | VarianceFlags::INDEPENDENT
                )
            {
                return Err(GenericCallVectorInvariant::InvalidInterfaceVariance {
                    signature,
                    type_,
                }
                .into());
            }
        }
    }

    Ok(Some(reference))
}

fn optional_generic_parameter_template(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
    type_parameters: &[TypeId],
    array_targets: Option<CanonicalArrayTargets>,
    signature: SignatureId,
) -> Result<Option<TypeId>, GenericCallVectorError> {
    let Some(record) = store.type_payload(type_) else {
        return Err(GenericCallVectorInvariant::CallableSignatureMismatch(signature).into());
    };
    let TypeData::Union(union) = record.data() else {
        return Ok(None);
    };
    let [left, right] = union.union.types.as_slice() else {
        return Ok(None);
    };
    let bootstrap = store
        .intrinsic_bootstrap()
        .ok_or(GenericCallVectorInvariant::MissingBootstrap)?;
    let template = if *left == bootstrap.undefined_type {
        *right
    } else if *right == bootstrap.undefined_type {
        *left
    } else {
        return Ok(None);
    };
    if record.alias().is_some()
        || union.origin.is_some()
        || bootstrap.cached_union_type(&union.union.types) != Some(type_)
    {
        return Err(GenericCallVectorInvariant::CallableSignatureMismatch(signature).into());
    }
    let generic = validate_generic_parameter_template(
        store,
        template,
        type_parameters,
        array_targets,
        signature,
        &mut Vec::new(),
    )?;
    Ok((generic || valid_fixed_generic_source_parameter_type(store, template)).then_some(template))
}

fn validate_generic_call_type_parameter(
    store: &CanonicalTypeMapperStore,
    type_parameter: TypeId,
    earlier: &[GenericCallTypeParameter],
    no_constraint: TypeId,
) -> Result<(Option<TypeId>, Option<TypeId>, TypeId), GenericCallVectorError> {
    let record = store.type_payload(type_parameter).ok_or(
        GenericCallVectorInvariant::InvalidTypeParameter(type_parameter),
    )?;
    let TypeData::TypeParameter(data) = record.data() else {
        return Err(GenericCallVectorInvariant::InvalidTypeParameter(type_parameter).into());
    };
    let symbol = record
        .symbol()
        .ok_or(GenericCallVectorInvariant::InvalidTypeParameter(
            type_parameter,
        ))?;
    let computed = ObjectFlags::COULD_CONTAIN_TYPE_VARIABLES
        | ObjectFlags::COULD_CONTAIN_TYPE_VARIABLES_COMPUTED;
    let valid_symbol = store.symbol(symbol).is_some_and(|symbol_record| {
        symbol_record.flags() == SymbolFlags::TYPE_PARAMETER
            && symbol_record.check_flags() == CheckFlags::NONE
    });
    if record.flags() != TypeFlags::TYPE_PARAMETER
        || (record.object_flags() != ObjectFlags::NONE && record.object_flags() != computed)
        || record.alias().is_some()
        || !valid_symbol
        || store.get_merged_symbol(symbol) != Some(symbol)
        || cached_ordinary_type_parameter_owner(store, type_parameter) != Some(symbol)
        || data.target.is_some()
        || data.mapper.is_some()
        || data.is_this_type
    {
        return Err(GenericCallVectorInvariant::InvalidTypeParameter(type_parameter).into());
    }
    let constraint = data
        .constraint
        .ok_or(GenericCallVectorInvariant::InvalidTypeParameter(
            type_parameter,
        ))?;
    let default_type =
        data.resolved_default_type
            .ok_or(GenericCallVectorInvariant::InvalidTypeParameter(
                type_parameter,
            ))?;
    let base_constraint = if constraint == no_constraint {
        no_constraint
    } else {
        validate_generic_constraint_dependency(store, constraint, earlier, type_parameter)?
    };
    if data
        .constrained
        .resolved_base_constraint
        .is_some_and(|cached| cached != base_constraint)
    {
        return Err(GenericCallVectorInvariant::InvalidTypeParameter(type_parameter).into());
    }
    let constraint = (constraint != no_constraint).then_some(constraint);
    let default_type = (default_type != no_constraint).then_some(default_type);
    if let Some(default_type) = default_type {
        validate_generic_type_parameter_dependency(store, default_type, earlier, type_parameter)?;
    }
    Ok((constraint, default_type, base_constraint))
}

fn validate_generic_constraint_dependency(
    store: &CanonicalTypeMapperStore,
    constraint: TypeId,
    earlier: &[GenericCallTypeParameter],
    owner: TypeId,
) -> Result<TypeId, GenericCallVectorError> {
    if let Some(parameter) = earlier
        .iter()
        .find(|parameter| parameter.type_ == constraint)
    {
        return Ok(parameter.base_constraint);
    }
    let record = store.type_payload(constraint).ok_or(
        GenericCallVectorUnsupported::TypeParameterDependency {
            type_parameter: owner,
            dependency: constraint,
        },
    )?;
    match record.data() {
        TypeData::Intrinsic(_) | TypeData::Literal(_) | TypeData::UniqueEsSymbol(_) => {
            Ok(constraint)
        }
        TypeData::Union(union)
            if record.alias().is_none()
                && (union.origin.is_none()
                    || authenticated_nongeneric_keyof_union(store, constraint)) =>
        {
            for constituent in &union.union.types {
                let base =
                    validate_generic_constraint_dependency(store, *constituent, earlier, owner)?;
                if base != *constituent {
                    return Err(GenericCallVectorUnsupported::TypeParameterDependency {
                        type_parameter: owner,
                        dependency: constraint,
                    }
                    .into());
                }
            }
            Ok(constraint)
        }
        _ => Err(GenericCallVectorUnsupported::TypeParameterDependency {
            type_parameter: owner,
            dependency: constraint,
        }
        .into()),
    }
}

fn validate_generic_type_parameter_dependency(
    store: &CanonicalTypeMapperStore,
    dependency: TypeId,
    earlier: &[GenericCallTypeParameter],
    owner: TypeId,
) -> Result<(), GenericCallVectorError> {
    let record = store.type_payload(dependency).ok_or(
        GenericCallVectorUnsupported::TypeParameterDependency {
            type_parameter: owner,
            dependency,
        },
    )?;
    match record.data() {
        TypeData::Intrinsic(_) | TypeData::Literal(_) | TypeData::UniqueEsSymbol(_) => Ok(()),
        TypeData::TypeParameter(_)
            if earlier
                .iter()
                .any(|parameter| parameter.type_ == dependency) =>
        {
            Ok(())
        }
        TypeData::Union(union)
            if record.alias().is_none()
                && (union.origin.is_none()
                    || authenticated_nongeneric_keyof_union(store, dependency)) =>
        {
            for constituent in &union.union.types {
                validate_generic_type_parameter_dependency(store, *constituent, earlier, owner)?;
            }
            Ok(())
        }
        _ => Err(GenericCallVectorUnsupported::TypeParameterDependency {
            type_parameter: owner,
            dependency,
        }
        .into()),
    }
}

/// Recognizes only the exact root-cached result of `keyof` on a named object.
fn authenticated_nongeneric_keyof_union(store: &CanonicalTypeMapperStore, type_: TypeId) -> bool {
    let Some(record) = store.type_payload(type_) else {
        return false;
    };
    let TypeData::Union(union) = record.data() else {
        return false;
    };
    if record.alias().is_some() {
        return false;
    }
    let Some(origin) = union.origin else {
        return false;
    };
    let Some(origin_record) = store.type_payload(origin) else {
        return false;
    };
    let TypeData::Index(index) = origin_record.data() else {
        return false;
    };
    if origin_record.flags() != TypeFlags::INDEX
        || origin_record.object_flags() != ObjectFlags::NONE
        || origin_record.symbol().is_some()
        || origin_record.alias().is_some()
        || index.index_flags != IndexFlags::NONE
    {
        return false;
    }
    let Ok(plan) = plan_nongeneric_keyof_type(store, index.target) else {
        return false;
    };
    plan.retains_index_origin()
        && cached_nongeneric_keyof_type(store, &plan).is_ok_and(|cached| cached == Some(type_))
}

fn validate_generic_mapper_type(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
    type_parameters: &[TypeId],
    array_targets: Option<CanonicalArrayTargets>,
    signature: SignatureId,
    active_types: &mut Vec<TypeId>,
) -> Result<(), GenericCallVectorError> {
    let record = store
        .type_payload(type_)
        .ok_or(GenericCallVectorUnsupported::InstantiationType { signature, type_ })?;
    match record.data() {
        TypeData::Intrinsic(_) | TypeData::Literal(_) | TypeData::UniqueEsSymbol(_) => Ok(()),
        TypeData::TypeParameter(_) if type_parameters.contains(&type_) => Ok(()),
        TypeData::Union(union) if record.alias().is_none() && union.origin.is_none() => {
            for constituent in &union.union.types {
                validate_generic_mapper_type(
                    store,
                    *constituent,
                    type_parameters,
                    None,
                    signature,
                    active_types,
                )?;
            }
            Ok(())
        }
        TypeData::TypeReference(_) | TypeData::Interface(_) => {
            if let Some(array_targets) = array_targets {
                let reference = store
                    .canonical_array_reference_with_targets(array_targets, type_)
                    .map_err(|error| GenericCallVectorInvariant::InvalidArrayType {
                        signature,
                        type_,
                        error,
                    })?;
                if let Some(reference) = reference {
                    if reference.array_literal || active_types.contains(&type_) {
                        return Err(GenericCallVectorInvariant::InvalidArrayType {
                            signature,
                            type_,
                            error: ArrayTypeError::InvalidReference(type_),
                        }
                        .into());
                    }
                    active_types.push(type_);
                    validate_generic_mapper_type(
                        store,
                        reference.element_type,
                        type_parameters,
                        Some(array_targets),
                        signature,
                        active_types,
                    )?;
                    active_types.pop();
                    return Ok(());
                }
            }

            let Some(reference) = validate_generic_interface_reference(store, type_, signature)?
            else {
                return Err(
                    GenericCallVectorUnsupported::InstantiationType { signature, type_ }.into(),
                );
            };
            if active_types.contains(&type_) {
                return Err(GenericCallVectorInvariant::InvalidInterfaceReference {
                    signature,
                    type_,
                }
                .into());
            }
            active_types.push(type_);
            for argument in reference.type_arguments {
                validate_generic_mapper_type(
                    store,
                    argument,
                    type_parameters,
                    array_targets,
                    signature,
                    active_types,
                )?;
            }
            active_types.pop();
            Ok(())
        }
        _ => Err(GenericCallVectorUnsupported::InstantiationType { signature, type_ }.into()),
    }
}

fn minimum_type_argument_count(parameters: &[GenericCallTypeParameter]) -> usize {
    parameters
        .iter()
        .enumerate()
        .filter_map(|(index, parameter)| parameter.default_type.is_none().then_some(index + 1))
        .max()
        .unwrap_or_default()
}

fn explicit_checked_type_arguments(
    store: &mut CanonicalTypeMapperStore,
    shape: &GenericCallSignatureShape,
    explicit: &[TypeId],
    session: &mut InstantiationSession,
) -> Result<Vec<TypeId>, GenericCallVectorError> {
    let sources = shape
        .type_parameters
        .iter()
        .map(|parameter| parameter.type_)
        .collect::<Vec<_>>();
    let mut result = explicit.to_vec();
    for index in explicit.len()..shape.type_parameters.len() {
        let default_type = shape.type_parameters[index].default_type.expect(
            "valid partial explicit arity guarantees every omitted parameter has a default",
        );
        let instantiated = instantiate_generic_call_type(
            store,
            default_type,
            &sources[..index],
            &result[..index],
            shape.array_targets,
            session,
        )?;
        result.push(instantiated);
    }
    Ok(result)
}

fn explicit_recovery_type_arguments(
    store: &CanonicalTypeMapperStore,
    shape: &GenericCallSignatureShape,
    explicit: &[TypeId],
) -> Result<Vec<TypeId>, GenericCallVectorError> {
    let unknown = store
        .intrinsic_bootstrap()
        .map(|bootstrap| bootstrap.unknown_type)
        .ok_or(GenericCallVectorInvariant::MissingBootstrap)?;
    let mut result = explicit
        .iter()
        .copied()
        .take(shape.type_parameters.len())
        .collect::<Vec<_>>();
    for parameter in shape.type_parameters.iter().skip(result.len()) {
        result.push(
            parameter
                .default_type
                .or(parameter.constraint)
                .unwrap_or(unknown),
        );
    }
    Ok(result)
}

fn failure_type_arguments(
    store: &mut CanonicalTypeMapperStore,
    shape: &GenericCallSignatureShape,
    request: GenericCallVectorRequest<'_>,
    is_assignable: &mut impl FnMut(
        &mut CanonicalTypeMapperStore,
        TypeId,
        TypeId,
    ) -> Result<bool, RelationUnavailable>,
    is_strict_subtype: &mut impl FnMut(
        &mut CanonicalTypeMapperStore,
        TypeId,
        TypeId,
    ) -> Result<bool, RelationUnavailable>,
    is_subtype: &mut impl FnMut(
        &mut CanonicalTypeMapperStore,
        TypeId,
        TypeId,
    ) -> Result<bool, RelationUnavailable>,
    session: &mut InstantiationSession,
) -> Result<Vec<TypeId>, GenericCallVectorError> {
    match request.explicit_type_arguments {
        Some(explicit) => explicit_recovery_type_arguments(store, shape, explicit),
        None => infer_generic_call_type_arguments(
            store,
            shape,
            request.arguments,
            is_assignable,
            is_strict_subtype,
            is_subtype,
            session,
        ),
    }
}

fn infer_generic_call_type_arguments(
    store: &mut CanonicalTypeMapperStore,
    shape: &GenericCallSignatureShape,
    arguments: &[TypeId],
    is_assignable: &mut impl FnMut(
        &mut CanonicalTypeMapperStore,
        TypeId,
        TypeId,
    ) -> Result<bool, RelationUnavailable>,
    is_strict_subtype: &mut impl FnMut(
        &mut CanonicalTypeMapperStore,
        TypeId,
        TypeId,
    ) -> Result<bool, RelationUnavailable>,
    is_subtype: &mut impl FnMut(
        &mut CanonicalTypeMapperStore,
        TypeId,
        TypeId,
    ) -> Result<bool, RelationUnavailable>,
    session: &mut InstantiationSession,
) -> Result<Vec<TypeId>, GenericCallVectorError> {
    let type_parameters = shape
        .type_parameters
        .iter()
        .map(|parameter| parameter.type_)
        .collect::<Vec<_>>();
    let mut buckets = vec![Vec::new(); type_parameters.len()];
    let mut contravariant_buckets = vec![Vec::new(); type_parameters.len()];
    let fixed_parameter_count =
        shape.parameter_templates.len() - usize::from(shape.rest_element_template.is_some());
    for (index, argument) in arguments.iter().copied().enumerate() {
        let Some(parameter) = shape
            .parameter_templates
            .get(index)
            .copied()
            .filter(|_| index < fixed_parameter_count)
            .or(shape.rest_element_template)
        else {
            break;
        };
        let parameter = if index >= shape.minimum_argument_count {
            optional_generic_parameter_template(
                store,
                parameter,
                &type_parameters,
                shape.array_targets,
                shape.signature,
            )?
            .unwrap_or(parameter)
        } else {
            parameter
        };
        if valid_fixed_generic_source_parameter_type(store, parameter) {
            continue;
        }
        collect_generic_call_inferences(
            store,
            shape.array_targets,
            argument,
            parameter,
            &type_parameters,
            &mut buckets,
            &mut contravariant_buckets,
            shape.signature,
            &mut Vec::new(),
            false,
        )?;
    }

    let unknown = store
        .intrinsic_bootstrap()
        .map(|bootstrap| bootstrap.unknown_type)
        .ok_or(GenericCallVectorInvariant::MissingBootstrap)?;
    let mut inferred = Vec::with_capacity(type_parameters.len());
    for (index, parameter) in shape.type_parameters.iter().enumerate() {
        let instantiated_constraint = parameter
            .constraint
            .map(|constraint| {
                instantiate_generic_call_type(
                    store,
                    constraint,
                    &type_parameters[..index],
                    &inferred[..index],
                    shape.array_targets,
                    session,
                )
            })
            .transpose()?;
        let treatment = if parameter
            .constraint
            .is_some_and(|constraint| type_maybe_primitive(store, constraint))
        {
            InferenceLiteralTreatment::Regularize
        } else if type_parameter_is_top_level_in_return(store, shape.return_type, parameter.type_) {
            InferenceLiteralTreatment::Preserve
        } else {
            InferenceLiteralTreatment::Widen
        };
        let candidate = if !contravariant_buckets[index].is_empty() {
            infer_naked_type_parameter_variance_candidates(
                store,
                &buckets[index],
                &contravariant_buckets[index],
                treatment,
                shape.array_targets,
                |store, source, target| is_assignable(store, source, target),
                |store, source, target| is_strict_subtype(store, source, target),
                |store, source, target| is_subtype(store, source, target),
            )?
        } else {
            match shape.array_targets {
                Some(array_targets) => infer_naked_type_parameter_candidates_with_array_targets(
                    store,
                    &buckets[index],
                    treatment,
                    array_targets,
                    |store, source, target| is_strict_subtype(store, source, target),
                    |store, source, target| is_subtype(store, source, target),
                )?,
                None => infer_naked_type_parameter_candidates(
                    store,
                    &buckets[index],
                    treatment,
                    |store, source, target| is_strict_subtype(store, source, target),
                    |store, source, target| is_subtype(store, source, target),
                )?,
            }
        };
        let mut argument = match candidate {
            Some(candidate) => candidate,
            None => parameter
                .default_type
                .map(|default_type| {
                    instantiate_generic_call_type(
                        store,
                        default_type,
                        &type_parameters[..index],
                        &inferred[..index],
                        shape.array_targets,
                        session,
                    )
                })
                .transpose()?
                .unwrap_or(unknown),
        };
        if let Some(constraint) = instantiated_constraint
            && !is_assignable(store, argument, constraint)?
        {
            argument = constraint;
        }
        inferred.push(argument);
        session.clear_active_mapper_caches();
    }
    Ok(inferred)
}

#[allow(clippy::too_many_arguments, clippy::too_many_lines)] // Keep wrapper and variance proofs in one inference walk.
fn collect_generic_call_inferences(
    store: &mut CanonicalTypeMapperStore,
    array_targets: Option<CanonicalArrayTargets>,
    source: TypeId,
    target: TypeId,
    type_parameters: &[TypeId],
    buckets: &mut [Vec<TypeId>],
    contravariant_buckets: &mut [Vec<TypeId>],
    signature: SignatureId,
    active_targets: &mut Vec<TypeId>,
    contravariant: bool,
) -> Result<(), GenericCallVectorError> {
    if is_non_inferrable_inference_source(store, source, array_targets)
        .map_err(|error| GenericCallVectorError::Inference(error.into()))?
    {
        return Ok(());
    }
    if let Some(index) = type_parameters
        .iter()
        .position(|type_parameter| *type_parameter == target)
    {
        match array_targets {
            Some(array_targets) => {
                validate_inference_leaf_with_array_targets(store, source, array_targets)
            }
            None => validate_inference_leaf(store, source),
        }
        .map_err(|error| GenericCallVectorError::Inference(error.into()))?;
        let bucket = if contravariant {
            &mut contravariant_buckets[index]
        } else {
            &mut buckets[index]
        };
        if !bucket.contains(&source) {
            bucket.push(source);
        }
        return Ok(());
    }

    if let Some(template) = validated_generic_union_inference_template(
        store,
        target,
        type_parameters,
        array_targets,
        signature,
    )? {
        let sources = match store
            .type_payload(source)
            .map(super::type_records::TypeRecord::data)
        {
            Some(TypeData::Union(union)) => {
                match array_targets {
                    Some(targets) => {
                        validate_inference_leaf_with_array_targets(store, source, targets)
                    }
                    None => validate_inference_leaf(store, source),
                }
                .map_err(|error| GenericCallVectorError::Inference(error.into()))?;
                union.union.types.clone()
            }
            Some(_) => vec![source],
            None => {
                return Err(GenericCallVectorError::Inference(
                    NakedTypeInferenceError::InvalidCandidate(source).into(),
                ));
            }
        };
        let unmatched = sources
            .into_iter()
            .filter(|source| {
                !template
                    .fixed
                    .iter()
                    .any(|fixed| generic_union_fixed_constituent_matches(store, *source, *fixed))
            })
            .collect::<Vec<_>>();
        let candidate = match unmatched.as_slice() {
            [] => source,
            [candidate] => *candidate,
            candidates => canonical_anonymous_union(store, candidates)
                .map_err(|error| GenericCallVectorError::Inference(error.into()))?,
        };
        return collect_generic_call_inferences(
            store,
            array_targets,
            candidate,
            template.parameter,
            type_parameters,
            buckets,
            contravariant_buckets,
            signature,
            active_targets,
            contravariant,
        );
    }

    if let Some(array_targets) = array_targets {
        let target_reference = store
            .canonical_array_reference_with_targets(array_targets, target)
            .map_err(|error| GenericCallVectorInvariant::InvalidArrayType {
                signature,
                type_: target,
                error,
            })?;
        if let Some(target_reference) = target_reference {
            if active_targets.contains(&target) {
                return Err(GenericCallVectorError::Inference(
                    NakedTypeInferenceError::RecursiveArrayCandidate(target).into(),
                ));
            }
            let source_reference = store
                .canonical_array_reference_with_targets(array_targets, source)
                .map_err(|error| {
                    GenericCallVectorError::Inference(
                        NakedTypeInferenceError::InvalidCanonicalArrayCandidate {
                            candidate: source,
                            error,
                        }
                        .into(),
                    )
                })?;
            let Some(source_reference) = source_reference else {
                return Ok(());
            };
            active_targets.push(target);
            let result = collect_generic_call_inferences(
                store,
                Some(array_targets),
                source_reference.element_type,
                target_reference.element_type,
                type_parameters,
                buckets,
                contravariant_buckets,
                signature,
                active_targets,
                contravariant,
            );
            active_targets.pop();
            return result;
        }
    }

    let target_reference = validate_generic_interface_reference(store, target, signature)?
        .expect("signature validation admitted a canonical generic interface target");
    let source_target = store
        .type_payload(source)
        .and_then(|record| match record.data() {
            TypeData::TypeReference(reference) => reference.object.target,
            TypeData::Interface(interface) => interface.reference.object.target,
            _ => None,
        });
    if source_target != Some(target_reference.target) {
        return Ok(());
    }
    let source_reference = validate_generic_interface_reference(store, source, signature)?.ok_or(
        GenericCallVectorInvariant::InvalidInterfaceReference {
            signature,
            type_: source,
        },
    )?;
    if active_targets.contains(&target) {
        return Err(GenericCallVectorInvariant::InvalidInterfaceReference {
            signature,
            type_: target,
        }
        .into());
    }
    let owner = store
        .type_payload(target_reference.target)
        .and_then(super::type_records::TypeRecord::symbol)
        .ok_or(GenericCallVectorInvariant::InvalidInterfaceReference {
            signature,
            type_: target,
        })?;
    let variances = store
        .variance_links(owner)
        .and_then(|links| links.variances.as_ref())
        .cloned();
    active_targets.push(target);
    let result = source_reference
        .type_arguments
        .into_iter()
        .zip(target_reference.type_arguments)
        .enumerate()
        .try_for_each(|(index, (source, target))| {
            let argument_contravariant = variances
                .as_ref()
                .and_then(|variances| variances.get(index))
                .is_some_and(|variance| {
                    *variance & VarianceFlags::VARIANCE_MASK == VarianceFlags::CONTRAVARIANT
                });
            collect_generic_call_inferences(
                store,
                array_targets,
                source,
                target,
                type_parameters,
                buckets,
                contravariant_buckets,
                signature,
                active_targets,
                contravariant != argument_contravariant,
            )
        });
    active_targets.pop();
    result
}

fn generic_union_fixed_constituent_matches(
    store: &CanonicalTypeMapperStore,
    source: TypeId,
    fixed: TypeId,
) -> bool {
    if source == fixed {
        return true;
    }
    let Some(source) = store.type_payload(source) else {
        return false;
    };
    let Some(fixed) = store.type_payload(fixed) else {
        return false;
    };
    source.flags().intersects(TypeFlags::STRING_LITERAL) && fixed.flags() == TypeFlags::STRING
        || source.flags().intersects(TypeFlags::NUMBER_LITERAL)
            && fixed.flags() == TypeFlags::NUMBER
        || source.flags().intersects(TypeFlags::BIG_INT_LITERAL)
            && fixed.flags() == TypeFlags::BIG_INT
        || source.flags().intersects(TypeFlags::BOOLEAN_LITERAL)
            && fixed.flags().intersects(TypeFlags::BOOLEAN)
}

fn type_maybe_primitive(store: &CanonicalTypeMapperStore, type_: TypeId) -> bool {
    let Some(record) = store.type_payload(type_) else {
        return false;
    };
    record.flags().intersects(TypeFlags::PRIMITIVE)
        || matches!(record.data(), TypeData::Union(union)
            if union.union.types.iter().copied().any(|type_| type_maybe_primitive(store, type_)))
}

fn type_parameter_is_top_level_in_return(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
    type_parameter: TypeId,
) -> bool {
    if type_ == type_parameter {
        return true;
    }
    matches!(store.type_payload(type_).map(super::type_records::TypeRecord::data),
    Some(TypeData::Union(union))
        if union.union.types.iter().copied().any(|constituent| {
            type_parameter_is_top_level_in_return(store, constituent, type_parameter)
        }))
}

fn check_explicit_type_argument_constraints(
    store: &mut CanonicalTypeMapperStore,
    shape: &GenericCallSignatureShape,
    explicit: &[TypeId],
    checked: &[TypeId],
    is_assignable: &mut impl FnMut(
        &mut CanonicalTypeMapperStore,
        TypeId,
        TypeId,
    ) -> Result<bool, RelationUnavailable>,
    session: &mut InstantiationSession,
) -> Result<Option<GenericCallVectorApplicability>, GenericCallVectorError> {
    let sources = shape
        .type_parameters
        .iter()
        .map(|parameter| parameter.type_)
        .collect::<Vec<_>>();
    for (index, type_argument) in explicit.iter().copied().enumerate() {
        let Some(constraint) = shape.type_parameters[index].constraint else {
            continue;
        };
        let constraint = instantiate_generic_call_type(
            store,
            constraint,
            &sources,
            checked,
            shape.array_targets,
            session,
        )?;
        if !is_assignable(store, type_argument, constraint)? {
            return Ok(Some(
                GenericCallVectorApplicability::ExplicitTypeArgumentConstraint {
                    index,
                    type_argument,
                    constraint,
                },
            ));
        }
    }
    Ok(None)
}

fn check_generic_call_arguments(
    store: &mut CanonicalTypeMapperStore,
    arguments: &[TypeId],
    shape: &GenericCallSignatureShape,
    sources: &[TypeId],
    checked: &GenericCallVectorInstantiation,
    session: &mut InstantiationSession,
    is_assignable: &mut impl FnMut(
        &mut CanonicalTypeMapperStore,
        TypeId,
        TypeId,
    ) -> Result<bool, RelationUnavailable>,
) -> Result<Option<GenericCallVectorApplicability>, GenericCallVectorError> {
    for (index, argument_type) in arguments.iter().copied().enumerate() {
        let fixed_parameter_count =
            shape.parameter_templates.len() - usize::from(shape.rest_element_template.is_some());
        let parameter_index = if index < fixed_parameter_count {
            index
        } else {
            fixed_parameter_count
        };
        let parameter_type = demand_generic_call_vector_parameter(
            store,
            shape,
            sources,
            &checked.type_arguments,
            checked.signature,
            parameter_index,
            session,
        )?;
        let parameter_type = if index >= fixed_parameter_count {
            let targets = shape
                .array_targets
                .ok_or(GenericCallVectorUnsupported::RestSignature(shape.signature))?;
            store
                .canonical_array_reference_with_targets(targets, parameter_type)
                .map_err(|error| GenericCallVectorInvariant::InvalidArrayType {
                    signature: shape.signature,
                    type_: parameter_type,
                    error,
                })?
                .map(|reference| reference.element_type)
                .ok_or(GenericCallVectorUnsupported::RestSignature(shape.signature))?
        } else {
            parameter_type
        };
        if !is_assignable(store, argument_type, parameter_type)? {
            return Ok(Some(
                GenericCallVectorApplicability::ArgumentNotAssignable {
                    index,
                    argument_type,
                    parameter_type,
                },
            ));
        }
    }
    Ok(None)
}

fn instantiate_generic_call_type(
    store: &mut CanonicalTypeMapperStore,
    type_: TypeId,
    sources: &[TypeId],
    targets: &[TypeId],
    array_targets: Option<CanonicalArrayTargets>,
    session: &mut InstantiationSession,
) -> Result<TypeId, InstantiationError> {
    if authenticated_nongeneric_keyof_union(store, type_) {
        return Ok(type_);
    }
    instantiate_type_with_vector_and_session(store, type_, sources, targets, array_targets, session)
}

fn generic_call_projection(
    callee: TypeId,
    shape: &GenericCallSignatureShape,
    type_arguments: Vec<TypeId>,
    shell: GenericCallVectorCachedInstantiation,
    recovery: bool,
) -> GenericCallVectorProjection {
    GenericCallVectorProjection {
        callee,
        generic_signature: shape.signature,
        type_parameters: shape
            .type_parameters
            .iter()
            .map(|parameter| parameter.type_)
            .collect(),
        instantiation: GenericCallVectorInstantiation {
            type_arguments,
            signature: shell.signature,
            mapper: shell.mapper,
        },
        recovery,
    }
}

const fn generic_call_vector_caches_checked_instantiation(
    applicability: GenericCallVectorApplicability,
) -> bool {
    matches!(
        applicability,
        GenericCallVectorApplicability::Applicable
            | GenericCallVectorApplicability::ArgumentNotAssignable { .. }
    )
}

fn get_or_create_checked_generic_call_vector_shell(
    store: &mut CanonicalTypeMapperStore,
    shape: &GenericCallSignatureShape,
    sources: &[TypeId],
    type_arguments: &[TypeId],
) -> Result<(GenericCallVectorCachedInstantiation, bool), GenericCallVectorError> {
    let key = type_list_key(type_arguments);
    let lookup = store.cached_signature(shape.signature, key, type_arguments);
    get_or_create_checked_generic_call_vector_shell_with(
        store,
        shape,
        sources,
        type_arguments,
        lookup,
        |store, parameter_count| {
            store.try_reserve_mappers(1)
                && store.try_reserve_checker_symbol_allocations(parameter_count, 0)
                && store.try_reserve_value_symbol_links(parameter_count)
                && store.try_reserve_signatures(1)
                && store.try_reserve_cached_signatures(1)
        },
    )
}

fn get_or_create_checked_generic_call_vector_shell_with(
    store: &mut CanonicalTypeMapperStore,
    shape: &GenericCallSignatureShape,
    sources: &[TypeId],
    type_arguments: &[TypeId],
    lookup: CachedSignatureLookup,
    reserve: impl FnOnce(&mut CanonicalTypeMapperStore, usize) -> bool,
) -> Result<(GenericCallVectorCachedInstantiation, bool), GenericCallVectorError> {
    if let Some(cached) = cached_generic_call_vector_instantiation_from_lookup(
        store,
        shape,
        sources,
        type_arguments,
        lookup,
    )? {
        return Ok((cached, false));
    }
    let plan = prepare_generic_call_vector_signature(store, shape, sources, type_arguments)?;
    let exact_type_arguments = type_arguments.to_vec().into_boxed_slice();
    if !reserve(store, shape.parameter_templates.len()) {
        return Err(GenericCallVectorInvariant::Capacity(shape.signature).into());
    }
    let published =
        publish_prepared_generic_call_vector_signature(store, shape, sources, type_arguments, plan);
    assert!(
        store.set_cached_signature(
            shape.signature,
            type_list_key(type_arguments),
            exact_type_arguments,
            published.signature,
        ),
        "the complete checked shell is committed to cachedSignatures last"
    );
    Ok((published, true))
}

fn get_or_create_generic_call_vector_recovery_shell(
    store: &mut CanonicalTypeMapperStore,
    shape: &GenericCallSignatureShape,
    sources: &[TypeId],
    type_arguments: &[TypeId],
    existing_call_signature: Option<SignatureId>,
    checked: Option<GenericCallVectorCachedInstantiation>,
) -> Result<GenericCallVectorCachedInstantiation, GenericCallVectorError> {
    if let Some(existing) = existing_call_signature {
        return validate_existing_generic_call_vector_recovery(
            store,
            shape,
            sources,
            type_arguments,
            existing,
            checked,
        );
    }

    let plan = prepare_generic_call_vector_signature(store, shape, sources, type_arguments)?;
    let parameter_count = shape.parameter_templates.len();
    if !store.try_reserve_mappers(1)
        || !store.try_reserve_checker_symbol_allocations(parameter_count, 0)
        || !store.try_reserve_value_symbol_links(parameter_count)
        || !store.try_reserve_signatures(1)
    {
        return Err(GenericCallVectorInvariant::Capacity(shape.signature).into());
    }
    let recovery =
        publish_prepared_generic_call_vector_signature(store, shape, sources, type_arguments, plan);
    assert_eq!(
        store.cached_signatures_contain(recovery.signature),
        Some(false),
        "recovery signatures must remain absent from the global cache"
    );
    if let Some(checked) = checked {
        assert_ne!(
            recovery.signature, checked.signature,
            "TS2345 recovery must be distinct from the checked signature"
        );
    }
    Ok(recovery)
}

fn materialize_validated_generic_call_vector_source(
    store: &mut CanonicalTypeMapperStore,
    resolution: &GenericCallVectorResolution,
    callable: &ValidatedSingleCallable,
    existing_call_signature: Option<SignatureId>,
) -> Result<GenericCallVectorSourceMaterialization, GenericCallVectorError> {
    let shape = validate_generic_call_signature_shape(
        store,
        resolution.projection.callee,
        callable,
        resolution.capability.array_targets,
    )?;
    let sources = validate_generic_call_vector_resolution(store, resolution, &shape)?;
    let call = &resolution.projection.instantiation;
    let call_mapper = validate_generic_call_vector_shell(
        store,
        &shape,
        &sources,
        &call.type_arguments,
        call.signature,
    )?;
    if call_mapper != call.mapper
        || existing_call_signature.is_some_and(|existing| existing != call.signature)
    {
        return Err(GenericCallVectorInvariant::InvalidCallInstantiation {
            target: shape.signature,
            signature: existing_call_signature.unwrap_or(call.signature),
        }
        .into());
    }
    let checked_instantiation = resolution
        .checked_instantiation
        .as_ref()
        .map(|checked| {
            validate_checked_generic_call_vector_instantiation(store, &shape, &sources, checked)
        })
        .transpose()?;
    Ok(GenericCallVectorSourceMaterialization {
        call_signature: call.signature,
        call_mapper,
        checked_instantiation,
    })
}

fn prepare_generic_call_vector_signature(
    store: &CanonicalTypeMapperStore,
    shape: &GenericCallSignatureShape,
    sources: &[TypeId],
    type_arguments: &[TypeId],
) -> Result<PreparedGenericCallVectorSignature, GenericCallVectorError> {
    let original =
        store
            .signature(shape.signature)
            .ok_or(GenericCallVectorInvariant::InvalidSignature(
                shape.signature,
            ))?;
    let original_parameters = original.parameters().to_vec();
    let flags = original.flags() & SignatureFlags::PROPAGATING_FLAGS;
    let declaration = original.declaration();
    let min_argument_count = original.min_argument_count();
    let mut parameter_plans = Vec::with_capacity(original_parameters.len());
    for (index, target) in original_parameters.iter().copied().enumerate() {
        let parameter =
            store
                .symbol(target)
                .ok_or(GenericCallVectorInvariant::InvalidParameterSymbol {
                    signature: shape.signature,
                    index,
                    symbol: target,
                })?;
        let mut data = SymbolData::new(
            parameter.flags() | SymbolFlags::TRANSIENT,
            parameter.name().to_owned(),
        );
        data.check_flags = CheckFlags::INSTANTIATED;
        data.declarations = parameter.declarations().map(<[_]>::to_vec);
        data.value_declaration = parameter.value_declaration();
        data.parent = parameter.parent();
        parameter_plans.push(GenericCallVectorParameterPlan {
            target,
            data,
            name_type: store
                .value_symbol_links(target)
                .and_then(|links| links.name_type),
        });
    }
    Ok(PreparedGenericCallVectorSignature {
        mapper_sources: sources.to_vec(),
        mapper_targets: type_arguments.to_vec(),
        instantiated_parameters: Vec::with_capacity(parameter_plans.len()),
        parameter_plans,
        flags,
        declaration,
        min_argument_count,
    })
}

fn publish_prepared_generic_call_vector_signature(
    store: &mut CanonicalTypeMapperStore,
    shape: &GenericCallSignatureShape,
    sources: &[TypeId],
    type_arguments: &[TypeId],
    plan: PreparedGenericCallVectorSignature,
) -> GenericCallVectorCachedInstantiation {
    let PreparedGenericCallVectorSignature {
        mapper_sources,
        mapper_targets,
        parameter_plans,
        mut instantiated_parameters,
        flags,
        declaration,
        min_argument_count,
    } = plan;
    let mapper = store
        .new_type_mapper(mapper_sources, mapper_targets)
        .expect("prevalidated mapper endpoints must remain owned");
    for parameter in parameter_plans {
        let instantiated = store
            .alloc_symbol(parameter.data)
            .expect("reserved transient parameter allocation must succeed");
        assert!(store.set_value_symbol_links(
            instantiated,
            ValueSymbolLinks {
                resolved_type: None,
                target: Some(parameter.target),
                mapper: Some(mapper),
                name_type: parameter.name_type,
                ..ValueSymbolLinks::default()
            },
        ));
        instantiated_parameters.push(instantiated);
    }
    let signature = store
        .alloc_signature(
            flags,
            declaration,
            Vec::new(),
            None,
            instantiated_parameters,
            None,
            None,
            min_argument_count,
        )
        .expect("reserved instantiated signature allocation must succeed");
    assert!(store.set_signature_target_and_mapper(signature, Some(shape.signature), Some(mapper),));
    assert_eq!(
        valid_generic_call_vector_signature_shell(
            store,
            shape,
            sources,
            type_arguments,
            store
                .signature(shape.signature)
                .expect("validated generic signature must remain present"),
            store
                .signature(signature)
                .expect("published instantiated signature must remain present"),
        ),
        Some(mapper),
        "publication must build the exact requested instantiation graph"
    );
    GenericCallVectorCachedInstantiation { signature, mapper }
}

fn validate_existing_generic_call_vector_recovery(
    store: &CanonicalTypeMapperStore,
    shape: &GenericCallSignatureShape,
    sources: &[TypeId],
    type_arguments: &[TypeId],
    signature: SignatureId,
    checked: Option<GenericCallVectorCachedInstantiation>,
) -> Result<GenericCallVectorCachedInstantiation, GenericCallVectorError> {
    let original =
        store
            .signature(shape.signature)
            .ok_or(GenericCallVectorInvariant::InvalidSignature(
                shape.signature,
            ))?;
    let existing =
        store
            .signature(signature)
            .ok_or(GenericCallVectorInvariant::InvalidCallInstantiation {
                target: shape.signature,
                signature,
            })?;
    let mapper = valid_generic_call_vector_signature_shell(
        store,
        shape,
        sources,
        type_arguments,
        original,
        existing,
    )
    .filter(|_| store.cached_signatures_contain(signature) == Some(false))
    .filter(|_| checked.is_none_or(|checked| checked.signature != signature))
    .ok_or(GenericCallVectorInvariant::InvalidCallInstantiation {
        target: shape.signature,
        signature,
    })?;
    Ok(GenericCallVectorCachedInstantiation { signature, mapper })
}

fn materialize_validated_generic_call_vector_checked_instantiation(
    store: &mut CanonicalTypeMapperStore,
    resolution: &GenericCallVectorResolution,
    callable: &ValidatedSingleCallable,
) -> Result<GenericCallVectorMaterialization, GenericCallVectorError> {
    if !generic_call_vector_caches_checked_instantiation(resolution.applicability) {
        return Ok(GenericCallVectorMaterialization::Unmaterialized {
            applicability: resolution.applicability,
        });
    }

    let shape = validate_generic_call_signature_shape(
        store,
        resolution.projection.callee,
        callable,
        resolution.capability.array_targets,
    )?;
    let checked = validate_generic_call_vector_checked_resolution(store, resolution, &shape)?;
    let sources = shape
        .type_parameters
        .iter()
        .map(|parameter| parameter.type_)
        .collect::<Vec<_>>();
    let cached =
        validate_checked_generic_call_vector_instantiation(store, &shape, &sources, &checked)?;
    Ok(GenericCallVectorMaterialization::Reused(cached))
}

fn validate_generic_call_vector_resolution(
    store: &CanonicalTypeMapperStore,
    resolution: &GenericCallVectorResolution,
    shape: &GenericCallSignatureShape,
) -> Result<Vec<TypeId>, GenericCallVectorError> {
    let sources = shape
        .type_parameters
        .iter()
        .map(|parameter| parameter.type_)
        .collect::<Vec<_>>();
    if resolution.capability.checked_return_source != shape.return_type
        || resolution.capability.array_targets != shape.array_targets
        || resolution.projection.generic_signature != shape.signature
        || resolution.projection.type_parameters != sources
    {
        return Err(
            GenericCallVectorInvariant::InvalidCheckedInstantiation(shape.signature).into(),
        );
    }
    let selected = &resolution.projection.instantiation;
    if !valid_generic_call_vector_instantiation(store, selected, sources.len())
        || validate_generic_call_vector_shell(
            store,
            shape,
            &sources,
            &selected.type_arguments,
            selected.signature,
        )? != selected.mapper
        || store.cached_signatures_contain(selected.signature)
            != Some(!resolution.projection.recovery)
    {
        return Err(
            GenericCallVectorInvariant::InvalidCheckedInstantiation(shape.signature).into(),
        );
    }
    if let Some(checked) = &resolution.checked_instantiation {
        validate_checked_generic_call_vector_instantiation(store, shape, &sources, checked)?;
    }
    match resolution.applicability {
        GenericCallVectorApplicability::Applicable => {
            if resolution.projection.recovery
                || resolution.checked_instantiation.as_ref()
                    != Some(&resolution.projection.instantiation)
            {
                return Err(GenericCallVectorInvariant::InvalidCheckedInstantiation(
                    shape.signature,
                )
                .into());
            }
        }
        GenericCallVectorApplicability::TypeArgumentArity {
            minimum,
            maximum,
            actual,
        } => {
            if !resolution.projection.recovery
                || resolution.checked_instantiation.is_some()
                || minimum != minimum_type_argument_count(&shape.type_parameters)
                || maximum != sources.len()
                || actual >= minimum && actual <= maximum
            {
                return Err(GenericCallVectorInvariant::InvalidCheckedInstantiation(
                    shape.signature,
                )
                .into());
            }
        }
        GenericCallVectorApplicability::TooFewArguments { expected, actual } => {
            if !resolution.projection.recovery
                || resolution.checked_instantiation.is_some()
                || expected != shape.minimum_argument_count
                || actual >= expected
            {
                return Err(GenericCallVectorInvariant::InvalidCheckedInstantiation(
                    shape.signature,
                )
                .into());
            }
        }
        GenericCallVectorApplicability::TooManyArguments { expected, actual } => {
            if !resolution.projection.recovery
                || resolution.checked_instantiation.is_some()
                || shape.rest_element_template.is_some()
                || expected != shape.parameter_templates.len()
                || actual <= expected
            {
                return Err(GenericCallVectorInvariant::InvalidCheckedInstantiation(
                    shape.signature,
                )
                .into());
            }
        }
        GenericCallVectorApplicability::ExplicitTypeArgumentConstraint {
            index,
            type_argument,
            constraint,
        } => {
            if !resolution.projection.recovery
                || resolution.checked_instantiation.is_some()
                || store.type_payload(type_argument).is_none()
                || store.type_payload(constraint).is_none()
                || resolution
                    .projection
                    .instantiation
                    .type_arguments
                    .get(index)
                    .copied()
                    != Some(type_argument)
            {
                return Err(GenericCallVectorInvariant::InvalidCheckedInstantiation(
                    shape.signature,
                )
                .into());
            }
        }
        GenericCallVectorApplicability::ArgumentNotAssignable {
            index,
            argument_type,
            parameter_type,
        } => {
            let Some(checked) = resolution.checked_instantiation.as_ref() else {
                return Err(GenericCallVectorInvariant::InvalidCheckedInstantiation(
                    shape.signature,
                )
                .into());
            };
            let fixed_parameter_count = shape.parameter_templates.len()
                - usize::from(shape.rest_element_template.is_some());
            let expected_parameter = if index < fixed_parameter_count {
                resolved_generic_call_vector_parameter(store, checked.signature, index)
            } else {
                resolved_generic_call_vector_parameter(
                    store,
                    checked.signature,
                    fixed_parameter_count,
                )
                .and_then(|rest| {
                    shape.array_targets.and_then(|targets| {
                        store
                            .canonical_array_reference_with_targets(targets, rest)
                            .ok()
                            .flatten()
                            .map(|reference| reference.element_type)
                    })
                })
            };
            if !resolution.projection.recovery
                || store.type_payload(argument_type).is_none()
                || store.type_payload(parameter_type).is_none()
                || checked.signature == resolution.projection.instantiation.signature
                || expected_parameter != Some(parameter_type)
            {
                return Err(GenericCallVectorInvariant::InvalidCheckedInstantiation(
                    shape.signature,
                )
                .into());
            }
        }
    }
    Ok(sources)
}

fn validate_checked_generic_call_vector_instantiation(
    store: &CanonicalTypeMapperStore,
    shape: &GenericCallSignatureShape,
    sources: &[TypeId],
    instantiation: &GenericCallVectorInstantiation,
) -> Result<GenericCallVectorCachedInstantiation, GenericCallVectorError> {
    if !valid_generic_call_vector_instantiation(store, instantiation, sources.len())
        || validate_generic_call_vector_shell(
            store,
            shape,
            sources,
            &instantiation.type_arguments,
            instantiation.signature,
        )? != instantiation.mapper
        || store.cached_signatures_contain(instantiation.signature) != Some(true)
        || !matches!(
            store.cached_signature(
                shape.signature,
                type_list_key(&instantiation.type_arguments),
                &instantiation.type_arguments,
            ),
            CachedSignatureLookup::Hit(signature) if signature == instantiation.signature
        )
    {
        return Err(
            GenericCallVectorInvariant::InvalidCheckedInstantiation(shape.signature).into(),
        );
    }
    Ok(GenericCallVectorCachedInstantiation {
        signature: instantiation.signature,
        mapper: instantiation.mapper,
    })
}

fn resolved_generic_call_vector_parameter(
    store: &CanonicalTypeMapperStore,
    signature: SignatureId,
    index: usize,
) -> Option<TypeId> {
    store
        .signature(signature)
        .and_then(|signature| signature.parameters().get(index))
        .and_then(|parameter| store.value_symbol_links(*parameter))
        .and_then(|links| links.resolved_type)
}

fn validate_generic_call_vector_checked_resolution(
    store: &CanonicalTypeMapperStore,
    resolution: &GenericCallVectorResolution,
    shape: &GenericCallSignatureShape,
) -> Result<GenericCallVectorInstantiation, GenericCallVectorError> {
    validate_generic_call_vector_resolution(store, resolution, shape)?;
    if !generic_call_vector_caches_checked_instantiation(resolution.applicability) {
        return Err(
            GenericCallVectorInvariant::InvalidCheckedInstantiation(shape.signature).into(),
        );
    }
    resolution.checked_instantiation.clone().ok_or_else(|| {
        GenericCallVectorInvariant::InvalidCheckedInstantiation(shape.signature).into()
    })
}

#[allow(clippy::too_many_arguments)]
fn generic_call_type_instantiation_matches(
    store: &CanonicalTypeMapperStore,
    array_targets: Option<CanonicalArrayTargets>,
    template: TypeId,
    actual: TypeId,
    sources: &[TypeId],
    targets: &[TypeId],
    active_templates: &mut Vec<TypeId>,
) -> bool {
    // A recovering instantiation substitutes the canonical error type at the
    // exact recursive boundary where the budget is exhausted. That boundary
    // is valid at any depth, including inside retained Array/union wrappers.
    if store
        .intrinsic_bootstrap()
        .is_some_and(|bootstrap| actual == bootstrap.error_type)
    {
        return true;
    }
    if let Some(index) = sources.iter().position(|source| *source == template) {
        return targets.get(index).copied() == Some(actual);
    }
    if valid_fixed_generic_source_parameter_type(store, template) {
        return template == actual;
    }
    let Some(template_record) = store.type_payload(template) else {
        return false;
    };
    match template_record.data() {
        TypeData::Intrinsic(_) | TypeData::Literal(_) | TypeData::UniqueEsSymbol(_) => {
            template == actual
        }
        TypeData::Union(union) if template_record.alias().is_none() && union.origin.is_none() => {
            generic_call_union_instantiation_matches(
                store,
                array_targets,
                &union.union.types,
                actual,
                sources,
                targets,
                active_templates,
            )
        }
        TypeData::TypeReference(_) | TypeData::Interface(_) => {
            if active_templates.contains(&template) {
                return false;
            }

            if let Some(array_targets) = array_targets {
                let Ok(template_reference) =
                    store.canonical_array_reference_with_targets(array_targets, template)
                else {
                    return false;
                };
                if let Some(template_reference) = template_reference {
                    let Ok(Some(actual_reference)) =
                        store.canonical_array_reference_with_targets(array_targets, actual)
                    else {
                        return false;
                    };
                    if template_reference.array_literal
                        || actual_reference.array_literal
                        || template_reference.readonly != actual_reference.readonly
                    {
                        return false;
                    }
                    active_templates.push(template);
                    let matches = generic_call_type_instantiation_matches(
                        store,
                        Some(array_targets),
                        template_reference.element_type,
                        actual_reference.element_type,
                        sources,
                        targets,
                        active_templates,
                    );
                    active_templates.pop();
                    return matches;
                }
            }

            let (Ok(template_reference), Ok(actual_reference)) = (
                validate_direct_generic_reference(store, template),
                validate_direct_generic_reference(store, actual),
            ) else {
                return false;
            };
            if template_reference.target != actual_reference.target
                || template_reference.type_arguments.len() != actual_reference.type_arguments.len()
            {
                return false;
            }
            active_templates.push(template);
            let matches = template_reference
                .type_arguments
                .into_iter()
                .zip(actual_reference.type_arguments)
                .all(|(template, actual)| {
                    generic_call_type_instantiation_matches(
                        store,
                        array_targets,
                        template,
                        actual,
                        sources,
                        targets,
                        active_templates,
                    )
                });
            active_templates.pop();
            matches
        }
        _ => false,
    }
}

fn generic_call_union_instantiation_matches(
    store: &CanonicalTypeMapperStore,
    array_targets: Option<CanonicalArrayTargets>,
    templates: &[TypeId],
    actual: TypeId,
    sources: &[TypeId],
    targets: &[TypeId],
    active_templates: &mut Vec<TypeId>,
) -> bool {
    let Some(actual_record) = store.type_payload(actual) else {
        return false;
    };
    let actual_types = match actual_record.data() {
        TypeData::Union(union)
            if actual_record.alias().is_none()
                && union.origin.is_none()
                && match array_targets {
                    Some(array_targets) => store
                        .validate_cached_union_result_with_array_targets(
                            array_targets,
                            actual,
                            None,
                        )
                        .is_ok(),
                    None => store.validate_cached_union_result(actual, None).is_ok(),
                } =>
        {
            union.union.types.as_slice()
        }
        _ => std::slice::from_ref(&actual),
    };
    if actual_record.flags().intersects(TypeFlags::ANY_OR_UNKNOWN)
        && templates.iter().copied().any(|template| {
            generic_call_type_instantiation_matches(
                store,
                array_targets,
                template,
                actual,
                sources,
                targets,
                active_templates,
            )
        })
    {
        return true;
    }
    if actual_types.iter().copied().any(|candidate| {
        !templates.iter().copied().any(|template| {
            generic_call_union_template_matches(
                store,
                array_targets,
                template,
                candidate,
                sources,
                targets,
                active_templates,
            )
        })
    }) {
        return false;
    }
    templates.iter().copied().all(|template| {
        if let Some(mapped) =
            generic_call_mapped_union_constituents(store, array_targets, template, sources, targets)
        {
            return mapped.iter().copied().all(|member| {
                actual_types.iter().copied().any(|candidate| {
                    generic_call_type_instantiation_matches(
                        store,
                        array_targets,
                        member,
                        candidate,
                        sources,
                        targets,
                        active_templates,
                    )
                }) || generic_call_mapped_template_is_redundant(
                    store,
                    member,
                    actual_types,
                    sources,
                    targets,
                )
            });
        }
        actual_types.iter().copied().any(|candidate| {
            generic_call_union_template_matches(
                store,
                array_targets,
                template,
                candidate,
                sources,
                targets,
                active_templates,
            )
        }) || generic_call_mapped_template_is_redundant(
            store,
            template,
            actual_types,
            sources,
            targets,
        )
    })
}

#[allow(clippy::too_many_arguments)]
fn generic_call_union_template_matches(
    store: &CanonicalTypeMapperStore,
    array_targets: Option<CanonicalArrayTargets>,
    template: TypeId,
    actual: TypeId,
    sources: &[TypeId],
    targets: &[TypeId],
    active_templates: &mut Vec<TypeId>,
) -> bool {
    if generic_call_type_instantiation_matches(
        store,
        array_targets,
        template,
        actual,
        sources,
        targets,
        active_templates,
    ) {
        return true;
    }
    generic_call_mapped_union_constituents(store, array_targets, template, sources, targets)
        .is_some_and(|constituents| constituents.contains(&actual))
}

fn generic_call_mapped_union_constituents<'store>(
    store: &'store CanonicalTypeMapperStore,
    array_targets: Option<CanonicalArrayTargets>,
    template: TypeId,
    sources: &[TypeId],
    targets: &[TypeId],
) -> Option<&'store [TypeId]> {
    let mapped = sources
        .iter()
        .position(|source| *source == template)
        .and_then(|index| targets.get(index))
        .copied()?;
    let record = store.type_payload(mapped)?;
    let TypeData::Union(union) = record.data() else {
        return None;
    };
    if record.alias().is_some()
        || union.origin.is_some() && !authenticated_nongeneric_keyof_union(store, mapped)
        || match array_targets {
            Some(array_targets) => store
                .validate_cached_union_result_with_array_targets(array_targets, mapped, None)
                .is_err(),
            None => store.validate_cached_union_result(mapped, None).is_err(),
        }
    {
        return None;
    }
    Some(&union.union.types)
}

fn generic_call_mapped_template_is_redundant(
    store: &CanonicalTypeMapperStore,
    template: TypeId,
    actual_types: &[TypeId],
    sources: &[TypeId],
    targets: &[TypeId],
) -> bool {
    let mapped = sources
        .iter()
        .position(|source| *source == template)
        .and_then(|index| targets.get(index))
        .copied()
        .unwrap_or(template);
    let Some(record) = store.type_payload(mapped) else {
        return false;
    };
    if record.flags().intersects(TypeFlags::NEVER) {
        return true;
    }
    let TypeData::Literal(literal) = record.data() else {
        return false;
    };
    actual_types.iter().copied().any(|actual| {
        actual == literal.regular_type
            || store.type_payload(actual).is_some_and(|actual| {
                record.flags().intersects(TypeFlags::STRING_LITERAL)
                    && actual.flags().intersects(TypeFlags::STRING)
                    || record.flags().intersects(TypeFlags::NUMBER_LITERAL)
                        && actual.flags().intersects(TypeFlags::NUMBER)
                    || record.flags().intersects(TypeFlags::BIG_INT_LITERAL)
                        && actual.flags().intersects(TypeFlags::BIG_INT)
            })
    })
}

fn valid_generic_call_vector_instantiation(
    store: &CanonicalTypeMapperStore,
    instantiation: &GenericCallVectorInstantiation,
    type_parameter_count: usize,
) -> bool {
    if instantiation.type_arguments.len() != type_parameter_count
        || instantiation
            .type_arguments
            .iter()
            .any(|type_| store.type_payload(*type_).is_none())
    {
        return false;
    }
    store.signature(instantiation.signature).is_some()
        && store.mapper_payload(instantiation.mapper).is_some()
}

fn cached_generic_call_vector_instantiation_from_lookup(
    store: &CanonicalTypeMapperStore,
    shape: &GenericCallSignatureShape,
    sources: &[TypeId],
    type_arguments: &[TypeId],
    lookup: CachedSignatureLookup,
) -> Result<Option<GenericCallVectorCachedInstantiation>, GenericCallVectorError> {
    let cached = match lookup {
        CachedSignatureLookup::Missing => return Ok(None),
        CachedSignatureLookup::Hit(signature) => signature,
        CachedSignatureLookup::HashCollision(cached) => {
            return Err(
                GenericCallVectorInvariant::InstantiationCacheHashCollision {
                    target: shape.signature,
                    cached,
                }
                .into(),
            );
        }
        CachedSignatureLookup::Invalid => {
            return Err(
                GenericCallVectorInvariant::InvalidCheckedInstantiation(shape.signature).into(),
            );
        }
    };
    let original =
        store
            .signature(shape.signature)
            .ok_or(GenericCallVectorInvariant::InvalidSignature(
                shape.signature,
            ))?;
    let signature =
        store
            .signature(cached)
            .ok_or(GenericCallVectorInvariant::InvalidCachedInstantiation {
                target: shape.signature,
                signature: cached,
            })?;
    let mapper = valid_generic_call_vector_signature_shell(
        store,
        shape,
        sources,
        type_arguments,
        original,
        signature,
    )
    .ok_or(GenericCallVectorInvariant::InvalidCachedInstantiation {
        target: shape.signature,
        signature: cached,
    })?;
    Ok(Some(GenericCallVectorCachedInstantiation {
        signature: cached,
        mapper,
    }))
}

fn valid_generic_call_vector_signature_shell(
    store: &CanonicalTypeMapperStore,
    shape: &GenericCallSignatureShape,
    sources: &[TypeId],
    type_arguments: &[TypeId],
    original: &super::signatures::Signature,
    signature: &super::signatures::Signature,
) -> Option<TypeMapperId> {
    let mapper = signature.mapper()?;
    if sources.len() != shape.type_parameters.len()
        || type_arguments.len() != sources.len()
        || sources
            .iter()
            .zip(&shape.type_parameters)
            .any(|(source, parameter)| *source != parameter.type_)
        || signature.flags() != original.flags() & SignatureFlags::PROPAGATING_FLAGS
        || signature.declaration() != original.declaration()
        || !signature.type_parameters().is_empty()
        || signature.this_parameter().is_some()
        || signature.parameters().len() != original.parameters().len()
        || signature.resolved_return_type().is_some_and(|resolved| {
            !generic_call_type_instantiation_matches(
                store,
                shape.array_targets,
                shape.return_type,
                resolved,
                sources,
                type_arguments,
                &mut Vec::new(),
            )
        })
        || signature.resolved_type_predicate().is_some()
        || signature.min_argument_count() != original.min_argument_count()
        || signature.resolved_min_argument_count() != -1
        || signature.target() != Some(shape.signature)
        || store.type_mapper_has_exact_endpoints(mapper, sources, type_arguments) != Some(true)
        || signature.isolated_signature_type().is_some()
        || signature.composite().is_some()
        || signature
            .parameters()
            .iter()
            .copied()
            .zip(original.parameters().iter().copied())
            .zip(shape.parameter_templates.iter().copied())
            .any(|((parameter, target), template)| {
                !cached_instantiated_parameter_shell(
                    store,
                    parameter,
                    target,
                    mapper,
                    template,
                    sources,
                    type_arguments,
                    shape.array_targets,
                )
            })
    {
        return None;
    }
    Some(mapper)
}

#[allow(clippy::too_many_arguments)]
fn cached_instantiated_parameter_shell(
    store: &CanonicalTypeMapperStore,
    parameter: SemanticSymbolId,
    target: SemanticSymbolId,
    mapper: TypeMapperId,
    template: TypeId,
    sources: &[TypeId],
    type_arguments: &[TypeId],
    array_targets: Option<CanonicalArrayTargets>,
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
        && store.value_symbol_links(parameter).is_some_and(|links| {
            links
                == &ValueSymbolLinks {
                    resolved_type: links.resolved_type,
                    target: Some(target),
                    mapper: Some(mapper),
                    name_type,
                    ..ValueSymbolLinks::default()
                }
                && links.resolved_type.is_none_or(|resolved| {
                    generic_call_type_instantiation_matches(
                        store,
                        array_targets,
                        template,
                        resolved,
                        sources,
                        type_arguments,
                        &mut Vec::new(),
                    )
                })
        })
}

fn validate_generic_call_vector_shell(
    store: &CanonicalTypeMapperStore,
    shape: &GenericCallSignatureShape,
    sources: &[TypeId],
    type_arguments: &[TypeId],
    signature: SignatureId,
) -> Result<TypeMapperId, GenericCallVectorError> {
    let original =
        store
            .signature(shape.signature)
            .ok_or(GenericCallVectorInvariant::InvalidSignature(
                shape.signature,
            ))?;
    let instantiated = store.signature(signature).ok_or(
        GenericCallVectorInvariant::InvalidCachedInstantiation {
            target: shape.signature,
            signature,
        },
    )?;
    valid_generic_call_vector_signature_shell(
        store,
        shape,
        sources,
        type_arguments,
        original,
        instantiated,
    )
    .ok_or_else(|| {
        GenericCallVectorInvariant::InvalidCachedInstantiation {
            target: shape.signature,
            signature,
        }
        .into()
    })
}

fn demand_generic_call_vector_parameter(
    store: &mut CanonicalTypeMapperStore,
    shape: &GenericCallSignatureShape,
    sources: &[TypeId],
    type_arguments: &[TypeId],
    signature: SignatureId,
    index: usize,
    session: &mut InstantiationSession,
) -> Result<TypeId, GenericCallVectorError> {
    let mapper =
        validate_generic_call_vector_shell(store, shape, sources, type_arguments, signature)?;
    let parameter = store
        .signature(signature)
        .and_then(|signature| signature.parameters().get(index))
        .copied()
        .ok_or(GenericCallVectorInvariant::InvalidCachedInstantiation {
            target: shape.signature,
            signature,
        })?;
    let mut links = store.value_symbol_links(parameter).cloned().ok_or(
        GenericCallVectorInvariant::InvalidCachedInstantiation {
            target: shape.signature,
            signature,
        },
    )?;
    if let Some(resolved) = links.resolved_type {
        return Ok(resolved);
    }
    let template = shape.parameter_templates.get(index).copied().ok_or(
        GenericCallVectorInvariant::InvalidCachedInstantiation {
            target: shape.signature,
            signature,
        },
    )?;
    let resolved = if valid_fixed_generic_source_parameter_type(store, template) {
        template
    } else {
        instantiate_type_with_session(store, template, mapper, shape.array_targets, session)?
    };
    links.resolved_type = Some(resolved);
    assert!(
        store.set_value_symbol_links(parameter, links),
        "the warm-validated transient parameter accepts its instantiated type"
    );
    Ok(resolved)
}

fn demand_generic_call_vector_return(
    store: &mut CanonicalTypeMapperStore,
    shape: &GenericCallSignatureShape,
    sources: &[TypeId],
    type_arguments: &[TypeId],
    signature: SignatureId,
    session: &mut InstantiationSession,
) -> Result<TypeId, GenericCallVectorError> {
    let mapper =
        validate_generic_call_vector_shell(store, shape, sources, type_arguments, signature)?;
    if let Some(resolved) = store
        .signature(signature)
        .and_then(super::signatures::Signature::resolved_return_type)
    {
        return Ok(resolved);
    }
    let resolved = instantiate_type_with_session(
        store,
        shape.return_type,
        mapper,
        shape.array_targets,
        session,
    )?;
    assert!(
        store.set_signature_resolved_return_type(signature, Some(resolved)),
        "the warm-validated instantiated signature accepts its return type"
    );
    Ok(resolved)
}

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
    Instantiation(InstantiationError),
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

impl From<InstantiationError> for IdentityGenericCallError {
    fn from(error: InstantiationError) -> Self {
        Self::Instantiation(error)
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

/// One host-proven exported declared-property-object root that semantic-only
/// inference must otherwise keep opaque. The candidate is exact and the fields
/// remain private so only the source entry point can mint this proof.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct SourceDeclaredInferenceProof {
    candidate: TypeId,
}

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
struct SourceIdentityInferenceProofs {
    argument: Option<SourceDeclaredInferenceProof>,
    type_argument: Option<SourceDeclaredInferenceProof>,
}

/// Resolves the first generic call branch through the store's callable
/// provider and authoritative relation context.
pub(super) fn resolve_identity_generic_call(
    store: &mut CanonicalTypeMapperStore,
    global_types: &CanonicalGlobalTypes,
    strict_function_types: bool,
    request: IdentityGenericCallRequest<'_>,
) -> Result<IdentityGenericCallResolution, IdentityGenericCallError> {
    let mut session = InstantiationSession::new(InstantiationLimits::default());
    resolve_identity_generic_call_with_session(
        store,
        global_types,
        strict_function_types,
        request,
        None,
        &mut session,
    )
}

pub(super) fn resolve_identity_generic_call_with_session(
    store: &mut CanonicalTypeMapperStore,
    global_types: &CanonicalGlobalTypes,
    strict_function_types: bool,
    request: IdentityGenericCallRequest<'_>,
    existing_call_signature: Option<SignatureId>,
    session: &mut InstantiationSession,
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
        existing_call_signature,
        session,
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

/// Resolves the identity slice for source syntax with one retained-host
/// capability: an exact exported, non-generic type-alias object or simple
/// interface may be used as the root inference candidate after host-aware
/// property-graph validation. Semantic-only callers retain
/// [`resolve_identity_generic_call`]'s behavior.
pub(super) fn resolve_source_identity_generic_call(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    global_types: &CanonicalGlobalTypes,
    strict_function_types: bool,
    request: IdentityGenericCallRequest<'_>,
) -> Result<IdentityGenericCallResolution, IdentityGenericCallError> {
    let mut session = InstantiationSession::new(InstantiationLimits::default());
    resolve_source_identity_generic_call_with_session(
        store,
        host,
        global_types,
        strict_function_types,
        request,
        None,
        &mut session,
    )
}

#[allow(clippy::too_many_arguments)]
pub(super) fn resolve_source_identity_generic_call_with_session(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    global_types: &CanonicalGlobalTypes,
    strict_function_types: bool,
    request: IdentityGenericCallRequest<'_>,
    existing_call_signature: Option<SignatureId>,
    session: &mut InstantiationSession,
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
    let argument = request.arguments[0];
    let proofs = SourceIdentityInferenceProofs {
        argument: source_declared_inference_proof(store, host, argument)?,
        type_argument: request
            .explicit_type_arguments
            .map(|type_arguments| source_declared_inference_proof(store, host, type_arguments[0]))
            .transpose()?
            .flatten(),
    };
    let prepared = prepare_validated_identity_call_with_proofs(
        store,
        request,
        &callable,
        cache_provenance,
        proofs,
    )?;
    resolve_prepared_identity_call(
        store,
        prepared,
        existing_call_signature,
        session,
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

fn source_declared_inference_proof(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    candidate: TypeId,
) -> Result<Option<SourceDeclaredInferenceProof>, IdentityGenericCallError> {
    if !matches!(
        validate_inference_leaf(store, candidate),
        Err(NakedTypeInferenceError::UnsupportedCandidate(failed)) if failed == candidate
    ) || store.type_payload(candidate).is_none_or(|record| {
        !matches!(record.data(), TypeData::Interface(_))
            && (!matches!(record.data(), TypeData::Object(_)) || record.alias().is_none())
    }) {
        return Ok(None);
    }
    if !source_declared_inference_candidate_is_exported(store, candidate) {
        return Ok(None);
    }
    let Some(_) = store.resolved_declared_property_object(host, candidate)? else {
        return Ok(None);
    };
    Ok(Some(SourceDeclaredInferenceProof { candidate }))
}

/// The source-only override exists solely for a cross-module boundary. Local
/// declared roots already belong to the ordinary inference domain; requiring
/// the exact alias/interface declaration to be exported prevents a nested
/// modifier-free declaration from acquiring this capability.
pub(super) fn source_declared_inference_candidate_is_exported(
    store: &CanonicalTypeMapperStore,
    candidate: TypeId,
) -> bool {
    let Some(record) = store.type_payload(candidate) else {
        return false;
    };
    let (symbol, expected_kind) = match record.data() {
        TypeData::Object(_) => {
            let Some(symbol) = record
                .alias()
                .and_then(|alias| store.type_alias(alias))
                .and_then(super::type_records::TypeAlias::symbol)
            else {
                return false;
            };
            (symbol, SyntaxKind::TypeAliasDeclaration)
        }
        TypeData::Interface(_) => {
            let Some(symbol) = record.symbol() else {
                return false;
            };
            (symbol, SyntaxKind::InterfaceDeclaration)
        }
        _ => return false,
    };
    let Some(symbol_record) = store.symbol(symbol) else {
        return false;
    };
    let Some([declaration]) = symbol_record.declarations() else {
        return false;
    };
    store.get_merged_symbol(symbol) == Some(symbol)
        && store.source_node_kind(*declaration) == Some(expected_kind)
        && store.source_node_is_exported(*declaration) == Some(true)
}

fn identity_type_parameter_cache_provenance(
    store: &CanonicalTypeMapperStore,
    callee: TypeId,
    callable: &ValidatedSingleCallable,
) -> IdentityTypeParameterCacheProvenance {
    let Some(provenance) = store.source_callable_provenance(callee) else {
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
    let Some([type_parameter_provenance]) =
        store.source_callable_type_parameters(callable.signature)
    else {
        return IdentityTypeParameterCacheProvenance::RequireResolvedCaches;
    };
    if provenance.signature != callable.signature
        || type_parameter_provenance.type_parameter != *type_parameter
        || type_parameter_provenance.symbol != type_parameter_owner
        || type_parameter_provenance.constraint.is_some()
        || type_parameter_provenance.default_type.is_some()
        || store.source_callable_type_for_signature(callable.signature) != Some(callee)
        || store
            .symbol(type_parameter_owner)
            .and_then(|symbol| symbol.declarations())
            != Some(&[type_parameter_provenance.declaration])
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
    let mut session = InstantiationSession::new(InstantiationLimits::default());
    resolve_validated_identity_call(
        store,
        request,
        callable,
        cache_provenance,
        None,
        &mut session,
        |_, _, _| Ok(true),
    )
}

fn resolve_validated_identity_call(
    store: &mut CanonicalTypeMapperStore,
    request: IdentityGenericCallRequest<'_>,
    callable: &ValidatedSingleCallable,
    cache_provenance: IdentityTypeParameterCacheProvenance,
    existing_call_signature: Option<SignatureId>,
    session: &mut InstantiationSession,
    is_assignable: impl FnMut(
        &mut CanonicalTypeMapperStore,
        TypeId,
        TypeId,
    ) -> Result<bool, RelationUnavailable>,
) -> Result<IdentityGenericCallResolution, IdentityGenericCallError> {
    let prepared = prepare_validated_identity_call_with_proofs(
        store,
        request,
        callable,
        cache_provenance,
        SourceIdentityInferenceProofs::default(),
    )?;
    resolve_prepared_identity_call(
        store,
        prepared,
        existing_call_signature,
        session,
        is_assignable,
    )
}

fn resolve_prepared_identity_call(
    store: &mut CanonicalTypeMapperStore,
    prepared: PreparedIdentityGenericCall,
    existing_call_signature: Option<SignatureId>,
    session: &mut InstantiationSession,
    mut is_assignable: impl FnMut(
        &mut CanonicalTypeMapperStore,
        TypeId,
        TypeId,
    ) -> Result<bool, RelationUnavailable>,
) -> Result<IdentityGenericCallResolution, IdentityGenericCallError> {
    let shape = identity_generic_call_vector_shape(store, prepared.shape).map_err(|error| {
        map_identity_vector_error(error, prepared.shape, prepared.type_argument)
    })?;
    let sources = [prepared.shape.type_parameter];
    let type_arguments = [prepared.type_argument];
    // Checked shells are cached before applicability, matching
    // getSignatureInstantiationWithoutFillingInTypeArguments.
    let (checked, _) =
        get_or_create_checked_generic_call_vector_shell(store, &shape, &sources, &type_arguments)
            .map_err(|error| {
            map_identity_vector_error(error, prepared.shape, prepared.type_argument)
        })?;
    let parameter_type = demand_generic_call_vector_parameter(
        store,
        &shape,
        &sources,
        &type_arguments,
        checked.signature,
        0,
        session,
    )
    .map_err(|error| map_identity_vector_error(error, prepared.shape, prepared.type_argument))?;
    let applicability = check_identity_argument_applicability(
        prepared.argument,
        parameter_type,
        |source, target| is_assignable(store, source, target),
    )?;
    let selected = if applicability == DirectCallApplicability::Applicable {
        if existing_call_signature.is_some_and(|existing| existing != checked.signature) {
            return Err(IdentityGenericCallInvariant::InvalidCachedInstantiation {
                target: prepared.shape.signature,
                type_argument: prepared.type_argument,
                signature: existing_call_signature
                    .expect("the mismatching existing signature is present"),
            }
            .into());
        }
        checked
    } else {
        get_or_create_generic_call_vector_recovery_shell(
            store,
            &shape,
            &sources,
            &type_arguments,
            existing_call_signature,
            Some(checked),
        )
        .map_err(|error| map_identity_vector_error(error, prepared.shape, prepared.type_argument))?
    };
    Ok(project_prepared_identity_call(
        prepared,
        selected,
        parameter_type,
        applicability,
    ))
}

fn prepare_validated_identity_call(
    store: &CanonicalTypeMapperStore,
    request: IdentityGenericCallRequest<'_>,
    callable: &ValidatedSingleCallable,
    cache_provenance: IdentityTypeParameterCacheProvenance,
) -> Result<PreparedIdentityGenericCall, IdentityGenericCallError> {
    prepare_validated_identity_call_with_proofs(
        store,
        request,
        callable,
        cache_provenance,
        SourceIdentityInferenceProofs::default(),
    )
}

fn prepare_validated_identity_call_with_proofs(
    store: &CanonicalTypeMapperStore,
    request: IdentityGenericCallRequest<'_>,
    callable: &ValidatedSingleCallable,
    cache_provenance: IdentityTypeParameterCacheProvenance,
    proofs: SourceIdentityInferenceProofs,
) -> Result<PreparedIdentityGenericCall, IdentityGenericCallError> {
    validate_request_form(store, request)?;
    let shape =
        validate_identity_signature_shape(store, request.callee, callable, cache_provenance)?;
    let argument = request.arguments[0];
    let type_argument = match request.explicit_type_arguments {
        Some(type_arguments) => {
            let type_argument = type_arguments[0];
            validate_inference_leaf_with_source_proof(store, type_argument, proofs.type_argument)
                .map_err(|error| map_inference_leaf_error(error, type_argument, true))?;
            type_argument
        }
        None => match proofs.argument {
            Some(proof) => {
                validate_inference_leaf_with_source_proof(store, argument, Some(proof))
                    .map_err(|error| map_inference_leaf_error(error, argument, false))?;
                argument
            }
            None => infer_naked_type_parameter(store, argument)
                .map_err(|error| map_inference_leaf_error(error, argument, false))?,
        },
    };
    validate_inference_leaf_with_source_proof(store, argument, proofs.argument)
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

fn validate_inference_leaf_with_source_proof(
    store: &CanonicalTypeMapperStore,
    candidate: TypeId,
    proof: Option<SourceDeclaredInferenceProof>,
) -> Result<(), NakedTypeInferenceError> {
    match validate_inference_leaf(store, candidate) {
        Err(NakedTypeInferenceError::UnsupportedCandidate(failed))
            if failed == candidate && proof.is_some_and(|proof| proof.candidate == candidate) =>
        {
            Ok(())
        }
        result => result,
    }
}

fn project_prepared_identity_call(
    prepared: PreparedIdentityGenericCall,
    selected: GenericCallVectorCachedInstantiation,
    parameter_type: TypeId,
    applicability: DirectCallApplicability,
) -> IdentityGenericCallResolution {
    let projection = IdentityGenericCallProjection {
        callee: prepared.callee,
        generic_signature: prepared.shape.signature,
        signature: selected.signature,
        mapper: selected.mapper,
        type_parameter: prepared.shape.type_parameter,
        type_argument: prepared.type_argument,
        argument_target: DirectCallArgumentTarget {
            index: 0,
            argument_type: prepared.argument,
            parameter_type,
        },
        return_type: prepared.type_argument,
        return_kind: prepared.return_kind,
    };
    IdentityGenericCallResolution {
        projection,
        applicability,
    }
}

fn identity_generic_call_vector_shape(
    store: &CanonicalTypeMapperStore,
    shape: IdentitySignatureShape,
) -> Result<GenericCallSignatureShape, GenericCallVectorError> {
    let no_constraint = store
        .intrinsic_bootstrap()
        .map(|bootstrap| bootstrap.no_constraint_type)
        .ok_or(GenericCallVectorInvariant::MissingBootstrap)?;
    Ok(GenericCallSignatureShape {
        signature: shape.signature,
        type_parameters: vec![GenericCallTypeParameter {
            type_: shape.type_parameter,
            constraint: None,
            default_type: None,
            base_constraint: no_constraint,
        }],
        parameter_templates: vec![shape.type_parameter],
        rest_element_template: None,
        minimum_argument_count: 1,
        return_type: shape.type_parameter,
        array_targets: None,
    })
}

fn map_identity_vector_error(
    error: GenericCallVectorError,
    shape: IdentitySignatureShape,
    type_argument: TypeId,
) -> IdentityGenericCallError {
    match error {
        GenericCallVectorError::Instantiation(error) => {
            IdentityGenericCallError::Instantiation(error)
        }
        GenericCallVectorError::Relation(error) => IdentityGenericCallError::Relation(error),
        GenericCallVectorError::Invariant(GenericCallVectorInvariant::Capacity(signature)) => {
            IdentityGenericCallInvariant::Capacity(signature).into()
        }
        GenericCallVectorError::Invariant(
            GenericCallVectorInvariant::InstantiationCacheHashCollision { target, cached },
        ) => IdentityGenericCallInvariant::InstantiationCacheHashCollision {
            target,
            type_argument,
            cached,
        }
        .into(),
        GenericCallVectorError::Invariant(GenericCallVectorInvariant::InvalidSignature(
            signature,
        )) => IdentityGenericCallInvariant::InvalidSignature(signature).into(),
        GenericCallVectorError::Invariant(
            GenericCallVectorInvariant::InvalidCachedInstantiation { target, signature }
            | GenericCallVectorInvariant::InvalidCallInstantiation { target, signature },
        ) => IdentityGenericCallInvariant::InvalidCachedInstantiation {
            target,
            type_argument,
            signature,
        }
        .into(),
        GenericCallVectorError::Invariant(_) => {
            IdentityGenericCallInvariant::InvalidCachedInstantiation {
                target: shape.signature,
                type_argument,
                signature: shape.signature,
            }
            .into()
        }
        GenericCallVectorError::Unsupported(_) | GenericCallVectorError::Inference(_) => {
            IdentityGenericCallInvariant::InvalidSignature(shape.signature).into()
        }
    }
}

/// Resolves the selected identity signature's return through the same lazy
/// shell primitive used by the full-vector path.
pub(super) fn demand_identity_generic_call_selected_return(
    store: &mut CanonicalTypeMapperStore,
    resolution: &IdentityGenericCallResolution,
    session: &mut InstantiationSession,
) -> Result<(TypeId, DirectCallReturnKind), IdentityGenericCallError> {
    let callee = resolution.projection.callee;
    let callable = match validate_stored_single_callable(store, callee) {
        StoredSingleCallableValidation::NotCallable => {
            return Err(IdentityGenericCallUnsupported::NotExactSingleCallable(callee).into());
        }
        StoredSingleCallableValidation::Pending { .. } => {
            return Err(IdentityGenericCallUnsupported::PendingCallable(callee).into());
        }
        StoredSingleCallableValidation::Malformed { .. } => {
            return Err(IdentityGenericCallInvariant::MalformedCallable(callee).into());
        }
        StoredSingleCallableValidation::Valid { callable, .. } => callable,
    };
    let provenance = identity_type_parameter_cache_provenance(store, callee, &callable);
    demand_validated_identity_generic_call_selected_return(
        store, resolution, &callable, provenance, session,
    )
}

pub(super) fn demand_identity_generic_call_return_with_session(
    store: &mut CanonicalTypeMapperStore,
    resolution: &IdentityGenericCallResolution,
    session: &mut InstantiationSession,
) -> Result<TypeId, IdentityGenericCallError> {
    demand_identity_generic_call_selected_return(store, resolution, session)
        .map(|(return_type, _)| return_type)
}

fn demand_validated_identity_generic_call_selected_return(
    store: &mut CanonicalTypeMapperStore,
    resolution: &IdentityGenericCallResolution,
    callable: &ValidatedSingleCallable,
    provenance: IdentityTypeParameterCacheProvenance,
    session: &mut InstantiationSession,
) -> Result<(TypeId, DirectCallReturnKind), IdentityGenericCallError> {
    let callee = resolution.projection.callee;
    let identity_shape = validate_identity_signature_shape(store, callee, callable, provenance)?;
    let shape = identity_generic_call_vector_shape(store, identity_shape).map_err(|error| {
        map_identity_vector_error(error, identity_shape, resolution.projection.type_argument)
    })?;
    let sources = [identity_shape.type_parameter];
    let type_arguments = [resolution.projection.type_argument];
    let mapper = validate_generic_call_vector_shell(
        store,
        &shape,
        &sources,
        &type_arguments,
        resolution.projection.signature,
    )
    .map_err(|error| {
        map_identity_vector_error(error, identity_shape, resolution.projection.type_argument)
    })?;
    if mapper != resolution.projection.mapper
        || store.cached_signatures_contain(resolution.projection.signature)
            != Some(resolution.applicability == DirectCallApplicability::Applicable)
    {
        return Err(IdentityGenericCallInvariant::InvalidCachedInstantiation {
            target: identity_shape.signature,
            type_argument: resolution.projection.type_argument,
            signature: resolution.projection.signature,
        }
        .into());
    }
    let return_type = demand_generic_call_vector_return(
        store,
        &shape,
        &sources,
        &type_arguments,
        resolution.projection.signature,
        session,
    )
    .map_err(|error| {
        map_identity_vector_error(error, identity_shape, resolution.projection.type_argument)
    })?;
    let return_kind = if store
        .type_payload(return_type)
        .is_some_and(|record| record.flags().intersects(TypeFlags::VOID))
    {
        DirectCallReturnKind::Void
    } else {
        DirectCallReturnKind::Value
    };
    let recovered = store
        .intrinsic_bootstrap()
        .is_some_and(|bootstrap| return_type == bootstrap.error_type);
    if !recovered
        && (return_type != resolution.projection.return_type
            || return_kind != resolution.projection.return_kind)
    {
        return Err(IdentityGenericCallInvariant::InvalidInstantiation {
            source: identity_shape.type_parameter,
            expected: resolution.projection.return_type,
            actual: return_type,
        }
        .into());
    }
    Ok((return_type, return_kind))
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
            | NakedTypeInferenceError::MalformedDeclaredPropertyObject(_)
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
    use ts_ast::{FileId, NodeData};
    use ts_binder::{
        CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
        EscapedName, SymbolData,
    };
    use ts_jsnum::Number;
    use ts_parser::parse_source_file;

    use super::*;
    use crate::semantic::{
        CanonicalCheckerContext, CanonicalCheckerOptions, DeclaredTypeLinks,
        IntrinsicBootstrapOptions, SemanticStore, VarianceLinks, bootstrap::UnionReduction,
        instantiate::InstantiationLimits, mapper::TypeMapper, type_records::TypeRecord,
        types::ObjectFlags,
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
                rest_parameter: None,
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

    #[derive(Clone, Copy)]
    enum GenericTypeSpec {
        Exact(TypeId),
        Parameter(usize),
    }

    fn generic_type_spec(spec: GenericTypeSpec, type_parameters: &[TypeId]) -> TypeId {
        match spec {
            GenericTypeSpec::Exact(type_) => type_,
            GenericTypeSpec::Parameter(index) => type_parameters[index],
        }
    }

    fn vector_callable(
        store: &mut CanonicalTypeMapperStore,
        names: &[&str],
        constraints: &[Option<GenericTypeSpec>],
        defaults: &[Option<GenericTypeSpec>],
        parameter_indices: &[usize],
        return_type: impl FnOnce(&mut CanonicalTypeMapperStore, &[TypeId]) -> TypeId,
    ) -> (ValidatedSingleCallable, Vec<TypeId>) {
        vector_callable_with_minimum(
            store,
            names,
            constraints,
            defaults,
            parameter_indices,
            parameter_indices.len(),
            return_type,
        )
    }

    fn vector_callable_with_minimum(
        store: &mut CanonicalTypeMapperStore,
        names: &[&str],
        constraints: &[Option<GenericTypeSpec>],
        defaults: &[Option<GenericTypeSpec>],
        parameter_indices: &[usize],
        minimum_argument_count: usize,
        return_type: impl FnOnce(&mut CanonicalTypeMapperStore, &[TypeId]) -> TypeId,
    ) -> (ValidatedSingleCallable, Vec<TypeId>) {
        assert_eq!(constraints.len(), names.len());
        assert_eq!(defaults.len(), names.len());
        assert!(minimum_argument_count <= parameter_indices.len());
        let no_constraint = store.intrinsic_bootstrap().unwrap().no_constraint_type;
        let mut type_parameters = Vec::with_capacity(names.len());
        for name in names {
            let symbol = store
                .alloc_symbol(SymbolData::new(
                    SymbolFlags::TYPE_PARAMETER,
                    EscapedName::source(*name),
                ))
                .unwrap();
            let type_parameter = store.alloc_type_parameter(Some(symbol)).unwrap();
            assert!(store.set_declared_type_links(
                symbol,
                DeclaredTypeLinks {
                    declared_type: Some(type_parameter),
                    ..DeclaredTypeLinks::default()
                },
            ));
            type_parameters.push(type_parameter);
        }
        for (index, type_parameter) in type_parameters.iter().copied().enumerate() {
            let constraint = constraints[index].map_or(no_constraint, |spec| {
                generic_type_spec(spec, &type_parameters)
            });
            let default_type = defaults[index].map_or(no_constraint, |spec| {
                generic_type_spec(spec, &type_parameters)
            });
            assert!(store.set_type_parameter_resolution(
                type_parameter,
                Some(constraint),
                None,
                None,
                Some(default_type),
            ));
        }
        let parameter_types = parameter_indices
            .iter()
            .map(|index| type_parameters[*index])
            .collect::<Vec<_>>();
        let mut parameter_symbols = Vec::with_capacity(parameter_types.len());
        for (index, parameter_type) in parameter_types.iter().copied().enumerate() {
            let symbol = store
                .alloc_symbol(SymbolData::new(
                    SymbolFlags::FUNCTION_SCOPED_VARIABLE,
                    EscapedName::source(format!("arg{index}")),
                ))
                .unwrap();
            assert!(store.set_value_symbol_links(
                symbol,
                ValueSymbolLinks {
                    resolved_type: Some(parameter_type),
                    ..ValueSymbolLinks::default()
                },
            ));
            parameter_symbols.push(symbol);
        }
        let return_type = return_type(store, &type_parameters);
        let signature = store
            .alloc_signature(
                SignatureFlags::NONE,
                None,
                type_parameters.clone(),
                None,
                parameter_symbols,
                Some(return_type),
                None,
                i32::try_from(minimum_argument_count).unwrap(),
            )
            .unwrap();
        let owner = store.intrinsic_bootstrap().unwrap().any_function_type;
        (
            ValidatedSingleCallable {
                owner,
                signature,
                parameters: parameter_types,
                rest_parameter: None,
                min_argument_count: minimum_argument_count,
                return_type: Some(return_type),
                strict_variance_exempt: false,
            },
            type_parameters,
        )
    }

    fn union_vector_callable(
        store: &mut CanonicalTypeMapperStore,
        fixed: &[TypeId],
    ) -> (ValidatedSingleCallable, TypeId, TypeId) {
        let (mut callable, parameters) =
            vector_callable(store, &["T"], &[None], &[None], &[0], |_, parameters| {
                parameters[0]
            });
        let parameter = parameters[0];
        let mut constituents = Vec::with_capacity(fixed.len() + 1);
        constituents.push(parameter);
        constituents.extend_from_slice(fixed);
        let union = store
            .alloc_union_type(ObjectFlags::NONE, constituents)
            .unwrap();
        let symbol = store.signature(callable.signature).unwrap().parameters()[0];
        assert!(store.set_value_symbol_links(
            symbol,
            ValueSymbolLinks {
                resolved_type: Some(union),
                ..ValueSymbolLinks::default()
            },
        ));
        callable.parameters[0] = union;
        (callable, parameter, union)
    }

    fn canonical_array_target(store: &mut CanonicalTypeMapperStore, name: &str) -> TypeId {
        let symbol = store
            .alloc_symbol(SymbolData::new(
                SymbolFlags::INTERFACE,
                EscapedName::source(name),
            ))
            .unwrap();
        let parameter_symbol = store
            .alloc_symbol(SymbolData::new(
                SymbolFlags::TYPE_PARAMETER,
                EscapedName::source("T"),
            ))
            .unwrap();
        let parameter = store.alloc_type_parameter(Some(parameter_symbol)).unwrap();
        assert!(store.set_declared_type_links(
            parameter_symbol,
            DeclaredTypeLinks {
                declared_type: Some(parameter),
                ..DeclaredTypeLinks::default()
            },
        ));
        let target = store
            .alloc_interface_type(ObjectFlags::INTERFACE, Some(symbol))
            .unwrap();
        let this_type = store.alloc_type_parameter(Some(symbol)).unwrap();
        assert!(store.initialize_interface_type_parameters(
            target,
            vec![parameter, this_type],
            0,
            this_type,
            type_list_key(&[parameter]),
        ));
        target
    }

    fn canonical_array_targets(store: &mut CanonicalTypeMapperStore) -> CanonicalArrayTargets {
        CanonicalArrayTargets::for_test(
            canonical_array_target(store, "Array"),
            canonical_array_target(store, "ReadonlyArray"),
        )
    }

    fn canonical_array_type(
        store: &mut CanonicalTypeMapperStore,
        targets: CanonicalArrayTargets,
        element: TypeId,
        readonly: bool,
    ) -> TypeId {
        store
            .create_canonical_array_type_with_targets(targets, element, readonly)
            .unwrap()
    }

    fn canonical_interface_target(store: &mut CanonicalTypeMapperStore, name: &str) -> TypeId {
        let target = canonical_array_target(store, name);
        let owner = store.type_payload(target).unwrap().symbol().unwrap();
        assert!(store.set_declared_type_links(
            owner,
            DeclaredTypeLinks {
                declared_type: Some(target),
                ..DeclaredTypeLinks::default()
            },
        ));
        target
    }

    fn canonical_interface_reference(
        store: &mut CanonicalTypeMapperStore,
        target: TypeId,
        argument: TypeId,
    ) -> TypeId {
        store
            .create_direct_generic_reference_type(target, &[argument])
            .unwrap()
    }

    fn array_literal_clone(
        store: &mut CanonicalTypeMapperStore,
        targets: CanonicalArrayTargets,
        element: TypeId,
    ) -> TypeId {
        let base = canonical_array_type(store, targets, element, false);
        let base_record = store.type_payload(base).unwrap();
        let flags = base_record.object_flags() & !ObjectFlags::MEMBERS_RESOLVED
            | ObjectFlags::ARRAY_LITERAL
            | ObjectFlags::CONTAINS_OBJECT_OR_ARRAY_LITERAL;
        let symbol = base_record.symbol();
        let TypeData::TypeReference(reference) = base_record.data() else {
            panic!("canonical Array instantiations are direct references")
        };
        let target = reference.object.target;
        let arguments = reference.resolved_type_arguments.clone();
        let clone = store.alloc_type_reference(flags, symbol).unwrap();
        assert!(store.set_type_object_flags(clone, flags));
        assert!(store.set_object_target_and_mapper(clone, target, None));
        assert!(store.set_type_reference_resolution(clone, None, arguments));
        assert_eq!(
            store.derived_types.array_literal_types.insert(base, clone),
            None
        );
        clone
    }

    fn structured_vector_callable(
        store: &mut CanonicalTypeMapperStore,
        parameter_type: impl FnOnce(&mut CanonicalTypeMapperStore, TypeId) -> TypeId,
        return_type: impl FnOnce(&mut CanonicalTypeMapperStore, TypeId) -> TypeId,
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
        let no_constraint = store.intrinsic_bootstrap().unwrap().no_constraint_type;
        assert!(store.set_type_parameter_resolution(
            type_parameter,
            Some(no_constraint),
            None,
            None,
            Some(no_constraint),
        ));
        let parameter_type = parameter_type(store, type_parameter);
        let return_type = return_type(store, type_parameter);
        let parameter = store
            .alloc_symbol(SymbolData::new(
                SymbolFlags::FUNCTION_SCOPED_VARIABLE,
                EscapedName::source("value"),
            ))
            .unwrap();
        assert!(store.set_value_symbol_links(
            parameter,
            ValueSymbolLinks {
                resolved_type: Some(parameter_type),
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
                Some(return_type),
                None,
                1,
            )
            .unwrap();
        let owner = store.intrinsic_bootstrap().unwrap().any_function_type;
        (
            ValidatedSingleCallable {
                owner,
                signature,
                parameters: vec![parameter_type],
                rest_parameter: None,
                min_argument_count: 1,
                return_type: Some(return_type),
                strict_variance_exempt: false,
            },
            type_parameter,
        )
    }

    fn rest_vector_callable(
        store: &mut CanonicalTypeMapperStore,
        targets: CanonicalArrayTargets,
        fixed_parameters: usize,
        return_array: bool,
    ) -> (ValidatedSingleCallable, TypeId) {
        let parameter_indices = vec![0; fixed_parameters + 1];
        let (mut callable, parameters) = vector_callable_with_minimum(
            store,
            &["T"],
            &[None],
            &[None],
            &parameter_indices,
            fixed_parameters,
            |store, parameters| {
                if return_array {
                    canonical_array_type(store, targets, parameters[0], false)
                } else {
                    parameters[0]
                }
            },
        );
        let type_parameter = parameters[0];
        let rest = canonical_array_type(store, targets, type_parameter, false);
        let rest_symbol = *store
            .signature(callable.signature)
            .unwrap()
            .parameters()
            .last()
            .unwrap();
        assert!(store.set_value_symbol_links(
            rest_symbol,
            ValueSymbolLinks {
                resolved_type: Some(rest),
                ..ValueSymbolLinks::default()
            },
        ));
        assert!(store.set_signature_flags(callable.signature, SignatureFlags::HAS_REST_PARAMETER,));
        callable.parameters.pop();
        callable.rest_parameter = Some(rest);
        (callable, type_parameter)
    }

    fn vector_request<'a>(
        callee: TypeId,
        explicit_type_arguments: Option<&'a [TypeId]>,
        arguments: &'a [TypeId],
    ) -> GenericCallVectorRequest<'a> {
        GenericCallVectorRequest {
            form: DirectCallForm::Call,
            optional_chain: false,
            explicit_type_arguments,
            has_spread_argument: false,
            callee,
            arguments,
        }
    }

    fn scalar_assignable(store: &CanonicalTypeMapperStore, source: TypeId, target: TypeId) -> bool {
        if source == target {
            return true;
        }
        let Some(source_record) = store.type_payload(source) else {
            return false;
        };
        let Some(target_record) = store.type_payload(target) else {
            return false;
        };
        if source_record
            .flags()
            .intersects(TypeFlags::NEVER | TypeFlags::ANY)
        {
            return true;
        }
        if let (TypeData::Literal(source), TypeData::Literal(target)) =
            (source_record.data(), target_record.data())
            && source.regular_type == target.regular_type
        {
            return true;
        }
        if target_record.flags().intersects(TypeFlags::ANY_OR_UNKNOWN) {
            return true;
        }
        if let TypeData::Union(source_union) = source_record.data() {
            return source_union
                .union
                .types
                .iter()
                .copied()
                .all(|constituent| scalar_assignable(store, constituent, target));
        }
        if let TypeData::Union(target_union) = target_record.data() {
            return target_union
                .union
                .types
                .iter()
                .copied()
                .any(|constituent| scalar_assignable(store, source, constituent));
        }
        source_record.flags().intersects(TypeFlags::STRING_LITERAL)
            && target_record.flags() == TypeFlags::STRING
            || source_record.flags().intersects(TypeFlags::NUMBER_LITERAL)
                && target_record.flags() == TypeFlags::NUMBER
            || source_record.flags().intersects(TypeFlags::BIG_INT_LITERAL)
                && target_record.flags() == TypeFlags::BIG_INT
            || source_record.flags().intersects(TypeFlags::BOOLEAN_LITERAL)
                && target_record.flags() == TypeFlags::BOOLEAN
    }

    fn scalar_or_array_assignable(
        store: &CanonicalTypeMapperStore,
        targets: CanonicalArrayTargets,
        source: TypeId,
        target: TypeId,
    ) -> bool {
        if scalar_assignable(store, source, target) {
            return true;
        }
        let (Ok(Some(source)), Ok(Some(target))) = (
            store.canonical_array_reference_with_targets(targets, source),
            store.canonical_array_reference_with_targets(targets, target),
        ) else {
            return false;
        };
        (!source.readonly || target.readonly)
            && scalar_or_array_assignable(store, targets, source.element_type, target.element_type)
    }

    fn project_vector(
        store: &mut CanonicalTypeMapperStore,
        callable: &ValidatedSingleCallable,
        request: GenericCallVectorRequest<'_>,
    ) -> Result<GenericCallVectorResolution, GenericCallVectorError> {
        project_validated_generic_call_vector(
            store,
            request,
            callable,
            None,
            |store, source, target| Ok(scalar_assignable(store, source, target)),
            CanonicalTypeMapperStore::is_type_strict_subtype_of,
            CanonicalTypeMapperStore::is_type_subtype_of,
        )
    }

    fn project_array_vector(
        store: &mut CanonicalTypeMapperStore,
        targets: CanonicalArrayTargets,
        callable: &ValidatedSingleCallable,
        request: GenericCallVectorRequest<'_>,
    ) -> Result<GenericCallVectorResolution, GenericCallVectorError> {
        project_validated_generic_call_vector(
            store,
            request,
            callable,
            Some(targets),
            |store, source, target| Ok(scalar_or_array_assignable(store, targets, source, target)),
            |store, source, target| {
                Ok(source != target && scalar_or_array_assignable(store, targets, source, target))
            },
            |store, source, target| Ok(scalar_or_array_assignable(store, targets, source, target)),
        )
    }

    fn materialize_vector(
        store: &mut CanonicalTypeMapperStore,
        callable: &ValidatedSingleCallable,
        resolution: &GenericCallVectorResolution,
    ) -> Result<GenericCallVectorMaterialization, GenericCallVectorError> {
        materialize_validated_generic_call_vector_checked_instantiation(store, resolution, callable)
    }

    fn materialize_source_vector(
        store: &mut CanonicalTypeMapperStore,
        callable: &ValidatedSingleCallable,
        resolution: &GenericCallVectorResolution,
        existing_call_signature: Option<SignatureId>,
    ) -> Result<GenericCallVectorSourceMaterialization, GenericCallVectorError> {
        materialize_validated_generic_call_vector_source(
            store,
            resolution,
            callable,
            existing_call_signature,
        )
    }

    fn demand_vector_parameter(
        store: &mut CanonicalTypeMapperStore,
        callable: &ValidatedSingleCallable,
        resolution: &GenericCallVectorResolution,
        instantiation: &GenericCallVectorInstantiation,
        index: usize,
    ) -> TypeId {
        let shape = validate_generic_call_signature_shape(
            store,
            resolution.projection.callee,
            callable,
            resolution.capability.array_targets,
        )
        .unwrap();
        let sources = shape
            .type_parameters
            .iter()
            .map(|parameter| parameter.type_)
            .collect::<Vec<_>>();
        demand_generic_call_vector_parameter(
            store,
            &shape,
            &sources,
            &instantiation.type_arguments,
            instantiation.signature,
            index,
            &mut InstantiationSession::new(InstantiationLimits::default()),
        )
        .unwrap()
    }

    fn demand_vector_return(
        store: &mut CanonicalTypeMapperStore,
        callable: &ValidatedSingleCallable,
        resolution: &GenericCallVectorResolution,
        instantiation: &GenericCallVectorInstantiation,
    ) -> TypeId {
        let shape = validate_generic_call_signature_shape(
            store,
            resolution.projection.callee,
            callable,
            resolution.capability.array_targets,
        )
        .unwrap();
        let sources = shape
            .type_parameters
            .iter()
            .map(|parameter| parameter.type_)
            .collect::<Vec<_>>();
        demand_generic_call_vector_return(
            store,
            &shape,
            &sources,
            &instantiation.type_arguments,
            instantiation.signature,
            &mut InstantiationSession::new(InstantiationLimits::default()),
        )
        .unwrap()
    }

    #[derive(Debug, Eq, PartialEq)]
    struct VectorCacheGraphCounts {
        mappers: usize,
        symbols: usize,
        signatures: usize,
        cached_signatures: usize,
        links: [usize; 26],
        types: usize,
        unions: usize,
        unions_of_unions: usize,
        union_validation_scans: usize,
    }

    fn vector_cache_graph_counts(store: &CanonicalTypeMapperStore) -> VectorCacheGraphCounts {
        let bootstrap = store.intrinsic_bootstrap().unwrap();
        VectorCacheGraphCounts {
            mappers: store.mapper_len(),
            symbols: store.symbol_len(),
            signatures: store.signature_len(),
            cached_signatures: store.cached_signature_len(),
            links: store.checker_link_allocated_lengths(),
            types: store.type_len(),
            unions: bootstrap.union_cache_len(),
            unions_of_unions: bootstrap.union_of_union_cache_len(),
            union_validation_scans: store.union_cache_validation_scan_count(),
        }
    }

    fn fresh_string(store: &mut CanonicalTypeMapperStore, value: &str) -> TypeId {
        let regular = store.regular_string_literal_type(value.into()).unwrap();
        store.fresh_type_of_literal_type(regular).unwrap()
    }

    fn fresh_number(store: &mut CanonicalTypeMapperStore, value: f64) -> TypeId {
        let regular = store
            .regular_number_literal_type(Number::new(value))
            .unwrap();
        store.fresh_type_of_literal_type(regular).unwrap()
    }

    fn assert_recovery_only_source_lifecycle(
        store: &mut CanonicalTypeMapperStore,
        callable: &ValidatedSingleCallable,
        resolution: &GenericCallVectorResolution,
    ) -> GenericCallVectorSourceMaterialization {
        assert!(resolution.projection.recovery);
        assert!(!generic_call_vector_caches_checked_instantiation(
            resolution.applicability,
        ));
        let before = vector_cache_graph_counts(store);
        let first = materialize_source_vector(store, callable, resolution, None).unwrap();
        assert_eq!(first.checked_instantiation, None);
        assert_eq!(vector_cache_graph_counts(store), before);
        assert_eq!(
            store.cached_signatures_contain(first.call_signature),
            Some(false),
        );

        let warm_counts = vector_cache_graph_counts(store);
        assert_eq!(
            materialize_source_vector(store, callable, resolution, Some(first.call_signature)),
            Ok(first),
        );
        assert_eq!(vector_cache_graph_counts(store), warm_counts);

        let second = materialize_source_vector(store, callable, resolution, None).unwrap();
        assert_eq!(second.checked_instantiation, None);
        assert_eq!(second, first);
        assert_eq!(
            store.cached_signatures_contain(second.call_signature),
            Some(false),
        );
        let second_warm_counts = vector_cache_graph_counts(store);
        assert_eq!(
            materialize_source_vector(store, callable, resolution, Some(second.call_signature)),
            Ok(second),
        );
        assert_eq!(vector_cache_graph_counts(store), second_warm_counts);
        first
    }

    #[test]
    fn optional_generic_parameters_accept_omission_and_infer_unknown() {
        let mut store = initialized_store();
        let (number, string, unknown) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (
                bootstrap.number_type,
                bootstrap.string_type,
                bootstrap.unknown_type,
            )
        };
        let (optional, _) = vector_callable_with_minimum(
            &mut store,
            &["T"],
            &[None],
            &[None],
            &[0],
            0,
            |_, parameters| parameters[0],
        );

        let omitted = project_vector(
            &mut store,
            &optional,
            vector_request(optional.owner, None, &[]),
        )
        .unwrap();
        assert_eq!(
            omitted.applicability,
            GenericCallVectorApplicability::Applicable
        );
        assert_eq!(omitted.projection.instantiation.type_arguments, [unknown]);

        let explicit = project_vector(
            &mut store,
            &optional,
            vector_request(optional.owner, Some(&[string]), &[]),
        )
        .unwrap();
        assert_eq!(
            explicit.applicability,
            GenericCallVectorApplicability::Applicable
        );
        assert_eq!(explicit.projection.instantiation.type_arguments, [string]);

        let supplied = project_vector(
            &mut store,
            &optional,
            vector_request(optional.owner, None, &[number]),
        )
        .unwrap();
        assert_eq!(
            supplied.applicability,
            GenericCallVectorApplicability::Applicable
        );
        assert_eq!(supplied.projection.instantiation.type_arguments, [number]);

        let extra = project_vector(
            &mut store,
            &optional,
            vector_request(optional.owner, None, &[number, number]),
        )
        .unwrap();
        assert_eq!(
            extra.applicability,
            GenericCallVectorApplicability::TooManyArguments {
                expected: 1,
                actual: 2,
            }
        );
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Check all private markers and each public fallback shape.
    fn generic_calls_ignore_binding_placeholders_and_preserve_default_fallbacks() {
        let mut store = initialized_store();
        let (auto, silent_never, placeholder_any, any_function, never, any, unknown, string) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (
                bootstrap.auto_type,
                bootstrap.silent_never_type,
                bootstrap.non_inferrable_any_type,
                bootstrap.any_function_type,
                bootstrap.never_type,
                bootstrap.any_type,
                bootstrap.unknown_type,
                bootstrap.string_type,
            )
        };
        let (callable, _) = vector_callable(
            &mut store,
            &["T"],
            &[None],
            &[None],
            &[0],
            |_, parameters| parameters[0],
        );

        let first = project_vector(
            &mut store,
            &callable,
            vector_request(callable.owner, None, &[auto]),
        )
        .unwrap();

        assert_eq!(
            first.applicability,
            GenericCallVectorApplicability::Applicable,
        );
        assert_eq!(first.projection.instantiation.type_arguments, [unknown]);
        assert_eq!(
            demand_vector_return(
                &mut store,
                &callable,
                &first,
                &first.projection.instantiation,
            ),
            unknown,
        );
        let warm = vector_cache_graph_counts(&store);
        for source in [auto, silent_never, placeholder_any, any_function] {
            let replay = project_vector(
                &mut store,
                &callable,
                vector_request(callable.owner, None, &[source]),
            )
            .unwrap();
            assert_eq!(replay, first);
            assert_eq!(vector_cache_graph_counts(&store), warm);
        }

        let (defaulted, _) = vector_callable(
            &mut store,
            &["T"],
            &[None],
            &[Some(GenericTypeSpec::Exact(string))],
            &[0],
            |_, parameters| parameters[0],
        );
        let (constrained, _) = vector_callable(
            &mut store,
            &["T"],
            &[Some(GenericTypeSpec::Exact(string))],
            &[None],
            &[0],
            |_, parameters| parameters[0],
        );
        for callable in [&defaulted, &constrained] {
            for source in [auto, silent_never, placeholder_any] {
                let result = project_vector(
                    &mut store,
                    callable,
                    vector_request(callable.owner, None, &[source]),
                )
                .unwrap();
                assert_eq!(
                    result.applicability,
                    GenericCallVectorApplicability::Applicable,
                );
                assert_eq!(result.projection.instantiation.type_arguments, [string]);
            }
        }

        for source in [never, any] {
            let result = project_vector(
                &mut store,
                &callable,
                vector_request(callable.owner, None, &[source]),
            )
            .unwrap();
            assert_eq!(result.projection.instantiation.type_arguments, [source]);
        }
    }

    #[test]
    fn generic_array_inference_ignores_propagated_binding_placeholders() {
        let mut store = initialized_store();
        let targets = canonical_array_targets(&mut store);
        let (auto, unknown) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (bootstrap.auto_type, bootstrap.unknown_type)
        };
        let (callable, _) = structured_vector_callable(
            &mut store,
            |store, type_parameter| canonical_array_type(store, targets, type_parameter, false),
            |_, type_parameter| type_parameter,
        );
        let argument = canonical_array_type(&mut store, targets, auto, false);

        let resolution = project_array_vector(
            &mut store,
            targets,
            &callable,
            vector_request(callable.owner, None, &[argument]),
        )
        .unwrap();

        assert_eq!(
            resolution.applicability,
            GenericCallVectorApplicability::Applicable,
        );
        assert_eq!(
            resolution.projection.instantiation.type_arguments,
            [unknown]
        );
        let warm = vector_cache_graph_counts(&store);
        assert_eq!(
            project_array_vector(
                &mut store,
                targets,
                &callable,
                vector_request(callable.owner, None, &[argument]),
            ),
            Ok(resolution),
        );
        assert_eq!(vector_cache_graph_counts(&store), warm);
    }

    #[test]
    fn forged_non_inferrable_call_source_fails_before_signature_publication() {
        let mut store = initialized_store();
        let (callable, _) = vector_callable(
            &mut store,
            &["T"],
            &[None],
            &[None],
            &[0],
            |_, parameters| parameters[0],
        );
        let forged = store
            .alloc_plain_object_type(
                ObjectFlags::ANONYMOUS | ObjectFlags::NON_INFERRABLE_TYPE,
                None,
            )
            .unwrap();
        let before = vector_cache_graph_counts(&store);

        assert_eq!(
            project_vector(
                &mut store,
                &callable,
                vector_request(callable.owner, None, &[forged]),
            ),
            Err(GenericCallVectorError::Inference(
                NakedTypeCandidateError::Candidate(NakedTypeInferenceError::UnsupportedCandidate(
                    forged
                ),),
            )),
        );
        assert_eq!(vector_cache_graph_counts(&store), before);
    }

    #[test]
    fn omitted_optional_generic_parameters_apply_dependent_defaults() {
        let mut store = initialized_store();
        let string = store.intrinsic_bootstrap().unwrap().string_type;
        let (optional, _) = vector_callable_with_minimum(
            &mut store,
            &["T", "U"],
            &[None, None],
            &[None, Some(GenericTypeSpec::Parameter(0))],
            &[0, 1],
            1,
            |_, parameters| parameters[1],
        );

        let omitted = project_vector(
            &mut store,
            &optional,
            vector_request(optional.owner, None, &[string]),
        )
        .unwrap();
        assert_eq!(
            omitted.applicability,
            GenericCallVectorApplicability::Applicable
        );
        assert_eq!(
            omitted.projection.instantiation.type_arguments,
            [string, string]
        );

        let missing = project_vector(
            &mut store,
            &optional,
            vector_request(optional.owner, None, &[]),
        )
        .unwrap();
        assert_eq!(
            missing.applicability,
            GenericCallVectorApplicability::TooFewArguments {
                expected: 1,
                actual: 0,
            }
        );
    }

    #[test]
    fn generic_union_parameters_infer_unmatched_and_fully_matched_sources() {
        let mut store = initialized_store();
        let (string, number, never, auto, unknown) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (
                bootstrap.string_type,
                bootstrap.number_type,
                bootstrap.never_type,
                bootstrap.auto_type,
                bootstrap.unknown_type,
            )
        };
        let literal = fresh_string(&mut store, "value");
        let (callable, parameter, _) = union_vector_callable(&mut store, &[string]);

        for (source, expected) in [
            (number, number),
            (string, string),
            (literal, literal),
            (never, never),
            (auto, unknown),
        ] {
            let resolution = project_vector(
                &mut store,
                &callable,
                vector_request(callable.owner, None, &[source]),
            )
            .unwrap();

            assert_eq!(
                resolution.applicability,
                GenericCallVectorApplicability::Applicable,
            );
            assert_eq!(resolution.projection.type_parameters, [parameter]);
            assert_eq!(
                resolution.projection.instantiation.type_arguments,
                [expected]
            );
            assert_eq!(
                demand_vector_return(
                    &mut store,
                    &callable,
                    &resolution,
                    &resolution.projection.instantiation,
                ),
                expected,
            );
            let warm = vector_cache_graph_counts(&store);
            assert_eq!(
                project_vector(
                    &mut store,
                    &callable,
                    vector_request(callable.owner, None, &[source]),
                ),
                Ok(resolution),
            );
            assert_eq!(vector_cache_graph_counts(&store), warm);
        }
    }

    #[test]
    fn generic_union_parameters_infer_only_unmatched_source_constituents() {
        let mut store = initialized_store();
        let (string, number, bigint) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (
                bootstrap.string_type,
                bootstrap.number_type,
                bootstrap.bigint_type,
            )
        };
        let (callable, _, _) = union_vector_callable(&mut store, &[string]);
        let matched = store
            .expression_union_type(&[string, number], UnionReduction::Literal)
            .unwrap();
        let multiple = store
            .expression_union_type(&[number, bigint], UnionReduction::Literal)
            .unwrap();

        let selected = project_vector(
            &mut store,
            &callable,
            vector_request(callable.owner, None, &[matched]),
        )
        .unwrap();
        assert_eq!(
            selected.applicability,
            GenericCallVectorApplicability::Applicable,
        );
        assert_eq!(selected.projection.instantiation.type_arguments, [number]);

        let combined = project_vector(
            &mut store,
            &callable,
            vector_request(callable.owner, None, &[multiple]),
        )
        .unwrap();
        assert_eq!(
            combined.applicability,
            GenericCallVectorApplicability::Applicable,
        );
        let inferred = combined.projection.instantiation.type_arguments[0];
        let TypeData::Union(union) = store.type_payload(inferred).unwrap().data() else {
            panic!("multiple unmatched constituents must retain their canonical union")
        };
        assert_eq!(union.union.types.len(), 2);
        assert!(union.union.types.contains(&number));
        assert!(union.union.types.contains(&bigint));

        let (multiple_fixed, _, _) = union_vector_callable(&mut store, &[string, number]);
        let all = store
            .expression_union_type(&[string, number, bigint], UnionReduction::Literal)
            .unwrap();
        let remaining = project_vector(
            &mut store,
            &multiple_fixed,
            vector_request(multiple_fixed.owner, None, &[all]),
        )
        .unwrap();
        assert_eq!(
            remaining.applicability,
            GenericCallVectorApplicability::Applicable,
        );
        assert_eq!(remaining.projection.instantiation.type_arguments, [bigint]);

        let signature = combined.projection.instantiation.signature;
        let warm = vector_cache_graph_counts(&store);
        assert_eq!(
            project_vector(
                &mut store,
                &callable,
                vector_request(callable.owner, None, &[multiple]),
            ),
            Ok(combined),
        );
        assert_eq!(vector_cache_graph_counts(&store), warm);

        let parameter = store.signature(signature).unwrap().parameters()[0];
        let mut links = store.value_symbol_links(parameter).unwrap().clone();
        links.resolved_type = Some(matched);
        assert!(store.set_value_symbol_links(parameter, links));
        let forged = vector_cache_graph_counts(&store);
        assert_eq!(
            project_vector(
                &mut store,
                &callable,
                vector_request(callable.owner, None, &[multiple]),
            ),
            Err(GenericCallVectorError::Invariant(
                GenericCallVectorInvariant::InvalidCachedInstantiation {
                    target: callable.signature,
                    signature,
                },
            )),
        );
        assert_eq!(vector_cache_graph_counts(&store), forged);
    }

    #[test]
    fn contravariant_union_inference_keeps_never_fallback_and_cache_identity() {
        let mut store = initialized_store();
        let target = canonical_interface_target(&mut store, "Consumer");
        let owner = store.type_payload(target).unwrap().symbol().unwrap();
        assert!(store.set_variance_links(
            owner,
            VarianceLinks {
                variances: Some(vec![VarianceFlags::CONTRAVARIANT]),
            },
        ));
        let (string, number, never) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (
                bootstrap.string_type,
                bootstrap.number_type,
                bootstrap.never_type,
            )
        };
        let (mut callable, parameters) = vector_callable(
            &mut store,
            &["T"],
            &[None],
            &[None],
            &[0, 0],
            |_, parameters| parameters[0],
        );
        let template = store
            .alloc_union_type(ObjectFlags::NONE, vec![parameters[0], string])
            .unwrap();
        let consumer = canonical_interface_reference(&mut store, target, template);
        let symbol = store.signature(callable.signature).unwrap().parameters()[1];
        assert!(store.set_value_symbol_links(
            symbol,
            ValueSymbolLinks {
                resolved_type: Some(consumer),
                ..ValueSymbolLinks::default()
            },
        ));
        callable.parameters[1] = consumer;
        let actual = store
            .expression_union_type(&[string, number], UnionReduction::Literal)
            .unwrap();
        let argument = canonical_interface_reference(&mut store, target, actual);

        let resolution = project_vector(
            &mut store,
            &callable,
            vector_request(callable.owner, None, &[never, argument]),
        )
        .unwrap();

        assert_eq!(
            resolution.applicability,
            GenericCallVectorApplicability::Applicable,
        );
        assert_eq!(resolution.projection.instantiation.type_arguments, [number]);
        let warm = vector_cache_graph_counts(&store);
        assert_eq!(
            project_vector(
                &mut store,
                &callable,
                vector_request(callable.owner, None, &[never, argument]),
            ),
            Ok(resolution),
        );
        assert_eq!(vector_cache_graph_counts(&store), warm);
    }

    #[test]
    fn malformed_generic_union_templates_fail_before_signature_publication() {
        for nested in [false, true] {
            let mut store = initialized_store();
            let (string, number) = {
                let bootstrap = store.intrinsic_bootstrap().unwrap();
                (bootstrap.string_type, bootstrap.number_type)
            };
            let (mut callable, parameter, _) = union_vector_callable(&mut store, &[string]);
            let constituents = if nested {
                let inner = store
                    .alloc_union_type(ObjectFlags::NONE, vec![string, number])
                    .unwrap();
                vec![parameter, inner]
            } else {
                vec![parameter, string, string]
            };
            let forged = store
                .alloc_union_type(ObjectFlags::NONE, constituents)
                .unwrap();
            let symbol = store.signature(callable.signature).unwrap().parameters()[0];
            assert!(store.set_value_symbol_links(
                symbol,
                ValueSymbolLinks {
                    resolved_type: Some(forged),
                    ..ValueSymbolLinks::default()
                },
            ));
            callable.parameters[0] = forged;
            let before = vector_cache_graph_counts(&store);

            assert_eq!(
                project_vector(
                    &mut store,
                    &callable,
                    vector_request(callable.owner, None, &[number]),
                ),
                Err(GenericCallVectorError::Invariant(
                    GenericCallVectorInvariant::InvalidUnionParameter {
                        signature: callable.signature,
                        type_: forged,
                    },
                )),
            );
            assert_eq!(vector_cache_graph_counts(&store), before);
        }
    }

    #[test]
    fn generic_interface_inference_reuses_checked_signature_and_return_identity() {
        let mut store = initialized_store();
        let target = canonical_interface_target(&mut store, "Box");
        let owner = store.type_payload(target).unwrap().symbol().unwrap();
        assert!(store.set_variance_links(
            owner,
            VarianceLinks {
                variances: Some(vec![VarianceFlags::COVARIANT]),
            },
        ));
        let (callable, type_parameter) = structured_vector_callable(
            &mut store,
            |store, type_parameter| canonical_interface_reference(store, target, type_parameter),
            |store, type_parameter| canonical_interface_reference(store, target, type_parameter),
        );
        let number = store.intrinsic_bootstrap().unwrap().number_type;
        let argument = canonical_interface_reference(&mut store, target, number);

        let inferred = project_vector(
            &mut store,
            &callable,
            vector_request(callable.owner, None, &[argument]),
        )
        .unwrap();

        assert_eq!(
            inferred.applicability,
            GenericCallVectorApplicability::Applicable
        );
        assert_eq!(inferred.projection.type_parameters, [type_parameter]);
        assert_eq!(inferred.projection.instantiation.type_arguments, [number]);
        assert_eq!(
            demand_vector_parameter(
                &mut store,
                &callable,
                &inferred,
                &inferred.projection.instantiation,
                0,
            ),
            argument,
        );
        assert_eq!(
            demand_vector_return(
                &mut store,
                &callable,
                &inferred,
                &inferred.projection.instantiation,
            ),
            argument,
        );

        let warm = vector_cache_graph_counts(&store);
        let explicit = project_vector(
            &mut store,
            &callable,
            vector_request(callable.owner, Some(&[number]), &[argument]),
        )
        .unwrap();
        assert_eq!(explicit, inferred);
        assert_eq!(vector_cache_graph_counts(&store), warm);
        assert_eq!(
            project_vector(
                &mut store,
                &callable,
                vector_request(callable.owner, None, &[argument]),
            ),
            Ok(inferred),
        );
        assert_eq!(vector_cache_graph_counts(&store), warm);
    }

    #[test]
    fn generic_interface_inference_preserves_nested_and_array_wrapped_targets() {
        let mut store = initialized_store();
        let target = canonical_interface_target(&mut store, "Box");
        let number = store.intrinsic_bootstrap().unwrap().number_type;
        let (nested, _) = structured_vector_callable(
            &mut store,
            |store, type_parameter| {
                let inner = canonical_interface_reference(store, target, type_parameter);
                canonical_interface_reference(store, target, inner)
            },
            |store, type_parameter| {
                let inner = canonical_interface_reference(store, target, type_parameter);
                canonical_interface_reference(store, target, inner)
            },
        );
        let inner = canonical_interface_reference(&mut store, target, number);
        let nested_argument = canonical_interface_reference(&mut store, target, inner);
        let nested_resolution = project_vector(
            &mut store,
            &nested,
            vector_request(nested.owner, None, &[nested_argument]),
        )
        .unwrap();

        assert_eq!(
            nested_resolution.projection.instantiation.type_arguments,
            [number],
        );
        assert_eq!(
            demand_vector_return(
                &mut store,
                &nested,
                &nested_resolution,
                &nested_resolution.projection.instantiation,
            ),
            nested_argument,
        );
        let outer_reference = validate_direct_generic_reference(&store, nested_argument).unwrap();
        let inner_reference = validate_direct_generic_reference(&store, inner).unwrap();
        assert_eq!(outer_reference.target, target);
        assert_eq!(outer_reference.type_arguments, [inner]);
        assert_eq!(inner_reference.target, target);
        assert_eq!(inner_reference.type_arguments, [number]);

        let array_targets = canonical_array_targets(&mut store);
        for array_target in [
            array_targets.array_type(),
            array_targets.readonly_array_type(),
        ] {
            let owner = store.type_payload(array_target).unwrap().symbol().unwrap();
            assert!(store.set_declared_type_links(
                owner,
                DeclaredTypeLinks {
                    declared_type: Some(array_target),
                    ..DeclaredTypeLinks::default()
                },
            ));
        }
        let (mixed, _) = structured_vector_callable(
            &mut store,
            |store, type_parameter| {
                let array = canonical_array_type(store, array_targets, type_parameter, false);
                canonical_interface_reference(store, target, array)
            },
            |store, type_parameter| {
                let array = canonical_array_type(store, array_targets, type_parameter, false);
                canonical_interface_reference(store, target, array)
            },
        );
        let array = canonical_array_type(&mut store, array_targets, number, false);
        let mixed_argument = canonical_interface_reference(&mut store, target, array);
        let mixed_resolution = project_array_vector(
            &mut store,
            array_targets,
            &mixed,
            vector_request(mixed.owner, None, &[mixed_argument]),
        )
        .unwrap();

        assert_eq!(
            mixed_resolution.applicability,
            GenericCallVectorApplicability::Applicable,
        );
        assert_eq!(
            mixed_resolution.projection.instantiation.type_arguments,
            [number],
        );
        assert_eq!(
            demand_vector_return(
                &mut store,
                &mixed,
                &mixed_resolution,
                &mixed_resolution.projection.instantiation,
            ),
            mixed_argument,
        );
    }

    #[test]
    fn generic_interface_mismatches_preserve_argument_diagnostics() {
        let mut store = initialized_store();
        let target = canonical_interface_target(&mut store, "Box");
        let other_target = canonical_interface_target(&mut store, "Other");
        let (callable, _) = structured_vector_callable(
            &mut store,
            |store, type_parameter| canonical_interface_reference(store, target, type_parameter),
            |store, type_parameter| canonical_interface_reference(store, target, type_parameter),
        );
        let (number, string, unknown) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (
                bootstrap.number_type,
                bootstrap.string_type,
                bootstrap.unknown_type,
            )
        };
        let number_box = canonical_interface_reference(&mut store, target, number);
        let string_box = canonical_interface_reference(&mut store, target, string);
        let unknown_box = canonical_interface_reference(&mut store, target, unknown);
        let other_number = canonical_interface_reference(&mut store, other_target, number);

        let explicit = project_vector(
            &mut store,
            &callable,
            vector_request(callable.owner, Some(&[string]), &[number_box]),
        )
        .unwrap();
        assert_eq!(
            explicit.applicability,
            GenericCallVectorApplicability::ArgumentNotAssignable {
                index: 0,
                argument_type: number_box,
                parameter_type: string_box,
            },
        );
        assert_eq!(explicit.applicability.diagnostic_code(), Some(2345));

        let mismatched_target = project_vector(
            &mut store,
            &callable,
            vector_request(callable.owner, None, &[other_number]),
        )
        .unwrap();
        assert_eq!(
            mismatched_target.projection.instantiation.type_arguments,
            [unknown],
        );
        assert_eq!(
            mismatched_target.applicability,
            GenericCallVectorApplicability::ArgumentNotAssignable {
                index: 0,
                argument_type: other_number,
                parameter_type: unknown_box,
            },
        );
    }

    #[test]
    fn forged_generic_interface_reference_is_rejected_before_projection_writes() {
        let mut store = initialized_store();
        let target = canonical_interface_target(&mut store, "Box");
        let mut forged = None;
        let (callable, _) = structured_vector_callable(
            &mut store,
            |store, type_parameter| {
                let canonical = canonical_interface_reference(store, target, type_parameter);
                let owner = store.type_payload(canonical).unwrap().symbol();
                let duplicate = store
                    .alloc_type_reference(ObjectFlags::NONE, owner)
                    .unwrap();
                assert!(store.set_object_target_and_mapper(duplicate, Some(target), None));
                assert!(store.set_type_reference_resolution(
                    duplicate,
                    None,
                    Some(vec![type_parameter]),
                ));
                forged = Some(duplicate);
                duplicate
            },
            |_, type_parameter| type_parameter,
        );
        let forged = forged.unwrap();
        let number = store.intrinsic_bootstrap().unwrap().number_type;
        let argument = canonical_interface_reference(&mut store, target, number);
        let before = vector_cache_graph_counts(&store);

        assert_eq!(
            project_vector(
                &mut store,
                &callable,
                vector_request(callable.owner, None, &[argument]),
            ),
            Err(GenericCallVectorError::Invariant(
                GenericCallVectorInvariant::InvalidInterfaceReference {
                    signature: callable.signature,
                    type_: forged,
                },
            )),
        );
        assert_eq!(vector_cache_graph_counts(&store), before);
    }

    #[test]
    fn poisoned_generic_interface_cache_is_rejected_before_projection_writes() {
        let mut store = initialized_store();
        let target = canonical_interface_target(&mut store, "Box");
        let (callable, _) = structured_vector_callable(
            &mut store,
            |store, type_parameter| canonical_interface_reference(store, target, type_parameter),
            |_, type_parameter| type_parameter,
        );
        let (number, string) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (bootstrap.number_type, bootstrap.string_type)
        };
        let argument = canonical_interface_reference(&mut store, target, number);
        let owner = store.type_payload(target).unwrap().symbol();
        let poison = store
            .alloc_type_reference(ObjectFlags::NONE, owner)
            .unwrap();
        assert!(store.set_object_target_and_mapper(poison, Some(target), None));
        assert!(store.set_type_reference_resolution(poison, None, Some(vec![number])));
        assert!(store.try_reserve_object_instantiations(target, 1));
        assert_eq!(
            store.insert_object_instantiation(target, type_list_key(&[string]), poison),
            Some(poison),
        );
        let before = vector_cache_graph_counts(&store);

        assert_eq!(
            project_vector(
                &mut store,
                &callable,
                vector_request(callable.owner, None, &[argument]),
            ),
            Err(GenericCallVectorError::Invariant(
                GenericCallVectorInvariant::InvalidInterfaceReference {
                    signature: callable.signature,
                    type_: callable.parameters[0],
                },
            )),
        );
        assert_eq!(vector_cache_graph_counts(&store), before);
    }

    #[test]
    fn contravariant_generic_interface_inference_reuses_checked_signature() {
        let mut store = initialized_store();
        let target = canonical_interface_target(&mut store, "Consumer");
        let owner = store.type_payload(target).unwrap().symbol().unwrap();
        assert!(store.set_variance_links(
            owner,
            VarianceLinks {
                variances: Some(vec![VarianceFlags::CONTRAVARIANT]),
            },
        ));
        let (callable, parameter) = structured_vector_callable(
            &mut store,
            |store, type_parameter| canonical_interface_reference(store, target, type_parameter),
            |_, type_parameter| type_parameter,
        );
        let string = store.intrinsic_bootstrap().unwrap().string_type;
        let argument = canonical_interface_reference(&mut store, target, string);

        let first = project_vector(
            &mut store,
            &callable,
            vector_request(callable.owner, None, &[argument]),
        )
        .unwrap();

        assert_eq!(
            first.applicability,
            GenericCallVectorApplicability::Applicable
        );
        assert_eq!(first.projection.type_parameters, [parameter]);
        assert_eq!(first.projection.instantiation.type_arguments, [string]);
        assert_eq!(
            demand_vector_return(
                &mut store,
                &callable,
                &first,
                &first.projection.instantiation,
            ),
            string,
        );
        let warm = vector_cache_graph_counts(&store);
        assert_eq!(
            project_vector(
                &mut store,
                &callable,
                vector_request(callable.owner, None, &[argument]),
            ),
            Ok(first),
        );
        assert_eq!(vector_cache_graph_counts(&store), warm);
    }

    #[test]
    fn nested_contravariant_interface_arguments_restore_covariant_inference() {
        let mut store = initialized_store();
        let target = canonical_interface_target(&mut store, "Consumer");
        let owner = store.type_payload(target).unwrap().symbol().unwrap();
        assert!(store.set_variance_links(
            owner,
            VarianceLinks {
                variances: Some(vec![VarianceFlags::CONTRAVARIANT]),
            },
        ));
        let (callable, parameter) = structured_vector_callable(
            &mut store,
            |store, type_parameter| {
                let inner = canonical_interface_reference(store, target, type_parameter);
                canonical_interface_reference(store, target, inner)
            },
            |_, type_parameter| type_parameter,
        );
        let string = store.intrinsic_bootstrap().unwrap().string_type;
        let inner = canonical_interface_reference(&mut store, target, string);
        let argument = canonical_interface_reference(&mut store, target, inner);
        let mut covariant = vec![Vec::new()];
        let mut contravariant = vec![Vec::new()];
        let before = vector_cache_graph_counts(&store);

        assert_eq!(
            collect_generic_call_inferences(
                &mut store,
                None,
                argument,
                callable.parameters[0],
                &[parameter],
                &mut covariant,
                &mut contravariant,
                callable.signature,
                &mut Vec::new(),
                false,
            ),
            Ok(()),
        );
        assert_eq!(covariant, [vec![string]]);
        assert_eq!(contravariant, [Vec::<TypeId>::new()]);
        assert_eq!(vector_cache_graph_counts(&store), before);
    }

    #[test]
    fn mixed_variance_call_prefers_contravariant_inference_over_never_and_any() {
        let mut store = initialized_store();
        let target = canonical_interface_target(&mut store, "Consumer");
        let owner = store.type_payload(target).unwrap().symbol().unwrap();
        assert!(store.set_variance_links(
            owner,
            VarianceLinks {
                variances: Some(vec![VarianceFlags::CONTRAVARIANT]),
            },
        ));
        let (mut callable, parameters) = vector_callable(
            &mut store,
            &["T"],
            &[None],
            &[None],
            &[0, 0],
            |_, parameters| parameters[0],
        );
        let consumer = canonical_interface_reference(&mut store, target, parameters[0]);
        let symbol = store.signature(callable.signature).unwrap().parameters()[1];
        assert!(store.set_value_symbol_links(
            symbol,
            ValueSymbolLinks {
                resolved_type: Some(consumer),
                ..ValueSymbolLinks::default()
            },
        ));
        callable.parameters[1] = consumer;
        let (never, any, string) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (
                bootstrap.never_type,
                bootstrap.any_type,
                bootstrap.string_type,
            )
        };
        let argument = canonical_interface_reference(&mut store, target, string);

        let resolution = project_vector(
            &mut store,
            &callable,
            vector_request(callable.owner, None, &[never, argument]),
        )
        .unwrap();

        assert_eq!(
            resolution.applicability,
            GenericCallVectorApplicability::Applicable,
        );
        assert_eq!(resolution.projection.instantiation.type_arguments, [string]);
        assert_eq!(
            demand_vector_return(
                &mut store,
                &callable,
                &resolution,
                &resolution.projection.instantiation,
            ),
            string,
        );
        let warm = vector_cache_graph_counts(&store);
        for source in [never, any] {
            let replay = project_vector(
                &mut store,
                &callable,
                vector_request(callable.owner, None, &[source, argument]),
            )
            .unwrap();
            assert_eq!(replay, resolution);
            assert_eq!(vector_cache_graph_counts(&store), warm);
        }
    }

    #[test]
    fn generic_interface_variance_rejects_malformed_caches() {
        for variances in [
            Vec::new(),
            vec![VarianceFlags::INDEPENDENT | VarianceFlags::COVARIANT],
        ] {
            let mut store = initialized_store();
            let target = canonical_interface_target(&mut store, "Box");
            let (callable, _) = structured_vector_callable(
                &mut store,
                |store, type_parameter| {
                    canonical_interface_reference(store, target, type_parameter)
                },
                |store, type_parameter| {
                    canonical_interface_reference(store, target, type_parameter)
                },
            );
            let number = store.intrinsic_bootstrap().unwrap().number_type;
            let argument = canonical_interface_reference(&mut store, target, number);
            let owner = store.type_payload(target).unwrap().symbol().unwrap();
            assert!(store.set_variance_links(
                owner,
                VarianceLinks {
                    variances: Some(variances),
                },
            ));
            let before = vector_cache_graph_counts(&store);
            let expected = GenericCallVectorError::Invariant(
                GenericCallVectorInvariant::InvalidInterfaceVariance {
                    signature: callable.signature,
                    type_: callable.parameters[0],
                },
            );

            assert_eq!(
                project_vector(
                    &mut store,
                    &callable,
                    vector_request(callable.owner, None, &[argument]),
                ),
                Err(expected),
            );
            assert_eq!(vector_cache_graph_counts(&store), before);
        }
    }

    #[test]
    fn canonical_array_target_inference_reuses_checked_cache_on_warm_calls() {
        let mut store = initialized_store();
        let targets = canonical_array_targets(&mut store);
        let (first, type_parameter) = structured_vector_callable(
            &mut store,
            |store, type_parameter| canonical_array_type(store, targets, type_parameter, false),
            |_, type_parameter| type_parameter,
        );
        let number = store.intrinsic_bootstrap().unwrap().number_type;
        let ordinary_argument = canonical_array_type(&mut store, targets, number, false);
        let argument = array_literal_clone(&mut store, targets, number);
        let resolution = project_array_vector(
            &mut store,
            targets,
            &first,
            vector_request(first.owner, None, &[argument]),
        )
        .unwrap();

        assert_eq!(
            resolution.applicability,
            GenericCallVectorApplicability::Applicable
        );
        assert_eq!(resolution.projection.type_parameters, [type_parameter]);
        assert_eq!(resolution.projection.instantiation.type_arguments, [number]);
        assert_eq!(
            demand_vector_parameter(
                &mut store,
                &first,
                &resolution,
                &resolution.projection.instantiation,
                0,
            ),
            ordinary_argument,
        );
        assert_eq!(
            demand_vector_return(
                &mut store,
                &first,
                &resolution,
                &resolution.projection.instantiation,
            ),
            number,
        );

        let materialized = materialize_vector(&mut store, &first, &resolution).unwrap();
        let GenericCallVectorMaterialization::Reused(published) = materialized else {
            panic!("resolution must already have published the checked Array shell")
        };
        let warm_counts = vector_cache_graph_counts(&store);
        assert_eq!(
            materialize_vector(&mut store, &first, &resolution),
            Ok(GenericCallVectorMaterialization::Reused(published))
        );
        assert_eq!(vector_cache_graph_counts(&store), warm_counts);

        let replay = project_array_vector(
            &mut store,
            targets,
            &first,
            vector_request(first.owner, None, &[argument]),
        )
        .unwrap();
        assert_eq!(replay, resolution);
        assert_eq!(vector_cache_graph_counts(&store), warm_counts);
    }

    #[test]
    fn canonical_array_returns_instantiate_nested_mutable_and_readonly_targets() {
        let mut store = initialized_store();
        let targets = canonical_array_targets(&mut store);
        let (wrap, _) = structured_vector_callable(
            &mut store,
            |_, type_parameter| type_parameter,
            |store, type_parameter| canonical_array_type(store, targets, type_parameter, true),
        );
        let text = fresh_string(&mut store, "x");
        let string = store.intrinsic_bootstrap().unwrap().string_type;
        let before = store.type_len();
        let wrapped = project_array_vector(
            &mut store,
            targets,
            &wrap,
            vector_request(wrap.owner, None, &[text]),
        )
        .unwrap();
        let readonly_string = canonical_array_type(&mut store, targets, string, true);
        assert_eq!(wrapped.projection.instantiation.type_arguments, [string]);
        assert_eq!(
            demand_vector_parameter(
                &mut store,
                &wrap,
                &wrapped,
                &wrapped.projection.instantiation,
                0,
            ),
            string,
        );
        assert_eq!(
            demand_vector_return(
                &mut store,
                &wrap,
                &wrapped,
                &wrapped.projection.instantiation,
            ),
            readonly_string
        );
        assert_eq!(store.type_len(), before + 1);

        let (nested, _) = structured_vector_callable(
            &mut store,
            |store, type_parameter| {
                let inner = canonical_array_type(store, targets, type_parameter, false);
                canonical_array_type(store, targets, inner, true)
            },
            |store, type_parameter| {
                let inner = canonical_array_type(store, targets, type_parameter, true);
                canonical_array_type(store, targets, inner, false)
            },
        );
        let number = store.intrinsic_bootstrap().unwrap().number_type;
        let inner_source = canonical_array_type(&mut store, targets, number, false);
        let source = canonical_array_type(&mut store, targets, inner_source, false);
        let result = project_array_vector(
            &mut store,
            targets,
            &nested,
            vector_request(nested.owner, None, &[source]),
        )
        .unwrap();
        let expected_parameter = canonical_array_type(&mut store, targets, inner_source, true);
        let readonly_number = canonical_array_type(&mut store, targets, number, true);
        let expected_return = canonical_array_type(&mut store, targets, readonly_number, false);
        assert_eq!(
            result.applicability,
            GenericCallVectorApplicability::Applicable
        );
        assert_eq!(result.projection.instantiation.type_arguments, [number]);
        assert_eq!(
            demand_vector_parameter(
                &mut store,
                &nested,
                &result,
                &result.projection.instantiation,
                0,
            ),
            expected_parameter,
        );
        assert_eq!(
            demand_vector_return(
                &mut store,
                &nested,
                &result,
                &result.projection.instantiation,
            ),
            expected_return,
        );
    }

    #[test]
    fn naked_inference_accepts_canonical_array_candidates_with_retained_targets() {
        let mut store = initialized_store();
        let targets = canonical_array_targets(&mut store);
        let (identity, _) = structured_vector_callable(
            &mut store,
            |_, type_parameter| type_parameter,
            |_, type_parameter| type_parameter,
        );
        let number = store.intrinsic_bootstrap().unwrap().number_type;
        let array = canonical_array_type(&mut store, targets, number, false);
        let resolution = project_array_vector(
            &mut store,
            targets,
            &identity,
            vector_request(identity.owner, None, &[array]),
        )
        .unwrap();

        assert_eq!(
            resolution.applicability,
            GenericCallVectorApplicability::Applicable
        );
        assert_eq!(resolution.projection.instantiation.type_arguments, [array]);
        assert_eq!(
            demand_vector_parameter(
                &mut store,
                &identity,
                &resolution,
                &resolution.projection.instantiation,
                0,
            ),
            array,
        );
        assert_eq!(
            demand_vector_return(
                &mut store,
                &identity,
                &resolution,
                &resolution.projection.instantiation,
            ),
            array,
        );
    }

    #[test]
    fn structured_array_mismatch_caches_checked_signature_and_replays_distinct_recoveries() {
        let mut store = initialized_store();
        let targets = canonical_array_targets(&mut store);
        let (first, _) = structured_vector_callable(
            &mut store,
            |store, type_parameter| canonical_array_type(store, targets, type_parameter, false),
            |_, type_parameter| type_parameter,
        );
        let (number, unknown) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (bootstrap.number_type, bootstrap.unknown_type)
        };
        let array_unknown = canonical_array_type(&mut store, targets, unknown, false);
        let resolution = project_array_vector(
            &mut store,
            targets,
            &first,
            vector_request(first.owner, None, &[number]),
        )
        .unwrap();
        assert_eq!(
            resolution.projection.instantiation.type_arguments,
            [unknown]
        );
        assert_eq!(
            demand_vector_parameter(
                &mut store,
                &first,
                &resolution,
                resolution.checked_instantiation.as_ref().unwrap(),
                0,
            ),
            array_unknown,
        );
        assert_eq!(
            resolution.applicability,
            GenericCallVectorApplicability::ArgumentNotAssignable {
                index: 0,
                argument_type: number,
                parameter_type: array_unknown,
            }
        );

        let before = vector_cache_graph_counts(&store);
        let first_call = materialize_source_vector(&mut store, &first, &resolution, None).unwrap();
        let checked = first_call.checked_instantiation.unwrap();
        assert_ne!(first_call.call_signature, checked.signature);
        assert_eq!(vector_cache_graph_counts(&store), before);
        let warm_counts = vector_cache_graph_counts(&store);
        assert_eq!(
            materialize_source_vector(
                &mut store,
                &first,
                &resolution,
                Some(first_call.call_signature),
            ),
            Ok(first_call)
        );
        assert_eq!(vector_cache_graph_counts(&store), warm_counts);

        let second_call = materialize_source_vector(&mut store, &first, &resolution, None).unwrap();
        assert_eq!(second_call.checked_instantiation, Some(checked));
        assert_eq!(second_call.call_signature, first_call.call_signature);
        assert_eq!(store.cached_signature_len(), before.cached_signatures);
        let second_warm_counts = vector_cache_graph_counts(&store);
        assert_eq!(
            materialize_source_vector(
                &mut store,
                &first,
                &resolution,
                Some(second_call.call_signature),
            ),
            Ok(second_call)
        );
        assert_eq!(vector_cache_graph_counts(&store), second_warm_counts);
    }

    #[test]
    fn forged_array_parameter_is_rejected_before_projection_writes() {
        let mut store = initialized_store();
        let targets = canonical_array_targets(&mut store);
        let mut forged = None;
        let (callable, _) = structured_vector_callable(
            &mut store,
            |store, type_parameter| {
                let canonical = canonical_array_type(store, targets, type_parameter, false);
                let symbol = store.type_payload(canonical).unwrap().symbol();
                let duplicate = store
                    .alloc_type_reference(ObjectFlags::NONE, symbol)
                    .unwrap();
                assert!(store.set_object_target_and_mapper(
                    duplicate,
                    Some(targets.array_type()),
                    None,
                ));
                assert!(store.set_type_reference_resolution(
                    duplicate,
                    None,
                    Some(vec![type_parameter]),
                ));
                forged = Some(duplicate);
                duplicate
            },
            |_, type_parameter| type_parameter,
        );
        let forged = forged.unwrap();
        let number = store.intrinsic_bootstrap().unwrap().number_type;
        let before = vector_cache_graph_counts(&store);

        assert_eq!(
            project_array_vector(
                &mut store,
                targets,
                &callable,
                vector_request(callable.owner, None, &[number]),
            ),
            Err(GenericCallVectorError::Invariant(
                GenericCallVectorInvariant::InvalidArrayType {
                    signature: callable.signature,
                    type_: forged,
                    error: ArrayTypeError::InvalidReference(forged),
                }
            ))
        );
        assert_eq!(vector_cache_graph_counts(&store), before);
    }

    #[test]
    fn vector_inference_preserves_returned_literals_and_widens_other_parameters() {
        let mut store = initialized_store();
        let (pair, parameters) = vector_callable(
            &mut store,
            &["T", "U"],
            &[None, None],
            &[None, None],
            &[0, 1],
            |_, parameters| parameters[1],
        );
        let text = fresh_string(&mut store, "x");
        let one = fresh_number(&mut store, 1.0);
        let string = store.intrinsic_bootstrap().unwrap().string_type;
        let counts = (
            store.mapper_len(),
            store.signature_len(),
            store.cached_signature_len(),
        );

        let result = project_vector(
            &mut store,
            &pair,
            vector_request(pair.owner, None, &[text, one]),
        )
        .unwrap();

        assert_eq!(
            result.applicability,
            GenericCallVectorApplicability::Applicable
        );
        assert_eq!(result.projection.type_parameters, parameters);
        assert_eq!(
            result.projection.instantiation.type_arguments,
            [string, one]
        );
        assert_eq!(
            [
                demand_vector_parameter(
                    &mut store,
                    &pair,
                    &result,
                    &result.projection.instantiation,
                    0,
                ),
                demand_vector_parameter(
                    &mut store,
                    &pair,
                    &result,
                    &result.projection.instantiation,
                    1,
                ),
            ],
            [string, one],
        );
        assert_eq!(
            demand_vector_return(&mut store, &pair, &result, &result.projection.instantiation,),
            one,
        );
        assert!(!result.projection.recovery);
        assert_eq!(
            (
                store.mapper_len(),
                store.signature_len(),
                store.cached_signature_len(),
            ),
            (counts.0 + 1, counts.1 + 1, counts.2 + 1),
            "applicability publishes one globally cached checked shell"
        );
    }

    #[test]
    fn generic_array_rest_parameters_infer_all_arguments_and_reuse_checked_signatures() {
        let mut store = initialized_store();
        let targets = canonical_array_targets(&mut store);
        let (callable, _) = rest_vector_callable(&mut store, targets, 0, true);
        let first = fresh_number(&mut store, 1.0);
        let second = fresh_number(&mut store, 2.0);
        let number = store.intrinsic_bootstrap().unwrap().number_type;

        let inferred = project_array_vector(
            &mut store,
            targets,
            &callable,
            vector_request(callable.owner, None, &[first, second]),
        )
        .unwrap();
        assert_eq!(
            inferred.applicability,
            GenericCallVectorApplicability::Applicable
        );
        assert_eq!(inferred.projection.instantiation.type_arguments, [number]);
        let instantiated_rest = demand_vector_parameter(
            &mut store,
            &callable,
            &inferred,
            &inferred.projection.instantiation,
            0,
        );
        assert_eq!(
            store
                .canonical_array_reference_with_targets(targets, instantiated_rest)
                .unwrap()
                .unwrap()
                .element_type,
            number,
        );
        let result = demand_vector_return(
            &mut store,
            &callable,
            &inferred,
            &inferred.projection.instantiation,
        );
        assert_eq!(result, instantiated_rest);
        assert!(
            store
                .signature(inferred.projection.instantiation.signature)
                .unwrap()
                .has_rest_parameter()
        );

        let warm = vector_cache_graph_counts(&store);
        let repeated = project_array_vector(
            &mut store,
            targets,
            &callable,
            vector_request(callable.owner, None, &[second, first]),
        )
        .unwrap();
        assert_eq!(
            repeated.projection.instantiation.signature,
            inferred.projection.instantiation.signature,
        );
        assert_eq!(vector_cache_graph_counts(&store), warm);

        let empty = project_array_vector(
            &mut store,
            targets,
            &callable,
            vector_request(callable.owner, None, &[]),
        )
        .unwrap();
        assert_eq!(
            empty.projection.instantiation.type_arguments,
            [store.intrinsic_bootstrap().unwrap().unknown_type],
        );
    }

    #[test]
    fn generic_array_rest_parameters_preserve_fixed_prefix_and_argument_diagnostics() {
        let mut store = initialized_store();
        let targets = canonical_array_targets(&mut store);
        let (callable, _) = rest_vector_callable(&mut store, targets, 1, false);
        let first = fresh_string(&mut store, "first");
        let second = fresh_string(&mut store, "second");
        let number = fresh_number(&mut store, 1.0);
        let string = store.intrinsic_bootstrap().unwrap().string_type;

        let inferred = project_array_vector(
            &mut store,
            targets,
            &callable,
            vector_request(callable.owner, None, &[first, second]),
        )
        .unwrap();
        assert_eq!(
            inferred.applicability,
            GenericCallVectorApplicability::Applicable
        );
        let TypeData::Union(union) = store
            .type_payload(inferred.projection.instantiation.type_arguments[0])
            .unwrap()
            .data()
        else {
            panic!("a returned type parameter must retain every rest literal candidate")
        };
        assert!(union.union.types.contains(&first));
        assert!(union.union.types.contains(&second));

        let wrong = project_array_vector(
            &mut store,
            targets,
            &callable,
            vector_request(callable.owner, Some(&[string]), &[first, number]),
        )
        .unwrap();
        assert_eq!(
            wrong.applicability,
            GenericCallVectorApplicability::ArgumentNotAssignable {
                index: 1,
                argument_type: number,
                parameter_type: string,
            },
        );
        assert!(wrong.projection.recovery);
        assert!(wrong.checked_instantiation.is_some());

        let missing = project_array_vector(
            &mut store,
            targets,
            &callable,
            vector_request(callable.owner, None, &[]),
        )
        .unwrap();
        assert_eq!(
            missing.applicability,
            GenericCallVectorApplicability::TooFewArguments {
                expected: 1,
                actual: 0,
            },
        );
    }

    #[test]
    fn generic_array_rest_parameters_keep_fixed_primitive_prefix_out_of_inference() {
        let mut store = initialized_store();
        let targets = canonical_array_targets(&mut store);
        let (mut callable, _) = rest_vector_callable(&mut store, targets, 1, true);
        let (string, number) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (bootstrap.string_type, bootstrap.number_type)
        };
        let prefix = store.signature(callable.signature).unwrap().parameters()[0];
        assert!(store.set_value_symbol_links(
            prefix,
            ValueSymbolLinks {
                resolved_type: Some(string),
                ..ValueSymbolLinks::default()
            },
        ));
        callable.parameters[0] = string;
        let label = fresh_string(&mut store, "label");
        let first = fresh_number(&mut store, 1.0);
        let second = fresh_number(&mut store, 2.0);

        let inferred = project_array_vector(
            &mut store,
            targets,
            &callable,
            vector_request(callable.owner, None, &[label, first, second]),
        )
        .unwrap();
        assert_eq!(
            inferred.applicability,
            GenericCallVectorApplicability::Applicable,
        );
        assert_eq!(inferred.projection.instantiation.type_arguments, [number]);
        assert_eq!(
            demand_vector_parameter(
                &mut store,
                &callable,
                &inferred,
                &inferred.projection.instantiation,
                0,
            ),
            string,
        );
        let result = demand_vector_return(
            &mut store,
            &callable,
            &inferred,
            &inferred.projection.instantiation,
        );
        assert_eq!(
            store
                .canonical_array_reference_with_targets(targets, result)
                .unwrap()
                .unwrap()
                .element_type,
            number,
        );

        let warm = vector_cache_graph_counts(&store);
        let repeated = project_array_vector(
            &mut store,
            targets,
            &callable,
            vector_request(callable.owner, None, &[label, second]),
        )
        .unwrap();
        assert_eq!(
            repeated.projection.instantiation.signature,
            inferred.projection.instantiation.signature,
        );
        assert_eq!(vector_cache_graph_counts(&store), warm);

        let wrong_prefix = project_array_vector(
            &mut store,
            targets,
            &callable,
            vector_request(callable.owner, None, &[first, second]),
        )
        .unwrap();
        assert_eq!(
            wrong_prefix.applicability,
            GenericCallVectorApplicability::ArgumentNotAssignable {
                index: 0,
                argument_type: first,
                parameter_type: string,
            },
        );

        let wrong_rest = project_array_vector(
            &mut store,
            targets,
            &callable,
            vector_request(callable.owner, None, &[label, first, label]),
        )
        .unwrap();
        assert_eq!(
            wrong_rest.applicability,
            GenericCallVectorApplicability::ArgumentNotAssignable {
                index: 2,
                argument_type: label,
                parameter_type: number,
            },
        );
    }

    #[test]
    fn generic_fixed_parameters_reject_unauthenticated_objects_before_cache_writes() {
        let mut store = initialized_store();
        let targets = canonical_array_targets(&mut store);
        let (mut callable, _) = rest_vector_callable(&mut store, targets, 1, true);
        let forged = store
            .alloc_plain_object_type(ObjectFlags::ANONYMOUS, None)
            .unwrap();
        let prefix = store.signature(callable.signature).unwrap().parameters()[0];
        assert!(store.set_value_symbol_links(
            prefix,
            ValueSymbolLinks {
                resolved_type: Some(forged),
                ..ValueSymbolLinks::default()
            },
        ));
        callable.parameters[0] = forged;
        let number = store.intrinsic_bootstrap().unwrap().number_type;
        let before = vector_cache_graph_counts(&store);

        assert_eq!(
            project_array_vector(
                &mut store,
                targets,
                &callable,
                vector_request(callable.owner, None, &[forged, number]),
            ),
            Err(GenericCallVectorError::Unsupported(
                GenericCallVectorUnsupported::NonNakedParameter {
                    signature: callable.signature,
                    index: 0,
                    type_: forged,
                },
            )),
        );
        assert_eq!(vector_cache_graph_counts(&store), before);
    }

    #[test]
    fn generic_rest_rejects_readonly_arrays_without_publishing_signature_cache_entries() {
        let mut store = initialized_store();
        let targets = canonical_array_targets(&mut store);
        let (mut callable, type_parameter) = rest_vector_callable(&mut store, targets, 0, false);
        let readonly = canonical_array_type(&mut store, targets, type_parameter, true);
        let symbol = store.signature(callable.signature).unwrap().parameters()[0];
        assert!(store.set_value_symbol_links(
            symbol,
            ValueSymbolLinks {
                resolved_type: Some(readonly),
                ..ValueSymbolLinks::default()
            },
        ));
        callable.rest_parameter = Some(readonly);
        let before = vector_cache_graph_counts(&store);

        assert_eq!(
            project_array_vector(
                &mut store,
                targets,
                &callable,
                vector_request(callable.owner, None, &[]),
            ),
            Err(GenericCallVectorError::Unsupported(
                GenericCallVectorUnsupported::RestSignature(callable.signature),
            )),
        );
        assert_eq!(vector_cache_graph_counts(&store), before);
    }

    #[test]
    fn repeated_same_base_candidates_form_the_raw_literal_union() {
        let mut store = initialized_store();
        let (choose, _) = vector_callable(
            &mut store,
            &["T"],
            &[None],
            &[None],
            &[0, 0],
            |_, parameters| parameters[0],
        );
        let a = fresh_string(&mut store, "a");
        let b = fresh_string(&mut store, "b");

        let result = project_vector(
            &mut store,
            &choose,
            vector_request(choose.owner, None, &[a, b]),
        )
        .unwrap();

        assert_eq!(
            result.applicability,
            GenericCallVectorApplicability::Applicable
        );
        let inferred = result.projection.instantiation.type_arguments[0];
        assert_eq!(
            demand_vector_return(
                &mut store,
                &choose,
                &result,
                &result.projection.instantiation,
            ),
            inferred,
        );
        let TypeData::Union(data) = store.type_payload(inferred).unwrap().data() else {
            panic!("choose('a', 'b') must infer a literal union");
        };
        assert_eq!(data.union.types.len(), 2);
        assert!(data.union.types.contains(&a));
        assert!(data.union.types.contains(&b));
    }

    #[test]
    fn declaration_order_defaults_and_union_returns_use_the_full_vector() {
        let mut store = initialized_store();
        let (fallback, parameters) = vector_callable(
            &mut store,
            &["T", "U"],
            &[None, None],
            &[None, Some(GenericTypeSpec::Parameter(0))],
            &[0],
            |_, parameters| parameters[1],
        );
        let text = fresh_string(&mut store, "x");
        let string = store.intrinsic_bootstrap().unwrap().string_type;
        let fallback_result = project_vector(
            &mut store,
            &fallback,
            vector_request(fallback.owner, None, &[text]),
        )
        .unwrap();
        assert_eq!(
            fallback_result.projection.instantiation.type_arguments,
            [string, string]
        );
        assert_eq!(
            demand_vector_return(
                &mut store,
                &fallback,
                &fallback_result,
                &fallback_result.projection.instantiation,
            ),
            string,
        );

        let (both, _) = vector_callable(
            &mut store,
            &["A", "B"],
            &[None, None],
            &[None, None],
            &[0, 1],
            |store, parameters| {
                store
                    .alloc_union_type(ObjectFlags::NONE, parameters.to_vec())
                    .unwrap()
            },
        );
        let one = fresh_number(&mut store, 1.0);
        let both_result = project_vector(
            &mut store,
            &both,
            vector_request(both.owner, None, &[text, one]),
        )
        .unwrap();
        assert_eq!(
            both_result.projection.instantiation.type_arguments,
            [text, one]
        );
        let both_return = demand_vector_return(
            &mut store,
            &both,
            &both_result,
            &both_result.projection.instantiation,
        );
        let TypeData::Union(data) = store.type_payload(both_return).unwrap().data() else {
            panic!("T | U must instantiate through the full mapper vector");
        };
        assert!(data.union.types.contains(&text));
        assert!(data.union.types.contains(&one));
        assert_ne!(parameters[0], parameters[1]);
    }

    #[test]
    fn inferred_constraints_fallback_before_left_to_right_applicability() {
        let mut store = initialized_store();
        let (string, number) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (bootstrap.string_type, bootstrap.number_type)
        };
        let (dependent, _) = vector_callable(
            &mut store,
            &["T", "U"],
            &[None, Some(GenericTypeSpec::Parameter(0))],
            &[None, None],
            &[0, 1],
            |_, parameters| parameters[1],
        );
        let text = fresh_string(&mut store, "x");
        let one = fresh_number(&mut store, 1.0);

        let result = project_vector(
            &mut store,
            &dependent,
            vector_request(dependent.owner, None, &[text, one]),
        )
        .unwrap();

        assert_eq!(
            result
                .checked_instantiation
                .as_ref()
                .unwrap()
                .type_arguments,
            [string, string]
        );
        assert_eq!(
            result.applicability,
            GenericCallVectorApplicability::ArgumentNotAssignable {
                index: 1,
                argument_type: one,
                parameter_type: string,
            }
        );
        assert_eq!(result.applicability.diagnostic_code(), Some(2345));
        assert_eq!(
            demand_vector_return(
                &mut store,
                &dependent,
                &result,
                &result.projection.instantiation,
            ),
            string,
        );
        assert_ne!(number, string);
    }

    #[test]
    fn declared_constraint_shape_controls_literal_regularization() {
        let mut store = initialized_store();
        let string = store.intrinsic_bootstrap().unwrap().string_type;
        let a_regular = store.regular_string_literal_type("a".into()).unwrap();
        let b_regular = store.regular_string_literal_type("b".into()).unwrap();
        let c_regular = store.regular_string_literal_type("c".into()).unwrap();
        let a = store.fresh_type_of_literal_type(a_regular).unwrap();
        let b = store.fresh_type_of_literal_type(b_regular).unwrap();
        let c = store.fresh_type_of_literal_type(c_regular).unwrap();

        let (dependent, _) = vector_callable(
            &mut store,
            &["T", "U"],
            &[None, Some(GenericTypeSpec::Parameter(0))],
            &[None, None],
            &[0, 1, 1],
            |_, parameters| parameters[1],
        );
        let dependent_result = project_vector(
            &mut store,
            &dependent,
            vector_request(dependent.owner, None, &[a, b, c]),
        )
        .unwrap();
        assert_eq!(
            dependent_result.applicability,
            GenericCallVectorApplicability::Applicable
        );
        assert_eq!(
            dependent_result.projection.instantiation.type_arguments[0],
            string
        );
        let dependent_inference = dependent_result.projection.instantiation.type_arguments[1];
        let TypeData::Union(data) = store.type_payload(dependent_inference).unwrap().data() else {
            panic!("U extends T must preserve the fresh repeated candidates");
        };
        assert!(data.union.types.contains(&b));
        assert!(data.union.types.contains(&c));
        assert!(!data.union.types.contains(&b_regular));
        assert!(!data.union.types.contains(&c_regular));

        let (direct, _) = vector_callable(
            &mut store,
            &["T"],
            &[Some(GenericTypeSpec::Exact(string))],
            &[None],
            &[0, 0],
            |_, parameters| parameters[0],
        );
        let direct_result = project_vector(
            &mut store,
            &direct,
            vector_request(direct.owner, None, &[b, c]),
        )
        .unwrap();
        assert_eq!(
            direct_result.applicability,
            GenericCallVectorApplicability::Applicable
        );
        let direct_inference = direct_result.projection.instantiation.type_arguments[0];
        let TypeData::Union(data) = store.type_payload(direct_inference).unwrap().data() else {
            panic!("a direct primitive constraint must retain a regular literal union");
        };
        assert!(data.union.types.contains(&b_regular));
        assert!(data.union.types.contains(&c_regular));
        assert!(!data.union.types.contains(&b));
        assert!(!data.union.types.contains(&c));
    }

    #[test]
    #[allow(clippy::too_many_lines)] // One source graph proves cache identity and call outcomes.
    fn named_keyof_constraints_preserve_origin_and_reject_forged_cache_identities() {
        let parsed =
            parse_source_file("interface Types { a: string; b: number } type Keys = keyof Types;");
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(96_401);
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source("\"/generic-keyof.ts\""),
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
        let keyof = parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::TypeOperator).then_some(NodeRef::new(
                    parsed.arena.id(),
                    file,
                    node,
                ))
            })
            .unwrap();
        let constraint = context.get_type_from_type_node(keyof).unwrap();
        let store = context.store_mut_for_test();
        let (interface, keys) = {
            let TypeData::Union(union) = store.type_payload(constraint).unwrap().data() else {
                panic!("named keyof must retain its property-key union")
            };
            let origin = union
                .origin
                .expect("named keyof must retain an index origin");
            let TypeData::Index(index) = store.type_payload(origin).unwrap().data() else {
                panic!("named keyof origin must be an index type")
            };
            (index.target, union.union.types.clone())
        };
        assert!(authenticated_nongeneric_keyof_union(store, constraint));

        let (callable, _) = vector_callable(
            store,
            &["T"],
            &[Some(GenericTypeSpec::Exact(constraint))],
            &[None],
            &[0],
            |_, parameters| parameters[0],
        );
        let a = store.regular_string_literal_type("a".into()).unwrap();
        let b = store.regular_string_literal_type("b".into()).unwrap();
        let c = store.regular_string_literal_type("c".into()).unwrap();
        let string = store.intrinsic_bootstrap().unwrap().string_type;
        let (union_callable, union_parameter, _) = union_vector_callable(store, &[string]);
        assert_eq!(
            generic_call_mapped_union_constituents(
                store,
                None,
                union_parameter,
                &[union_parameter],
                &[constraint],
            ),
            Some(keys.as_slice()),
        );
        let union_resolution = project_vector(
            store,
            &union_callable,
            vector_request(union_callable.owner, Some(&[constraint]), &[a]),
        )
        .unwrap();
        assert_eq!(
            union_resolution.projection.instantiation.type_arguments,
            [constraint],
        );
        let union_warm = vector_cache_graph_counts(store);
        assert_eq!(
            project_vector(
                store,
                &union_callable,
                vector_request(union_callable.owner, Some(&[constraint]), &[a]),
            ),
            Ok(union_resolution),
        );
        assert_eq!(vector_cache_graph_counts(store), union_warm);

        let inferred =
            project_vector(store, &callable, vector_request(callable.owner, None, &[a])).unwrap();
        assert_eq!(
            inferred.applicability,
            GenericCallVectorApplicability::Applicable
        );
        assert_eq!(inferred.projection.instantiation.type_arguments, [a]);
        let cached_counts = vector_cache_graph_counts(store);
        let warm =
            project_vector(store, &callable, vector_request(callable.owner, None, &[a])).unwrap();
        assert_eq!(warm.projection, inferred.projection);
        assert_eq!(vector_cache_graph_counts(store), cached_counts);

        let explicit = project_vector(
            store,
            &callable,
            vector_request(callable.owner, Some(&[b]), &[b]),
        )
        .unwrap();
        assert_eq!(
            explicit.applicability,
            GenericCallVectorApplicability::Applicable
        );
        assert_eq!(explicit.projection.instantiation.type_arguments, [b]);

        let rejected = project_vector(
            store,
            &callable,
            vector_request(callable.owner, Some(&[c]), &[c]),
        )
        .unwrap();
        assert_eq!(
            rejected.applicability,
            GenericCallVectorApplicability::ExplicitTypeArgumentConstraint {
                index: 0,
                type_argument: c,
                constraint,
            }
        );

        let inferred_rejection =
            project_vector(store, &callable, vector_request(callable.owner, None, &[c])).unwrap();
        assert_eq!(
            inferred_rejection.applicability,
            GenericCallVectorApplicability::ArgumentNotAssignable {
                index: 0,
                argument_type: c,
                parameter_type: constraint,
            }
        );
        assert_eq!(
            inferred_rejection
                .checked_instantiation
                .as_ref()
                .unwrap()
                .type_arguments,
            [constraint]
        );
        assert_eq!(
            demand_vector_return(
                store,
                &callable,
                &inferred_rejection,
                &inferred_rejection.projection.instantiation,
            ),
            constraint
        );

        let (defaulted, _) = vector_callable_with_minimum(
            store,
            &["V"],
            &[None],
            &[Some(GenericTypeSpec::Exact(constraint))],
            &[0],
            0,
            |_, parameters| parameters[0],
        );
        let defaulted_result = project_vector(
            store,
            &defaulted,
            vector_request(defaulted.owner, None, &[]),
        )
        .unwrap();
        assert_eq!(
            defaulted_result.applicability,
            GenericCallVectorApplicability::Applicable
        );
        assert_eq!(
            defaulted_result.projection.instantiation.type_arguments,
            [constraint]
        );

        let mut prepared = store.prepare_type_query_types(&[], &[], &[], 1, 0).unwrap();
        let forged_origin = store.alloc_index_type(interface, IndexFlags::NONE).unwrap();
        let forged = store
            .literal_union_type_prepared_with_index_origin(&keys, forged_origin, &mut prepared)
            .unwrap();
        assert_ne!(forged, constraint);
        assert!(!authenticated_nongeneric_keyof_union(store, forged));
        assert_eq!(
            generic_call_mapped_union_constituents(
                store,
                None,
                union_parameter,
                &[union_parameter],
                &[forged],
            ),
            None,
        );
        assert!(!generic_call_union_instantiation_matches(
            store,
            None,
            &[union_parameter, string],
            string,
            &[union_parameter],
            &[forged],
            &mut Vec::new(),
        ));
        let (forged_callable, parameters) = vector_callable(
            store,
            &["U"],
            &[Some(GenericTypeSpec::Exact(forged))],
            &[None],
            &[0],
            |_, parameters| parameters[0],
        );
        let before = vector_cache_graph_counts(store);
        assert_eq!(
            project_vector(
                store,
                &forged_callable,
                vector_request(forged_callable.owner, None, &[a]),
            ),
            Err(GenericCallVectorError::Unsupported(
                GenericCallVectorUnsupported::TypeParameterDependency {
                    type_parameter: parameters[0],
                    dependency: forged,
                }
            ))
        );
        assert_eq!(vector_cache_graph_counts(store), before);
    }

    #[test]
    #[allow(clippy::too_many_lines)] // One source graph proves cold, warm, and forged callables.
    fn contextual_rest_inference_reuses_checked_signature_inside_an_active_relation() {
        let library = parse_source_file("interface Array<T> {} interface ReadonlyArray<T> {}");
        let parsed = parse_source_file(concat!(
            "declare function toInstantiate<A, B>(a?: A, b?: B): B; ",
            "declare function contextual(...s: string[]): string;",
        ));
        assert!(library.diagnostics.is_empty(), "{:?}", library.diagnostics);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let library_file = FileId::new(96_400);
        let file = FileId::new(96_402);
        let mut binder = CanonicalBinder::new();
        for (source, source_file, path) in [
            (
                &library,
                library_file,
                "\"/contextual-generic-rest-lib.d.ts\"",
            ),
            (&parsed, file, "\"/contextual-generic-rest.ts\""),
        ] {
            binder
                .bind_source_file_with_facts(
                    &source.arena,
                    source.source_file,
                    source_file,
                    CanonicalSourceFileFacts::new(
                        EscapedName::source(path),
                        CanonicalSourceLanguage::TypeScript,
                        false,
                        CanonicalModuleState::Script,
                    ),
                )
                .unwrap();
            binder
                .bind_typescript_declaration_slice(&source.arena, source_file)
                .unwrap();
        }
        let mut context = CanonicalCheckerContext::new(
            binder.finish(),
            [(library_file, &library.arena), (file, &parsed.arena)]
                .into_iter()
                .collect(),
            CanonicalCheckerOptions::default(),
        )
        .unwrap();
        context.check_source_file(file).unwrap();
        let callable = |expected: &str| {
            let declaration = parsed
                .arena
                .iter()
                .find_map(|(node, record)| {
                    let NodeData::FunctionDeclaration(function) = &record.data else {
                        return None;
                    };
                    let name = function.name?;
                    let NodeData::Identifier(identifier) = &parsed.arena.get(name)?.data else {
                        return None;
                    };
                    (identifier.text == expected).then_some(NodeRef::new(
                        parsed.arena.id(),
                        file,
                        node,
                    ))
                })
                .unwrap();
            let owner = context.file(file).unwrap().1.symbol(declaration).unwrap();
            let type_ = context
                .store()
                .source_callable_type_for_owner(owner)
                .unwrap();
            match validate_stored_single_callable(context.store(), type_) {
                StoredSingleCallableValidation::Valid { callable, .. } => callable,
                other => panic!("expected validated source callable {expected}: {other:?}"),
            }
        };
        let source = callable("toInstantiate");
        let contextual = callable("contextual");
        let array_targets = CanonicalArrayTargets::from_global_types(context.global_types());
        let string = context.store().intrinsic_bootstrap().unwrap().string_type;
        let type_parameters = context
            .store()
            .signature(source.signature)
            .unwrap()
            .type_parameters()
            .to_vec();
        let store = context.store_mut_for_test();
        let before = vector_cache_graph_counts(store);
        let observation = store.begin_relation_read_observation().unwrap();

        let inferred = instantiate_generic_signature_in_context_of(
            store,
            &source,
            &contextual,
            Some(array_targets),
        )
        .unwrap();

        assert!(store.relation_read_observation_is_active());
        assert!(store.discard_relation_read_observation(observation));
        assert_eq!(inferred.owner, source.owner);
        assert_eq!(inferred.parameters, [string, string]);
        assert_eq!(inferred.rest_parameter, None);
        assert_eq!(inferred.min_argument_count, 0);
        assert_eq!(inferred.return_type, Some(string));
        assert_eq!(
            store.cached_signatures_contain(inferred.signature),
            Some(true)
        );
        let instantiated = store.signature(inferred.signature).unwrap();
        assert_eq!(instantiated.target(), Some(source.signature));
        let mapper = instantiated.mapper().unwrap();
        assert_eq!(
            store.type_mapper_has_exact_endpoints(mapper, &type_parameters, &[string, string]),
            Some(true),
        );
        let after = vector_cache_graph_counts(store);
        assert_eq!(after.signatures, before.signatures + 1);
        assert_eq!(after.mappers, before.mappers + 1);
        assert_eq!(after.cached_signatures, before.cached_signatures + 1);

        let warm = instantiate_generic_signature_in_context_of(
            store,
            &source,
            &contextual,
            Some(array_targets),
        )
        .unwrap();
        assert_eq!(warm, inferred);
        assert_eq!(vector_cache_graph_counts(store), after);

        let mut forged = contextual.clone();
        forged.parameters.push(string);
        assert_eq!(
            instantiate_generic_signature_in_context_of(
                store,
                &source,
                &forged,
                Some(array_targets),
            ),
            Err(GenericCallVectorError::Invariant(
                GenericCallVectorInvariant::CallableSignatureMismatch(contextual.signature),
            )),
        );
        assert_eq!(vector_cache_graph_counts(store), after);
    }

    #[test]
    fn explicit_constraint_failure_is_ts2344_and_suppresses_argument_failure() {
        let mut store = initialized_store();
        let (string, number) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (bootstrap.string_type, bootstrap.number_type)
        };
        let (constrained, _) = vector_callable(
            &mut store,
            &["T"],
            &[Some(GenericTypeSpec::Exact(string))],
            &[None],
            &[0],
            |_, parameters| parameters[0],
        );

        let result = project_vector(
            &mut store,
            &constrained,
            vector_request(constrained.owner, Some(&[number]), &[string]),
        )
        .unwrap();

        assert_eq!(
            result.applicability,
            GenericCallVectorApplicability::ExplicitTypeArgumentConstraint {
                index: 0,
                type_argument: number,
                constraint: string,
            }
        );
        assert_eq!(result.applicability.diagnostic_code(), Some(2344));
        assert_eq!(
            demand_vector_return(
                &mut store,
                &constrained,
                &result,
                &result.projection.instantiation,
            ),
            number,
        );
        assert!(result.projection.recovery);
    }

    #[test]
    fn type_arity_precedes_value_arity_and_recovers_default_constraint_unknown() {
        let mut store = initialized_store();
        let (string, number, boolean) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (
                bootstrap.string_type,
                bootstrap.number_type,
                bootstrap.boolean_type,
            )
        };
        let (pair, _) = vector_callable(
            &mut store,
            &["T", "U"],
            &[None, None],
            &[None, None],
            &[0, 1],
            |_, parameters| parameters[1],
        );
        let missing = project_vector(
            &mut store,
            &pair,
            vector_request(pair.owner, Some(&[string]), &[]),
        )
        .unwrap();
        let unknown = store.intrinsic_bootstrap().unwrap().unknown_type;
        assert_eq!(
            missing.applicability,
            GenericCallVectorApplicability::TypeArgumentArity {
                minimum: 2,
                maximum: 2,
                actual: 1,
            }
        );
        assert_eq!(missing.applicability.diagnostic_code(), Some(2558));
        assert_eq!(
            missing.projection.instantiation.type_arguments,
            [string, unknown]
        );
        assert_eq!(
            demand_vector_return(
                &mut store,
                &pair,
                &missing,
                &missing.projection.instantiation,
            ),
            unknown,
        );

        let (fallback, _) = vector_callable(
            &mut store,
            &["A", "B"],
            &[None, None],
            &[None, Some(GenericTypeSpec::Parameter(0))],
            &[0],
            |_, parameters| parameters[1],
        );
        let extra = project_vector(
            &mut store,
            &fallback,
            vector_request(
                fallback.owner,
                Some(&[string, number, boolean]),
                &[string, number],
            ),
        )
        .unwrap();
        assert_eq!(extra.applicability.diagnostic_code(), Some(2558));
        assert_eq!(
            extra.projection.instantiation.type_arguments,
            [string, number]
        );
        assert_eq!(
            demand_vector_return(
                &mut store,
                &fallback,
                &extra,
                &extra.projection.instantiation,
            ),
            number,
        );

        let (defaulted, _) = vector_callable(
            &mut store,
            &["T"],
            &[None],
            &[Some(GenericTypeSpec::Exact(string))],
            &[0],
            |_, parameters| parameters[0],
        );
        let empty = project_vector(
            &mut store,
            &defaulted,
            vector_request(defaulted.owner, Some(&[]), &[number]),
        )
        .unwrap();
        assert_eq!(
            empty.applicability,
            GenericCallVectorApplicability::Applicable,
            "the source grammar consumer owns TS1099 and zero type arguments trigger inference"
        );
        assert_eq!(empty.projection.instantiation.type_arguments, [number]);
    }

    #[test]
    fn valid_partial_explicit_failure_exposes_raw_default_recovery_projection() {
        let mut store = initialized_store();
        let (string, number) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (bootstrap.string_type, bootstrap.number_type)
        };
        let (two, parameters) = vector_callable(
            &mut store,
            &["T", "U"],
            &[None, None],
            &[None, Some(GenericTypeSpec::Parameter(0))],
            &[0, 1],
            |_, parameters| parameters[1],
        );
        let result = project_vector(
            &mut store,
            &two,
            vector_request(two.owner, Some(&[string]), &[string, number]),
        )
        .unwrap();

        let checked = result.checked_instantiation.as_ref().unwrap();
        assert_eq!(checked.type_arguments, [string, string]);
        assert_eq!(
            result.applicability,
            GenericCallVectorApplicability::ArgumentNotAssignable {
                index: 1,
                argument_type: number,
                parameter_type: string,
            }
        );
        assert_eq!(
            result.projection.instantiation.type_arguments,
            [string, parameters[0]]
        );
        assert_eq!(
            demand_vector_return(&mut store, &two, &result, &result.projection.instantiation,),
            parameters[0],
            "pinned overload-failure recovery maps U to the raw default T once"
        );
    }

    #[test]
    fn explicit_constraints_are_checked_in_declaration_order() {
        let mut store = initialized_store();
        let (string, number, boolean) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (
                bootstrap.string_type,
                bootstrap.number_type,
                bootstrap.boolean_type,
            )
        };
        let (ordered, _) = vector_callable(
            &mut store,
            &["T", "U"],
            &[
                Some(GenericTypeSpec::Exact(string)),
                Some(GenericTypeSpec::Exact(number)),
            ],
            &[None, None],
            &[0, 1],
            |store, parameters| {
                store
                    .alloc_union_type(ObjectFlags::NONE, parameters.to_vec())
                    .unwrap()
            },
        );
        let first = project_vector(
            &mut store,
            &ordered,
            vector_request(ordered.owner, Some(&[boolean, string]), &[boolean, string]),
        )
        .unwrap();
        assert!(matches!(
            first.applicability,
            GenericCallVectorApplicability::ExplicitTypeArgumentConstraint { index: 0, .. }
        ));
        let second = project_vector(
            &mut store,
            &ordered,
            vector_request(ordered.owner, Some(&[string, boolean]), &[string, boolean]),
        )
        .unwrap();
        assert!(matches!(
            second.applicability,
            GenericCallVectorApplicability::ExplicitTypeArgumentConstraint { index: 1, .. }
        ));
    }

    #[test]
    fn vector_base_constraint_cache_must_be_cold_or_the_exact_eventual_base() {
        let mut store = initialized_store();
        let (no_constraint, string, number, boolean) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (
                bootstrap.no_constraint_type,
                bootstrap.string_type,
                bootstrap.number_type,
                bootstrap.boolean_type,
            )
        };

        let (free, free_parameters) = vector_callable(
            &mut store,
            &["T"],
            &[None],
            &[None],
            &[0],
            |_, parameters| parameters[0],
        );
        assert!(store.set_resolved_base_constraint(free_parameters[0], Some(no_constraint)));
        assert_eq!(
            project_vector(
                &mut store,
                &free,
                vector_request(free.owner, None, &[string]),
            )
            .unwrap()
            .applicability,
            GenericCallVectorApplicability::Applicable
        );
        assert!(store.set_resolved_base_constraint(free_parameters[0], Some(string)));
        assert_eq!(
            project_vector(
                &mut store,
                &free,
                vector_request(free.owner, None, &[string]),
            ),
            Err(GenericCallVectorError::Invariant(
                GenericCallVectorInvariant::InvalidTypeParameter(free_parameters[0])
            ))
        );

        let (boolean_constrained, boolean_parameters) = vector_callable(
            &mut store,
            &["T"],
            &[Some(GenericTypeSpec::Exact(boolean))],
            &[None],
            &[0],
            |_, parameters| parameters[0],
        );
        assert!(store.set_resolved_base_constraint(boolean_parameters[0], Some(boolean)));
        assert_eq!(
            project_vector(
                &mut store,
                &boolean_constrained,
                vector_request(boolean_constrained.owner, None, &[boolean]),
            )
            .unwrap()
            .applicability,
            GenericCallVectorApplicability::Applicable,
            "the canonical boolean union is its own primitive base constraint"
        );

        let (dependent, dependent_parameters) = vector_callable(
            &mut store,
            &["T", "U"],
            &[
                Some(GenericTypeSpec::Exact(string)),
                Some(GenericTypeSpec::Parameter(0)),
            ],
            &[None, None],
            &[0, 1],
            |_, parameters| parameters[1],
        );
        assert_eq!(
            project_vector(
                &mut store,
                &dependent,
                vector_request(dependent.owner, None, &[string, string]),
            )
            .unwrap()
            .applicability,
            GenericCallVectorApplicability::Applicable,
            "both dependent base-constraint caches may remain cold"
        );
        for parameter in &dependent_parameters {
            assert!(store.set_resolved_base_constraint(*parameter, Some(string)));
        }
        assert_eq!(
            project_vector(
                &mut store,
                &dependent,
                vector_request(dependent.owner, None, &[string, string]),
            )
            .unwrap()
            .applicability,
            GenericCallVectorApplicability::Applicable,
            "U extends T has T's eventual string base"
        );
        assert!(store.set_resolved_base_constraint(dependent_parameters[1], Some(number)));
        assert_eq!(
            project_vector(
                &mut store,
                &dependent,
                vector_request(dependent.owner, None, &[string, string]),
            ),
            Err(GenericCallVectorError::Invariant(
                GenericCallVectorInvariant::InvalidTypeParameter(dependent_parameters[1])
            ))
        );
    }

    #[test]
    fn mixed_inference_keeps_leftmost_recovery_candidate_and_reports_first_mismatch() {
        let mut store = initialized_store();
        let (choose, _) = vector_callable(
            &mut store,
            &["T"],
            &[None],
            &[None],
            &[0, 0],
            |_, parameters| parameters[0],
        );
        let one = fresh_number(&mut store, 1.0);
        let text = fresh_string(&mut store, "b");

        let result = project_vector(
            &mut store,
            &choose,
            vector_request(choose.owner, None, &[one, text]),
        )
        .unwrap();

        assert_eq!(
            demand_vector_return(
                &mut store,
                &choose,
                &result,
                &result.projection.instantiation,
            ),
            one,
        );
        assert_eq!(
            result.applicability,
            GenericCallVectorApplicability::ArgumentNotAssignable {
                index: 1,
                argument_type: text,
                parameter_type: one,
            }
        );
    }

    #[test]
    fn vector_checked_materialization_publishes_exact_ordered_cache_and_reuses_it() {
        let mut store = initialized_store();
        let (string, number) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (bootstrap.string_type, bootstrap.number_type)
        };
        let (pair, type_parameters) = vector_callable(
            &mut store,
            &["T", "U"],
            &[None, None],
            &[None, None],
            &[0, 1],
            |_, parameters| parameters[1],
        );
        let resolution = project_vector(
            &mut store,
            &pair,
            vector_request(pair.owner, Some(&[string, number]), &[string, number]),
        )
        .unwrap();
        let checked = resolution.checked_instantiation.as_ref().unwrap().clone();
        let before = vector_cache_graph_counts(&store);

        let first = materialize_vector(&mut store, &pair, &resolution).unwrap();
        let GenericCallVectorMaterialization::Reused(cached) = first else {
            panic!("resolution must publish the checked shell before applicability");
        };
        assert_eq!(vector_cache_graph_counts(&store), before);
        assert_eq!(
            store.type_mapper_has_exact_endpoints(
                cached.mapper,
                &type_parameters,
                &[string, number],
            ),
            Some(true)
        );
        let original = store.signature(pair.signature).unwrap();
        let original_parameters = original.parameters().to_vec();
        let original_flags = original.flags();
        let original_declaration = original.declaration();
        let original_min_argument_count = original.min_argument_count();
        let instantiated = store.signature(cached.signature).unwrap();
        assert_eq!(
            instantiated.flags(),
            original_flags & SignatureFlags::PROPAGATING_FLAGS
        );
        assert_eq!(instantiated.declaration(), original_declaration);
        assert!(instantiated.type_parameters().is_empty());
        assert_eq!(instantiated.this_parameter(), None);
        assert_eq!(instantiated.resolved_return_type(), None);
        assert_eq!(instantiated.resolved_type_predicate(), None);
        assert_eq!(
            instantiated.min_argument_count(),
            original_min_argument_count
        );
        assert_eq!(instantiated.resolved_min_argument_count(), -1);
        assert_eq!(instantiated.target(), Some(pair.signature));
        assert_eq!(instantiated.mapper(), Some(cached.mapper));
        assert_eq!(instantiated.isolated_signature_type(), None);
        assert_eq!(instantiated.composite(), None);
        assert_eq!(instantiated.parameters().len(), 2);
        for (index, ((parameter, target), template)) in instantiated
            .parameters()
            .iter()
            .copied()
            .zip(original_parameters)
            .zip(pair.parameters.iter().copied())
            .enumerate()
        {
            assert!(cached_instantiated_parameter_shell(
                &store,
                parameter,
                target,
                cached.mapper,
                template,
                &type_parameters,
                &checked.type_arguments,
                None,
            ));
            assert_eq!(
                store
                    .value_symbol_links(parameter)
                    .and_then(|links| links.resolved_type),
                Some([string, number][index]),
                "applicability must demand used parameters left-to-right",
            );
        }
        assert_eq!(
            store.cached_signature(
                pair.signature,
                type_list_key(&checked.type_arguments),
                &checked.type_arguments,
            ),
            CachedSignatureLookup::Hit(cached.signature)
        );

        let shape = validate_generic_call_signature_shape(&store, pair.owner, &pair, None).unwrap();
        let mut session = InstantiationSession::new(InstantiationLimits::default());
        assert_eq!(
            demand_generic_call_vector_return(
                &mut store,
                &shape,
                &type_parameters,
                &checked.type_arguments,
                cached.signature,
                &mut session,
            ),
            Ok(number),
        );

        let warm_counts = vector_cache_graph_counts(&store);
        assert_eq!(
            materialize_vector(&mut store, &pair, &resolution),
            Ok(GenericCallVectorMaterialization::Reused(cached))
        );
        assert_eq!(vector_cache_graph_counts(&store), warm_counts);
    }

    #[test]
    fn ts2345_materializes_checked_inferred_and_explicit_vectors_not_recovery_vectors() {
        let mut store = initialized_store();
        let (string, number) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (bootstrap.string_type, bootstrap.number_type)
        };

        let (choose, choose_parameters) = vector_callable(
            &mut store,
            &["T"],
            &[None],
            &[None],
            &[0, 0],
            |_, parameters| parameters[0],
        );
        let inferred_number = fresh_number(&mut store, 1.0);
        let inferred_string = fresh_string(&mut store, "mixed");
        let inferred = project_vector(
            &mut store,
            &choose,
            vector_request(choose.owner, None, &[inferred_number, inferred_string]),
        )
        .unwrap();
        assert!(matches!(
            inferred.applicability,
            GenericCallVectorApplicability::ArgumentNotAssignable { .. }
        ));
        let inferred_checked = inferred.checked_instantiation.as_ref().unwrap();
        let GenericCallVectorMaterialization::Reused(inferred_cached) =
            materialize_vector(&mut store, &choose, &inferred).unwrap()
        else {
            panic!("an inferred TS2345 candidate is cached before applicability");
        };
        assert_eq!(
            store.type_mapper_has_exact_endpoints(
                inferred_cached.mapper,
                &choose_parameters,
                &inferred_checked.type_arguments,
            ),
            Some(true)
        );
        assert_eq!(
            store
                .signature(inferred_cached.signature)
                .unwrap()
                .resolved_return_type(),
            None,
            "TS2345 must leave the retained checked return unresolved",
        );
        let inferred_recovery_return = demand_vector_return(
            &mut store,
            &choose,
            &inferred,
            &inferred.projection.instantiation,
        );
        assert_eq!(
            store
                .signature(inferred.projection.instantiation.signature)
                .unwrap()
                .resolved_return_type(),
            Some(inferred_recovery_return),
        );
        assert_eq!(
            store
                .signature(inferred_cached.signature)
                .unwrap()
                .resolved_return_type(),
            None,
        );

        let (two, type_parameters) = vector_callable(
            &mut store,
            &["T", "U"],
            &[None, None],
            &[None, Some(GenericTypeSpec::Parameter(0))],
            &[0, 1],
            |_, parameters| parameters[1],
        );
        let explicit = project_vector(
            &mut store,
            &two,
            vector_request(two.owner, Some(&[string]), &[string, number]),
        )
        .unwrap();
        let explicit_checked = explicit.checked_instantiation.as_ref().unwrap();
        assert_eq!(explicit_checked.type_arguments, [string, string]);
        assert_eq!(
            demand_vector_return(
                &mut store,
                &two,
                &explicit,
                &explicit.projection.instantiation,
            ),
            type_parameters[0],
        );
        let GenericCallVectorMaterialization::Reused(explicit_cached) =
            materialize_vector(&mut store, &two, &explicit).unwrap()
        else {
            panic!("an explicit TS2345 candidate is cached before applicability");
        };
        assert_eq!(
            store.type_mapper_has_exact_endpoints(
                explicit_cached.mapper,
                &type_parameters,
                &[string, string],
            ),
            Some(true),
            "raw default recovery must not leak into the global mapper"
        );
        let explicit_signature = store.signature(explicit_cached.signature).unwrap();
        assert_eq!(explicit_signature.resolved_return_type(), None);
        for parameter in explicit_signature.parameters() {
            assert_eq!(
                store
                    .value_symbol_links(*parameter)
                    .and_then(|links| links.resolved_type),
                Some(string)
            );
        }
    }

    #[test]
    fn ts2345_stops_at_first_mismatch_and_a_later_warm_call_fills_only_the_suffix() {
        let mut store = initialized_store();
        let (string, number) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (bootstrap.string_type, bootstrap.number_type)
        };
        let (callable, _) = vector_callable(
            &mut store,
            &["T", "U", "V"],
            &[None, None, None],
            &[None, None, None],
            &[0, 1, 2],
            |_, parameters| parameters[2],
        );
        let failed = project_vector(
            &mut store,
            &callable,
            vector_request(
                callable.owner,
                Some(&[string, string, string]),
                &[number, string, string],
            ),
        )
        .unwrap();
        assert!(matches!(
            failed.applicability,
            GenericCallVectorApplicability::ArgumentNotAssignable { index: 0, .. },
        ));
        let checked = failed.checked_instantiation.as_ref().unwrap();
        let checked_parameters = store
            .signature(checked.signature)
            .unwrap()
            .parameters()
            .to_vec();
        assert_eq!(
            checked_parameters
                .iter()
                .map(|parameter| {
                    store
                        .value_symbol_links(*parameter)
                        .and_then(|links| links.resolved_type)
                })
                .collect::<Vec<_>>(),
            [Some(string), None, None],
        );
        assert_eq!(
            store
                .signature(checked.signature)
                .unwrap()
                .resolved_return_type(),
            None,
        );
        assert_eq!(
            demand_vector_return(
                &mut store,
                &callable,
                &failed,
                &failed.projection.instantiation,
            ),
            string,
        );
        assert_eq!(
            store
                .signature(checked.signature)
                .unwrap()
                .resolved_return_type(),
            None,
        );

        let before_warm = vector_cache_graph_counts(&store);
        let applicable = project_vector(
            &mut store,
            &callable,
            vector_request(
                callable.owner,
                Some(&[string, string, string]),
                &[string, string, string],
            ),
        )
        .unwrap();
        assert_eq!(
            applicable.applicability,
            GenericCallVectorApplicability::Applicable,
        );
        assert_eq!(
            applicable.projection.instantiation.signature,
            checked.signature,
        );
        assert_eq!(
            checked_parameters
                .iter()
                .map(|parameter| {
                    store
                        .value_symbol_links(*parameter)
                        .and_then(|links| links.resolved_type)
                })
                .collect::<Vec<_>>(),
            [Some(string), Some(string), Some(string)],
        );
        assert_eq!(
            store
                .signature(checked.signature)
                .unwrap()
                .resolved_return_type(),
            None,
        );
        assert_eq!(vector_cache_graph_counts(&store), before_warm);
    }

    #[test]
    fn recovery_only_vector_diagnostics_are_explicitly_unmaterialized_without_writes() {
        let mut store = initialized_store();
        let (string, number) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (bootstrap.string_type, bootstrap.number_type)
        };
        let (pair, _) = vector_callable(
            &mut store,
            &["T", "U"],
            &[None, None],
            &[None, None],
            &[0, 1],
            |_, parameters| parameters[1],
        );

        let type_arity = project_vector(
            &mut store,
            &pair,
            vector_request(pair.owner, Some(&[string]), &[string, number]),
        )
        .unwrap();
        assert_eq!(type_arity.applicability.diagnostic_code(), Some(2558));
        let before = vector_cache_graph_counts(&store);
        assert_eq!(
            materialize_vector(&mut store, &pair, &type_arity),
            Ok(GenericCallVectorMaterialization::Unmaterialized {
                applicability: type_arity.applicability,
            })
        );
        assert_eq!(vector_cache_graph_counts(&store), before);

        let value_arity = project_vector(
            &mut store,
            &pair,
            vector_request(pair.owner, None, &[string]),
        )
        .unwrap();
        assert_eq!(value_arity.applicability.diagnostic_code(), Some(2554));
        let before = vector_cache_graph_counts(&store);
        assert_eq!(
            materialize_vector(&mut store, &pair, &value_arity),
            Ok(GenericCallVectorMaterialization::Unmaterialized {
                applicability: value_arity.applicability,
            })
        );
        assert_eq!(vector_cache_graph_counts(&store), before);

        let (constrained, _) = vector_callable(
            &mut store,
            &["T"],
            &[Some(GenericTypeSpec::Exact(string))],
            &[None],
            &[0],
            |_, parameters| parameters[0],
        );
        let constraint = project_vector(
            &mut store,
            &constrained,
            vector_request(constrained.owner, Some(&[number]), &[number]),
        )
        .unwrap();
        assert_eq!(constraint.applicability.diagnostic_code(), Some(2344));
        let before = vector_cache_graph_counts(&store);
        assert_eq!(
            materialize_vector(&mut store, &constrained, &constraint),
            Ok(GenericCallVectorMaterialization::Unmaterialized {
                applicability: constraint.applicability,
            })
        );
        assert_eq!(vector_cache_graph_counts(&store), before);
    }

    #[test]
    fn vector_cache_failures_are_atomic_and_warm_validation_is_retryable() {
        let mut store = initialized_store();
        let (string, number) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (bootstrap.string_type, bootstrap.number_type)
        };
        let (pair, type_parameters) = vector_callable(
            &mut store,
            &["T", "U"],
            &[None, None],
            &[None, None],
            &[0, 1],
            |_, parameters| parameters[1],
        );
        let resolution = project_vector(
            &mut store,
            &pair,
            vector_request(pair.owner, Some(&[string, number]), &[string, number]),
        )
        .unwrap();
        let before = vector_cache_graph_counts(&store);

        let shape = validate_generic_call_signature_shape(&store, pair.owner, &pair, None).unwrap();
        let checked = resolution.checked_instantiation.as_ref().unwrap();
        assert_eq!(
            cached_generic_call_vector_instantiation_from_lookup(
                &store,
                &shape,
                &type_parameters,
                &checked.type_arguments,
                CachedSignatureLookup::HashCollision(pair.signature),
            ),
            Err(GenericCallVectorError::Invariant(
                GenericCallVectorInvariant::InstantiationCacheHashCollision {
                    target: pair.signature,
                    cached: pair.signature,
                }
            ))
        );
        assert_eq!(vector_cache_graph_counts(&store), before);

        let GenericCallVectorMaterialization::Reused(cached) =
            materialize_vector(&mut store, &pair, &resolution).unwrap()
        else {
            panic!("resolution must already have published exactly once");
        };
        let wrong_mapper = store
            .new_type_mapper(type_parameters, vec![number, string])
            .unwrap();
        assert!(store.set_signature_target_and_mapper(
            cached.signature,
            Some(pair.signature),
            Some(wrong_mapper),
        ));
        let poisoned_counts = vector_cache_graph_counts(&store);
        assert_eq!(
            materialize_vector(&mut store, &pair, &resolution),
            Err(GenericCallVectorError::Invariant(
                GenericCallVectorInvariant::InvalidCachedInstantiation {
                    target: pair.signature,
                    signature: cached.signature,
                }
            ))
        );
        assert_eq!(vector_cache_graph_counts(&store), poisoned_counts);

        assert!(store.set_signature_target_and_mapper(
            cached.signature,
            Some(pair.signature),
            Some(cached.mapper),
        ));
        assert_eq!(
            materialize_vector(&mut store, &pair, &resolution),
            Ok(GenericCallVectorMaterialization::Reused(cached))
        );
        let parameter = store.signature(cached.signature).unwrap().parameters()[0];
        let target = store
            .value_symbol_links(parameter)
            .and_then(|links| links.target)
            .unwrap();
        assert!(store.set_value_symbol_links(
            parameter,
            ValueSymbolLinks {
                resolved_type: Some(number),
                target: Some(target),
                mapper: Some(cached.mapper),
                ..ValueSymbolLinks::default()
            },
        ));
        let poisoned_counts = vector_cache_graph_counts(&store);
        assert_eq!(
            materialize_vector(&mut store, &pair, &resolution),
            Err(GenericCallVectorError::Invariant(
                GenericCallVectorInvariant::InvalidCachedInstantiation {
                    target: pair.signature,
                    signature: cached.signature,
                }
            ))
        );
        assert_eq!(vector_cache_graph_counts(&store), poisoned_counts);
    }

    #[test]
    fn poisoned_cold_suffix_is_rejected_before_any_missing_slot_is_filled() {
        let mut store = initialized_store();
        let (string, number) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (bootstrap.string_type, bootstrap.number_type)
        };
        let (pair, type_parameters) = vector_callable(
            &mut store,
            &["T", "U"],
            &[None, None],
            &[None, None],
            &[0, 1],
            |_, parameters| parameters[1],
        );
        let resolution = project_vector(
            &mut store,
            &pair,
            vector_request(pair.owner, Some(&[string, string]), &[number, string]),
        )
        .unwrap();
        assert!(matches!(
            resolution.applicability,
            GenericCallVectorApplicability::ArgumentNotAssignable { index: 0, .. },
        ));
        let checked = resolution.checked_instantiation.as_ref().unwrap();
        let parameters = store
            .signature(checked.signature)
            .unwrap()
            .parameters()
            .to_vec();
        assert_eq!(
            store
                .value_symbol_links(parameters[1])
                .and_then(|links| links.resolved_type),
            None,
        );
        let mut poisoned = store.value_symbol_links(parameters[1]).unwrap().clone();
        poisoned.function_or_constructor_checked = true;
        assert!(store.set_value_symbol_links(parameters[1], poisoned.clone()));
        let before = vector_cache_graph_counts(&store);
        let shape = validate_generic_call_signature_shape(&store, pair.owner, &pair, None).unwrap();
        let mut session = InstantiationSession::new(InstantiationLimits::default());

        assert_eq!(
            demand_generic_call_vector_parameter(
                &mut store,
                &shape,
                &type_parameters,
                &checked.type_arguments,
                checked.signature,
                1,
                &mut session,
            ),
            Err(GenericCallVectorError::Invariant(
                GenericCallVectorInvariant::InvalidCachedInstantiation {
                    target: pair.signature,
                    signature: checked.signature,
                },
            )),
        );
        assert_eq!(
            store.value_symbol_links(parameters[1]),
            Some(&poisoned),
            "warm validation must not repair or partially fill a poisoned suffix",
        );
        assert_eq!(
            store
                .signature(checked.signature)
                .unwrap()
                .resolved_return_type(),
            None,
        );
        assert_eq!(vector_cache_graph_counts(&store), before);
    }

    #[test]
    fn recovering_deep_parameter_revalidates_then_warms_without_new_work() {
        let mut store = initialized_store();
        let targets = canonical_array_targets(&mut store);
        let (callable, _) = structured_vector_callable(
            &mut store,
            |store, type_parameter| canonical_array_type(store, targets, type_parameter, false),
            |_, type_parameter| type_parameter,
        );
        let (number, error_type) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (bootstrap.number_type, bootstrap.error_type)
        };
        let mut session = InstantiationSession::new_recovering(
            &store,
            InstantiationLimits {
                max_depth: 100,
                max_count: 1,
            },
            error_type,
        )
        .unwrap();
        let mark = session.limit_event_mark();
        let resolution = project_validated_generic_call_vector_with_session(
            &mut store,
            vector_request(callable.owner, Some(&[number]), &[number]),
            &callable,
            Some(targets),
            None,
            &mut session,
            |_, _, _| Ok(true),
            CanonicalTypeMapperStore::is_type_strict_subtype_of,
            CanonicalTypeMapperStore::is_type_subtype_of,
        )
        .unwrap();
        assert_eq!(
            resolution.applicability,
            GenericCallVectorApplicability::Applicable,
        );
        let checked = resolution.checked_instantiation.as_ref().unwrap();
        let recovered_parameter =
            demand_vector_parameter(&mut store, &callable, &resolution, checked, 0);
        let recovered = store
            .canonical_array_reference_with_targets(targets, recovered_parameter)
            .unwrap()
            .expect("the recovery boundary retains the outer Array wrapper");
        assert_eq!(recovered.element_type, error_type);
        assert!(session.limit_event_occurred_since(mark));

        let shape =
            validate_generic_call_signature_shape(&store, callable.owner, &callable, Some(targets))
                .unwrap();
        let sources = shape
            .type_parameters
            .iter()
            .map(|parameter| parameter.type_)
            .collect::<Vec<_>>();
        assert_eq!(
            validate_generic_call_vector_resolution(&store, &resolution, &shape),
            Ok(sources.clone()),
        );
        assert_eq!(
            demand_generic_call_vector_return(
                &mut store,
                &shape,
                &sources,
                &checked.type_arguments,
                checked.signature,
                &mut session,
            ),
            Ok(error_type),
        );

        let warm_counts = vector_cache_graph_counts(&store);
        let warm_mark = session.limit_event_mark();
        let replay = project_validated_generic_call_vector_with_session(
            &mut store,
            vector_request(callable.owner, Some(&[number]), &[number]),
            &callable,
            Some(targets),
            None,
            &mut session,
            |_, _, _| Ok(true),
            CanonicalTypeMapperStore::is_type_strict_subtype_of,
            CanonicalTypeMapperStore::is_type_subtype_of,
        )
        .unwrap();
        assert_eq!(replay, resolution);
        assert_eq!(
            demand_generic_call_vector_return(
                &mut store,
                &shape,
                &sources,
                &checked.type_arguments,
                checked.signature,
                &mut session,
            ),
            Ok(error_type),
        );
        assert!(!session.limit_event_occurred_since(warm_mark));
        assert_eq!(vector_cache_graph_counts(&store), warm_counts);
    }

    #[test]
    fn forged_checked_union_vector_is_rejected_read_only_before_cache_lookup() {
        let mut store = initialized_store();
        let (string, number) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (bootstrap.string_type, bootstrap.number_type)
        };
        let (both, _) = vector_callable(
            &mut store,
            &["T", "U"],
            &[None, None],
            &[None, None],
            &[0, 1],
            |store, parameters| {
                store
                    .alloc_union_type(ObjectFlags::NONE, parameters.to_vec())
                    .unwrap()
            },
        );
        let resolution = project_vector(
            &mut store,
            &both,
            vector_request(both.owner, Some(&[string, number]), &[string, number]),
        )
        .unwrap();
        let forged_argument = fresh_string(&mut store, "forged");
        let mut forged = resolution.clone();
        let forged_checked = forged.checked_instantiation.as_mut().unwrap();
        forged_checked.type_arguments[0] = forged_argument;
        let before = vector_cache_graph_counts(&store);

        assert_eq!(
            materialize_vector(&mut store, &both, &forged),
            Err(GenericCallVectorError::Invariant(
                GenericCallVectorInvariant::InvalidCachedInstantiation {
                    target: both.signature,
                    signature: resolution.checked_instantiation.as_ref().unwrap().signature,
                }
            ))
        );
        assert_eq!(
            vector_cache_graph_counts(&store),
            before,
            "read-only vector validation must reject malformed internal state without interning its union"
        );
    }

    #[test]
    fn stale_ts2345_checked_return_source_is_rejected_read_only() {
        let mut store = initialized_store();
        let (string, number) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (bootstrap.string_type, bootstrap.number_type)
        };
        let (pair, type_parameters) = vector_callable(
            &mut store,
            &["T", "U"],
            &[None, None],
            &[None, None],
            &[0, 1],
            |_, parameters| parameters[1],
        );
        let resolution = project_vector(
            &mut store,
            &pair,
            vector_request(pair.owner, Some(&[string, number]), &[string, string]),
        )
        .unwrap();
        assert!(matches!(
            resolution.applicability,
            GenericCallVectorApplicability::ArgumentNotAssignable { .. }
        ));

        assert!(
            store.set_signature_resolved_return_type(pair.signature, Some(type_parameters[0]),)
        );
        let mut changed_pair = pair.clone();
        changed_pair.return_type = Some(type_parameters[0]);
        let before = vector_cache_graph_counts(&store);
        assert_eq!(
            materialize_vector(&mut store, &changed_pair, &resolution),
            Err(GenericCallVectorError::Invariant(
                GenericCallVectorInvariant::InvalidCheckedInstantiation(pair.signature)
            ))
        );
        assert_eq!(vector_cache_graph_counts(&store), before);
    }

    #[test]
    fn source_materializer_shares_partial_and_full_applicable_checked_cache() {
        let mut store = initialized_store();
        let string = store.intrinsic_bootstrap().unwrap().string_type;
        let (callable, _) = vector_callable(
            &mut store,
            &["T", "U"],
            &[None, None],
            &[None, Some(GenericTypeSpec::Parameter(0))],
            &[0, 1],
            |_, parameters| parameters[1],
        );
        let partial = project_vector(
            &mut store,
            &callable,
            vector_request(callable.owner, Some(&[string]), &[string, string]),
        )
        .unwrap();
        let before = vector_cache_graph_counts(&store);
        let first = materialize_source_vector(&mut store, &callable, &partial, None).unwrap();
        let checked = first.checked_instantiation.unwrap();
        assert_eq!(first.call_signature, checked.signature);
        assert_eq!(first.call_mapper, checked.mapper);
        assert_eq!(vector_cache_graph_counts(&store), before);
        assert_eq!(
            store.cached_signatures_contain(first.call_signature),
            Some(true),
        );

        let full = project_vector(
            &mut store,
            &callable,
            vector_request(callable.owner, Some(&[string, string]), &[string, string]),
        )
        .unwrap();
        assert_eq!(
            partial.checked_instantiation, full.checked_instantiation,
            "partial and full explicit syntax must key the same checked vector",
        );
        let shared_counts = vector_cache_graph_counts(&store);
        assert_eq!(
            materialize_source_vector(&mut store, &callable, &full, None),
            Ok(first),
        );
        assert_eq!(vector_cache_graph_counts(&store), shared_counts);
        assert_eq!(
            materialize_source_vector(&mut store, &callable, &partial, Some(first.call_signature),),
            Ok(first),
        );
        assert_eq!(vector_cache_graph_counts(&store), shared_counts);

        assert_eq!(
            materialize_source_vector(&mut store, &callable, &partial, Some(callable.signature),),
            Err(GenericCallVectorError::Invariant(
                GenericCallVectorInvariant::InvalidCallInstantiation {
                    target: callable.signature,
                    signature: callable.signature,
                },
            )),
        );
        assert_eq!(vector_cache_graph_counts(&store), shared_counts);

        assert!(store.set_signature_target_and_mapper(
            checked.signature,
            Some(callable.signature),
            None,
        ));
        let poisoned_counts = vector_cache_graph_counts(&store);
        assert_eq!(
            materialize_source_vector(&mut store, &callable, &partial, None),
            Err(GenericCallVectorError::Invariant(
                GenericCallVectorInvariant::InvalidCachedInstantiation {
                    target: callable.signature,
                    signature: checked.signature,
                },
            )),
        );
        assert_eq!(vector_cache_graph_counts(&store), poisoned_counts);
    }

    #[test]
    fn source_ts2345_uses_prepublished_checked_and_raw_default_recovery_shells() {
        let mut store = initialized_store();
        let (string, number) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (bootstrap.string_type, bootstrap.number_type)
        };
        let (callable, type_parameters) = vector_callable(
            &mut store,
            &["T", "U"],
            &[None, None],
            &[None, Some(GenericTypeSpec::Parameter(0))],
            &[0, 1],
            |_, parameters| parameters[1],
        );
        let resolution = project_vector(
            &mut store,
            &callable,
            vector_request(callable.owner, Some(&[string]), &[string, number]),
        )
        .unwrap();
        assert!(matches!(
            resolution.applicability,
            GenericCallVectorApplicability::ArgumentNotAssignable { index: 1, .. },
        ));
        let checked_vector = resolution.checked_instantiation.as_ref().unwrap();
        assert_eq!(checked_vector.type_arguments, [string, string]);
        assert_eq!(
            resolution.projection.instantiation.type_arguments,
            [string, type_parameters[0]],
        );
        let before = vector_cache_graph_counts(&store);

        let first = materialize_source_vector(&mut store, &callable, &resolution, None).unwrap();
        let checked = first.checked_instantiation.unwrap();
        assert_ne!(first.call_signature, checked.signature);
        assert_ne!(first.call_mapper, checked.mapper);
        assert_eq!(vector_cache_graph_counts(&store), before);
        assert_eq!(
            store.cached_signatures_contain(checked.signature),
            Some(true),
        );
        assert_eq!(
            store.cached_signatures_contain(first.call_signature),
            Some(false),
        );
        assert_eq!(
            store.type_mapper_has_exact_endpoints(
                checked.mapper,
                &type_parameters,
                &[string, string],
            ),
            Some(true),
        );
        assert_eq!(
            store.type_mapper_has_exact_endpoints(
                first.call_mapper,
                &type_parameters,
                &[string, type_parameters[0]],
            ),
            Some(true),
        );
        assert_eq!(
            store
                .signature(checked.signature)
                .unwrap()
                .resolved_return_type(),
            None,
        );
        let recovery = store.signature(first.call_signature).unwrap();
        assert_eq!(recovery.target(), Some(callable.signature));
        assert_eq!(recovery.mapper(), Some(first.call_mapper));
        assert_eq!(recovery.resolved_return_type(), None);
        for parameter in recovery.parameters() {
            assert_eq!(
                store
                    .value_symbol_links(*parameter)
                    .and_then(|links| links.resolved_type),
                None,
                "the recovery parameter row remains cold",
            );
        }
        assert_eq!(
            demand_vector_return(
                &mut store,
                &callable,
                &resolution,
                &resolution.projection.instantiation,
            ),
            type_parameters[0],
            "overload-failure default U=T remains the raw T in the recovery mapper",
        );
        assert_eq!(
            store
                .signature(checked.signature)
                .unwrap()
                .resolved_return_type(),
            None,
            "selected recovery finalization must not fill the checked return",
        );
        let after_first = vector_cache_graph_counts(&store);
        let second = materialize_source_vector(&mut store, &callable, &resolution, None).unwrap();
        assert_eq!(second.checked_instantiation, Some(checked));
        assert_eq!(second, first);
        assert_eq!(vector_cache_graph_counts(&store), after_first);
        let warm_counts = after_first;
        assert_eq!(
            materialize_source_vector(
                &mut store,
                &callable,
                &resolution,
                Some(second.call_signature),
            ),
            Ok(second),
        );
        assert_eq!(vector_cache_graph_counts(&store), warm_counts);
        assert_eq!(
            materialize_source_vector(&mut store, &callable, &resolution, Some(checked.signature),),
            Err(GenericCallVectorError::Invariant(
                GenericCallVectorInvariant::InvalidCallInstantiation {
                    target: callable.signature,
                    signature: checked.signature,
                },
            )),
        );
        assert_eq!(vector_cache_graph_counts(&store), warm_counts);

        assert!(store.set_signature_target_and_mapper(
            first.call_signature,
            Some(callable.signature),
            Some(checked.mapper),
        ));
        let poisoned_counts = vector_cache_graph_counts(&store);
        assert_eq!(
            materialize_source_vector(
                &mut store,
                &callable,
                &resolution,
                Some(first.call_signature),
            ),
            Err(GenericCallVectorError::Invariant(
                GenericCallVectorInvariant::InvalidCachedInstantiation {
                    target: callable.signature,
                    signature: first.call_signature,
                },
            )),
        );
        assert_eq!(vector_cache_graph_counts(&store), poisoned_counts);
    }

    #[test]
    fn source_recovery_only_diagnostics_are_uncached_distinct_and_warm_stable() {
        let mut store = initialized_store();
        let (string, number) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (bootstrap.string_type, bootstrap.number_type)
        };
        let (pair, _) = vector_callable(
            &mut store,
            &["T", "U"],
            &[None, None],
            &[None, None],
            &[0, 1],
            |_, parameters| parameters[1],
        );

        let type_arity = project_vector(
            &mut store,
            &pair,
            vector_request(pair.owner, Some(&[string]), &[string, number]),
        )
        .unwrap();
        assert!(matches!(
            type_arity.applicability,
            GenericCallVectorApplicability::TypeArgumentArity {
                minimum: 2,
                maximum: 2,
                actual: 1,
            },
        ));
        assert_recovery_only_source_lifecycle(&mut store, &pair, &type_arity);

        let too_few = project_vector(
            &mut store,
            &pair,
            vector_request(pair.owner, None, &[string]),
        )
        .unwrap();
        assert_eq!(
            too_few.applicability,
            GenericCallVectorApplicability::TooFewArguments {
                expected: 2,
                actual: 1,
            },
        );
        assert_recovery_only_source_lifecycle(&mut store, &pair, &too_few);

        let too_many = project_vector(
            &mut store,
            &pair,
            vector_request(pair.owner, None, &[string, number, number]),
        )
        .unwrap();
        assert_eq!(
            too_many.applicability,
            GenericCallVectorApplicability::TooManyArguments {
                expected: 2,
                actual: 3,
            },
        );
        assert_recovery_only_source_lifecycle(&mut store, &pair, &too_many);

        let (constrained, _) = vector_callable(
            &mut store,
            &["T"],
            &[Some(GenericTypeSpec::Exact(string))],
            &[None],
            &[0],
            |_, parameters| parameters[0],
        );
        let constraint = project_vector(
            &mut store,
            &constrained,
            vector_request(constrained.owner, Some(&[number]), &[number]),
        )
        .unwrap();
        assert!(matches!(
            constraint.applicability,
            GenericCallVectorApplicability::ExplicitTypeArgumentConstraint {
                index: 0,
                type_argument,
                constraint,
            } if type_argument == number && constraint == string,
        ));
        assert!(
            constraint.checked_instantiation.is_none(),
            "TS2344 must not create a checked shell",
        );
        let constraint_call =
            assert_recovery_only_source_lifecycle(&mut store, &constrained, &constraint);
        assert_eq!(constraint_call.checked_instantiation, None);

        let exact_type_arguments = constraint
            .projection
            .instantiation
            .type_arguments
            .clone()
            .into_boxed_slice();
        assert!(store.set_cached_signature(
            constrained.signature,
            type_list_key(&exact_type_arguments),
            exact_type_arguments,
            constraint_call.call_signature,
        ));
        let poisoned_counts = vector_cache_graph_counts(&store);
        assert_eq!(
            materialize_source_vector(
                &mut store,
                &constrained,
                &constraint,
                Some(constraint_call.call_signature),
            ),
            Err(GenericCallVectorError::Invariant(
                GenericCallVectorInvariant::InvalidCheckedInstantiation(constrained.signature),
            )),
        );
        assert_eq!(vector_cache_graph_counts(&store), poisoned_counts);
    }

    #[test]
    fn source_recovery_rejects_stale_raw_return_without_writes() {
        let mut store = initialized_store();
        let string = store.intrinsic_bootstrap().unwrap().string_type;
        let (callable, type_parameters) = vector_callable(
            &mut store,
            &["T", "U"],
            &[None, None],
            &[None, None],
            &[0, 1],
            |_, parameters| parameters[1],
        );
        let resolution = project_vector(
            &mut store,
            &callable,
            vector_request(callable.owner, None, &[string]),
        )
        .unwrap();
        assert!(matches!(
            resolution.applicability,
            GenericCallVectorApplicability::TooFewArguments { .. },
        ));
        assert!(
            store.set_signature_resolved_return_type(callable.signature, Some(type_parameters[0]),)
        );
        let mut changed = callable.clone();
        changed.return_type = Some(type_parameters[0]);
        let before = vector_cache_graph_counts(&store);
        assert_eq!(
            materialize_source_vector(&mut store, &changed, &resolution, None),
            Err(GenericCallVectorError::Invariant(
                GenericCallVectorInvariant::InvalidCheckedInstantiation(callable.signature),
            )),
        );
        assert_eq!(vector_cache_graph_counts(&store), before);
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
    fn source_declared_inference_proof_never_waives_a_foreign_candidate() {
        let mut store = initialized_store();
        let proven = store
            .alloc_plain_object_type(ObjectFlags::ANONYMOUS, None)
            .unwrap();
        let foreign = store
            .alloc_plain_object_type(ObjectFlags::ANONYMOUS, None)
            .unwrap();
        let proof = SourceDeclaredInferenceProof { candidate: proven };

        assert_eq!(
            validate_inference_leaf(&store, foreign),
            Err(NakedTypeInferenceError::UnsupportedCandidate(foreign))
        );
        assert_eq!(
            validate_inference_leaf_with_source_proof(&store, foreign, Some(proof)),
            Err(NakedTypeInferenceError::UnsupportedCandidate(foreign))
        );
        assert_eq!(
            validate_inference_leaf_with_source_proof(&store, proven, Some(proof)),
            Ok(())
        );
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
    fn identity_recovery_at_count_limit_revalidates_return_and_warm_shell() {
        let mut store = initialized_store();
        let (callable, _) = identity_callable(&mut store);
        let (string, error_type) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (bootstrap.string_type, bootstrap.error_type)
        };
        let mut session = InstantiationSession::new_recovering(
            &store,
            InstantiationLimits {
                max_depth: 100,
                max_count: 0,
            },
            error_type,
        )
        .unwrap();
        let mark = session.limit_event_mark();
        let resolution = resolve_validated_identity_call(
            &mut store,
            inferred_request(callable.owner, &[string]),
            &callable,
            EXACT_SOURCE,
            None,
            &mut session,
            |_, _, _| Ok(true),
        )
        .unwrap();
        assert_eq!(
            resolution.applicability,
            DirectCallApplicability::Applicable,
        );
        let [parameter] = store
            .signature(resolution.projection.signature)
            .unwrap()
            .parameters()
        else {
            panic!("identity shell must retain one parameter")
        };
        assert_eq!(
            store
                .value_symbol_links(*parameter)
                .and_then(|links| links.resolved_type),
            Some(error_type),
        );
        assert_eq!(
            demand_validated_identity_generic_call_selected_return(
                &mut store,
                &resolution,
                &callable,
                EXACT_SOURCE,
                &mut session,
            ),
            Ok((error_type, DirectCallReturnKind::Value)),
        );
        assert!(session.limit_event_occurred_since(mark));

        let warm_counts = vector_cache_graph_counts(&store);
        let warm_mark = session.limit_event_mark();
        let replay = resolve_validated_identity_call(
            &mut store,
            inferred_request(callable.owner, &[string]),
            &callable,
            EXACT_SOURCE,
            None,
            &mut session,
            |_, _, _| Ok(true),
        )
        .unwrap();
        assert_eq!(replay, resolution);
        assert_eq!(
            demand_validated_identity_generic_call_selected_return(
                &mut store,
                &replay,
                &callable,
                EXACT_SOURCE,
                &mut session,
            ),
            Ok((error_type, DirectCallReturnKind::Value)),
        );
        assert!(!session.limit_event_occurred_since(warm_mark));
        assert_eq!(vector_cache_graph_counts(&store), warm_counts);
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
    fn relation_unavailable_retains_the_checked_shell_published_before_applicability() {
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

        let mut session = InstantiationSession::new(InstantiationLimits::default());
        assert_eq!(
            resolve_validated_identity_call(
                &mut store,
                inferred_request(callable.owner, &[string]),
                &callable,
                EXACT_SOURCE,
                None,
                &mut session,
                |_, _, _| Err(RelationUnavailable::MissingBootstrap),
            ),
            Err(IdentityGenericCallError::Relation(
                RelationUnavailable::MissingBootstrap
            ))
        );
        assert_eq!(store.mapper_len(), counts.0 + 1);
        assert_eq!(store.symbol_len(), counts.1 + 1);
        assert_eq!(store.signature_len(), counts.2 + 1);
        assert_eq!(store.cached_signature_len(), counts.3 + 1);
        assert_ne!(store.checker_link_allocated_lengths(), counts.4);
        let published = (
            store.mapper_len(),
            store.symbol_len(),
            store.signature_len(),
            store.cached_signature_len(),
            store.checker_link_allocated_lengths(),
        );

        let repaired = project_validated_identity_call(
            &mut store,
            inferred_request(callable.owner, &[string]),
            &callable,
            EXACT_SOURCE,
        )
        .unwrap();
        assert_eq!(repaired.projection.type_argument, string);
        assert_eq!(
            (
                store.mapper_len(),
                store.symbol_len(),
                store.signature_len(),
                store.cached_signature_len(),
                store.checker_link_allocated_lengths(),
            ),
            published,
        );
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
