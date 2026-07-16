//! Exact semantic kernels for bounded generic direct-call verticals.
//!
//! The full-vector branch admits one stored signature with ordered type
//! parameters, fixed required parameters whose targets are naked type
//! parameters, and a mapper-supported return. It owns declaration-order
//! inference/default/constraint finalization and overload-failure projection,
//! but deliberately leaves instantiated-signature cache publication to its
//! eventual source consumer. The original exact `<T>(value: T): T` entry points
//! remain available for compatibility with the installed identity-call source
//! path and its one-row cache protocol.

#![allow(dead_code)] // Installed ahead of the source-call dispatch consumer.

use ts_ast::SyntaxKind;
use ts_binder::{CheckFlags, SymbolData, SymbolFlags};

use super::{
    CanonicalGlobalTypes, CanonicalTypeMapperStore, DeclaredTypeHost, RelationUnavailable,
    SemanticSymbolId, SignatureId, TypeId, TypeMapperId, ValueSymbolLinks,
    callables::{
        StoredSingleCallableValidation, ValidatedSingleCallable, validate_stored_single_callable,
    },
    calls::{
        DirectCallApplicability, DirectCallArgumentTarget, DirectCallForm, DirectCallReturnKind,
    },
    declared::{cached_ordinary_type_parameter_owner, type_list_key},
    inference::{
        InferenceLiteralTreatment, NakedTypeCandidateError, NakedTypeInferenceError,
        infer_naked_type_parameter, infer_naked_type_parameter_candidates, validate_inference_leaf,
    },
    instantiate::{InstantiationError, instantiate_type_with_vector},
    signatures::SignatureFlags,
    source_callables::{StoredSourceCallableValidation, validate_stored_source_callable},
    store::CachedSignatureLookup,
    type_records::TypeData,
    types::{ObjectFlags, TypeFlags},
};

/// Syntax-neutral input for the declaration-order generic-call kernel.
///
/// `Some` preserves the distinction between explicit syntax and inference.
/// An empty explicit list is normalized back to inference because the parser
/// owns TS1099 while pinned overload resolution observes zero type arguments.
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
    MissingBootstrap,
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

/// One mapper-equivalent projection with no mapper/signature cache published.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct GenericCallVectorInstantiation {
    pub(super) type_arguments: Vec<TypeId>,
    pub(super) parameter_types: Vec<TypeId>,
    pub(super) return_type: TypeId,
    pub(super) return_kind: DirectCallReturnKind,
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

/// Complete pure-resolution result.
///
/// `checked_instantiation` retains the normal inference/default vector used to
/// classify TS2344/TS2345. `projection` may instead contain the raw
/// overload-failure vector used for the call expression's final return type.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct GenericCallVectorResolution {
    pub(super) projection: GenericCallVectorProjection,
    pub(super) checked_instantiation: Option<GenericCallVectorInstantiation>,
    pub(super) applicability: GenericCallVectorApplicability,
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
    parameter_type_parameters: Vec<TypeId>,
    return_type: TypeId,
}

/// Resolves the bounded full-vector generic branch through the canonical
/// callable provider. It deliberately does not allocate a mapper, transient
/// parameter symbol, instantiated signature, or cached-signature entry. The
/// source provider must reject `const` type-parameter declarations before
/// publication because stored type-parameter records do not retain that bit.
pub(super) fn resolve_generic_call_vector(
    store: &mut CanonicalTypeMapperStore,
    global_types: &CanonicalGlobalTypes,
    strict_function_types: bool,
    request: GenericCallVectorRequest<'_>,
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
    project_validated_generic_call_vector(
        store,
        request,
        &callable,
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

fn project_validated_generic_call_vector(
    store: &mut CanonicalTypeMapperStore,
    request: GenericCallVectorRequest<'_>,
    callable: &ValidatedSingleCallable,
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
    let shape = validate_generic_call_signature_shape(store, request.callee, callable)?;
    let minimum_type_arguments = minimum_type_argument_count(&shape.type_parameters);
    if let Some(explicit) = request.explicit_type_arguments
        && (explicit.len() < minimum_type_arguments || explicit.len() > shape.type_parameters.len())
    {
        let recovery = explicit_recovery_type_arguments(store, &shape, explicit)?;
        let projection = generic_call_projection(store, request.callee, &shape, recovery, true)?;
        return Ok(GenericCallVectorResolution {
            projection,
            checked_instantiation: None,
            applicability: GenericCallVectorApplicability::TypeArgumentArity {
                minimum: minimum_type_arguments,
                maximum: shape.type_parameters.len(),
                actual: explicit.len(),
            },
        });
    }

    let expected_arguments = shape.parameter_type_parameters.len();
    if request.arguments.len() != expected_arguments {
        let recovery = failure_type_arguments(
            store,
            &shape,
            request,
            &mut is_assignable,
            &mut is_strict_subtype,
            &mut is_subtype,
        )?;
        let projection = generic_call_projection(store, request.callee, &shape, recovery, true)?;
        let applicability = if request.arguments.len() < expected_arguments {
            GenericCallVectorApplicability::TooFewArguments {
                expected: expected_arguments,
                actual: request.arguments.len(),
            }
        } else {
            GenericCallVectorApplicability::TooManyArguments {
                expected: expected_arguments,
                actual: request.arguments.len(),
            }
        };
        return Ok(GenericCallVectorResolution {
            projection,
            checked_instantiation: None,
            applicability,
        });
    }

    let selected_type_arguments = match request.explicit_type_arguments {
        Some(explicit) => explicit_checked_type_arguments(store, &shape, explicit)?,
        None => {
            infer_generic_call_type_arguments(
                store,
                &shape,
                request.arguments,
                &mut is_assignable,
                &mut is_strict_subtype,
                &mut is_subtype,
            )?
        }
    };
    let checked = instantiate_generic_call_shape(store, &shape, selected_type_arguments.clone())?;

    if let Some(explicit) = request.explicit_type_arguments
        && let Some(applicability) = check_explicit_type_argument_constraints(
            store,
            &shape,
            explicit,
            &selected_type_arguments,
            &mut is_assignable,
        )?
    {
        let recovery = explicit_recovery_type_arguments(store, &shape, explicit)?;
        let projection = generic_call_projection(store, request.callee, &shape, recovery, true)?;
        return Ok(GenericCallVectorResolution {
            projection,
            checked_instantiation: Some(checked),
            applicability,
        });
    }

    if let Some(applicability) = check_generic_call_arguments(
        store,
        request.arguments,
        &checked.parameter_types,
        &mut is_assignable,
    )? {
        let recovery = match request.explicit_type_arguments {
            Some(explicit) => explicit_recovery_type_arguments(store, &shape, explicit)?,
            None => selected_type_arguments,
        };
        let projection = generic_call_projection(store, request.callee, &shape, recovery, true)?;
        return Ok(GenericCallVectorResolution {
            projection,
            checked_instantiation: Some(checked),
            applicability,
        });
    }

    Ok(GenericCallVectorResolution {
        projection: GenericCallVectorProjection {
            callee: request.callee,
            generic_signature: shape.signature,
            type_parameters: shape
                .type_parameters
                .iter()
                .map(|parameter| parameter.type_)
                .collect(),
            instantiation: checked.clone(),
            recovery: false,
        },
        checked_instantiation: Some(checked),
        applicability: GenericCallVectorApplicability::Applicable,
    })
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
    if signature.flags() != SignatureFlags::NONE {
        return Err(GenericCallVectorUnsupported::SignatureFlags(callable.signature).into());
    }
    if signature.this_parameter().is_some() {
        return Err(GenericCallVectorUnsupported::ExplicitThisParameter(callable.signature).into());
    }
    if signature.has_rest_parameter() {
        return Err(GenericCallVectorUnsupported::RestSignature(callable.signature).into());
    }
    let parameter_count = signature.parameters().len();
    if signature.min_argument_count() != i32::try_from(parameter_count).unwrap_or(-1)
        || callable.min_argument_count != parameter_count
    {
        return Err(GenericCallVectorUnsupported::NonRequiredParameter(callable.signature).into());
    }
    if callable.parameters.len() != parameter_count
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
    let Some(return_type) = callable.return_type else {
        return Err(GenericCallVectorUnsupported::UnresolvedReturnType(callable.signature).into());
    };
    if signature.resolved_return_type() != Some(return_type) {
        return Err(
            GenericCallVectorInvariant::CallableSignatureMismatch(callable.signature).into(),
        );
    }

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
        let (constraint, default_type, base_constraint) =
            validate_generic_call_type_parameter(
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
    for (index, (symbol, projected)) in signature
        .parameters()
        .iter()
        .copied()
        .zip(callable.parameters.iter().copied())
        .enumerate()
    {
        if !type_parameter_ids.contains(&projected) {
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
    validate_generic_mapper_type(store, return_type, &type_parameter_ids, callable.signature)?;
    Ok(GenericCallSignatureShape {
        signature: callable.signature,
        type_parameters,
        parameter_type_parameters: callable.parameters.clone(),
        return_type,
    })
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
        TypeData::Union(union) if record.alias().is_none() && union.origin.is_none() => {
            for constituent in &union.union.types {
                let base = validate_generic_constraint_dependency(
                    store,
                    *constituent,
                    earlier,
                    owner,
                )?;
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
        TypeData::Union(union) if record.alias().is_none() && union.origin.is_none() => {
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

fn validate_generic_mapper_type(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
    type_parameters: &[TypeId],
    signature: SignatureId,
) -> Result<(), GenericCallVectorError> {
    let record = store
        .type_payload(type_)
        .ok_or(GenericCallVectorUnsupported::InstantiationType { signature, type_ })?;
    match record.data() {
        TypeData::Intrinsic(_) | TypeData::Literal(_) | TypeData::UniqueEsSymbol(_) => Ok(()),
        TypeData::TypeParameter(_) if type_parameters.contains(&type_) => Ok(()),
        TypeData::Union(union) if record.alias().is_none() && union.origin.is_none() => {
            for constituent in &union.union.types {
                validate_generic_mapper_type(store, *constituent, type_parameters, signature)?;
            }
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
        let instantiated =
            instantiate_type_with_vector(store, default_type, &sources[..index], &result[..index])?;
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
) -> Result<Vec<TypeId>, GenericCallVectorError> {
    let type_parameters = shape
        .type_parameters
        .iter()
        .map(|parameter| parameter.type_)
        .collect::<Vec<_>>();
    let mut buckets = vec![Vec::new(); type_parameters.len()];
    for (argument, parameter) in arguments
        .iter()
        .copied()
        .zip(shape.parameter_type_parameters.iter().copied())
    {
        let index = type_parameters
            .iter()
            .position(|type_parameter| *type_parameter == parameter)
            .expect("signature validation proved every parameter is a naked type parameter");
        validate_inference_leaf(store, argument)
            .map_err(|error| GenericCallVectorError::Inference(error.into()))?;
        if !buckets[index].contains(&argument) {
            buckets[index].push(argument);
        }
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
                instantiate_type_with_vector(
                    store,
                    constraint,
                    &type_parameters[..index],
                    &inferred[..index],
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
        let candidate = infer_naked_type_parameter_candidates(
            store,
            &buckets[index],
            treatment,
            |store, source, target| is_strict_subtype(store, source, target),
            |store, source, target| is_subtype(store, source, target),
        )?;
        let mut argument = match candidate {
            Some(candidate) => candidate,
            None => parameter
                .default_type
                .map(|default_type| {
                    instantiate_type_with_vector(
                        store,
                        default_type,
                        &type_parameters[..index],
                        &inferred[..index],
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
    }
    Ok(inferred)
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
        let constraint = instantiate_type_with_vector(store, constraint, &sources, checked)?;
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
    parameters: &[TypeId],
    is_assignable: &mut impl FnMut(
        &mut CanonicalTypeMapperStore,
        TypeId,
        TypeId,
    ) -> Result<bool, RelationUnavailable>,
) -> Result<Option<GenericCallVectorApplicability>, GenericCallVectorError> {
    for (index, (argument_type, parameter_type)) in arguments
        .iter()
        .copied()
        .zip(parameters.iter().copied())
        .enumerate()
    {
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

fn instantiate_generic_call_shape(
    store: &mut CanonicalTypeMapperStore,
    shape: &GenericCallSignatureShape,
    type_arguments: Vec<TypeId>,
) -> Result<GenericCallVectorInstantiation, GenericCallVectorError> {
    let sources = shape
        .type_parameters
        .iter()
        .map(|parameter| parameter.type_)
        .collect::<Vec<_>>();
    let mut parameter_types = Vec::with_capacity(shape.parameter_type_parameters.len());
    for parameter in &shape.parameter_type_parameters {
        parameter_types.push(instantiate_type_with_vector(
            store,
            *parameter,
            &sources,
            &type_arguments,
        )?);
    }
    let return_type =
        instantiate_type_with_vector(store, shape.return_type, &sources, &type_arguments)?;
    let return_kind = if store
        .type_payload(return_type)
        .is_some_and(|record| record.flags().intersects(TypeFlags::VOID))
    {
        DirectCallReturnKind::Void
    } else {
        DirectCallReturnKind::Value
    };
    Ok(GenericCallVectorInstantiation {
        type_arguments,
        parameter_types,
        return_type,
        return_kind,
    })
}

fn generic_call_projection(
    store: &mut CanonicalTypeMapperStore,
    callee: TypeId,
    shape: &GenericCallSignatureShape,
    type_arguments: Vec<TypeId>,
    recovery: bool,
) -> Result<GenericCallVectorProjection, GenericCallVectorError> {
    Ok(GenericCallVectorProjection {
        callee,
        generic_signature: shape.signature,
        type_parameters: shape
            .type_parameters
            .iter()
            .map(|parameter| parameter.type_)
            .collect(),
        instantiation: instantiate_generic_call_shape(store, shape, type_arguments)?,
        recovery,
    })
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
    resolve_validated_identity_call_with_proofs(
        store,
        request,
        &callable,
        cache_provenance,
        proofs,
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
    resolve_validated_identity_call(store, request, callable, cache_provenance, |_, _, _| {
        Ok(true)
    })
}

fn resolve_validated_identity_call(
    store: &mut CanonicalTypeMapperStore,
    request: IdentityGenericCallRequest<'_>,
    callable: &ValidatedSingleCallable,
    cache_provenance: IdentityTypeParameterCacheProvenance,
    is_assignable: impl FnMut(
        &mut CanonicalTypeMapperStore,
        TypeId,
        TypeId,
    ) -> Result<bool, RelationUnavailable>,
) -> Result<IdentityGenericCallResolution, IdentityGenericCallError> {
    resolve_validated_identity_call_with_proofs(
        store,
        request,
        callable,
        cache_provenance,
        SourceIdentityInferenceProofs::default(),
        is_assignable,
    )
}

fn resolve_validated_identity_call_with_proofs(
    store: &mut CanonicalTypeMapperStore,
    request: IdentityGenericCallRequest<'_>,
    callable: &ValidatedSingleCallable,
    cache_provenance: IdentityTypeParameterCacheProvenance,
    proofs: SourceIdentityInferenceProofs,
    mut is_assignable: impl FnMut(
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
        proofs,
    )?;
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
        assert_eq!(constraints.len(), names.len());
        assert_eq!(defaults.len(), names.len());
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
                i32::try_from(parameter_types.len()).unwrap(),
            )
            .unwrap();
        let owner = store.intrinsic_bootstrap().unwrap().any_function_type;
        (
            ValidatedSingleCallable {
                owner,
                signature,
                parameters: parameter_types,
                min_argument_count: parameter_indices.len(),
                return_type: Some(return_type),
                strict_variance_exempt: false,
            },
            type_parameters,
        )
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

    fn project_vector(
        store: &mut CanonicalTypeMapperStore,
        callable: &ValidatedSingleCallable,
        request: GenericCallVectorRequest<'_>,
    ) -> Result<GenericCallVectorResolution, GenericCallVectorError> {
        project_validated_generic_call_vector(
            store,
            request,
            callable,
            |store, source, target| Ok(scalar_assignable(store, source, target)),
            CanonicalTypeMapperStore::is_type_strict_subtype_of,
            CanonicalTypeMapperStore::is_type_subtype_of,
        )
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
            result.projection.instantiation.parameter_types,
            [string, one]
        );
        assert_eq!(result.projection.instantiation.return_type, one);
        assert!(!result.projection.recovery);
        assert_eq!(
            (
                store.mapper_len(),
                store.signature_len(),
                store.cached_signature_len(),
            ),
            counts,
            "pure vector projection must not publish mapper/signature cache state"
        );
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
        assert_eq!(result.projection.instantiation.return_type, inferred);
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
        assert_eq!(fallback_result.projection.instantiation.return_type, string);

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
        let TypeData::Union(data) = store
            .type_payload(both_result.projection.instantiation.return_type)
            .unwrap()
            .data()
        else {
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
        assert_eq!(result.projection.instantiation.return_type, string);
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
        let dependent_inference =
            dependent_result.projection.instantiation.type_arguments[1];
        let TypeData::Union(data) = store
            .type_payload(dependent_inference)
            .unwrap()
            .data()
        else {
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
        assert_eq!(result.projection.instantiation.return_type, number);
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
        assert_eq!(missing.projection.instantiation.return_type, unknown);

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
        assert_eq!(extra.projection.instantiation.return_type, number);

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
            "the parser owns TS1099 and zero type arguments trigger inference"
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
            result.projection.instantiation.return_type, parameters[0],
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

        assert_eq!(result.projection.instantiation.return_type, one);
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
