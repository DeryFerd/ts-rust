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
    SignatureId, TypeId, TypeMapperId, TypeMapperKind, ValueSymbolLinks,
    callables::{
        StoredSingleCallableValidation, ValidatedSingleCallable, validate_stored_single_callable,
    },
    calls::{
        DirectCallApplicability, DirectCallArgumentTarget, DirectCallForm, DirectCallReturnKind,
    },
    inference::{NakedTypeInferenceError, infer_naked_type_parameter, validate_inference_leaf},
    instantiate::{InstantiationError, instantiate_type},
    signatures::SignatureFlags,
    type_records::{ConstrainedTypeData, TypeData},
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
    Capacity(SignatureId),
    Publication(SignatureId),
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
    let mut resolution = project_validated_identity_call(store, request, &callable)?;
    resolution.applicability =
        check_identity_argument_applicability(&resolution.projection, |source, target| {
            store.is_type_assignable_to_with_global_types_and_strict_function_types(
                source,
                target,
                global_types,
                strict_function_types,
            )
        })?;
    Ok(resolution)
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
) -> Result<IdentityGenericCallResolution, IdentityGenericCallError> {
    validate_request_form(store, request)?;
    let shape = validate_identity_signature_shape(store, request.callee, callable)?;
    let argument = request.arguments[0];
    let type_argument = match request.explicit_type_arguments {
        Some(type_arguments) => {
            let type_argument = type_arguments[0];
            validate_inference_leaf(store, type_argument)
                .map_err(|_| IdentityGenericCallUnsupported::TypeArgumentLeaf(type_argument))?;
            type_argument
        }
        None => infer_naked_type_parameter(store, argument)
            .map_err(|_| IdentityGenericCallUnsupported::ArgumentLeaf(argument))?,
    };
    validate_inference_leaf(store, argument)
        .map_err(|_| IdentityGenericCallUnsupported::ArgumentLeaf(argument))?;

    let (signature, mapper, parameter_type, return_type) =
        get_or_create_identity_instantiation(store, shape, type_argument)?;
    let return_record = store.type_payload(return_type).ok_or(
        IdentityGenericCallInvariant::InvalidInstantiation {
            source: shape.type_parameter,
            expected: type_argument,
            actual: return_type,
        },
    )?;
    let return_kind = if return_record.flags().intersects(TypeFlags::VOID) {
        DirectCallReturnKind::Void
    } else {
        DirectCallReturnKind::Value
    };
    let projection = IdentityGenericCallProjection {
        callee: request.callee,
        generic_signature: shape.signature,
        signature,
        mapper,
        type_parameter: shape.type_parameter,
        type_argument,
        argument_target: DirectCallArgumentTarget {
            index: 0,
            argument_type: argument,
            parameter_type,
        },
        return_type,
        return_kind,
    };
    Ok(IdentityGenericCallResolution {
        projection,
        applicability: DirectCallApplicability::Applicable,
    })
}

fn validate_identity_signature_shape(
    store: &CanonicalTypeMapperStore,
    callee: TypeId,
    callable: &ValidatedSingleCallable,
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
    validate_unconstrained_default_free_parameter(store, type_parameter)?;
    Ok(IdentitySignatureShape {
        signature: callable.signature,
        type_parameter,
        parameter_symbol,
    })
}

fn validate_unconstrained_default_free_parameter(
    store: &CanonicalTypeMapperStore,
    type_parameter: TypeId,
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
    if record.flags() != TypeFlags::TYPE_PARAMETER
        || record.object_flags() != ObjectFlags::NONE
        || record.alias().is_some()
        || symbol_record.flags() != SymbolFlags::TYPE_PARAMETER
        || symbol_record.check_flags() != CheckFlags::NONE
        || store.get_merged_symbol(symbol) != Some(symbol)
        || data.constrained != ConstrainedTypeData::default()
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
    match data.resolved_default_type {
        None => {
            return Err(
                IdentityGenericCallUnsupported::UnresolvedTypeParameterDefault(type_parameter)
                    .into(),
            );
        }
        Some(default) if default != no_constraint => {
            return Err(
                IdentityGenericCallUnsupported::DefaultedTypeParameter(type_parameter).into(),
            );
        }
        Some(_) => Ok(()),
    }
}

fn get_or_create_identity_instantiation(
    store: &mut CanonicalTypeMapperStore,
    shape: IdentitySignatureShape,
    type_argument: TypeId,
) -> Result<(SignatureId, TypeMapperId, TypeId, TypeId), IdentityGenericCallError> {
    if let Some((signature, mapper)) = cached_identity_instantiation(store, shape, type_argument) {
        return Ok((signature, mapper, type_argument, type_argument));
    }
    if !store.try_reserve_checker_symbol_allocations(1, 0) || !store.try_reserve_signatures(1) {
        return Err(IdentityGenericCallInvariant::Capacity(shape.signature).into());
    }
    let mapper = store
        .new_simple_type_mapper(shape.type_parameter, type_argument)
        .ok_or(IdentityGenericCallInvariant::Publication(shape.signature))?;
    let parameter_type = instantiate_type(store, shape.type_parameter, mapper)?;
    let return_type = instantiate_type(store, shape.type_parameter, mapper)?;
    if parameter_type != type_argument {
        return Err(IdentityGenericCallInvariant::InvalidInstantiation {
            source: shape.type_parameter,
            expected: type_argument,
            actual: parameter_type,
        }
        .into());
    }
    if return_type != type_argument {
        return Err(IdentityGenericCallInvariant::InvalidInstantiation {
            source: shape.type_parameter,
            expected: type_argument,
            actual: return_type,
        }
        .into());
    }

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
    parameter_data.members = None;
    parameter_data.exports = None;
    parameter_data.export_symbol = None;
    let instantiated_parameter = store
        .alloc_symbol(parameter_data)
        .ok_or(IdentityGenericCallInvariant::Publication(shape.signature))?;
    if !store.set_value_symbol_links(
        instantiated_parameter,
        ValueSymbolLinks {
            resolved_type: Some(parameter_type),
            target: Some(shape.parameter_symbol),
            mapper: Some(mapper),
            name_type,
            ..ValueSymbolLinks::default()
        },
    ) {
        return Err(IdentityGenericCallInvariant::Publication(shape.signature).into());
    }
    let original =
        store
            .signature(shape.signature)
            .ok_or(IdentityGenericCallInvariant::InvalidSignature(
                shape.signature,
            ))?;
    let signature = store
        .alloc_signature(
            original.flags() & SignatureFlags::PROPAGATING_FLAGS,
            original.declaration(),
            Vec::new(),
            None,
            vec![instantiated_parameter],
            Some(return_type),
            None,
            original.min_argument_count(),
        )
        .ok_or(IdentityGenericCallInvariant::Publication(shape.signature))?;
    if !store.set_signature_target_and_mapper(signature, Some(shape.signature), Some(mapper)) {
        return Err(IdentityGenericCallInvariant::Publication(shape.signature).into());
    }
    Ok((signature, mapper, parameter_type, return_type))
}

fn cached_identity_instantiation(
    store: &CanonicalTypeMapperStore,
    shape: IdentitySignatureShape,
    type_argument: TypeId,
) -> Option<(SignatureId, TypeMapperId)> {
    let original = store.signature(shape.signature)?;
    for (signature_id, signature) in store.signatures() {
        let Some(mapper) = signature.mapper() else {
            continue;
        };
        let [parameter] = signature.parameters() else {
            continue;
        };
        let parameter = *parameter;
        if signature.flags() != original.flags() & SignatureFlags::PROPAGATING_FLAGS
            || signature.declaration() != original.declaration()
            || !signature.type_parameters().is_empty()
            || signature.this_parameter().is_some()
            || signature.resolved_return_type() != Some(type_argument)
            || signature.resolved_type_predicate().is_some()
            || signature.min_argument_count() != original.min_argument_count()
            || signature.resolved_min_argument_count() != -1
            || signature.target() != Some(shape.signature)
            || store.mapper_kind(mapper) != Some(TypeMapperKind::Simple)
            || store.map_type(mapper, shape.type_parameter) != Some(type_argument)
            || signature.isolated_signature_type().is_some()
            || signature.composite().is_some()
            || !cached_instantiated_parameter(
                store,
                parameter,
                shape.parameter_symbol,
                mapper,
                type_argument,
            )
        {
            continue;
        }
        return Some((signature_id, mapper));
    }
    None
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
    projection: &IdentityGenericCallProjection,
    mut is_assignable: impl FnMut(TypeId, TypeId) -> Result<bool, RelationUnavailable>,
) -> Result<DirectCallApplicability, RelationUnavailable> {
    let target = projection.argument_target;
    if is_assignable(target.argument_type, target.parameter_type)? {
        Ok(DirectCallApplicability::Applicable)
    } else {
        Ok(DirectCallApplicability::ArgumentNotAssignable {
            index: target.index,
            argument_type: target.argument_type,
            parameter_type: target.parameter_type,
        })
    }
}

#[cfg(test)]
mod tests {
    use ts_binder::{EscapedName, SymbolData};
    use ts_jsnum::Number;

    use super::*;
    use crate::semantic::{
        IntrinsicBootstrapOptions, SemanticStore, mapper::TypeMapper, type_records::TypeRecord,
    };

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
        let no_constraint = store.intrinsic_bootstrap().unwrap().no_constraint_type;
        assert!(store.set_type_parameter_resolution(
            type_parameter,
            Some(no_constraint),
            None,
            None,
            Some(no_constraint),
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
                check_identity_argument_applicability(&resolution.projection, |source, target| {
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
        )
        .unwrap();

        assert_eq!(resolution.projection.type_argument, string);
        assert_eq!(resolution.projection.return_type, string);
        assert_eq!(
            check_identity_argument_applicability(&resolution.projection, |source, target| {
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
            ),
            Err(IdentityGenericCallError::Unsupported(
                IdentityGenericCallUnsupported::NonNakedReturn(callable.signature)
            ))
        );
    }
}
