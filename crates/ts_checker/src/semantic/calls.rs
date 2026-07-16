//! Exact semantic kernel for one ordinary, direct call expression.
//!
//! This is the dependency-closed single-candidate branch of pinned
//! typescript-go `checkCallExpression`, `resolveCallExpression`, `resolveCall`,
//! `chooseOverload`, and `hasCorrectArity`. Syntax planning and expression
//! typing remain with the source checker. This module accepts an already-typed
//! callee and arguments, proves that the callee is one stored non-generic call
//! signature, checks fixed arity and argument assignability, and projects the
//! resolved return type. It never substitutes `any` for an unsupported or
//! malformed call.

use super::{
    CanonicalGlobalTypes, CanonicalTypeMapperStore, RelationUnavailable, SignatureId, TypeId,
    callables::{
        StoredSingleCallableValidation, ValidatedSingleCallable, validate_stored_single_callable,
    },
    signatures::SignatureFlags,
    type_records::TypeData,
    types::TypeFlags,
};

/// Call-like syntax presented to the direct-call semantic kernel.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum DirectCallForm {
    Call,
    #[allow(dead_code)] // Retained as an explicit typed rejection seam.
    New,
    #[allow(dead_code)] // Retained as an explicit typed rejection seam.
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

/// Resolves the dependency-closed single-non-generic-candidate call branch.
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

    let callable = match validate_stored_single_callable(store, request.callee) {
        StoredSingleCallableValidation::NotCallable => {
            return Err(DirectCallUnsupported::NotExactSingleCallable(request.callee).into());
        }
        StoredSingleCallableValidation::Pending { .. } => {
            return Err(DirectCallUnsupported::PendingCallable(request.callee).into());
        }
        StoredSingleCallableValidation::Malformed { .. } => {
            return Err(DirectCallInvariant::MalformedCallable(request.callee).into());
        }
        StoredSingleCallableValidation::Valid { callable, .. } => callable,
    };
    let mut resolution =
        project_validated_direct_call(store, Some(global_types), request, &callable)?;
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
    Ok(resolution)
}

fn validate_direct_call_form(request: DirectCallRequest<'_>) -> Result<(), DirectCallError> {
    if request.form != DirectCallForm::Call {
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
    use ts_binder::{EscapedName, SemanticSymbolId, SymbolData, SymbolFlags};

    use super::*;
    use crate::semantic::{
        IntrinsicBootstrapOptions, SemanticStore, TypeRecord, mapper::TypeMapper,
    };

    fn initialized_store() -> CanonicalTypeMapperStore {
        let mut store = SemanticStore::<TypeRecord, TypeMapper>::new();
        store
            .initialize_intrinsic_bootstrap(IntrinsicBootstrapOptions::default())
            .unwrap();
        store
    }

    fn parameter(store: &mut CanonicalTypeMapperStore, name: &str) -> SemanticSymbolId {
        store
            .alloc_symbol(SymbolData::new(
                SymbolFlags::FUNCTION_SCOPED_VARIABLE,
                EscapedName::source(name),
            ))
            .unwrap()
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
                    form: DirectCallForm::TaggedTemplate,
                    ..request(callee, &[])
                },
                DirectCallUnsupported::Form(DirectCallForm::TaggedTemplate),
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
