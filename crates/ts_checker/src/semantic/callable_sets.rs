//! Ordered, syntax-neutral callable-set projections.
//!
//! Providers retain ownership of syntax, binder provenance, and publication.
//! This leaf freezes the shared stored representation consumed by overload
//! selection: call signatures remain in provider order, followed by construct
//! signatures. Candidate reordering is deliberately a resolver concern.

use std::collections::HashSet;

use super::{
    CanonicalTypeMapperStore, SignatureId, TypeId,
    callables::{
        CallableFamily, StoredSingleCallableValidation, ValidatedSingleCallable,
        validate_stored_single_callable_provider,
    },
    object_members::{StoredDeclaredCallSetValidation, validate_stored_declared_call_set},
    signatures::SignatureFlags,
    source_overloads::{StoredSourceOverloadValidation, validate_stored_source_overload},
};

/// Immutable callable members after provider and store validation.
///
/// `call_signatures` preserves the stored call-signature prefix exactly.
/// Construct signatures retain their exact identities until the construct-call
/// semantic kernel is installed.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct CallableSetProjection {
    pub(super) owner: TypeId,
    pub(super) call_signatures: Box<[ValidatedSingleCallable]>,
    pub(super) construct_signatures: Box<[SignatureId]>,
}

/// Store-only callable-set classification shared by future overload consumers.
///
/// `edges` is provider-owned and includes every type dependency required by
/// graph validation. The normalized set intentionally contains only the
/// signatures visible to calls and constructs.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) enum StoredCallableSetValidation {
    NotCallable,
    Pending {
        family: CallableFamily,
    },
    Valid {
        family: CallableFamily,
        projection: CallableSetProjection,
        edges: Vec<TypeId>,
    },
    Malformed {
        family: CallableFamily,
    },
}

/// Validates every installed callable provider and normalizes its ordered set.
///
/// Exact-single providers retain their established validation path. The
/// declared-member provider proves its source and publication provenance first,
/// then reuses [`validate_stored_callable_set_projection`] for the common
/// ordered representation.
pub(super) fn validate_stored_callable_set(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
) -> StoredCallableSetValidation {
    match validate_stored_single_callable_provider(store, type_) {
        StoredSingleCallableValidation::NotCallable => {}
        StoredSingleCallableValidation::Pending { family } => {
            return StoredCallableSetValidation::Pending { family };
        }
        StoredSingleCallableValidation::Malformed { family } => {
            return StoredCallableSetValidation::Malformed { family };
        }
        StoredSingleCallableValidation::Valid {
            family,
            callable,
            edges,
        } => {
            return StoredCallableSetValidation::Valid {
                family,
                projection: CallableSetProjection {
                    owner: type_,
                    call_signatures: Box::new([callable]),
                    construct_signatures: Box::new([]),
                },
                edges,
            };
        }
    }
    let family = CallableFamily::SourceFunctionOverloads;
    match validate_stored_source_overload(store, type_) {
        StoredSourceOverloadValidation::NotSourceOverload => {}
        StoredSourceOverloadValidation::Malformed => {
            return StoredCallableSetValidation::Malformed { family };
        }
        StoredSourceOverloadValidation::Valid(edges) => {
            let Some(projection) =
                validate_stored_callable_set_projection(store, type_, false)
            else {
                return StoredCallableSetValidation::Malformed { family };
            };
            return StoredCallableSetValidation::Valid {
                family,
                projection,
                edges,
            };
        }
    }
    let family = CallableFamily::DeclaredCallSignatures;
    match validate_stored_declared_call_set(store, type_) {
        StoredDeclaredCallSetValidation::NotDeclaredCallSet => {
            StoredCallableSetValidation::NotCallable
        }
        StoredDeclaredCallSetValidation::Malformed => {
            StoredCallableSetValidation::Malformed { family }
        }
        StoredDeclaredCallSetValidation::Valid(edges) => {
            let Some(projection) = validate_stored_callable_set_projection(store, type_, false)
            else {
                return StoredCallableSetValidation::Malformed { family };
            };
            StoredCallableSetValidation::Valid {
                family,
                projection,
                edges,
            }
        }
    }
}

/// Projects one provider-proven structured-signature cache without changing
/// its order.
///
/// This function does not decide whether `owner` belongs to a callable family.
/// Callers must first prove provider-specific source and cache provenance. It
/// validates the common immutable suffix: a unique call prefix, a unique
/// construct suffix, exact parameter-value caches, and store-owned type edges.
pub(super) fn validate_stored_callable_set_projection(
    store: &CanonicalTypeMapperStore,
    owner: TypeId,
    strict_variance_exempt: bool,
) -> Option<CallableSetProjection> {
    validate_stored_callable_set_projection_with(
        store,
        owner,
        strict_variance_exempt,
        |signature| {
            store
                .callable_signature_parameter_types(signature)
                .map(<[TypeId]>::to_vec)
        },
    )
}

fn validate_stored_callable_set_projection_with(
    store: &CanonicalTypeMapperStore,
    owner: TypeId,
    strict_variance_exempt: bool,
    mut parameter_types: impl FnMut(SignatureId) -> Option<Vec<TypeId>>,
) -> Option<CallableSetProjection> {
    let structured = store.type_payload(owner)?.data().structured()?;
    let signatures = structured.signatures.as_deref()?;
    if signatures.is_empty() || structured.call_signature_count > signatures.len() {
        return None;
    }

    let mut unique = HashSet::with_capacity(signatures.len());
    let mut call_signatures = Vec::with_capacity(structured.call_signature_count);
    let mut construct_signatures =
        Vec::with_capacity(signatures.len() - structured.call_signature_count);
    for (index, signature) in signatures.iter().copied().enumerate() {
        if !unique.insert(signature) {
            return None;
        }
        let record = store.signature(signature)?;
        let is_construct = record.flags().contains(SignatureFlags::CONSTRUCT);
        if is_construct != (index >= structured.call_signature_count) {
            return None;
        }
        let mut parameters = parameter_types(signature)?;
        if parameters.len() != record.parameters().len()
            || parameters
                .iter()
                .any(|parameter| store.type_payload(*parameter).is_none())
            || record
                .resolved_return_type()
                .is_some_and(|return_type| store.type_payload(return_type).is_none())
        {
            return None;
        }
        let minimum = usize::try_from(record.min_argument_count()).ok()?;
        let rest_parameter = if record.has_rest_parameter() {
            Some(parameters.pop()?)
        } else {
            None
        };
        if minimum > parameters.len() {
            return None;
        }

        if is_construct {
            construct_signatures.push(signature);
        } else {
            call_signatures.push(ValidatedSingleCallable {
                owner,
                signature,
                parameters,
                rest_parameter,
                min_argument_count: minimum,
                return_type: record.resolved_return_type(),
                strict_variance_exempt,
            });
        }
    }

    Some(CallableSetProjection {
        owner,
        call_signatures: call_signatures.into_boxed_slice(),
        construct_signatures: construct_signatures.into_boxed_slice(),
    })
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use ts_binder::{EscapedName, SymbolData, SymbolFlags};

    use super::*;
    use crate::semantic::{
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

    fn signature(
        store: &mut CanonicalTypeMapperStore,
        flags: SignatureFlags,
        parameter_types: &[TypeId],
        minimum: i32,
        return_type: TypeId,
    ) -> SignatureId {
        let parameters = parameter_types
            .iter()
            .enumerate()
            .map(|(index, _)| {
                store
                    .alloc_symbol(SymbolData::new(
                        SymbolFlags::FUNCTION_SCOPED_VARIABLE,
                        EscapedName::source(format!("p{index}")),
                    ))
                    .unwrap()
            })
            .collect();
        store
            .alloc_signature(
                flags,
                None,
                Vec::new(),
                None,
                parameters,
                Some(return_type),
                None,
                minimum,
            )
            .unwrap()
    }

    fn owner(
        store: &mut CanonicalTypeMapperStore,
        calls: Vec<SignatureId>,
        constructs: Vec<SignatureId>,
    ) -> TypeId {
        let owner = store
            .alloc_plain_object_type(ObjectFlags::ANONYMOUS, None)
            .unwrap();
        assert!(store.set_structured_type_members(
            owner,
            None,
            None,
            Some(calls),
            Some(constructs),
            None,
        ));
        owner
    }

    fn project(
        store: &CanonicalTypeMapperStore,
        owner: TypeId,
        parameter_types: &HashMap<SignatureId, Vec<TypeId>>,
    ) -> Option<CallableSetProjection> {
        validate_stored_callable_set_projection_with(store, owner, false, |signature| {
            parameter_types.get(&signature).cloned()
        })
    }

    #[test]
    fn call_order_and_construct_partition_are_preserved() {
        let mut store = initialized_store();
        let bootstrap = store.intrinsic_bootstrap().unwrap();
        let number = bootstrap.number_type;
        let string = bootstrap.string_type;
        let first = signature(&mut store, SignatureFlags::NONE, &[number], 1, string);
        let second = signature(&mut store, SignatureFlags::NONE, &[string], 1, number);
        let construct = signature(&mut store, SignatureFlags::CONSTRUCT, &[number], 1, string);
        let owner = owner(&mut store, vec![second, first], vec![construct]);
        let parameter_types = HashMap::from([
            (first, vec![number]),
            (second, vec![string]),
            (construct, vec![number]),
        ]);

        let projected = project(&store, owner, &parameter_types).unwrap();
        assert_eq!(projected.owner, owner);
        assert_eq!(
            projected
                .call_signatures
                .iter()
                .map(|callable| callable.signature)
                .collect::<Vec<_>>(),
            vec![second, first]
        );
        assert_eq!(projected.construct_signatures.as_ref(), &[construct]);
    }

    #[test]
    fn duplicate_signature_ids_are_rejected() {
        let mut store = initialized_store();
        let number = store.intrinsic_bootstrap().unwrap().number_type;
        let signature = signature(&mut store, SignatureFlags::NONE, &[], 0, number);
        let owner = owner(&mut store, vec![signature, signature], Vec::new());
        let parameter_types = HashMap::from([(signature, Vec::new())]);

        assert_eq!(project(&store, owner, &parameter_types), None);
    }

    #[test]
    fn call_and_construct_flags_must_match_the_stored_prefix() {
        let mut store = initialized_store();
        let number = store.intrinsic_bootstrap().unwrap().number_type;
        let call = signature(&mut store, SignatureFlags::NONE, &[], 0, number);
        let construct = signature(&mut store, SignatureFlags::CONSTRUCT, &[], 0, number);
        let parameter_types = HashMap::from([(call, Vec::new()), (construct, Vec::new())]);
        let construct_in_call_prefix = owner(&mut store, vec![construct], Vec::new());
        let call_in_construct_suffix = owner(&mut store, Vec::new(), vec![call]);

        assert_eq!(
            project(&store, construct_in_call_prefix, &parameter_types),
            None
        );
        assert_eq!(
            project(&store, call_in_construct_suffix, &parameter_types),
            None
        );
    }

    #[test]
    fn missing_or_malformed_parameter_caches_are_rejected() {
        let mut store = initialized_store();
        let bootstrap = store.intrinsic_bootstrap().unwrap();
        let number = bootstrap.number_type;
        let string = bootstrap.string_type;
        let signature = signature(&mut store, SignatureFlags::NONE, &[number], 1, string);
        let owner = owner(&mut store, vec![signature], Vec::new());

        assert_eq!(project(&store, owner, &HashMap::new()), None);
        assert_eq!(
            project(&store, owner, &HashMap::from([(signature, Vec::new())])),
            None
        );
    }

    #[test]
    fn foreign_types_and_owners_are_rejected() {
        let mut store = initialized_store();
        let number = store.intrinsic_bootstrap().unwrap().number_type;
        let signature = signature(&mut store, SignatureFlags::NONE, &[number], 1, number);
        let owner = owner(&mut store, vec![signature], Vec::new());
        let foreign = initialized_store();
        let foreign_number = foreign.intrinsic_bootstrap().unwrap().number_type;

        assert_eq!(
            project(
                &store,
                owner,
                &HashMap::from([(signature, vec![foreign_number])])
            ),
            None
        );
        assert_eq!(
            project(
                &store,
                foreign_number,
                &HashMap::from([(signature, vec![number])])
            ),
            None
        );
    }

    #[test]
    fn invalid_minimum_and_rest_shapes_are_rejected() {
        let mut store = initialized_store();
        let number = store.intrinsic_bootstrap().unwrap().number_type;
        let invalid_minimum = signature(&mut store, SignatureFlags::NONE, &[], 1, number);
        let missing_rest = signature(
            &mut store,
            SignatureFlags::HAS_REST_PARAMETER,
            &[],
            0,
            number,
        );
        let invalid_rest_minimum = signature(
            &mut store,
            SignatureFlags::HAS_REST_PARAMETER,
            &[number],
            1,
            number,
        );
        let parameter_types = HashMap::from([
            (invalid_minimum, Vec::new()),
            (missing_rest, Vec::new()),
            (invalid_rest_minimum, vec![number]),
        ]);
        let invalid_minimum_owner = owner(&mut store, vec![invalid_minimum], Vec::new());
        let missing_rest_owner = owner(&mut store, vec![missing_rest], Vec::new());
        let invalid_rest_minimum_owner = owner(&mut store, vec![invalid_rest_minimum], Vec::new());

        assert_eq!(
            project(&store, invalid_minimum_owner, &parameter_types),
            None
        );
        assert_eq!(project(&store, missing_rest_owner, &parameter_types), None);
        assert_eq!(
            project(&store, invalid_rest_minimum_owner, &parameter_types),
            None,
        );
    }

    #[test]
    fn rest_only_callables_have_zero_fixed_arity() {
        let mut store = initialized_store();
        let number = store.intrinsic_bootstrap().unwrap().number_type;
        let rest = signature(
            &mut store,
            SignatureFlags::HAS_REST_PARAMETER,
            &[number],
            0,
            number,
        );
        let owner = owner(&mut store, vec![rest], Vec::new());
        let projected = project(&store, owner, &HashMap::from([(rest, vec![number])])).unwrap();
        let [callable] = projected.call_signatures.as_ref() else {
            panic!("expected one call signature")
        };
        assert!(callable.parameters.is_empty());
        assert_eq!(callable.rest_parameter, Some(number));
        assert_eq!(callable.min_argument_count, 0);
    }
}
