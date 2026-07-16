//! Dependency-closed inference for a naked type parameter.
//!
//! This is the first exact branch of pinned `inferTypes` used by generic call
//! resolution. When the target is the inference context's type parameter,
//! upstream records the source type itself as a covariant candidate. The
//! bounded Rust branch accepts only primitive, literal, unique-symbol, and
//! anonymous primitive-union candidates. In particular, it preserves fresh
//! literal identity for `<T>(value: T): T`; widening is intentionally not
//! performed because `T` occurs at top level in the return type.

#![allow(dead_code)] // Installed ahead of the generic-call dispatch consumer.

use std::collections::HashSet;

use super::{TypeId, mapper::CanonicalTypeMapperStore, type_records::TypeData, types::TypeFlags};

/// A missing dependency or shape outside naked leaf inference.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum NakedTypeInferenceError {
    InvalidCandidate(TypeId),
    UnsupportedCandidate(TypeId),
    AliasedUnion(TypeId),
    OriginUnion(TypeId),
    EmptyUnion(TypeId),
    NestedUnion { union: TypeId, constituent: TypeId },
    DuplicateUnionConstituent { union: TypeId, constituent: TypeId },
}

/// Infers one naked type parameter from one already-typed argument.
///
/// The return is deliberately the exact candidate identity. Pinned
/// `getCovariantInference` does not widen fresh literals when the inferred type
/// parameter occurs at top level in the signature return, which is the only
/// signature shape admitted by the first generic-call consumer.
pub(super) fn infer_naked_type_parameter(
    store: &CanonicalTypeMapperStore,
    candidate: TypeId,
) -> Result<TypeId, NakedTypeInferenceError> {
    validate_inference_leaf(store, candidate)?;
    Ok(candidate)
}

/// Proves that a type is inside the first explicit/inferred argument domain.
pub(super) fn validate_inference_leaf(
    store: &CanonicalTypeMapperStore,
    candidate: TypeId,
) -> Result<(), NakedTypeInferenceError> {
    let record = store
        .type_payload(candidate)
        .ok_or(NakedTypeInferenceError::InvalidCandidate(candidate))?;
    match record.data() {
        TypeData::Intrinsic(_) if intrinsic_leaf_flags(record.flags()) => Ok(()),
        TypeData::Literal(_) if literal_leaf_flags(record.flags()) => Ok(()),
        TypeData::UniqueEsSymbol(_) if record.flags() == TypeFlags::UNIQUE_ES_SYMBOL => Ok(()),
        TypeData::Union(union) => {
            if record.alias().is_some() {
                return Err(NakedTypeInferenceError::AliasedUnion(candidate));
            }
            if union.origin.is_some() {
                return Err(NakedTypeInferenceError::OriginUnion(candidate));
            }
            if union.union.types.is_empty() {
                return Err(NakedTypeInferenceError::EmptyUnion(candidate));
            }
            let mut seen = HashSet::with_capacity(union.union.types.len());
            for constituent in &union.union.types {
                if !seen.insert(*constituent) {
                    return Err(NakedTypeInferenceError::DuplicateUnionConstituent {
                        union: candidate,
                        constituent: *constituent,
                    });
                }
                if store
                    .type_payload(*constituent)
                    .is_some_and(|record| matches!(record.data(), TypeData::Union(_)))
                {
                    return Err(NakedTypeInferenceError::NestedUnion {
                        union: candidate,
                        constituent: *constituent,
                    });
                }
                validate_inference_leaf(store, *constituent)?;
            }
            Ok(())
        }
        _ => Err(NakedTypeInferenceError::UnsupportedCandidate(candidate)),
    }
}

fn intrinsic_leaf_flags(flags: TypeFlags) -> bool {
    flags == TypeFlags::ANY
        || flags == TypeFlags::UNKNOWN
        || flags == TypeFlags::UNDEFINED
        || flags == TypeFlags::NULL
        || flags == TypeFlags::VOID
        || flags == TypeFlags::STRING
        || flags == TypeFlags::NUMBER
        || flags == TypeFlags::BIG_INT
        || flags == TypeFlags::BOOLEAN
        || flags == TypeFlags::ES_SYMBOL
        || flags == TypeFlags::NON_PRIMITIVE
        || flags == TypeFlags::NEVER
}

fn literal_leaf_flags(flags: TypeFlags) -> bool {
    flags == TypeFlags::STRING_LITERAL
        || flags == TypeFlags::NUMBER_LITERAL
        || flags == TypeFlags::BIG_INT_LITERAL
        || flags == TypeFlags::BOOLEAN_LITERAL
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::semantic::{
        IntrinsicBootstrapOptions, SemanticStore, mapper::TypeMapper, type_records::TypeRecord,
        types::ObjectFlags,
    };

    fn initialized_store() -> CanonicalTypeMapperStore {
        let mut store = SemanticStore::<TypeRecord, TypeMapper>::new();
        store
            .initialize_intrinsic_bootstrap(IntrinsicBootstrapOptions::default())
            .unwrap();
        store
    }

    #[test]
    fn naked_inference_preserves_fresh_literal_identity() {
        let mut store = initialized_store();
        let regular = store.regular_string_literal_type("x".into()).unwrap();
        let fresh = store.fresh_type_of_literal_type(regular).unwrap();

        assert_eq!(infer_naked_type_parameter(&store, fresh), Ok(fresh));
        assert_ne!(fresh, regular);
    }

    #[test]
    fn primitive_and_anonymous_union_leaves_are_admitted() {
        let mut store = initialized_store();
        let bootstrap = store.intrinsic_bootstrap().unwrap();
        let string = bootstrap.string_type;
        let number = bootstrap.number_type;
        let union = store
            .alloc_union_type(ObjectFlags::PRIMITIVE_UNION, vec![string, number])
            .unwrap();

        assert_eq!(infer_naked_type_parameter(&store, string), Ok(string));
        assert_eq!(infer_naked_type_parameter(&store, union), Ok(union));
    }

    #[test]
    fn aliases_origins_and_nested_unions_fail_closed() {
        let mut store = initialized_store();
        let bootstrap = store.intrinsic_bootstrap().unwrap();
        let string = bootstrap.string_type;
        let number = bootstrap.number_type;

        let aliased = store
            .alloc_union_type(ObjectFlags::PRIMITIVE_UNION, vec![string, number])
            .unwrap();
        let alias = store.alloc_type_alias(None).unwrap();
        assert!(store.set_type_alias(aliased, Some(alias)));
        assert_eq!(
            infer_naked_type_parameter(&store, aliased),
            Err(NakedTypeInferenceError::AliasedUnion(aliased))
        );

        let inner = store
            .alloc_union_type(ObjectFlags::PRIMITIVE_UNION, vec![string, number])
            .unwrap();
        let outer = store
            .alloc_union_type(ObjectFlags::PRIMITIVE_UNION, vec![inner, string])
            .unwrap();
        assert_eq!(
            infer_naked_type_parameter(&store, outer),
            Err(NakedTypeInferenceError::NestedUnion {
                union: outer,
                constituent: inner,
            })
        );
    }
}
