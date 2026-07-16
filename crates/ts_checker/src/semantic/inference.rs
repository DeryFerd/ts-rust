//! Dependency-closed inference for a naked type parameter.
//!
//! This is the first exact branch of pinned `inferTypes` used by generic call
//! resolution. When the target is the inference context's type parameter,
//! upstream records the source type itself as a covariant candidate. The
//! bounded Rust branch accepts only primitive, literal, unique-symbol, and
//! anonymous primitive-union candidates. It preserves candidates that do not
//! require widening, including fresh literals. Widening sentinels remain a
//! typed boundary until the exact final `getWidenedType` step is available.

#![allow(dead_code)] // Installed ahead of the generic-call dispatch consumer.

use std::collections::HashSet;

use super::{
    TypeId,
    bootstrap::LiteralTypeCacheError,
    mapper::CanonicalTypeMapperStore,
    type_records::TypeData,
    types::{ObjectFlags, TypeFlags},
};

/// A missing dependency or shape outside naked leaf inference.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum NakedTypeInferenceError {
    InvalidCandidate(TypeId),
    InvalidCanonicalCandidate {
        candidate: TypeId,
        error: LiteralTypeCacheError,
    },
    UnsupportedCandidate(TypeId),
    RequiresWidening(TypeId),
    AliasedUnion(TypeId),
    OriginUnion(TypeId),
    EmptyUnion(TypeId),
    NestedUnion {
        union: TypeId,
        constituent: TypeId,
    },
    DuplicateUnionConstituent {
        union: TypeId,
        constituent: TypeId,
    },
}

/// Infers one naked type parameter from one already-typed argument.
///
/// The return is the exact candidate identity only after proving that pinned
/// `getCovariantInference` would not take its final widening path.
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
    match store.validate_union_constituent(candidate) {
        Ok(()) => {}
        Err(LiteralTypeCacheError::UnsupportedUnionConstituent(_)) => {
            return Err(NakedTypeInferenceError::UnsupportedCandidate(candidate));
        }
        Err(error) => {
            return Err(NakedTypeInferenceError::InvalidCanonicalCandidate { candidate, error });
        }
    }
    if record
        .object_flags()
        .intersects(ObjectFlags::REQUIRES_WIDENING)
    {
        return Err(NakedTypeInferenceError::RequiresWidening(candidate));
    }
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
    use ts_binder::{EscapedName, SymbolData, SymbolFlags};

    use super::*;
    use crate::semantic::{
        IntrinsicBootstrapOptions, SemanticStore, bootstrap::UnionReduction, mapper::TypeMapper,
        type_records::TypeRecord,
    };

    fn initialized_store_with(strict_null_checks: bool) -> CanonicalTypeMapperStore {
        let mut store = SemanticStore::<TypeRecord, TypeMapper>::new();
        store
            .initialize_intrinsic_bootstrap(IntrinsicBootstrapOptions {
                strict_null_checks,
                ..IntrinsicBootstrapOptions::default()
            })
            .unwrap();
        store
    }

    fn initialized_store() -> CanonicalTypeMapperStore {
        initialized_store_with(false)
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
            .expression_union_type(&[string, number], UnionReduction::None)
            .unwrap();

        assert_eq!(infer_naked_type_parameter(&store, string), Ok(string));
        assert_eq!(infer_naked_type_parameter(&store, union), Ok(union));
    }

    #[test]
    fn aliases_and_origins_fail_closed() {
        let mut store = initialized_store();
        let bootstrap = store.intrinsic_bootstrap().unwrap();
        let string = bootstrap.string_type;
        let number = bootstrap.number_type;
        let bigint = bootstrap.bigint_type;

        let alias_symbol = store
            .alloc_symbol(SymbolData::new(
                SymbolFlags::TYPE_ALIAS,
                EscapedName::source("Alias"),
            ))
            .unwrap();
        let aliased = store
            .literal_union_type(&[string, number], Some(alias_symbol))
            .unwrap();
        assert_eq!(
            infer_naked_type_parameter(&store, aliased),
            Err(NakedTypeInferenceError::AliasedUnion(aliased))
        );

        let outer = store
            .expression_union_type(&[aliased, bigint], UnionReduction::None)
            .unwrap();
        assert_eq!(
            infer_naked_type_parameter(&store, outer),
            Err(NakedTypeInferenceError::OriginUnion(outer))
        );
    }

    #[test]
    fn malformed_literal_cache_is_an_invariant() {
        let mut store = initialized_store();
        let regular = store.regular_string_literal_type("x".into()).unwrap();
        let fresh = store.fresh_type_of_literal_type(regular).unwrap();
        assert!(store.set_literal_links(fresh, None, regular));

        assert_eq!(
            infer_naked_type_parameter(&store, fresh),
            Err(NakedTypeInferenceError::InvalidCanonicalCandidate {
                candidate: fresh,
                error: LiteralTypeCacheError::InvalidCachedLiteral(fresh),
            })
        );
    }

    #[test]
    fn null_and_undefined_widening_follow_strictness() {
        let strict = initialized_store_with(true);
        let strict_bootstrap = strict.intrinsic_bootstrap().unwrap();
        assert_eq!(
            infer_naked_type_parameter(&strict, strict_bootstrap.undefined_widening_type),
            Ok(strict_bootstrap.undefined_type)
        );
        assert_eq!(
            infer_naked_type_parameter(&strict, strict_bootstrap.null_widening_type),
            Ok(strict_bootstrap.null_type)
        );

        let non_strict = initialized_store_with(false);
        let non_strict_bootstrap = non_strict.intrinsic_bootstrap().unwrap();
        assert_eq!(
            infer_naked_type_parameter(&non_strict, non_strict_bootstrap.undefined_type),
            Ok(non_strict_bootstrap.undefined_type)
        );
        assert_eq!(
            infer_naked_type_parameter(&non_strict, non_strict_bootstrap.null_type),
            Ok(non_strict_bootstrap.null_type)
        );
        assert_eq!(
            infer_naked_type_parameter(&non_strict, non_strict_bootstrap.undefined_widening_type),
            Err(NakedTypeInferenceError::RequiresWidening(
                non_strict_bootstrap.undefined_widening_type
            ))
        );
        assert_eq!(
            infer_naked_type_parameter(&non_strict, non_strict_bootstrap.null_widening_type),
            Err(NakedTypeInferenceError::RequiresWidening(
                non_strict_bootstrap.null_widening_type
            ))
        );
    }
}
