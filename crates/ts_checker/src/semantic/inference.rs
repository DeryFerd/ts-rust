//! Dependency-closed inference for a naked type parameter.
//!
//! This is the first exact branch of pinned `inferTypes` used by generic call
//! resolution. When the target is the inference context's type parameter,
//! upstream records the source type itself as a covariant candidate. The
//! bounded Rust branch accepts primitive, literal, unique-symbol, anonymous
//! primitive-union, and exact resolved nongeneric declared-property-object
//! candidates. Declared objects are admitted only as the root candidate, not
//! recursively inside a union. The branch preserves candidates that do not
//! require widening, including fresh literals. Widening sentinels remain a
//! typed boundary until the exact final `getWidenedType` step is available.

#![allow(dead_code)] // Installed ahead of the generic-call dispatch consumer.

use std::collections::HashSet;

use super::{
    RelationUnavailable, TypeId,
    bootstrap::LiteralTypeCacheError,
    instantiate::canonical_anonymous_union,
    mapper::CanonicalTypeMapperStore,
    object_members::{
        DeclaredPropertyObjectValidation, validate_resolved_declared_property_object,
    },
    type_records::TypeData,
    types::{ObjectFlags, TypeFlags},
};

/// Literal handling selected by pinned `getCovariantInference` for one naked
/// type parameter's candidate bucket.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum InferenceLiteralTreatment {
    /// The type parameter occurs at top level in the return type.
    Preserve,
    /// A primitive constraint converts fresh literals to their regular peers.
    Regularize,
    /// A top-level parameter that is not returned widens fresh literals.
    Widen,
}

/// Failure while finalizing one declaration-order inference bucket.
#[derive(Debug, PartialEq)]
pub(super) enum NakedTypeCandidateError {
    Candidate(NakedTypeInferenceError),
    Union(LiteralTypeCacheError),
    Relation(RelationUnavailable),
}

impl From<NakedTypeInferenceError> for NakedTypeCandidateError {
    fn from(error: NakedTypeInferenceError) -> Self {
        Self::Candidate(error)
    }
}

impl From<LiteralTypeCacheError> for NakedTypeCandidateError {
    fn from(error: LiteralTypeCacheError) -> Self {
        Self::Union(error)
    }
}

impl From<RelationUnavailable> for NakedTypeCandidateError {
    fn from(error: RelationUnavailable) -> Self {
        Self::Relation(error)
    }
}

/// A missing dependency or shape outside naked leaf inference.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum NakedTypeInferenceError {
    InvalidCandidate(TypeId),
    InvalidCanonicalCandidate {
        candidate: TypeId,
        error: LiteralTypeCacheError,
    },
    MalformedDeclaredPropertyObject(TypeId),
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

/// Finalizes all covariant candidates collected for one naked type parameter.
///
/// Candidate identity is de-duplicated in encounter order. Same-base literal
/// candidates form a canonical literal union; otherwise the exact two-pass
/// strict-subtype/subtype selection chooses the single common supertype.
/// Strict-null inference removes nullable constituents before selection and
/// adds the combined nullable flags back afterward. `None` means no inference
/// was made and leaves default/constraint/unknown fallback to the owning call
/// context.
pub(super) fn infer_naked_type_parameter_candidates(
    store: &mut CanonicalTypeMapperStore,
    candidates: &[TypeId],
    treatment: InferenceLiteralTreatment,
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
) -> Result<Option<TypeId>, NakedTypeCandidateError> {
    let mut prepared = Vec::with_capacity(candidates.len());
    for candidate in candidates {
        validate_inference_leaf(store, *candidate)?;
        let candidate = inference_candidate_literal_treatment(store, *candidate, treatment)?;
        if !prepared.contains(&candidate) {
            prepared.push(candidate);
        }
    }
    if prepared.is_empty() {
        return Ok(None);
    }
    let strict_null_checks = store
        .intrinsic_bootstrap()
        .ok_or(LiteralTypeCacheError::BootstrapUninitialized)?
        .options
        .strict_null_checks;
    let nullable = combined_nullable_flags(store, &prepared)?;
    let primary = if strict_null_checks {
        let mut primary = Vec::with_capacity(prepared.len());
        for candidate in &prepared {
            primary.push(remove_nullable_from_candidate(store, *candidate)?);
        }
        primary
    } else {
        prepared
    };
    let common = if primary.len() == 1 {
        primary[0]
    } else if literal_candidates_have_same_base(store, &primary) {
        canonical_anonymous_union(store, &primary)?
    } else {
        single_common_supertype(
            store,
            &primary,
            &mut is_strict_subtype,
            &mut is_subtype,
        )?
    };
    if strict_null_checks && nullable != TypeFlags::NONE {
        add_nullable_to_candidate(store, common, nullable).map(Some)
    } else {
        Ok(Some(common))
    }
}

fn single_common_supertype(
    store: &mut CanonicalTypeMapperStore,
    types: &[TypeId],
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
) -> Result<TypeId, NakedTypeCandidateError> {
    let strict_candidate = find_leftmost_type(store, types, is_strict_subtype)?;
    let mut strict_supertype = true;
    for type_ in types {
        if *type_ != strict_candidate && !is_strict_subtype(store, *type_, strict_candidate)? {
            strict_supertype = false;
            break;
        }
    }
    if strict_supertype {
        return Ok(strict_candidate);
    }
    find_leftmost_type(store, types, is_subtype)
}

fn find_leftmost_type(
    store: &mut CanonicalTypeMapperStore,
    types: &[TypeId],
    relation: &mut impl FnMut(
        &mut CanonicalTypeMapperStore,
        TypeId,
        TypeId,
    ) -> Result<bool, RelationUnavailable>,
) -> Result<TypeId, NakedTypeCandidateError> {
    let mut candidate = None;
    for type_ in types {
        if candidate.is_none() || relation(store, candidate.unwrap(), *type_)? {
            candidate = Some(*type_);
        }
    }
    Ok(candidate.expect("candidate finalization proved a nonempty bucket"))
}

fn combined_nullable_flags(
    store: &CanonicalTypeMapperStore,
    candidates: &[TypeId],
) -> Result<TypeFlags, NakedTypeCandidateError> {
    let mut flags = TypeFlags::NONE;
    for candidate in candidates {
        let record = store.type_payload(*candidate).ok_or(
            LiteralTypeCacheError::UnsupportedUnionConstituent(*candidate),
        )?;
        match record.data() {
            TypeData::Union(union) => {
                flags |= combined_nullable_flags(store, &union.union.types)?;
            }
            _ => flags |= record.flags() & TypeFlags::NULLABLE,
        }
    }
    Ok(flags)
}

fn remove_nullable_from_candidate(
    store: &mut CanonicalTypeMapperStore,
    candidate: TypeId,
) -> Result<TypeId, NakedTypeCandidateError> {
    let record = store.type_payload(candidate).ok_or(
        LiteralTypeCacheError::UnsupportedUnionConstituent(candidate),
    )?;
    if record.flags().intersects(TypeFlags::NULLABLE) {
        return store
            .intrinsic_bootstrap()
            .map(|bootstrap| bootstrap.never_type)
            .ok_or(LiteralTypeCacheError::BootstrapUninitialized.into());
    }
    let TypeData::Union(union) = record.data() else {
        return Ok(candidate);
    };
    let constituents = union.union.types.clone();
    let mut filtered = Vec::with_capacity(constituents.len());
    let mut changed = false;
    for constituent in constituents {
        let primary = remove_nullable_from_candidate(store, constituent)?;
        changed |= primary != constituent;
        filtered.push(primary);
    }
    if changed {
        canonical_anonymous_union(store, &filtered).map_err(Into::into)
    } else {
        Ok(candidate)
    }
}

fn add_nullable_to_candidate(
    store: &mut CanonicalTypeMapperStore,
    candidate: TypeId,
    nullable: TypeFlags,
) -> Result<TypeId, NakedTypeCandidateError> {
    let bootstrap = store
        .intrinsic_bootstrap()
        .ok_or(LiteralTypeCacheError::BootstrapUninitialized)?;
    let undefined = bootstrap.undefined_type;
    let null = bootstrap.null_type;
    let mut types = Vec::with_capacity(3);
    types.push(candidate);
    if nullable.intersects(TypeFlags::UNDEFINED) {
        types.push(undefined);
    }
    if nullable.intersects(TypeFlags::NULL) {
        types.push(null);
    }
    canonical_anonymous_union(store, &types).map_err(Into::into)
}

fn inference_candidate_literal_treatment(
    store: &mut CanonicalTypeMapperStore,
    candidate: TypeId,
    treatment: InferenceLiteralTreatment,
) -> Result<TypeId, LiteralTypeCacheError> {
    if treatment == InferenceLiteralTreatment::Preserve {
        return Ok(candidate);
    }
    let record =
        store
            .type_payload(candidate)
            .ok_or(LiteralTypeCacheError::UnsupportedUnionConstituent(
                candidate,
            ))?;
    match record.data() {
        TypeData::Literal(data) => {
            let regular = data.regular_type;
            let fresh = data.fresh_type == Some(candidate) && regular != candidate;
            if treatment == InferenceLiteralTreatment::Regularize {
                return Ok(regular);
            }
            if !fresh {
                return Ok(candidate);
            }
            let bootstrap = store
                .intrinsic_bootstrap()
                .ok_or(LiteralTypeCacheError::BootstrapUninitialized)?;
            if record.flags() == TypeFlags::STRING_LITERAL {
                Ok(bootstrap.string_type)
            } else if record.flags() == TypeFlags::NUMBER_LITERAL {
                Ok(bootstrap.number_type)
            } else if record.flags() == TypeFlags::BIG_INT_LITERAL {
                Ok(bootstrap.bigint_type)
            } else if record.flags() == TypeFlags::BOOLEAN_LITERAL {
                Ok(bootstrap.boolean_type)
            } else {
                Err(LiteralTypeCacheError::UnsupportedUnionConstituent(
                    candidate,
                ))
            }
        }
        TypeData::Union(data) => {
            let constituents = data.union.types.clone();
            let mut treated = Vec::with_capacity(constituents.len());
            let mut changed = false;
            for constituent in constituents {
                let mapped = inference_candidate_literal_treatment(store, constituent, treatment)?;
                changed |= mapped != constituent;
                treated.push(mapped);
            }
            if changed {
                canonical_anonymous_union(store, &treated)
            } else {
                Ok(candidate)
            }
        }
        _ => Ok(candidate),
    }
}

fn literal_candidates_have_same_base(
    store: &CanonicalTypeMapperStore,
    candidates: &[TypeId],
) -> bool {
    let mut base = None;
    for candidate in candidates {
        let Some(record) = store.type_payload(*candidate) else {
            return false;
        };
        if record.flags().intersects(TypeFlags::NEVER) {
            continue;
        }
        let Some(candidate_base) = literal_candidate_base(store, *candidate) else {
            return false;
        };
        if base
            .replace(candidate_base)
            .is_some_and(|base| base != candidate_base)
        {
            return false;
        }
    }
    true
}

fn literal_candidate_base(
    store: &CanonicalTypeMapperStore,
    candidate: TypeId,
) -> Option<TypeFlags> {
    let record = store.type_payload(candidate)?;
    if record.flags() == TypeFlags::STRING_LITERAL {
        return Some(TypeFlags::STRING);
    }
    if record.flags() == TypeFlags::NUMBER_LITERAL {
        return Some(TypeFlags::NUMBER);
    }
    if record.flags() == TypeFlags::BIG_INT_LITERAL {
        return Some(TypeFlags::BIG_INT);
    }
    if record.flags() == TypeFlags::BOOLEAN_LITERAL {
        return Some(TypeFlags::BOOLEAN);
    }
    if record.flags() != TypeFlags::UNION {
        return None;
    }
    let TypeData::Union(union) = record.data() else {
        return None;
    };
    let mut base = TypeFlags::NONE;
    for constituent in &union.union.types {
        base |= literal_candidate_base(store, *constituent)?;
    }
    (base != TypeFlags::NONE).then_some(base)
}

/// Proves that a type is inside the first explicit/inferred argument domain.
pub(super) fn validate_inference_leaf(
    store: &CanonicalTypeMapperStore,
    candidate: TypeId,
) -> Result<(), NakedTypeInferenceError> {
    validate_inference_candidate(store, candidate, true)
}

fn validate_inference_candidate(
    store: &CanonicalTypeMapperStore,
    candidate: TypeId,
    allow_declared_object: bool,
) -> Result<(), NakedTypeInferenceError> {
    let record = store
        .type_payload(candidate)
        .ok_or(NakedTypeInferenceError::InvalidCandidate(candidate))?;
    if record
        .object_flags()
        .intersects(ObjectFlags::REQUIRES_WIDENING)
    {
        return Err(NakedTypeInferenceError::RequiresWidening(candidate));
    }
    match validate_resolved_declared_property_object(store, candidate) {
        DeclaredPropertyObjectValidation::Valid(_) if allow_declared_object => return Ok(()),
        DeclaredPropertyObjectValidation::Valid(_) => {
            return Err(NakedTypeInferenceError::UnsupportedCandidate(candidate));
        }
        DeclaredPropertyObjectValidation::Malformed => {
            return Err(NakedTypeInferenceError::MalformedDeclaredPropertyObject(
                candidate,
            ));
        }
        DeclaredPropertyObjectValidation::NotDeclared => {}
    }
    match store.validate_union_constituent(candidate) {
        Ok(()) => {}
        Err(LiteralTypeCacheError::UnsupportedUnionConstituent(_)) => {
            return Err(NakedTypeInferenceError::UnsupportedCandidate(candidate));
        }
        Err(error) => {
            return Err(NakedTypeInferenceError::InvalidCanonicalCandidate { candidate, error });
        }
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
                validate_inference_candidate(store, *constituent, false)?;
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
