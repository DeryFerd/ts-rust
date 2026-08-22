//! Dependency-closed inference for a naked type parameter.
//!
//! This is the first exact branch of pinned `inferTypes` used by generic call
//! resolution. When the target is the inference context's type parameter,
//! upstream records the source type itself as a covariant candidate. The
//! bounded Rust branch accepts primitive, literal, unique-symbol, anonymous
//! primitive-union, and exact resolved nongeneric declared-property-object
//! candidates, plus canonical Array/ReadonlyArray references when the caller
//! retains the authoritative global targets. Declared objects are admitted
//! only as the root candidate, not recursively inside a union. The branch
//! preserves candidates that do not require widening, including fresh
//! literals. Widening sentinels remain a typed boundary until the exact final
//! `getWidenedType` step is available.

#![allow(dead_code)] // Installed ahead of the generic-call dispatch consumer.

use std::collections::HashSet;

use super::{
    RelationUnavailable, TypeId,
    array_types::{ArrayTypeError, CanonicalArrayTargets},
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
    InvalidCanonicalArrayCandidate {
        candidate: TypeId,
        error: ArrayTypeError,
    },
    RecursiveArrayCandidate(TypeId),
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
) -> Result<Option<TypeId>, NakedTypeCandidateError> {
    infer_naked_type_parameter_candidates_with_optional_array_targets(
        store,
        candidates,
        treatment,
        None,
        is_strict_subtype,
        is_subtype,
    )
}

pub(super) fn infer_naked_type_parameter_candidates_with_array_targets(
    store: &mut CanonicalTypeMapperStore,
    candidates: &[TypeId],
    treatment: InferenceLiteralTreatment,
    array_targets: CanonicalArrayTargets,
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
) -> Result<Option<TypeId>, NakedTypeCandidateError> {
    infer_naked_type_parameter_candidates_with_optional_array_targets(
        store,
        candidates,
        treatment,
        Some(array_targets),
        is_strict_subtype,
        is_subtype,
    )
}

fn infer_naked_type_parameter_candidates_with_optional_array_targets(
    store: &mut CanonicalTypeMapperStore,
    candidates: &[TypeId],
    treatment: InferenceLiteralTreatment,
    array_targets: Option<CanonicalArrayTargets>,
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
        validate_inference_leaf_with_optional_array_targets(store, *candidate, array_targets)?;
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
        single_common_supertype(store, &primary, &mut is_strict_subtype, &mut is_subtype)?
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
    let record =
        store
            .type_payload(candidate)
            .ok_or(LiteralTypeCacheError::UnsupportedUnionConstituent(
                candidate,
            ))?;
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
    validate_inference_leaf_with_optional_array_targets(store, candidate, None)
}

pub(super) fn validate_inference_leaf_with_array_targets(
    store: &CanonicalTypeMapperStore,
    candidate: TypeId,
    array_targets: CanonicalArrayTargets,
) -> Result<(), NakedTypeInferenceError> {
    validate_inference_leaf_with_optional_array_targets(store, candidate, Some(array_targets))
}

fn validate_inference_leaf_with_optional_array_targets(
    store: &CanonicalTypeMapperStore,
    candidate: TypeId,
    array_targets: Option<CanonicalArrayTargets>,
) -> Result<(), NakedTypeInferenceError> {
    validate_inference_candidate(store, candidate, true, array_targets, &mut HashSet::new())
}

fn validate_inference_candidate(
    store: &CanonicalTypeMapperStore,
    candidate: TypeId,
    allow_declared_object: bool,
    array_targets: Option<CanonicalArrayTargets>,
    active_arrays: &mut HashSet<TypeId>,
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
    if let Some(array_targets) = array_targets {
        match store.canonical_array_reference_with_targets(array_targets, candidate) {
            Ok(Some(reference)) => {
                if !active_arrays.insert(candidate) {
                    return Err(NakedTypeInferenceError::RecursiveArrayCandidate(candidate));
                }
                let result = validate_inference_candidate(
                    store,
                    reference.element_type,
                    true,
                    Some(array_targets),
                    active_arrays,
                );
                active_arrays.remove(&candidate);
                return result;
            }
            Ok(None) => {}
            Err(error) => {
                return Err(NakedTypeInferenceError::InvalidCanonicalArrayCandidate {
                    candidate,
                    error,
                });
            }
        }
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
                validate_inference_candidate(store, *constituent, false, None, active_arrays)?;
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
    use ts_ast::{FileId, NodeRef, SyntaxKind};
    use ts_binder::{
        CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
        EscapedName, SymbolData, SymbolFlags,
    };
    use ts_jsnum::Number;
    use ts_parser::parse_source_file;

    use super::*;
    use crate::semantic::{
        CanonicalCheckerContext, CanonicalCheckerOptions, IntrinsicBootstrapOptions, SemanticStore,
        bootstrap::UnionReduction, mapper::TypeMapper, type_records::TypeRecord,
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

    fn infer_preserved(
        store: &mut CanonicalTypeMapperStore,
        candidates: &[TypeId],
    ) -> Result<Option<TypeId>, NakedTypeCandidateError> {
        infer_naked_type_parameter_candidates(
            store,
            candidates,
            InferenceLiteralTreatment::Preserve,
            CanonicalTypeMapperStore::is_type_strict_subtype_of,
            CanonicalTypeMapperStore::is_type_subtype_of,
        )
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
    fn candidate_buckets_union_same_base_literals_and_widen_non_returned_literals() {
        let mut store = initialized_store();
        let a = store.regular_string_literal_type("a".into()).unwrap();
        let b = store.regular_string_literal_type("b".into()).unwrap();
        let fresh_a = store.fresh_type_of_literal_type(a).unwrap();
        let fresh_b = store.fresh_type_of_literal_type(b).unwrap();

        let union = infer_naked_type_parameter_candidates(
            &mut store,
            &[fresh_a, fresh_b],
            InferenceLiteralTreatment::Preserve,
            CanonicalTypeMapperStore::is_type_strict_subtype_of,
            CanonicalTypeMapperStore::is_type_subtype_of,
        )
        .unwrap()
        .unwrap();
        let TypeData::Union(data) = store.type_payload(union).unwrap().data() else {
            panic!("distinct same-base literals must infer a union");
        };
        assert_eq!(data.union.types.len(), 2);

        let string = store.intrinsic_bootstrap().unwrap().string_type;
        assert_eq!(
            infer_naked_type_parameter_candidates(
                &mut store,
                &[fresh_a, fresh_b],
                InferenceLiteralTreatment::Widen,
                CanonicalTypeMapperStore::is_type_strict_subtype_of,
                CanonicalTypeMapperStore::is_type_subtype_of,
            ),
            Ok(Some(string))
        );
    }

    #[test]
    fn common_supertype_uses_strict_subtyping_and_flattens_literal_unions() {
        let mut store = initialized_store();
        let (any, unknown, string, boolean) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (
                bootstrap.any_type,
                bootstrap.unknown_type,
                bootstrap.string_type,
                bootstrap.boolean_type,
            )
        };
        let a = store.regular_string_literal_type("a".into()).unwrap();
        for candidates in [[any, a], [a, any]] {
            assert_eq!(infer_preserved(&mut store, &candidates), Ok(Some(any)));
        }
        for candidates in [[unknown, a], [a, unknown]] {
            assert_eq!(infer_preserved(&mut store, &candidates), Ok(Some(unknown)));
        }
        for candidates in [[string, a], [a, string]] {
            assert_eq!(infer_preserved(&mut store, &candidates), Ok(Some(string)));
        }

        let one = store.regular_number_literal_type(Number::new(1.0)).unwrap();
        let two = store.regular_number_literal_type(Number::new(2.0)).unwrap();
        let three = store.regular_number_literal_type(Number::new(3.0)).unwrap();
        let one_or_two = store.literal_union_type(&[one, two], None).unwrap();
        for candidates in [[one_or_two, three], [three, one_or_two]] {
            let result = infer_preserved(&mut store, &candidates).unwrap().unwrap();
            let TypeData::Union(data) = store.type_payload(result).unwrap().data() else {
                panic!("homogeneous literal-union buckets must remain a union");
            };
            assert_eq!(data.union.types.len(), 3);
            assert!(data.union.types.contains(&one));
            assert!(data.union.types.contains(&two));
            assert!(data.union.types.contains(&three));
        }

        let b = store.regular_string_literal_type("b".into()).unwrap();
        let one_or_a = store.literal_union_type(&[one, a], None).unwrap();
        let two_or_b = store.literal_union_type(&[two, b], None).unwrap();
        let mixed = infer_preserved(&mut store, &[one_or_a, two_or_b])
            .unwrap()
            .unwrap();
        let TypeData::Union(data) = store.type_payload(mixed).unwrap().data() else {
            panic!("matching number|string literal-base masks must combine");
        };
        assert_eq!(data.union.types.len(), 4);
        for member in [one, a, two, b] {
            assert!(data.union.types.contains(&member));
        }

        let true_ = store.intrinsic_bootstrap().unwrap().true_type;
        let false_ = store.intrinsic_bootstrap().unwrap().false_type;
        let mut fresh_boolean = None;
        for candidates in [[true_, false_], [false_, true_]] {
            let result = infer_preserved(&mut store, &candidates).unwrap().unwrap();
            assert_eq!(fresh_boolean.get_or_insert(result), &result);
            assert_ne!(result, boolean);
            let record = store.type_payload(result).unwrap();
            assert_eq!(record.flags(), TypeFlags::UNION | TypeFlags::BOOLEAN);
            let TypeData::Union(data) = record.data() else {
                panic!("fresh true and false retain a distinct boolean union");
            };
            assert!(data.union.types.contains(&true_));
            assert!(data.union.types.contains(&false_));
        }
    }

    #[test]
    fn strict_null_common_supertype_removes_then_restores_nullable_members() {
        let mut store = initialized_store_with(true);
        let (null, undefined) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (bootstrap.null_type, bootstrap.undefined_type)
        };
        let a = store.regular_string_literal_type("a".into()).unwrap();
        for nullable in [null, undefined] {
            for candidates in [[nullable, a], [a, nullable]] {
                let result = infer_preserved(&mut store, &candidates).unwrap().unwrap();
                let TypeData::Union(data) = store.type_payload(result).unwrap().data() else {
                    panic!("strict-null inference must restore the nullable member");
                };
                assert_eq!(data.union.types.len(), 2);
                assert!(data.union.types.contains(&a));
                assert!(data.union.types.contains(&nullable));
            }
        }
    }

    #[test]
    fn declared_object_common_supertype_is_structural_then_left_biased() {
        let parsed = parse_source_file(concat!(
            "type Narrow = { a: string }; ",
            "type Wide = { a: string; b: number }; ",
            "type Unrelated = { c: number };",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(1_060);
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source("\"/project/inference-objects.ts\""),
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
        context.check_source_file(file).unwrap();
        let mut type_literals = parsed
            .arena
            .iter()
            .filter_map(|(node, record)| {
                (record.kind == SyntaxKind::TypeLiteral).then_some((
                    record.range.start,
                    NodeRef::new(parsed.arena.id(), file, node),
                ))
            })
            .collect::<Vec<_>>();
        type_literals.sort_by_key(|(start, _)| *start);
        let [narrow, wide, unrelated] = type_literals
            .iter()
            .map(|(_, node)| {
                context
                    .store()
                    .type_node_links(*node)
                    .and_then(|links| links.resolved_type)
                    .expect("source checking must publish each declared type literal")
            })
            .collect::<Vec<_>>()
            .try_into()
            .unwrap();
        let store = context.store_mut_for_test();

        for candidates in [[narrow, wide], [wide, narrow]] {
            assert_eq!(
                infer_preserved(store, &candidates),
                Ok(Some(narrow)),
                "the broader structural base wins regardless of order"
            );
        }
        assert_eq!(
            infer_preserved(store, &[narrow, unrelated]),
            Ok(Some(narrow))
        );
        assert_eq!(
            infer_preserved(store, &[unrelated, narrow]),
            Ok(Some(unrelated)),
            "unrelated candidates remain left-biased for later applicability"
        );
    }

    #[test]
    fn primitive_constraints_regularize_fresh_candidates_without_widening_them() {
        let mut store = initialized_store();
        let regular = store.regular_number_literal_type(Number::new(1.0)).unwrap();
        let fresh = store.fresh_type_of_literal_type(regular).unwrap();

        assert_eq!(
            infer_naked_type_parameter_candidates(
                &mut store,
                &[fresh],
                InferenceLiteralTreatment::Regularize,
                CanonicalTypeMapperStore::is_type_strict_subtype_of,
                CanonicalTypeMapperStore::is_type_subtype_of,
            ),
            Ok(Some(regular))
        );
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
