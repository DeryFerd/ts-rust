//! Dependency-closed inference for a naked type parameter.
//!
//! This is the first exact branch of pinned `inferTypes` used by generic call
//! resolution. When the target is the inference context's type parameter,
//! upstream records the source type itself as a covariant or authenticated
//! contravariant candidate. The bounded Rust branch accepts primitive, literal,
//! unique-symbol, anonymous primitive-union, and exact resolved nongeneric
//! declared-property-object candidates, validated derived object literals,
//! authenticated template-literal patterns, fixed tuples, and
//! canonical Array/ReadonlyArray references when the caller retains the
//! authoritative global targets.
//! Declared objects and tuples are admitted only as root candidates or nested
//! array/tuple elements, not as union constituents. Derived object literals
//! are also admitted as union constituents. The branch preserves
//! candidates that do not require widening, including fresh literals.
//! Authenticated internal placeholders are skipped so binding patterns cannot
//! become the only source of a public type argument.
//! Widening sentinels remain a typed boundary until the exact final
//! `getWidenedType` step is available.

#![allow(dead_code)] // Installed ahead of the generic-call dispatch consumer.

use std::collections::HashSet;

use super::{
    RelationUnavailable, TypeId,
    array_types::{ArrayTypeError, CanonicalArrayTargets},
    bootstrap::LiteralTypeCacheError,
    derived_types::DerivedObjectLiteralValidation,
    instantiate::canonical_anonymous_union,
    mapper::CanonicalTypeMapperStore,
    object_members::{
        DeclaredPropertyObjectValidation, validate_resolved_declared_property_object,
    },
    signatures::ElementFlags,
    tuple_types::TupleTypeError,
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
    InvalidCanonicalTupleCandidate {
        candidate: TypeId,
        error: TupleTypeError,
    },
    RecursiveArrayCandidate(TypeId),
    RecursiveTupleCandidate(TypeId),
    MalformedDeclaredPropertyObject(TypeId),
    UnsupportedCandidate(TypeId),
    NonInferrableCandidate(TypeId),
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

/// Recognizes authenticated internal placeholders that upstream inference skips.
///
/// Array and tuple markers are accepted only when their canonical caches prove
/// that the non-inferrable flag was propagated from an exact nested marker.
pub(super) fn is_non_inferrable_inference_source(
    store: &CanonicalTypeMapperStore,
    candidate: TypeId,
    array_targets: Option<CanonicalArrayTargets>,
) -> Result<bool, NakedTypeInferenceError> {
    non_inferrable_inference_source_worker(store, candidate, array_targets, &mut HashSet::new())
}

#[allow(clippy::too_many_lines)] // Authenticate sentinels and their propagated containers together.
fn non_inferrable_inference_source_worker(
    store: &CanonicalTypeMapperStore,
    candidate: TypeId,
    array_targets: Option<CanonicalArrayTargets>,
    active_candidates: &mut HashSet<TypeId>,
) -> Result<bool, NakedTypeInferenceError> {
    let record = store
        .type_payload(candidate)
        .ok_or(NakedTypeInferenceError::InvalidCandidate(candidate))?;
    let bootstrap = store
        .intrinsic_bootstrap()
        .ok_or(NakedTypeInferenceError::InvalidCandidate(candidate))?;
    let intrinsic_marker = if candidate == bootstrap.auto_type {
        Some((TypeFlags::ANY, ObjectFlags::NON_INFERRABLE_TYPE))
    } else if candidate == bootstrap.silent_never_type {
        Some((TypeFlags::NEVER, ObjectFlags::NON_INFERRABLE_TYPE))
    } else if candidate == bootstrap.non_inferrable_any_type {
        Some((TypeFlags::ANY, ObjectFlags::CONTAINS_WIDENING_TYPE))
    } else {
        None
    };
    if let Some((flags, object_flags)) = intrinsic_marker {
        return if record.flags() == flags
            && record.object_flags() == object_flags
            && record.symbol().is_none()
            && record.alias().is_none()
            && matches!(record.data(), TypeData::Intrinsic(_))
        {
            Ok(true)
        } else {
            Err(NakedTypeInferenceError::InvalidCandidate(candidate))
        };
    }
    if candidate == bootstrap.any_function_type {
        return if record.flags() == TypeFlags::OBJECT
            && record.object_flags()
                == ObjectFlags::ANONYMOUS
                    | ObjectFlags::MEMBERS_RESOLVED
                    | ObjectFlags::NON_INFERRABLE_TYPE
            && record.symbol().is_none()
            && record.alias().is_none()
            && matches!(
                record.data(),
                TypeData::Object(object)
                    if object.target.is_none()
                        && object.mapper.is_none()
                        && object.structured.members.is_none()
                        && object.structured.properties.is_none()
                        && object.structured.signatures.is_none()
                        && object.structured.call_signature_count == 0
                        && object.structured.index_infos.is_none()
            ) {
            Ok(true)
        } else {
            Err(NakedTypeInferenceError::InvalidCandidate(candidate))
        };
    }
    if !record
        .object_flags()
        .contains(ObjectFlags::NON_INFERRABLE_TYPE)
    {
        return Ok(false);
    }

    if let Some(targets) = array_targets {
        match store.canonical_array_reference_with_targets(targets, candidate) {
            Ok(Some(reference)) => {
                if !active_candidates.insert(candidate) {
                    return Err(NakedTypeInferenceError::RecursiveArrayCandidate(candidate));
                }
                let blocked = non_inferrable_inference_source_worker(
                    store,
                    reference.element_type,
                    Some(targets),
                    active_candidates,
                );
                active_candidates.remove(&candidate);
                return if blocked? {
                    Ok(true)
                } else {
                    Err(NakedTypeInferenceError::InvalidCanonicalArrayCandidate {
                        candidate,
                        error: ArrayTypeError::InvalidReference(candidate),
                    })
                };
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

    match store.canonical_tuple_shape(candidate) {
        Ok(Some(tuple)) => {
            if !active_candidates.insert(candidate) {
                return Err(NakedTypeInferenceError::RecursiveTupleCandidate(candidate));
            }
            let mut blocked = false;
            let result = tuple.element_types().iter().try_for_each(|element| {
                blocked |= non_inferrable_inference_source_worker(
                    store,
                    *element,
                    array_targets,
                    active_candidates,
                )?;
                Ok::<_, NakedTypeInferenceError>(())
            });
            active_candidates.remove(&candidate);
            result?;
            if blocked {
                Ok(true)
            } else {
                Err(NakedTypeInferenceError::InvalidCanonicalTupleCandidate {
                    candidate,
                    error: TupleTypeError::InvalidInstantiationCache {
                        target: tuple.target(),
                        instance: candidate,
                    },
                })
            }
        }
        Ok(None) => Err(NakedTypeInferenceError::UnsupportedCandidate(candidate)),
        Err(error) => {
            Err(NakedTypeInferenceError::InvalidCanonicalTupleCandidate { candidate, error })
        }
    }
}

/// Infers one naked type parameter from one already-typed argument.
///
/// The return is the exact candidate identity only after proving that pinned
/// `getCovariantInference` would not take its final widening path.
pub(super) fn infer_naked_type_parameter(
    store: &CanonicalTypeMapperStore,
    candidate: TypeId,
) -> Result<TypeId, NakedTypeInferenceError> {
    if is_non_inferrable_inference_source(store, candidate, None)? {
        return Err(NakedTypeInferenceError::NonInferrableCandidate(candidate));
    }
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

/// Combines exact covariant and contravariant candidates for one type parameter.
///
/// Pinned TypeScript inference prefers a usable covariant result when it fits
/// a contravariant candidate. Covariant `never` and `any` instead yield to an
/// available contravariant result, while a sole `never` candidate remains exact.
#[allow(clippy::too_many_arguments)] // Keep relation capabilities and array provenance explicit.
pub(super) fn infer_naked_type_parameter_variance_candidates(
    store: &mut CanonicalTypeMapperStore,
    covariant: &[TypeId],
    contravariant: &[TypeId],
    treatment: InferenceLiteralTreatment,
    array_targets: Option<CanonicalArrayTargets>,
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
) -> Result<Option<TypeId>, NakedTypeCandidateError> {
    for candidate in covariant.iter().chain(contravariant) {
        if is_non_inferrable_inference_source(store, *candidate, array_targets)? {
            continue;
        }
        validate_inference_leaf_with_optional_array_targets(store, *candidate, array_targets)?;
    }

    let covariant = infer_naked_type_parameter_candidates_with_optional_array_targets(
        store,
        covariant,
        treatment,
        array_targets,
        |store, source, target| is_strict_subtype(store, source, target),
        |store, source, target| is_subtype(store, source, target),
    )?;

    let mut contravariant_result = None;
    for candidate in contravariant {
        if is_non_inferrable_inference_source(store, *candidate, array_targets)? {
            continue;
        }
        if contravariant_result.is_none_or(|current| current == *candidate) {
            contravariant_result = Some(*candidate);
            continue;
        }
        let current = contravariant_result.expect("the first candidate initialized the result");
        if is_subtype(store, *candidate, current)? {
            contravariant_result = Some(*candidate);
        }
    }

    match (covariant, contravariant_result) {
        (None, None) => Ok(None),
        (Some(candidate), None) | (None, Some(candidate)) => Ok(Some(candidate)),
        (Some(covariant), Some(contravariant_result)) => {
            let flags = store
                .type_payload(covariant)
                .ok_or(NakedTypeInferenceError::InvalidCandidate(covariant))?
                .flags();
            if flags.intersects(TypeFlags::NEVER | TypeFlags::ANY) {
                return Ok(Some(contravariant_result));
            }
            for candidate in contravariant {
                if is_non_inferrable_inference_source(store, *candidate, array_targets)? {
                    continue;
                }
                if is_assignable(store, covariant, *candidate)? {
                    return Ok(Some(covariant));
                }
            }
            Ok(Some(contravariant_result))
        }
    }
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
        if is_non_inferrable_inference_source(store, *candidate, array_targets)? {
            continue;
        }
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
    active_candidates: &mut HashSet<TypeId>,
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
    if let TypeData::TemplateLiteral(template) = record.data() {
        if record.flags() != TypeFlags::TEMPLATE_LITERAL
            || record.object_flags() != ObjectFlags::NONE
            || record.symbol().is_some()
            || record.alias().is_some()
            || template.types.is_empty()
            || template.texts.len() != template.types.len() + 1
            || store
                .cached_resolved_template_literal_type(&template.texts, &template.types)
                .ok()
                .flatten()
                != Some(candidate)
        {
            return Err(NakedTypeInferenceError::InvalidCandidate(candidate));
        }
        return Ok(());
    }
    if let Some(array_targets) = array_targets {
        match store.canonical_array_reference_with_targets(array_targets, candidate) {
            Ok(Some(reference)) => {
                if !active_candidates.insert(candidate) {
                    return Err(NakedTypeInferenceError::RecursiveArrayCandidate(candidate));
                }
                let result = validate_inference_candidate(
                    store,
                    reference.element_type,
                    true,
                    Some(array_targets),
                    active_candidates,
                );
                active_candidates.remove(&candidate);
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
    match store.canonical_tuple_shape(candidate) {
        Ok(Some(tuple)) => {
            if !allow_declared_object || tuple.combined_flags().intersects(ElementFlags::VARIABLE) {
                return Err(NakedTypeInferenceError::UnsupportedCandidate(candidate));
            }
            if !active_candidates.insert(candidate) {
                return Err(NakedTypeInferenceError::RecursiveTupleCandidate(candidate));
            }
            let result = tuple.element_types().iter().try_for_each(|element| {
                validate_inference_candidate(
                    store,
                    *element,
                    true,
                    array_targets,
                    active_candidates,
                )
            });
            active_candidates.remove(&candidate);
            return result;
        }
        Ok(None) => {}
        Err(error) => {
            return Err(NakedTypeInferenceError::InvalidCanonicalTupleCandidate {
                candidate,
                error,
            });
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
        TypeData::Object(_)
            if matches!(
                array_targets.map_or_else(
                    || store.validate_derived_object_literal_for_relation(candidate),
                    |targets| store
                        .validate_derived_object_literal_with_array_targets(candidate, targets),
                ),
                DerivedObjectLiteralValidation::Valid { .. }
            ) =>
        {
            Ok(())
        }
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
                validate_inference_candidate(store, *constituent, false, None, active_candidates)?;
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
        CanonicalCheckerContext, CanonicalCheckerOptions, DeclaredTypeLinks,
        IntrinsicBootstrapOptions, SemanticStore, bootstrap::UnionReduction,
        declared::type_list_key, mapper::TypeMapper, tuple_types::CanonicalTupleTypeRequest,
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

    fn canonical_tuple(
        store: &mut CanonicalTypeMapperStore,
        elements: &[TypeId],
        flags: &[ElementFlags],
        readonly: bool,
    ) -> TypeId {
        let infos = flags
            .iter()
            .copied()
            .map(|flags| store.create_tuple_element_info(flags, None).unwrap())
            .collect::<Vec<_>>();
        store
            .create_canonical_tuple_type(CanonicalTupleTypeRequest::new(elements, &infos, readonly))
            .unwrap()
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

    fn infer_variance(
        store: &mut CanonicalTypeMapperStore,
        covariant: &[TypeId],
        contravariant: &[TypeId],
    ) -> Result<Option<TypeId>, NakedTypeCandidateError> {
        infer_naked_type_parameter_variance_candidates(
            store,
            covariant,
            contravariant,
            InferenceLiteralTreatment::Preserve,
            None,
            CanonicalTypeMapperStore::is_type_assignable_to,
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
    fn naked_inference_accepts_canonical_templates_and_rejects_duplicate_patterns() {
        let mut store = initialized_store();
        let string = store.intrinsic_bootstrap().unwrap().string_type;
        let texts = ["prefix-".to_owned(), String::new()];
        let template = store.get_template_literal_type(&texts, &[string]).unwrap();
        let warm = (store.type_len(), store.mapper_len(), store.signature_len());

        assert_eq!(infer_naked_type_parameter(&store, template), Ok(template));
        assert_eq!(infer_preserved(&mut store, &[template]), Ok(Some(template)));
        assert_eq!(
            (store.type_len(), store.mapper_len(), store.signature_len(),),
            warm,
        );

        let duplicate = store
            .alloc_template_literal_type(texts.to_vec(), vec![string])
            .unwrap();
        assert_eq!(
            infer_naked_type_parameter(&store, duplicate),
            Err(NakedTypeInferenceError::InvalidCandidate(duplicate)),
        );
    }

    #[test]
    fn internal_placeholder_candidates_are_skipped_without_exposing_private_types() {
        let mut store = initialized_store();
        let (auto, silent_never, placeholder_any, any_function, never, any, string) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (
                bootstrap.auto_type,
                bootstrap.silent_never_type,
                bootstrap.non_inferrable_any_type,
                bootstrap.any_function_type,
                bootstrap.never_type,
                bootstrap.any_type,
                bootstrap.string_type,
            )
        };
        let before = (
            store.type_len(),
            store.mapper_len(),
            store.signature_len(),
            store.intrinsic_bootstrap().unwrap().union_cache_len(),
        );

        for candidate in [auto, silent_never, placeholder_any, any_function] {
            assert_eq!(
                is_non_inferrable_inference_source(&store, candidate, None),
                Ok(true),
            );
            assert_eq!(
                infer_naked_type_parameter(&store, candidate),
                Err(NakedTypeInferenceError::NonInferrableCandidate(candidate)),
            );
            assert_eq!(infer_preserved(&mut store, &[candidate]), Ok(None));
            assert_eq!(
                infer_preserved(&mut store, &[candidate, string]),
                Ok(Some(string)),
            );
            assert_eq!(
                infer_variance(&mut store, &[candidate], &[string]),
                Ok(Some(string)),
            );
            assert_eq!(
                infer_variance(&mut store, &[string], &[candidate]),
                Ok(Some(string)),
            );
        }
        assert_eq!(infer_preserved(&mut store, &[never]), Ok(Some(never)));
        assert_eq!(infer_preserved(&mut store, &[any]), Ok(Some(any)));
        assert_eq!(
            (
                store.type_len(),
                store.mapper_len(),
                store.signature_len(),
                store.intrinsic_bootstrap().unwrap().union_cache_len(),
            ),
            before,
        );
    }

    #[test]
    fn non_inferrable_markers_propagate_through_authenticated_arrays_and_tuples() {
        let mut store = initialized_store();
        let (auto, silent_never, string) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (
                bootstrap.auto_type,
                bootstrap.silent_never_type,
                bootstrap.string_type,
            )
        };
        let targets = CanonicalArrayTargets::for_test(
            canonical_array_target(&mut store, "Array"),
            canonical_array_target(&mut store, "ReadonlyArray"),
        );
        let array = store
            .create_canonical_array_type_with_targets(targets, auto, false)
            .unwrap();
        let readonly = store
            .create_canonical_array_type_with_targets(targets, silent_never, true)
            .unwrap();
        let tuple = canonical_tuple(
            &mut store,
            &[string, auto],
            &[ElementFlags::REQUIRED, ElementFlags::REQUIRED],
            false,
        );
        let before = (
            store.type_len(),
            store.mapper_len(),
            store.signature_len(),
            store.canonical_tuple_target_len(),
        );

        for candidate in [array, readonly, tuple] {
            assert!(
                store
                    .type_payload(candidate)
                    .unwrap()
                    .object_flags()
                    .contains(ObjectFlags::NON_INFERRABLE_TYPE),
            );
            assert_eq!(
                is_non_inferrable_inference_source(&store, candidate, Some(targets)),
                Ok(true),
            );
            assert_eq!(
                infer_naked_type_parameter_candidates_with_array_targets(
                    &mut store,
                    &[candidate],
                    InferenceLiteralTreatment::Preserve,
                    targets,
                    CanonicalTypeMapperStore::is_type_strict_subtype_of,
                    CanonicalTypeMapperStore::is_type_subtype_of,
                ),
                Ok(None),
            );
        }
        assert_eq!(
            (
                store.type_len(),
                store.mapper_len(),
                store.signature_len(),
                store.canonical_tuple_target_len(),
            ),
            before,
        );
    }

    #[test]
    fn forged_non_inferrable_markers_fail_before_candidate_publication() {
        let mut store = initialized_store();
        let forged = store
            .alloc_plain_object_type(
                ObjectFlags::ANONYMOUS | ObjectFlags::NON_INFERRABLE_TYPE,
                None,
            )
            .unwrap();
        let string = store.intrinsic_bootstrap().unwrap().string_type;
        let before = (
            store.type_len(),
            store.mapper_len(),
            store.signature_len(),
            store.intrinsic_bootstrap().unwrap().union_cache_len(),
        );

        assert_eq!(
            is_non_inferrable_inference_source(&store, forged, None),
            Err(NakedTypeInferenceError::UnsupportedCandidate(forged)),
        );
        assert_eq!(
            infer_preserved(&mut store, &[string, forged]),
            Err(NakedTypeCandidateError::Candidate(
                NakedTypeInferenceError::UnsupportedCandidate(forged),
            )),
        );
        assert_eq!(
            (
                store.type_len(),
                store.mapper_len(),
                store.signature_len(),
                store.intrinsic_bootstrap().unwrap().union_cache_len(),
            ),
            before,
        );

        let mut store = initialized_store();
        let string = store.intrinsic_bootstrap().unwrap().string_type;
        let targets = CanonicalArrayTargets::for_test(
            canonical_array_target(&mut store, "Array"),
            canonical_array_target(&mut store, "ReadonlyArray"),
        );
        let array = store
            .create_canonical_array_type_with_targets(targets, string, false)
            .unwrap();
        assert!(store.add_type_object_flags(array, ObjectFlags::NON_INFERRABLE_TYPE));
        let before = (
            store.type_len(),
            store.mapper_len(),
            store.signature_len(),
            store.intrinsic_bootstrap().unwrap().union_cache_len(),
        );
        let expected = NakedTypeInferenceError::InvalidCanonicalArrayCandidate {
            candidate: array,
            error: ArrayTypeError::InvalidReference(array),
        };

        assert_eq!(
            is_non_inferrable_inference_source(&store, array, Some(targets)),
            Err(expected),
        );
        assert_eq!(
            infer_naked_type_parameter_candidates_with_array_targets(
                &mut store,
                &[array],
                InferenceLiteralTreatment::Preserve,
                targets,
                CanonicalTypeMapperStore::is_type_strict_subtype_of,
                CanonicalTypeMapperStore::is_type_subtype_of,
            ),
            Err(NakedTypeCandidateError::Candidate(expected)),
        );
        assert_eq!(
            (
                store.type_len(),
                store.mapper_len(),
                store.signature_len(),
                store.intrinsic_bootstrap().unwrap().union_cache_len(),
            ),
            before,
        );
    }

    #[test]
    fn mixed_variance_prefers_contravariant_types_over_never_and_any() {
        let mut store = initialized_store();
        let (never, any, string) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (
                bootstrap.never_type,
                bootstrap.any_type,
                bootstrap.string_type,
            )
        };
        let before = (
            store.type_len(),
            store.mapper_len(),
            store.signature_len(),
            store.intrinsic_bootstrap().unwrap().union_cache_len(),
        );

        assert_eq!(
            infer_variance(&mut store, &[never], &[string]),
            Ok(Some(string))
        );
        assert_eq!(
            infer_variance(&mut store, &[any], &[string]),
            Ok(Some(string))
        );
        assert_eq!(infer_variance(&mut store, &[never], &[]), Ok(Some(never)));
        assert_eq!(infer_variance(&mut store, &[], &[string]), Ok(Some(string)));
        assert_eq!(
            (
                store.type_len(),
                store.mapper_len(),
                store.signature_len(),
                store.intrinsic_bootstrap().unwrap().union_cache_len(),
            ),
            before,
        );
    }

    #[test]
    fn mixed_variance_keeps_compatible_covariance_and_selects_common_subtypes() {
        let mut store = initialized_store();
        let (string, number) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (bootstrap.string_type, bootstrap.number_type)
        };
        let literal = store.regular_string_literal_type("value".into()).unwrap();

        assert_eq!(
            infer_variance(&mut store, &[literal], &[string]),
            Ok(Some(literal)),
        );
        assert_eq!(
            infer_variance(&mut store, &[number], &[string]),
            Ok(Some(string)),
        );
        for candidates in [[string, literal], [literal, string]] {
            assert_eq!(
                infer_variance(&mut store, &[], &candidates),
                Ok(Some(literal)),
            );
        }
    }

    #[test]
    fn mixed_variance_rejects_invalid_candidates_before_union_publication() {
        let mut store = initialized_store();
        let first = store.regular_string_literal_type("first".into()).unwrap();
        let second = store.regular_string_literal_type("second".into()).unwrap();
        let invalid = store
            .alloc_plain_object_type(ObjectFlags::ANONYMOUS, None)
            .unwrap();
        let before = (
            store.type_len(),
            store.mapper_len(),
            store.signature_len(),
            store.intrinsic_bootstrap().unwrap().union_cache_len(),
        );

        assert_eq!(
            infer_variance(&mut store, &[first, second], &[invalid]),
            Err(NakedTypeCandidateError::Candidate(
                NakedTypeInferenceError::UnsupportedCandidate(invalid),
            )),
        );
        assert_eq!(
            (
                store.type_len(),
                store.mapper_len(),
                store.signature_len(),
                store.intrinsic_bootstrap().unwrap().union_cache_len(),
            ),
            before,
        );
    }

    #[test]
    fn fixed_tuple_candidates_preserve_nested_and_readonly_identities_without_writes() {
        let mut store = initialized_store_with(true);
        let (string, number, undefined) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (
                bootstrap.string_type,
                bootstrap.number_type,
                bootstrap.undefined_type,
            )
        };
        let optional_number = store
            .literal_union_type(&[number, undefined], None)
            .unwrap();
        let mutable = canonical_tuple(
            &mut store,
            &[string, number],
            &[ElementFlags::REQUIRED, ElementFlags::REQUIRED],
            false,
        );
        let readonly = canonical_tuple(
            &mut store,
            &[string, number],
            &[ElementFlags::REQUIRED, ElementFlags::REQUIRED],
            true,
        );
        let optional = canonical_tuple(
            &mut store,
            &[string, optional_number],
            &[ElementFlags::REQUIRED, ElementFlags::OPTIONAL],
            false,
        );
        let nested = canonical_tuple(
            &mut store,
            &[mutable, readonly],
            &[ElementFlags::REQUIRED, ElementFlags::REQUIRED],
            false,
        );
        let empty = canonical_tuple(&mut store, &[], &[], false);
        let before = (
            store.type_len(),
            store.mapper_len(),
            store.signature_len(),
            store.canonical_tuple_target_len(),
            store.intrinsic_bootstrap().unwrap().union_cache_len(),
        );

        for candidate in [mutable, readonly, optional, nested, empty] {
            assert_eq!(infer_naked_type_parameter(&store, candidate), Ok(candidate));
            assert_eq!(
                infer_preserved(&mut store, &[candidate]),
                Ok(Some(candidate))
            );
            assert_eq!(
                infer_preserved(&mut store, &[candidate, candidate]),
                Ok(Some(candidate))
            );
        }
        assert!(
            !store
                .canonical_tuple_shape(mutable)
                .unwrap()
                .unwrap()
                .is_readonly()
        );
        assert!(
            store
                .canonical_tuple_shape(readonly)
                .unwrap()
                .unwrap()
                .is_readonly()
        );
        assert_eq!(
            (
                store.type_len(),
                store.mapper_len(),
                store.signature_len(),
                store.canonical_tuple_target_len(),
                store.intrinsic_bootstrap().unwrap().union_cache_len(),
            ),
            before
        );
    }

    #[test]
    fn fixed_tuple_elements_are_admitted_inside_authenticated_arrays() {
        let mut store = initialized_store();
        let (string, number) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (bootstrap.string_type, bootstrap.number_type)
        };
        let tuple = canonical_tuple(
            &mut store,
            &[string, number],
            &[ElementFlags::REQUIRED, ElementFlags::REQUIRED],
            true,
        );
        let targets = CanonicalArrayTargets::for_test(
            canonical_array_target(&mut store, "Array"),
            canonical_array_target(&mut store, "ReadonlyArray"),
        );
        let array = store
            .create_canonical_array_type_with_targets(targets, tuple, false)
            .unwrap();
        let before = (
            store.type_len(),
            store.mapper_len(),
            store.signature_len(),
            store.canonical_tuple_target_len(),
        );

        assert_eq!(
            validate_inference_leaf_with_array_targets(&store, array, targets),
            Ok(())
        );
        assert_eq!(
            infer_naked_type_parameter_candidates_with_array_targets(
                &mut store,
                &[array],
                InferenceLiteralTreatment::Preserve,
                targets,
                CanonicalTypeMapperStore::is_type_strict_subtype_of,
                CanonicalTypeMapperStore::is_type_subtype_of,
            ),
            Ok(Some(array))
        );
        assert_eq!(
            (
                store.type_len(),
                store.mapper_len(),
                store.signature_len(),
                store.canonical_tuple_target_len(),
            ),
            before
        );
    }

    #[test]
    fn malformed_variable_and_unsupported_tuple_candidates_fail_closed() {
        let mut store = initialized_store();
        let (string, number) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (bootstrap.string_type, bootstrap.number_type)
        };
        let rest = canonical_tuple(
            &mut store,
            &[string, number],
            &[ElementFlags::REQUIRED, ElementFlags::REST],
            false,
        );
        let parameter = store.alloc_type_parameter(None).unwrap();
        let variadic = canonical_tuple(
            &mut store,
            &[string, parameter],
            &[ElementFlags::REQUIRED, ElementFlags::VARIADIC],
            false,
        );
        for candidate in [rest, variadic] {
            assert_eq!(
                infer_naked_type_parameter(&store, candidate),
                Err(NakedTypeInferenceError::UnsupportedCandidate(candidate))
            );
        }

        let opaque = store
            .alloc_plain_object_type(ObjectFlags::ANONYMOUS, None)
            .unwrap();
        let opaque_tuple = canonical_tuple(&mut store, &[opaque], &[ElementFlags::REQUIRED], false);
        assert_eq!(
            infer_naked_type_parameter(&store, opaque_tuple),
            Err(NakedTypeInferenceError::UnsupportedCandidate(opaque))
        );

        let tuple = canonical_tuple(&mut store, &[string], &[ElementFlags::REQUIRED], false);
        let target = store
            .canonical_tuple_shape(tuple)
            .unwrap()
            .unwrap()
            .target();
        let this_type = match store.type_payload(target).unwrap().data() {
            TypeData::Tuple(tuple) => tuple.interface.this_type.unwrap(),
            _ => unreachable!("a validated tuple has a canonical tuple target"),
        };
        assert!(store.set_resolved_base_constraint(this_type, Some(number)));
        let before = (store.type_len(), store.canonical_tuple_target_len());
        assert_eq!(
            infer_naked_type_parameter(&store, tuple),
            Err(NakedTypeInferenceError::InvalidCanonicalTupleCandidate {
                candidate: tuple,
                error: TupleTypeError::InvalidTargetCache(target),
            })
        );
        assert_eq!(
            (store.type_len(), store.canonical_tuple_target_len()),
            before
        );
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
    #[allow(clippy::too_many_lines)] // One source graph checks object and array candidates.
    fn derived_object_candidates_keep_their_types_and_complete_union() {
        let source = parse_source_file(concat!(
            "declare const log: any; ",
            "const broad = { log }; ",
            "const text = { log: 'value' }; ",
            "const highlighted = { log: 'value', highlighted: true }; ",
            "const numeric = { log: 1 };",
        ));
        assert!(source.diagnostics.is_empty());
        let file = FileId::new(163_001);
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &source.arena,
                source.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source("\"/project/derived-inference.ts\""),
                    CanonicalSourceLanguage::TypeScript,
                    false,
                    CanonicalModuleState::Script,
                ),
            )
            .unwrap();
        binder
            .bind_typescript_declaration_slice(&source.arena, file)
            .unwrap();
        let mut context = CanonicalCheckerContext::new(
            binder.finish(),
            [(file, &source.arena)].into_iter().collect(),
            CanonicalCheckerOptions {
                intrinsic: IntrinsicBootstrapOptions {
                    strict_null_checks: true,
                    ..IntrinsicBootstrapOptions::default()
                },
                ..CanonicalCheckerOptions::default()
            },
        )
        .unwrap();
        context.check_source_file(file).unwrap();
        assert!(context.diagnostics().is_empty());
        let mut object_nodes = source
            .arena
            .iter()
            .filter_map(|(node, record)| {
                (record.kind == SyntaxKind::ObjectLiteralExpression).then_some((
                    record.range.start,
                    NodeRef::new(source.arena.id(), file, node),
                ))
            })
            .collect::<Vec<_>>();
        object_nodes.sort_by_key(|(start, _)| *start);
        let originals = object_nodes
            .iter()
            .map(|(_, node)| {
                context
                    .store()
                    .type_node_links(*node)
                    .unwrap()
                    .resolved_type
                    .unwrap()
            })
            .collect::<Vec<_>>();
        let store = context.store_mut_for_test();
        let branch_source = store
            .literal_union_type(&[originals[2], originals[0]], None)
            .unwrap();
        let branches = store.get_widened_type(branch_source).unwrap();
        assert_eq!(infer_naked_type_parameter(store, branches), Ok(branches));
        let TypeData::Union(branch_union) = store.type_payload(branches).unwrap().data() else {
            panic!("the first argument must retain both object branches")
        };
        assert_eq!(branch_union.union.types.len(), 2);
        assert!(branch_union.union.types.iter().any(|member| {
            store
                .type_payload(*member)
                .and_then(|record| record.data().structured())
                .and_then(|record| record.members)
                .and_then(|members| store.symbol_table(members))
                .and_then(|members| members.get_source("highlighted"))
                .and_then(|property| store.symbol(property))
                .is_some_and(|property| property.flags().contains(SymbolFlags::OPTIONAL))
        }));
        let derived = originals
            .into_iter()
            .map(|original| store.get_widened_type(original).unwrap())
            .collect::<Vec<_>>();
        let [broad, text, highlighted, numeric] = derived.as_slice() else {
            panic!("expected the four real object literal types")
        };
        for &candidate in &derived {
            assert!(matches!(
                store.validate_derived_object_literal_for_relation(candidate),
                DerivedObjectLiteralValidation::Valid { .. }
            ));
            assert_eq!(infer_naked_type_parameter(store, candidate), Ok(candidate));
        }
        assert_ne!(broad, text);
        let constituents = [*text, *highlighted, *numeric];
        let union = store.literal_union_type(&constituents, None).unwrap();
        assert_eq!(infer_naked_type_parameter(store, union), Ok(union));
        let TypeData::Union(data) = store.type_payload(union).unwrap().data() else {
            panic!("the object candidates must retain their complete union")
        };
        assert_eq!(data.union.types.len(), constituents.len());
        for candidate in constituents {
            assert!(data.union.types.contains(&candidate));
        }
        let targets = CanonicalArrayTargets::for_test(
            canonical_array_target(store, "Array"),
            canonical_array_target(store, "ReadonlyArray"),
        );
        for element in [*broad, branches, union] {
            let array = store
                .create_canonical_array_type_with_targets(targets, element, false)
                .unwrap();
            assert_eq!(
                validate_inference_leaf_with_array_targets(store, array, targets),
                Ok(())
            );
            assert_eq!(
                infer_naked_type_parameter_candidates_with_array_targets(
                    store,
                    &[array],
                    InferenceLiteralTreatment::Widen,
                    targets,
                    CanonicalTypeMapperStore::is_type_strict_subtype_of,
                    CanonicalTypeMapperStore::is_type_subtype_of,
                ),
                Ok(Some(array)),
            );
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
