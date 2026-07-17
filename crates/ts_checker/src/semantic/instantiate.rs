//! Dependency-closed type instantiation.
//!
//! This is the first exact slice of pinned `instantiateTypeWorker`. It covers
//! primitive and literal leaves, direct type-parameter mapping, canonical
//! Array/ReadonlyArray references under an explicit target capability, and
//! anonymous origin-free unions whose constituents remain inside the installed
//! canonical union domain. Other object, signature, alias, and origin
//! instantiation needs its owning caches and is rejected instead of identity.

use std::collections::{HashMap, HashSet};

use super::{
    TypeAliasId, TypeId, TypeMapperId,
    array_types::{ArrayTypeError, CanonicalArrayTargets},
    bootstrap::LiteralTypeCacheError,
    mapper::{CanonicalTypeMapperStore, TypeMapperApplication},
    type_records::TypeData,
};

/// Pinned checker limits for one instantiation query.
///
/// `max_depth` and `max_count` correspond to upstream's depth 100 and
/// per-expression count 5,000,000 guards. The Rust leaf returns a typed error
/// because publishing the checker error identity and TS2589 diagnostic belongs
/// to the eventual query context.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[allow(dead_code)] // Installed ahead of the generic call/signature consumer.
pub(super) struct InstantiationLimits {
    pub max_depth: usize,
    pub max_count: usize,
}

impl Default for InstantiationLimits {
    fn default() -> Self {
        Self {
            max_depth: 100,
            max_count: 5_000_000,
        }
    }
}

/// A semantic dependency or guard that prevents exact instantiation.
#[derive(Debug, PartialEq)]
#[allow(dead_code)] // Installed ahead of the generic call/signature consumer.
pub(super) enum InstantiationError {
    InvalidType(TypeId),
    InvalidMapper(TypeMapperId),
    DepthLimit {
        depth: usize,
        limit: usize,
    },
    CountLimit {
        count: usize,
        limit: usize,
    },
    UnsupportedType(TypeId),
    UnsupportedAliasedUnion(TypeId),
    UnsupportedUnionOrigin(TypeId),
    UnsupportedUnionConstituent(TypeId),
    /// Needs a read-only canonical union identity validator that admits type
    /// parameters; the installed literal-union validator intentionally does not.
    UnvalidatedUnchangedUnion(TypeId),
    Array(ArrayTypeError),
    Union(LiteralTypeCacheError),
}

impl std::fmt::Display for InstantiationError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::InvalidType(type_) => {
                write!(formatter, "cannot instantiate invalid type {type_:?}")
            }
            Self::InvalidMapper(mapper) => {
                write!(
                    formatter,
                    "cannot instantiate with invalid mapper {mapper:?}"
                )
            }
            Self::DepthLimit { depth, limit } => write!(
                formatter,
                "type instantiation depth {depth} reached configured limit {limit}"
            ),
            Self::CountLimit { count, limit } => write!(
                formatter,
                "type instantiation count {count} reached configured limit {limit}"
            ),
            Self::UnsupportedType(type_) => {
                write!(
                    formatter,
                    "type {type_:?} is outside the installed instantiation slice"
                )
            }
            Self::UnsupportedAliasedUnion(type_) => write!(
                formatter,
                "union {type_:?} requires type-alias instantiation"
            ),
            Self::UnsupportedUnionOrigin(type_) => write!(
                formatter,
                "union {type_:?} requires named-union origin instantiation"
            ),
            Self::UnsupportedUnionConstituent(type_) => write!(
                formatter,
                "union constituent {type_:?} is outside the primitive/literal mapper slice"
            ),
            Self::UnvalidatedUnchangedUnion(type_) => write!(
                formatter,
                "unchanged generic union {type_:?} requires canonical identity validation"
            ),
            Self::Array(error) => error.fmt(formatter),
            Self::Union(error) => error.fmt(formatter),
        }
    }
}

impl std::error::Error for InstantiationError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Array(error) => Some(error),
            Self::Union(error) => Some(error),
            _ => None,
        }
    }
}

impl From<LiteralTypeCacheError> for InstantiationError {
    fn from(error: LiteralTypeCacheError) -> Self {
        Self::Union(error)
    }
}

impl From<ArrayTypeError> for InstantiationError {
    fn from(error: ArrayTypeError) -> Self {
        Self::Array(error)
    }
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
struct InstantiationCacheKey {
    type_: TypeId,
    alias: Option<TypeAliasId>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum InstantiationMappingIdentity {
    Stored(TypeMapperId),
    Vector {
        sources: usize,
        source_count: usize,
        targets: usize,
        target_count: usize,
    },
}

#[derive(Debug)]
struct ActiveMapperFrame {
    mapping: InstantiationMappingIdentity,
    cache: HashMap<InstantiationCacheKey, TypeId>,
}

/// Checker-query-owned instantiation accounting and recursive mapper cache.
///
/// The per-query count is intentionally not reset by each instantiation call:
/// upstream shares it across all work caused by one checked source element or
/// expression. Query owners call [`Self::reset_query`] at that boundary. The
/// total count remains cumulative across resets, matching checker telemetry.
#[derive(Debug)]
#[allow(dead_code)] // Installed ahead of the source-element query owner.
pub(super) struct InstantiationSession {
    limits: InstantiationLimits,
    depth: usize,
    count: usize,
    total_count: usize,
    active_mappers: Vec<ActiveMapperFrame>,
}

impl InstantiationSession {
    pub(super) fn new(limits: InstantiationLimits) -> Self {
        Self {
            limits,
            depth: 0,
            count: 0,
            total_count: 0,
            active_mappers: Vec::new(),
        }
    }

    /// Starts the next source-element or expression query. This must not reset
    /// `total_count`, which is checker-global upstream.
    #[allow(dead_code)] // Called by the future source-element query owner.
    pub(super) fn reset_query(&mut self) {
        self.depth = 0;
        self.count = 0;
        self.active_mappers.clear();
    }

    #[cfg(test)]
    const fn query_count(&self) -> usize {
        self.count
    }

    /// Cumulative checker telemetry; unlike the query counter, this survives
    /// [`Self::reset_query`].
    #[allow(dead_code)] // Read by the future checker telemetry owner.
    pub(super) const fn total_count(&self) -> usize {
        self.total_count
    }
}

/// Instantiates one type through the dependency-closed mapper slice.
#[allow(dead_code)] // Installed ahead of the generic call/signature consumer.
pub(super) fn instantiate_type(
    store: &mut CanonicalTypeMapperStore,
    type_: TypeId,
    mapper: TypeMapperId,
) -> Result<TypeId, InstantiationError> {
    instantiate_type_with_limits(store, type_, mapper, InstantiationLimits::default())
}

#[allow(dead_code)] // Configurable boundary used by checker-query integration and focused tests.
pub(super) fn instantiate_type_with_limits(
    store: &mut CanonicalTypeMapperStore,
    type_: TypeId,
    mapper: TypeMapperId,
    limits: InstantiationLimits,
) -> Result<TypeId, InstantiationError> {
    let mut session = InstantiationSession::new(limits);
    instantiate_type_with_session(store, type_, mapper, None, &mut session)
}

/// Instantiates inside an existing checker query. The caller owns the
/// [`InstantiationSession::reset_query`] boundary.
#[allow(dead_code)] // Installed ahead of the source-element query owner.
pub(super) fn instantiate_type_with_session(
    store: &mut CanonicalTypeMapperStore,
    type_: TypeId,
    mapper: TypeMapperId,
    array_targets: Option<CanonicalArrayTargets>,
    session: &mut InstantiationSession,
) -> Result<TypeId, InstantiationError> {
    if store.mapper_payload(mapper).is_none() {
        return Err(InstantiationError::InvalidMapper(mapper));
    }
    instantiate_type_with_alias(
        store,
        type_,
        InstantiationMapping::Stored(mapper),
        array_targets,
        None,
        session,
    )
}

/// Instantiates through the exact parallel vectors used by `newTypeMapper`
/// without publishing a mapper record.
///
/// Generic-call inference needs to project parameter and return types before
/// the owning signature cache is ready to commit. Keeping this representation
/// borrowed makes that resolution phase independent of mapper/signature cache
/// publication while preserving the pinned mapper's first-match behavior.
pub(super) fn instantiate_type_with_vector(
    store: &mut CanonicalTypeMapperStore,
    type_: TypeId,
    sources: &[TypeId],
    targets: &[TypeId],
) -> Result<TypeId, InstantiationError> {
    instantiate_type_with_vector_and_optional_array_targets(store, type_, sources, targets, None)
}

/// Vector instantiation with retained canonical `Array` targets.
pub(super) fn instantiate_type_with_vector_and_array_targets(
    store: &mut CanonicalTypeMapperStore,
    type_: TypeId,
    sources: &[TypeId],
    targets: &[TypeId],
    array_targets: CanonicalArrayTargets,
) -> Result<TypeId, InstantiationError> {
    instantiate_type_with_vector_and_optional_array_targets(
        store,
        type_,
        sources,
        targets,
        Some(array_targets),
    )
}

fn instantiate_type_with_vector_and_optional_array_targets(
    store: &mut CanonicalTypeMapperStore,
    type_: TypeId,
    sources: &[TypeId],
    targets: &[TypeId],
    array_targets: Option<CanonicalArrayTargets>,
) -> Result<TypeId, InstantiationError> {
    if sources.len() != targets.len() {
        return Err(InstantiationError::InvalidType(type_));
    }
    for endpoint in sources.iter().chain(targets) {
        if store.type_payload(*endpoint).is_none() {
            return Err(InstantiationError::InvalidType(*endpoint));
        }
    }
    let mut session = InstantiationSession::new(InstantiationLimits::default());
    instantiate_type_with_alias(
        store,
        type_,
        InstantiationMapping::Vector { sources, targets },
        array_targets,
        None,
        &mut session,
    )
}

#[derive(Clone, Copy, Debug)]
enum InstantiationMapping<'a> {
    Stored(TypeMapperId),
    Vector {
        sources: &'a [TypeId],
        targets: &'a [TypeId],
    },
}

impl InstantiationMapping<'_> {
    fn identity(self) -> InstantiationMappingIdentity {
        match self {
            Self::Stored(mapper) => InstantiationMappingIdentity::Stored(mapper),
            Self::Vector { sources, targets } => InstantiationMappingIdentity::Vector {
                sources: sources.as_ptr() as usize,
                source_count: sources.len(),
                targets: targets.as_ptr() as usize,
                target_count: targets.len(),
            },
        }
    }
}

fn instantiate_type_with_alias(
    store: &mut CanonicalTypeMapperStore,
    type_: TypeId,
    mapping: InstantiationMapping<'_>,
    array_targets: Option<CanonicalArrayTargets>,
    alias: Option<TypeAliasId>,
    session: &mut InstantiationSession,
) -> Result<TypeId, InstantiationError> {
    if !could_contain_installed_type_variables(store, type_, array_targets)? {
        return Ok(type_);
    }
    if session.depth == session.limits.max_depth {
        return Err(InstantiationError::DepthLimit {
            depth: session.depth,
            limit: session.limits.max_depth,
        });
    }
    if session.count >= session.limits.max_count {
        return Err(InstantiationError::CountLimit {
            count: session.count,
            limit: session.limits.max_count,
        });
    }

    let mapping_identity = mapping.identity();
    let existing_index = session
        .active_mappers
        .iter()
        .rposition(|frame| frame.mapping == mapping_identity);
    let frame_index = if let Some(index) = existing_index {
        index
    } else {
        session.active_mappers.push(ActiveMapperFrame {
            mapping: mapping_identity,
            cache: HashMap::new(),
        });
        session.active_mappers.len() - 1
    };
    let key = InstantiationCacheKey { type_, alias };
    if let Some(cached) = session.active_mappers[frame_index].cache.get(&key) {
        return Ok(*cached);
    }

    session.total_count += 1;
    session.count += 1;
    session.depth += 1;
    let result = instantiate_type_worker(store, type_, mapping, array_targets, session);
    if existing_index.is_none() {
        let popped = session
            .active_mappers
            .pop()
            .expect("a first active mapper owns its scratch cache");
        debug_assert_eq!(popped.mapping, mapping_identity);
    } else if let Ok(instantiated) = &result {
        session.active_mappers[frame_index]
            .cache
            .insert(key, *instantiated);
    }
    session.depth -= 1;
    result
}

fn could_contain_installed_type_variables(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
    array_targets: Option<CanonicalArrayTargets>,
) -> Result<bool, InstantiationError> {
    could_contain_installed_type_variables_worker(store, type_, array_targets, &mut HashSet::new())
}

fn could_contain_installed_type_variables_worker(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
    array_targets: Option<CanonicalArrayTargets>,
    seen: &mut HashSet<TypeId>,
) -> Result<bool, InstantiationError> {
    if !seen.insert(type_) {
        // The installed domain cannot construct a recursive union/array graph,
        // but fail conservatively if a future producer exposes one.
        return Ok(true);
    }
    let record = store
        .type_payload(type_)
        .ok_or(InstantiationError::InvalidType(type_))?;
    let result = match record.data() {
        TypeData::TypeParameter(_) => Ok(true),
        TypeData::Intrinsic(_) | TypeData::Literal(_) | TypeData::UniqueEsSymbol(_) => Ok(false),
        TypeData::Union(data) => {
            // Preserve the installed slice's typed alias/origin boundaries.
            // Their eventual implementations will inspect alias arguments and
            // origin graphs as part of the full upstream predicate.
            if record.alias().is_some() || data.origin.is_some() {
                Ok(true)
            } else {
                let constituents = data.union.types.clone();
                constituents
                    .into_iter()
                    .try_fold(false, |contains, constituent| {
                        Ok(contains
                            || could_contain_installed_type_variables_worker(
                                store,
                                constituent,
                                array_targets,
                                seen,
                            )?)
                    })
            }
        }
        TypeData::TypeReference(_) => {
            let Some(array_targets) = array_targets else {
                return Ok(true);
            };
            match store.canonical_array_reference_with_targets(array_targets, type_)? {
                Some(reference) => could_contain_installed_type_variables_worker(
                    store,
                    reference.element_type,
                    Some(array_targets),
                    seen,
                ),
                None => Ok(true),
            }
        }
        _ => Ok(true),
    };
    seen.remove(&type_);
    result
}

enum InstantiationWork {
    TypeParameter,
    Identity,
    Union {
        aliased: bool,
        has_origin: bool,
        constituents: Vec<TypeId>,
    },
    TypeReference,
    Unsupported,
}

fn instantiate_type_worker(
    store: &mut CanonicalTypeMapperStore,
    type_: TypeId,
    mapping: InstantiationMapping<'_>,
    array_targets: Option<CanonicalArrayTargets>,
    session: &mut InstantiationSession,
) -> Result<TypeId, InstantiationError> {
    let work = {
        let record = store
            .type_payload(type_)
            .ok_or(InstantiationError::InvalidType(type_))?;
        match record.data() {
            TypeData::TypeParameter(_) => InstantiationWork::TypeParameter,
            TypeData::Intrinsic(_) | TypeData::Literal(_) | TypeData::UniqueEsSymbol(_) => {
                InstantiationWork::Identity
            }
            TypeData::Union(data) => InstantiationWork::Union {
                aliased: record.alias().is_some(),
                has_origin: data.origin.is_some(),
                constituents: data.union.types.clone(),
            },
            TypeData::TypeReference(_) => InstantiationWork::TypeReference,
            _ => InstantiationWork::Unsupported,
        }
    };
    match work {
        InstantiationWork::TypeParameter => {
            apply_mapping(store, type_, mapping, array_targets, session)
        }
        InstantiationWork::Identity => Ok(type_),
        InstantiationWork::Union {
            aliased,
            has_origin,
            constituents,
        } => {
            if aliased {
                return Err(InstantiationError::UnsupportedAliasedUnion(type_));
            }
            if has_origin {
                return Err(InstantiationError::UnsupportedUnionOrigin(type_));
            }
            instantiate_union(store, type_, &constituents, mapping, array_targets, session)
        }
        InstantiationWork::TypeReference => instantiate_array_reference(
            store,
            type_,
            mapping,
            array_targets.ok_or(InstantiationError::UnsupportedType(type_))?,
            session,
        ),
        InstantiationWork::Unsupported => Err(InstantiationError::UnsupportedType(type_)),
    }
}

fn apply_mapping(
    store: &mut CanonicalTypeMapperStore,
    type_: TypeId,
    mapping: InstantiationMapping<'_>,
    array_targets: Option<CanonicalArrayTargets>,
    session: &mut InstantiationSession,
) -> Result<TypeId, InstantiationError> {
    match mapping {
        InstantiationMapping::Vector { sources, targets } => {
            if store.type_payload(type_).is_none() {
                return Err(InstantiationError::InvalidType(type_));
            }
            Ok(sources
                .iter()
                .position(|source| *source == type_)
                .map_or(type_, |index| targets[index]))
        }
        InstantiationMapping::Stored(mapper) => {
            if store.type_payload(type_).is_none() {
                return Err(InstantiationError::InvalidType(type_));
            }
            let application = store
                .mapper_application(mapper, type_)
                .ok_or(InstantiationError::InvalidMapper(mapper))?;
            match application {
                TypeMapperApplication::Direct(mapped_type) => Ok(mapped_type),
                TypeMapperApplication::Merged { first, second } => {
                    let intermediate = apply_mapping(
                        store,
                        type_,
                        InstantiationMapping::Stored(first),
                        array_targets,
                        session,
                    )?;
                    apply_mapping(
                        store,
                        intermediate,
                        InstantiationMapping::Stored(second),
                        array_targets,
                        session,
                    )
                }
                TypeMapperApplication::Composite { first, second } => {
                    let intermediate = apply_mapping(
                        store,
                        type_,
                        InstantiationMapping::Stored(first),
                        array_targets,
                        session,
                    )?;
                    if intermediate == type_ {
                        apply_mapping(
                            store,
                            type_,
                            InstantiationMapping::Stored(second),
                            array_targets,
                            session,
                        )
                    } else {
                        instantiate_type_with_alias(
                            store,
                            intermediate,
                            InstantiationMapping::Stored(second),
                            array_targets,
                            None,
                            session,
                        )
                    }
                }
            }
        }
    }
}

fn instantiate_array_reference(
    store: &mut CanonicalTypeMapperStore,
    source: TypeId,
    mapping: InstantiationMapping<'_>,
    array_targets: CanonicalArrayTargets,
    session: &mut InstantiationSession,
) -> Result<TypeId, InstantiationError> {
    let Some(reference) = store.canonical_array_reference_with_targets(array_targets, source)?
    else {
        return Err(InstantiationError::UnsupportedType(source));
    };
    let element = instantiate_type_with_alias(
        store,
        reference.element_type,
        mapping,
        Some(array_targets),
        None,
        session,
    )?;
    if element == reference.element_type {
        return Ok(source);
    }
    store
        .create_canonical_array_type_with_targets(array_targets, element, reference.readonly)
        .map_err(Into::into)
}

fn instantiate_union(
    store: &mut CanonicalTypeMapperStore,
    source: TypeId,
    constituents: &[TypeId],
    mapping: InstantiationMapping<'_>,
    array_targets: Option<CanonicalArrayTargets>,
    session: &mut InstantiationSession,
) -> Result<TypeId, InstantiationError> {
    let mut mapped_types = Vec::with_capacity(constituents.len());
    let mut changed = false;
    let mut contains_type_parameter = false;
    for constituent in constituents {
        let record = store
            .type_payload(*constituent)
            .ok_or(InstantiationError::InvalidType(*constituent))?;
        if !matches!(
            record.data(),
            TypeData::Intrinsic(_)
                | TypeData::Literal(_)
                | TypeData::UniqueEsSymbol(_)
                | TypeData::TypeParameter(_)
        ) {
            return Err(InstantiationError::UnsupportedUnionConstituent(
                *constituent,
            ));
        }
        contains_type_parameter |= matches!(record.data(), TypeData::TypeParameter(_));
    }
    if !contains_type_parameter {
        return Ok(source);
    }
    for constituent in constituents {
        let instantiated = instantiate_type_with_alias(
            store,
            *constituent,
            mapping,
            array_targets,
            None,
            session,
        )?;
        changed |= instantiated != *constituent;
        mapped_types.push(instantiated);
    }
    if !changed {
        return Err(InstantiationError::UnvalidatedUnchangedUnion(source));
    }
    canonical_anonymous_union(store, &mapped_types).map_err(Into::into)
}

pub(super) fn canonical_anonymous_union(
    store: &mut CanonicalTypeMapperStore,
    types: &[TypeId],
) -> Result<TypeId, LiteralTypeCacheError> {
    let mut prepared = store.prepare_type_query_types(&[], &[], &[], 1, 0)?;
    store.literal_union_type_prepared(types, None, &mut prepared)
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
    fn maps_type_parameters_and_preserves_dependency_closed_leaves() {
        let mut store = initialized_store();
        let (string, number) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (bootstrap.string_type, bootstrap.number_type)
        };
        let parameter = store.alloc_type_parameter(None).unwrap();
        let mapper = store.new_simple_type_mapper(parameter, number).unwrap();

        assert_eq!(instantiate_type(&mut store, parameter, mapper), Ok(number));
        assert_eq!(instantiate_type(&mut store, string, mapper), Ok(string));
    }

    #[test]
    fn instantiates_anonymous_union_with_literal_reduction() {
        let mut store = initialized_store();
        let (string, number) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (bootstrap.string_type, bootstrap.number_type)
        };
        let parameter = store.alloc_type_parameter(None).unwrap();
        let source = store
            .alloc_union_type(ObjectFlags::NONE, vec![parameter, string])
            .unwrap();
        let mapper = store.new_simple_type_mapper(parameter, number).unwrap();

        let result = instantiate_type(&mut store, source, mapper).unwrap();
        let TypeData::Union(data) = store.type_payload(result).unwrap().data() else {
            panic!("two primitive constituents must remain a union");
        };
        assert_eq!(data.union.types, [string, number]);
    }

    #[test]
    fn composite_mapper_recursively_instantiates_a_changed_intermediate() {
        let mut store = initialized_store();
        let (string, number) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (bootstrap.string_type, bootstrap.number_type)
        };
        let outer = store.alloc_type_parameter(None).unwrap();
        let inner = store.alloc_type_parameter(None).unwrap();
        let intermediate = store
            .alloc_union_type(ObjectFlags::NONE, vec![inner, string])
            .unwrap();
        let first = store.new_simple_type_mapper(outer, intermediate).unwrap();
        let second = store.new_simple_type_mapper(inner, number).unwrap();
        let merged = store.merge_type_mappers(Some(first), second).unwrap();
        let composite = store.combine_type_mappers(Some(first), second).unwrap();

        assert_eq!(
            instantiate_type(&mut store, outer, merged),
            Ok(intermediate)
        );
        let instantiated = instantiate_type(&mut store, outer, composite).unwrap();
        let TypeData::Union(data) = store.type_payload(instantiated).unwrap().data() else {
            panic!("the recursively instantiated intermediate must remain a union");
        };
        assert_eq!(data.union.types, [string, number]);
    }

    #[test]
    fn active_mapper_cache_precedes_instantiation_counter_increment() {
        let mut store = initialized_store();
        let (string, number) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (bootstrap.string_type, bootstrap.number_type)
        };
        let parameter = store.alloc_type_parameter(None).unwrap();
        let source = store
            .alloc_union_type(ObjectFlags::NONE, vec![parameter, parameter, string])
            .unwrap();
        let mapper = store.new_simple_type_mapper(parameter, number).unwrap();
        let mut session = InstantiationSession::new(InstantiationLimits {
            max_depth: 10,
            max_count: 3,
        });

        let result =
            instantiate_type_with_session(&mut store, source, mapper, None, &mut session).unwrap();

        assert_eq!(session.query_count(), 2, "the repeated leaf must hit cache");
        let TypeData::Union(data) = store.type_payload(result).unwrap().data() else {
            panic!("the remaining string and number constituents must form a union");
        };
        assert_eq!(data.union.types, [string, number]);
    }

    #[test]
    fn session_count_resets_only_at_the_explicit_query_boundary() {
        let mut store = initialized_store();
        let number = store.intrinsic_bootstrap().unwrap().number_type;
        let parameter = store.alloc_type_parameter(None).unwrap();
        let mapper = store.new_simple_type_mapper(parameter, number).unwrap();
        let mut session = InstantiationSession::new(InstantiationLimits {
            max_depth: 10,
            max_count: 1,
        });

        assert_eq!(
            instantiate_type_with_session(&mut store, parameter, mapper, None, &mut session),
            Ok(number)
        );
        assert_eq!(session.query_count(), 1);
        assert_eq!(session.total_count(), 1);
        assert_eq!(
            instantiate_type_with_session(&mut store, parameter, mapper, None, &mut session),
            Err(InstantiationError::CountLimit { count: 1, limit: 1 })
        );

        session.reset_query();
        assert_eq!(
            instantiate_type_with_session(&mut store, parameter, mapper, None, &mut session),
            Ok(number)
        );
        assert_eq!(session.query_count(), 1);
        assert_eq!(session.total_count(), 2);
    }

    #[test]
    fn vector_instantiation_maps_many_parameters_without_allocating_a_mapper() {
        let mut store = initialized_store();
        let (string, number) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (bootstrap.string_type, bootstrap.number_type)
        };
        let first = store.alloc_type_parameter(None).unwrap();
        let second = store.alloc_type_parameter(None).unwrap();
        let source = store
            .alloc_union_type(ObjectFlags::NONE, vec![first, second])
            .unwrap();
        let mapper_count = store.mapper_len();

        let result =
            instantiate_type_with_vector(&mut store, source, &[first, second], &[string, number])
                .unwrap();

        assert_eq!(store.mapper_len(), mapper_count);
        let TypeData::Union(data) = store.type_payload(result).unwrap().data() else {
            panic!("two distinct mapped leaves must remain a union");
        };
        assert_eq!(data.union.types, [string, number]);
    }

    #[test]
    fn vector_instantiation_is_single_pass_for_dependent_recovery_arguments() {
        let mut store = initialized_store();
        let string = store.intrinsic_bootstrap().unwrap().string_type;
        let first = store.alloc_type_parameter(None).unwrap();
        let second = store.alloc_type_parameter(None).unwrap();

        assert_eq!(
            instantiate_type_with_vector(&mut store, second, &[first, second], &[string, first],),
            Ok(first),
            "newTypeMapper maps U to its raw recovery target T without remapping T"
        );
    }

    #[test]
    fn unchanged_generic_union_fails_closed_without_identity_validator() {
        let mut store = initialized_store();
        let string = store.intrinsic_bootstrap().unwrap().string_type;
        let parameter = store.alloc_type_parameter(None).unwrap();
        let source = store
            .alloc_union_type(ObjectFlags::NONE, vec![parameter, string])
            .unwrap();
        let mapper = store.new_simple_type_mapper(parameter, parameter).unwrap();
        let before = store.type_len();

        assert_eq!(
            instantiate_type(&mut store, source, mapper),
            Err(InstantiationError::UnvalidatedUnchangedUnion(source))
        );
        assert_eq!(store.type_len(), before);
    }

    #[test]
    fn non_variable_leaves_do_not_consume_instantiation_limits() {
        let mut store = initialized_store();
        let (string, number) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (bootstrap.string_type, bootstrap.number_type)
        };
        let parameter = store.alloc_type_parameter(None).unwrap();
        let mapper = store.new_simple_type_mapper(parameter, number).unwrap();
        let limits = InstantiationLimits {
            max_depth: 0,
            max_count: 0,
        };
        assert_eq!(
            instantiate_type_with_limits(&mut store, string, mapper, limits),
            Ok(string)
        );

        let union = store
            .alloc_union_type(ObjectFlags::NONE, vec![string, number])
            .unwrap();
        assert_eq!(
            instantiate_type_with_limits(&mut store, union, mapper, limits),
            Ok(union)
        );
        assert_eq!(
            instantiate_type_with_limits(&mut store, parameter, mapper, limits),
            Err(InstantiationError::DepthLimit { depth: 0, limit: 0 })
        );
    }

    #[test]
    fn aliases_and_limits_fail_closed_without_semantic_writes() {
        let mut store = initialized_store();
        let (string, number) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (bootstrap.string_type, bootstrap.number_type)
        };
        let parameter = store.alloc_type_parameter(None).unwrap();
        let source = store
            .alloc_union_type(ObjectFlags::NONE, vec![parameter, string])
            .unwrap();
        let alias = store.alloc_type_alias(None).unwrap();
        assert!(store.set_type_alias(source, Some(alias)));
        let mapper = store.new_simple_type_mapper(parameter, number).unwrap();
        let before = store.type_len();

        assert_eq!(
            instantiate_type(&mut store, source, mapper),
            Err(InstantiationError::UnsupportedAliasedUnion(source))
        );
        assert_eq!(store.type_len(), before);

        assert!(store.set_type_alias(source, None));
        assert_eq!(
            instantiate_type_with_limits(
                &mut store,
                source,
                mapper,
                InstantiationLimits {
                    max_depth: 1,
                    max_count: 10,
                },
            ),
            Err(InstantiationError::DepthLimit { depth: 1, limit: 1 })
        );
        assert_eq!(store.type_len(), before);
    }
}
