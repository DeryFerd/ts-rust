//! Dependency-closed type instantiation.
//!
//! This is the first exact slice of pinned `instantiateTypeWorker`. It covers
//! primitive and literal leaves, direct type-parameter mapping, and anonymous
//! origin-free unions whose constituents remain inside the installed canonical
//! union domain. Object, signature, alias, and origin instantiation need their
//! owning caches and are rejected instead of being treated as identities.

use super::{
    TypeId, TypeMapperId, bootstrap::LiteralTypeCacheError, mapper::CanonicalTypeMapperStore,
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
            Self::Union(error) => error.fmt(formatter),
        }
    }
}

impl std::error::Error for InstantiationError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
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

#[derive(Clone, Copy, Debug)]
struct InstantiationState {
    limits: InstantiationLimits,
    count: usize,
}

impl InstantiationState {
    fn enter(&mut self, depth: usize) -> Result<(), InstantiationError> {
        if depth >= self.limits.max_depth {
            return Err(InstantiationError::DepthLimit {
                depth,
                limit: self.limits.max_depth,
            });
        }
        if self.count >= self.limits.max_count {
            return Err(InstantiationError::CountLimit {
                count: self.count,
                limit: self.limits.max_count,
            });
        }
        self.count += 1;
        Ok(())
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
    if store.mapper_payload(mapper).is_none() {
        return Err(InstantiationError::InvalidMapper(mapper));
    }
    let mut state = InstantiationState { limits, count: 0 };
    instantiate_type_worker(store, type_, mapper, 0, &mut state)
}

fn instantiate_type_worker(
    store: &mut CanonicalTypeMapperStore,
    type_: TypeId,
    mapper: TypeMapperId,
    depth: usize,
    state: &mut InstantiationState,
) -> Result<TypeId, InstantiationError> {
    let record = store
        .type_payload(type_)
        .ok_or(InstantiationError::InvalidType(type_))?;
    match record.data() {
        TypeData::TypeParameter(_) => {
            state.enter(depth)?;
            store
                .map_type(mapper, type_)
                .ok_or(InstantiationError::InvalidMapper(mapper))
        }
        TypeData::Intrinsic(_) | TypeData::Literal(_) | TypeData::UniqueEsSymbol(_) => Ok(type_),
        TypeData::Union(data) => {
            if record.alias().is_some() {
                return Err(InstantiationError::UnsupportedAliasedUnion(type_));
            }
            if data.origin.is_some() {
                return Err(InstantiationError::UnsupportedUnionOrigin(type_));
            }
            let constituents = data.union.types.clone();
            instantiate_union(store, type_, &constituents, mapper, depth, state)
        }
        _ => Err(InstantiationError::UnsupportedType(type_)),
    }
}

fn instantiate_union(
    store: &mut CanonicalTypeMapperStore,
    source: TypeId,
    constituents: &[TypeId],
    mapper: TypeMapperId,
    depth: usize,
    state: &mut InstantiationState,
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
    state.enter(depth)?;
    for constituent in constituents {
        let instantiated = instantiate_type_worker(store, *constituent, mapper, depth + 1, state)?;
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
