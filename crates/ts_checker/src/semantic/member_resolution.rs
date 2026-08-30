//! Exact first leaf of union property synthesis.
//!
//! This ports the direct-property portion of pinned
//! `getPropertyOfUnionOrIntersectionType` and
//! `createUnionOrIntersectionProperty`. The receiver has exactly two
//! already-resolved property-only constituents: either the original anonymous,
//! declaration-free raw objects or two source-declared interfaces and type
//! literals. The leaf intentionally does not project apparent
//! `Object`/`Function` members, index signatures, callables, intersections, or
//! deferred property types.
//!
//! The existing `UnionOrIntersectionTypeData` cache is authoritative. A cold
//! query allocates its augmented property-cache table before synthesizing a
//! property, including same-symbol and all-missing queries. Warm hits are
//! proved from the selected name only and allocate nothing.
//! Symbol display shares the read-only plan assembly and exact cache proof.

use ts_ast::{NodeRef, SyntaxKind};
use ts_binder::{
    CheckFlags, EscapedName, InternalSymbolName, SemanticSymbolId, SymbolFlags, SymbolTableId,
    semantic::PreparedSymbolTable,
};

use super::{
    CanonicalTypeMapperStore, DeclaredTypeHost, RelationUnavailable, TypeId,
    bootstrap::{LiteralTypeCacheError, PreparedTypeQueryTypes},
    links::ValueSymbolLinks,
    object_members::{
        DeclaredPropertyObjectProof, DeclaredPropertyObjectValidation,
        validate_resolved_declared_property_object,
    },
    relater::ResolvedOwnProperty,
    store::SourceNodeParent,
    type_records::{
        ConstituentMapState, ConstrainedTypeData, StructuredTypeData, TypeCacheState, TypeData,
    },
    types::{ObjectFlags, TypeFlags},
};

/// One public, non-partial property projected from an exact union receiver.
///
/// `symbol` preserves pinned identity: a same-symbol union returns the original
/// source symbol, while distinct source symbols return the cached synthetic
/// symbol. `type_` composes lookup with pinned `getTypeOfSymbol` read
/// optionality, so a strict optional borrowed source keeps its raw value links
/// while this projection returns `raw | undefined`.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ResolvedUnionProperty {
    symbol: SemanticSymbolId,
    type_: TypeId,
    optional: bool,
    readonly: bool,
}

impl ResolvedUnionProperty {
    #[must_use]
    pub const fn symbol(&self) -> SemanticSymbolId {
        self.symbol
    }

    #[must_use]
    pub const fn type_id(&self) -> TypeId {
        self.type_
    }

    #[must_use]
    pub const fn is_optional(&self) -> bool {
        self.optional
    }

    #[must_use]
    pub const fn is_readonly(&self) -> bool {
        self.readonly
    }
}

/// A malformed cache or a deliberately unported member-resolution family.
///
/// No variant is a negative property lookup. A valid union with no public
/// property returns `Ok(None)`.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum UnionPropertyError {
    InvalidUnion(TypeId),
    UnsupportedUnion(TypeId),
    UnsupportedConstituent(TypeId),
    UnsupportedPropertyType(TypeId),
    UnsupportedExactOptionalProperty(TypeId),
    InvalidProperty(SemanticSymbolId),
    InvalidCache(TypeId),
    Relation(RelationUnavailable),
    TypeCache(LiteralTypeCacheError),
    Capacity(TypeId),
}

/// Public failure surface for a context-owned union-property query.
///
/// Internal literal/union cache implementation errors are deliberately folded
/// into [`Self::InvalidCache`], so this adapter does not expose a private
/// bootstrap error family.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CanonicalUnionPropertyError {
    InvalidUnion(TypeId),
    UnsupportedUnion(TypeId),
    UnsupportedConstituent(TypeId),
    UnsupportedPropertyType(TypeId),
    UnsupportedExactOptionalProperty(TypeId),
    InvalidProperty(SemanticSymbolId),
    InvalidCache(TypeId),
    Relation(RelationUnavailable),
    Capacity(TypeId),
}

impl CanonicalUnionPropertyError {
    pub(super) const fn from_internal(union: TypeId, error: UnionPropertyError) -> Self {
        match error {
            UnionPropertyError::InvalidUnion(type_) => Self::InvalidUnion(type_),
            UnionPropertyError::UnsupportedUnion(type_) => Self::UnsupportedUnion(type_),
            UnionPropertyError::UnsupportedConstituent(type_) => {
                Self::UnsupportedConstituent(type_)
            }
            UnionPropertyError::UnsupportedPropertyType(type_) => {
                Self::UnsupportedPropertyType(type_)
            }
            UnionPropertyError::UnsupportedExactOptionalProperty(type_) => {
                Self::UnsupportedExactOptionalProperty(type_)
            }
            UnionPropertyError::InvalidProperty(symbol) => Self::InvalidProperty(symbol),
            UnionPropertyError::InvalidCache(type_) => Self::InvalidCache(type_),
            UnionPropertyError::Relation(error) => Self::Relation(error),
            UnionPropertyError::TypeCache(LiteralTypeCacheError::Capacity) => Self::Capacity(union),
            UnionPropertyError::TypeCache(_) => Self::InvalidCache(union),
            UnionPropertyError::Capacity(type_) => Self::Capacity(type_),
        }
    }
}

impl std::fmt::Display for CanonicalUnionPropertyError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::InvalidUnion(type_) => {
                write!(formatter, "union type {type_:?} has invalid member state")
            }
            Self::UnsupportedUnion(type_) => {
                write!(
                    formatter,
                    "union type {type_:?} is outside the direct member adapter"
                )
            }
            Self::UnsupportedConstituent(type_) => write!(
                formatter,
                "union constituent {type_:?} is outside the supported property-object modes"
            ),
            Self::UnsupportedPropertyType(type_) => write!(
                formatter,
                "property type {type_:?} is outside the terminal union-member leaf"
            ),
            Self::UnsupportedExactOptionalProperty(type_) => write!(
                formatter,
                "union type {type_:?} requires exact optional missing-type synthesis"
            ),
            Self::InvalidProperty(symbol) => {
                write!(
                    formatter,
                    "property symbol {symbol:?} has invalid union inputs"
                )
            }
            Self::InvalidCache(type_) => {
                write!(
                    formatter,
                    "union type {type_:?} has an invalid property cache"
                )
            }
            Self::Relation(error) => error.fmt(formatter),
            Self::Capacity(type_) => {
                write!(
                    formatter,
                    "union property query for {type_:?} exhausted capacity"
                )
            }
        }
    }
}

impl std::error::Error for CanonicalUnionPropertyError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Relation(error) => Some(error),
            Self::InvalidUnion(_)
            | Self::UnsupportedUnion(_)
            | Self::UnsupportedConstituent(_)
            | Self::UnsupportedPropertyType(_)
            | Self::UnsupportedExactOptionalProperty(_)
            | Self::InvalidProperty(_)
            | Self::InvalidCache(_)
            | Self::Capacity(_) => None,
        }
    }
}

impl std::fmt::Display for UnionPropertyError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::InvalidUnion(type_) => {
                write!(formatter, "union type {type_:?} has invalid member state")
            }
            Self::UnsupportedUnion(type_) => {
                write!(
                    formatter,
                    "union type {type_:?} is outside the direct member leaf"
                )
            }
            Self::UnsupportedConstituent(type_) => write!(
                formatter,
                "union constituent {type_:?} is outside the resolved property-object leaf"
            ),
            Self::UnsupportedPropertyType(type_) => write!(
                formatter,
                "property type {type_:?} is outside the terminal union-member leaf"
            ),
            Self::UnsupportedExactOptionalProperty(type_) => write!(
                formatter,
                "union type {type_:?} requires exact optional missing-type synthesis"
            ),
            Self::InvalidProperty(symbol) => {
                write!(
                    formatter,
                    "property symbol {symbol:?} has invalid union inputs"
                )
            }
            Self::InvalidCache(type_) => {
                write!(
                    formatter,
                    "union type {type_:?} has an invalid property cache"
                )
            }
            Self::Relation(error) => error.fmt(formatter),
            Self::TypeCache(error) => error.fmt(formatter),
            Self::Capacity(type_) => {
                write!(
                    formatter,
                    "union property query for {type_:?} exhausted capacity"
                )
            }
        }
    }
}

impl std::error::Error for UnionPropertyError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Relation(error) => Some(error),
            Self::TypeCache(error) => Some(error),
            Self::InvalidUnion(_)
            | Self::UnsupportedUnion(_)
            | Self::UnsupportedConstituent(_)
            | Self::UnsupportedPropertyType(_)
            | Self::UnsupportedExactOptionalProperty(_)
            | Self::InvalidProperty(_)
            | Self::InvalidCache(_)
            | Self::Capacity(_) => None,
        }
    }
}

impl From<RelationUnavailable> for UnionPropertyError {
    fn from(error: RelationUnavailable) -> Self {
        Self::Relation(error)
    }
}

impl From<LiteralTypeCacheError> for UnionPropertyError {
    fn from(error: LiteralTypeCacheError) -> Self {
        Self::TypeCache(error)
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct SourceProperty {
    symbol: SemanticSymbolId,
    raw_type: TypeId,
    optional: bool,
    readonly: bool,
    declaration: Option<NodeRef>,
    value_declaration: Option<NodeRef>,
    parent: Option<SemanticSymbolId>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct SyntheticPropertyPlan {
    sources: Vec<SourceProperty>,
    optional: bool,
    readonly: bool,
    partial: bool,
    declarations: Option<Vec<NodeRef>>,
    value_declaration: Option<NodeRef>,
    parent: Option<SemanticSymbolId>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum UnionMemberMode {
    Raw,
    Declared,
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum PropertyOutcome {
    Missing,
    Borrowed(SourceProperty),
    Synthetic(SyntheticPropertyPlan),
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct UnionPropertyPlan {
    union: TypeId,
    name: EscapedName,
    cache: Option<SymbolTableId>,
    cache_without_function_property_augment: Option<SymbolTableId>,
    outcome: PropertyOutcome,
}

type ValidatedUnionShell = (
    Vec<TypeId>,
    Option<SymbolTableId>,
    Option<SymbolTableId>,
    UnionMemberMode,
);

struct PreparedColdQuery {
    cache: Option<PreparedSymbolTable>,
    types: Option<PreparedTypeQueryTypes>,
}

#[derive(Clone, Copy)]
struct EffectiveTypes {
    values: [TypeId; 2],
    len: usize,
}

impl EffectiveTypes {
    fn as_slice(&self) -> &[TypeId] {
        &self.values[..self.len]
    }
}

impl CanonicalTypeMapperStore {
    /// Resolves one direct property from an already-resolved union receiver.
    ///
    /// Partial properties are synthesized and cached exactly, then filtered
    /// from this public result. This mirrors pinned
    /// `getPropertyOfUnionOrIntersectionType`, while keeping the internal
    /// `READ_PARTIAL` entry observable through the union's property cache.
    pub(super) fn resolved_union_property(
        &mut self,
        union: TypeId,
        name: &str,
    ) -> Result<Option<ResolvedUnionProperty>, UnionPropertyError> {
        let plan = plan_union_property(self, union, name)?;
        if let Some(cache) = plan.cache {
            let cached = self
                .symbol_table(cache)
                .ok_or(UnionPropertyError::InvalidCache(union))?
                .get(plan.name.as_ref());
            if let Some(cached) = cached {
                return validate_cached_property(self, &plan, cached);
            }
        }

        let mut prepared = prepare_cold_query(self, &plan)?;
        let cache = match plan.cache {
            Some(cache) => cache,
            None => publish_property_cache(
                self,
                &plan,
                prepared
                    .cache
                    .take()
                    .expect("a cold union query prepared its property-cache table"),
            ),
        };
        match &plan.outcome {
            PropertyOutcome::Missing => Ok(None),
            PropertyOutcome::Borrowed(property) => {
                assert_eq!(
                    self.insert_symbol(cache, plan.name.clone(), property.symbol),
                    Some(None)
                );
                let type_ = materialize_source_read_type(self, *property, prepared.types.as_mut());
                Ok(Some(project_source_property(*property, type_)))
            }
            PropertyOutcome::Synthetic(synthetic) => {
                let property = publish_synthetic_property(
                    self,
                    &plan,
                    synthetic,
                    prepared
                        .types
                        .as_mut()
                        .expect("a synthetic property prepared its type unions"),
                );
                assert_eq!(
                    self.insert_symbol(cache, plan.name.clone(), property.symbol),
                    Some(None)
                );
                if synthetic.partial {
                    Ok(None)
                } else {
                    Ok(Some(property))
                }
            }
        }
    }
}

fn plan_union_property(
    store: &mut CanonicalTypeMapperStore,
    union: TypeId,
    name: &str,
) -> Result<UnionPropertyPlan, UnionPropertyError> {
    let (constituents, cache, cache_without_function_property_augment, mode) =
        validate_union_shell(store, union)?;
    let source_name = name;
    let name = EscapedName::source(source_name);
    let mut properties = Vec::new();
    properties
        .try_reserve_exact(constituents.len())
        .map_err(|_| UnionPropertyError::Capacity(union))?;
    for constituent in constituents {
        // Preserve the provider's full proof, including absent-name queries
        // on raw objects whose members are authenticated transient symbols.
        let resolved = store.resolved_own_property(constituent, source_name)?;
        properties.push(
            resolved
                .map(|property| {
                    validate_source_property(store, constituent, mode, property, name.as_ref())
                })
                .transpose()?,
        );
    }
    finish_union_property_plan(
        store,
        union,
        name,
        cache,
        cache_without_function_property_augment,
        properties,
    )
}

/// Rebuilds a display proof without calling the mutable member resolver.
fn plan_cached_union_property(
    store: &CanonicalTypeMapperStore,
    union: TypeId,
    name: &str,
) -> Result<UnionPropertyPlan, UnionPropertyError> {
    let (constituents, cache, cache_without_function_property_augment, mode) =
        validate_union_shell(store, union)?;
    let name = EscapedName::source(name);
    let mut properties = Vec::new();
    properties
        .try_reserve_exact(constituents.len())
        .map_err(|_| UnionPropertyError::Capacity(union))?;
    for constituent in constituents {
        properties.push(read_union_source_property(
            store,
            constituent,
            mode,
            name.as_ref(),
        )?);
    }
    finish_union_property_plan(
        store,
        union,
        name,
        cache,
        cache_without_function_property_augment,
        properties,
    )
}

fn finish_union_property_plan(
    store: &CanonicalTypeMapperStore,
    union: TypeId,
    name: EscapedName,
    cache: Option<SymbolTableId>,
    cache_without_function_property_augment: Option<SymbolTableId>,
    properties: Vec<Option<SourceProperty>>,
) -> Result<UnionPropertyPlan, UnionPropertyError> {
    let mut found = Vec::new();
    found
        .try_reserve_exact(2)
        .map_err(|_| UnionPropertyError::Capacity(union))?;
    found.extend(properties.into_iter().flatten());
    let options = store
        .intrinsic_bootstrap()
        .ok_or(LiteralTypeCacheError::BootstrapUninitialized)?
        .options;
    if options.strict_null_checks
        && options.exact_optional_property_types
        && found.iter().any(|property| property.optional)
    {
        return Err(UnionPropertyError::UnsupportedExactOptionalProperty(union));
    }
    let outcome = match found.as_slice() {
        [] => PropertyOutcome::Missing,
        [property, other] if property.symbol == other.symbol => {
            PropertyOutcome::Borrowed(*property)
        }
        _ => {
            if found.len() > 2 {
                return Err(UnionPropertyError::UnsupportedUnion(union));
            }
            let partial = found.len() != 2;
            PropertyOutcome::Synthetic(synthetic_plan(union, found, partial)?)
        }
    };
    Ok(UnionPropertyPlan {
        union,
        name,
        cache,
        cache_without_function_property_augment,
        outcome,
    })
}

/// Reads only the resolved property objects admitted by `validate_union_shell`.
fn read_union_source_property(
    store: &CanonicalTypeMapperStore,
    constituent: TypeId,
    mode: UnionMemberMode,
    name: ts_binder::EscapedNameRef<'_>,
) -> Result<Option<SourceProperty>, UnionPropertyError> {
    let invalid = || RelationUnavailable::InvalidStructuredMembers(constituent);
    let structured = store
        .type_payload(constituent)
        .and_then(|record| record.data().structured())
        .ok_or_else(invalid)?;
    let properties = structured.properties.as_deref().unwrap_or_default();
    let Some(members) = structured.members else {
        return if properties.is_empty() {
            Ok(None)
        } else {
            Err(invalid().into())
        };
    };
    let members = store.symbol_table(members).ok_or_else(invalid)?;
    if members.len() != properties.len() {
        return Err(invalid().into());
    }
    let synthetic_structural = mode == UnionMemberMode::Raw
        && properties.iter().any(|property| {
            store
                .symbol(*property)
                .is_some_and(|record| record.flags().contains(SymbolFlags::TRANSIENT))
        });
    for (index, property) in properties.iter().enumerate() {
        let record = if synthetic_structural {
            super::relater::validated_synthetic_structural_property(store, constituent, *property)?
        } else {
            store
                .symbol(*property)
                .ok_or(RelationUnavailable::Symbol(*property))?
        };
        if !synthetic_structural
            && (!record.flags().contains(SymbolFlags::PROPERTY)
                || record
                    .flags()
                    .without(SymbolFlags::PROPERTY | SymbolFlags::OPTIONAL)
                    != SymbolFlags::NONE
                || record.check_flags().bits() & !CheckFlags::READONLY.bits() != 0
                || record.name().is_reserved_member_name()
                || record.name().is_private_identifier()
                || record.name().is_late_bound()
                || mode == UnionMemberMode::Raw
                    && record
                        .declarations()
                        .is_some_and(|declarations| !declarations.is_empty()))
        {
            return Err(RelationUnavailable::UnsupportedProperty(*property).into());
        }
        if properties[..index].contains(property)
            || members.get(record.name()) != Some(*property)
            || mode == UnionMemberMode::Raw && record.parent().is_some()
        {
            return Err(invalid().into());
        }
    }
    let Some(symbol) = members.get(name) else {
        return Ok(None);
    };
    let record = store.symbol(symbol).ok_or_else(invalid)?;
    let type_ = store
        .value_symbol_links(symbol)
        .and_then(|links| links.resolved_type)
        .ok_or(RelationUnavailable::UnresolvedPropertyType(symbol))?;
    validate_source_property(
        store,
        constituent,
        mode,
        ResolvedOwnProperty {
            symbol,
            type_,
            optional: record.flags().contains(SymbolFlags::OPTIONAL),
            readonly: record.check_flags().contains(CheckFlags::READONLY),
        },
        name,
    )
    .map(Some)
}

/// Proves a published union property without resolving members or writing caches.
/// The result is used only to match a source parent's member table.
pub(super) fn published_union_property_source(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    symbol: SemanticSymbolId,
) -> Result<Option<SemanticSymbolId>, UnionPropertyError> {
    let record = store
        .symbol(symbol)
        .ok_or(UnionPropertyError::InvalidProperty(symbol))?;
    let containing = store
        .value_symbol_links(symbol)
        .and_then(|links| links.containing_type);
    let containing_data = containing.and_then(|type_| store.type_payload(type_));
    // Intersections use the same check flag. Leave their own cached properties
    // to the existing display path, but reject a redirected containing type.
    if record
        .check_flags()
        .contains(CheckFlags::SYNTHETIC_PROPERTY)
        && let Some(TypeData::Intersection(data)) =
            containing_data.map(super::type_records::TypeRecord::data)
    {
        return if data
            .intersection
            .property_cache
            .and_then(|cache| store.symbol_table(cache))
            .and_then(|cache| cache.get(record.name()))
            == Some(symbol)
            && data
                .intersection
                .resolved_properties
                .as_ref()
                .is_some_and(|properties| properties.contains(&symbol))
        {
            Ok(None)
        } else {
            Err(UnionPropertyError::InvalidProperty(symbol))
        };
    }
    if !containing_data.is_some_and(|record| matches!(record.data(), TypeData::Union(_)))
        && !record
            .check_flags()
            .contains(CheckFlags::SYNTHETIC_PROPERTY)
    {
        return Ok(None);
    }
    let invalid = || UnionPropertyError::InvalidProperty(symbol);
    let union = containing.ok_or_else(invalid)?;
    let name = record.name().as_utf8().ok_or_else(invalid)?;
    let plan = plan_cached_union_property(store, union, name)?;
    let PropertyOutcome::Synthetic(synthetic) = &plan.outcome else {
        return Err(invalid());
    };
    if store.object_literal_property_clone_origin(symbol).is_some()
        || plan
            .cache
            .and_then(|cache| store.symbol_table(cache))
            .and_then(|cache| cache.get(record.name()))
            != Some(symbol)
    {
        return Err(invalid());
    }
    validate_cached_property(store, &plan, symbol)?;
    for source in &synthetic.sources {
        let Some(declaration) = source.declaration else {
            continue;
        };
        let node = host.node(declaration).ok_or_else(invalid)?;
        let owner = source.parent.ok_or_else(invalid)?;
        let Some([owner_declaration]) =
            store.symbol(owner).and_then(|record| record.declarations())
        else {
            return Err(invalid());
        };
        if !host.symbol_matches(store, declaration, source.symbol)
            || !host.symbol_matches(store, *owner_declaration, owner)
            || store.source_node_kind(declaration) != Some(node.kind)
            || host.node(*owner_declaration).is_none_or(|owner_node| {
                store.source_node_kind(*owner_declaration) != Some(owner_node.kind)
            })
            || node
                .parent
                .map(|parent| NodeRef::new(declaration.arena, declaration.file, parent))
                != Some(*owner_declaration)
        {
            return Err(invalid());
        }
    }
    Ok(Some(if synthetic.parent.is_some() {
        synthetic.sources[0].symbol
    } else {
        symbol
    }))
}

fn validate_union_shell(
    store: &CanonicalTypeMapperStore,
    union: TypeId,
) -> Result<ValidatedUnionShell, UnionPropertyError> {
    let record = store
        .type_payload(union)
        .ok_or(UnionPropertyError::InvalidUnion(union))?;
    let TypeData::Union(data) = record.data() else {
        return Err(UnionPropertyError::UnsupportedUnion(union));
    };
    if data.union.types.len() != 2 {
        return Err(UnionPropertyError::UnsupportedUnion(union));
    }
    let left_mode = classify_union_constituent(store, union, data.union.types[0])?;
    let right_mode = classify_union_constituent(store, union, data.union.types[1])?;
    if left_mode != right_mode {
        return Err(UnionPropertyError::UnsupportedUnion(union));
    }
    let mode = left_mode;
    if record.flags() != TypeFlags::UNION
        || record.object_flags() != ObjectFlags::NONE
        || record.symbol().is_some()
        || mode == UnionMemberMode::Raw && record.alias().is_some()
        || data.union.structured != StructuredTypeData::default()
        || data.union.types[0] >= data.union.types[1]
        || data.union.resolved_properties.is_some()
        || data.resolved_reduced_type.is_some()
        || data.regular_type.is_some()
        || data.origin.is_some()
        || !data.key_property_name.is_empty()
        || data.constituent_map != ConstituentMapState::Unallocated
    {
        return Err(UnionPropertyError::InvalidUnion(union));
    }
    if [
        data.union.property_cache,
        data.union.property_cache_without_function_property_augment,
    ]
    .into_iter()
    .flatten()
    .any(|cache| store.symbol_table(cache).is_none())
    {
        return Err(UnionPropertyError::InvalidCache(union));
    }
    if mode == UnionMemberMode::Declared {
        let expected_alias = match record.alias() {
            Some(alias) => Some(
                store
                    .type_alias(alias)
                    .and_then(super::type_records::TypeAlias::symbol)
                    .ok_or(UnionPropertyError::InvalidUnion(union))?,
            ),
            None => None,
        };
        store.validate_cached_union_result(union, expected_alias)?;
    }
    Ok((
        data.union.types.clone(),
        data.union.property_cache,
        data.union.property_cache_without_function_property_augment,
        mode,
    ))
}

fn classify_union_constituent(
    store: &CanonicalTypeMapperStore,
    union: TypeId,
    type_: TypeId,
) -> Result<UnionMemberMode, UnionPropertyError> {
    if validate_plain_property_object(store, type_).is_ok() {
        return Ok(UnionMemberMode::Raw);
    }
    match validate_resolved_declared_property_object(store, type_) {
        DeclaredPropertyObjectValidation::Valid(
            DeclaredPropertyObjectProof::TypeLiteral | DeclaredPropertyObjectProof::Interface,
        ) => Ok(UnionMemberMode::Declared),
        DeclaredPropertyObjectValidation::NotDeclared => {
            Err(UnionPropertyError::UnsupportedConstituent(type_))
        }
        DeclaredPropertyObjectValidation::Malformed => Err(UnionPropertyError::InvalidUnion(union)),
    }
}

fn validate_plain_property_object(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
) -> Result<(), UnionPropertyError> {
    let record = store
        .type_payload(type_)
        .ok_or(UnionPropertyError::UnsupportedConstituent(type_))?;
    let TypeData::Object(object) = record.data() else {
        return Err(UnionPropertyError::UnsupportedConstituent(type_));
    };
    if record.flags() != TypeFlags::OBJECT
        || record.object_flags() != ObjectFlags::ANONYMOUS | ObjectFlags::MEMBERS_RESOLVED
        || record.symbol().is_some()
        || record.alias().is_some()
        || object.target.is_some()
        || object.mapper.is_some()
        || object.instantiations != TypeCacheState::Unallocated
        || object.structured.constrained != ConstrainedTypeData::default()
        || object.structured.signatures.is_some()
        || object.structured.call_signature_count != 0
        || object.structured.index_infos.is_some()
        || object
            .structured
            .object_type_without_abstract_construct_signatures
            .is_some()
    {
        return Err(UnionPropertyError::UnsupportedConstituent(type_));
    }
    Ok(())
}

fn validate_source_property(
    store: &CanonicalTypeMapperStore,
    constituent: TypeId,
    mode: UnionMemberMode,
    property: ResolvedOwnProperty,
    name: ts_binder::EscapedNameRef<'_>,
) -> Result<SourceProperty, UnionPropertyError> {
    let record = store
        .symbol(property.symbol)
        .ok_or(UnionPropertyError::InvalidProperty(property.symbol))?;
    let expected_flags = SymbolFlags::PROPERTY
        | if property.optional {
            SymbolFlags::OPTIONAL
        } else {
            SymbolFlags::NONE
        };
    let expected_checks = if property.readonly {
        CheckFlags::READONLY
    } else {
        CheckFlags::NONE
    };
    if record.flags() != expected_flags
        || record.check_flags() != expected_checks
        || record.name() != name
        || record.members().is_some()
        || record.exports().is_some()
        || record.export_symbol().is_some()
        || store.get_merged_symbol(property.symbol) != Some(property.symbol)
        || store.value_symbol_links(property.symbol)
            != Some(&ValueSymbolLinks {
                resolved_type: Some(property.type_),
                ..ValueSymbolLinks::default()
            })
    {
        return Err(UnionPropertyError::InvalidProperty(property.symbol));
    }
    let (declaration, value_declaration, parent) = match mode {
        UnionMemberMode::Raw => {
            if record.declarations().is_some()
                || record.value_declaration().is_some()
                || record.parent().is_some()
            {
                return Err(UnionPropertyError::InvalidProperty(property.symbol));
            }
            (None, None, None)
        }
        UnionMemberMode::Declared => {
            let (declaration, parent) =
                validate_declared_property_provenance(store, constituent, property.symbol)?;
            (Some(declaration), Some(declaration), Some(parent))
        }
    };
    if !supported_terminal_property_type(store, property.type_) {
        return Err(UnionPropertyError::UnsupportedPropertyType(property.type_));
    }
    store.validate_union_constituent(property.type_)?;
    Ok(SourceProperty {
        symbol: property.symbol,
        raw_type: property.type_,
        optional: property.optional,
        readonly: property.readonly,
        declaration,
        value_declaration,
        parent,
    })
}

fn validate_declared_property_provenance(
    store: &CanonicalTypeMapperStore,
    constituent: TypeId,
    property: SemanticSymbolId,
) -> Result<(NodeRef, SemanticSymbolId), UnionPropertyError> {
    let record = store
        .type_payload(constituent)
        .ok_or(UnionPropertyError::InvalidProperty(property))?;
    let (structured, interface) = match record.data() {
        TypeData::Object(object) => (&object.structured, false),
        TypeData::Interface(interface) => (&interface.reference.object.structured, true),
        _ => return Err(UnionPropertyError::InvalidProperty(property)),
    };
    let owner = record
        .symbol()
        .ok_or(UnionPropertyError::InvalidProperty(property))?;
    let owner_record = store
        .symbol(owner)
        .ok_or(UnionPropertyError::InvalidProperty(property))?;
    let [owner_declaration] = owner_record.declarations().unwrap_or_default() else {
        return Err(UnionPropertyError::InvalidProperty(property));
    };
    let property_record = store
        .symbol(property)
        .ok_or(UnionPropertyError::InvalidProperty(property))?;
    let [declaration] = property_record.declarations().unwrap_or_default() else {
        return Err(UnionPropertyError::InvalidProperty(property));
    };
    let members = structured
        .members
        .ok_or(UnionPropertyError::InvalidProperty(property))?;
    let owner_matches = if interface {
        owner_record.flags() == SymbolFlags::INTERFACE
            && owner_record.name().as_utf8().is_some()
            && store.source_node_kind(*owner_declaration) == Some(SyntaxKind::InterfaceDeclaration)
    } else {
        owner_record.flags() == SymbolFlags::TYPE_LITERAL
            && owner_record.name() == InternalSymbolName::Type.as_ref()
            && store.source_node_kind(*owner_declaration) == Some(SyntaxKind::TypeLiteral)
    };
    if !owner_matches
        || owner_record.check_flags() != CheckFlags::NONE
        || owner_record.value_declaration().is_some()
        || owner_record.members() != Some(members)
        || owner_record.exports().is_some()
        || owner_record.parent().is_some()
        || owner_record.export_symbol().is_some()
        || store.get_merged_symbol(owner) != Some(owner)
        || property_record.value_declaration() != Some(*declaration)
        || property_record.parent() != Some(owner)
        || !matches!(
            store.source_node_kind(*declaration),
            Some(SyntaxKind::PropertyDeclaration | SyntaxKind::PropertySignature)
        )
        || store.source_node_parent(*declaration)
            != Some(SourceNodeParent::Parent(*owner_declaration))
        || structured
            .properties
            .as_deref()
            .is_none_or(|properties| !properties.contains(&property))
        || store
            .symbol_table(members)
            .and_then(|table| table.get(property_record.name()))
            != Some(property)
    {
        return Err(UnionPropertyError::InvalidProperty(property));
    }
    Ok((*declaration, owner))
}

fn supported_terminal_property_type(store: &CanonicalTypeMapperStore, type_: TypeId) -> bool {
    store.type_payload(type_).is_some_and(|record| {
        record.flags().intersects(
            TypeFlags::PRIMITIVE
                | TypeFlags::ANY_OR_UNKNOWN
                | TypeFlags::NEVER
                | TypeFlags::NON_PRIMITIVE
                | TypeFlags::UNION,
        )
    })
}

fn synthetic_plan(
    union: TypeId,
    sources: Vec<SourceProperty>,
    partial: bool,
) -> Result<SyntheticPropertyPlan, UnionPropertyError> {
    debug_assert!(!sources.is_empty(), "a synthetic property has a source");
    debug_assert!(
        sources.len() <= 2,
        "the exact leaf has at most two property sources"
    );
    let mut declarations = Vec::new();
    declarations
        .try_reserve_exact(sources.len())
        .map_err(|_| UnionPropertyError::Capacity(union))?;
    for source in &sources {
        if let Some(declaration) = source.declaration
            && !declarations.contains(&declaration)
        {
            declarations.push(declaration);
        }
    }
    let first_value_declaration = sources.first().and_then(|source| source.value_declaration);
    let uniform_value_declaration = first_value_declaration.is_some()
        && sources
            .iter()
            .all(|source| source.value_declaration == first_value_declaration);
    let value_declaration = uniform_value_declaration
        .then_some(first_value_declaration)
        .flatten();
    let parent = value_declaration.and_then(|_| sources.first().and_then(|source| source.parent));
    Ok(SyntheticPropertyPlan {
        optional: sources.iter().any(|source| source.optional),
        readonly: sources.iter().any(|source| source.readonly),
        sources,
        partial,
        declarations: (!declarations.is_empty()).then_some(declarations),
        value_declaration,
        parent,
    })
}

fn prepare_cold_query(
    store: &mut CanonicalTypeMapperStore,
    plan: &UnionPropertyPlan,
) -> Result<PreparedColdQuery, UnionPropertyError> {
    let table_count = usize::from(plan.cache.is_none());
    let symbol_count = usize::from(matches!(&plan.outcome, PropertyOutcome::Synthetic(_)));
    if !store.try_reserve_checker_symbol_allocations(symbol_count, table_count)
        || !store.try_reserve_value_symbol_links(symbol_count)
    {
        return Err(UnionPropertyError::Capacity(plan.union));
    }
    let cache = if plan.cache.is_none() {
        Some(PreparedSymbolTable::new(1).ok_or(UnionPropertyError::Capacity(plan.union))?)
    } else {
        None
    };
    let strict = store
        .intrinsic_bootstrap()
        .ok_or(LiteralTypeCacheError::BootstrapUninitialized)?
        .options
        .strict_null_checks;
    let union_operations = match &plan.outcome {
        PropertyOutcome::Missing => 0,
        PropertyOutcome::Borrowed(source) => usize::from(strict && source.optional),
        PropertyOutcome::Synthetic(synthetic) => {
            let optional_operations = if strict {
                synthetic
                    .sources
                    .iter()
                    .filter(|source| source.optional)
                    .count()
            } else {
                0
            };
            optional_operations
                .checked_add(1)
                .ok_or(UnionPropertyError::Capacity(plan.union))?
        }
    };
    let types = if union_operations != 0 {
        Some(store.prepare_type_query_types(&[], &[], &[], union_operations, 0)?)
    } else {
        None
    };
    Ok(PreparedColdQuery { cache, types })
}

fn publish_property_cache(
    store: &mut CanonicalTypeMapperStore,
    plan: &UnionPropertyPlan,
    prepared: PreparedSymbolTable,
) -> SymbolTableId {
    let cache = store.alloc_prepared_symbol_table(prepared);
    assert!(store.set_union_or_intersection_caches(
        plan.union,
        Some(cache),
        plan.cache_without_function_property_augment,
        None,
    ));
    cache
}

fn publish_synthetic_property(
    store: &mut CanonicalTypeMapperStore,
    plan: &UnionPropertyPlan,
    synthetic: &SyntheticPropertyPlan,
    prepared: &mut PreparedTypeQueryTypes,
) -> ResolvedUnionProperty {
    let effective = materialize_effective_types(store, synthetic, prepared);
    let check_flags = synthetic_check_flags(store, synthetic, effective.as_slice());
    let flags = SymbolFlags::PROPERTY
        | if synthetic.optional {
            SymbolFlags::OPTIONAL
        } else {
            SymbolFlags::NONE
        };
    let symbol = store.alloc_transient_symbol(flags, plan.name.clone(), check_flags);
    if synthetic.declarations.is_some() || synthetic.value_declaration.is_some() {
        assert!(store.set_symbol_declarations(
            symbol,
            synthetic.declarations.clone(),
            synthetic.value_declaration,
        ));
    }
    if synthetic.parent.is_some() {
        assert!(store.set_symbol_relationships(symbol, None, None, synthetic.parent, None,));
    }
    let type_ = store
        .literal_union_type_prepared(effective.as_slice(), None, prepared)
        .expect("a prepared terminal property union is infallible");
    assert!(store.set_value_symbol_links(
        symbol,
        ValueSymbolLinks {
            resolved_type: Some(type_),
            containing_type: Some(plan.union),
            ..ValueSymbolLinks::default()
        },
    ));
    ResolvedUnionProperty {
        symbol,
        type_,
        optional: synthetic.optional,
        readonly: synthetic.readonly,
    }
}

fn materialize_effective_types(
    store: &mut CanonicalTypeMapperStore,
    synthetic: &SyntheticPropertyPlan,
    prepared: &mut PreparedTypeQueryTypes,
) -> EffectiveTypes {
    let (strict, sentinel, filler) = {
        let bootstrap = store
            .intrinsic_bootstrap()
            .expect("a prepared property query retains bootstrap");
        (
            bootstrap.options.strict_null_checks,
            bootstrap.undefined_or_missing_type,
            bootstrap.never_type,
        )
    };
    let mut values = [filler; 2];
    for (index, source) in synthetic.sources.iter().enumerate() {
        let type_ = if strict && source.optional {
            store
                .literal_union_type_prepared(&[source.raw_type, sentinel], None, prepared)
                .expect("a prepared optional property union is infallible")
        } else {
            source.raw_type
        };
        values[index] = type_;
    }
    EffectiveTypes {
        values,
        len: synthetic.sources.len(),
    }
}

fn materialize_source_read_type(
    store: &mut CanonicalTypeMapperStore,
    source: SourceProperty,
    prepared: Option<&mut PreparedTypeQueryTypes>,
) -> TypeId {
    let (strict, sentinel) = {
        let bootstrap = store
            .intrinsic_bootstrap()
            .expect("a prepared property query retains bootstrap");
        (
            bootstrap.options.strict_null_checks,
            bootstrap.undefined_or_missing_type,
        )
    };
    if strict && source.optional {
        store
            .literal_union_type_prepared(
                &[source.raw_type, sentinel],
                None,
                prepared.expect("a strict optional source prepared its read union"),
            )
            .expect("a prepared optional property read union is infallible")
    } else {
        source.raw_type
    }
}

fn synthetic_check_flags(
    store: &CanonicalTypeMapperStore,
    synthetic: &SyntheticPropertyPlan,
    effective: &[TypeId],
) -> CheckFlags {
    let mut flags = CheckFlags::SYNTHETIC_PROPERTY | CheckFlags::CONTAINS_PUBLIC;
    if synthetic.readonly {
        flags |= CheckFlags::READONLY;
    }
    if synthetic.partial {
        flags |= CheckFlags::READ_PARTIAL;
    }
    if effective
        .first()
        .is_some_and(|first| effective.iter().any(|type_| type_ != first))
    {
        flags |= CheckFlags::HAS_NON_UNIFORM_TYPE;
    }
    if effective.iter().any(|type_| {
        store.type_payload(*type_).is_some_and(|record| {
            record
                .flags()
                .intersects(TypeFlags::UNIT | TypeFlags::BOOLEAN)
                || matches!(record.data(), TypeData::Union(union) if union.union.types.iter().all(|constituent| {
                    store.type_payload(*constituent).is_some_and(|record| record.flags().intersects(TypeFlags::UNIT))
                }))
        })
    }) {
        flags |= CheckFlags::HAS_LITERAL_TYPE;
    }
    if effective.iter().any(|type_| {
        store
            .type_payload(*type_)
            .is_some_and(|record| record.flags().intersects(TypeFlags::NEVER))
    }) {
        flags |= CheckFlags::HAS_NEVER_TYPE;
    }
    flags
}

fn validate_cached_property(
    store: &CanonicalTypeMapperStore,
    plan: &UnionPropertyPlan,
    cached: SemanticSymbolId,
) -> Result<Option<ResolvedUnionProperty>, UnionPropertyError> {
    match &plan.outcome {
        PropertyOutcome::Missing => Err(UnionPropertyError::InvalidCache(plan.union)),
        PropertyOutcome::Borrowed(source) => {
            if cached != source.symbol {
                return Err(UnionPropertyError::InvalidCache(plan.union));
            }
            let type_ = cached_source_read_type(store, plan.union, *source)?;
            Ok(Some(project_source_property(*source, type_)))
        }
        PropertyOutcome::Synthetic(synthetic) => {
            let effective = cached_effective_types(store, plan.union, synthetic)?;
            let expected_type =
                cached_terminal_union_identity(store, plan.union, effective.as_slice())?;
            let expected_flags = SymbolFlags::PROPERTY
                | SymbolFlags::TRANSIENT
                | if synthetic.optional {
                    SymbolFlags::OPTIONAL
                } else {
                    SymbolFlags::NONE
                };
            let record = store
                .symbol(cached)
                .ok_or(UnionPropertyError::InvalidCache(plan.union))?;
            if record.flags() != expected_flags
                || record.check_flags()
                    != synthetic_check_flags(store, synthetic, effective.as_slice())
                || record.name() != plan.name.as_ref()
                || record.declarations() != synthetic.declarations.as_deref()
                || record.value_declaration() != synthetic.value_declaration
                || record.parent() != synthetic.parent
                || record.members().is_some()
                || record.exports().is_some()
                || record.export_symbol().is_some()
                || store.get_merged_symbol(cached) != Some(cached)
                || store.value_symbol_links(cached)
                    != Some(&ValueSymbolLinks {
                        resolved_type: Some(expected_type),
                        containing_type: Some(plan.union),
                        ..ValueSymbolLinks::default()
                    })
            {
                return Err(UnionPropertyError::InvalidCache(plan.union));
            }
            let property = ResolvedUnionProperty {
                symbol: cached,
                type_: expected_type,
                optional: synthetic.optional,
                readonly: synthetic.readonly,
            };
            if synthetic.partial {
                Ok(None)
            } else {
                Ok(Some(property))
            }
        }
    }
}

fn cached_effective_types(
    store: &CanonicalTypeMapperStore,
    union: TypeId,
    synthetic: &SyntheticPropertyPlan,
) -> Result<EffectiveTypes, UnionPropertyError> {
    let (strict, sentinel, filler) = {
        let bootstrap = store
            .intrinsic_bootstrap()
            .ok_or(LiteralTypeCacheError::BootstrapUninitialized)?;
        (
            bootstrap.options.strict_null_checks,
            bootstrap.undefined_or_missing_type,
            bootstrap.never_type,
        )
    };
    let mut values = [filler; 2];
    for (index, source) in synthetic.sources.iter().enumerate() {
        let type_ = if strict && source.optional {
            cached_terminal_union_identity(store, union, &[source.raw_type, sentinel])?
        } else {
            source.raw_type
        };
        values[index] = type_;
    }
    Ok(EffectiveTypes {
        values,
        len: synthetic.sources.len(),
    })
}

fn cached_source_read_type(
    store: &CanonicalTypeMapperStore,
    union: TypeId,
    source: SourceProperty,
) -> Result<TypeId, UnionPropertyError> {
    let (strict, sentinel) = {
        let bootstrap = store
            .intrinsic_bootstrap()
            .ok_or(LiteralTypeCacheError::BootstrapUninitialized)?;
        (
            bootstrap.options.strict_null_checks,
            bootstrap.undefined_or_missing_type,
        )
    };
    if strict && source.optional {
        cached_terminal_union_identity(store, union, &[source.raw_type, sentinel])
    } else {
        Ok(source.raw_type)
    }
}

fn cached_terminal_union_identity(
    store: &CanonicalTypeMapperStore,
    receiver: TypeId,
    inputs: &[TypeId],
) -> Result<TypeId, UnionPropertyError> {
    let filler = store
        .intrinsic_bootstrap()
        .ok_or(LiteralTypeCacheError::BootstrapUninitialized)?
        .never_type;
    let mut flattened = [filler; 4];
    let mut flattened_len = 0usize;
    for member in inputs {
        store
            .validate_cached_union_result(*member, None)
            .map_err(|_| UnionPropertyError::InvalidCache(receiver))?;
        if let TypeData::Union(data) = store
            .type_payload(*member)
            .ok_or(UnionPropertyError::InvalidCache(receiver))?
            .data()
        {
            let end = flattened_len
                .checked_add(data.union.types.len())
                .filter(|end| *end <= flattened.len())
                .ok_or(UnionPropertyError::InvalidCache(receiver))?;
            flattened[flattened_len..end].copy_from_slice(&data.union.types);
            flattened_len = end;
        } else {
            let slot = flattened
                .get_mut(flattened_len)
                .ok_or(UnionPropertyError::InvalidCache(receiver))?;
            *slot = *member;
            flattened_len += 1;
        }
    }
    flattened[..flattened_len].sort_by_key(|member| {
        (
            store
                .type_payload(*member)
                .expect("flattened types remain store-owned")
                .flags(),
            *member,
        )
    });
    let mut unique_len = 0usize;
    for index in 0..flattened_len {
        let candidate = flattened[index];
        if unique_len == 0 || flattened[unique_len - 1] != candidate {
            flattened[unique_len] = candidate;
            unique_len += 1;
        }
    }
    let flattened = &flattened[..unique_len];
    let result = match flattened {
        [] => {
            store
                .intrinsic_bootstrap()
                .ok_or(LiteralTypeCacheError::BootstrapUninitialized)?
                .never_type
        }
        [single] => *single,
        ordered => store
            .intrinsic_bootstrap()
            .ok_or(LiteralTypeCacheError::BootstrapUninitialized)?
            .cached_union_type(ordered)
            .ok_or(UnionPropertyError::InvalidCache(receiver))?,
    };
    store
        .validate_cached_union_result(result, None)
        .map_err(|_| UnionPropertyError::InvalidCache(receiver))?;
    Ok(result)
}

const fn project_source_property(source: SourceProperty, type_: TypeId) -> ResolvedUnionProperty {
    ResolvedUnionProperty {
        symbol: source.symbol,
        type_,
        optional: source.optional,
        readonly: source.readonly,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ts_binder::SymbolData;

    use crate::semantic::{
        IntrinsicBootstrapOptions,
        mapper::TypeMapper,
        store::SemanticStore,
        type_records::{TypeRecord, UnionTypeData},
    };

    type TestStore = SemanticStore<TypeRecord, TypeMapper>;

    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
    struct State {
        types: usize,
        checker_symbols: usize,
        tables: usize,
        links: [usize; 26],
    }

    fn initialized(options: IntrinsicBootstrapOptions) -> TestStore {
        let mut store = TestStore::new();
        store.initialize_intrinsic_bootstrap(options).unwrap();
        store
    }

    fn state(store: &TestStore) -> State {
        State {
            types: store.type_len(),
            checker_symbols: store.symbol_store().checker_created_symbol_len(),
            tables: store.symbol_store().symbol_table_len(),
            links: store.checker_link_allocated_lengths(),
        }
    }

    fn alloc_property(
        store: &mut TestStore,
        name: &str,
        type_: TypeId,
        optional: bool,
        readonly: bool,
    ) -> SemanticSymbolId {
        let flags = SymbolFlags::PROPERTY
            | if optional {
                SymbolFlags::OPTIONAL
            } else {
                SymbolFlags::NONE
            };
        let symbol = store
            .alloc_symbol(SymbolData::new(flags, EscapedName::source(name)))
            .unwrap();
        if readonly {
            assert!(store.set_source_property_readonly(symbol, true));
        }
        assert!(store.set_value_symbol_links(
            symbol,
            ValueSymbolLinks {
                resolved_type: Some(type_),
                ..ValueSymbolLinks::default()
            },
        ));
        symbol
    }

    fn alloc_object(store: &mut TestStore, properties: &[SemanticSymbolId]) -> TypeId {
        let object = store
            .alloc_plain_object_type(ObjectFlags::ANONYMOUS, None)
            .unwrap();
        let members = if properties.is_empty() {
            None
        } else {
            let members = store.alloc_symbol_table();
            for property in properties {
                let name = store.symbol(*property).unwrap().name().to_owned();
                assert_eq!(store.insert_symbol(members, name, *property), Some(None));
            }
            Some(members)
        };
        assert!(store.set_structured_type_members(
            object,
            members,
            (!properties.is_empty()).then(|| properties.to_vec()),
            None,
            None,
            None,
        ));
        object
    }

    fn alloc_union(store: &mut TestStore, left: TypeId, right: TypeId) -> TypeId {
        let mut types = vec![left, right];
        types.sort();
        store.alloc_union_type(ObjectFlags::NONE, types).unwrap()
    }

    fn union_data(store: &TestStore, union: TypeId) -> &UnionTypeData {
        let TypeData::Union(data) = store.type_payload(union).unwrap().data() else {
            panic!("fixture must retain its union payload")
        };
        data
    }

    fn cached_property(store: &TestStore, union: TypeId, name: &str) -> Option<SemanticSymbolId> {
        union_data(store, union)
            .union
            .property_cache
            .and_then(|cache| store.symbol_table(cache))
            .and_then(|cache| cache.get_source(name))
    }

    fn sorted_types(store: &TestStore, mut types: Vec<TypeId>) -> Vec<TypeId> {
        types.sort_by_key(|type_| (store.type_payload(*type_).unwrap().flags(), *type_));
        types.dedup();
        types
    }

    #[test]
    fn distinct_properties_synthesize_exact_flags_type_and_warm_identity() {
        let mut store = initialized(IntrinsicBootstrapOptions::default());
        let (string, bigint) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (bootstrap.string_type, bootstrap.bigint_type)
        };
        let left_property = alloc_property(&mut store, "value", string, false, false);
        let right_property = alloc_property(&mut store, "value", bigint, true, true);
        let left = alloc_object(&mut store, &[left_property]);
        let right = alloc_object(&mut store, &[right_property]);
        let union = alloc_union(&mut store, left, right);
        let before = state(&store);

        let property = store
            .resolved_union_property(union, "value")
            .unwrap()
            .unwrap();
        assert_ne!(property.symbol, left_property);
        assert_ne!(property.symbol, right_property);
        assert!(property.optional);
        assert!(property.readonly);
        let expected_types = sorted_types(&store, vec![string, bigint]);
        assert_eq!(
            union_data(&store, property.type_).union.types,
            expected_types
        );
        assert_eq!(
            store
                .intrinsic_bootstrap()
                .unwrap()
                .cached_union_type(&expected_types),
            Some(property.type_)
        );

        let record = store.symbol(property.symbol).unwrap();
        assert_eq!(
            record.flags(),
            SymbolFlags::PROPERTY | SymbolFlags::OPTIONAL | SymbolFlags::TRANSIENT
        );
        assert_eq!(
            record.check_flags(),
            CheckFlags::SYNTHETIC_PROPERTY
                | CheckFlags::CONTAINS_PUBLIC
                | CheckFlags::READONLY
                | CheckFlags::HAS_NON_UNIFORM_TYPE
        );
        assert!(record.declarations().is_none());
        assert!(record.value_declaration().is_none());
        assert!(record.parent().is_none());
        assert_eq!(
            store.value_symbol_links(property.symbol),
            Some(&ValueSymbolLinks {
                resolved_type: Some(property.type_),
                containing_type: Some(union),
                ..ValueSymbolLinks::default()
            })
        );
        assert_eq!(
            cached_property(&store, union, "value"),
            Some(property.symbol)
        );
        let data = union_data(&store, union);
        assert!(
            data.union
                .property_cache_without_function_property_augment
                .is_none()
        );
        assert!(data.union.resolved_properties.is_none());
        let cold = state(&store);
        assert_eq!(cold.types, before.types + 1);
        assert_eq!(cold.checker_symbols, before.checker_symbols + 1);
        assert_eq!(cold.tables, before.tables + 1);

        assert_eq!(
            store.resolved_union_property(union, "value"),
            Ok(Some(property))
        );
        assert_eq!(state(&store), cold);
    }

    #[test]
    fn augmented_cache_query_preserves_and_ignores_noaugment_namespace() {
        let mut store = initialized(IntrinsicBootstrapOptions::default());
        let (string, bigint) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (bootstrap.string_type, bootstrap.bigint_type)
        };
        let left_property = alloc_property(&mut store, "value", string, false, false);
        let right_property = alloc_property(&mut store, "value", bigint, false, false);
        let left = alloc_object(&mut store, &[left_property]);
        let right = alloc_object(&mut store, &[right_property]);
        let union = alloc_union(&mut store, left, right);

        let unrelated = alloc_property(&mut store, "unrelated", string, false, false);
        let noaugment = store.alloc_symbol_table();
        assert_eq!(
            store.insert_symbol(noaugment, EscapedName::source("value"), unrelated),
            Some(None)
        );
        assert!(store.set_union_or_intersection_caches(union, None, Some(noaugment), None,));
        let before = state(&store);

        let property = store
            .resolved_union_property(union, "value")
            .unwrap()
            .unwrap();
        let data = union_data(&store, union);
        assert_eq!(
            data.union.property_cache_without_function_property_augment,
            Some(noaugment)
        );
        assert_eq!(
            store.symbol_table(noaugment).unwrap().get_source("value"),
            Some(unrelated)
        );
        assert_eq!(
            cached_property(&store, union, "value"),
            Some(property.symbol)
        );
        let cold = state(&store);
        assert_eq!(cold.tables, before.tables + 1);

        assert_eq!(
            store.resolved_union_property(union, "value"),
            Ok(Some(property))
        );
        assert_eq!(state(&store), cold);
    }

    #[test]
    fn distinct_symbols_with_one_effective_type_still_synthesize_without_nonuniform_flag() {
        let mut store = initialized(IntrinsicBootstrapOptions::default());
        let string = store.intrinsic_bootstrap().unwrap().string_type;
        let left_property = alloc_property(&mut store, "value", string, false, false);
        let right_property = alloc_property(&mut store, "value", string, false, false);
        let left = alloc_object(&mut store, &[left_property]);
        let right = alloc_object(&mut store, &[right_property]);
        let union = alloc_union(&mut store, left, right);
        let before = state(&store);

        let property = store
            .resolved_union_property(union, "value")
            .unwrap()
            .unwrap();
        assert_ne!(property.symbol, left_property);
        assert_ne!(property.symbol, right_property);
        assert_eq!(property.type_, string);
        assert_eq!(
            store.symbol(property.symbol).unwrap().check_flags(),
            CheckFlags::SYNTHETIC_PROPERTY | CheckFlags::CONTAINS_PUBLIC
        );
        let cold = state(&store);
        assert_eq!(cold.types, before.types);
        assert_eq!(cold.checker_symbols, before.checker_symbols + 1);
        assert_eq!(cold.tables, before.tables + 1);

        assert_eq!(
            store.resolved_union_property(union, "value"),
            Ok(Some(property))
        );
        assert_eq!(state(&store), cold);
    }

    #[test]
    fn strict_optional_read_type_includes_undefined_before_final_union() {
        let mut store = initialized(IntrinsicBootstrapOptions {
            strict_null_checks: true,
            exact_optional_property_types: false,
        });
        let (undefined, string, number) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (
                bootstrap.undefined_type,
                bootstrap.string_type,
                bootstrap.number_type,
            )
        };
        let required = alloc_property(&mut store, "value", number, false, false);
        let optional = alloc_property(&mut store, "value", string, true, false);
        let left = alloc_object(&mut store, &[required]);
        let right = alloc_object(&mut store, &[optional]);
        let union = alloc_union(&mut store, left, right);
        let before = state(&store);

        let property = store
            .resolved_union_property(union, "value")
            .unwrap()
            .unwrap();
        let optional_types = sorted_types(&store, vec![undefined, string]);
        let optional_type = store
            .intrinsic_bootstrap()
            .unwrap()
            .cached_union_type(&optional_types)
            .unwrap();
        assert_eq!(
            union_data(&store, optional_type).union.types,
            optional_types
        );
        let expected_types = sorted_types(&store, vec![undefined, string, number]);
        assert_eq!(
            union_data(&store, property.type_).union.types,
            expected_types
        );
        assert!(property.optional);
        assert!(
            store
                .symbol(property.symbol)
                .unwrap()
                .check_flags()
                .contains(CheckFlags::HAS_NON_UNIFORM_TYPE)
        );
        let cold = state(&store);
        assert_eq!(cold.types, before.types + 2);
        assert_eq!(
            store.resolved_union_property(union, "value"),
            Ok(Some(property))
        );
        assert_eq!(state(&store), cold);
    }

    #[test]
    fn same_symbol_is_borrowed_after_allocating_only_the_cache_table() {
        let mut store = initialized(IntrinsicBootstrapOptions::default());
        let string = store.intrinsic_bootstrap().unwrap().string_type;
        let shared = alloc_property(&mut store, "value", string, true, true);
        let left = alloc_object(&mut store, &[shared]);
        let right = alloc_object(&mut store, &[shared]);
        let union = alloc_union(&mut store, left, right);
        let before = state(&store);
        let original_links = store.value_symbol_links(shared).unwrap().clone();

        let property = store
            .resolved_union_property(union, "value")
            .unwrap()
            .unwrap();
        assert_eq!(
            property,
            ResolvedUnionProperty {
                symbol: shared,
                type_: string,
                optional: true,
                readonly: true,
            }
        );
        assert_eq!(cached_property(&store, union, "value"), Some(shared));
        assert_eq!(store.value_symbol_links(shared), Some(&original_links));
        let cold = state(&store);
        assert_eq!(cold.types, before.types);
        assert_eq!(cold.checker_symbols, before.checker_symbols);
        assert_eq!(cold.tables, before.tables + 1);
        assert_eq!(cold.links, before.links);

        assert_eq!(
            store.resolved_union_property(union, "value"),
            Ok(Some(property))
        );
        assert_eq!(state(&store), cold);
    }

    #[test]
    fn strict_optional_same_symbol_borrows_identity_but_projects_effective_read_type() {
        let mut store = initialized(IntrinsicBootstrapOptions {
            strict_null_checks: true,
            exact_optional_property_types: false,
        });
        let (undefined, string) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (bootstrap.undefined_type, bootstrap.string_type)
        };
        let shared = alloc_property(&mut store, "value", string, true, false);
        let left = alloc_object(&mut store, &[shared]);
        let right = alloc_object(&mut store, &[shared]);
        let union = alloc_union(&mut store, left, right);
        let before = state(&store);
        let original_links = store.value_symbol_links(shared).unwrap().clone();

        let property = store
            .resolved_union_property(union, "value")
            .unwrap()
            .unwrap();
        let expected_types = sorted_types(&store, vec![undefined, string]);
        assert_eq!(property.symbol, shared);
        assert_eq!(
            store
                .intrinsic_bootstrap()
                .unwrap()
                .cached_union_type(&expected_types),
            Some(property.type_)
        );
        assert_eq!(
            union_data(&store, property.type_).union.types,
            expected_types
        );
        assert!(property.optional);
        assert!(!property.readonly);
        assert_eq!(store.value_symbol_links(shared), Some(&original_links));
        assert_eq!(cached_property(&store, union, "value"), Some(shared));
        let cold = state(&store);
        assert_eq!(cold.types, before.types + 1);
        assert_eq!(cold.checker_symbols, before.checker_symbols);
        assert_eq!(cold.tables, before.tables + 1);
        assert_eq!(cold.links, before.links);

        assert_eq!(
            store.resolved_union_property(union, "value"),
            Ok(Some(property))
        );
        assert_eq!(state(&store), cold);
    }

    #[test]
    fn missing_constituent_caches_partial_but_public_lookup_filters_it() {
        let mut store = initialized(IntrinsicBootstrapOptions::default());
        let string = store.intrinsic_bootstrap().unwrap().string_type;
        let source = alloc_property(&mut store, "value", string, false, false);
        let left = alloc_object(&mut store, &[source]);
        let right = alloc_object(&mut store, &[]);
        let union = alloc_union(&mut store, left, right);

        assert_eq!(store.resolved_union_property(union, "value"), Ok(None));
        let partial = cached_property(&store, union, "value").unwrap();
        let record = store.symbol(partial).unwrap();
        assert_eq!(
            record.flags(),
            SymbolFlags::PROPERTY | SymbolFlags::TRANSIENT
        );
        assert_eq!(
            record.check_flags(),
            CheckFlags::SYNTHETIC_PROPERTY | CheckFlags::CONTAINS_PUBLIC | CheckFlags::READ_PARTIAL
        );
        assert_eq!(
            store.value_symbol_links(partial),
            Some(&ValueSymbolLinks {
                resolved_type: Some(string),
                containing_type: Some(union),
                ..ValueSymbolLinks::default()
            })
        );
        let cold = state(&store);
        assert_eq!(store.resolved_union_property(union, "value"), Ok(None));
        assert_eq!(state(&store), cold);
    }

    #[test]
    fn all_missing_still_allocates_one_empty_cache_table() {
        let mut store = initialized(IntrinsicBootstrapOptions::default());
        let left = alloc_object(&mut store, &[]);
        let right = alloc_object(&mut store, &[]);
        let union = alloc_union(&mut store, left, right);
        let before = state(&store);

        assert_eq!(store.resolved_union_property(union, "value"), Ok(None));
        assert!(union_data(&store, union).union.property_cache.is_some());
        assert_eq!(cached_property(&store, union, "value"), None);
        let cold = state(&store);
        assert_eq!(cold.types, before.types);
        assert_eq!(cold.checker_symbols, before.checker_symbols);
        assert_eq!(cold.tables, before.tables + 1);
        assert_eq!(cold.links, before.links);

        assert_eq!(store.resolved_union_property(union, "value"), Ok(None));
        assert_eq!(state(&store), cold);
    }

    #[test]
    fn raw_transient_members_preserve_absent_name_cache_publication_and_replay() {
        let mut store = initialized(IntrinsicBootstrapOptions::default());
        let number = store.intrinsic_bootstrap().unwrap().number_type;
        let objects = ["left", "right"].map(|name| {
            let property = store.alloc_transient_symbol(
                SymbolFlags::PROPERTY,
                EscapedName::source(name),
                CheckFlags::NONE,
            );
            assert!(store.set_value_symbol_links(
                property,
                ValueSymbolLinks {
                    resolved_type: Some(number),
                    ..ValueSymbolLinks::default()
                },
            ));
            alloc_object(&mut store, &[property])
        });
        let union = alloc_union(&mut store, objects[0], objects[1]);
        assert!(union_data(&store, union).union.property_cache.is_none());
        let before = state(&store);

        assert_eq!(store.resolved_union_property(union, "absent"), Ok(None));
        let cache = union_data(&store, union)
            .union
            .property_cache
            .expect("an absent-name query publishes its empty cache");
        assert!(store.symbol_table(cache).unwrap().is_empty());
        assert_eq!(cached_property(&store, union, "absent"), None);
        let cold = state(&store);
        assert_eq!(cold.types, before.types);
        assert_eq!(cold.checker_symbols, before.checker_symbols);
        assert_eq!(cold.tables, before.tables + 1);
        assert_eq!(cold.links, before.links);
        let published = union_data(&store, union).clone();

        for _ in 0..2 {
            assert_eq!(store.resolved_union_property(union, "absent"), Ok(None));
            assert_eq!(union_data(&store, union), &published);
            assert!(store.symbol_table(cache).unwrap().is_empty());
            assert_eq!(state(&store), cold);
        }
    }

    #[test]
    fn raw_and_declared_type_literal_constituents_reject_whole_union_mode_without_writes() {
        let mut store = initialized(IntrinsicBootstrapOptions::default());
        let declared = store.intrinsic_bootstrap().unwrap().empty_type_literal_type;
        let raw = alloc_object(&mut store, &[]);
        let union = alloc_union(&mut store, declared, raw);
        let before = state(&store);

        assert_eq!(
            store.resolved_union_property(union, "value"),
            Err(UnionPropertyError::UnsupportedUnion(union))
        );
        assert_eq!(state(&store), before);
        assert!(union_data(&store, union).union.property_cache.is_none());
    }

    #[test]
    fn selected_cache_poison_fails_without_scanning_unrelated_entries() {
        let mut store = initialized(IntrinsicBootstrapOptions::default());
        let (string, bigint) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (bootstrap.string_type, bootstrap.bigint_type)
        };
        let left_property = alloc_property(&mut store, "value", string, false, false);
        let right_property = alloc_property(&mut store, "value", bigint, false, false);
        let left = alloc_object(&mut store, &[left_property]);
        let right = alloc_object(&mut store, &[right_property]);
        let union = alloc_union(&mut store, left, right);
        let unrelated = alloc_property(&mut store, "poison", string, false, false);
        let cache = store.alloc_symbol_table();
        assert_eq!(
            store.insert_symbol(cache, EscapedName::source("unrelated"), unrelated),
            Some(None)
        );
        assert!(store.set_union_or_intersection_caches(union, Some(cache), None, None,));

        let property = store
            .resolved_union_property(union, "value")
            .unwrap()
            .unwrap();
        assert_eq!(
            cached_property(&store, union, "value"),
            Some(property.symbol)
        );

        let mut poisoned = initialized(IntrinsicBootstrapOptions::default());
        let (string, bigint) = {
            let bootstrap = poisoned.intrinsic_bootstrap().unwrap();
            (bootstrap.string_type, bootstrap.bigint_type)
        };
        let left_property = alloc_property(&mut poisoned, "value", string, false, false);
        let right_property = alloc_property(&mut poisoned, "value", bigint, false, false);
        let left = alloc_object(&mut poisoned, &[left_property]);
        let right = alloc_object(&mut poisoned, &[right_property]);
        let union = alloc_union(&mut poisoned, left, right);
        let wrong = alloc_property(&mut poisoned, "wrong", string, false, false);
        let cache = poisoned.alloc_symbol_table();
        assert_eq!(
            poisoned.insert_symbol(cache, EscapedName::source("value"), wrong),
            Some(None)
        );
        assert!(poisoned.set_union_or_intersection_caches(union, Some(cache), None, None,));
        let before = state(&poisoned);
        assert_eq!(
            poisoned.resolved_union_property(union, "value"),
            Err(UnionPropertyError::InvalidCache(union))
        );
        assert_eq!(state(&poisoned), before);
    }

    #[test]
    fn malformed_foreign_and_exact_optional_inputs_fail_before_writes() {
        let mut store = initialized(IntrinsicBootstrapOptions::default());
        let (string, bigint) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (bootstrap.string_type, bootstrap.bigint_type)
        };
        let left_property = alloc_property(&mut store, "value", string, false, false);
        let right_property = alloc_property(&mut store, "value", bigint, false, false);
        let left = alloc_object(&mut store, &[left_property]);
        let right = alloc_object(&mut store, &[right_property]);
        let union = store
            .alloc_union_type(ObjectFlags::NONE, vec![right, left])
            .unwrap();
        let before = state(&store);
        assert_eq!(
            store.resolved_union_property(union, "value"),
            Err(UnionPropertyError::InvalidUnion(union))
        );
        assert_eq!(state(&store), before);

        let mut foreign = initialized(IntrinsicBootstrapOptions::default());
        let string = foreign.intrinsic_bootstrap().unwrap().string_type;
        let property = alloc_property(&mut foreign, "value", string, false, false);
        let left = alloc_object(&mut foreign, &[property]);
        let right = alloc_object(&mut foreign, &[property]);
        let foreign_union = alloc_union(&mut foreign, left, right);
        let before = state(&store);
        assert_eq!(
            store.resolved_union_property(foreign_union, "value"),
            Err(UnionPropertyError::InvalidUnion(foreign_union))
        );
        assert_eq!(state(&store), before);

        let mut exact = initialized(IntrinsicBootstrapOptions {
            strict_null_checks: true,
            exact_optional_property_types: true,
        });
        let (string, bigint) = {
            let bootstrap = exact.intrinsic_bootstrap().unwrap();
            (bootstrap.string_type, bootstrap.bigint_type)
        };
        let required = alloc_property(&mut exact, "value", string, false, false);
        let optional = alloc_property(&mut exact, "value", bigint, true, false);
        let left = alloc_object(&mut exact, &[required]);
        let right = alloc_object(&mut exact, &[optional]);
        let union = alloc_union(&mut exact, left, right);
        let before = state(&exact);
        assert_eq!(
            exact.resolved_union_property(union, "value"),
            Err(UnionPropertyError::UnsupportedExactOptionalProperty(union))
        );
        assert_eq!(state(&exact), before);
    }
}
