//! Complete ID-backed payloads for typescript-go's canonical `Type` graph.
//!
//! The field inventory is pinned to `internal/checker/types.go` at
//! `dc37b5249ab60e2bbce936f71b883e6c8136167e`, especially `TypeAlias`, `Type`,
//! and the concrete `TypeData` records at lines 643-1245. Go pointer identity is
//! represented by store-branded IDs. `Option<Vec<_>>` and the explicit cache
//! states preserve nil versus allocated-empty slices/maps; vector order is
//! retained exactly.

use std::collections::BTreeSet;

use ts_ast::NodeRef;
use ts_jsnum::{Number, PseudoBigInt};

use super::{
    ids::{
        ConditionalRootId, IndexInfoId, SemanticStoreId, SemanticSymbolId, SignatureId,
        TypeAliasId, TypeId, TypeMapperId,
    },
    signatures::{IndexFlags, TupleMetadata},
    store::SemanticStore,
    types::{AccessFlags, ObjectFlags, TypeFlags},
};

/// The exact 128-bit key shape used by upstream semantic caches.
///
/// Hash construction belongs to later checker algorithms; this record only
/// preserves the complete key without substituting strings for identity.
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[repr(transparent)]
pub struct CacheHashKey(u128);

impl CacheHashKey {
    #[must_use]
    pub const fn new(value: u128) -> Self {
        Self(value)
    }

    #[must_use]
    pub const fn from_halves(high: u64, low: u64) -> Self {
        Self(((high as u128) << 64) | low as u128)
    }

    #[must_use]
    pub const fn get(self) -> u128 {
        self.0
    }

    #[must_use]
    pub const fn is_zero(self) -> bool {
        self.0 == 0
    }
}

/// One `map[CacheHashKey]*Type` entry in insertion/canonical construction order.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct TypeCacheEntry {
    pub key: CacheHashKey,
    pub value: TypeId,
}

/// Nil versus allocated state of an upstream type-instantiation map.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub enum TypeCacheState {
    #[default]
    Unallocated,
    Allocated(Vec<TypeCacheEntry>),
}

/// One unit-discriminant entry from `UnionType.constituentMap`.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ConstituentEntry {
    pub key: TypeId,
    pub value: TypeId,
}

/// Nil versus allocated state of `map[*Type]*Type`.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub enum ConstituentMapState {
    #[default]
    Unallocated,
    Allocated(Vec<ConstituentEntry>),
}

/// Literal values accepted by pinned `LiteralType.value`.
///
/// `ComputedEnum` is upstream's `nil` value for a computed enum member; it is
/// distinct from absence of a literal payload.
#[derive(Clone, Debug, PartialEq)]
pub enum LiteralValue {
    String(String),
    Number(Number),
    Boolean(bool),
    BigInt(PseudoBigInt),
    ComputedEnum,
}

/// Selects the exact regular literal link at allocation time.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum RegularLiteralLink {
    SelfType,
    Type(TypeId),
}

/// Provisional B02 symbol-table contract.
///
/// B02 has not yet supplied the canonical symbol-table owner. Until it does,
/// this minimal record preserves entry order and brands the complete table by
/// semantic store. It cannot be constructed without validating every symbol.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SemanticSymbolTable {
    store: SemanticStoreId,
    entries: Vec<(String, SemanticSymbolId)>,
}

impl SemanticSymbolTable {
    #[must_use]
    pub fn entries(&self) -> &[(String, SemanticSymbolId)] {
        &self.entries
    }

    #[must_use]
    pub fn get(&self, name: &str) -> Option<SemanticSymbolId> {
        self.entries
            .iter()
            .find_map(|(entry, symbol)| (entry == name).then_some(*symbol))
    }

    #[must_use]
    pub fn len(&self) -> usize {
        self.entries.len()
    }

    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }
}

/// Arena-owned equivalent of upstream `TypeAlias`.
#[derive(Debug, Eq, PartialEq)]
pub struct TypeAlias {
    id: TypeAliasId,
    symbol: Option<SemanticSymbolId>,
    type_arguments: Option<Vec<TypeId>>,
}

impl TypeAlias {
    #[must_use]
    pub const fn id(&self) -> TypeAliasId {
        self.id
    }

    #[must_use]
    pub const fn symbol(&self) -> Option<SemanticSymbolId> {
        self.symbol
    }

    #[must_use]
    pub fn type_arguments(&self) -> Option<&[TypeId]> {
        self.type_arguments.as_deref()
    }
}

/// Fields embedded by every constrained type.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct ConstrainedTypeData {
    pub resolved_base_constraint: Option<TypeId>,
}

/// Fields embedded by every type with members.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct StructuredTypeData {
    pub constrained: ConstrainedTypeData,
    pub members: Option<SemanticSymbolTable>,
    pub properties: Option<Vec<SemanticSymbolId>>,
    /// Call signatures followed by construct signatures, exactly as upstream.
    pub signatures: Option<Vec<SignatureId>>,
    pub call_signature_count: usize,
    pub index_infos: Option<Vec<IndexInfoId>>,
    pub object_type_without_abstract_construct_signatures: Option<TypeId>,
}

/// Fields embedded by every object type.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct ObjectTypeData {
    pub structured: StructuredTypeData,
    pub target: Option<TypeId>,
    pub mapper: Option<TypeMapperId>,
    pub instantiations: TypeCacheState,
}

/// Deferred or resolved instantiation of an interface/tuple target.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct TypeReferenceData {
    pub object: ObjectTypeData,
    pub node: Option<NodeRef>,
    pub resolved_type_arguments: Option<Vec<TypeId>>,
}

/// Originating class or interface data.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct InterfaceTypeData {
    pub reference: TypeReferenceData,
    pub all_type_parameters: Option<Vec<TypeId>>,
    pub outer_type_parameter_count: usize,
    pub this_type: Option<TypeId>,
    pub base_types_resolved: bool,
    pub declared_members_resolved: bool,
    pub resolved_base_constructor_type: Option<TypeId>,
    pub resolved_base_types: Option<Vec<TypeId>>,
    pub declared_members: Option<SemanticSymbolTable>,
    pub declared_call_signatures: Option<Vec<SignatureId>>,
    pub declared_construct_signatures: Option<Vec<SignatureId>>,
    pub declared_index_infos: Option<Vec<IndexInfoId>>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct IntrinsicTypeData {
    pub intrinsic_name: String,
}

#[derive(Clone, Debug, PartialEq)]
pub struct LiteralTypeData {
    pub value: LiteralValue,
    pub fresh_type: Option<TypeId>,
    pub regular_type: TypeId,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct UniqueEsSymbolTypeData {
    pub name: String,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TupleTypeData {
    pub interface: InterfaceTypeData,
    pub metadata: TupleMetadata,
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct InstantiationExpressionTypeData {
    pub object: ObjectTypeData,
    pub node: Option<NodeRef>,
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct MappedTypeData {
    pub object: ObjectTypeData,
    pub declaration: Option<NodeRef>,
    pub type_parameter: Option<TypeId>,
    pub constraint_type: Option<TypeId>,
    pub name_type: Option<TypeId>,
    pub template_type: Option<TypeId>,
    pub modifiers_type: Option<TypeId>,
    pub resolved_apparent_type: Option<TypeId>,
    pub contains_error: bool,
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct ReverseMappedTypeData {
    pub object: ObjectTypeData,
    pub source: Option<TypeId>,
    pub mapped_type: Option<TypeId>,
    pub constraint_type: Option<TypeId>,
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct EvolvingArrayTypeData {
    pub object: ObjectTypeData,
    pub element_type: Option<TypeId>,
    pub final_array_type: Option<TypeId>,
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct UnionOrIntersectionTypeData {
    pub structured: StructuredTypeData,
    pub types: Vec<TypeId>,
    pub property_cache: Option<SemanticSymbolTable>,
    pub property_cache_without_function_property_augment: Option<SemanticSymbolTable>,
    pub resolved_properties: Option<Vec<SemanticSymbolId>>,
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct UnionTypeData {
    pub union: UnionOrIntersectionTypeData,
    pub resolved_reduced_type: Option<TypeId>,
    pub regular_type: Option<TypeId>,
    pub origin: Option<TypeId>,
    pub key_property_name: String,
    pub constituent_map: ConstituentMapState,
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct IntersectionTypeData {
    pub intersection: UnionOrIntersectionTypeData,
    pub resolved_apparent_type: Option<TypeId>,
    pub unique_literal_filled_instantiation: Option<TypeId>,
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct TypeParameterData {
    pub constrained: ConstrainedTypeData,
    pub constraint: Option<TypeId>,
    pub target: Option<TypeId>,
    pub mapper: Option<TypeMapperId>,
    pub is_this_type: bool,
    /// Sentinel `TypeId`s preserve upstream resolving/circular/default states.
    pub resolved_default_type: Option<TypeId>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct IndexTypeData {
    pub constrained: ConstrainedTypeData,
    pub target: TypeId,
    pub index_flags: IndexFlags,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct IndexedAccessTypeData {
    pub constrained: ConstrainedTypeData,
    pub object_type: TypeId,
    pub index_type: TypeId,
    pub access_flags: AccessFlags,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TemplateLiteralTypeData {
    pub constrained: ConstrainedTypeData,
    pub texts: Vec<String>,
    pub types: Vec<TypeId>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct StringMappingTypeData {
    pub constrained: ConstrainedTypeData,
    pub target: TypeId,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SubstitutionTypeData {
    pub constrained: ConstrainedTypeData,
    pub base_type: TypeId,
    pub constraint: TypeId,
}

/// Arena-owned `ConditionalRoot`; identity is observable in upstream relation
/// recursion and therefore cannot be flattened into each conditional type.
#[derive(Debug, Eq, PartialEq)]
pub struct ConditionalRoot {
    id: ConditionalRootId,
    node: NodeRef,
    check_type: TypeId,
    extends_type: TypeId,
    is_distributive: bool,
    infer_type_parameters: Option<Vec<TypeId>>,
    outer_type_parameters: Option<Vec<TypeId>>,
    instantiations: TypeCacheState,
    alias: Option<TypeAliasId>,
}

impl ConditionalRoot {
    #[must_use]
    pub const fn id(&self) -> ConditionalRootId {
        self.id
    }

    #[must_use]
    pub const fn node(&self) -> NodeRef {
        self.node
    }

    #[must_use]
    pub const fn check_type(&self) -> TypeId {
        self.check_type
    }

    #[must_use]
    pub const fn extends_type(&self) -> TypeId {
        self.extends_type
    }

    #[must_use]
    pub const fn is_distributive(&self) -> bool {
        self.is_distributive
    }

    #[must_use]
    pub fn infer_type_parameters(&self) -> Option<&[TypeId]> {
        self.infer_type_parameters.as_deref()
    }

    #[must_use]
    pub fn outer_type_parameters(&self) -> Option<&[TypeId]> {
        self.outer_type_parameters.as_deref()
    }

    #[must_use]
    pub const fn instantiations(&self) -> &TypeCacheState {
        &self.instantiations
    }

    #[must_use]
    pub const fn alias(&self) -> Option<TypeAliasId> {
        self.alias
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ConditionalTypeData {
    pub constrained: ConstrainedTypeData,
    pub root: ConditionalRootId,
    pub check_type: TypeId,
    pub extends_type: TypeId,
    pub resolved_true_type: Option<TypeId>,
    pub resolved_false_type: Option<TypeId>,
    pub resolved_inferred_true_type: Option<TypeId>,
    pub resolved_default_constraint: Option<TypeId>,
    pub resolved_constraint_of_distributive: Option<TypeId>,
    pub mapper: Option<TypeMapperId>,
    pub combined_mapper: Option<TypeMapperId>,
}

/// Complete concrete payload alternatives for pinned `Type.data`.
#[derive(Debug, PartialEq)]
pub enum TypeData {
    Intrinsic(IntrinsicTypeData),
    Literal(LiteralTypeData),
    UniqueEsSymbol(UniqueEsSymbolTypeData),
    Object(ObjectTypeData),
    TypeReference(TypeReferenceData),
    Interface(InterfaceTypeData),
    Tuple(TupleTypeData),
    InstantiationExpression(InstantiationExpressionTypeData),
    Mapped(MappedTypeData),
    ReverseMapped(ReverseMappedTypeData),
    EvolvingArray(EvolvingArrayTypeData),
    Union(UnionTypeData),
    Intersection(IntersectionTypeData),
    TypeParameter(TypeParameterData),
    Index(IndexTypeData),
    IndexedAccess(IndexedAccessTypeData),
    TemplateLiteral(TemplateLiteralTypeData),
    StringMapping(StringMappingTypeData),
    Substitution(SubstitutionTypeData),
    Conditional(ConditionalTypeData),
}

/// Stable discriminator for all canonical `TypeData` implementations.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum TypeDataKind {
    Intrinsic,
    Literal,
    UniqueEsSymbol,
    Object,
    TypeReference,
    Interface,
    Tuple,
    InstantiationExpression,
    Mapped,
    ReverseMapped,
    EvolvingArray,
    Union,
    Intersection,
    TypeParameter,
    Index,
    IndexedAccess,
    TemplateLiteral,
    StringMapping,
    Substitution,
    Conditional,
}

impl TypeData {
    #[must_use]
    pub const fn kind(&self) -> TypeDataKind {
        match self {
            Self::Intrinsic(_) => TypeDataKind::Intrinsic,
            Self::Literal(_) => TypeDataKind::Literal,
            Self::UniqueEsSymbol(_) => TypeDataKind::UniqueEsSymbol,
            Self::Object(_) => TypeDataKind::Object,
            Self::TypeReference(_) => TypeDataKind::TypeReference,
            Self::Interface(_) => TypeDataKind::Interface,
            Self::Tuple(_) => TypeDataKind::Tuple,
            Self::InstantiationExpression(_) => TypeDataKind::InstantiationExpression,
            Self::Mapped(_) => TypeDataKind::Mapped,
            Self::ReverseMapped(_) => TypeDataKind::ReverseMapped,
            Self::EvolvingArray(_) => TypeDataKind::EvolvingArray,
            Self::Union(_) => TypeDataKind::Union,
            Self::Intersection(_) => TypeDataKind::Intersection,
            Self::TypeParameter(_) => TypeDataKind::TypeParameter,
            Self::Index(_) => TypeDataKind::Index,
            Self::IndexedAccess(_) => TypeDataKind::IndexedAccess,
            Self::TemplateLiteral(_) => TypeDataKind::TemplateLiteral,
            Self::StringMapping(_) => TypeDataKind::StringMapping,
            Self::Substitution(_) => TypeDataKind::Substitution,
            Self::Conditional(_) => TypeDataKind::Conditional,
        }
    }

    fn constrained_mut(&mut self) -> Option<&mut ConstrainedTypeData> {
        match self {
            Self::Object(data) => Some(&mut data.structured.constrained),
            Self::TypeReference(data) => Some(&mut data.object.structured.constrained),
            Self::Interface(data) => Some(&mut data.reference.object.structured.constrained),
            Self::Tuple(data) => Some(&mut data.interface.reference.object.structured.constrained),
            Self::InstantiationExpression(data) => Some(&mut data.object.structured.constrained),
            Self::Mapped(data) => Some(&mut data.object.structured.constrained),
            Self::ReverseMapped(data) => Some(&mut data.object.structured.constrained),
            Self::EvolvingArray(data) => Some(&mut data.object.structured.constrained),
            Self::Union(data) => Some(&mut data.union.structured.constrained),
            Self::Intersection(data) => Some(&mut data.intersection.structured.constrained),
            Self::TypeParameter(data) => Some(&mut data.constrained),
            Self::Index(data) => Some(&mut data.constrained),
            Self::IndexedAccess(data) => Some(&mut data.constrained),
            Self::TemplateLiteral(data) => Some(&mut data.constrained),
            Self::StringMapping(data) => Some(&mut data.constrained),
            Self::Substitution(data) => Some(&mut data.constrained),
            Self::Conditional(data) => Some(&mut data.constrained),
            Self::Intrinsic(_) | Self::Literal(_) | Self::UniqueEsSymbol(_) => None,
        }
    }

    fn structured_mut(&mut self) -> Option<&mut StructuredTypeData> {
        match self {
            Self::Object(data) => Some(&mut data.structured),
            Self::TypeReference(data) => Some(&mut data.object.structured),
            Self::Interface(data) => Some(&mut data.reference.object.structured),
            Self::Tuple(data) => Some(&mut data.interface.reference.object.structured),
            Self::InstantiationExpression(data) => Some(&mut data.object.structured),
            Self::Mapped(data) => Some(&mut data.object.structured),
            Self::ReverseMapped(data) => Some(&mut data.object.structured),
            Self::EvolvingArray(data) => Some(&mut data.object.structured),
            Self::Union(data) => Some(&mut data.union.structured),
            Self::Intersection(data) => Some(&mut data.intersection.structured),
            _ => None,
        }
    }

    fn object_mut(&mut self) -> Option<&mut ObjectTypeData> {
        match self {
            Self::Object(data) => Some(data),
            Self::TypeReference(data) => Some(&mut data.object),
            Self::Interface(data) => Some(&mut data.reference.object),
            Self::Tuple(data) => Some(&mut data.interface.reference.object),
            Self::InstantiationExpression(data) => Some(&mut data.object),
            Self::Mapped(data) => Some(&mut data.object),
            Self::ReverseMapped(data) => Some(&mut data.object),
            Self::EvolvingArray(data) => Some(&mut data.object),
            _ => None,
        }
    }

    fn reference_mut(&mut self) -> Option<&mut TypeReferenceData> {
        match self {
            Self::TypeReference(data) => Some(data),
            Self::Interface(data) => Some(&mut data.reference),
            Self::Tuple(data) => Some(&mut data.interface.reference),
            _ => None,
        }
    }

    fn interface_mut(&mut self) -> Option<&mut InterfaceTypeData> {
        match self {
            Self::Interface(data) => Some(data),
            Self::Tuple(data) => Some(&mut data.interface),
            _ => None,
        }
    }
}

/// Store-owned canonical type record. `checker *Checker` is represented by the
/// owning [`SemanticStore`], not by a second pointer inside every record.
#[derive(Debug, PartialEq)]
pub struct TypeRecord {
    id: TypeId,
    flags: TypeFlags,
    object_flags: ObjectFlags,
    symbol: Option<SemanticSymbolId>,
    alias: Option<TypeAliasId>,
    data: TypeData,
}

impl TypeRecord {
    #[must_use]
    pub const fn id(&self) -> TypeId {
        self.id
    }

    #[must_use]
    pub const fn flags(&self) -> TypeFlags {
        self.flags
    }

    #[must_use]
    pub const fn object_flags(&self) -> ObjectFlags {
        self.object_flags
    }

    #[must_use]
    pub const fn symbol(&self) -> Option<SemanticSymbolId> {
        self.symbol
    }

    #[must_use]
    pub const fn alias(&self) -> Option<TypeAliasId> {
        self.alias
    }

    #[must_use]
    pub const fn data(&self) -> &TypeData {
        &self.data
    }
}

/// Canonical store specialization used by subsequent type-checker modules.
pub type CanonicalSemanticStore<SymbolPayload, MapperPayload> =
    SemanticStore<TypeRecord, SymbolPayload, MapperPayload>;

impl<SymbolPayload, MapperPayload> SemanticStore<TypeRecord, SymbolPayload, MapperPayload> {
    fn alloc_record(
        &mut self,
        flags: TypeFlags,
        object_flags: ObjectFlags,
        symbol: Option<SemanticSymbolId>,
        make_data: impl FnOnce(TypeId) -> TypeData,
    ) -> Option<TypeId> {
        if !self.valid_record_symbol(symbol) {
            return None;
        }
        Some(self.alloc_type_with(|id| TypeRecord {
            id,
            flags,
            object_flags: object_flags.normalized_for_new_type(),
            symbol,
            alias: None,
            data: make_data(id),
        }))
    }

    #[must_use]
    pub fn type_alias(&self, id: TypeAliasId) -> Option<&TypeAlias> {
        self.type_alias_payload(id)
    }

    #[must_use]
    pub fn type_alias_len(&self) -> usize {
        self.type_alias_len_internal()
    }

    /// Allocates the identity-bearing shell first so alias arguments may later
    /// form recursive type graphs.
    pub fn alloc_type_alias(&mut self, symbol: Option<SemanticSymbolId>) -> Option<TypeAliasId> {
        if !self.valid_record_symbol(symbol) {
            return None;
        }
        Some(self.alloc_type_alias_with(|id| TypeAlias {
            id,
            symbol,
            type_arguments: None,
        }))
    }

    pub fn set_type_alias_arguments(
        &mut self,
        alias: TypeAliasId,
        type_arguments: Option<Vec<TypeId>>,
    ) -> bool {
        if self.type_alias_payload(alias).is_none()
            || !self.valid_optional_record_types(type_arguments.as_deref())
        {
            return false;
        }
        let Some(record) = self.type_alias_payload_mut(alias) else {
            return false;
        };
        record.type_arguments = type_arguments;
        true
    }

    /// Constructs the provisional B02 symbol table after validating store
    /// provenance and rejecting duplicate escaped names.
    #[must_use]
    pub fn create_semantic_symbol_table(
        &self,
        entries: Vec<(String, SemanticSymbolId)>,
    ) -> Option<SemanticSymbolTable> {
        let mut names = BTreeSet::new();
        if entries.iter().any(|(name, symbol)| {
            !names.insert(name.as_str()) || self.symbol_payload(*symbol).is_none()
        }) {
            return None;
        }
        Some(SemanticSymbolTable {
            store: self.id(),
            entries,
        })
    }

    #[must_use]
    pub fn conditional_root(&self, id: ConditionalRootId) -> Option<&ConditionalRoot> {
        self.conditional_root_payload(id)
    }

    #[must_use]
    pub fn conditional_root_len(&self) -> usize {
        self.conditional_root_len_internal()
    }

    #[allow(clippy::too_many_arguments)] // Mirrors the complete upstream record.
    pub fn alloc_conditional_root(
        &mut self,
        node: NodeRef,
        check_type: TypeId,
        extends_type: TypeId,
        is_distributive: bool,
        infer_type_parameters: Option<Vec<TypeId>>,
        outer_type_parameters: Option<Vec<TypeId>>,
        alias: Option<TypeAliasId>,
    ) -> Option<ConditionalRootId> {
        if !self.contains_node_ref(node)
            || !self.valid_record_type(check_type)
            || !self.valid_record_type(extends_type)
            || !self.valid_optional_record_types(infer_type_parameters.as_deref())
            || !self.valid_optional_record_types(outer_type_parameters.as_deref())
            || !self.valid_record_alias(alias)
        {
            return None;
        }
        Some(self.alloc_conditional_root_with(|id| ConditionalRoot {
            id,
            node,
            check_type,
            extends_type,
            is_distributive,
            infer_type_parameters,
            outer_type_parameters,
            instantiations: TypeCacheState::Unallocated,
            alias,
        }))
    }

    pub fn set_conditional_root_instantiations(
        &mut self,
        root: ConditionalRootId,
        instantiations: TypeCacheState,
    ) -> bool {
        if self.conditional_root_payload(root).is_none() || !self.valid_type_cache(&instantiations)
        {
            return false;
        }
        let Some(record) = self.conditional_root_payload_mut(root) else {
            return false;
        };
        record.instantiations = instantiations;
        true
    }

    pub fn set_conditional_root_alias(
        &mut self,
        root: ConditionalRootId,
        alias: Option<TypeAliasId>,
    ) -> bool {
        if self.conditional_root_payload(root).is_none() || !self.valid_record_alias(alias) {
            return false;
        }
        let Some(record) = self.conditional_root_payload_mut(root) else {
            return false;
        };
        record.alias = alias;
        true
    }

    pub fn alloc_intrinsic_type(
        &mut self,
        flags: TypeFlags,
        intrinsic_name: impl Into<String>,
    ) -> TypeId {
        self.alloc_intrinsic_type_ex(flags, intrinsic_name, ObjectFlags::NONE)
    }

    pub fn alloc_intrinsic_type_ex(
        &mut self,
        flags: TypeFlags,
        intrinsic_name: impl Into<String>,
        object_flags: ObjectFlags,
    ) -> TypeId {
        let intrinsic_name = intrinsic_name.into();
        self.alloc_type_with(|id| TypeRecord {
            id,
            flags,
            object_flags: object_flags.normalized_for_new_type(),
            symbol: None,
            alias: None,
            data: TypeData::Intrinsic(IntrinsicTypeData { intrinsic_name }),
        })
    }

    pub fn alloc_literal_type(
        &mut self,
        flags: TypeFlags,
        value: LiteralValue,
        regular_type: RegularLiteralLink,
    ) -> Option<TypeId> {
        if let RegularLiteralLink::Type(regular_type) = regular_type
            && !self.valid_record_type(regular_type)
        {
            return None;
        }
        self.alloc_record(flags, ObjectFlags::NONE, None, |id| {
            TypeData::Literal(LiteralTypeData {
                value,
                fresh_type: None,
                regular_type: match regular_type {
                    RegularLiteralLink::SelfType => id,
                    RegularLiteralLink::Type(regular_type) => regular_type,
                },
            })
        })
    }

    pub fn alloc_unique_es_symbol_type(
        &mut self,
        symbol: Option<SemanticSymbolId>,
        name: impl Into<String>,
    ) -> Option<TypeId> {
        let name = name.into();
        self.alloc_record(
            TypeFlags::UNIQUE_ES_SYMBOL,
            ObjectFlags::NONE,
            symbol,
            |_| TypeData::UniqueEsSymbol(UniqueEsSymbolTypeData { name }),
        )
    }

    pub fn alloc_plain_object_type(
        &mut self,
        object_flags: ObjectFlags,
        symbol: Option<SemanticSymbolId>,
    ) -> Option<TypeId> {
        if !object_flags.intersects(ObjectFlags::ANONYMOUS)
            || !Self::object_kind_matches(
                object_flags,
                ObjectFlags::ANONYMOUS | ObjectFlags::SINGLE_SIGNATURE_TYPE,
            )
        {
            return None;
        }
        self.alloc_record(TypeFlags::OBJECT, object_flags, symbol, |_| {
            TypeData::Object(ObjectTypeData::default())
        })
    }

    pub fn alloc_type_reference(
        &mut self,
        object_flags: ObjectFlags,
        symbol: Option<SemanticSymbolId>,
    ) -> Option<TypeId> {
        if !Self::object_kind_matches(object_flags, ObjectFlags::REFERENCE) {
            return None;
        }
        self.alloc_record(
            TypeFlags::OBJECT,
            object_flags | ObjectFlags::REFERENCE,
            symbol,
            |_| TypeData::TypeReference(TypeReferenceData::default()),
        )
    }

    pub fn alloc_interface_type(
        &mut self,
        object_flags: ObjectFlags,
        symbol: Option<SemanticSymbolId>,
    ) -> Option<TypeId> {
        if !object_flags.intersects(ObjectFlags::CLASS_OR_INTERFACE)
            || !Self::object_kind_matches(
                object_flags,
                ObjectFlags::CLASS_OR_INTERFACE | ObjectFlags::REFERENCE,
            )
        {
            return None;
        }
        self.alloc_record(TypeFlags::OBJECT, object_flags, symbol, |_| {
            TypeData::Interface(InterfaceTypeData::default())
        })
    }

    pub fn alloc_tuple_type(
        &mut self,
        object_flags: ObjectFlags,
        symbol: Option<SemanticSymbolId>,
        metadata: TupleMetadata,
    ) -> Option<TypeId> {
        if !Self::object_kind_matches(object_flags, ObjectFlags::REFERENCE | ObjectFlags::TUPLE)
            || metadata.element_infos().iter().any(|element| {
                element
                    .labeled_declaration()
                    .is_some_and(|node| !self.contains_node_ref(node))
            })
        {
            return None;
        }
        self.alloc_record(
            TypeFlags::OBJECT,
            object_flags | ObjectFlags::REFERENCE | ObjectFlags::TUPLE,
            symbol,
            |_| {
                TypeData::Tuple(TupleTypeData {
                    interface: InterfaceTypeData::default(),
                    metadata,
                })
            },
        )
    }

    pub fn alloc_instantiation_expression_type(
        &mut self,
        object_flags: ObjectFlags,
        symbol: Option<SemanticSymbolId>,
        node: Option<NodeRef>,
    ) -> Option<TypeId> {
        if !self.valid_record_node(node)
            || !Self::object_kind_matches(
                object_flags,
                ObjectFlags::ANONYMOUS | ObjectFlags::INSTANTIATION_EXPRESSION_TYPE,
            )
        {
            return None;
        }
        self.alloc_record(
            TypeFlags::OBJECT,
            object_flags | ObjectFlags::ANONYMOUS | ObjectFlags::INSTANTIATION_EXPRESSION_TYPE,
            symbol,
            |_| {
                TypeData::InstantiationExpression(InstantiationExpressionTypeData {
                    object: ObjectTypeData::default(),
                    node,
                })
            },
        )
    }

    pub fn alloc_mapped_type(
        &mut self,
        object_flags: ObjectFlags,
        symbol: Option<SemanticSymbolId>,
        declaration: Option<NodeRef>,
    ) -> Option<TypeId> {
        if !self.valid_record_node(declaration)
            || !Self::object_kind_matches(object_flags, ObjectFlags::MAPPED)
        {
            return None;
        }
        self.alloc_record(
            TypeFlags::OBJECT,
            object_flags | ObjectFlags::MAPPED,
            symbol,
            |_| {
                TypeData::Mapped(MappedTypeData {
                    declaration,
                    ..MappedTypeData::default()
                })
            },
        )
    }

    pub fn alloc_reverse_mapped_type(
        &mut self,
        object_flags: ObjectFlags,
        symbol: Option<SemanticSymbolId>,
    ) -> Option<TypeId> {
        if !Self::object_kind_matches(
            object_flags,
            ObjectFlags::ANONYMOUS | ObjectFlags::REVERSE_MAPPED,
        ) {
            return None;
        }
        self.alloc_record(
            TypeFlags::OBJECT,
            object_flags | ObjectFlags::ANONYMOUS | ObjectFlags::REVERSE_MAPPED,
            symbol,
            |_| TypeData::ReverseMapped(ReverseMappedTypeData::default()),
        )
    }

    pub fn alloc_evolving_array_type(
        &mut self,
        object_flags: ObjectFlags,
        symbol: Option<SemanticSymbolId>,
    ) -> Option<TypeId> {
        if !Self::object_kind_matches(object_flags, ObjectFlags::EVOLVING_ARRAY) {
            return None;
        }
        self.alloc_record(
            TypeFlags::OBJECT,
            object_flags | ObjectFlags::EVOLVING_ARRAY,
            symbol,
            |_| TypeData::EvolvingArray(EvolvingArrayTypeData::default()),
        )
    }

    pub fn alloc_union_type(
        &mut self,
        object_flags: ObjectFlags,
        types: Vec<TypeId>,
    ) -> Option<TypeId> {
        if !self.valid_record_types(&types) {
            return None;
        }
        self.alloc_record(TypeFlags::UNION, object_flags, None, |_| {
            TypeData::Union(UnionTypeData {
                union: UnionOrIntersectionTypeData {
                    types,
                    ..UnionOrIntersectionTypeData::default()
                },
                ..UnionTypeData::default()
            })
        })
    }

    pub fn alloc_intersection_type(
        &mut self,
        object_flags: ObjectFlags,
        types: Vec<TypeId>,
    ) -> Option<TypeId> {
        if !self.valid_record_types(&types) {
            return None;
        }
        self.alloc_record(TypeFlags::INTERSECTION, object_flags, None, |_| {
            TypeData::Intersection(IntersectionTypeData {
                intersection: UnionOrIntersectionTypeData {
                    types,
                    ..UnionOrIntersectionTypeData::default()
                },
                ..IntersectionTypeData::default()
            })
        })
    }

    pub fn alloc_type_parameter(&mut self, symbol: Option<SemanticSymbolId>) -> Option<TypeId> {
        self.alloc_record(TypeFlags::TYPE_PARAMETER, ObjectFlags::NONE, symbol, |_| {
            TypeData::TypeParameter(TypeParameterData::default())
        })
    }

    pub fn alloc_index_type(&mut self, target: TypeId, index_flags: IndexFlags) -> Option<TypeId> {
        if !self.valid_record_type(target) {
            return None;
        }
        self.alloc_record(TypeFlags::INDEX, ObjectFlags::NONE, None, |_| {
            TypeData::Index(IndexTypeData {
                constrained: ConstrainedTypeData::default(),
                target,
                index_flags,
            })
        })
    }

    pub fn alloc_indexed_access_type(
        &mut self,
        object_type: TypeId,
        index_type: TypeId,
        access_flags: AccessFlags,
    ) -> Option<TypeId> {
        if !self.valid_record_type(object_type)
            || !self.valid_record_type(index_type)
            || access_flags.bits() & !AccessFlags::PERSISTENT.bits() != 0
        {
            return None;
        }
        self.alloc_record(TypeFlags::INDEXED_ACCESS, ObjectFlags::NONE, None, |_| {
            TypeData::IndexedAccess(IndexedAccessTypeData {
                constrained: ConstrainedTypeData::default(),
                object_type,
                index_type,
                access_flags,
            })
        })
    }

    pub fn alloc_template_literal_type(
        &mut self,
        texts: Vec<String>,
        types: Vec<TypeId>,
    ) -> Option<TypeId> {
        if types.is_empty() || texts.len() != types.len() + 1 || !self.valid_record_types(&types) {
            return None;
        }
        self.alloc_record(TypeFlags::TEMPLATE_LITERAL, ObjectFlags::NONE, None, |_| {
            TypeData::TemplateLiteral(TemplateLiteralTypeData {
                constrained: ConstrainedTypeData::default(),
                texts,
                types,
            })
        })
    }

    pub fn alloc_string_mapping_type(
        &mut self,
        symbol: Option<SemanticSymbolId>,
        target: TypeId,
    ) -> Option<TypeId> {
        if !self.valid_record_type(target) {
            return None;
        }
        self.alloc_record(TypeFlags::STRING_MAPPING, ObjectFlags::NONE, symbol, |_| {
            TypeData::StringMapping(StringMappingTypeData {
                constrained: ConstrainedTypeData::default(),
                target,
            })
        })
    }

    pub fn alloc_substitution_type(
        &mut self,
        base_type: TypeId,
        constraint: TypeId,
    ) -> Option<TypeId> {
        if !self.valid_record_type(base_type) || !self.valid_record_type(constraint) {
            return None;
        }
        self.alloc_record(TypeFlags::SUBSTITUTION, ObjectFlags::NONE, None, |_| {
            TypeData::Substitution(SubstitutionTypeData {
                constrained: ConstrainedTypeData::default(),
                base_type,
                constraint,
            })
        })
    }

    pub fn alloc_conditional_type(
        &mut self,
        root: ConditionalRootId,
        check_type: TypeId,
        extends_type: TypeId,
        mapper: Option<TypeMapperId>,
        combined_mapper: Option<TypeMapperId>,
    ) -> Option<TypeId> {
        if self.conditional_root_payload(root).is_none()
            || !self.valid_record_type(check_type)
            || !self.valid_record_type(extends_type)
            || !self.valid_record_mapper(mapper)
            || !self.valid_record_mapper(combined_mapper)
        {
            return None;
        }
        self.alloc_record(TypeFlags::CONDITIONAL, ObjectFlags::NONE, None, |_| {
            TypeData::Conditional(ConditionalTypeData {
                constrained: ConstrainedTypeData::default(),
                root,
                check_type,
                extends_type,
                resolved_true_type: None,
                resolved_false_type: None,
                resolved_inferred_true_type: None,
                resolved_default_constraint: None,
                resolved_constraint_of_distributive: None,
                mapper,
                combined_mapper,
            })
        })
    }

    pub fn set_type_object_flags(&mut self, id: TypeId, object_flags: ObjectFlags) -> bool {
        let Some(record) = self.type_payload_mut(id) else {
            return false;
        };
        record.object_flags = object_flags;
        true
    }

    pub fn set_type_symbol(&mut self, id: TypeId, symbol: Option<SemanticSymbolId>) -> bool {
        if !self.valid_record_symbol(symbol) {
            return false;
        }
        let Some(record) = self.type_payload_mut(id) else {
            return false;
        };
        record.symbol = symbol;
        true
    }

    pub fn set_type_alias(&mut self, id: TypeId, alias: Option<TypeAliasId>) -> bool {
        if !self.valid_record_alias(alias) {
            return false;
        }
        let Some(record) = self.type_payload_mut(id) else {
            return false;
        };
        record.alias = alias;
        true
    }

    pub fn set_resolved_base_constraint(&mut self, id: TypeId, constraint: Option<TypeId>) -> bool {
        if !self.valid_optional_record_type(constraint) {
            return false;
        }
        let Some(constrained) = self
            .type_payload_mut(id)
            .and_then(|record| record.data.constrained_mut())
        else {
            return false;
        };
        constrained.resolved_base_constraint = constraint;
        true
    }

    #[allow(clippy::too_many_arguments)] // Mirrors setStructuredTypeMembers and its derived properties.
    pub fn set_structured_type_members(
        &mut self,
        id: TypeId,
        members: Option<SemanticSymbolTable>,
        properties: Option<Vec<SemanticSymbolId>>,
        call_signatures: Option<Vec<SignatureId>>,
        construct_signatures: Option<Vec<SignatureId>>,
        index_infos: Option<Vec<IndexInfoId>>,
    ) -> bool {
        if !self.valid_symbol_table(members.as_ref())
            || !self.valid_optional_record_symbols(properties.as_deref())
            || !self.valid_optional_record_signatures(call_signatures.as_deref())
            || !self.valid_optional_record_signatures(construct_signatures.as_deref())
            || !self.valid_optional_record_index_infos(index_infos.as_deref())
        {
            return false;
        }
        let call_count = call_signatures.as_ref().map_or(0, Vec::len);
        let signatures = match (call_signatures, construct_signatures) {
            (None, None) => None,
            (Some(call), None) if call.is_empty() => None,
            (None, Some(construct)) if construct.is_empty() => None,
            (Some(call), Some(construct)) if call.is_empty() && construct.is_empty() => None,
            (call, construct) => Some(
                call.into_iter()
                    .flatten()
                    .chain(construct.into_iter().flatten())
                    .collect(),
            ),
        };
        let Some(record) = self.type_payload_mut(id) else {
            return false;
        };
        let Some(structured) = record.data.structured_mut() else {
            return false;
        };
        structured.members = members;
        structured.properties = properties;
        structured.signatures = signatures;
        structured.call_signature_count = call_count;
        structured.index_infos = index_infos;
        record.object_flags |= ObjectFlags::MEMBERS_RESOLVED;
        true
    }

    pub fn set_object_type_without_abstract_construct_signatures(
        &mut self,
        id: TypeId,
        value: Option<TypeId>,
    ) -> bool {
        if !self.valid_optional_record_type(value) {
            return false;
        }
        let Some(structured) = self
            .type_payload_mut(id)
            .and_then(|record| record.data.structured_mut())
        else {
            return false;
        };
        structured.object_type_without_abstract_construct_signatures = value;
        true
    }

    pub fn set_object_target_and_mapper(
        &mut self,
        id: TypeId,
        target: Option<TypeId>,
        mapper: Option<TypeMapperId>,
    ) -> bool {
        if !self.valid_optional_record_type(target) || !self.valid_record_mapper(mapper) {
            return false;
        }
        let Some(object) = self
            .type_payload_mut(id)
            .and_then(|record| record.data.object_mut())
        else {
            return false;
        };
        object.target = target;
        object.mapper = mapper;
        true
    }

    pub fn set_object_instantiations(
        &mut self,
        id: TypeId,
        instantiations: TypeCacheState,
    ) -> bool {
        if !self.valid_type_cache(&instantiations) {
            return false;
        }
        let Some(object) = self
            .type_payload_mut(id)
            .and_then(|record| record.data.object_mut())
        else {
            return false;
        };
        object.instantiations = instantiations;
        true
    }

    pub fn set_type_reference_resolution(
        &mut self,
        id: TypeId,
        node: Option<NodeRef>,
        resolved_type_arguments: Option<Vec<TypeId>>,
    ) -> bool {
        if !self.valid_record_node(node)
            || !self.valid_optional_record_types(resolved_type_arguments.as_deref())
        {
            return false;
        }
        let Some(reference) = self
            .type_payload_mut(id)
            .and_then(|record| record.data.reference_mut())
        else {
            return false;
        };
        reference.node = node;
        reference.resolved_type_arguments = resolved_type_arguments;
        true
    }

    pub fn set_interface_type_parameters(
        &mut self,
        id: TypeId,
        all_type_parameters: Option<Vec<TypeId>>,
        outer_type_parameter_count: usize,
        this_type: Option<TypeId>,
    ) -> bool {
        if !self.valid_optional_record_types(all_type_parameters.as_deref())
            || !self.valid_optional_record_type(this_type)
            || outer_type_parameter_count > all_type_parameters.as_ref().map_or(0, Vec::len)
            || all_type_parameters.as_ref().is_some_and(|parameters| {
                this_type.is_some() && parameters.last().copied() != this_type
            })
        {
            return false;
        }
        let Some(interface) = self
            .type_payload_mut(id)
            .and_then(|record| record.data.interface_mut())
        else {
            return false;
        };
        interface.all_type_parameters = all_type_parameters;
        interface.outer_type_parameter_count = outer_type_parameter_count;
        interface.this_type = this_type;
        true
    }

    pub fn set_interface_base_resolution(
        &mut self,
        id: TypeId,
        base_types_resolved: bool,
        resolved_base_constructor_type: Option<TypeId>,
        resolved_base_types: Option<Vec<TypeId>>,
    ) -> bool {
        if !self.valid_optional_record_type(resolved_base_constructor_type)
            || !self.valid_optional_record_types(resolved_base_types.as_deref())
        {
            return false;
        }
        let Some(interface) = self
            .type_payload_mut(id)
            .and_then(|record| record.data.interface_mut())
        else {
            return false;
        };
        interface.base_types_resolved = base_types_resolved;
        interface.resolved_base_constructor_type = resolved_base_constructor_type;
        interface.resolved_base_types = resolved_base_types;
        true
    }

    #[allow(clippy::too_many_arguments)] // Mirrors the declared-member caches exactly.
    pub fn set_interface_declared_members(
        &mut self,
        id: TypeId,
        resolved: bool,
        members: Option<SemanticSymbolTable>,
        call_signatures: Option<Vec<SignatureId>>,
        construct_signatures: Option<Vec<SignatureId>>,
        index_infos: Option<Vec<IndexInfoId>>,
    ) -> bool {
        if !self.valid_symbol_table(members.as_ref())
            || !self.valid_optional_record_signatures(call_signatures.as_deref())
            || !self.valid_optional_record_signatures(construct_signatures.as_deref())
            || !self.valid_optional_record_index_infos(index_infos.as_deref())
        {
            return false;
        }
        let Some(interface) = self
            .type_payload_mut(id)
            .and_then(|record| record.data.interface_mut())
        else {
            return false;
        };
        interface.declared_members_resolved = resolved;
        interface.declared_members = members;
        interface.declared_call_signatures = call_signatures;
        interface.declared_construct_signatures = construct_signatures;
        interface.declared_index_infos = index_infos;
        true
    }

    pub fn set_instantiation_expression_node(&mut self, id: TypeId, node: Option<NodeRef>) -> bool {
        if !self.valid_record_node(node) {
            return false;
        }
        let Some(TypeData::InstantiationExpression(data)) =
            self.type_payload_mut(id).map(|record| &mut record.data)
        else {
            return false;
        };
        data.node = node;
        true
    }

    #[allow(clippy::too_many_arguments)] // Mirrors all lazy MappedType caches.
    pub fn set_mapped_type_resolution(
        &mut self,
        id: TypeId,
        declaration: Option<NodeRef>,
        type_parameter: Option<TypeId>,
        constraint_type: Option<TypeId>,
        name_type: Option<TypeId>,
        template_type: Option<TypeId>,
        modifiers_type: Option<TypeId>,
        resolved_apparent_type: Option<TypeId>,
        contains_error: bool,
    ) -> bool {
        if !self.valid_record_node(declaration)
            || ![
                type_parameter,
                constraint_type,
                name_type,
                template_type,
                modifiers_type,
                resolved_apparent_type,
            ]
            .into_iter()
            .all(|value| self.valid_optional_record_type(value))
        {
            return false;
        }
        let Some(TypeData::Mapped(data)) = self.type_payload_mut(id).map(|record| &mut record.data)
        else {
            return false;
        };
        data.declaration = declaration;
        data.type_parameter = type_parameter;
        data.constraint_type = constraint_type;
        data.name_type = name_type;
        data.template_type = template_type;
        data.modifiers_type = modifiers_type;
        data.resolved_apparent_type = resolved_apparent_type;
        data.contains_error = contains_error;
        true
    }

    pub fn set_reverse_mapped_types(
        &mut self,
        id: TypeId,
        source: Option<TypeId>,
        mapped_type: Option<TypeId>,
        constraint_type: Option<TypeId>,
    ) -> bool {
        if ![source, mapped_type, constraint_type]
            .into_iter()
            .all(|value| self.valid_optional_record_type(value))
        {
            return false;
        }
        let Some(TypeData::ReverseMapped(data)) =
            self.type_payload_mut(id).map(|record| &mut record.data)
        else {
            return false;
        };
        data.source = source;
        data.mapped_type = mapped_type;
        data.constraint_type = constraint_type;
        true
    }

    pub fn set_evolving_array_types(
        &mut self,
        id: TypeId,
        element_type: Option<TypeId>,
        final_array_type: Option<TypeId>,
    ) -> bool {
        if !self.valid_optional_record_type(element_type)
            || !self.valid_optional_record_type(final_array_type)
        {
            return false;
        }
        let Some(TypeData::EvolvingArray(data)) =
            self.type_payload_mut(id).map(|record| &mut record.data)
        else {
            return false;
        };
        data.element_type = element_type;
        data.final_array_type = final_array_type;
        true
    }

    pub fn set_union_or_intersection_caches(
        &mut self,
        id: TypeId,
        property_cache: Option<SemanticSymbolTable>,
        property_cache_without_function_property_augment: Option<SemanticSymbolTable>,
        resolved_properties: Option<Vec<SemanticSymbolId>>,
    ) -> bool {
        if !self.valid_symbol_table(property_cache.as_ref())
            || !self.valid_symbol_table(property_cache_without_function_property_augment.as_ref())
            || !self.valid_optional_record_symbols(resolved_properties.as_deref())
        {
            return false;
        }
        let Some(record) = self.type_payload_mut(id) else {
            return false;
        };
        let union = match &mut record.data {
            TypeData::Union(data) => &mut data.union,
            TypeData::Intersection(data) => &mut data.intersection,
            _ => return false,
        };
        union.property_cache = property_cache;
        union.property_cache_without_function_property_augment =
            property_cache_without_function_property_augment;
        union.resolved_properties = resolved_properties;
        true
    }

    #[allow(clippy::too_many_arguments)] // Mirrors the union-only lazy caches.
    pub fn set_union_caches(
        &mut self,
        id: TypeId,
        resolved_reduced_type: Option<TypeId>,
        regular_type: Option<TypeId>,
        origin: Option<TypeId>,
        key_property_name: impl Into<String>,
        constituent_map: ConstituentMapState,
    ) -> bool {
        if ![resolved_reduced_type, regular_type, origin]
            .into_iter()
            .all(|value| self.valid_optional_record_type(value))
            || !self.valid_constituent_map(&constituent_map)
        {
            return false;
        }
        let key_property_name = key_property_name.into();
        let Some(TypeData::Union(data)) = self.type_payload_mut(id).map(|record| &mut record.data)
        else {
            return false;
        };
        data.resolved_reduced_type = resolved_reduced_type;
        data.regular_type = regular_type;
        data.origin = origin;
        data.key_property_name = key_property_name;
        data.constituent_map = constituent_map;
        true
    }

    pub fn set_intersection_caches(
        &mut self,
        id: TypeId,
        resolved_apparent_type: Option<TypeId>,
        unique_literal_filled_instantiation: Option<TypeId>,
    ) -> bool {
        if !self.valid_optional_record_type(resolved_apparent_type)
            || !self.valid_optional_record_type(unique_literal_filled_instantiation)
        {
            return false;
        }
        let Some(TypeData::Intersection(data)) =
            self.type_payload_mut(id).map(|record| &mut record.data)
        else {
            return false;
        };
        data.resolved_apparent_type = resolved_apparent_type;
        data.unique_literal_filled_instantiation = unique_literal_filled_instantiation;
        true
    }

    #[allow(clippy::too_many_arguments)] // Mirrors the complete TypeParameter record.
    pub fn set_type_parameter_resolution(
        &mut self,
        id: TypeId,
        constraint: Option<TypeId>,
        target: Option<TypeId>,
        mapper: Option<TypeMapperId>,
        is_this_type: bool,
        resolved_default_type: Option<TypeId>,
    ) -> bool {
        if ![constraint, target, resolved_default_type]
            .into_iter()
            .all(|value| self.valid_optional_record_type(value))
            || !self.valid_record_mapper(mapper)
        {
            return false;
        }
        let Some(TypeData::TypeParameter(data)) =
            self.type_payload_mut(id).map(|record| &mut record.data)
        else {
            return false;
        };
        data.constraint = constraint;
        data.target = target;
        data.mapper = mapper;
        data.is_this_type = is_this_type;
        data.resolved_default_type = resolved_default_type;
        true
    }

    pub fn set_literal_links(
        &mut self,
        id: TypeId,
        fresh_type: Option<TypeId>,
        regular_type: TypeId,
    ) -> bool {
        if !self.valid_optional_record_type(fresh_type) || !self.valid_record_type(regular_type) {
            return false;
        }
        let Some(TypeData::Literal(data)) =
            self.type_payload_mut(id).map(|record| &mut record.data)
        else {
            return false;
        };
        data.fresh_type = fresh_type;
        data.regular_type = regular_type;
        true
    }

    #[allow(clippy::too_many_arguments)] // Mirrors all conditional lazy caches.
    pub fn set_conditional_resolution(
        &mut self,
        id: TypeId,
        resolved_true_type: Option<TypeId>,
        resolved_false_type: Option<TypeId>,
        resolved_inferred_true_type: Option<TypeId>,
        resolved_default_constraint: Option<TypeId>,
        resolved_constraint_of_distributive: Option<TypeId>,
        mapper: Option<TypeMapperId>,
        combined_mapper: Option<TypeMapperId>,
    ) -> bool {
        if ![
            resolved_true_type,
            resolved_false_type,
            resolved_inferred_true_type,
            resolved_default_constraint,
            resolved_constraint_of_distributive,
        ]
        .into_iter()
        .all(|value| self.valid_optional_record_type(value))
            || !self.valid_record_mapper(mapper)
            || !self.valid_record_mapper(combined_mapper)
        {
            return false;
        }
        let Some(TypeData::Conditional(data)) =
            self.type_payload_mut(id).map(|record| &mut record.data)
        else {
            return false;
        };
        data.resolved_true_type = resolved_true_type;
        data.resolved_false_type = resolved_false_type;
        data.resolved_inferred_true_type = resolved_inferred_true_type;
        data.resolved_default_constraint = resolved_default_constraint;
        data.resolved_constraint_of_distributive = resolved_constraint_of_distributive;
        data.mapper = mapper;
        data.combined_mapper = combined_mapper;
        true
    }

    fn valid_record_type(&self, id: TypeId) -> bool {
        self.type_payload(id).is_some()
    }

    fn object_kind_matches(flags: ObjectFlags, allowed: ObjectFlags) -> bool {
        (flags & ObjectFlags::OBJECT_TYPE_KIND_MASK & !allowed).is_empty()
    }

    fn valid_record_types(&self, ids: &[TypeId]) -> bool {
        ids.iter().all(|id| self.valid_record_type(*id))
    }

    fn valid_optional_record_type(&self, id: Option<TypeId>) -> bool {
        id.is_none_or(|id| self.valid_record_type(id))
    }

    fn valid_optional_record_types(&self, ids: Option<&[TypeId]>) -> bool {
        ids.is_none_or(|ids| self.valid_record_types(ids))
    }

    fn valid_record_symbol(&self, id: Option<SemanticSymbolId>) -> bool {
        id.is_none_or(|id| self.symbol_payload(id).is_some())
    }

    fn valid_optional_record_symbols(&self, ids: Option<&[SemanticSymbolId]>) -> bool {
        ids.is_none_or(|ids| ids.iter().all(|id| self.symbol_payload(*id).is_some()))
    }

    fn valid_record_mapper(&self, id: Option<TypeMapperId>) -> bool {
        id.is_none_or(|id| self.mapper_payload(id).is_some())
    }

    fn valid_record_alias(&self, id: Option<TypeAliasId>) -> bool {
        id.is_none_or(|id| self.type_alias_payload(id).is_some())
    }

    fn valid_record_node(&self, node: Option<NodeRef>) -> bool {
        node.is_none_or(|node| self.contains_node_ref(node))
    }

    fn valid_optional_record_signatures(&self, ids: Option<&[SignatureId]>) -> bool {
        ids.is_none_or(|ids| ids.iter().all(|id| self.signature(*id).is_some()))
    }

    fn valid_optional_record_index_infos(&self, ids: Option<&[IndexInfoId]>) -> bool {
        ids.is_none_or(|ids| ids.iter().all(|id| self.index_info(*id).is_some()))
    }

    fn valid_symbol_table(&self, table: Option<&SemanticSymbolTable>) -> bool {
        table.is_none_or(|table| {
            table.store == self.id()
                && table
                    .entries
                    .iter()
                    .all(|(_, symbol)| self.symbol_payload(*symbol).is_some())
        })
    }

    fn valid_type_cache(&self, cache: &TypeCacheState) -> bool {
        let TypeCacheState::Allocated(entries) = cache else {
            return true;
        };
        let mut keys = BTreeSet::new();
        entries
            .iter()
            .all(|entry| keys.insert(entry.key) && self.valid_record_type(entry.value))
    }

    fn valid_constituent_map(&self, map: &ConstituentMapState) -> bool {
        let ConstituentMapState::Allocated(entries) = map else {
            return true;
        };
        let mut keys = BTreeSet::new();
        entries.iter().all(|entry| {
            keys.insert(entry.key)
                && self.valid_record_type(entry.key)
                && self.valid_record_type(entry.value)
        })
    }
}

#[cfg(test)]
mod tests {
    use ts_ast::FileId;
    use ts_jsnum::{Number, PseudoBigInt};
    use ts_parser::parse_source_file;

    use super::*;
    use crate::semantic::{
        AstScope,
        signatures::{ElementFlags, SignatureFlags},
    };

    type TestStore = CanonicalSemanticStore<&'static str, &'static str>;

    struct SeededStore {
        store: TestStore,
        node: NodeRef,
        base: TypeId,
        symbol: SemanticSymbolId,
        mapper: TypeMapperId,
        alias: TypeAliasId,
        root: ConditionalRootId,
        signature: SignatureId,
        index_info: IndexInfoId,
    }

    fn seeded_store(payload: &'static str) -> SeededStore {
        let parsed = parse_source_file("type Result<T> = T extends string ? T : never;");
        let scope = AstScope::new(FileId::new(0), &parsed.arena);
        let node = scope.node_ref(parsed.source_file).unwrap();
        let mut store = TestStore::new();
        assert!(store.register_ast_scope(scope));
        let base = store.alloc_intrinsic_type(TypeFlags::STRING, "string");
        let symbol = store.alloc_symbol(payload);
        let mapper = store.alloc_mapper(payload);
        let alias = store.alloc_type_alias(Some(symbol)).unwrap();
        let root = store
            .alloc_conditional_root(node, base, base, true, None, None, Some(alias))
            .unwrap();
        let signature = store
            .alloc_signature(
                SignatureFlags::NONE,
                Some(node),
                vec![base],
                Some(symbol),
                vec![symbol],
                Some(base),
                None,
                1,
            )
            .unwrap();
        let index_info = store
            .alloc_index_info(base, base, false, Some(node), vec![node])
            .unwrap();
        SeededStore {
            store,
            node,
            base,
            symbol,
            mapper,
            alias,
            root,
            signature,
            index_info,
        }
    }

    #[test]
    fn allocators_cover_every_concrete_type_data_variant() {
        let mut seeded = seeded_store("local");
        let store = &mut seeded.store;
        let element = store
            .create_tuple_element_info(ElementFlags::REQUIRED, Some(seeded.node))
            .unwrap();
        let tuple_metadata = store.create_tuple_metadata(vec![element], true).unwrap();

        let ids = [
            seeded.base,
            store
                .alloc_literal_type(
                    TypeFlags::STRING_LITERAL,
                    LiteralValue::String("value".into()),
                    RegularLiteralLink::SelfType,
                )
                .unwrap(),
            store
                .alloc_unique_es_symbol_type(Some(seeded.symbol), "unique")
                .unwrap(),
            store
                .alloc_plain_object_type(ObjectFlags::ANONYMOUS, Some(seeded.symbol))
                .unwrap(),
            store
                .alloc_type_reference(ObjectFlags::NONE, Some(seeded.symbol))
                .unwrap(),
            store
                .alloc_interface_type(ObjectFlags::INTERFACE, Some(seeded.symbol))
                .unwrap(),
            store
                .alloc_tuple_type(ObjectFlags::NONE, None, tuple_metadata)
                .unwrap(),
            store
                .alloc_instantiation_expression_type(
                    ObjectFlags::NONE,
                    Some(seeded.symbol),
                    Some(seeded.node),
                )
                .unwrap(),
            store
                .alloc_mapped_type(ObjectFlags::NONE, Some(seeded.symbol), Some(seeded.node))
                .unwrap(),
            store
                .alloc_reverse_mapped_type(ObjectFlags::NONE, None)
                .unwrap(),
            store
                .alloc_evolving_array_type(ObjectFlags::NONE, Some(seeded.symbol))
                .unwrap(),
            store
                .alloc_union_type(ObjectFlags::NONE, vec![seeded.base])
                .unwrap(),
            store
                .alloc_intersection_type(ObjectFlags::NONE, vec![seeded.base])
                .unwrap(),
            store.alloc_type_parameter(Some(seeded.symbol)).unwrap(),
            store
                .alloc_index_type(seeded.base, IndexFlags::STRINGS_ONLY)
                .unwrap(),
            store
                .alloc_indexed_access_type(seeded.base, seeded.base, AccessFlags::INCLUDE_UNDEFINED)
                .unwrap(),
            store
                .alloc_template_literal_type(
                    vec!["before".into(), "after".into()],
                    vec![seeded.base],
                )
                .unwrap(),
            store
                .alloc_string_mapping_type(Some(seeded.symbol), seeded.base)
                .unwrap(),
            store
                .alloc_substitution_type(seeded.base, seeded.base)
                .unwrap(),
            store
                .alloc_conditional_type(
                    seeded.root,
                    seeded.base,
                    seeded.base,
                    Some(seeded.mapper),
                    Some(seeded.mapper),
                )
                .unwrap(),
        ];
        let kinds = ids.map(|id| store.type_payload(id).unwrap().data().kind());
        assert_eq!(
            kinds,
            [
                TypeDataKind::Intrinsic,
                TypeDataKind::Literal,
                TypeDataKind::UniqueEsSymbol,
                TypeDataKind::Object,
                TypeDataKind::TypeReference,
                TypeDataKind::Interface,
                TypeDataKind::Tuple,
                TypeDataKind::InstantiationExpression,
                TypeDataKind::Mapped,
                TypeDataKind::ReverseMapped,
                TypeDataKind::EvolvingArray,
                TypeDataKind::Union,
                TypeDataKind::Intersection,
                TypeDataKind::TypeParameter,
                TypeDataKind::Index,
                TypeDataKind::IndexedAccess,
                TypeDataKind::TemplateLiteral,
                TypeDataKind::StringMapping,
                TypeDataKind::Substitution,
                TypeDataKind::Conditional,
            ]
        );
    }

    #[test]
    fn construction_preserves_exact_defaults_order_and_nil_states() {
        let mut seeded = seeded_store("local");
        let reset = ObjectFlags::COULD_CONTAIN_TYPE_VARIABLES_COMPUTED
            | ObjectFlags::COULD_CONTAIN_TYPE_VARIABLES
            | ObjectFlags::MEMBERS_RESOLVED
            | ObjectFlags::CONTAINS_WIDENING_TYPE;
        let intrinsic = seeded
            .store
            .alloc_intrinsic_type_ex(TypeFlags::UNKNOWN, "unknown", reset);
        assert_eq!(
            seeded.store.type_payload(intrinsic).unwrap().object_flags(),
            ObjectFlags::CONTAINS_WIDENING_TYPE
        );

        let literal = seeded
            .store
            .alloc_literal_type(
                TypeFlags::NUMBER_LITERAL,
                LiteralValue::Number(Number::new(1.25)),
                RegularLiteralLink::SelfType,
            )
            .unwrap();
        let TypeData::Literal(literal_data) = seeded.store.type_payload(literal).unwrap().data()
        else {
            panic!("expected literal")
        };
        assert_eq!(literal_data.fresh_type, None);
        assert_eq!(literal_data.regular_type, literal);

        let union = seeded
            .store
            .alloc_union_type(ObjectFlags::NONE, vec![literal, seeded.base, intrinsic])
            .unwrap();
        let TypeData::Union(union_data) = seeded.store.type_payload(union).unwrap().data() else {
            panic!("expected union")
        };
        assert_eq!(union_data.union.types, [literal, seeded.base, intrinsic]);
        assert_eq!(union_data.union.structured.members, None);
        assert_eq!(union_data.union.structured.signatures, None);
        assert_eq!(union_data.union.structured.index_infos, None);
        assert_eq!(union_data.constituent_map, ConstituentMapState::Unallocated);
        assert!(union_data.key_property_name.is_empty());

        let template = seeded
            .store
            .alloc_template_literal_type(
                vec!["a".into(), "b".into(), "c".into()],
                vec![literal, seeded.base],
            )
            .unwrap();
        let TypeData::TemplateLiteral(template_data) =
            seeded.store.type_payload(template).unwrap().data()
        else {
            panic!("expected template literal")
        };
        assert_eq!(template_data.texts, ["a", "b", "c"]);
        assert_eq!(template_data.types, [literal, seeded.base]);

        let object = seeded
            .store
            .alloc_plain_object_type(ObjectFlags::ANONYMOUS, Some(seeded.symbol))
            .unwrap();
        let table = seeded
            .store
            .create_semantic_symbol_table(vec![("p".into(), seeded.symbol)])
            .unwrap();
        assert!(seeded.store.set_structured_type_members(
            object,
            Some(table),
            Some(vec![seeded.symbol]),
            Some(vec![seeded.signature]),
            Some(vec![seeded.signature]),
            Some(vec![seeded.index_info]),
        ));
        let TypeData::Object(object_data) = seeded.store.type_payload(object).unwrap().data()
        else {
            panic!("expected object")
        };
        assert_eq!(
            object_data.structured.signatures,
            Some(vec![seeded.signature, seeded.signature])
        );
        assert_eq!(object_data.structured.call_signature_count, 1);
        assert!(
            seeded
                .store
                .type_payload(object)
                .unwrap()
                .object_flags()
                .contains(ObjectFlags::MEMBERS_RESOLVED)
        );
    }

    #[test]
    fn literal_values_preserve_all_upstream_alternatives() {
        let mut store = TestStore::new();
        let values = [
            LiteralValue::String("s".into()),
            LiteralValue::Number(Number::new(-0.0)),
            LiteralValue::Boolean(false),
            LiteralValue::BigInt(PseudoBigInt::parse_valid("0x10n")),
            LiteralValue::ComputedEnum,
        ];
        let ids = values.map(|value| {
            store
                .alloc_literal_type(TypeFlags::ENUM_LITERAL, value, RegularLiteralLink::SelfType)
                .unwrap()
        });
        assert!(matches!(
            store.type_payload(ids[0]).unwrap().data(),
            TypeData::Literal(LiteralTypeData {
                value: LiteralValue::String(value),
                ..
            }) if value == "s"
        ));
        assert!(matches!(
            store.type_payload(ids[1]).unwrap().data(),
            TypeData::Literal(LiteralTypeData {
                value: LiteralValue::Number(value),
                ..
            }) if value.value().is_sign_negative()
        ));
        assert!(matches!(
            store.type_payload(ids[2]).unwrap().data(),
            TypeData::Literal(LiteralTypeData {
                value: LiteralValue::Boolean(false),
                ..
            })
        ));
        assert!(matches!(
            store.type_payload(ids[3]).unwrap().data(),
            TypeData::Literal(LiteralTypeData {
                value: LiteralValue::BigInt(value),
                ..
            }) if value.base10_value == "16"
        ));
        assert!(matches!(
            store.type_payload(ids[4]).unwrap().data(),
            TypeData::Literal(LiteralTypeData {
                value: LiteralValue::ComputedEnum,
                ..
            })
        ));
    }

    #[test]
    fn two_phase_updates_represent_observable_cycles() {
        let mut seeded = seeded_store("local");
        let regular = seeded
            .store
            .alloc_literal_type(
                TypeFlags::STRING_LITERAL,
                LiteralValue::String("x".into()),
                RegularLiteralLink::SelfType,
            )
            .unwrap();
        let fresh = seeded
            .store
            .alloc_literal_type(
                TypeFlags::STRING_LITERAL,
                LiteralValue::String("x".into()),
                RegularLiteralLink::Type(regular),
            )
            .unwrap();
        assert!(
            seeded
                .store
                .set_literal_links(regular, Some(fresh), regular)
        );

        let interface = seeded
            .store
            .alloc_interface_type(ObjectFlags::INTERFACE, Some(seeded.symbol))
            .unwrap();
        assert!(seeded.store.set_object_target_and_mapper(
            interface,
            Some(interface),
            Some(seeded.mapper)
        ));
        assert!(seeded.store.set_interface_type_parameters(
            interface,
            Some(vec![interface]),
            0,
            Some(interface),
        ));

        let alias = seeded.store.alloc_type_alias(Some(seeded.symbol)).unwrap();
        assert!(seeded.store.set_type_alias(interface, Some(alias)));
        assert!(
            seeded
                .store
                .set_type_alias_arguments(alias, Some(vec![interface]))
        );

        let conditional = seeded
            .store
            .alloc_conditional_type(
                seeded.root,
                seeded.base,
                seeded.base,
                Some(seeded.mapper),
                None,
            )
            .unwrap();
        assert!(seeded.store.set_conditional_root_instantiations(
            seeded.root,
            TypeCacheState::Allocated(vec![TypeCacheEntry {
                key: CacheHashKey::from_halves(1, 2),
                value: conditional,
            }]),
        ));

        let TypeData::Literal(regular_data) = seeded.store.type_payload(regular).unwrap().data()
        else {
            panic!("expected literal")
        };
        assert_eq!(regular_data.fresh_type, Some(fresh));
        let TypeData::Literal(fresh_data) = seeded.store.type_payload(fresh).unwrap().data() else {
            panic!("expected literal")
        };
        assert_eq!(fresh_data.regular_type, regular);
        assert_eq!(
            seeded.store.type_alias(alias).unwrap().type_arguments(),
            Some([interface].as_slice())
        );
        assert_eq!(
            seeded
                .store
                .conditional_root(seeded.root)
                .unwrap()
                .instantiations(),
            &TypeCacheState::Allocated(vec![TypeCacheEntry {
                key: CacheHashKey::from_halves(1, 2),
                value: conditional,
            }])
        );
    }

    #[test]
    fn foreign_handles_are_rejected_per_slot_before_mutation() {
        let first = seeded_store("first");
        let mut second = seeded_store("second");
        assert_eq!(first.base.get(), second.base.get());
        assert_eq!(first.symbol.get(), second.symbol.get());
        assert_eq!(first.mapper.get(), second.mapper.get());
        assert_eq!(first.alias.get(), second.alias.get());
        assert_eq!(first.root.get(), second.root.get());
        assert_eq!(second.store.type_alias(first.alias), None);
        assert_eq!(second.store.conditional_root(first.root), None);

        let type_count = second.store.type_len();
        assert_eq!(
            second.store.alloc_literal_type(
                TypeFlags::STRING_LITERAL,
                LiteralValue::String("x".into()),
                RegularLiteralLink::Type(first.base),
            ),
            None
        );
        assert_eq!(
            second
                .store
                .alloc_unique_es_symbol_type(Some(first.symbol), "foreign"),
            None
        );
        assert_eq!(
            second
                .store
                .alloc_union_type(ObjectFlags::NONE, vec![first.base]),
            None
        );
        assert_eq!(
            second
                .store
                .alloc_indexed_access_type(first.base, second.base, AccessFlags::NONE,),
            None
        );
        assert_eq!(
            second
                .store
                .alloc_indexed_access_type(second.base, first.base, AccessFlags::NONE,),
            None
        );
        assert_eq!(
            second.store.alloc_conditional_type(
                first.root,
                second.base,
                second.base,
                Some(second.mapper),
                None,
            ),
            None
        );
        assert_eq!(
            second.store.alloc_conditional_type(
                second.root,
                first.base,
                second.base,
                Some(second.mapper),
                None,
            ),
            None
        );
        assert_eq!(
            second.store.alloc_conditional_type(
                second.root,
                second.base,
                first.base,
                Some(second.mapper),
                None,
            ),
            None
        );
        assert_eq!(
            second.store.alloc_conditional_type(
                second.root,
                second.base,
                second.base,
                Some(first.mapper),
                None,
            ),
            None
        );
        assert_eq!(second.store.type_len(), type_count);

        let object = second
            .store
            .alloc_plain_object_type(ObjectFlags::ANONYMOUS, Some(second.symbol))
            .unwrap();
        assert!(!second.store.set_type_symbol(object, Some(first.symbol)));
        assert!(!second.store.set_type_alias(object, Some(first.alias)));
        assert!(
            !second
                .store
                .set_resolved_base_constraint(object, Some(first.base))
        );
        assert!(!second.store.set_object_target_and_mapper(
            object,
            Some(first.base),
            Some(second.mapper),
        ));
        assert!(!second.store.set_object_target_and_mapper(
            object,
            Some(second.base),
            Some(first.mapper),
        ));
        assert!(!second.store.set_object_instantiations(
            object,
            TypeCacheState::Allocated(vec![TypeCacheEntry {
                key: CacheHashKey::new(1),
                value: first.base,
            }]),
        ));
        let foreign_table = first
            .store
            .create_semantic_symbol_table(vec![("x".into(), first.symbol)])
            .unwrap();
        assert!(!second.store.set_structured_type_members(
            object,
            Some(foreign_table),
            None,
            None,
            None,
            None,
        ));
        assert!(!second.store.set_structured_type_members(
            object,
            None,
            Some(vec![first.symbol]),
            None,
            None,
            None,
        ));
        assert!(!second.store.set_structured_type_members(
            object,
            None,
            None,
            Some(vec![first.signature]),
            None,
            None,
        ));
        assert!(!second.store.set_structured_type_members(
            object,
            None,
            None,
            None,
            None,
            Some(vec![first.index_info]),
        ));

        let TypeData::Object(data) = second.store.type_payload(object).unwrap().data() else {
            panic!("expected object")
        };
        assert_eq!(
            second.store.type_payload(object).unwrap().symbol(),
            Some(second.symbol)
        );
        assert_eq!(second.store.type_payload(object).unwrap().alias(), None);
        assert_eq!(data.structured.constrained.resolved_base_constraint, None);
        assert_eq!(data.target, None);
        assert_eq!(data.mapper, None);
        assert_eq!(data.instantiations, TypeCacheState::Unallocated);
        assert_eq!(data.structured.members, None);
        assert_eq!(data.structured.properties, None);
        assert_eq!(data.structured.signatures, None);
        assert_eq!(data.structured.index_infos, None);
    }

    #[test]
    fn nested_tables_and_caches_reject_duplicates_without_mutation() {
        let mut seeded = seeded_store("local");
        assert!(
            seeded
                .store
                .create_semantic_symbol_table(vec![
                    ("same".into(), seeded.symbol),
                    ("same".into(), seeded.symbol),
                ])
                .is_none()
        );
        let object = seeded
            .store
            .alloc_plain_object_type(ObjectFlags::ANONYMOUS, Some(seeded.symbol))
            .unwrap();
        let duplicate_key = CacheHashKey::new(7);
        assert!(!seeded.store.set_object_instantiations(
            object,
            TypeCacheState::Allocated(vec![
                TypeCacheEntry {
                    key: duplicate_key,
                    value: seeded.base,
                },
                TypeCacheEntry {
                    key: duplicate_key,
                    value: object,
                },
            ]),
        ));
        let union = seeded
            .store
            .alloc_union_type(ObjectFlags::NONE, vec![seeded.base, object])
            .unwrap();
        assert!(!seeded.store.set_union_caches(
            union,
            None,
            None,
            None,
            "key",
            ConstituentMapState::Allocated(vec![
                ConstituentEntry {
                    key: seeded.base,
                    value: object,
                },
                ConstituentEntry {
                    key: seeded.base,
                    value: union,
                },
            ]),
        ));
        let TypeData::Object(object_data) = seeded.store.type_payload(object).unwrap().data()
        else {
            panic!("expected object")
        };
        assert_eq!(object_data.instantiations, TypeCacheState::Unallocated);
        let TypeData::Union(union_data) = seeded.store.type_payload(union).unwrap().data() else {
            panic!("expected union")
        };
        assert_eq!(union_data.constituent_map, ConstituentMapState::Unallocated);
        assert!(union_data.key_property_name.is_empty());
    }

    #[test]
    fn allocated_empty_states_and_entry_order_remain_observable() {
        assert_eq!(std::mem::size_of::<CacheHashKey>(), 16);
        let mut seeded = seeded_store("local");
        let second_symbol = seeded.store.alloc_symbol("second");
        let table = seeded
            .store
            .create_semantic_symbol_table(vec![
                ("z".into(), seeded.symbol),
                ("a".into(), second_symbol),
            ])
            .unwrap();
        assert_eq!(
            table.entries(),
            [
                ("z".to_owned(), seeded.symbol),
                ("a".to_owned(), second_symbol),
            ]
        );
        let empty_table = seeded
            .store
            .create_semantic_symbol_table(Vec::new())
            .unwrap();
        assert!(empty_table.is_empty());

        assert!(
            seeded
                .store
                .set_type_alias_arguments(seeded.alias, Some(Vec::new()))
        );
        assert_eq!(
            seeded
                .store
                .type_alias(seeded.alias)
                .unwrap()
                .type_arguments(),
            Some([].as_slice())
        );

        let object = seeded
            .store
            .alloc_plain_object_type(ObjectFlags::ANONYMOUS, Some(seeded.symbol))
            .unwrap();
        assert!(
            seeded
                .store
                .set_object_instantiations(object, TypeCacheState::Allocated(Vec::new()),)
        );
        let TypeData::Object(object_data) = seeded.store.type_payload(object).unwrap().data()
        else {
            panic!("expected object")
        };
        assert_eq!(
            object_data.instantiations,
            TypeCacheState::Allocated(Vec::new())
        );

        let union = seeded
            .store
            .alloc_union_type(ObjectFlags::NONE, vec![seeded.base, object])
            .unwrap();
        let first_key = CacheHashKey::from_halves(0x0123, 0x4567);
        let second_key = CacheHashKey::new(9);
        assert_eq!(first_key.get(), (0x0123_u128 << 64) | 0x4567);
        assert!(seeded.store.set_object_instantiations(
            object,
            TypeCacheState::Allocated(vec![
                TypeCacheEntry {
                    key: second_key,
                    value: union,
                },
                TypeCacheEntry {
                    key: first_key,
                    value: seeded.base,
                },
            ]),
        ));
        assert!(seeded.store.set_union_caches(
            union,
            None,
            None,
            None,
            "kind",
            ConstituentMapState::Allocated(vec![
                ConstituentEntry {
                    key: object,
                    value: union,
                },
                ConstituentEntry {
                    key: seeded.base,
                    value: object,
                },
            ]),
        ));
        let TypeData::Object(object_data) = seeded.store.type_payload(object).unwrap().data()
        else {
            panic!("expected object")
        };
        assert_eq!(
            object_data.instantiations,
            TypeCacheState::Allocated(vec![
                TypeCacheEntry {
                    key: second_key,
                    value: union,
                },
                TypeCacheEntry {
                    key: first_key,
                    value: seeded.base,
                },
            ])
        );
        let TypeData::Union(union_data) = seeded.store.type_payload(union).unwrap().data() else {
            panic!("expected union")
        };
        assert_eq!(
            union_data.constituent_map,
            ConstituentMapState::Allocated(vec![
                ConstituentEntry {
                    key: object,
                    value: union,
                },
                ConstituentEntry {
                    key: seeded.base,
                    value: object,
                },
            ])
        );
    }

    #[test]
    fn auxiliary_records_and_node_slots_reject_foreign_provenance() {
        let first = seeded_store("first");
        let mut second = seeded_store("second");
        assert!(
            second
                .store
                .create_semantic_symbol_table(vec![("x".into(), first.symbol)])
                .is_none()
        );
        assert_eq!(second.store.alloc_type_alias(Some(first.symbol)), None);
        assert!(!second.store.set_type_alias_arguments(first.alias, None));
        assert!(
            !second
                .store
                .set_type_alias_arguments(second.alias, Some(vec![first.base]))
        );
        assert_eq!(
            second
                .store
                .type_alias(second.alias)
                .unwrap()
                .type_arguments(),
            None
        );

        let root_count = second.store.conditional_root_len();
        assert_eq!(
            second.store.alloc_conditional_root(
                first.node,
                second.base,
                second.base,
                true,
                None,
                None,
                Some(second.alias),
            ),
            None
        );
        assert_eq!(
            second.store.alloc_conditional_root(
                second.node,
                first.base,
                second.base,
                true,
                None,
                None,
                Some(second.alias),
            ),
            None
        );
        assert_eq!(
            second.store.alloc_conditional_root(
                second.node,
                second.base,
                first.base,
                true,
                None,
                None,
                Some(second.alias),
            ),
            None
        );
        assert_eq!(
            second.store.alloc_conditional_root(
                second.node,
                second.base,
                second.base,
                true,
                Some(vec![first.base]),
                None,
                Some(second.alias),
            ),
            None
        );
        assert_eq!(
            second.store.alloc_conditional_root(
                second.node,
                second.base,
                second.base,
                true,
                None,
                Some(vec![first.base]),
                Some(second.alias),
            ),
            None
        );
        assert_eq!(
            second.store.alloc_conditional_root(
                second.node,
                second.base,
                second.base,
                true,
                None,
                None,
                Some(first.alias),
            ),
            None
        );
        assert_eq!(second.store.conditional_root_len(), root_count);
        assert!(
            !second
                .store
                .set_conditional_root_instantiations(first.root, TypeCacheState::Unallocated)
        );
        assert!(
            !second
                .store
                .set_conditional_root_alias(second.root, Some(first.alias))
        );
        assert_eq!(
            second.store.conditional_root(second.root).unwrap().alias(),
            Some(second.alias)
        );

        let reference = second
            .store
            .alloc_type_reference(ObjectFlags::NONE, Some(second.symbol))
            .unwrap();
        assert!(!second.store.set_type_reference_resolution(
            reference,
            Some(first.node),
            Some(vec![second.base]),
        ));
        assert!(!second.store.set_type_reference_resolution(
            reference,
            Some(second.node),
            Some(vec![first.base]),
        ));
        let TypeData::TypeReference(reference_data) =
            second.store.type_payload(reference).unwrap().data()
        else {
            panic!("expected type reference")
        };
        assert_eq!(reference_data.node, None);
        assert_eq!(reference_data.resolved_type_arguments, None);

        let expression = second
            .store
            .alloc_instantiation_expression_type(ObjectFlags::NONE, Some(second.symbol), None)
            .unwrap();
        assert!(
            !second
                .store
                .set_instantiation_expression_node(expression, Some(first.node))
        );
        let TypeData::InstantiationExpression(expression_data) =
            second.store.type_payload(expression).unwrap().data()
        else {
            panic!("expected instantiation expression")
        };
        assert_eq!(expression_data.node, None);

        let foreign_element = first
            .store
            .create_tuple_element_info(ElementFlags::REQUIRED, Some(first.node))
            .unwrap();
        let foreign_metadata = first
            .store
            .create_tuple_metadata(vec![foreign_element], false)
            .unwrap();
        let type_count = second.store.type_len();
        assert_eq!(
            second
                .store
                .alloc_tuple_type(ObjectFlags::NONE, None, foreign_metadata),
            None
        );
        assert_eq!(second.store.type_len(), type_count);
    }

    #[test]
    fn invalid_shape_constraints_fail_without_allocation() {
        let mut seeded = seeded_store("local");
        let count = seeded.store.type_len();
        assert_eq!(
            seeded
                .store
                .alloc_plain_object_type(ObjectFlags::NONE, Some(seeded.symbol)),
            None
        );
        assert_eq!(
            seeded
                .store
                .alloc_interface_type(ObjectFlags::REFERENCE, Some(seeded.symbol)),
            None
        );
        assert_eq!(
            seeded
                .store
                .alloc_indexed_access_type(seeded.base, seeded.base, AccessFlags::WRITING,),
            None
        );
        assert_eq!(
            seeded
                .store
                .alloc_template_literal_type(vec!["only one".into()], vec![seeded.base],),
            None
        );
        assert_eq!(
            seeded
                .store
                .alloc_template_literal_type(vec![String::new()], Vec::new()),
            None
        );
        assert_eq!(seeded.store.type_len(), count);
    }
}
