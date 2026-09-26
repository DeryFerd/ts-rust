//! Complete ID-backed payloads for typescript-go's canonical `Type` graph.
//!
//! The field inventory is pinned to `internal/checker/types.go` at
//! `dc37b5249ab60e2bbce936f71b883e6c8136167e`, especially `TypeAlias`, `Type`,
//! and the concrete `TypeData` records at lines 643-1245. Go pointer identity is
//! represented by store-branded IDs. `Option<Vec<_>>` preserves nil versus
//! allocated-empty slices, while explicit `HashMap` states preserve nil versus
//! allocated-empty maps without turning checker hot paths into linear scans.

use std::{
    collections::{BTreeMap, HashMap},
    fmt,
    sync::Arc,
};

use ts_ast::{NodeRef, SyntaxKind};
use ts_binder::{EscapedName, InternalSymbolName, SemanticSymbolId, SymbolTableId};
use ts_jsnum::{Number, PseudoBigInt};
use xxhash_rust::xxh3::Xxh3;

use super::{
    ids::{ConditionalRootId, IndexInfoId, SignatureId, TypeAliasId, TypeId, TypeMapperId},
    signatures::{IndexFlags, TupleMetadata},
    store::SemanticStore,
    types::{AccessFlags, ObjectFlags, TypeFlags},
};

/// The exact 128-bit key shape used by upstream semantic caches.
///
/// Relation-key construction lives in the canonical relation substrate; other
/// cache algorithms use this record while their exact builders are ported.
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

/// Ordered type-list hash shared by every pinned instantiation cache. The
/// exact list must still be retained by caches where collisions are
/// semantically distinguishable.
pub(super) fn type_list_key(types: &[TypeId]) -> CacheHashKey {
    let mut hasher = Xxh3::new();
    hasher.update(
        &u64::try_from(types.len())
            .expect("type-list length must fit the pinned uint64 encoding")
            .to_le_bytes(),
    );
    for type_id in types {
        hasher.update(&type_id.get().to_le_bytes());
    }
    CacheHashKey::new(hasher.digest128())
}

/// Nil versus allocated state of an upstream type-instantiation map.
#[derive(Clone, Default, Eq, PartialEq)]
pub enum TypeCacheState {
    #[default]
    Unallocated,
    Allocated(HashMap<CacheHashKey, TypeId>),
}

impl fmt::Debug for TypeCacheState {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Unallocated => formatter.write_str("Unallocated"),
            Self::Allocated(entries) => formatter
                .debug_tuple("Allocated")
                .field(&entries.iter().collect::<BTreeMap<_, _>>())
                .finish(),
        }
    }
}

/// Nil versus allocated state of `map[*Type]*Type`.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub enum ConstituentMapState {
    #[default]
    Unallocated,
    Allocated(HashMap<TypeId, TypeId>),
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

/// Arena-owned equivalent of upstream `TypeAlias`.
#[derive(Debug, Eq, PartialEq)]
pub struct TypeAlias {
    id: TypeAliasId,
    symbol: Option<SemanticSymbolId>,
    type_arguments: Option<Vec<TypeId>>,
    imported_body: Option<Arc<super::source_imports::SourceAliasBodyTypeImportPlan>>,
}

impl TypeAlias {
    pub(super) fn imported_body(
        &self,
    ) -> Option<&super::source_imports::SourceAliasBodyTypeImportPlan> {
        self.imported_body.as_deref()
    }

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
    pub members: Option<SymbolTableId>,
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
    pub(super) source_computed_literal:
        Option<std::sync::Arc<super::object_members::SourceComputedObjectLiteralOrigin>>,
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
    pub declared_members: Option<SymbolTableId>,
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
    pub name: EscapedName,
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
    pub property_cache: Option<SymbolTableId>,
    pub property_cache_without_function_property_augment: Option<SymbolTableId>,
    pub resolved_properties: Option<Vec<SemanticSymbolId>>,
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct UnionTypeData {
    pub union: UnionOrIntersectionTypeData,
    pub resolved_reduced_type: Option<TypeId>,
    pub regular_type: Option<TypeId>,
    pub origin: Option<TypeId>,
    pub key_property_name: EscapedName,
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

    pub(super) const fn constrained(&self) -> Option<&ConstrainedTypeData> {
        match self {
            Self::Object(data) => Some(&data.structured.constrained),
            Self::TypeReference(data) => Some(&data.object.structured.constrained),
            Self::Interface(data) => Some(&data.reference.object.structured.constrained),
            Self::Tuple(data) => Some(&data.interface.reference.object.structured.constrained),
            Self::InstantiationExpression(data) => Some(&data.object.structured.constrained),
            Self::Mapped(data) => Some(&data.object.structured.constrained),
            Self::ReverseMapped(data) => Some(&data.object.structured.constrained),
            Self::EvolvingArray(data) => Some(&data.object.structured.constrained),
            Self::Union(data) => Some(&data.union.structured.constrained),
            Self::Intersection(data) => Some(&data.intersection.structured.constrained),
            Self::TypeParameter(data) => Some(&data.constrained),
            Self::Index(data) => Some(&data.constrained),
            Self::IndexedAccess(data) => Some(&data.constrained),
            Self::TemplateLiteral(data) => Some(&data.constrained),
            Self::StringMapping(data) => Some(&data.constrained),
            Self::Substitution(data) => Some(&data.constrained),
            Self::Conditional(data) => Some(&data.constrained),
            Self::Intrinsic(_) | Self::Literal(_) | Self::UniqueEsSymbol(_) => None,
        }
    }

    /// Borrows the fields embedded by every structured type without resolving
    /// them. Relation fast paths use this only after observing upstream's
    /// `MembersResolved` bit; lazy member construction remains checker-owned.
    pub(super) const fn structured(&self) -> Option<&StructuredTypeData> {
        match self {
            Self::Object(data) => Some(&data.structured),
            Self::TypeReference(data) => Some(&data.object.structured),
            Self::Interface(data) => Some(&data.reference.object.structured),
            Self::Tuple(data) => Some(&data.interface.reference.object.structured),
            Self::InstantiationExpression(data) => Some(&data.object.structured),
            Self::Mapped(data) => Some(&data.object.structured),
            Self::ReverseMapped(data) => Some(&data.object.structured),
            Self::EvolvingArray(data) => Some(&data.object.structured),
            Self::Union(data) => Some(&data.union.structured),
            Self::Intersection(data) => Some(&data.intersection.structured),
            _ => None,
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

    fn object(&self) -> Option<&ObjectTypeData> {
        match self {
            Self::Object(data) => Some(data),
            Self::TypeReference(data) => Some(&data.object),
            Self::Interface(data) => Some(&data.reference.object),
            Self::Tuple(data) => Some(&data.interface.reference.object),
            Self::InstantiationExpression(data) => Some(&data.object),
            Self::Mapped(data) => Some(&data.object),
            Self::ReverseMapped(data) => Some(&data.object),
            Self::EvolvingArray(data) => Some(&data.object),
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

    fn reference(&self) -> Option<&TypeReferenceData> {
        match self {
            Self::TypeReference(data) => Some(data),
            Self::Interface(data) => Some(&data.reference),
            Self::Tuple(data) => Some(&data.interface.reference),
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

    fn interface(&self) -> Option<&InterfaceTypeData> {
        match self {
            Self::Interface(data) => Some(data),
            Self::Tuple(data) => Some(&data.interface),
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
    pub(super) fn attach_source_computed_literal(
        &mut self,
        origin: std::sync::Arc<super::object_members::SourceComputedObjectLiteralOrigin>,
    ) -> bool {
        if self.id != origin.type_id()
            || self.symbol != Some(origin.owner())
            || self.flags != TypeFlags::OBJECT
            || self.alias.is_some()
            || !self.object_flags.contains(
                ObjectFlags::OBJECT_LITERAL
                    | ObjectFlags::FRESH_LITERAL
                    | ObjectFlags::MEMBERS_RESOLVED,
            )
        {
            return false;
        }
        let TypeData::Object(object) = &mut self.data else {
            return false;
        };
        if object.source_computed_literal.is_some()
            || object.target.is_some()
            || object.mapper.is_some()
            || object.instantiations != TypeCacheState::Unallocated
        {
            return false;
        }
        object.source_computed_literal = Some(origin);
        true
    }

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
pub type CanonicalSemanticStore<MapperPayload> = SemanticStore<TypeRecord, MapperPayload>;

impl SemanticStore<TypeRecord, super::mapper::TypeMapper> {
    /// Retains the host-proved origin only on the original imported wrapper result.
    pub(super) fn retain_type_alias_imported_body(
        &mut self,
        result: TypeId,
        proof: Arc<super::source_imports::SourceAliasBodyTypeImportPlan>,
    ) -> bool {
        let Some(record) = self.type_payload(result) else {
            return false;
        };
        let Some(alias) = record.alias() else {
            return false;
        };
        if !matches!(record.data(), TypeData::Object(object)
            if object.target.is_some() && object.mapper.is_some())
            || !record
                .object_flags()
                .contains(ObjectFlags::ANONYMOUS | ObjectFlags::INSTANTIATED)
            || proof.validate_wrapper_identity(self, alias).is_err()
        {
            return false;
        }
        let Some(identity) = self.type_alias_payload(alias) else {
            return false;
        };
        if let Some(existing) = identity.imported_body.as_ref() {
            return existing.as_ref() == proof.as_ref();
        }
        self.type_alias_payload_mut(alias)
            .expect("the alias identity was checked")
            .imported_body = Some(proof);
        self.mark_relation_inputs_dirty();
        self.mark_union_cache_validation_dirty();
        true
    }
}

impl<MapperPayload> SemanticStore<TypeRecord, MapperPayload> {
    pub(super) fn type_is_exact_callable_object(&self, type_: TypeId) -> bool {
        self.source_callable_provenance(type_).is_some()
            || self.source_overload_provenance(type_).is_some()
            || self.type_has_declared_call_set_provenance(type_)
            || self.type_payload(type_)
            .and_then(TypeRecord::symbol)
            .and_then(|symbol| self.symbol(symbol))
            .and_then(ts_binder::semantic::Symbol::declarations)
            .is_some_and(|declarations| {
                matches!(declarations, [declaration] if self.source_node_kind(*declaration) == Some(SyntaxKind::FunctionType))
            })
    }

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
            imported_body: None,
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
        let relation_dirty = self.relation_type_alias_is_observable(alias)
            && self
                .type_alias_payload(alias)
                .is_some_and(|current| current.type_arguments() != type_arguments.as_deref());
        let Some(record) = self.type_alias_payload_mut(alias) else {
            return false;
        };
        record.type_arguments = type_arguments;
        if relation_dirty {
            self.mark_relation_inputs_dirty();
        }
        self.mark_union_cache_validation_dirty();
        true
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
    ) -> Option<TypeId> {
        self.alloc_intrinsic_type_ex(flags, intrinsic_name, ObjectFlags::NONE)
    }

    pub fn alloc_intrinsic_type_ex(
        &mut self,
        flags: TypeFlags,
        intrinsic_name: impl Into<String>,
        object_flags: ObjectFlags,
    ) -> Option<TypeId> {
        let object_flags = object_flags.normalized_for_new_type();
        if !Self::valid_intrinsic_flags(flags)
            || !Self::object_flags_are_subset(object_flags, ObjectFlags::PROPAGATING_FLAGS)
        {
            return None;
        }
        let intrinsic_name = intrinsic_name.into();
        Some(self.alloc_type_with(|id| TypeRecord {
            id,
            flags,
            object_flags,
            symbol: None,
            alias: None,
            data: TypeData::Intrinsic(IntrinsicTypeData { intrinsic_name }),
        }))
    }

    pub fn alloc_literal_type(
        &mut self,
        flags: TypeFlags,
        value: LiteralValue,
        regular_type: RegularLiteralLink,
    ) -> Option<TypeId> {
        if !Self::valid_literal_flags(&value, flags) {
            return None;
        }
        if let RegularLiteralLink::Type(regular_type) = regular_type {
            let regular_record = self.type_payload(regular_type)?;
            if !Self::record_is_compatible_literal(regular_record, flags, &value) {
                return None;
            }
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

    /// Allocates the identity-bearing unique-symbol type for `symbol`.
    ///
    /// Pinned `getESSymbolLikeTypeForNode` derives this name from the symbol's
    /// immutable name and lazily assigned process-global ID. Keeping that
    /// derivation here prevents callers from constructing a unique-symbol type
    /// whose `symbol` and `name` identify different declarations.
    pub fn alloc_unique_es_symbol_type(&mut self, symbol: SemanticSymbolId) -> Option<TypeId> {
        let name = self.unique_symbol_name(symbol)?;
        self.alloc_record(
            TypeFlags::UNIQUE_ES_SYMBOL,
            ObjectFlags::NONE,
            Some(symbol),
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
        if !Self::has_exactly_one_interface_origin(object_flags)
            || object_flags.intersects(ObjectFlags::REFERENCE)
            || !Self::object_kind_matches(object_flags, ObjectFlags::CLASS_OR_INTERFACE)
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
        let object_flags = object_flags.normalized_for_new_type();
        if !self.valid_record_types(&types) || !Self::valid_union_object_flags(object_flags) {
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
        let object_flags = object_flags.normalized_for_new_type();
        if !self.valid_record_types(&types) || !Self::valid_intersection_object_flags(object_flags)
        {
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

    /// Replaces cached/modifier object flags without permitting a payload-kind
    /// transition. Interface `Reference` state is changed atomically by
    /// [`Self::initialize_interface_type_parameters`], not through this method.
    pub fn set_type_object_flags(&mut self, id: TypeId, object_flags: ObjectFlags) -> bool {
        let Some(record) = self.type_payload(id) else {
            return false;
        };
        if !Self::valid_object_flag_transition(record, object_flags) {
            return false;
        }
        if record.object_flags == object_flags {
            return true;
        }
        let relation_dirty = self.relation_type_is_observable(id);
        let preserves_union_cache_identity = matches!(record.data, TypeData::Union(_))
            && Self::union_cache_lazy_object_flag_transition(record.object_flags, object_flags);
        let Some(record) = self.type_payload_mut(id) else {
            return false;
        };
        record.object_flags = object_flags;
        if relation_dirty {
            self.mark_relation_inputs_dirty();
        }
        if !preserves_union_cache_identity {
            self.mark_union_cache_validation_dirty();
        }
        true
    }

    /// Adds lazy, propagation, or payload-specific object flags atomically.
    pub fn add_type_object_flags(&mut self, id: TypeId, added: ObjectFlags) -> bool {
        let Some(current) = self.type_payload(id).map(TypeRecord::object_flags) else {
            return false;
        };
        self.set_type_object_flags(id, current | added)
    }

    /// Copies compatible object flags while clearing caller-selected cache or
    /// freshness bits, as required by cloning and object-literal regularization.
    pub fn copy_type_object_flags(
        &mut self,
        target: TypeId,
        source: TypeId,
        excluded: ObjectFlags,
    ) -> bool {
        let Some(source_flags) = self.type_payload(source).map(TypeRecord::object_flags) else {
            return false;
        };
        self.set_type_object_flags(target, source_flags & !excluded)
    }

    /// Adds the only post-construction `TypeFlags` refinements used upstream:
    /// `Boolean` and `EnumLiteral` on union payloads.
    pub fn add_type_flags(&mut self, id: TypeId, added: TypeFlags) -> bool {
        let Some(record) = self.type_payload(id) else {
            return false;
        };
        let candidate = record.flags | added;
        if !Self::valid_type_flag_transition(record, candidate) {
            return false;
        }
        if record.flags == candidate {
            return true;
        }
        let relation_dirty = self.relation_type_is_observable(id);
        let Some(record) = self.type_payload_mut(id) else {
            return false;
        };
        record.flags = candidate;
        if relation_dirty {
            self.mark_relation_inputs_dirty();
        }
        self.mark_union_cache_validation_dirty();
        true
    }

    /// Copies flags only when the target payload can legally carry them and
    /// the copy does not remove an existing refinement.
    pub fn copy_type_flags(&mut self, target: TypeId, source: TypeId) -> bool {
        let Some(source_flags) = self.type_payload(source).map(TypeRecord::flags) else {
            return false;
        };
        let Some(target_record) = self.type_payload(target) else {
            return false;
        };
        if !Self::valid_type_flag_transition(target_record, source_flags) {
            return false;
        }
        if target_record.flags == source_flags {
            return true;
        }
        let relation_dirty = self.relation_type_is_observable(target);
        let Some(target_record) = self.type_payload_mut(target) else {
            return false;
        };
        target_record.flags = source_flags;
        if relation_dirty {
            self.mark_relation_inputs_dirty();
        }
        self.mark_union_cache_validation_dirty();
        true
    }

    pub fn set_type_symbol(&mut self, id: TypeId, symbol: Option<SemanticSymbolId>) -> bool {
        let Some(record) = self.type_payload(id) else {
            return false;
        };
        if matches!(record.data, TypeData::UniqueEsSymbol(_)) || !self.valid_record_symbol(symbol) {
            return false;
        }
        if record.symbol == symbol {
            return true;
        }
        let relation_dirty = self.relation_type_is_observable(id);
        let Some(record) = self.type_payload_mut(id) else {
            return false;
        };
        record.symbol = symbol;
        if relation_dirty {
            self.mark_relation_inputs_dirty();
        }
        self.mark_union_cache_validation_dirty();
        true
    }

    pub fn set_type_alias(&mut self, id: TypeId, alias: Option<TypeAliasId>) -> bool {
        if !self.valid_record_alias(alias) {
            return false;
        }
        if alias.and_then(|alias| self.type_alias(alias)).is_some_and(|alias| alias.imported_body().is_some())
            && self.type_payload(id).is_none_or(|record| {
                !record.object_flags().contains(ObjectFlags::ANONYMOUS | ObjectFlags::INSTANTIATED)
                    || !matches!(record.data(), TypeData::Object(object) if object.target.is_some() && object.mapper.is_some())
            })
        {
            return false;
        }
        let Some(current) = self.type_payload(id).map(TypeRecord::alias) else {
            return false;
        };
        if current == alias {
            return true;
        }
        let relation_dirty = self.relation_type_is_observable(id);
        let Some(record) = self.type_payload_mut(id) else {
            return false;
        };
        record.alias = alias;
        if relation_dirty {
            self.mark_relation_inputs_dirty();
        }
        self.mark_union_cache_validation_dirty();
        true
    }

    pub fn set_resolved_base_constraint(&mut self, id: TypeId, constraint: Option<TypeId>) -> bool {
        if !self.valid_optional_record_type(constraint) {
            return false;
        }
        let relation_dirty = self.relation_type_is_observable(id)
            && self
                .type_payload(id)
                .and_then(|record| record.data.constrained())
                .is_some_and(|constrained| constrained.resolved_base_constraint != constraint);
        let dirty = self.type_is_exact_callable_object(id);
        let Some(constrained) = self
            .type_payload_mut(id)
            .and_then(|record| record.data.constrained_mut())
        else {
            return false;
        };
        constrained.resolved_base_constraint = constraint;
        if relation_dirty {
            self.mark_relation_inputs_dirty();
        }
        if dirty {
            self.mark_union_cache_validation_dirty();
        }
        true
    }

    #[allow(clippy::too_many_arguments)] // Mirrors setStructuredTypeMembers and its derived properties.
    pub fn set_structured_type_members(
        &mut self,
        id: TypeId,
        members: Option<SymbolTableId>,
        properties: Option<Vec<SemanticSymbolId>>,
        call_signatures: Option<Vec<SignatureId>>,
        construct_signatures: Option<Vec<SignatureId>>,
        index_infos: Option<Vec<IndexInfoId>>,
    ) -> bool {
        if !self.valid_symbol_table(members)
            || !self.valid_optional_record_symbols(properties.as_deref())
            || !self.valid_optional_record_signatures(call_signatures.as_deref())
            || !self.valid_optional_record_signatures(construct_signatures.as_deref())
            || !self.valid_optional_record_index_infos(index_infos.as_deref())
        {
            return false;
        }
        let call_count = call_signatures.as_ref().map_or(0, Vec::len);
        let dirty = self.type_is_exact_callable_object(id)
            && self
                .type_payload(id)
                .and_then(|record| record.data().structured())
                .is_some_and(|structured| structured != &StructuredTypeData::default());
        let signatures = match (call_signatures, construct_signatures) {
            (None, None) => None,
            (Some(call), None) if call.is_empty() => None,
            (None, Some(construct)) if construct.is_empty() => None,
            (Some(call), Some(construct)) if call.is_empty() && construct.is_empty() => None,
            (Some(call), None) => Some(call),
            (None, Some(construct)) => Some(construct),
            (Some(call), Some(construct)) if call.is_empty() => Some(construct),
            (Some(call), Some(construct)) if construct.is_empty() => Some(call),
            (Some(call), Some(construct)) => Some(call.into_iter().chain(construct).collect()),
        };
        let relation_dirty = self.relation_type_is_observable(id)
            && self.type_payload(id).is_some_and(|record| {
                record.data().structured().is_some_and(|structured| {
                    structured.members != members
                        || structured.properties.as_ref() != properties.as_ref()
                        || structured.signatures.as_ref() != signatures.as_ref()
                        || structured.call_signature_count != call_count
                        || structured.index_infos.as_ref() != index_infos.as_ref()
                })
            });
        {
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
        }
        if relation_dirty {
            self.mark_relation_inputs_dirty();
        }
        if dirty {
            self.mark_union_cache_validation_dirty();
        }
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
        let relation_dirty = self.relation_type_is_observable(id)
            && self
                .type_payload(id)
                .and_then(|record| record.data.structured())
                .is_some_and(|structured| {
                    structured.object_type_without_abstract_construct_signatures != value
                });
        let dirty = self.type_is_exact_callable_object(id);
        let Some(structured) = self
            .type_payload_mut(id)
            .and_then(|record| record.data.structured_mut())
        else {
            return false;
        };
        structured.object_type_without_abstract_construct_signatures = value;
        if relation_dirty {
            self.mark_relation_inputs_dirty();
        }
        if dirty {
            self.mark_union_cache_validation_dirty();
        }
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
        if matches!(
            self.type_payload(id).map(TypeRecord::data),
            Some(TypeData::Interface(_) | TypeData::Tuple(_))
        ) {
            return false;
        }
        let relation_dirty = self.relation_type_is_observable(id)
            && self
                .type_payload(id)
                .and_then(|record| record.data.object())
                .is_some_and(|object| object.target != target || object.mapper != mapper);
        let dirty = self.type_is_exact_callable_object(id);
        let Some(object) = self
            .type_payload_mut(id)
            .and_then(|record| record.data.object_mut())
        else {
            return false;
        };
        object.target = target;
        object.mapper = mapper;
        if relation_dirty {
            self.mark_relation_inputs_dirty();
        }
        if dirty {
            self.mark_union_cache_validation_dirty();
        }
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
        if matches!(
            self.type_payload(id).map(TypeRecord::data),
            Some(TypeData::Interface(_) | TypeData::Tuple(_))
        ) {
            return false;
        }
        let relation_dirty = self
            .type_payload(id)
            .and_then(|record| record.data.object())
            .is_some_and(|object| {
                (self.relation_type_is_observable(id) && object.instantiations != instantiations)
                    || self.relation_observes_object_instantiation_change(
                        id,
                        &object.instantiations,
                        &instantiations,
                    )
            });
        let dirty = self.type_is_exact_callable_object(id);
        let Some(object) = self
            .type_payload_mut(id)
            .and_then(|record| record.data.object_mut())
        else {
            return false;
        };
        object.instantiations = instantiations;
        if relation_dirty {
            self.mark_relation_inputs_dirty();
        }
        if dirty {
            self.mark_union_cache_validation_dirty();
        }
        true
    }

    /// Reads one exact object-instantiation entry for a relation query.
    ///
    /// The owner type is observed by [`Self::type_payload`], while the exact
    /// key lets ordinary insertions avoid invalidating relations that read a
    /// different entry in the same target-local cache.
    pub(super) fn relation_object_instantiation(
        &self,
        id: TypeId,
        key: CacheHashKey,
    ) -> Option<TypeId> {
        self.observe_relation_object_instantiation_read(id, key);
        let object = self.type_payload(id)?.data.object()?;
        let TypeCacheState::Allocated(instantiations) = &object.instantiations else {
            return None;
        };
        instantiations.get(&key).copied()
    }

    /// Reserves target-local instantiation slots without allocating a nil map.
    /// Foreign, non-object, and unallocated-cache identities fail unchanged.
    pub(super) fn try_reserve_object_instantiations(
        &mut self,
        id: TypeId,
        additional: usize,
    ) -> bool {
        let Some(object) = self
            .type_payload_mut(id)
            .and_then(|record| record.data.object_mut())
        else {
            return false;
        };
        let TypeCacheState::Allocated(instantiations) = &mut object.instantiations else {
            return false;
        };
        instantiations.try_reserve(additional).is_ok()
    }

    /// Publishes one object instantiation without replacing an existing cache
    /// entry. Returns the canonical entry for `key`, whether pre-existing or
    /// newly inserted.
    ///
    /// Origin interface and tuple caches are allocated by
    /// [`Self::initialize_interface_type_parameters`]. Their non-self entries
    /// must be type references targeting that origin. Other object caches retain
    /// the broader upstream instantiation value shape.
    pub fn insert_object_instantiation(
        &mut self,
        id: TypeId,
        key: CacheHashKey,
        instantiation: TypeId,
    ) -> Option<TypeId> {
        if !self.valid_record_type(instantiation) {
            return None;
        }
        let origin_interface = matches!(
            self.type_payload(id).map(TypeRecord::data),
            Some(TypeData::Interface(_) | TypeData::Tuple(_))
        );
        if origin_interface
            && instantiation != id
            && !matches!(
                self.type_payload(instantiation).map(TypeRecord::data),
                Some(TypeData::TypeReference(data)) if data.object.target == Some(id)
            )
        {
            return None;
        }
        let relation_dirty = self.relation_object_instantiation_map_is_observable(id)
            || self.relation_object_instantiation_is_observable(id, key);
        let object = self
            .type_payload_mut(id)
            .and_then(|record| record.data.object_mut())?;
        let TypeCacheState::Allocated(instantiations) = &mut object.instantiations else {
            return None;
        };
        if let Some(existing) = instantiations.get(&key) {
            return Some(*existing);
        }
        if origin_interface && instantiation == id {
            return None;
        }
        instantiations.insert(key, instantiation);
        if relation_dirty {
            self.mark_relation_inputs_dirty();
        }
        Some(instantiation)
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
        if matches!(
            self.type_payload(id).map(TypeRecord::data),
            Some(TypeData::Interface(_) | TypeData::Tuple(_))
        ) {
            return false;
        }
        let relation_dirty = self.relation_type_is_observable(id)
            && self
                .type_payload(id)
                .and_then(|record| record.data.reference())
                .is_some_and(|reference| {
                    reference.node != node
                        || reference.resolved_type_arguments.as_ref()
                            != resolved_type_arguments.as_ref()
                });
        let Some(reference) = self
            .type_payload_mut(id)
            .and_then(|record| record.data.reference_mut())
        else {
            return false;
        };
        reference.node = node;
        reference.resolved_type_arguments = resolved_type_arguments;
        if relation_dirty {
            self.mark_relation_inputs_dirty();
        }
        true
    }

    /// Initializes the one recursive `this` edge of a class, interface, or
    /// tuple target. `self_instantiation_key` is the pinned `getTypeListKey`
    /// for `all_type_parameters` excluding the final `this_type`.
    ///
    /// The pinned constructors allocate a fresh type parameter and publish its
    /// `isThisType` marker, self constraint, owner target, resolved arguments,
    /// initial self-instantiation cache, the owner's `thisType`, and its
    /// `Reference` flag as one initialization sequence. This operation validates
    /// the complete transition before changing either record and may only be
    /// performed once. Generic object/reference setters intentionally cannot
    /// replace those origin-interface fields afterward.
    pub fn initialize_interface_type_parameters(
        &mut self,
        id: TypeId,
        all_type_parameters: Vec<TypeId>,
        outer_type_parameter_count: usize,
        this_type: TypeId,
        self_instantiation_key: CacheHashKey,
    ) -> bool {
        let Some(record) = self.type_payload(id) else {
            return false;
        };
        let (is_tuple, is_uninitialized) = match &record.data {
            TypeData::Interface(data) => (
                false,
                data.all_type_parameters.is_none()
                    && data.outer_type_parameter_count == 0
                    && data.this_type.is_none()
                    && data.reference.object.target.is_none()
                    && data.reference.object.mapper.is_none()
                    && data.reference.object.instantiations == TypeCacheState::Unallocated
                    && data.reference.node.is_none()
                    && data.reference.resolved_type_arguments.is_none(),
            ),
            TypeData::Tuple(data) => (
                true,
                data.interface.all_type_parameters.is_none()
                    && data.interface.outer_type_parameter_count == 0
                    && data.interface.this_type.is_none()
                    && data.interface.reference.object.target.is_none()
                    && data.interface.reference.object.mapper.is_none()
                    && data.interface.reference.object.instantiations
                        == TypeCacheState::Unallocated
                    && data.interface.reference.node.is_none()
                    && data.interface.reference.resolved_type_arguments.is_none(),
            ),
            _ => return false,
        };
        if !is_uninitialized
            || record.object_flags.contains(ObjectFlags::REFERENCE) != is_tuple
            || all_type_parameters.is_empty()
            || all_type_parameters.last().copied() != Some(this_type)
            || all_type_parameters[..all_type_parameters.len() - 1].contains(&this_type)
            || outer_type_parameter_count >= all_type_parameters.len()
            || (is_tuple && outer_type_parameter_count != 0)
            || !self.valid_record_types(&all_type_parameters)
            || !all_type_parameters.iter().all(|parameter| {
                matches!(
                    self.type_payload(*parameter).map(TypeRecord::data),
                    Some(TypeData::TypeParameter(_))
                )
            })
            || !matches!(
                self.type_payload(this_type).map(TypeRecord::data),
                Some(TypeData::TypeParameter(data)) if data == &TypeParameterData::default()
            )
        {
            return false;
        }

        let resolved_type_arguments = all_type_parameters[..all_type_parameters.len() - 1].to_vec();
        let instantiations =
            TypeCacheState::Allocated(HashMap::from([(self_instantiation_key, id)]));
        let relation_dirty =
            self.relation_type_is_observable(id) || self.relation_type_is_observable(this_type);

        // Both records and their exact payload kinds were validated above, and
        // all allocations are complete before the first mutation is made.
        let Some(TypeData::TypeParameter(this_data)) = self
            .type_payload_mut(this_type)
            .map(|record| &mut record.data)
        else {
            unreachable!("validated this type parameter disappeared")
        };
        this_data.constraint = Some(id);
        this_data.is_this_type = true;

        let Some(record) = self.type_payload_mut(id) else {
            unreachable!("validated interface or tuple disappeared")
        };
        let Some(interface) = record.data.interface_mut() else {
            unreachable!("validated interface or tuple changed payload kind")
        };
        interface.all_type_parameters = Some(all_type_parameters);
        interface.outer_type_parameter_count = outer_type_parameter_count;
        interface.this_type = Some(this_type);
        interface.reference.object.target = Some(id);
        interface.reference.object.instantiations = instantiations;
        interface.reference.resolved_type_arguments = Some(resolved_type_arguments);
        record.object_flags |= ObjectFlags::REFERENCE;
        if relation_dirty {
            self.mark_relation_inputs_dirty();
        }
        true
    }

    /// Publishes the complete recursive target graph created by pinned
    /// `createTupleTargetType`.
    ///
    /// All fallible capacity work is performed by the tuple constructor before
    /// this transition. The supplied cache therefore already owns its exact
    /// self-instantiation entry and may retain spare capacity for the concrete
    /// reference created by the same request.
    pub(super) fn initialize_tuple_target(
        &mut self,
        id: TypeId,
        resolved_type_arguments: Vec<TypeId>,
        all_type_parameters: Vec<TypeId>,
        this_type: TypeId,
        declared_members: SymbolTableId,
        instantiations: TypeCacheState,
    ) -> bool {
        let Some(record) = self.type_payload(id) else {
            return false;
        };
        let TypeData::Tuple(tuple) = record.data() else {
            return false;
        };
        if record.flags() != TypeFlags::OBJECT
            || record.object_flags() != (ObjectFlags::REFERENCE | ObjectFlags::TUPLE)
            || record.symbol().is_some()
            || record.alias().is_some()
            || tuple.interface != InterfaceTypeData::default()
            || tuple.metadata.element_infos().len() != resolved_type_arguments.len()
            || self.symbol_table(declared_members).is_none()
            || all_type_parameters.len() != resolved_type_arguments.len() + 1
            || &all_type_parameters[..resolved_type_arguments.len()]
                != resolved_type_arguments.as_slice()
            || all_type_parameters.last().copied() != Some(this_type)
            || resolved_type_arguments.contains(&this_type)
            || resolved_type_arguments
                .iter()
                .enumerate()
                .any(|(index, parameter)| resolved_type_arguments[..index].contains(parameter))
            || !resolved_type_arguments.iter().all(|parameter| {
                matches!(
                    self.type_payload(*parameter),
                    Some(parameter_record)
                        if parameter_record.flags() == TypeFlags::TYPE_PARAMETER
                            && parameter_record.object_flags().is_empty()
                            && parameter_record.symbol().is_none()
                            && parameter_record.alias().is_none()
                            && matches!(
                                parameter_record.data(),
                                TypeData::TypeParameter(data)
                                    if data == &TypeParameterData::default()
                            )
                )
            })
        {
            return false;
        }
        let Some(this_record) = self.type_payload(this_type) else {
            return false;
        };
        if this_record.flags() != TypeFlags::TYPE_PARAMETER
            || !this_record.object_flags().is_empty()
            || this_record.symbol().is_some()
            || this_record.alias().is_some()
            || !matches!(
                this_record.data(),
                TypeData::TypeParameter(data) if data == &TypeParameterData::default()
            )
        {
            return false;
        }
        let TypeCacheState::Allocated(cache) = &instantiations else {
            return false;
        };
        if cache.len() != 1 || cache.get(&type_list_key(&resolved_type_arguments)) != Some(&id) {
            return false;
        }
        let relation_dirty =
            self.relation_type_is_observable(id) || self.relation_type_is_observable(this_type);

        let Some(TypeData::TypeParameter(this_data)) = self
            .type_payload_mut(this_type)
            .map(|record| &mut record.data)
        else {
            unreachable!("validated empty-tuple this type disappeared")
        };
        this_data.constraint = Some(id);
        this_data.is_this_type = true;

        let Some(TypeData::Tuple(tuple)) = self.type_payload_mut(id).map(|record| &mut record.data)
        else {
            unreachable!("validated tuple target disappeared")
        };
        tuple.interface.all_type_parameters = Some(all_type_parameters);
        tuple.interface.this_type = Some(this_type);
        tuple.interface.reference.object.target = Some(id);
        tuple.interface.reference.object.instantiations = instantiations;
        tuple.interface.reference.resolved_type_arguments = Some(resolved_type_arguments);
        tuple.interface.declared_members_resolved = true;
        tuple.interface.declared_members = Some(declared_members);
        if relation_dirty {
            self.mark_relation_inputs_dirty();
        }
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
        let relation_dirty = self.relation_type_is_observable(id)
            && self
                .type_payload(id)
                .and_then(|record| record.data.interface())
                .is_some_and(|interface| {
                    interface.base_types_resolved != base_types_resolved
                        || interface.resolved_base_constructor_type
                            != resolved_base_constructor_type
                        || interface.resolved_base_types.as_ref() != resolved_base_types.as_ref()
                });
        let Some(interface) = self
            .type_payload_mut(id)
            .and_then(|record| record.data.interface_mut())
        else {
            return false;
        };
        interface.base_types_resolved = base_types_resolved;
        interface.resolved_base_constructor_type = resolved_base_constructor_type;
        interface.resolved_base_types = resolved_base_types;
        if relation_dirty {
            self.mark_relation_inputs_dirty();
        }
        true
    }

    /// Atomically publishes the cold interface result produced when every
    /// declaration has no heritage clause. This mirrors pinned `getBaseTypes`:
    /// resolving bases invalidates the structured-member cache even when the
    /// resolved base list is absent rather than allocated empty.
    pub(super) fn publish_interface_no_base_resolution(&mut self, id: TypeId) -> bool {
        let relation_dirty = self.relation_type_is_observable(id);
        let Some(record) = self.type_payload_mut(id) else {
            return false;
        };
        if !record.object_flags.contains(ObjectFlags::INTERFACE) {
            return false;
        }
        let TypeData::Interface(interface) = &mut record.data else {
            return false;
        };
        if interface.base_types_resolved
            || interface.resolved_base_constructor_type.is_some()
            || interface.resolved_base_types.is_some()
        {
            return false;
        }
        interface.base_types_resolved = true;
        record.object_flags &= !ObjectFlags::MEMBERS_RESOLVED;
        if relation_dirty {
            self.mark_relation_inputs_dirty();
        }
        true
    }

    #[allow(clippy::too_many_arguments)] // Mirrors the declared-member caches exactly.
    pub fn set_interface_declared_members(
        &mut self,
        id: TypeId,
        resolved: bool,
        members: Option<SymbolTableId>,
        call_signatures: Option<Vec<SignatureId>>,
        construct_signatures: Option<Vec<SignatureId>>,
        index_infos: Option<Vec<IndexInfoId>>,
    ) -> bool {
        if !self.valid_symbol_table(members)
            || !self.valid_optional_record_signatures(call_signatures.as_deref())
            || !self.valid_optional_record_signatures(construct_signatures.as_deref())
            || !self.valid_optional_record_index_infos(index_infos.as_deref())
        {
            return false;
        }
        let relation_dirty = self.relation_type_is_observable(id)
            && self
                .type_payload(id)
                .and_then(|record| record.data.interface())
                .is_some_and(|interface| {
                    interface.declared_members_resolved != resolved
                        || interface.declared_members != members
                        || interface.declared_call_signatures.as_ref() != call_signatures.as_ref()
                        || interface.declared_construct_signatures.as_ref()
                            != construct_signatures.as_ref()
                        || interface.declared_index_infos.as_ref() != index_infos.as_ref()
                });
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
        if relation_dirty {
            self.mark_relation_inputs_dirty();
        }
        true
    }

    pub fn set_instantiation_expression_node(&mut self, id: TypeId, node: Option<NodeRef>) -> bool {
        if !self.valid_record_node(node) {
            return false;
        }
        let relation_dirty = self.relation_type_is_observable(id)
            && self.type_payload(id).is_some_and(|record| {
                matches!(&record.data, TypeData::InstantiationExpression(data) if data.node != node)
            });
        let Some(TypeData::InstantiationExpression(data)) =
            self.type_payload_mut(id).map(|record| &mut record.data)
        else {
            return false;
        };
        data.node = node;
        if relation_dirty {
            self.mark_relation_inputs_dirty();
        }
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
        let relation_dirty = self.relation_type_is_observable(id)
            && self.type_payload(id).is_some_and(|record| {
                matches!(&record.data, TypeData::Mapped(data)
                    if data.declaration != declaration
                        || data.type_parameter != type_parameter
                        || data.constraint_type != constraint_type
                        || data.name_type != name_type
                        || data.template_type != template_type
                        || data.modifiers_type != modifiers_type
                        || data.resolved_apparent_type != resolved_apparent_type
                        || data.contains_error != contains_error)
            });
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
        if relation_dirty {
            self.mark_relation_inputs_dirty();
        }
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
        let relation_dirty = self.relation_type_is_observable(id)
            && self.type_payload(id).is_some_and(|record| {
                matches!(&record.data, TypeData::ReverseMapped(data)
                    if data.source != source
                        || data.mapped_type != mapped_type
                        || data.constraint_type != constraint_type)
            });
        let Some(TypeData::ReverseMapped(data)) =
            self.type_payload_mut(id).map(|record| &mut record.data)
        else {
            return false;
        };
        data.source = source;
        data.mapped_type = mapped_type;
        data.constraint_type = constraint_type;
        if relation_dirty {
            self.mark_relation_inputs_dirty();
        }
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
        let relation_dirty = self.relation_type_is_observable(id)
            && self.type_payload(id).is_some_and(|record| {
                matches!(&record.data, TypeData::EvolvingArray(data)
                    if data.element_type != element_type
                        || data.final_array_type != final_array_type)
            });
        let Some(TypeData::EvolvingArray(data)) =
            self.type_payload_mut(id).map(|record| &mut record.data)
        else {
            return false;
        };
        data.element_type = element_type;
        data.final_array_type = final_array_type;
        if relation_dirty {
            self.mark_relation_inputs_dirty();
        }
        true
    }

    pub fn set_union_or_intersection_caches(
        &mut self,
        id: TypeId,
        property_cache: Option<SymbolTableId>,
        property_cache_without_function_property_augment: Option<SymbolTableId>,
        resolved_properties: Option<Vec<SemanticSymbolId>>,
    ) -> bool {
        if !self.valid_symbol_table(property_cache)
            || !self.valid_symbol_table(property_cache_without_function_property_augment)
            || !self.valid_optional_record_symbols(resolved_properties.as_deref())
        {
            return false;
        }
        let relation_dirty = self.relation_type_is_observable(id)
            && self.type_payload(id).is_some_and(|record| {
                let union = match &record.data {
                    TypeData::Union(data) => &data.union,
                    TypeData::Intersection(data) => &data.intersection,
                    _ => return false,
                };
                union.property_cache != property_cache
                    || union.property_cache_without_function_property_augment
                        != property_cache_without_function_property_augment
                    || union.resolved_properties.as_ref() != resolved_properties.as_ref()
            });
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
        if relation_dirty {
            self.mark_relation_inputs_dirty();
        }
        true
    }

    #[allow(clippy::too_many_arguments)] // Mirrors the union-only lazy caches.
    pub fn set_union_caches(
        &mut self,
        id: TypeId,
        resolved_reduced_type: Option<TypeId>,
        regular_type: Option<TypeId>,
        origin: Option<TypeId>,
        key_property_name: EscapedName,
        constituent_map: ConstituentMapState,
    ) -> bool {
        if ![resolved_reduced_type, regular_type, origin]
            .into_iter()
            .all(|value| self.valid_optional_record_type(value))
            || !self.valid_union_discriminant_cache(&key_property_name, &constituent_map)
        {
            return false;
        }
        let relation_dirty = self.relation_type_is_observable(id)
            && self.type_payload(id).is_some_and(|record| {
                matches!(&record.data, TypeData::Union(data)
                    if data.resolved_reduced_type != resolved_reduced_type
                        || data.regular_type != regular_type
                        || data.origin != origin
                        || data.key_property_name != key_property_name
                        || data.constituent_map != constituent_map)
            });
        let Some(TypeData::Union(data)) = self.type_payload_mut(id).map(|record| &mut record.data)
        else {
            return false;
        };
        data.resolved_reduced_type = resolved_reduced_type;
        data.regular_type = regular_type;
        data.origin = origin;
        data.key_property_name = key_property_name;
        data.constituent_map = constituent_map;
        if relation_dirty {
            self.mark_relation_inputs_dirty();
        }
        self.mark_union_cache_validation_dirty();
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
        let relation_dirty = self.relation_type_is_observable(id)
            && self.type_payload(id).is_some_and(|record| {
                matches!(&record.data, TypeData::Intersection(data)
                    if data.resolved_apparent_type != resolved_apparent_type
                        || data.unique_literal_filled_instantiation
                            != unique_literal_filled_instantiation)
            });
        let Some(TypeData::Intersection(data)) =
            self.type_payload_mut(id).map(|record| &mut record.data)
        else {
            return false;
        };
        data.resolved_apparent_type = resolved_apparent_type;
        data.unique_literal_filled_instantiation = unique_literal_filled_instantiation;
        if relation_dirty {
            self.mark_relation_inputs_dirty();
        }
        true
    }

    /// Updates lazy resolution fields of an ordinary type parameter.
    ///
    /// An initialized interface/tuple `this` parameter may update the other
    /// lazy fields only while preserving its self constraint. Its identity
    /// marker can only be established by
    /// [`Self::initialize_interface_type_parameters`].
    pub fn set_type_parameter_resolution(
        &mut self,
        id: TypeId,
        constraint: Option<TypeId>,
        target: Option<TypeId>,
        mapper: Option<TypeMapperId>,
        resolved_default_type: Option<TypeId>,
    ) -> bool {
        if ![constraint, target, resolved_default_type]
            .into_iter()
            .all(|value| self.valid_optional_record_type(value))
            || !self.valid_record_mapper(mapper)
        {
            return false;
        }
        let relation_dirty = self.relation_type_is_observable(id)
            && self.type_payload(id).is_some_and(|record| {
                matches!(&record.data, TypeData::TypeParameter(data)
                    if data.constraint != constraint
                        || data.target != target
                        || data.mapper != mapper
                        || data.resolved_default_type != resolved_default_type)
            });
        let Some(TypeData::TypeParameter(data)) =
            self.type_payload_mut(id).map(|record| &mut record.data)
        else {
            return false;
        };
        if data.is_this_type && data.constraint != constraint {
            return false;
        }
        data.constraint = constraint;
        data.target = target;
        data.mapper = mapper;
        data.resolved_default_type = resolved_default_type;
        if relation_dirty {
            self.mark_relation_inputs_dirty();
        }
        true
    }

    pub fn set_literal_links(
        &mut self,
        id: TypeId,
        fresh_type: Option<TypeId>,
        regular_type: TypeId,
    ) -> bool {
        let compatible = self.type_payload(id).is_some_and(|record| {
            let TypeData::Literal(data) = &record.data else {
                return false;
            };
            self.type_payload(regular_type).is_some_and(|candidate| {
                Self::record_is_compatible_literal(candidate, record.flags, &data.value)
            }) && fresh_type.is_none_or(|fresh_type| {
                self.type_payload(fresh_type).is_some_and(|candidate| {
                    Self::record_is_compatible_literal(candidate, record.flags, &data.value)
                })
            })
        });
        if !compatible {
            return false;
        }
        let relation_dirty = self.relation_type_is_observable(id)
            && self.type_payload(id).is_some_and(|record| {
                matches!(&record.data, TypeData::Literal(data)
                    if data.fresh_type != fresh_type || data.regular_type != regular_type)
            });
        let Some(TypeData::Literal(data)) =
            self.type_payload_mut(id).map(|record| &mut record.data)
        else {
            return false;
        };
        data.fresh_type = fresh_type;
        data.regular_type = regular_type;
        if relation_dirty {
            self.mark_relation_inputs_dirty();
        }
        self.mark_union_cache_validation_dirty();
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
        let relation_dirty = self.relation_type_is_observable(id)
            && self.type_payload(id).is_some_and(|record| {
                matches!(&record.data, TypeData::Conditional(data)
                    if data.resolved_true_type != resolved_true_type
                        || data.resolved_false_type != resolved_false_type
                        || data.resolved_inferred_true_type != resolved_inferred_true_type
                        || data.resolved_default_constraint != resolved_default_constraint
                        || data.resolved_constraint_of_distributive
                            != resolved_constraint_of_distributive
                        || data.mapper != mapper
                        || data.combined_mapper != combined_mapper)
            });
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
        if relation_dirty {
            self.mark_relation_inputs_dirty();
        }
        true
    }

    fn valid_record_type(&self, id: TypeId) -> bool {
        self.type_payload(id).is_some()
    }

    fn object_kind_matches(flags: ObjectFlags, allowed: ObjectFlags) -> bool {
        flags.bits() & (1 << 31) == 0
            && (flags & ObjectFlags::OBJECT_TYPE_KIND_MASK & !allowed).is_empty()
    }

    fn has_exactly_one_interface_origin(flags: ObjectFlags) -> bool {
        let origin = flags & ObjectFlags::CLASS_OR_INTERFACE;
        origin == ObjectFlags::CLASS || origin == ObjectFlags::INTERFACE
    }

    fn object_flags_are_subset(flags: ObjectFlags, allowed: ObjectFlags) -> bool {
        flags.bits() & !allowed.bits() == 0
    }

    fn valid_intrinsic_flags(flags: TypeFlags) -> bool {
        flags.bits().is_power_of_two() && TypeFlags::INTRINSIC.contains(flags)
    }

    fn valid_literal_flags(value: &LiteralValue, flags: TypeFlags) -> bool {
        match value {
            LiteralValue::String(_) => {
                flags == TypeFlags::STRING_LITERAL
                    || flags == TypeFlags::STRING_LITERAL | TypeFlags::ENUM_LITERAL
            }
            LiteralValue::Number(_) => {
                flags == TypeFlags::NUMBER_LITERAL
                    || flags == TypeFlags::NUMBER_LITERAL | TypeFlags::ENUM_LITERAL
            }
            LiteralValue::Boolean(_) => flags == TypeFlags::BOOLEAN_LITERAL,
            LiteralValue::BigInt(_) => flags == TypeFlags::BIG_INT_LITERAL,
            LiteralValue::ComputedEnum => flags == TypeFlags::ENUM,
        }
    }

    fn literal_values_are_equal(left: &LiteralValue, right: &LiteralValue) -> bool {
        match (left, right) {
            (LiteralValue::String(left), LiteralValue::String(right)) => left == right,
            (LiteralValue::Number(left), LiteralValue::Number(right)) => {
                left == right || left.is_nan() && right.is_nan()
            }
            (LiteralValue::Boolean(left), LiteralValue::Boolean(right)) => left == right,
            (LiteralValue::BigInt(left), LiteralValue::BigInt(right)) => left == right,
            (LiteralValue::ComputedEnum, LiteralValue::ComputedEnum) => true,
            _ => false,
        }
    }

    fn record_is_compatible_literal(
        record: &TypeRecord,
        flags: TypeFlags,
        value: &LiteralValue,
    ) -> bool {
        matches!(
            &record.data,
            TypeData::Literal(data)
                if record.flags == flags && Self::literal_values_are_equal(&data.value, value)
        )
    }

    /// Checks the record header without resolving its members or operands.
    pub(super) fn type_record_header_is_valid(&self, type_: TypeId) -> bool {
        self.type_payload(type_).is_some_and(|record| {
            Self::valid_type_flags_for_record(record, record.flags)
                && Self::valid_object_flags_for_record(record, record.object_flags)
        })
    }

    fn valid_type_flags_for_record(record: &TypeRecord, flags: TypeFlags) -> bool {
        match &record.data {
            TypeData::Intrinsic(_) => Self::valid_intrinsic_flags(flags),
            TypeData::Literal(data) => Self::valid_literal_flags(&data.value, flags),
            TypeData::UniqueEsSymbol(_) => flags == TypeFlags::UNIQUE_ES_SYMBOL,
            TypeData::Object(_)
            | TypeData::TypeReference(_)
            | TypeData::Interface(_)
            | TypeData::Tuple(_)
            | TypeData::InstantiationExpression(_)
            | TypeData::Mapped(_)
            | TypeData::ReverseMapped(_)
            | TypeData::EvolvingArray(_) => flags == TypeFlags::OBJECT,
            TypeData::Union(_) => {
                let allowed = TypeFlags::UNION | TypeFlags::BOOLEAN | TypeFlags::ENUM_LITERAL;
                flags.contains(TypeFlags::UNION)
                    && flags.bits() & !allowed.bits() == 0
                    && !(flags.contains(TypeFlags::BOOLEAN)
                        && flags.contains(TypeFlags::ENUM_LITERAL))
            }
            TypeData::Intersection(_) => flags == TypeFlags::INTERSECTION,
            TypeData::TypeParameter(_) => flags == TypeFlags::TYPE_PARAMETER,
            TypeData::Index(_) => flags == TypeFlags::INDEX,
            TypeData::IndexedAccess(_) => flags == TypeFlags::INDEXED_ACCESS,
            TypeData::TemplateLiteral(_) => flags == TypeFlags::TEMPLATE_LITERAL,
            TypeData::StringMapping(_) => flags == TypeFlags::STRING_MAPPING,
            TypeData::Substitution(_) => flags == TypeFlags::SUBSTITUTION,
            TypeData::Conditional(_) => flags == TypeFlags::CONDITIONAL,
        }
    }

    fn valid_type_flag_transition(record: &TypeRecord, candidate: TypeFlags) -> bool {
        candidate.contains(record.flags) && Self::valid_type_flags_for_record(record, candidate)
    }

    fn common_non_object_flags() -> ObjectFlags {
        ObjectFlags::PROPAGATING_FLAGS
            | ObjectFlags::COULD_CONTAIN_TYPE_VARIABLES_COMPUTED
            | ObjectFlags::COULD_CONTAIN_TYPE_VARIABLES
    }

    pub(super) fn valid_union_object_flags(flags: ObjectFlags) -> bool {
        let allowed = Self::common_non_object_flags()
            | ObjectFlags::MEMBERS_RESOLVED
            | ObjectFlags::PRIMITIVE_UNION
            | ObjectFlags::IS_GENERIC_TYPE_COMPUTED
            | ObjectFlags::IS_GENERIC_TYPE
            | ObjectFlags::CONTAINS_INTERSECTIONS
            | ObjectFlags::IS_UNKNOWN_LIKE_UNION_COMPUTED
            | ObjectFlags::IS_UNKNOWN_LIKE_UNION;
        Self::object_flags_are_subset(flags, allowed)
            && Self::valid_union_cache_lazy_object_flags(
                flags & Self::union_cache_lazy_object_flags(),
            )
    }

    pub(super) fn union_cache_lazy_object_flags() -> ObjectFlags {
        ObjectFlags::MEMBERS_RESOLVED
            | ObjectFlags::COULD_CONTAIN_TYPE_VARIABLES_COMPUTED
            | ObjectFlags::COULD_CONTAIN_TYPE_VARIABLES
            | ObjectFlags::IS_GENERIC_TYPE_COMPUTED
            | ObjectFlags::IS_GENERIC_TYPE
            | ObjectFlags::IS_UNKNOWN_LIKE_UNION_COMPUTED
            | ObjectFlags::IS_UNKNOWN_LIKE_UNION
    }

    pub(super) fn valid_union_cache_lazy_object_flags(flags: ObjectFlags) -> bool {
        let allowed = Self::union_cache_lazy_object_flags();
        Self::object_flags_are_subset(flags, allowed)
            && (!flags.intersects(ObjectFlags::COULD_CONTAIN_TYPE_VARIABLES)
                || flags.intersects(ObjectFlags::COULD_CONTAIN_TYPE_VARIABLES_COMPUTED))
            && (!flags.intersects(ObjectFlags::IS_GENERIC_TYPE)
                || flags.intersects(ObjectFlags::IS_GENERIC_TYPE_COMPUTED))
            && (!flags.intersects(ObjectFlags::IS_UNKNOWN_LIKE_UNION)
                || flags.intersects(ObjectFlags::IS_UNKNOWN_LIKE_UNION_COMPUTED))
    }

    fn union_cache_lazy_object_flag_transition(
        current: ObjectFlags,
        candidate: ObjectFlags,
    ) -> bool {
        let lazy = Self::union_cache_lazy_object_flags();
        (current.bits() ^ candidate.bits()) & !lazy.bits() == 0
            && Self::valid_union_cache_lazy_object_flags(current & lazy)
            && Self::valid_union_cache_lazy_object_flags(candidate & lazy)
    }

    fn valid_intersection_object_flags(flags: ObjectFlags) -> bool {
        let allowed = Self::common_non_object_flags()
            | ObjectFlags::MEMBERS_RESOLVED
            | ObjectFlags::IS_GENERIC_TYPE_COMPUTED
            | ObjectFlags::IS_GENERIC_TYPE
            | ObjectFlags::IS_NEVER_INTERSECTION_COMPUTED
            | ObjectFlags::IS_NEVER_INTERSECTION
            | ObjectFlags::IS_CONSTRAINED_TYPE_VARIABLE;
        Self::object_flags_are_subset(flags, allowed)
    }

    fn valid_object_flags_for_record(record: &TypeRecord, flags: ObjectFlags) -> bool {
        let base_mask = ObjectFlags::CLASS_OR_INTERFACE
            | ObjectFlags::REFERENCE
            | ObjectFlags::TUPLE
            | ObjectFlags::ANONYMOUS
            | ObjectFlags::MAPPED
            | ObjectFlags::REVERSE_MAPPED
            | ObjectFlags::EVOLVING_ARRAY
            | ObjectFlags::INSTANTIATION_EXPRESSION_TYPE;
        let base = flags & base_mask;
        let object_payload_matches = match &record.data {
            TypeData::Object(_) => base == ObjectFlags::ANONYMOUS,
            TypeData::TypeReference(_) => {
                base == ObjectFlags::REFERENCE
                    && !flags.intersects(ObjectFlags::SINGLE_SIGNATURE_TYPE)
            }
            TypeData::Interface(data) => {
                let reference_state = data.all_type_parameters.is_some();
                let expected_base = (flags & ObjectFlags::CLASS_OR_INTERFACE)
                    | if reference_state {
                        ObjectFlags::REFERENCE
                    } else {
                        ObjectFlags::NONE
                    };
                Self::has_exactly_one_interface_origin(flags)
                    && base == expected_base
                    && flags.intersects(ObjectFlags::REFERENCE) == reference_state
                    && !flags.intersects(ObjectFlags::SINGLE_SIGNATURE_TYPE)
            }
            TypeData::Tuple(_) => {
                base == ObjectFlags::REFERENCE | ObjectFlags::TUPLE
                    && !flags.intersects(ObjectFlags::SINGLE_SIGNATURE_TYPE)
            }
            TypeData::InstantiationExpression(_) => {
                base == ObjectFlags::ANONYMOUS | ObjectFlags::INSTANTIATION_EXPRESSION_TYPE
                    && !flags.intersects(ObjectFlags::SINGLE_SIGNATURE_TYPE)
            }
            TypeData::Mapped(_) => {
                base == ObjectFlags::MAPPED && !flags.intersects(ObjectFlags::SINGLE_SIGNATURE_TYPE)
            }
            TypeData::ReverseMapped(_) => {
                base == ObjectFlags::ANONYMOUS | ObjectFlags::REVERSE_MAPPED
                    && !flags.intersects(ObjectFlags::SINGLE_SIGNATURE_TYPE)
            }
            TypeData::EvolvingArray(_) => {
                base == ObjectFlags::EVOLVING_ARRAY
                    && !flags.intersects(ObjectFlags::SINGLE_SIGNATURE_TYPE)
            }
            _ => false,
        };
        if record.flags == TypeFlags::OBJECT {
            return flags.bits() & (1 << 31) == 0 && object_payload_matches;
        }

        let allowed = match &record.data {
            TypeData::Intrinsic(_) => ObjectFlags::PROPAGATING_FLAGS,
            TypeData::Literal(_) | TypeData::UniqueEsSymbol(_) => ObjectFlags::NONE,
            TypeData::Union(_) => return Self::valid_union_object_flags(flags),
            TypeData::Intersection(_) => return Self::valid_intersection_object_flags(flags),
            TypeData::Substitution(_) => {
                Self::common_non_object_flags()
                    | ObjectFlags::IS_GENERIC_TYPE_COMPUTED
                    | ObjectFlags::IS_GENERIC_TYPE
            }
            TypeData::TypeParameter(_)
            | TypeData::Index(_)
            | TypeData::IndexedAccess(_)
            | TypeData::TemplateLiteral(_)
            | TypeData::StringMapping(_)
            | TypeData::Conditional(_) => Self::common_non_object_flags(),
            TypeData::Object(_)
            | TypeData::TypeReference(_)
            | TypeData::Interface(_)
            | TypeData::Tuple(_)
            | TypeData::InstantiationExpression(_)
            | TypeData::Mapped(_)
            | TypeData::ReverseMapped(_)
            | TypeData::EvolvingArray(_) => return false,
        };
        Self::object_flags_are_subset(flags, allowed)
    }

    fn valid_object_flag_transition(record: &TypeRecord, candidate: ObjectFlags) -> bool {
        if !Self::valid_object_flags_for_record(record, candidate) {
            return false;
        }
        if matches!(record.data, TypeData::Interface(_)) {
            return record.object_flags & ObjectFlags::CLASS_OR_INTERFACE
                == candidate & ObjectFlags::CLASS_OR_INTERFACE;
        }
        true
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
        id.is_none_or(|id| self.symbol(id).is_some())
    }

    fn valid_optional_record_symbols(&self, ids: Option<&[SemanticSymbolId]>) -> bool {
        ids.is_none_or(|ids| ids.iter().all(|id| self.symbol(*id).is_some()))
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

    fn valid_symbol_table(&self, table: Option<SymbolTableId>) -> bool {
        table.is_none_or(|table| self.symbol_table(table).is_some())
    }

    fn valid_type_cache(&self, cache: &TypeCacheState) -> bool {
        let TypeCacheState::Allocated(entries) = cache else {
            return true;
        };
        entries.values().all(|value| self.valid_record_type(*value))
    }

    fn valid_constituent_map(&self, map: &ConstituentMapState) -> bool {
        let ConstituentMapState::Allocated(entries) = map else {
            return true;
        };
        entries
            .iter()
            .all(|(key, value)| self.valid_record_type(*key) && self.valid_record_type(*value))
    }

    fn valid_union_discriminant_cache(
        &self,
        key_property_name: &EscapedName,
        constituent_map: &ConstituentMapState,
    ) -> bool {
        if !self.valid_constituent_map(constituent_map) {
            return false;
        }
        match constituent_map {
            ConstituentMapState::Unallocated => {
                key_property_name.is_empty()
                    || key_property_name.as_ref() == InternalSymbolName::Missing.as_ref()
            }
            ConstituentMapState::Allocated(_) => {
                !key_property_name.is_empty()
                    && !key_property_name.as_ref().is_reserved_member_name()
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use ts_ast::{FileId, SyntaxKind};
    use ts_binder::{EscapedName, SymbolData, SymbolFlags};
    use ts_jsnum::{Number, PseudoBigInt};
    use ts_parser::parse_source_file;

    use super::*;
    use crate::semantic::{
        AstScope,
        signatures::{ElementFlags, SignatureFlags},
    };

    type TestStore = CanonicalSemanticStore<&'static str>;

    fn alloc_test_symbol(store: &mut TestStore, name: &str) -> SemanticSymbolId {
        store
            .alloc_symbol(SymbolData::new(
                SymbolFlags::PROPERTY,
                EscapedName::source(name),
            ))
            .unwrap()
    }

    fn alloc_test_table(
        store: &mut TestStore,
        entries: &[(&str, SemanticSymbolId)],
    ) -> SymbolTableId {
        let table = store.alloc_symbol_table();
        for (name, symbol) in entries {
            assert_eq!(
                store.insert_symbol(table, EscapedName::source(name), *symbol),
                Some(None)
            );
        }
        table
    }

    fn type_parameter_snapshot(store: &TestStore, id: TypeId) -> TypeParameterData {
        let TypeData::TypeParameter(data) = store.type_payload(id).unwrap().data() else {
            panic!("expected type parameter")
        };
        data.clone()
    }

    fn interface_snapshot(store: &TestStore, id: TypeId) -> (InterfaceTypeData, ObjectFlags) {
        let record = store.type_payload(id).unwrap();
        let TypeData::Interface(data) = record.data() else {
            panic!("expected interface")
        };
        (data.clone(), record.object_flags())
    }

    fn union_snapshot(store: &TestStore, id: TypeId) -> UnionTypeData {
        let TypeData::Union(data) = store.type_payload(id).unwrap().data() else {
            panic!("expected union")
        };
        data.clone()
    }

    fn object_instantiation_snapshot(store: &TestStore, id: TypeId) -> TypeCacheState {
        let object = match store.type_payload(id).unwrap().data() {
            TypeData::Object(data) => data,
            TypeData::TypeReference(data) => &data.object,
            TypeData::Interface(data) => &data.reference.object,
            TypeData::Tuple(data) => &data.interface.reference.object,
            TypeData::InstantiationExpression(data) => &data.object,
            TypeData::Mapped(data) => &data.object,
            TypeData::ReverseMapped(data) => &data.object,
            TypeData::EvolvingArray(data) => &data.object,
            _ => panic!("expected object type"),
        };
        object.instantiations.clone()
    }

    struct SeededStore {
        store: TestStore,
        conditional_node: NodeRef,
        instantiation_node: NodeRef,
        mapped_node: NodeRef,
        reference_node: NodeRef,
        tuple_label_node: NodeRef,
        base: TypeId,
        symbol: SemanticSymbolId,
        mapper: TypeMapperId,
        alias: TypeAliasId,
        root: ConditionalRootId,
        signature: SignatureId,
        index_info: IndexInfoId,
    }

    fn seeded_store(payload: &'static str) -> SeededStore {
        let parsed = parse_source_file(
            "type Result<T> = T extends string ? T : never;\n\
             type Mapping<T> = { [K in keyof T]: T[K] };\n\
             type Reference = Array<string>;\n\
             type Tuple = [label: string];\n\
             declare function f<T>(parameter: T): void;\n\
             const instantiated = f<string>;",
        );
        let scope = AstScope::new(FileId::new(0), &parsed.arena);
        let node_of_kind = |kind| {
            let (node, _) = parsed
                .arena
                .iter()
                .find(|(_, node)| node.kind == kind)
                .unwrap_or_else(|| panic!("fixture is missing {kind:?}"));
            scope.node_ref(node).unwrap()
        };
        let conditional_node = node_of_kind(SyntaxKind::ConditionalType);
        let instantiation_node = node_of_kind(SyntaxKind::ExpressionWithTypeArguments);
        let mapped_node = node_of_kind(SyntaxKind::MappedType);
        let reference_node = node_of_kind(SyntaxKind::TypeReference);
        let tuple_label_node = node_of_kind(SyntaxKind::NamedTupleMember);
        let declaration_node = node_of_kind(SyntaxKind::Parameter);
        let mut store = TestStore::new();
        assert!(store.register_ast_scope(scope));
        let base = store
            .alloc_intrinsic_type(TypeFlags::STRING, "string")
            .unwrap();
        let symbol = alloc_test_symbol(&mut store, payload);
        let mapper = store.alloc_mapper(payload);
        let alias = store.alloc_type_alias(Some(symbol)).unwrap();
        let root = store
            .alloc_conditional_root(conditional_node, base, base, true, None, None, Some(alias))
            .unwrap();
        let signature = store
            .alloc_signature(
                SignatureFlags::NONE,
                Some(declaration_node),
                vec![base],
                Some(symbol),
                vec![symbol],
                Some(base),
                None,
                1,
            )
            .unwrap();
        let index_info = store
            .alloc_index_info(
                base,
                base,
                false,
                Some(declaration_node),
                vec![declaration_node],
            )
            .unwrap();
        SeededStore {
            store,
            conditional_node,
            instantiation_node,
            mapped_node,
            reference_node,
            tuple_label_node,
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
            .create_tuple_element_info(ElementFlags::REQUIRED, Some(seeded.tuple_label_node))
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
            store.alloc_unique_es_symbol_type(seeded.symbol).unwrap(),
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
                    Some(seeded.instantiation_node),
                )
                .unwrap(),
            store
                .alloc_mapped_type(
                    ObjectFlags::NONE,
                    Some(seeded.symbol),
                    Some(seeded.mapped_node),
                )
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
            .alloc_intrinsic_type_ex(TypeFlags::UNKNOWN, "unknown", reset)
            .unwrap();
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
        let table = alloc_test_table(&mut seeded.store, &[("p", seeded.symbol)]);
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
    fn one_sided_structured_signatures_reuse_input_allocations_and_order() {
        let mut seeded = seeded_store("local");
        let second = seeded
            .store
            .alloc_signature(
                SignatureFlags::CONSTRUCT,
                None,
                Vec::new(),
                None,
                Vec::new(),
                Some(seeded.base),
                None,
                0,
            )
            .unwrap();

        let call_object = seeded
            .store
            .alloc_plain_object_type(ObjectFlags::ANONYMOUS, Some(seeded.symbol))
            .unwrap();
        let mut calls = Vec::with_capacity(4);
        calls.extend([seeded.signature, second]);
        let calls_pointer = calls.as_ptr();
        let calls_capacity = calls.capacity();
        assert!(seeded.store.set_structured_type_members(
            call_object,
            None,
            None,
            Some(calls),
            None,
            None,
        ));
        let TypeData::Object(call_data) = seeded.store.type_payload(call_object).unwrap().data()
        else {
            panic!("expected object")
        };
        let stored_calls = call_data.structured.signatures.as_ref().unwrap();
        assert_eq!(stored_calls.as_slice(), &[seeded.signature, second]);
        assert_eq!(stored_calls.as_ptr(), calls_pointer);
        assert_eq!(stored_calls.capacity(), calls_capacity);
        assert_eq!(call_data.structured.call_signature_count, 2);

        let construct_object = seeded
            .store
            .alloc_plain_object_type(ObjectFlags::ANONYMOUS, Some(seeded.symbol))
            .unwrap();
        let mut constructs = Vec::with_capacity(4);
        constructs.extend([second, seeded.signature]);
        let constructs_pointer = constructs.as_ptr();
        let constructs_capacity = constructs.capacity();
        assert!(seeded.store.set_structured_type_members(
            construct_object,
            None,
            None,
            None,
            Some(constructs),
            None,
        ));
        let TypeData::Object(construct_data) =
            seeded.store.type_payload(construct_object).unwrap().data()
        else {
            panic!("expected object")
        };
        let stored_constructs = construct_data.structured.signatures.as_ref().unwrap();
        assert_eq!(stored_constructs.as_slice(), &[second, seeded.signature]);
        assert_eq!(stored_constructs.as_ptr(), constructs_pointer);
        assert_eq!(stored_constructs.capacity(), constructs_capacity);
        assert_eq!(construct_data.structured.call_signature_count, 0);
    }

    #[test]
    fn no_base_interface_publication_is_atomic_and_invalidates_only_cold_members() {
        let mut seeded = seeded_store("local");
        let interface = seeded
            .store
            .alloc_interface_type(ObjectFlags::INTERFACE, Some(seeded.symbol))
            .unwrap();
        assert!(
            seeded
                .store
                .set_structured_type_members(interface, None, None, None, None, None,)
        );
        assert!(
            seeded
                .store
                .type_payload(interface)
                .unwrap()
                .object_flags()
                .contains(ObjectFlags::MEMBERS_RESOLVED)
        );

        assert!(seeded.store.publish_interface_no_base_resolution(interface));
        let (resolved, flags) = interface_snapshot(&seeded.store, interface);
        assert!(resolved.base_types_resolved);
        assert!(resolved.resolved_base_constructor_type.is_none());
        assert!(resolved.resolved_base_types.is_none());
        assert!(!flags.contains(ObjectFlags::MEMBERS_RESOLVED));

        assert!(
            seeded
                .store
                .set_structured_type_members(interface, None, None, None, None, None,)
        );
        assert!(!seeded.store.publish_interface_no_base_resolution(interface));
        assert!(
            seeded
                .store
                .type_payload(interface)
                .unwrap()
                .object_flags()
                .contains(ObjectFlags::MEMBERS_RESOLVED)
        );

        let class = seeded
            .store
            .alloc_interface_type(ObjectFlags::CLASS, Some(seeded.symbol))
            .unwrap();
        let before = interface_snapshot(&seeded.store, class);
        assert!(!seeded.store.publish_interface_no_base_resolution(class));
        assert_eq!(interface_snapshot(&seeded.store, class), before);

        let allocated_empty_bases = seeded
            .store
            .alloc_interface_type(ObjectFlags::INTERFACE, Some(seeded.symbol))
            .unwrap();
        assert!(seeded.store.set_interface_base_resolution(
            allocated_empty_bases,
            true,
            None,
            Some(Vec::new()),
        ));
        let before = interface_snapshot(&seeded.store, allocated_empty_bases);
        assert!(
            before
                .0
                .resolved_base_types
                .as_ref()
                .is_some_and(Vec::is_empty)
        );
        assert!(
            !seeded
                .store
                .publish_interface_no_base_resolution(allocated_empty_bases)
        );
        assert_eq!(
            interface_snapshot(&seeded.store, allocated_empty_bases),
            before
        );
    }

    #[test]
    fn derived_unique_and_union_cache_names_remain_byte_exact() {
        let mut seeded = seeded_store("local");
        let unique = seeded
            .store
            .alloc_unique_es_symbol_type(seeded.symbol)
            .unwrap();
        let TypeData::UniqueEsSymbol(unique_data) =
            seeded.store.type_payload(unique).unwrap().data()
        else {
            panic!("expected unique symbol type")
        };
        let unique_name = unique_data.name.clone();
        assert_eq!(
            seeded.store.type_payload(unique).unwrap().symbol(),
            Some(seeded.symbol)
        );
        let global_id = seeded.store.global_symbol_id(seeded.symbol).unwrap();
        let mut expected_unique_name = b"\xFE@local@".to_vec();
        expected_unique_name.extend_from_slice(global_id.to_string().as_bytes());
        assert_eq!(unique_name.as_bytes(), expected_unique_name);
        assert_eq!(unique_name.as_utf8(), None);

        let object = seeded
            .store
            .alloc_plain_object_type(ObjectFlags::ANONYMOUS, Some(seeded.symbol))
            .unwrap();
        let union = seeded
            .store
            .alloc_union_type(ObjectFlags::NONE, vec![seeded.base, object])
            .unwrap();
        let key = EscapedName::source("kind");
        assert!(seeded.store.set_union_caches(
            union,
            None,
            None,
            None,
            key.clone(),
            ConstituentMapState::Allocated(HashMap::from([(seeded.base, object)])),
        ));
        let TypeData::Union(union_data) = seeded.store.type_payload(union).unwrap().data() else {
            panic!("expected union")
        };
        assert_eq!(union_data.key_property_name, key);
        assert_eq!(union_data.key_property_name.as_bytes(), b"kind");

        let missing_union = seeded
            .store
            .alloc_union_type(ObjectFlags::NONE, vec![seeded.base, object])
            .unwrap();
        let missing = EscapedName::internal(InternalSymbolName::Missing);
        assert!(seeded.store.set_union_caches(
            missing_union,
            None,
            None,
            None,
            missing.clone(),
            ConstituentMapState::Unallocated,
        ));
        let TypeData::Union(missing_data) =
            seeded.store.type_payload(missing_union).unwrap().data()
        else {
            panic!("expected union")
        };
        assert_eq!(missing_data.key_property_name, missing);
        assert_eq!(missing_data.key_property_name.as_bytes(), b"\xFEmissing");
    }

    #[test]
    fn unique_symbol_identity_is_derived_foreign_safe_and_immutable() {
        let mut first = seeded_store("first");
        let mut second = seeded_store("second");
        let second_type_count = second.store.type_len();
        assert_eq!(second.store.alloc_unique_es_symbol_type(first.symbol), None);
        assert_eq!(second.store.type_len(), second_type_count);

        let unique = first
            .store
            .alloc_unique_es_symbol_type(first.symbol)
            .unwrap();
        let replacement = alloc_test_symbol(&mut first.store, "replacement");
        let TypeData::UniqueEsSymbol(data) = first.store.type_payload(unique).unwrap().data()
        else {
            panic!("expected unique symbol type")
        };
        let original_name = data.name.clone();
        assert!(!first.store.set_type_symbol(unique, None));
        assert!(!first.store.set_type_symbol(unique, Some(first.symbol)));
        assert!(!first.store.set_type_symbol(unique, Some(replacement)));

        let record = first.store.type_payload(unique).unwrap();
        let TypeData::UniqueEsSymbol(data) = record.data() else {
            panic!("expected unique symbol type")
        };
        assert_eq!(record.symbol(), Some(first.symbol));
        assert_eq!(data.name, original_name);
    }

    #[test]
    fn union_discriminant_cache_states_are_validated_atomically() {
        let foreign = seeded_store("foreign");
        let mut seeded = seeded_store("local");
        let object = seeded
            .store
            .alloc_plain_object_type(ObjectFlags::ANONYMOUS, Some(seeded.symbol))
            .unwrap();
        let union = seeded
            .store
            .alloc_union_type(ObjectFlags::NONE, vec![seeded.base, object])
            .unwrap();
        let initial = union_snapshot(&seeded.store, union);
        let local_map = || ConstituentMapState::Allocated(HashMap::from([(seeded.base, object)]));

        assert!(!seeded.store.set_union_caches(
            union,
            Some(object),
            Some(seeded.base),
            Some(object),
            EscapedName::source(""),
            local_map(),
        ));
        assert!(!seeded.store.set_union_caches(
            union,
            Some(object),
            Some(seeded.base),
            Some(object),
            EscapedName::source("kind"),
            ConstituentMapState::Unallocated,
        ));
        assert!(!seeded.store.set_union_caches(
            union,
            Some(object),
            Some(seeded.base),
            Some(object),
            EscapedName::internal(InternalSymbolName::Missing),
            local_map(),
        ));
        assert!(!seeded.store.set_union_caches(
            union,
            Some(object),
            Some(seeded.base),
            Some(object),
            EscapedName::internal(InternalSymbolName::Call),
            ConstituentMapState::Unallocated,
        ));
        assert!(!seeded.store.set_union_caches(
            union,
            Some(object),
            Some(seeded.base),
            Some(object),
            EscapedName::internal(InternalSymbolName::Call),
            local_map(),
        ));
        assert!(!seeded.store.set_union_caches(
            union,
            Some(object),
            Some(seeded.base),
            Some(object),
            EscapedName::source("kind"),
            ConstituentMapState::Allocated(HashMap::from([(foreign.base, object)])),
        ));
        assert_eq!(union_snapshot(&seeded.store, union), initial);

        assert!(seeded.store.set_union_caches(
            union,
            Some(object),
            Some(seeded.base),
            Some(object),
            EscapedName::source("kind"),
            local_map(),
        ));
        let valid = union_snapshot(&seeded.store, union);
        assert!(!seeded.store.set_union_caches(
            union,
            None,
            None,
            None,
            EscapedName::internal(InternalSymbolName::Call),
            ConstituentMapState::Unallocated,
        ));
        assert_eq!(union_snapshot(&seeded.store, union), valid);
    }

    #[test]
    fn literal_values_preserve_all_upstream_alternatives() {
        let mut store = TestStore::new();
        let cases = [
            (TypeFlags::STRING_LITERAL, LiteralValue::String("s".into())),
            (
                TypeFlags::NUMBER_LITERAL,
                LiteralValue::Number(Number::new(-0.0)),
            ),
            (TypeFlags::BOOLEAN_LITERAL, LiteralValue::Boolean(false)),
            (
                TypeFlags::BIG_INT_LITERAL,
                LiteralValue::BigInt(PseudoBigInt::parse_valid("0x10n")),
            ),
            (TypeFlags::ENUM, LiteralValue::ComputedEnum),
        ];
        let ids = cases.map(|(flags, value)| {
            store
                .alloc_literal_type(flags, value, RegularLiteralLink::SelfType)
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
        let outer_type_parameter = seeded.store.alloc_type_parameter(None).unwrap();
        let this_type = seeded.store.alloc_type_parameter(None).unwrap();
        let self_instantiation_key = CacheHashKey::new(1);
        assert!(!seeded.store.initialize_interface_type_parameters(
            interface,
            vec![this_type, outer_type_parameter],
            1,
            this_type,
            self_instantiation_key,
        ));
        assert!(seeded.store.initialize_interface_type_parameters(
            interface,
            vec![outer_type_parameter, this_type],
            1,
            this_type,
            self_instantiation_key,
        ));
        assert!(
            seeded
                .store
                .type_payload(interface)
                .unwrap()
                .object_flags()
                .contains(ObjectFlags::REFERENCE)
        );

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
            TypeCacheState::Allocated(HashMap::from([(
                CacheHashKey::from_halves(1, 2),
                conditional,
            )])),
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
            &TypeCacheState::Allocated(HashMap::from([(
                CacheHashKey::from_halves(1, 2),
                conditional,
            )]))
        );
    }

    #[test]
    fn foreign_handles_are_rejected_per_slot_before_mutation() {
        let mut first = seeded_store("first");
        let mut second = seeded_store("second");
        assert_eq!(first.base.get(), second.base.get());
        assert_eq!(first.symbol.get(), second.symbol.get());
        assert_eq!(first.mapper.get(), second.mapper.get());
        assert_eq!(first.alias.get(), second.alias.get());
        assert_eq!(first.root.get(), second.root.get());
        assert_eq!(second.store.type_alias(first.alias), None);
        assert_eq!(second.store.conditional_root(first.root), None);

        let first_literal = first
            .store
            .alloc_literal_type(
                TypeFlags::STRING_LITERAL,
                LiteralValue::String("x".into()),
                RegularLiteralLink::SelfType,
            )
            .unwrap();
        let second_literal = second
            .store
            .alloc_literal_type(
                TypeFlags::STRING_LITERAL,
                LiteralValue::String("x".into()),
                RegularLiteralLink::SelfType,
            )
            .unwrap();
        assert_eq!(first_literal.get(), second_literal.get());

        let type_count = second.store.type_len();
        assert_eq!(
            second.store.alloc_literal_type(
                TypeFlags::STRING_LITERAL,
                LiteralValue::String("x".into()),
                RegularLiteralLink::Type(first_literal),
            ),
            None
        );
        assert!(!second.store.set_literal_links(
            second_literal,
            Some(first_literal),
            second_literal
        ));
        let TypeData::Literal(second_literal_data) =
            second.store.type_payload(second_literal).unwrap().data()
        else {
            panic!("expected literal")
        };
        assert_eq!(second_literal_data.fresh_type, None);
        assert_eq!(second_literal_data.regular_type, second_literal);
        assert_eq!(second.store.alloc_unique_es_symbol_type(first.symbol), None);
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
            TypeCacheState::Allocated(HashMap::from([(CacheHashKey::new(1), first.base)])),
        ));
        let foreign_table = alloc_test_table(&mut first.store, &[("x", first.symbol)]);
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
    fn nested_tables_and_hash_maps_reject_foreign_keys_and_values_without_mutation() {
        let first = seeded_store("first");
        let mut seeded = seeded_store("second");
        let duplicate_table = seeded.store.alloc_symbol_table();
        assert_eq!(
            seeded
                .store
                .insert_symbol(duplicate_table, EscapedName::source("same"), seeded.symbol,),
            Some(None)
        );
        assert_eq!(
            seeded
                .store
                .insert_symbol(duplicate_table, EscapedName::source("same"), seeded.symbol,),
            Some(Some(seeded.symbol))
        );
        let object = seeded
            .store
            .alloc_plain_object_type(ObjectFlags::ANONYMOUS, Some(seeded.symbol))
            .unwrap();
        assert!(!seeded.store.set_object_instantiations(
            object,
            TypeCacheState::Allocated(HashMap::from([(CacheHashKey::new(7), first.base)])),
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
            EscapedName::source("key"),
            ConstituentMapState::Allocated(HashMap::from([(first.base, object)])),
        ));
        assert!(!seeded.store.set_union_caches(
            union,
            None,
            None,
            None,
            EscapedName::source("key"),
            ConstituentMapState::Allocated(HashMap::from([(seeded.base, first.base)])),
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
    fn allocated_empty_states_and_hash_map_lookup_remain_observable() {
        assert_eq!(std::mem::size_of::<CacheHashKey>(), 16);
        let mut seeded = seeded_store("local");
        let second_symbol = alloc_test_symbol(&mut seeded.store, "second");
        let table = alloc_test_table(
            &mut seeded.store,
            &[("z", seeded.symbol), ("a", second_symbol)],
        );
        let table_record = seeded.store.symbol_table(table).unwrap();
        assert_eq!(table_record.len(), 2);
        assert_eq!(table_record.get_source("z"), Some(seeded.symbol));
        assert_eq!(table_record.get_source("a"), Some(second_symbol));
        let empty_table = seeded.store.alloc_symbol_table();
        assert!(seeded.store.symbol_table(empty_table).unwrap().is_empty());

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
                .set_object_instantiations(object, TypeCacheState::Allocated(HashMap::new()),)
        );
        let TypeData::Object(object_data) = seeded.store.type_payload(object).unwrap().data()
        else {
            panic!("expected object")
        };
        assert_eq!(
            object_data.instantiations,
            TypeCacheState::Allocated(HashMap::new())
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
            TypeCacheState::Allocated(HashMap::from([
                (second_key, union),
                (first_key, seeded.base),
            ])),
        ));
        assert!(seeded.store.set_union_caches(
            union,
            None,
            None,
            None,
            EscapedName::source("kind"),
            ConstituentMapState::Allocated(HashMap::from(
                [(object, union), (seeded.base, object),]
            )),
        ));
        let TypeData::Object(object_data) = seeded.store.type_payload(object).unwrap().data()
        else {
            panic!("expected object")
        };
        let TypeCacheState::Allocated(instantiations) = &object_data.instantiations else {
            panic!("expected allocated instantiations")
        };
        assert_eq!(instantiations.get(&second_key), Some(&union));
        assert_eq!(instantiations.get(&first_key), Some(&seeded.base));
        let TypeData::Union(union_data) = seeded.store.type_payload(union).unwrap().data() else {
            panic!("expected union")
        };
        let ConstituentMapState::Allocated(constituents) = &union_data.constituent_map else {
            panic!("expected allocated constituents")
        };
        assert_eq!(constituents.get(&object), Some(&union));
        assert_eq!(constituents.get(&seeded.base), Some(&object));
    }

    #[test]
    fn auxiliary_records_and_node_slots_reject_foreign_provenance() {
        let first = seeded_store("first");
        let mut second = seeded_store("second");
        let local_table = second.store.alloc_symbol_table();
        assert_eq!(
            second
                .store
                .insert_symbol(local_table, EscapedName::source("x"), first.symbol,),
            None
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
                first.conditional_node,
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
                second.conditional_node,
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
                second.conditional_node,
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
                second.conditional_node,
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
                second.conditional_node,
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
                second.conditional_node,
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
            Some(first.reference_node),
            Some(vec![second.base]),
        ));
        assert!(!second.store.set_type_reference_resolution(
            reference,
            Some(second.reference_node),
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
                .set_instantiation_expression_node(expression, Some(first.instantiation_node))
        );
        let TypeData::InstantiationExpression(expression_data) =
            second.store.type_payload(expression).unwrap().data()
        else {
            panic!("expected instantiation expression")
        };
        assert_eq!(expression_data.node, None);

        let foreign_element = first
            .store
            .create_tuple_element_info(ElementFlags::REQUIRED, Some(first.tuple_label_node))
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
    fn type_and_object_flag_transitions_preserve_payload_dispatch() {
        let mut seeded = seeded_store("local");
        let source = seeded
            .store
            .alloc_plain_object_type(ObjectFlags::ANONYMOUS, Some(seeded.symbol))
            .unwrap();
        let regular = seeded
            .store
            .alloc_plain_object_type(ObjectFlags::ANONYMOUS, Some(seeded.symbol))
            .unwrap();
        assert!(seeded.store.add_type_object_flags(
            source,
            ObjectFlags::OBJECT_LITERAL
                | ObjectFlags::FRESH_LITERAL
                | ObjectFlags::CONTAINS_OBJECT_OR_ARRAY_LITERAL,
        ));
        assert!(
            seeded
                .store
                .copy_type_object_flags(regular, source, ObjectFlags::FRESH_LITERAL,)
        );
        let regular_flags = seeded.store.type_payload(regular).unwrap().object_flags();
        assert!(regular_flags.contains(ObjectFlags::ANONYMOUS | ObjectFlags::OBJECT_LITERAL));
        assert!(!regular_flags.contains(ObjectFlags::FRESH_LITERAL));
        assert!(seeded.store.copy_type_flags(regular, source));
        assert_eq!(
            seeded.store.type_payload(regular).unwrap().flags(),
            TypeFlags::OBJECT
        );

        let before = seeded.store.type_payload(regular).unwrap().object_flags();
        assert!(
            !seeded
                .store
                .set_type_object_flags(regular, ObjectFlags::ANONYMOUS | ObjectFlags::MAPPED,)
        );
        assert!(
            !seeded
                .store
                .set_type_object_flags(regular, ObjectFlags::MAPPED)
        );
        assert_eq!(
            seeded.store.type_payload(regular).unwrap().object_flags(),
            before
        );

        let false_type = seeded
            .store
            .alloc_literal_type(
                TypeFlags::BOOLEAN_LITERAL,
                LiteralValue::Boolean(false),
                RegularLiteralLink::SelfType,
            )
            .unwrap();
        let true_type = seeded
            .store
            .alloc_literal_type(
                TypeFlags::BOOLEAN_LITERAL,
                LiteralValue::Boolean(true),
                RegularLiteralLink::SelfType,
            )
            .unwrap();
        let boolean_union = seeded
            .store
            .alloc_union_type(ObjectFlags::NONE, vec![false_type, true_type])
            .unwrap();
        assert!(
            seeded
                .store
                .add_type_flags(boolean_union, TypeFlags::BOOLEAN)
        );
        assert_eq!(
            seeded.store.type_payload(boolean_union).unwrap().flags(),
            TypeFlags::UNION | TypeFlags::BOOLEAN
        );

        let enum_a = seeded
            .store
            .alloc_literal_type(
                TypeFlags::STRING_LITERAL | TypeFlags::ENUM_LITERAL,
                LiteralValue::String("a".into()),
                RegularLiteralLink::SelfType,
            )
            .unwrap();
        let enum_b = seeded
            .store
            .alloc_literal_type(
                TypeFlags::STRING_LITERAL | TypeFlags::ENUM_LITERAL,
                LiteralValue::String("b".into()),
                RegularLiteralLink::SelfType,
            )
            .unwrap();
        let enum_union = seeded
            .store
            .alloc_union_type(ObjectFlags::NONE, vec![enum_a, enum_b])
            .unwrap();
        assert!(
            seeded
                .store
                .add_type_flags(enum_union, TypeFlags::ENUM_LITERAL)
        );
        assert_eq!(
            seeded.store.type_payload(enum_union).unwrap().flags(),
            TypeFlags::UNION | TypeFlags::ENUM_LITERAL
        );

        assert!(
            !seeded
                .store
                .add_type_flags(boolean_union, TypeFlags::STRING_LITERAL)
        );
        assert!(!seeded.store.add_type_flags(enum_union, TypeFlags::BOOLEAN));
        assert!(!seeded.store.copy_type_flags(regular, boolean_union));
        assert_eq!(
            seeded.store.type_payload(boolean_union).unwrap().flags(),
            TypeFlags::UNION | TypeFlags::BOOLEAN
        );
        assert_eq!(
            seeded.store.type_payload(enum_union).unwrap().flags(),
            TypeFlags::UNION | TypeFlags::ENUM_LITERAL
        );
        assert_eq!(
            seeded.store.type_payload(regular).unwrap().flags(),
            TypeFlags::OBJECT
        );
    }

    #[test]
    fn literal_flags_and_links_require_exact_kind_and_value() {
        let mut store = TestStore::new();
        let invalid = [
            (
                TypeFlags::NUMBER_LITERAL,
                LiteralValue::String("value".into()),
            ),
            (
                TypeFlags::ENUM_LITERAL,
                LiteralValue::String("value".into()),
            ),
            (
                TypeFlags::STRING_LITERAL,
                LiteralValue::Number(Number::new(1.0)),
            ),
            (
                TypeFlags::BIG_INT_LITERAL | TypeFlags::ENUM_LITERAL,
                LiteralValue::BigInt(PseudoBigInt::parse_valid("1n")),
            ),
            (TypeFlags::BOOLEAN, LiteralValue::Boolean(true)),
            (TypeFlags::ENUM_LITERAL, LiteralValue::ComputedEnum),
        ];
        let count = store.type_len();
        for (flags, value) in invalid {
            assert_eq!(
                store.alloc_literal_type(flags, value, RegularLiteralLink::SelfType),
                None
            );
        }
        assert_eq!(store.type_len(), count);

        let regular = store
            .alloc_literal_type(
                TypeFlags::STRING_LITERAL,
                LiteralValue::String("same".into()),
                RegularLiteralLink::SelfType,
            )
            .unwrap();
        let different_value = store
            .alloc_literal_type(
                TypeFlags::STRING_LITERAL,
                LiteralValue::String("different".into()),
                RegularLiteralLink::SelfType,
            )
            .unwrap();
        let different_flags = store
            .alloc_literal_type(
                TypeFlags::STRING_LITERAL | TypeFlags::ENUM_LITERAL,
                LiteralValue::String("same".into()),
                RegularLiteralLink::SelfType,
            )
            .unwrap();
        let number = store
            .alloc_literal_type(
                TypeFlags::NUMBER_LITERAL,
                LiteralValue::Number(Number::new(1.0)),
                RegularLiteralLink::SelfType,
            )
            .unwrap();
        let count = store.type_len();
        assert_eq!(
            store.alloc_literal_type(
                TypeFlags::STRING_LITERAL,
                LiteralValue::String("same".into()),
                RegularLiteralLink::Type(different_value),
            ),
            None
        );
        assert_eq!(store.type_len(), count);
        assert!(!store.set_literal_links(regular, Some(different_value), regular));
        assert!(!store.set_literal_links(regular, Some(different_flags), regular));
        assert!(!store.set_literal_links(regular, Some(number), regular));
        let TypeData::Literal(data) = store.type_payload(regular).unwrap().data() else {
            panic!("expected literal")
        };
        assert_eq!(data.fresh_type, None);
        assert_eq!(data.regular_type, regular);

        let regular_nan = store
            .alloc_literal_type(
                TypeFlags::NUMBER_LITERAL,
                LiteralValue::Number(Number::nan()),
                RegularLiteralLink::SelfType,
            )
            .unwrap();
        let fresh_nan = store
            .alloc_literal_type(
                TypeFlags::NUMBER_LITERAL,
                LiteralValue::Number(Number::nan()),
                RegularLiteralLink::Type(regular_nan),
            )
            .unwrap();
        assert!(store.set_literal_links(regular_nan, Some(fresh_nan), regular_nan));
    }

    #[test]
    #[allow(clippy::too_many_lines)] // One atomic interface/tuple transition matrix.
    fn interface_reference_initialization_is_exact_and_atomic() {
        let mut seeded = seeded_store("local");
        let count = seeded.store.type_len();
        assert_eq!(
            seeded.store.alloc_interface_type(
                ObjectFlags::CLASS | ObjectFlags::INTERFACE,
                Some(seeded.symbol),
            ),
            None
        );
        assert_eq!(seeded.store.type_len(), count);

        let interface = seeded
            .store
            .alloc_interface_type(ObjectFlags::CLASS, Some(seeded.symbol))
            .unwrap();
        let ordinary = seeded.store.alloc_type_parameter(None).unwrap();
        let candidate_this = seeded.store.alloc_type_parameter(None).unwrap();
        let constrained_candidate = seeded.store.alloc_type_parameter(None).unwrap();
        assert!(seeded.store.set_type_parameter_resolution(
            constrained_candidate,
            Some(seeded.base),
            None,
            None,
            None,
        ));
        let mut foreign = seeded_store("foreign");
        let foreign_this = foreign.store.alloc_type_parameter(None).unwrap();
        let owner_before = interface_snapshot(&seeded.store, interface);
        let candidate_before = type_parameter_snapshot(&seeded.store, candidate_this);
        let self_instantiation_key = CacheHashKey::new(41);

        assert!(
            !seeded
                .store
                .set_object_target_and_mapper(interface, Some(interface), None,)
        );
        assert!(
            !seeded
                .store
                .set_type_reference_resolution(interface, None, Some(vec![ordinary]),)
        );
        assert!(!seeded.store.set_object_instantiations(
            interface,
            TypeCacheState::Allocated(HashMap::from([(self_instantiation_key, interface)])),
        ));

        assert!(!seeded.store.initialize_interface_type_parameters(
            interface,
            Vec::new(),
            0,
            candidate_this,
            self_instantiation_key,
        ));
        assert!(!seeded.store.initialize_interface_type_parameters(
            interface,
            vec![ordinary, candidate_this],
            2,
            candidate_this,
            self_instantiation_key,
        ));
        assert!(!seeded.store.initialize_interface_type_parameters(
            interface,
            vec![candidate_this, ordinary],
            1,
            candidate_this,
            self_instantiation_key,
        ));
        assert!(!seeded.store.initialize_interface_type_parameters(
            interface,
            vec![ordinary, candidate_this, candidate_this],
            1,
            candidate_this,
            self_instantiation_key,
        ));
        assert!(!seeded.store.initialize_interface_type_parameters(
            interface,
            vec![ordinary, constrained_candidate],
            1,
            constrained_candidate,
            self_instantiation_key,
        ));
        assert!(!seeded.store.initialize_interface_type_parameters(
            interface,
            vec![seeded.base, candidate_this],
            1,
            candidate_this,
            self_instantiation_key,
        ));
        assert!(!seeded.store.initialize_interface_type_parameters(
            interface,
            vec![ordinary, foreign_this],
            1,
            foreign_this,
            self_instantiation_key,
        ));
        assert!(
            !seeded
                .store
                .set_type_object_flags(interface, ObjectFlags::CLASS | ObjectFlags::REFERENCE,)
        );
        assert_eq!(interface_snapshot(&seeded.store, interface), owner_before);
        assert_eq!(
            type_parameter_snapshot(&seeded.store, candidate_this),
            candidate_before
        );

        let this_type = seeded.store.alloc_type_parameter(None).unwrap();
        assert!(seeded.store.initialize_interface_type_parameters(
            interface,
            vec![ordinary, this_type],
            1,
            this_type,
            self_instantiation_key,
        ));
        assert_eq!(
            seeded.store.type_payload(interface).unwrap().object_flags(),
            ObjectFlags::CLASS | ObjectFlags::REFERENCE
        );
        let initialized_owner = interface_snapshot(&seeded.store, interface);
        let initialized_this = type_parameter_snapshot(&seeded.store, this_type);
        assert!(initialized_this.is_this_type);
        assert_eq!(initialized_this.constraint, Some(interface));
        assert_eq!(initialized_owner.0.reference.object.target, Some(interface));
        assert_eq!(initialized_owner.0.reference.object.mapper, None);
        assert_eq!(initialized_owner.0.reference.node, None);
        assert_eq!(
            initialized_owner
                .0
                .reference
                .resolved_type_arguments
                .as_deref(),
            Some([ordinary].as_slice())
        );
        let TypeCacheState::Allocated(interface_instantiations) =
            &initialized_owner.0.reference.object.instantiations
        else {
            panic!("expected initialized interface instantiations")
        };
        assert_eq!(interface_instantiations.len(), 1);
        assert_eq!(
            interface_instantiations.get(&self_instantiation_key),
            Some(&interface)
        );
        assert!(!seeded.store.initialize_interface_type_parameters(
            interface,
            vec![ordinary, this_type],
            1,
            this_type,
            self_instantiation_key,
        ));
        assert!(
            !seeded
                .store
                .set_type_parameter_resolution(this_type, None, None, None, None,)
        );
        assert!(!seeded.store.set_type_parameter_resolution(
            this_type,
            Some(seeded.base),
            None,
            None,
            None,
        ));
        assert!(!seeded.store.set_object_target_and_mapper(
            interface,
            Some(seeded.base),
            Some(seeded.mapper),
        ));
        assert!(!seeded.store.set_type_reference_resolution(
            interface,
            Some(seeded.reference_node),
            Some(vec![seeded.base]),
        ));
        assert!(!seeded.store.set_object_instantiations(
            interface,
            TypeCacheState::Allocated(HashMap::from([(CacheHashKey::new(99), seeded.base)])),
        ));
        assert_eq!(
            interface_snapshot(&seeded.store, interface),
            initialized_owner
        );
        assert_eq!(
            type_parameter_snapshot(&seeded.store, this_type),
            initialized_this
        );

        assert!(seeded.store.set_type_parameter_resolution(
            this_type,
            Some(interface),
            Some(ordinary),
            Some(seeded.mapper),
            Some(seeded.base),
        ));
        let resolved_this = type_parameter_snapshot(&seeded.store, this_type);
        assert!(resolved_this.is_this_type);
        assert_eq!(resolved_this.constraint, Some(interface));

        assert!(seeded.store.add_type_object_flags(
            interface,
            ObjectFlags::CONTAINS_WIDENING_TYPE
                | ObjectFlags::COULD_CONTAIN_TYPE_VARIABLES_COMPUTED
                | ObjectFlags::COULD_CONTAIN_TYPE_VARIABLES,
        ));
        assert!(
            !seeded
                .store
                .set_type_object_flags(interface, ObjectFlags::CLASS)
        );
        assert!(
            !seeded
                .store
                .set_type_object_flags(interface, ObjectFlags::INTERFACE | ObjectFlags::REFERENCE)
        );
        let TypeData::Interface(data) = seeded.store.type_payload(interface).unwrap().data() else {
            panic!("expected interface")
        };
        assert_eq!(data.all_type_parameters, Some(vec![ordinary, this_type]));
        assert_eq!(data.outer_type_parameter_count, 1);
        assert_eq!(data.this_type, Some(this_type));
        assert!(
            seeded
                .store
                .type_payload(interface)
                .unwrap()
                .object_flags()
                .contains(
                    ObjectFlags::CLASS
                        | ObjectFlags::REFERENCE
                        | ObjectFlags::CONTAINS_WIDENING_TYPE
                        | ObjectFlags::COULD_CONTAIN_TYPE_VARIABLES_COMPUTED
                        | ObjectFlags::COULD_CONTAIN_TYPE_VARIABLES,
                )
        );

        let element = seeded
            .store
            .create_tuple_element_info(ElementFlags::REQUIRED, Some(seeded.tuple_label_node))
            .unwrap();
        let metadata = seeded
            .store
            .create_tuple_metadata(vec![element], false)
            .unwrap();
        let tuple = seeded
            .store
            .alloc_tuple_type(ObjectFlags::NONE, None, metadata)
            .unwrap();
        let tuple_parameter = seeded.store.alloc_type_parameter(None).unwrap();
        let tuple_this = seeded.store.alloc_type_parameter(None).unwrap();
        let tuple_this_before = type_parameter_snapshot(&seeded.store, tuple_this);
        let tuple_self_instantiation_key = CacheHashKey::new(42);
        assert!(!seeded.store.initialize_interface_type_parameters(
            tuple,
            vec![tuple_parameter, tuple_this],
            1,
            tuple_this,
            tuple_self_instantiation_key,
        ));
        assert_eq!(
            type_parameter_snapshot(&seeded.store, tuple_this),
            tuple_this_before
        );
        assert!(seeded.store.initialize_interface_type_parameters(
            tuple,
            vec![tuple_parameter, tuple_this],
            0,
            tuple_this,
            tuple_self_instantiation_key,
        ));
        let tuple_record = seeded.store.type_payload(tuple).unwrap();
        let TypeData::Tuple(tuple_data) = tuple_record.data() else {
            panic!("expected tuple")
        };
        assert_eq!(
            tuple_data.interface.all_type_parameters,
            Some(vec![tuple_parameter, tuple_this])
        );
        assert_eq!(tuple_data.interface.outer_type_parameter_count, 0);
        assert_eq!(tuple_data.interface.this_type, Some(tuple_this));
        assert_eq!(tuple_data.interface.reference.object.target, Some(tuple));
        assert_eq!(
            tuple_data
                .interface
                .reference
                .resolved_type_arguments
                .as_deref(),
            Some([tuple_parameter].as_slice())
        );
        let TypeCacheState::Allocated(tuple_instantiations) =
            &tuple_data.interface.reference.object.instantiations
        else {
            panic!("expected initialized tuple instantiations")
        };
        assert_eq!(tuple_instantiations.len(), 1);
        assert_eq!(
            tuple_instantiations.get(&tuple_self_instantiation_key),
            Some(&tuple)
        );
        assert!(tuple_record.object_flags().contains(ObjectFlags::REFERENCE));
        let tuple_this_data = type_parameter_snapshot(&seeded.store, tuple_this);
        assert!(tuple_this_data.is_this_type);
        assert_eq!(tuple_this_data.constraint, Some(tuple));
        assert!(!seeded.store.set_object_target_and_mapper(
            tuple,
            Some(seeded.base),
            Some(seeded.mapper),
        ));
        assert!(!seeded.store.set_type_reference_resolution(
            tuple,
            Some(seeded.reference_node),
            Some(vec![seeded.base]),
        ));
        assert!(!seeded.store.set_object_instantiations(
            tuple,
            TypeCacheState::Allocated(HashMap::from([(CacheHashKey::new(100), seeded.base)])),
        ));
        assert!(!seeded.store.initialize_interface_type_parameters(
            tuple,
            vec![tuple_parameter, tuple_this],
            0,
            tuple_this,
            tuple_self_instantiation_key,
        ));
        assert!(
            !seeded
                .store
                .set_type_parameter_resolution(tuple_this, None, None, None, None,)
        );
    }

    #[test]
    fn object_instantiation_reservation_requires_an_owned_allocated_cache() {
        let mut seeded = seeded_store("local");
        let foreign = seeded_store("foreign");
        let uninitialized = seeded
            .store
            .alloc_interface_type(ObjectFlags::INTERFACE, Some(seeded.symbol))
            .unwrap();

        assert!(
            !seeded
                .store
                .try_reserve_object_instantiations(foreign.base, 1)
        );
        assert!(
            !seeded
                .store
                .try_reserve_object_instantiations(seeded.base, 1)
        );
        assert!(
            !seeded
                .store
                .try_reserve_object_instantiations(uninitialized, 1)
        );
        assert_eq!(
            object_instantiation_snapshot(&seeded.store, uninitialized),
            TypeCacheState::Unallocated
        );

        let parameter = seeded.store.alloc_type_parameter(None).unwrap();
        let this_type = seeded.store.alloc_type_parameter(None).unwrap();
        assert!(seeded.store.initialize_interface_type_parameters(
            uninitialized,
            vec![parameter, this_type],
            0,
            this_type,
            CacheHashKey::new(1),
        ));
        let before_failure = object_instantiation_snapshot(&seeded.store, uninitialized);
        assert!(
            !seeded
                .store
                .try_reserve_object_instantiations(uninitialized, usize::MAX)
        );
        assert_eq!(
            object_instantiation_snapshot(&seeded.store, uninitialized),
            before_failure
        );
        assert!(
            seeded
                .store
                .try_reserve_object_instantiations(uninitialized, 2)
        );
        assert_eq!(
            object_instantiation_snapshot(&seeded.store, uninitialized),
            before_failure
        );
    }

    #[test]
    #[allow(clippy::too_many_lines)] // One cache-growth and provenance transition matrix.
    fn object_instantiation_cache_growth_preserves_origin_identity_and_provenance() {
        let mut seeded = seeded_store("local");
        let interface = seeded
            .store
            .alloc_interface_type(ObjectFlags::INTERFACE, Some(seeded.symbol))
            .unwrap();
        let parameter = seeded.store.alloc_type_parameter(None).unwrap();
        let this_type = seeded.store.alloc_type_parameter(None).unwrap();
        let self_key = CacheHashKey::new(1);
        assert!(seeded.store.initialize_interface_type_parameters(
            interface,
            vec![parameter, this_type],
            0,
            this_type,
            self_key,
        ));

        let reference = seeded
            .store
            .alloc_type_reference(ObjectFlags::NONE, Some(seeded.symbol))
            .unwrap();
        assert!(
            seeded
                .store
                .set_object_target_and_mapper(reference, Some(interface), None)
        );
        assert!(seeded.store.set_type_reference_resolution(
            reference,
            None,
            Some(vec![seeded.base]),
        ));
        let reference_key = CacheHashKey::new(2);
        assert_eq!(
            seeded
                .store
                .insert_object_instantiation(interface, reference_key, reference),
            Some(reference)
        );
        let TypeCacheState::Allocated(cache) =
            object_instantiation_snapshot(&seeded.store, interface)
        else {
            panic!("expected allocated interface cache")
        };
        assert_eq!(cache.len(), 2);
        assert_eq!(cache.get(&self_key), Some(&interface));
        assert_eq!(cache.get(&reference_key), Some(&reference));

        let replacement = seeded
            .store
            .alloc_type_reference(ObjectFlags::NONE, Some(seeded.symbol))
            .unwrap();
        assert!(
            seeded
                .store
                .set_object_target_and_mapper(replacement, Some(interface), None)
        );
        let stable_cache = object_instantiation_snapshot(&seeded.store, interface);
        assert_eq!(
            seeded
                .store
                .insert_object_instantiation(interface, reference_key, replacement),
            Some(reference)
        );
        assert_eq!(
            seeded
                .store
                .insert_object_instantiation(interface, self_key, replacement),
            Some(interface)
        );
        assert_eq!(
            seeded
                .store
                .insert_object_instantiation(interface, CacheHashKey::new(3), interface,),
            None
        );

        let wrong_target = seeded
            .store
            .alloc_type_reference(ObjectFlags::NONE, Some(seeded.symbol))
            .unwrap();
        assert!(
            seeded
                .store
                .set_object_target_and_mapper(wrong_target, Some(seeded.base), None)
        );
        assert_eq!(
            seeded
                .store
                .insert_object_instantiation(interface, CacheHashKey::new(4), wrong_target,),
            None
        );
        let foreign = seeded_store("foreign");
        assert_eq!(
            seeded
                .store
                .insert_object_instantiation(interface, CacheHashKey::new(5), foreign.base,),
            None
        );
        assert_eq!(
            object_instantiation_snapshot(&seeded.store, interface),
            stable_cache
        );

        let object = seeded
            .store
            .alloc_plain_object_type(ObjectFlags::ANONYMOUS, Some(seeded.symbol))
            .unwrap();
        assert_eq!(
            seeded
                .store
                .insert_object_instantiation(object, CacheHashKey::new(6), seeded.base,),
            None
        );
        assert!(
            seeded
                .store
                .set_object_instantiations(object, TypeCacheState::Allocated(HashMap::new()),)
        );
        assert_eq!(
            seeded
                .store
                .insert_object_instantiation(object, CacheHashKey::new(6), seeded.base,),
            Some(seeded.base)
        );
        assert_eq!(
            seeded
                .store
                .insert_object_instantiation(object, CacheHashKey::new(6), interface,),
            Some(seeded.base)
        );
    }

    #[test]
    fn intrinsic_construction_rejects_dispatch_mismatches_without_allocation() {
        let mut store = TestStore::new();
        let count = store.type_len();
        assert_eq!(
            store.alloc_intrinsic_type(TypeFlags::STRING | TypeFlags::NUMBER, "invalid"),
            None
        );
        assert_eq!(
            store.alloc_intrinsic_type(TypeFlags::BOOLEAN, "invalid"),
            None
        );
        assert_eq!(
            store.alloc_intrinsic_type_ex(TypeFlags::STRING, "invalid", ObjectFlags::ANONYMOUS,),
            None
        );
        assert_eq!(store.type_len(), count);
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
