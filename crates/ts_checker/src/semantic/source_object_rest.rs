//! Proof for indexed objects copied by an actual object-rest binding.

use ts_ast::{NodeRef, SyntaxKind};
use ts_binder::{CheckFlags, EscapedName, SemanticSymbolId, SymbolFlags, SymbolTableId};

use super::{
    CanonicalTypeMapperStore,
    ids::{IndexInfoId, TypeAliasId, TypeId},
    relater::RelationUnavailable,
    type_records::{MappedTypeData, ObjectTypeData, TypeData, TypeRecord},
    types::{ObjectFlags, TypeFlags},
};

#[derive(Clone, Debug, Eq, PartialEq)]
enum ObjectShape {
    Object(ObjectTypeData),
    Mapped(MappedTypeData),
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct PropertyProof {
    symbol: SemanticSymbolId,
    name: EscapedName,
    flags: SymbolFlags,
    checks: CheckFlags,
    parent: Option<SemanticSymbolId>,
    merged: SemanticSymbolId,
    members: Option<SymbolTableId>,
    exports: Option<SymbolTableId>,
    export: Option<SemanticSymbolId>,
    declarations: Option<Vec<NodeRef>>,
    value: Option<NodeRef>,
    type_: Option<TypeId>,
}

impl PropertyProof {
    fn read(store: &CanonicalTypeMapperStore, symbol: SemanticSymbolId) -> Option<Self> {
        let record = store.symbol(symbol)?;
        Some(Self {
            symbol,
            name: record.name().to_owned(),
            flags: record.flags(),
            checks: record.check_flags(),
            parent: record.parent(),
            merged: store.get_merged_symbol(symbol)?,
            members: record.members(),
            exports: record.exports(),
            export: record.export_symbol(),
            declarations: record.declarations().map(<[NodeRef]>::to_vec),
            value: record.value_declaration(),
            type_: store
                .value_symbol_links(symbol)
                .and_then(|links| links.resolved_type),
        })
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct IndexProof {
    id: IndexInfoId,
    key: TypeId,
    value: TypeId,
    readonly: bool,
    declaration: Option<NodeRef>,
    symbol: Option<SemanticSymbolId>,
    components: Vec<NodeRef>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct ObjectProof {
    flags: ObjectFlags,
    owner: Option<PropertyProof>,
    alias: Option<(TypeAliasId, Option<SemanticSymbolId>, Option<Vec<TypeId>>)>,
    shape: ObjectShape,
    members: Vec<(EscapedName, SemanticSymbolId)>,
    properties: Vec<PropertyProof>,
    indexes: Vec<IndexProof>,
}

impl ObjectProof {
    fn read(store: &CanonicalTypeMapperStore, type_: TypeId) -> Option<Self> {
        let record = store.type_payload(type_)?;
        if record.flags() != TypeFlags::OBJECT
            || !record
                .object_flags()
                .contains(ObjectFlags::MEMBERS_RESOLVED)
        {
            return None;
        }
        let shape = match record.data() {
            TypeData::Object(object) => ObjectShape::Object(object.clone()),
            TypeData::Mapped(mapped) => ObjectShape::Mapped(mapped.clone()),
            _ => return None,
        };
        let structured = record.data().structured()?;
        if structured.signatures.is_some() || structured.call_signature_count != 0 {
            return None;
        }
        let properties = structured
            .properties
            .as_deref()
            .unwrap_or_default()
            .iter()
            .map(|symbol| PropertyProof::read(store, *symbol))
            .collect::<Option<Vec<_>>>()?;
        let members = match structured.members {
            Some(table) => store
                .symbol_table(table)?
                .iter()
                .map(|(name, symbol)| (name.to_owned(), symbol))
                .collect(),
            None => Vec::new(),
        };
        let indexes = structured
            .index_infos
            .as_deref()
            .unwrap_or_default()
            .iter()
            .map(|id| {
                let info = store.index_info(*id)?;
                Some(IndexProof {
                    id: *id,
                    key: info.key_type(),
                    value: info.value_type(),
                    readonly: info.is_readonly(),
                    declaration: info.declaration(),
                    symbol: info.index_symbol(),
                    components: info.components().to_vec(),
                })
            })
            .collect::<Option<Vec<_>>>()?;
        let owner = match record.symbol() {
            Some(owner) => Some(PropertyProof::read(store, owner)?),
            None => None,
        };
        let alias = match record.alias() {
            Some(id) => {
                let alias = store.type_alias(id)?;
                Some((
                    id,
                    alias.symbol(),
                    alias.type_arguments().map(<[TypeId]>::to_vec),
                ))
            }
            None => None,
        };
        Some(Self {
            flags: record.object_flags(),
            owner,
            alias,
            shape,
            members,
            properties,
            indexes,
        })
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct SourceObjectRestOrigin {
    result: TypeId,
    receiver: TypeId,
    binding: NodeRef,
    symbol: SemanticSymbolId,
    excluded: Vec<String>,
    source: ObjectProof,
    copied: ObjectProof,
}

impl SourceObjectRestOrigin {
    pub(super) const fn result(&self) -> TypeId {
        self.result
    }

    pub(super) fn references_index(&self, id: IndexInfoId) -> bool {
        self.source.indexes.iter().any(|index| index.id == id)
    }

    pub(super) fn new(
        store: &CanonicalTypeMapperStore,
        result: TypeId,
        receiver: TypeId,
        binding: NodeRef,
        symbol: SemanticSymbolId,
        excluded: Vec<String>,
    ) -> Option<Self> {
        // A rest result cannot be its own source. Nested rest copies stay unsupported.
        if result == receiver || store.source_object_rest_origin(receiver).is_some() {
            return None;
        }
        let origin = Self {
            result,
            receiver,
            binding,
            symbol,
            excluded,
            source: ObjectProof::read(store, receiver)?,
            copied: ObjectProof::read(store, result)?,
        };
        origin.is_exact(store).then_some(origin)
    }

    fn is_exact(&self, store: &CanonicalTypeMapperStore) -> bool {
        if self.result == self.receiver
            || store.source_object_rest_origin(self.receiver).is_some()
            || store.source_node_kind(self.binding) != Some(SyntaxKind::BindingElement)
            || store
                .symbol(self.symbol)
                .and_then(|symbol| symbol.value_declaration())
                != Some(self.binding)
            || ObjectProof::read(store, self.receiver).as_ref() != Some(&self.source)
            || ObjectProof::read(store, self.result).as_ref() != Some(&self.copied)
            || self.copied.flags != ObjectFlags::ANONYMOUS | ObjectFlags::MEMBERS_RESOLVED
            || self.copied.owner.is_some()
            || self.copied.alias.is_some()
            || self.copied.indexes != self.source.indexes
        {
            return false;
        }
        if matches!(
            store.type_payload(self.receiver).map(TypeRecord::data),
            Some(TypeData::Mapped(_))
        ) && !matches!(
            store.validate_mapped_type_relation_endpoint(self.receiver),
            Ok(Some(_))
        ) {
            return false;
        }
        let retained: Vec<_> = self
            .source
            .properties
            .iter()
            .filter(|property| {
                property
                    .name
                    .as_ref()
                    .as_utf8()
                    .is_some_and(|name| !self.excluded.iter().any(|key| key == name))
            })
            .collect();
        retained.len() == self.copied.properties.len()
            && self.copied.members.len() == retained.len()
            && retained
                .iter()
                .zip(&self.copied.properties)
                .all(|(source, copied)| {
                    source.symbol != copied.symbol
                        && source.name == copied.name
                        && source.type_ == copied.type_
                        && copied.type_.is_some()
                        && copied.flags
                            == (SymbolFlags::PROPERTY
                                | SymbolFlags::TRANSIENT
                                | (source.flags & SymbolFlags::OPTIONAL))
                        && copied.checks == CheckFlags::NONE
                        && copied.parent.is_none()
                        && copied.merged == copied.symbol
                        && copied.members.is_none()
                        && copied.exports.is_none()
                        && copied.export.is_none()
                        && copied.declarations.is_none()
                        && copied.value.is_none()
                        && self
                            .copied
                            .members
                            .iter()
                            .any(|(name, symbol)| name == &copied.name && *symbol == copied.symbol)
                })
    }
}

pub(super) fn validate(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
) -> Result<bool, RelationUnavailable> {
    let Some(origin) = store.source_object_rest_origin(type_) else {
        return Ok(false);
    };
    if origin.result != type_ || !origin.is_exact(store) {
        return Err(RelationUnavailable::InvalidStructuredMembers(type_));
    }
    Ok(true)
}
