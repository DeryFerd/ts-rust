//! Exact nongeneric property-key extraction.
//!
//! This leaf implements the dependency-independent prefix of pinned
//! `getIndexType` and `getLiteralTypeFromProperties`. It accepts only fully
//! resolved, source-owned interfaces and type literals. Named properties
//! become canonical regular string-literal types, a number index contributes
//! `number`, and a string index contributes `string | number`. The latter
//! absorbs every explicit property and number index in the result.
//!
//! Anonymous type literals can use the existing canonical literal/union
//! caches directly. A class/interface/reference or aliased object with two or
//! more raw key contributions requires upstream's checker-owned `propertiesTypes`
//! cache and an `IndexType(target)` union origin. Those shared facilities are
//! deliberately not recreated here: [`resolve_nongeneric_keyof_type`] returns
//! [`NongenericKeyofError::NamedOriginRequired`] before its first write.
//!
//! Generic objects, unions, intersections, tuples, apparent/inherited
//! members, computed/unique-symbol names, and unresolved member surfaces are
//! explicit composition boundaries.

use std::collections::HashSet;

use ts_ast::{NodeRef, SyntaxKind};
use ts_binder::{CheckFlags, InternalSymbolName, SemanticSymbolId, SymbolFlags};

use super::{
    CanonicalTypeMapperStore, TypeId,
    bootstrap::LiteralTypeCacheError,
    links::ValueSymbolLinks,
    object_members::{
        DeclaredPropertyObjectProof, DeclaredPropertyObjectValidation,
        validate_resolved_declared_property_object,
    },
    store::SourceNodeParent,
    type_records::{
        ConstrainedTypeData, InterfaceTypeData, ObjectTypeData, StructuredTypeData, TypeCacheState,
        TypeData, TypeRecord,
    },
    types::{ObjectFlags, TypeFlags},
};

/// One fully validated, reduced-object key surface.
///
/// Property names remain strings until execution so a named-origin boundary
/// can be returned without populating global literal caches. The plan is
/// immutable and contains enough information for the root-owned
/// `propertiesTypes`/`IndexType` follow-up.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct NongenericKeyofPlan {
    target: TypeId,
    proof: DeclaredPropertyObjectProof,
    property_names: Vec<String>,
    has_string_index: bool,
    has_number_index: bool,
    preserves_origin: bool,
}

impl NongenericKeyofPlan {
    pub(super) const fn target(&self) -> TypeId {
        self.target
    }

    pub(super) const fn proof(&self) -> DeclaredPropertyObjectProof {
        self.proof
    }

    pub(super) fn property_names(&self) -> &[String] {
        &self.property_names
    }

    pub(super) const fn has_string_index(&self) -> bool {
        self.has_string_index
    }

    pub(super) const fn has_number_index(&self) -> bool {
        self.has_number_index
    }

    pub(super) const fn preserves_origin(&self) -> bool {
        self.preserves_origin
    }

    /// Count after pinned literal reduction.
    ///
    /// A string index always reduces the result to `string | number`.
    pub(super) fn reduced_key_count(&self) -> usize {
        if self.has_string_index {
            2
        } else {
            self.property_names.len() + usize::from(self.has_number_index)
        }
    }

    /// Number of entries passed to pinned `getUnionTypeEx` before reduction.
    ///
    /// A string index contributes the already-unioned
    /// `stringOrNumberType` as one raw entry. `getUnionTypeEx` returns a
    /// single raw entry before consulting its origin, so this count—not the
    /// reduced cardinality—controls named-origin construction.
    pub(super) fn raw_contribution_count(&self) -> usize {
        self.property_names.len()
            + usize::from(self.has_string_index)
            + usize::from(self.has_number_index)
    }

    pub(super) fn named_origin_required(&self) -> bool {
        self.preserves_origin && self.raw_contribution_count() >= 2
    }
}

/// Exact failure or named-origin composition boundary.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum NongenericKeyofError {
    InvalidType(TypeId),
    UnsupportedObject(TypeId),
    MalformedObject(TypeId),
    NamedOriginRequired {
        target: TypeId,
        raw_contribution_count: usize,
        reduced_key_count: usize,
    },
    LiteralCache(LiteralTypeCacheError),
}

impl From<LiteralTypeCacheError> for NongenericKeyofError {
    fn from(error: LiteralTypeCacheError) -> Self {
        Self::LiteralCache(error)
    }
}

impl std::fmt::Display for NongenericKeyofError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(formatter, "nongeneric keyof resolution failed: {self:?}")
    }
}

impl std::error::Error for NongenericKeyofError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::LiteralCache(error) => Some(error),
            _ => None,
        }
    }
}

/// Extracts one exact resolved interface/type-literal key surface.
///
/// The function is read-only. In particular, it does not resolve members,
/// instantiate references, or populate literal/union caches.
pub(super) fn plan_nongeneric_keyof_type(
    store: &CanonicalTypeMapperStore,
    target: TypeId,
) -> Result<NongenericKeyofPlan, NongenericKeyofError> {
    let record = store
        .type_payload(target)
        .ok_or(NongenericKeyofError::InvalidType(target))?;

    let proof = match validate_resolved_declared_property_object(store, target) {
        DeclaredPropertyObjectValidation::Valid(proof) => proof,
        DeclaredPropertyObjectValidation::Malformed => {
            return Err(NongenericKeyofError::MalformedObject(target));
        }
        DeclaredPropertyObjectValidation::NotDeclared => {
            match validate_resolved_indexed_declared_object(store, target, record)? {
                Some(proof) => proof,
                None => return Err(NongenericKeyofError::UnsupportedObject(target)),
            }
        }
    };
    let structured = record
        .data()
        .structured()
        .ok_or(NongenericKeyofError::MalformedObject(target))?;
    let property_names = exact_property_names(store, structured)
        .ok_or(NongenericKeyofError::MalformedObject(target))?;
    let (has_string_index, has_number_index) = exact_index_kinds(store, structured)
        .ok_or(NongenericKeyofError::MalformedObject(target))?;
    let preserves_origin = proof == DeclaredPropertyObjectProof::Interface
        || record
            .object_flags()
            .intersects(ObjectFlags::CLASS_OR_INTERFACE | ObjectFlags::REFERENCE)
        || record.alias().is_some();
    Ok(NongenericKeyofPlan {
        target,
        proof,
        property_names,
        has_string_index,
        has_number_index,
        preserves_origin,
    })
}

/// Resolves an already validated anonymous/nongeneric key plan.
///
/// Repeated calls return the same literal/union identity and allocate nothing
/// after the first call. Named multi-key plans return their typed boundary
/// before literal-cache preparation, preserving atomic failure.
pub(super) fn resolve_nongeneric_keyof_type(
    store: &mut CanonicalTypeMapperStore,
    plan: &NongenericKeyofPlan,
) -> Result<TypeId, NongenericKeyofError> {
    validate_plan_against_store(store, plan)?;
    if plan.named_origin_required() {
        return Err(NongenericKeyofError::NamedOriginRequired {
            target: plan.target,
            raw_contribution_count: plan.raw_contribution_count(),
            reduced_key_count: plan.reduced_key_count(),
        });
    }

    // Pinned getLiteralTypeFromProperties asks for property literals even
    // when a string index later absorbs them during union reduction.
    let strings = plan.property_names.clone();
    let union_operations = usize::from(!plan.has_string_index && plan.reduced_key_count() >= 2);
    let mut prepared = store.prepare_type_query_types(&strings, &[], &[], union_operations, 0)?;
    let mut keys = Vec::with_capacity(plan.property_names.len() + 1);
    for name in &plan.property_names {
        keys.push(store.regular_string_literal_type(name.clone())?);
    }

    let (number_type, string_or_number_type, never_type) = {
        let bootstrap = store
            .intrinsic_bootstrap()
            .ok_or(LiteralTypeCacheError::BootstrapUninitialized)?;
        (
            bootstrap.number_type,
            bootstrap.string_or_number_type,
            bootstrap.never_type,
        )
    };
    if plan.has_string_index {
        return Ok(string_or_number_type);
    }
    if plan.has_number_index {
        keys.push(number_type);
    }
    keys.sort_unstable();
    keys.dedup();
    match keys.len() {
        0 => Ok(never_type),
        1 => Ok(keys[0]),
        _ => store
            .literal_union_type_prepared(&keys, None, &mut prepared)
            .map_err(Into::into),
    }
}

fn validate_plan_against_store(
    store: &CanonicalTypeMapperStore,
    plan: &NongenericKeyofPlan,
) -> Result<(), NongenericKeyofError> {
    let current = plan_nongeneric_keyof_type(store, plan.target)?;
    if current == *plan {
        Ok(())
    } else {
        Err(NongenericKeyofError::MalformedObject(plan.target))
    }
}

fn exact_property_names(
    store: &CanonicalTypeMapperStore,
    structured: &StructuredTypeData,
) -> Option<Vec<String>> {
    let properties = structured.properties.as_deref().unwrap_or_default();
    let mut names = Vec::with_capacity(properties.len());
    let mut seen_symbols = HashSet::with_capacity(properties.len());
    let mut seen_names = HashSet::with_capacity(properties.len());
    for property in properties {
        let record = store.symbol(*property)?;
        let name = record.name().as_utf8()?.to_owned();
        if !seen_symbols.insert(*property) || !seen_names.insert(name.clone()) {
            return None;
        }
        names.push(name);
    }
    Some(names)
}

fn exact_index_kinds(
    store: &CanonicalTypeMapperStore,
    structured: &StructuredTypeData,
) -> Option<(bool, bool)> {
    let Some(bootstrap) = store.intrinsic_bootstrap() else {
        return None;
    };
    let mut string = false;
    let mut number = false;
    let mut seen = HashSet::new();
    for id in structured.index_infos.as_deref().unwrap_or_default() {
        if !seen.insert(*id) {
            return None;
        }
        let info = store.index_info(*id)?;
        let slot = if info.key_type() == bootstrap.string_type {
            &mut string
        } else if info.key_type() == bootstrap.number_type {
            &mut number
        } else {
            return None;
        };
        if std::mem::replace(slot, true) {
            return None;
        }
    }
    Some((string, number))
}

fn validate_resolved_indexed_declared_object(
    store: &CanonicalTypeMapperStore,
    target: TypeId,
    record: &TypeRecord,
) -> Result<Option<DeclaredPropertyObjectProof>, NongenericKeyofError> {
    let Some(structured) = record.data().structured() else {
        return Ok(None);
    };
    if structured
        .index_infos
        .as_deref()
        .is_none_or(|indexes| indexes.is_empty())
    {
        return Ok(None);
    }
    if record.flags() != TypeFlags::OBJECT {
        return Err(NongenericKeyofError::MalformedObject(target));
    }
    let result = match record.data() {
        TypeData::Object(object) => {
            validate_indexed_type_literal_shell(store, target, record, object)
                .then_some(DeclaredPropertyObjectProof::TypeLiteral)
        }
        TypeData::Interface(interface) => {
            validate_indexed_interface_shell(store, target, record, interface)
                .then_some(DeclaredPropertyObjectProof::Interface)
        }
        _ => return Ok(None),
    };
    result
        .ok_or(NongenericKeyofError::MalformedObject(target))
        .map(Some)
}

fn validate_indexed_type_literal_shell(
    store: &CanonicalTypeMapperStore,
    target: TypeId,
    record: &TypeRecord,
    object: &ObjectTypeData,
) -> bool {
    let Some(owner) = record.symbol() else {
        return false;
    };
    let Some(owner_record) = store.symbol(owner) else {
        return false;
    };
    let Some([declaration]) = owner_record.declarations() else {
        return false;
    };
    record.object_flags() == ObjectFlags::ANONYMOUS | ObjectFlags::MEMBERS_RESOLVED
        && valid_object_tail(object)
        && valid_indexed_structured_tail(&object.structured)
        && owner_record.flags() == SymbolFlags::TYPE_LITERAL
        && owner_record.check_flags() == CheckFlags::NONE
        && owner_record.name() == InternalSymbolName::Type.as_ref()
        && owner_record.value_declaration().is_none()
        && owner_record.members() == object.structured.members
        && owner_record.exports().is_none()
        && owner_record.parent().is_none()
        && owner_record.export_symbol().is_none()
        && store.get_merged_symbol(owner) == Some(owner)
        && store.source_node_kind(*declaration) == Some(SyntaxKind::TypeLiteral)
        && store.type_node_links(*declaration).is_some_and(|links| {
            links.resolved_type == Some(target) && links.outer_type_parameters.is_none()
        })
        && valid_nongeneric_type_literal_alias(store, target, record, *declaration)
        && validate_indexed_member_table(store, owner, *declaration, &object.structured)
}

fn validate_indexed_interface_shell(
    store: &CanonicalTypeMapperStore,
    target: TypeId,
    record: &TypeRecord,
    interface: &InterfaceTypeData,
) -> bool {
    let Some(owner) = record.symbol() else {
        return false;
    };
    let Some(owner_record) = store.symbol(owner) else {
        return false;
    };
    let Some([declaration]) = owner_record.declarations() else {
        return false;
    };
    let object = &interface.reference.object;
    record.alias().is_none()
        && record.object_flags() == ObjectFlags::INTERFACE | ObjectFlags::MEMBERS_RESOLVED
        && valid_interface_identity(interface)
        && interface.base_types_resolved
        && interface.resolved_base_constructor_type.is_none()
        && interface.resolved_base_types.is_none()
        && interface.declared_members_resolved
        && interface.declared_members == object.structured.members
        && interface.declared_call_signatures.is_none()
        && interface.declared_construct_signatures.is_none()
        && interface.declared_index_infos.as_ref() == object.structured.index_infos.as_ref()
        && valid_indexed_structured_tail(&object.structured)
        && owner_record.flags() == SymbolFlags::INTERFACE
        && owner_record.check_flags() == CheckFlags::NONE
        && owner_record.name().as_utf8().is_some()
        && owner_record.value_declaration().is_none()
        && owner_record.members() == object.structured.members
        && owner_record.exports().is_none()
        && owner_record.parent().is_none()
        && owner_record.export_symbol().is_none()
        && store.get_merged_symbol(owner) == Some(owner)
        && store.source_node_is_exported(*declaration) == Some(false)
        && store.source_node_kind(*declaration) == Some(SyntaxKind::InterfaceDeclaration)
        && store
            .declared_type_links(owner)
            .is_some_and(|links| links.declared_type == Some(target))
        && validate_indexed_member_table(store, owner, *declaration, &object.structured)
}

fn valid_nongeneric_type_literal_alias(
    store: &CanonicalTypeMapperStore,
    target: TypeId,
    record: &TypeRecord,
    type_literal: NodeRef,
) -> bool {
    let Some(alias_id) = record.alias() else {
        return true;
    };
    let Some(alias) = store.type_alias(alias_id) else {
        return false;
    };
    let Some(symbol) = alias.symbol() else {
        return false;
    };
    let Some(symbol_record) = store.symbol(symbol) else {
        return false;
    };
    let Some([declaration]) = symbol_record.declarations() else {
        return false;
    };
    let mut child = type_literal;
    let direct = loop {
        let Some(SourceNodeParent::Parent(parent)) = store.source_node_parent(child) else {
            break false;
        };
        match store.source_node_kind(parent) {
            Some(SyntaxKind::ParenthesizedType) => child = parent,
            Some(SyntaxKind::TypeAliasDeclaration) => break parent == *declaration,
            _ => break false,
        }
    };
    direct
        && alias.type_arguments().is_none()
        && symbol_record.flags() == SymbolFlags::TYPE_ALIAS
        && symbol_record.check_flags() == CheckFlags::NONE
        && symbol_record.value_declaration().is_none()
        && symbol_record.members().is_none()
        && symbol_record.exports().is_none()
        && symbol_record.parent().is_none()
        && symbol_record.export_symbol().is_none()
        && store.get_merged_symbol(symbol) == Some(symbol)
        && store.source_node_is_exported(*declaration) == Some(false)
        && store.source_node_kind(*declaration) == Some(SyntaxKind::TypeAliasDeclaration)
        && store.type_alias_links(symbol).is_some_and(|links| {
            links.declared_type == Some(target)
                && links.type_parameters.is_none()
                && links.instantiations.is_none()
                && !links.is_constructor_declared_property
        })
        && store
            .type_alias_declared_type_owners(target)
            .is_some_and(|owners| owners.len() == 1 && owners.contains(&symbol))
}

fn valid_object_tail(object: &ObjectTypeData) -> bool {
    object.target.is_none()
        && object.mapper.is_none()
        && object.instantiations == TypeCacheState::Unallocated
}

fn valid_interface_identity(interface: &InterfaceTypeData) -> bool {
    interface.all_type_parameters.is_none()
        && interface.outer_type_parameter_count == 0
        && interface.this_type.is_none()
        && valid_object_tail(&interface.reference.object)
        && interface.reference.node.is_none()
        && interface.reference.resolved_type_arguments.is_none()
}

fn valid_indexed_structured_tail(structured: &StructuredTypeData) -> bool {
    structured.constrained == ConstrainedTypeData::default()
        && structured.signatures.is_none()
        && structured.call_signature_count == 0
        && structured
            .index_infos
            .as_ref()
            .is_some_and(|indexes| !indexes.is_empty())
        && structured
            .object_type_without_abstract_construct_signatures
            .is_none()
}

fn validate_indexed_member_table(
    store: &CanonicalTypeMapperStore,
    owner: SemanticSymbolId,
    owner_declaration: NodeRef,
    structured: &StructuredTypeData,
) -> bool {
    let properties = structured.properties.as_deref().unwrap_or_default();
    let indexes = structured.index_infos.as_deref().unwrap_or_default();
    let Some(members) = structured.members else {
        return false;
    };
    let Some(table) = store.symbol_table(members) else {
        return false;
    };
    if table.len() != properties.len() + 1 {
        return false;
    }

    let mut seen_properties = HashSet::with_capacity(properties.len());
    let mut seen_names = HashSet::with_capacity(properties.len());
    for property in properties {
        let Some(property_record) = store.symbol(*property) else {
            return false;
        };
        let Some([declaration]) = property_record.declarations() else {
            return false;
        };
        let allowed_flags = SymbolFlags::PROPERTY | SymbolFlags::OPTIONAL;
        let Some(name) = property_record.name().as_utf8() else {
            return false;
        };
        let Some(property_type) = store
            .value_symbol_links(*property)
            .and_then(|links| links.resolved_type)
        else {
            return false;
        };
        if !seen_properties.insert(*property)
            || !seen_names.insert(name.to_owned())
            || !property_record.flags().contains(SymbolFlags::PROPERTY)
            || property_record.flags().without(allowed_flags) != SymbolFlags::NONE
            || property_record.check_flags().bits() & !CheckFlags::READONLY.bits() != 0
            || property_record.name().is_reserved_member_name()
            || property_record.name().is_private_identifier()
            || property_record.name().is_late_bound()
            || property_record.value_declaration() != Some(*declaration)
            || property_record.parent() != Some(owner)
            || property_record.members().is_some()
            || property_record.exports().is_some()
            || property_record.export_symbol().is_some()
            || store.get_merged_symbol(*property) != Some(*property)
            || !matches!(
                store.source_node_kind(*declaration),
                Some(SyntaxKind::PropertyDeclaration | SyntaxKind::PropertySignature)
            )
            || store.source_node_parent(*declaration)
                != Some(SourceNodeParent::Parent(owner_declaration))
            || table.get(property_record.name()) != Some(*property)
            || store.value_symbol_links(*property)
                != Some(&ValueSymbolLinks {
                    resolved_type: Some(property_type),
                    ..ValueSymbolLinks::default()
                })
            || store.type_payload(property_type).is_none()
        {
            return false;
        }
    }

    let Some(index_symbol) = table.get(InternalSymbolName::Index.as_ref()) else {
        return false;
    };
    let Some(index_record) = store.symbol(index_symbol) else {
        return false;
    };
    let mut seen_infos = HashSet::with_capacity(indexes.len());
    let mut seen_keys = HashSet::with_capacity(indexes.len());
    let mut seen_declarations = HashSet::with_capacity(indexes.len());
    let declarations = indexes
        .iter()
        .map(|id| {
            let info = store.index_info(*id)?;
            let declaration = info.declaration()?;
            if !seen_infos.insert(*id)
                || !seen_keys.insert(info.key_type())
                || !seen_declarations.insert(declaration)
                || info.index_symbol().is_some()
                || !info.components().is_empty()
                || store.type_payload(info.value_type()).is_none()
                || store.source_node_kind(declaration) != Some(SyntaxKind::IndexSignature)
                || store.source_node_parent(declaration)
                    != Some(SourceNodeParent::Parent(owner_declaration))
            {
                return None;
            }
            Some(declaration)
        })
        .collect::<Option<Vec<_>>>();
    declarations.as_deref().is_some_and(|declarations| {
        index_record.flags() == SymbolFlags::SIGNATURE
            && index_record.check_flags() == CheckFlags::NONE
            && index_record.name() == InternalSymbolName::Index.as_ref()
            && index_record.declarations() == Some(declarations)
            && index_record.value_declaration().is_none()
            && index_record.members().is_none()
            && index_record.exports().is_none()
            && index_record.parent() == Some(owner)
            && index_record.export_symbol().is_none()
            && store.get_merged_symbol(index_symbol) == Some(index_symbol)
    })
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;

    use ts_ast::{FileId, NodeRef, SyntaxKind};
    use ts_binder::{
        BoundFile, CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts,
        CanonicalSourceLanguage, EscapedName, SemanticSymbolId,
    };
    use ts_parser::{ParseResult, parse_source_file};

    use super::{NongenericKeyofError, plan_nongeneric_keyof_type, resolve_nongeneric_keyof_type};
    use crate::semantic::{
        CanonicalTypeMapperStore, DeclaredTypeHost, IntrinsicBootstrapOptions, TypeAliasLinks,
        TypeId, object_members, type_records::TypeData,
    };

    struct Fixture {
        parsed: ParseResult,
        file: FileId,
        files: BTreeMap<FileId, BoundFile>,
        store: CanonicalTypeMapperStore,
    }

    fn fixture(source: &str) -> Fixture {
        let parsed = parse_source_file(source);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(75_001);
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source("\"/keyof.ts\""),
                    CanonicalSourceLanguage::TypeScript,
                    false,
                    CanonicalModuleState::Script,
                ),
            )
            .unwrap();
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
        let (symbols, files) = binder.finish().try_into_parts().unwrap();
        let mut store = CanonicalTypeMapperStore::from_symbol_store(symbols);
        assert!(
            store
                .register_source_file(&parsed.arena, parsed.source_file, file)
                .is_some()
        );
        store
            .initialize_intrinsic_bootstrap(IntrinsicBootstrapOptions::default())
            .unwrap();
        Fixture {
            parsed,
            file,
            files,
            store,
        }
    }

    fn node_of_kind(fixture: &Fixture, kind: SyntaxKind) -> NodeRef {
        fixture
            .parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == kind).then_some(NodeRef::new(
                    fixture.parsed.arena.id(),
                    fixture.file,
                    node,
                ))
            })
            .unwrap_or_else(|| panic!("fixture must contain {kind:?}"))
    }

    fn bound_symbol(fixture: &Fixture, node: NodeRef) -> SemanticSymbolId {
        let bound = fixture.files.get(&fixture.file).unwrap();
        bound
            .symbol(node)
            .or_else(|| bound.local_symbol(node))
            .unwrap()
    }

    fn keyword_type(store: &CanonicalTypeMapperStore, node: NodeRef, recursive: TypeId) -> TypeId {
        let bootstrap = store.intrinsic_bootstrap().unwrap();
        match store.source_node_kind(node).unwrap() {
            SyntaxKind::StringKeyword => bootstrap.string_type,
            SyntaxKind::NumberKeyword => bootstrap.number_type,
            SyntaxKind::BooleanKeyword => bootstrap.boolean_type,
            SyntaxKind::TypeReference => recursive,
            kind => panic!("unsupported test annotation {kind:?}"),
        }
    }

    fn resolve_inline_literal(fixture: &mut Fixture, paired_indexes: bool) -> TypeId {
        resolve_literal(fixture, paired_indexes, None)
    }

    fn resolve_aliased_literal(fixture: &mut Fixture) -> TypeId {
        let alias = node_of_kind(fixture, SyntaxKind::TypeAliasDeclaration);
        let symbol = bound_symbol(fixture, alias);
        resolve_literal(fixture, false, Some(symbol))
    }

    fn resolve_literal(
        fixture: &mut Fixture,
        paired_indexes: bool,
        alias: Option<SemanticSymbolId>,
    ) -> TypeId {
        let literal = node_of_kind(fixture, SyntaxKind::TypeLiteral);
        let host = DeclaredTypeHost::new([(
            &fixture.parsed.arena,
            fixture.files.get(&fixture.file).unwrap(),
        )])
        .unwrap();
        let plan = if paired_indexes {
            object_members::plan_concrete_indexed_access_type_literal(
                &fixture.store,
                &host,
                literal,
            )
            .unwrap()
        } else {
            object_members::plan_type_literal(&fixture.store, &host, literal, alias).unwrap()
        };
        let property_types = plan
            .property_type_nodes()
            .map(|node| keyword_type(&fixture.store, node, literal_type_sentinel(&fixture.store)))
            .collect::<Vec<_>>();
        let index_types = plan
            .index_type_nodes()
            .map(|(key, value)| {
                (
                    keyword_type(&fixture.store, key, literal_type_sentinel(&fixture.store)),
                    keyword_type(&fixture.store, value, literal_type_sentinel(&fixture.store)),
                )
            })
            .collect::<Vec<_>>();
        let state = object_members::ensure_type_literal_shell(&mut fixture.store, &plan).unwrap();
        let type_ = object_members::publish_declared_members(
            &mut fixture.store,
            &plan,
            state,
            &property_types,
            &index_types,
            &[],
        )
        .unwrap();
        if let Some(alias) = alias {
            assert!(fixture.store.set_type_alias_links(
                alias,
                TypeAliasLinks {
                    declared_type: Some(type_),
                    ..TypeAliasLinks::default()
                },
            ));
        }
        type_
    }

    fn literal_type_sentinel(store: &CanonicalTypeMapperStore) -> TypeId {
        store.intrinsic_bootstrap().unwrap().error_type
    }

    fn resolve_interface(fixture: &mut Fixture) -> TypeId {
        let declaration = node_of_kind(fixture, SyntaxKind::InterfaceDeclaration);
        let symbol = bound_symbol(fixture, declaration);
        let host = DeclaredTypeHost::new([(
            &fixture.parsed.arena,
            fixture.files.get(&fixture.file).unwrap(),
        )])
        .unwrap();
        let plan = object_members::plan_interface(&fixture.store, &host, symbol).unwrap();
        let type_ = fixture
            .store
            .get_declared_type_of_symbol(&host, symbol)
            .unwrap();
        let property_types = plan
            .property_type_nodes()
            .map(|node| keyword_type(&fixture.store, node, type_))
            .collect::<Vec<_>>();
        let state = object_members::interface_state(&fixture.store, &plan, type_).unwrap();
        object_members::publish_declared_members(
            &mut fixture.store,
            &plan,
            state,
            &property_types,
            &[],
            &[],
        )
        .unwrap()
    }

    fn union_constituents(store: &CanonicalTypeMapperStore, type_: TypeId) -> Vec<TypeId> {
        match store.type_payload(type_).unwrap().data() {
            TypeData::Union(union) => union.union.types.clone(),
            _ => vec![type_],
        }
    }

    fn cache_state(store: &CanonicalTypeMapperStore) -> (usize, usize, usize) {
        let bootstrap = store.intrinsic_bootstrap().unwrap();
        (
            store.type_len(),
            bootstrap.string_literal_cache_len(),
            bootstrap.union_cache_len(),
        )
    }

    #[test]
    fn anonymous_property_keys_are_canonical_and_warm_is_allocation_free() {
        let mut fixture = fixture("type Keys = keyof { alpha: string; beta: number };");
        let object = resolve_inline_literal(&mut fixture, false);
        let plan = plan_nongeneric_keyof_type(&fixture.store, object).unwrap();
        assert_eq!(plan.property_names(), ["alpha", "beta"]);
        assert!(!plan.preserves_origin());

        let cold = resolve_nongeneric_keyof_type(&mut fixture.store, &plan).unwrap();
        let after_cold = cache_state(&fixture.store);
        let warm = resolve_nongeneric_keyof_type(&mut fixture.store, &plan).unwrap();
        assert_eq!(warm, cold);
        assert_eq!(cache_state(&fixture.store), after_cold);

        let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
        assert_eq!(union_constituents(&fixture.store, cold), {
            let mut keys = vec![
                bootstrap.cached_string_literal_type("alpha").unwrap(),
                bootstrap.cached_string_literal_type("beta").unwrap(),
            ];
            keys.sort_unstable();
            keys
        });
    }

    #[test]
    fn index_precedence_matches_pinned_keyof_reduction() {
        let mut number = fixture("type Keys = keyof { named: string; [key: number]: number };");
        let number_object = resolve_inline_literal(&mut number, false);
        let number_plan = plan_nongeneric_keyof_type(&number.store, number_object).unwrap();
        assert!(!number_plan.has_string_index());
        assert!(number_plan.has_number_index());
        let number_result = resolve_nongeneric_keyof_type(&mut number.store, &number_plan).unwrap();
        let bootstrap = number.store.intrinsic_bootstrap().unwrap();
        let mut expected = vec![
            bootstrap.number_type,
            bootstrap.cached_string_literal_type("named").unwrap(),
        ];
        expected.sort_unstable();
        assert_eq!(union_constituents(&number.store, number_result), expected);

        let mut string = fixture("type Keys = keyof { named: string; [key: string]: string };");
        let string_object = resolve_inline_literal(&mut string, false);
        let string_plan = plan_nongeneric_keyof_type(&string.store, string_object).unwrap();
        assert!(string_plan.has_string_index());
        let string_result = resolve_nongeneric_keyof_type(&mut string.store, &string_plan).unwrap();
        let string_warm_state = cache_state(&string.store);
        assert_eq!(
            string_result,
            string
                .store
                .intrinsic_bootstrap()
                .unwrap()
                .string_or_number_type
        );
        assert!(
            string
                .store
                .intrinsic_bootstrap()
                .unwrap()
                .cached_string_literal_type("named")
                .is_some(),
            "pinned property-literal evaluation precedes string-index absorption"
        );
        assert_eq!(
            resolve_nongeneric_keyof_type(&mut string.store, &string_plan).unwrap(),
            string_result
        );
        assert_eq!(cache_state(&string.store), string_warm_state);

        let mut paired =
            fixture("type Keys = keyof { [text: string]: string; [position: number]: string };");
        let paired_object = resolve_inline_literal(&mut paired, true);
        let paired_plan = plan_nongeneric_keyof_type(&paired.store, paired_object).unwrap();
        assert!(paired_plan.has_string_index());
        assert!(paired_plan.has_number_index());
        assert_eq!(
            resolve_nongeneric_keyof_type(&mut paired.store, &paired_plan).unwrap(),
            paired
                .store
                .intrinsic_bootstrap()
                .unwrap()
                .string_or_number_type
        );
    }

    #[test]
    fn named_multi_key_plan_stops_before_global_cache_mutation() {
        let mut fixture = fixture("interface Model { first: string; second: number }");
        let interface = resolve_interface(&mut fixture);
        let plan = plan_nongeneric_keyof_type(&fixture.store, interface).unwrap();
        assert!(plan.preserves_origin());
        assert!(plan.named_origin_required());
        let before = cache_state(&fixture.store);
        assert_eq!(
            resolve_nongeneric_keyof_type(&mut fixture.store, &plan),
            Err(NongenericKeyofError::NamedOriginRequired {
                target: interface,
                raw_contribution_count: 2,
                reduced_key_count: 2,
            })
        );
        assert_eq!(cache_state(&fixture.store), before);
    }

    #[test]
    fn named_string_index_uses_raw_contribution_count_for_origin_boundary() {
        let mut index_only = fixture("type Table = { [key: string]: string };");
        let table = resolve_aliased_literal(&mut index_only);
        let plan = plan_nongeneric_keyof_type(&index_only.store, table).unwrap();
        assert!(plan.preserves_origin());
        assert_eq!(plan.raw_contribution_count(), 1);
        assert_eq!(plan.reduced_key_count(), 2);
        assert!(!plan.named_origin_required());
        assert_eq!(
            resolve_nongeneric_keyof_type(&mut index_only.store, &plan).unwrap(),
            index_only
                .store
                .intrinsic_bootstrap()
                .unwrap()
                .string_or_number_type
        );

        let mut mixed = fixture("type Table = { named: string; [key: string]: string };");
        let table = resolve_aliased_literal(&mut mixed);
        let plan = plan_nongeneric_keyof_type(&mixed.store, table).unwrap();
        assert_eq!(plan.raw_contribution_count(), 2);
        assert_eq!(plan.reduced_key_count(), 2);
        let before = cache_state(&mixed.store);
        assert_eq!(
            resolve_nongeneric_keyof_type(&mut mixed.store, &plan),
            Err(NongenericKeyofError::NamedOriginRequired {
                target: table,
                raw_contribution_count: 2,
                reduced_key_count: 2,
            })
        );
        assert_eq!(cache_state(&mixed.store), before);
    }

    #[test]
    fn named_single_key_and_recursive_value_cycle_do_not_need_origin_union() {
        let mut fixture = fixture("interface Node { next: Node }");
        let interface = resolve_interface(&mut fixture);
        let plan = plan_nongeneric_keyof_type(&fixture.store, interface).unwrap();
        assert_eq!(plan.property_names(), ["next"]);
        let result = resolve_nongeneric_keyof_type(&mut fixture.store, &plan).unwrap();
        assert_eq!(
            result,
            fixture
                .store
                .intrinsic_bootstrap()
                .unwrap()
                .cached_string_literal_type("next")
                .unwrap()
        );
    }

    #[test]
    fn duplicate_and_poisoned_member_surfaces_fail_closed() {
        let mut duplicate = fixture("type Keys = keyof { left: string; right: number };");
        let object = resolve_inline_literal(&mut duplicate, false);
        let (members, property, indexes) = {
            let structured = duplicate
                .store
                .type_payload(object)
                .and_then(|record| record.data().structured())
                .unwrap();
            (
                structured.members,
                structured.properties.as_ref().unwrap()[0],
                structured.index_infos.clone(),
            )
        };
        assert!(duplicate.store.set_structured_type_members(
            object,
            members,
            Some(vec![property, property]),
            None,
            None,
            indexes,
        ));
        assert_eq!(
            plan_nongeneric_keyof_type(&duplicate.store, object),
            Err(NongenericKeyofError::MalformedObject(object))
        );

        let mut poisoned = fixture("type Keys = keyof { named: string; [key: number]: number };");
        let indexed = resolve_inline_literal(&mut poisoned, false);
        let (members, properties, index) = {
            let structured = poisoned
                .store
                .type_payload(indexed)
                .and_then(|record| record.data().structured())
                .unwrap();
            (
                structured.members,
                structured.properties.clone(),
                structured.index_infos.as_ref().unwrap()[0],
            )
        };
        assert!(poisoned.store.set_structured_type_members(
            indexed,
            members,
            properties,
            None,
            None,
            Some(vec![index, index]),
        ));
        assert_eq!(
            plan_nongeneric_keyof_type(&poisoned.store, indexed),
            Err(NongenericKeyofError::MalformedObject(indexed))
        );
    }

    #[test]
    fn foreign_and_composite_targets_are_explicit_boundaries() {
        let mut first = fixture("type Keys = keyof { local: string };");
        let local = resolve_inline_literal(&mut first, false);
        let second = fixture("type Other = string;");
        assert_eq!(
            plan_nongeneric_keyof_type(&second.store, local),
            Err(NongenericKeyofError::InvalidType(local))
        );

        let string = first.store.intrinsic_bootstrap().unwrap().string_type;
        let number = first.store.intrinsic_bootstrap().unwrap().number_type;
        let union = first
            .store
            .alloc_union_type(
                crate::semantic::types::ObjectFlags::PRIMITIVE_UNION,
                vec![string, number],
            )
            .unwrap();
        assert_eq!(
            plan_nongeneric_keyof_type(&first.store, union),
            Err(NongenericKeyofError::UnsupportedObject(union))
        );
    }

    #[test]
    fn empty_anonymous_literal_reuses_never() {
        let mut fixture = fixture("type Keys = keyof {};");
        let object = resolve_inline_literal(&mut fixture, false);
        let plan = plan_nongeneric_keyof_type(&fixture.store, object).unwrap();
        assert_eq!(plan.reduced_key_count(), 0);
        assert_eq!(
            resolve_nongeneric_keyof_type(&mut fixture.store, &plan).unwrap(),
            fixture.store.intrinsic_bootstrap().unwrap().never_type
        );
    }
}
