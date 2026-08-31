//! Standard-library identities created by the pinned `initializeChecker`.
//!
//! This module owns the dependency-closed initialization sequence after
//! ordinary globals and global-scope augmentations have been merged. Missing
//! or malformed required library declarations retain the pinned empty-type
//! fallback. Wrong-kind and wrong-arity records are exact; missing-name
//! records include the pinned eager-name library hints, while general spelling
//! suggestion elaboration remains a later checker-diagnostics capability.
//! Unsupported semantic dependencies fail construction instead of silently
//! changing a type identity.

use std::collections::HashSet;

use ts_ast::{FileId, NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalNameResolutionError, CheckFlags, EscapedName, EscapedNameRef, InternalSymbolName,
    SemanticStoreId, SemanticSymbolId, SymbolFlags, SymbolTableId, resolve_global_name,
    semantic::{PreparedSymbolTable, should_replace_value_declaration},
};
use ts_diagnostics::{Diagnostic, message_by_code};

use super::{
    CanonicalTypeMapperStore, DeclaredTypeError, DeclaredTypeHost, TypeId, ValueSymbolLinks,
    declared::{DeclaredTypeUnavailable, cached_ordinary_type_parameter_owner, type_list_key},
    store::SourceNodeParent,
    type_records::{StructuredTypeData, TypeCacheState, TypeData},
    types::{ObjectFlags, TypeFlags},
};

const GLOBAL_TYPE_MUST_BE_CLASS_OR_INTERFACE: u32 = 2_316;
const GLOBAL_TYPE_MUST_HAVE_ARITY: u32 = 2_317;
const CANNOT_FIND_GLOBAL_TYPE: u32 = 2_318;
const ES2015_LIBRARY_SUGGESTION: &str = "es2015";

/// One diagnostic produced while resolving the pinned standard-library
/// identities. A missing global has no source node; wrong-kind and wrong-arity
/// diagnostics use the first class/interface/enum/type-alias declaration just
/// like `getGlobalTypeDeclaration` upstream.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CanonicalGlobalTypeDiagnostic {
    pub node: Option<NodeRef>,
    pub diagnostic: Diagnostic,
}

/// A demanded global and the source proof retained with its diagnostics.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct ResolvedGlobalType {
    type_: TypeId,
    diagnostics: Vec<CanonicalGlobalTypeDiagnostic>,
    proof: RequiredGlobalTypeProof,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct RequiredGlobalTypeProof {
    globals: SymbolTableId,
    name: String,
    arity: usize,
    symbol: Option<RequiredGlobalSymbolProof>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct RequiredGlobalSymbolProof {
    symbol: SemanticSymbolId,
    flags: SymbolFlags,
    declarations: Vec<NodeRef>,
    declared_type: Option<TypeId>,
}

impl ResolvedGlobalType {
    pub(super) const fn type_(&self) -> TypeId {
        self.type_
    }

    pub(super) fn diagnostics(&self) -> &[CanonicalGlobalTypeDiagnostic] {
        &self.diagnostics
    }

    pub(super) fn is_for(&self, name: &str, arity: usize) -> bool {
        self.proof.name == name && self.proof.arity == arity
    }

    pub(super) fn validate(
        &self,
        store: &CanonicalTypeMapperStore,
        host: &DeclaredTypeHost<'_>,
    ) -> Result<(), CanonicalGlobalTypeInitializationError> {
        if store.type_payload(self.type_).is_none()
            || self.proof
                != required_global_type_proof(store, host, &self.proof.name, self.proof.arity)?
        {
            return Err(CanonicalGlobalTypeInitializationError::InvalidType(
                self.type_,
            ));
        }
        Ok(())
    }
}

/// The eager standard-library identities installed by `initializeChecker`.
///
/// These IDs belong to the enclosing [`super::CanonicalCheckerContext`]. The
/// empty object/generic fallbacks are observable when a library is absent or
/// malformed, and [`Self::diagnostics`] records every required fallback.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CanonicalGlobalTypes {
    pub arguments_type: TypeId,
    pub global_this_value_type: TypeId,
    pub array_type: TypeId,
    pub object_type: TypeId,
    pub function_type: TypeId,
    pub callable_function_type: TypeId,
    pub newable_function_type: TypeId,
    pub string_type: TypeId,
    pub number_type: TypeId,
    pub boolean_type: TypeId,
    pub regexp_type: TypeId,
    pub any_array_type: TypeId,
    pub auto_array_type: TypeId,
    pub readonly_array_type: TypeId,
    pub any_readonly_array_type: TypeId,
    pub this_type: TypeId,
    diagnostics: Vec<CanonicalGlobalTypeDiagnostic>,
}

impl CanonicalGlobalTypes {
    /// Global fallback records in pinned initialization order.
    ///
    /// TS2316/TS2317 and the eager-name missing-library arguments are exact.
    /// General missing-name spelling suggestions remain a later diagnostics
    /// slice and currently retain the base TS2318 record.
    #[must_use]
    pub fn diagnostics(&self) -> &[CanonicalGlobalTypeDiagnostic] {
        &self.diagnostics
    }
}

/// One original global entry. Value types stay with the normal source query.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct GlobalThisMember {
    export_name: EscapedName,
    name: EscapedName,
    table_symbol: SemanticSymbolId,
    symbol: SemanticSymbolId,
    flags: SymbolFlags,
    canonical_flags: SymbolFlags,
    check_flags: CheckFlags,
    parent: Option<SemanticSymbolId>,
    declarations: Vec<NodeRef>,
    value_declaration: Option<NodeRef>,
    builtin_value_type: Option<TypeId>,
    first_declaration: Option<(usize, u32)>,
    retained: bool,
    value: bool,
}

impl GlobalThisMember {
    pub(super) const fn table_symbol(&self) -> SemanticSymbolId {
        self.table_symbol
    }

    pub(super) const fn symbol(&self) -> SemanticSymbolId {
        self.symbol
    }

    pub(super) const fn flags(&self) -> SymbolFlags {
        self.flags
    }

    pub(super) const fn check_flags(&self) -> CheckFlags {
        self.check_flags
    }

    pub(super) const fn parent(&self) -> Option<SemanticSymbolId> {
        self.parent
    }

    pub(super) fn declarations(&self) -> &[NodeRef] {
        &self.declarations
    }

    pub(super) const fn value_declaration(&self) -> Option<NodeRef> {
        self.value_declaration
    }

    pub(super) const fn builtin_value_type(&self) -> Option<TypeId> {
        self.builtin_value_type
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct GlobalThisMemberPlan {
    store: SemanticStoreId,
    receiver: TypeId,
    symbol: SemanticSymbolId,
    globals: SymbolTableId,
    exports: Vec<GlobalThisMember>,
    members: Vec<(EscapedName, SemanticSymbolId)>,
    properties: Vec<SemanticSymbolId>,
}

/// A query-local proof over the context's borrowed Program order.
/// It does not borrow the store or prepare any ordinary member value.
#[derive(Clone, Debug)]
pub(super) struct GlobalThisMembers<'host, 'arena> {
    host: &'host DeclaredTypeHost<'arena>,
    plan: GlobalThisMemberPlan,
    members_table: SymbolTableId,
}

impl GlobalThisMembers<'_, '_> {
    pub(super) const fn receiver(&self) -> TypeId {
        self.plan.receiver
    }

    pub(super) const fn symbol(&self) -> SemanticSymbolId {
        self.plan.symbol
    }

    pub(super) const fn globals(&self) -> SymbolTableId {
        self.plan.globals
    }

    pub(super) const fn members_table(&self) -> SymbolTableId {
        self.members_table
    }

    pub(super) fn members(&self) -> &[(EscapedName, SemanticSymbolId)] {
        &self.plan.members
    }

    pub(super) fn properties(&self) -> &[SemanticSymbolId] {
        &self.plan.properties
    }

    /// Looks up a named value property, keeping its original table identity.
    pub(super) fn get_source(&self, name: &str) -> Option<SemanticSymbolId> {
        self.plan
            .exports
            .iter()
            .find(|entry| entry.value && entry.name.as_utf8() == Some(name))
            .map(GlobalThisMember::table_symbol)
    }

    /// Reads a named value row by its original table identity, not a redirect.
    pub(super) fn member(&self, symbol: SemanticSymbolId) -> Option<&GlobalThisMember> {
        self.plan
            .exports
            .iter()
            .find(|entry| entry.value && entry.table_symbol == symbol)
    }

    /// Includes type-only and filtered exports for type lookup and diagnostics.
    pub(super) fn export_source(&self, name: &str) -> Option<&GlobalThisMember> {
        self.plan
            .exports
            .iter()
            .find(|entry| entry.export_name.as_utf8() == Some(name))
    }

    pub(super) fn validate(
        &self,
        store: &CanonicalTypeMapperStore,
    ) -> Result<(), DeclaredTypeError> {
        let identity = global_this_identity(store, self.plan.receiver)?;
        if identity.members != Some(self.members_table)
            || self.plan != global_this_member_plan(store, self.host, self.plan.receiver)?
        {
            return Err(invalid_global_this_members(self.plan.receiver));
        }
        validate_global_this_ready_members(store, &self.plan, self.members_table)
    }
}

/// This is only a rejection or demand hint. It does not admit a type graph.
pub(super) fn is_global_this_type_candidate(
    store: &CanonicalTypeMapperStore,
    globals: Option<&CanonicalGlobalTypes>,
    receiver: TypeId,
) -> bool {
    globals.is_some_and(|globals| globals.global_this_value_type == receiver)
        || store.intrinsic_bootstrap().is_some_and(|bootstrap| {
            store
                .value_symbol_links(bootstrap.global_this_symbol)
                .is_some_and(|links| links.resolved_type == Some(receiver))
                || store
                    .type_payload(receiver)
                    .is_some_and(|record| record.symbol() == Some(bootstrap.global_this_symbol))
        })
}

/// Recognizes the existing synthetic value after ordinary lexical resolution.
pub(super) fn source_global_this_value_type(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    globals: &CanonicalGlobalTypes,
    symbol: SemanticSymbolId,
) -> Result<Option<TypeId>, DeclaredTypeError> {
    let bootstrap = store
        .intrinsic_bootstrap()
        .ok_or(DeclaredTypeUnavailable::IntrinsicBootstrapNotInitialized)?;
    let canonical = store
        .get_merged_symbol(symbol)
        .ok_or(DeclaredTypeUnavailable::SymbolNotOwned(symbol))?;
    if symbol != bootstrap.global_this_symbol && canonical != bootstrap.global_this_symbol {
        return Ok(None);
    }
    if symbol != bootstrap.global_this_symbol {
        return Err(DeclaredTypeUnavailable::InvalidGlobalThisSymbol(symbol).into());
    }
    let receiver = globals.global_this_value_type;
    let identity = global_this_identity(store, receiver)?;
    if let Some(members) = identity.members {
        let plan = global_this_member_plan(store, host, receiver)?;
        validate_global_this_ready_members(store, &plan, members)?;
    }
    Ok(Some(receiver))
}

/// Proves one original export without preparing members or value types.
pub(super) fn source_global_this_export(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    globals: &CanonicalGlobalTypes,
    receiver: TypeId,
    name: &str,
) -> Result<Option<GlobalThisMember>, DeclaredTypeError> {
    if receiver != globals.global_this_value_type {
        return Err(invalid_global_this_members(receiver));
    }
    let identity = global_this_identity(store, receiver)?;
    let plan = global_this_member_plan(store, host, receiver)?;
    if let Some(members) = identity.members {
        validate_global_this_ready_members(store, &plan, members)?;
    }
    Ok(plan
        .exports
        .into_iter()
        .find(|member| member.export_name.as_utf8() == Some(name)))
}

/// Publishes one complete filtered table on the existing synthetic type.
pub(super) fn prepare_global_this_members<'host, 'arena>(
    store: &mut CanonicalTypeMapperStore,
    host: &'host DeclaredTypeHost<'arena>,
    globals: &CanonicalGlobalTypes,
    receiver: TypeId,
) -> Result<Option<GlobalThisMembers<'host, 'arena>>, DeclaredTypeError> {
    if !is_global_this_type_candidate(store, Some(globals), receiver) {
        return Ok(None);
    }
    if receiver != globals.global_this_value_type {
        return Err(invalid_global_this_members(receiver));
    }
    let identity = global_this_identity(store, receiver)?;
    let plan = global_this_member_plan(store, host, receiver)?;
    let members_table = if let Some(members) = identity.members {
        validate_global_this_ready_members(store, &plan, members)?;
        members
    } else {
        let capacity =
            || DeclaredTypeError::from(DeclaredTypeUnavailable::GlobalThisCapacity(receiver));
        let prepared = PreparedSymbolTable::new(plan.members.len()).ok_or_else(capacity)?;
        let mut properties = Vec::new();
        properties
            .try_reserve_exact(plan.properties.len())
            .map_err(|_| capacity())?;
        properties.extend_from_slice(&plan.properties);
        if !store.try_reserve_checker_symbol_allocations(0, 1) {
            return Err(capacity());
        }
        let members = store.alloc_prepared_symbol_table(prepared);
        for (name, symbol) in &plan.members {
            assert_eq!(
                store.insert_symbol(members, name.clone(), *symbol),
                Some(None)
            );
        }
        assert!(store.set_structured_type_members(
            receiver,
            Some(members),
            Some(properties),
            None,
            None,
            None,
        ));
        members
    };
    Ok(Some(GlobalThisMembers {
        host,
        plan,
        members_table,
    }))
}

#[derive(Clone, Copy)]
struct GlobalThisIdentity {
    symbol: SemanticSymbolId,
    globals: SymbolTableId,
    members: Option<SymbolTableId>,
}

fn invalid_global_this_members(receiver: TypeId) -> DeclaredTypeError {
    DeclaredTypeUnavailable::InvalidGlobalThisMembers(receiver).into()
}

fn invalid_global_this_member(receiver: TypeId, symbol: SemanticSymbolId) -> DeclaredTypeError {
    DeclaredTypeUnavailable::InvalidGlobalThisMember { receiver, symbol }.into()
}

fn global_this_identity(
    store: &CanonicalTypeMapperStore,
    receiver: TypeId,
) -> Result<GlobalThisIdentity, DeclaredTypeError> {
    let bootstrap = store
        .intrinsic_bootstrap()
        .ok_or(DeclaredTypeUnavailable::IntrinsicBootstrapNotInitialized)?;
    let symbol = bootstrap.global_this_symbol;
    let invalid_symbol =
        || DeclaredTypeError::from(DeclaredTypeUnavailable::InvalidGlobalThisSymbol(symbol));
    let record = store.symbol(symbol).ok_or_else(invalid_symbol)?;
    let flags = SymbolFlags::MODULE | SymbolFlags::TRANSIENT;
    let bindings = store.source_global_bindings().ok_or_else(invalid_symbol)?;
    let binding = bindings
        .get(EscapedNameRef::source("globalThis"))
        .ok_or_else(invalid_symbol)?;
    if store.get_merged_symbol(symbol) != Some(symbol)
        || record.name().as_utf8() != Some("globalThis")
        || record.flags() != flags
        || record.check_flags() != CheckFlags::READONLY
        || record.declarations().is_some()
        || record.value_declaration().is_some()
        || record.members().is_some()
        || record.exports() != Some(bootstrap.globals)
        || record.parent().is_some()
        || record.export_symbol().is_some()
        || bindings.table != bootstrap.globals
        || binding.table_symbol != symbol
        || binding.symbol != symbol
        || binding.flags != flags
        || binding.declarations().is_some()
        || store
            .symbol_table(bootstrap.globals)
            .and_then(|table| table.get_source("globalThis"))
            != Some(symbol)
        || store.value_symbol_links(symbol)
            != Some(&ValueSymbolLinks {
                resolved_type: Some(receiver),
                ..ValueSymbolLinks::default()
            })
        || store.module_symbol_links(symbol).is_some_and(|links| {
            links
                .resolved_exports
                .is_some_and(|table| table != bootstrap.globals)
                || links.type_only_export_star_map.is_some()
                || links.exports_checked
        })
    {
        return Err(invalid_symbol());
    }
    let invalid = || invalid_global_this_members(receiver);
    let record = store.type_payload(receiver).ok_or_else(invalid)?;
    let TypeData::Object(object) = record.data() else {
        return Err(invalid());
    };
    if record.flags() != TypeFlags::OBJECT
        || record.symbol() != Some(symbol)
        || record.alias().is_some()
        || object.target.is_some()
        || object.mapper.is_some()
        || object.instantiations != TypeCacheState::Unallocated
    {
        return Err(invalid());
    }
    let members = if record.object_flags() == ObjectFlags::ANONYMOUS {
        if object.structured != StructuredTypeData::default() {
            return Err(invalid());
        }
        None
    } else if record.object_flags() == ObjectFlags::ANONYMOUS | ObjectFlags::MEMBERS_RESOLVED {
        let structured = &object.structured;
        if structured.properties.is_none()
            || structured.constrained != Default::default()
            || structured.signatures.is_some()
            || structured.call_signature_count != 0
            || structured.index_infos.is_some()
            || structured
                .object_type_without_abstract_construct_signatures
                .is_some()
        {
            return Err(invalid());
        }
        Some(structured.members.ok_or_else(invalid)?)
    } else {
        return Err(invalid());
    };
    Ok(GlobalThisIdentity {
        symbol,
        globals: bootstrap.globals,
        members,
    })
}

fn global_this_member_plan(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    receiver: TypeId,
) -> Result<GlobalThisMemberPlan, DeclaredTypeError> {
    let identity = global_this_identity(store, receiver)?;
    let invalid = || invalid_global_this_members(receiver);
    let order = host.program_file_order().ok_or(
        DeclaredTypeUnavailable::GlobalThisProgramOrderUnavailable(receiver),
    )?;
    let mut files = HashSet::new();
    if order
        .iter()
        .any(|file| !files.insert(*file) || !host.has_program_file(*file))
    {
        return Err(DeclaredTypeUnavailable::GlobalThisProgramOrderUnavailable(receiver).into());
    }
    let bindings = store.source_global_bindings().ok_or_else(invalid)?;
    let table = store.symbol_table(identity.globals).ok_or_else(invalid)?;
    if bindings.table != identity.globals || bindings.iter().count() != table.len() {
        return Err(invalid());
    }
    let mut exports = Vec::new();
    for (name, table_symbol) in table.iter() {
        let binding = bindings.get(name).ok_or_else(invalid)?;
        if binding.table_symbol != table_symbol
            || store.get_merged_symbol(table_symbol) != Some(binding.symbol)
        {
            return Err(invalid_global_this_member(receiver, table_symbol));
        }
        exports.push(global_this_member(
            store, host, order, receiver, name, binding,
        )?);
    }
    exports.sort_by(|left, right| left.export_name.cmp(&right.export_name));
    let mut members = exports
        .iter()
        .filter(|entry| entry.retained)
        .map(|entry| (entry.name.clone(), entry.table_symbol))
        .collect::<Vec<_>>();
    members.sort_by(|left, right| left.0.cmp(&right.0));
    if members.windows(2).any(|pair| pair[0].0 == pair[1].0) {
        return Err(invalid());
    }
    let mut properties = exports
        .iter()
        .filter(|entry| entry.value)
        .collect::<Vec<_>>();
    properties.sort_by(|left, right| {
        match (left.first_declaration, right.first_declaration) {
            (Some(left), Some(right)) => left.cmp(&right),
            (Some(_), None) => std::cmp::Ordering::Less,
            (None, Some(_)) => std::cmp::Ordering::Greater,
            (None, None) => std::cmp::Ordering::Equal,
        }
        .then_with(|| left.name.cmp(&right.name))
        .then_with(|| left.table_symbol.cmp(&right.table_symbol))
    });
    let properties = properties
        .into_iter()
        .map(GlobalThisMember::table_symbol)
        .collect();
    Ok(GlobalThisMemberPlan {
        store: store.id(),
        receiver,
        symbol: identity.symbol,
        globals: identity.globals,
        exports,
        members,
        properties,
    })
}

fn validate_global_this_ready_members(
    store: &CanonicalTypeMapperStore,
    plan: &GlobalThisMemberPlan,
    members: SymbolTableId,
) -> Result<(), DeclaredTypeError> {
    let invalid = || invalid_global_this_members(plan.receiver);
    let table = store.symbol_table(members).ok_or_else(invalid)?;
    if store.id() != plan.store
        || members == plan.globals
        || table.len() != plan.members.len()
        || plan
            .members
            .iter()
            .any(|(name, symbol)| table.get(name.as_ref()) != Some(*symbol))
        || store
            .type_payload(plan.receiver)
            .and_then(|record| record.data().structured())
            .and_then(|structured| structured.properties.as_deref())
            != Some(plan.properties.as_slice())
    {
        return Err(invalid());
    }
    Ok(())
}

fn global_this_member(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    order: &[FileId],
    receiver: TypeId,
    name: EscapedNameRef<'_>,
    binding: &super::store::SourceGlobalBinding,
) -> Result<GlobalThisMember, DeclaredTypeError> {
    let symbol = binding.symbol;
    let invalid = || invalid_global_this_member(receiver, symbol);
    let record = store.symbol(symbol).ok_or_else(invalid)?;
    let table_record = store.symbol(binding.table_symbol).ok_or_else(invalid)?;
    if store.get_merged_symbol(symbol) != Some(symbol)
        || record.flags() != binding.flags
        || record.declarations() != binding.declarations()
        || record.name() != name
        || table_record.name() != name
        || table_record.check_flags() != record.check_flags()
        || binding.table_symbol != symbol
            && !store.source_raw_symbol_declarations_match(binding.table_symbol)
    {
        return Err(invalid());
    }
    let bootstrap = store.intrinsic_bootstrap().ok_or_else(invalid)?;
    let builtin = if symbol == bootstrap.global_this_symbol {
        global_this_identity(store, receiver)?;
        Some(receiver)
    } else if symbol == bootstrap.undefined_symbol {
        let type_ = bootstrap.undefined_widening_type;
        let expected_flags = if type_ == bootstrap.undefined_type {
            ObjectFlags::NONE
        } else {
            ObjectFlags::CONTAINS_WIDENING_TYPE
        };
        if binding.table_symbol != symbol
            || record.flags() != SymbolFlags::PROPERTY | SymbolFlags::TRANSIENT
            || record.check_flags() != CheckFlags::NONE
            || record.name().as_utf8() != Some("undefined")
            || record.declarations().is_some()
            || record.value_declaration().is_some()
            || record.members().is_some()
            || record.exports().is_some()
            || record.parent().is_some()
            || record.export_symbol().is_some()
            || store.value_symbol_links(symbol) != Some(&ValueSymbolLinks {
                resolved_type: Some(type_), ..ValueSymbolLinks::default()
            })
            || !store.type_payload(type_).is_some_and(|record| {
                record.flags() == TypeFlags::UNDEFINED
                    && record.object_flags() == expected_flags
                    && record.symbol().is_none()
                    && record.alias().is_none()
                    && matches!(record.data(), TypeData::Intrinsic(data) if data.intrinsic_name == "undefined")
            })
        {
            return Err(invalid());
        }
        Some(type_)
    } else {
        if record.flags().intersects(SymbolFlags::ALIAS) {
            return Err(
                DeclaredTypeUnavailable::UnsupportedGlobalThisMember { receiver, symbol }.into(),
            );
        }
        let declarations = record
            .declarations()
            .filter(|declarations| !declarations.is_empty())
            .ok_or_else(invalid)?;
        if !store.source_merged_symbol_declarations_match(symbol)
            || record.check_flags() != CheckFlags::NONE
            || record.export_symbol().is_some()
        {
            return Err(invalid());
        }
        let mixed = if let Some(owner) = store.source_global_interface_value_owner(symbol)? {
            owner.validate_current(store)?;
            true
        } else {
            false
        };
        let mut selected = None;
        let mut first_parent = None;
        let mut raw_owners = HashSet::new();
        for &declaration in declarations {
            if !order.contains(&declaration.file)
                || !host.symbol_matches(store, declaration, symbol)
            {
                return Err(invalid());
            }
            validate_global_this_declaration(store, host, receiver, declaration, symbol, name)?;
            let bound = host.bound_file(declaration).ok_or_else(invalid)?;
            let raw = [bound.symbol(declaration), bound.local_symbol(declaration)]
                .into_iter()
                .flatten()
                .find(|raw| store.get_merged_symbol(*raw) == Some(symbol))
                .ok_or_else(invalid)?;
            if !store.source_raw_symbol_declarations_match(raw) {
                return Err(invalid());
            }
            let raw_record = store.symbol(raw).ok_or_else(invalid)?;
            validate_global_this_source_parent(store, host, receiver, declaration, raw)?;
            if raw_owners.is_empty() {
                first_parent = raw_record.parent();
            }
            if raw_owners.insert(raw)
                && !mixed
                && let Some(incoming) = raw_record.value_declaration()
                && selected.is_none_or(|current| {
                    store
                        .source_node_kind(current)
                        .zip(store.source_node_kind(incoming))
                        .is_some_and(|(current, incoming)| {
                            should_replace_value_declaration(current, incoming)
                        })
                })
            {
                selected = Some(incoming);
            }
        }
        if !mixed && (record.value_declaration() != selected || record.parent() != first_parent) {
            return Err(invalid());
        }
        None
    };
    let declarations = record.declarations().unwrap_or_default().to_vec();
    let first_declaration = table_record
        .declarations()
        .and_then(|declarations| declarations.first())
        .map(|declaration| {
            let file = order
                .iter()
                .position(|file| *file == declaration.file)
                .ok_or_else(invalid)?;
            let start = store.source_node_start(*declaration).ok_or_else(invalid)?;
            Ok::<_, DeclaredTypeError>((file, start))
        })
        .transpose()?;
    let all_ambient_modules = table_record.declarations().is_some_and(|declarations| {
        !declarations.is_empty()
            && declarations.iter().all(|declaration| {
                host.node(*declaration).is_some_and(|node| {
                    matches!(&node.data, NodeData::ModuleDeclaration(module)
                    if module.keyword == SyntaxKind::GlobalKeyword
                        || host.node(NodeRef::new(declaration.arena, declaration.file, module.name))
                            .is_some_and(|name| name.kind == SyntaxKind::StringLiteral))
                })
            })
    });
    let retained = !table_record.flags().intersects(SymbolFlags::BLOCK_SCOPED)
        && !(table_record.flags().intersects(SymbolFlags::VALUE_MODULE) && all_ambient_modules);
    let value = retained
        && !name.is_reserved_member_name()
        && table_record.flags().intersects(SymbolFlags::VALUE);
    Ok(GlobalThisMember {
        export_name: name.to_owned(),
        name: table_record.name().to_owned(),
        table_symbol: binding.table_symbol,
        symbol,
        flags: table_record.flags(),
        canonical_flags: record.flags(),
        check_flags: table_record.check_flags(),
        parent: record.parent(),
        declarations,
        value_declaration: record.value_declaration(),
        builtin_value_type: builtin,
        first_declaration,
        retained,
        value,
    })
}

fn validate_global_this_source_node(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    node: NodeRef,
) -> bool {
    host.node(node).is_some_and(|record| {
        store.source_node_kind(node) == Some(record.kind)
            && store.source_node_start(node) == Some(record.range.start.get())
            && store.source_node_parent(node) == Some(record.parent.map_or(SourceNodeParent::Root, |parent| {
                SourceNodeParent::Parent(NodeRef::new(node.arena, node.file, parent))
            }))
            && store.source_identifier_text(node).is_none_or(|text| {
                matches!(&record.data, NodeData::Identifier(identifier) if identifier.text == text)
            })
    })
}

fn validate_global_this_declaration(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    receiver: TypeId,
    declaration: NodeRef,
    symbol: SemanticSymbolId,
    expected_name: EscapedNameRef<'_>,
) -> Result<(), DeclaredTypeError> {
    let invalid = || invalid_global_this_member(receiver, symbol);
    let record = host.node(declaration).ok_or_else(invalid)?;
    if !validate_global_this_source_node(store, host, declaration) {
        return Err(invalid());
    }
    let name = match &record.data {
        NodeData::ClassDeclaration(class) => class.name,
        NodeData::InterfaceDeclaration(interface) => Some(interface.name),
        NodeData::TypeAliasDeclaration(alias) => Some(alias.name),
        NodeData::EnumDeclaration(enumeration) => Some(enumeration.name),
        NodeData::ModuleDeclaration(module) => Some(module.name),
        NodeData::FunctionDeclaration(function) => function.name,
        NodeData::VariableDeclaration(variable) => Some(variable.name),
        NodeData::BindingElement(binding) => binding.name,
        _ => {
            return Err(
                DeclaredTypeUnavailable::UnsupportedGlobalThisMember { receiver, symbol }.into(),
            );
        }
    }
    .ok_or_else(invalid)?;
    let name = NodeRef::new(declaration.arena, declaration.file, name);
    let named = if matches!(&record.data, NodeData::ModuleDeclaration(module) if module.keyword == SyntaxKind::GlobalKeyword)
    {
        expected_name == InternalSymbolName::Global.as_ref()
    } else {
        match host.node(name).map(|node| &node.data) {
            Some(NodeData::Identifier(identifier)) => {
                expected_name.as_utf8() == Some(identifier.text.as_str())
            }
            Some(NodeData::StringLiteral(literal))
                if record.kind == SyntaxKind::ModuleDeclaration =>
            {
                expected_name.as_utf8() == Some(format!("\"{}\"", literal.text).as_str())
            }
            _ => false,
        }
    };
    if !named || store.source_node_parent(name) != Some(SourceNodeParent::Parent(declaration)) {
        return Err(invalid());
    }
    let mut children = Vec::new();
    record.for_each_child(|child| {
        children.push(NodeRef::new(declaration.arena, declaration.file, child))
    });
    children.sort_unstable();
    if store.source_direct_children(declaration).as_deref() != Some(children.as_slice())
        || children
            .iter()
            .any(|child| !validate_global_this_source_node(store, host, *child))
    {
        return Err(invalid());
    }
    Ok(())
}

fn validate_global_this_source_parent(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    receiver: TypeId,
    declaration: NodeRef,
    raw: SemanticSymbolId,
) -> Result<(), DeclaredTypeError> {
    let invalid = || invalid_global_this_member(receiver, raw);
    let record = store.symbol(raw).ok_or_else(invalid)?;
    let mut node = declaration;
    let mut seen = HashSet::new();
    loop {
        if !seen.insert(node) || !validate_global_this_source_node(store, host, node) {
            return Err(invalid());
        }
        let parent = host
            .node(node)
            .and_then(|node| node.parent)
            .ok_or_else(invalid)?;
        node = NodeRef::new(node.arena, node.file, parent);
        let parent = host.node(node).ok_or_else(invalid)?;
        if !validate_global_this_source_node(store, host, node) {
            return Err(invalid());
        }
        if parent.kind == SyntaxKind::SourceFile {
            return if record.parent().is_none() {
                Ok(())
            } else {
                Err(invalid())
            };
        }
        if let NodeData::ModuleDeclaration(module) = &parent.data {
            let bound = host.bound_file(node).ok_or_else(invalid)?;
            let name = NodeRef::new(node.arena, node.file, module.name);
            if module.keyword != SyntaxKind::GlobalKeyword
                || !bound
                    .module_augmentations()
                    .iter()
                    .any(|augmentation| augmentation.name() == name)
                || record.parent() != bound.symbol(node)
                || record.parent().is_none()
            {
                return Err(invalid());
            }
            return Ok(());
        }
        if matches!(
            parent.kind,
            SyntaxKind::FunctionDeclaration
                | SyntaxKind::FunctionExpression
                | SyntaxKind::ArrowFunction
        ) {
            return Err(invalid());
        }
    }
}

/// An invariant or not-yet-ported semantic dependency that prevents exact
/// global-library initialization.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CanonicalGlobalTypeInitializationError {
    MissingBootstrap,
    InvalidGlobals(SymbolTableId),
    InvalidSymbol(SemanticSymbolId),
    InvalidType(TypeId),
    InvalidValueSymbolLinks(SemanticSymbolId),
    NameResolution(CanonicalNameResolutionError),
    DeclaredType(DeclaredTypeError),
    InvalidAnonymousType,
    InvalidAnonymousTypeMembers(TypeId),
    InvalidGenericTarget(TypeId),
    InvalidTypeReference(TypeId),
    InvalidInstantiationCache(TypeId),
    InvalidGlobalObjectDeclaration(NodeRef),
    InvalidGlobalObjectBaseResolution(TypeId),
}

impl std::fmt::Display for CanonicalGlobalTypeInitializationError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::MissingBootstrap => {
                formatter.write_str("global library types require intrinsic bootstrap")
            }
            Self::InvalidGlobals(_) => {
                formatter.write_str("global library types received a foreign globals table")
            }
            Self::InvalidSymbol(symbol) => {
                write!(
                    formatter,
                    "global library type references invalid symbol {symbol:?}"
                )
            }
            Self::InvalidType(type_id) => {
                write!(
                    formatter,
                    "global library initialization cannot read {type_id:?}"
                )
            }
            Self::InvalidValueSymbolLinks(symbol) => write!(
                formatter,
                "global library initialization cannot publish value links for {symbol:?}"
            ),
            Self::NameResolution(error) => write!(formatter, "{error}"),
            Self::DeclaredType(error) => write!(formatter, "{error}"),
            Self::InvalidAnonymousType => formatter
                .write_str("global library initialization cannot allocate an anonymous type"),
            Self::InvalidAnonymousTypeMembers(type_id) => write!(
                formatter,
                "global library anonymous type {type_id:?} rejected empty resolved members"
            ),
            Self::InvalidGenericTarget(type_id) => write!(
                formatter,
                "global library type {type_id:?} is not an initialized generic interface"
            ),
            Self::InvalidTypeReference(type_id) => write!(
                formatter,
                "global library initialization cannot create a reference to {type_id:?}"
            ),
            Self::InvalidInstantiationCache(type_id) => write!(
                formatter,
                "global library type {type_id:?} rejected its canonical instantiation"
            ),
            Self::InvalidGlobalObjectDeclaration(declaration) => write!(
                formatter,
                "global Object base resolution cannot validate declaration {declaration:?}"
            ),
            Self::InvalidGlobalObjectBaseResolution(type_id) => write!(
                formatter,
                "global Object type {type_id:?} has contradictory base-resolution state"
            ),
        }
    }
}

impl std::error::Error for CanonicalGlobalTypeInitializationError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::NameResolution(error) => Some(error),
            Self::DeclaredType(error) => Some(error),
            _ => None,
        }
    }
}

impl From<DeclaredTypeError> for CanonicalGlobalTypeInitializationError {
    fn from(error: DeclaredTypeError) -> Self {
        Self::DeclaredType(error)
    }
}

impl From<CanonicalNameResolutionError> for CanonicalGlobalTypeInitializationError {
    fn from(error: CanonicalNameResolutionError) -> Self {
        Self::NameResolution(error)
    }
}

#[derive(Clone, Copy)]
struct BootstrapTypes {
    globals: SymbolTableId,
    undefined_symbol: SemanticSymbolId,
    arguments_symbol: SemanticSymbolId,
    unknown_symbol: SemanticSymbolId,
    global_this_symbol: SemanticSymbolId,
    undefined_widening_type: TypeId,
    error_type: TypeId,
    any_type: TypeId,
    auto_type: TypeId,
    empty_object_type: TypeId,
    empty_generic_type: TypeId,
}

struct GlobalTypeResolver<'store, 'host, 'arena> {
    store: &'store mut CanonicalTypeMapperStore,
    host: &'host DeclaredTypeHost<'arena>,
    globals: SymbolTableId,
    empty_object_type: TypeId,
    empty_generic_type: TypeId,
    diagnostics: Vec<CanonicalGlobalTypeDiagnostic>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum GlobalObjectNoBasePlan {
    NoPublish,
    Publish(TypeId),
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum GlobalObjectBaseResolutionState {
    Cold,
    NoBases,
    ResolvedBases,
    Invalid,
}

impl GlobalTypeResolver<'_, '_, '_> {
    fn resolve(
        &mut self,
        name: &str,
        arity: usize,
        report_errors: bool,
    ) -> Result<TypeId, CanonicalGlobalTypeInitializationError> {
        if self.store.symbol_table(self.globals).is_none() {
            return Err(CanonicalGlobalTypeInitializationError::InvalidGlobals(
                self.globals,
            ));
        }
        let symbol = {
            let mut resolver_host = self.host.name_resolver_host(self.store)?;
            resolve_global_name(
                self.store.symbol_store(),
                &mut resolver_host,
                name,
                SymbolFlags::TYPE,
                None,
                false,
                false,
            )?
        };
        let Some(symbol) = symbol else {
            if report_errors {
                if matches!(name, "Array" | "RegExp" | "String") {
                    self.push_diagnostic(
                        None,
                        CANNOT_FIND_GLOBAL_TYPE,
                        [name.to_owned(), ES2015_LIBRARY_SUGGESTION.to_owned()],
                    );
                } else {
                    self.push_diagnostic(None, CANNOT_FIND_GLOBAL_TYPE, [name.to_owned()]);
                }
            }
            return Ok(self.fallback(arity));
        };
        let flags = self
            .store
            .symbol(symbol)
            .ok_or(CanonicalGlobalTypeInitializationError::InvalidSymbol(
                symbol,
            ))?
            .flags();
        if flags.intersects(SymbolFlags::CLASS | SymbolFlags::INTERFACE) {
            let declared_type = self.store.get_declared_type_of_symbol(self.host, symbol)?;
            let actual_arity = interface_arity(self.store, declared_type)?;
            if actual_arity == arity {
                return Ok(declared_type);
            }
            if report_errors {
                self.push_diagnostic(
                    global_type_declaration(self.store, self.host, symbol),
                    GLOBAL_TYPE_MUST_HAVE_ARITY,
                    [name.to_owned(), arity.to_string()],
                );
            }
            return Ok(self.fallback(arity));
        }

        if report_errors {
            self.push_diagnostic(
                global_type_declaration(self.store, self.host, symbol),
                GLOBAL_TYPE_MUST_BE_CLASS_OR_INTERFACE,
                [name.to_owned()],
            );
        }
        Ok(self.fallback(arity))
    }

    fn fallback(&self, arity: usize) -> TypeId {
        if arity == 0 {
            self.empty_object_type
        } else {
            self.empty_generic_type
        }
    }

    fn push_diagnostic<const N: usize>(
        &mut self,
        node: Option<NodeRef>,
        code: u32,
        arguments: [String; N],
    ) {
        let message = message_by_code(code).expect("pinned global diagnostic is in the catalog");
        self.diagnostics.push(CanonicalGlobalTypeDiagnostic {
            node,
            diagnostic: Diagnostic::with_arguments(message, arguments),
        });
    }
}

/// Ports the eager global-type portion of pinned `initializeChecker`.
pub(super) fn initialize_global_library_types(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    globals: SymbolTableId,
    strict_bind_call_apply: bool,
) -> Result<CanonicalGlobalTypes, CanonicalGlobalTypeInitializationError> {
    let bootstrap = store
        .intrinsic_bootstrap()
        .map(|bootstrap| BootstrapTypes {
            globals: bootstrap.globals,
            undefined_symbol: bootstrap.undefined_symbol,
            arguments_symbol: bootstrap.arguments_symbol,
            unknown_symbol: bootstrap.unknown_symbol,
            global_this_symbol: bootstrap.global_this_symbol,
            undefined_widening_type: bootstrap.undefined_widening_type,
            error_type: bootstrap.error_type,
            any_type: bootstrap.any_type,
            auto_type: bootstrap.auto_type,
            empty_object_type: bootstrap.empty_object_type,
            empty_generic_type: bootstrap.empty_generic_type,
        })
        .ok_or(CanonicalGlobalTypeInitializationError::MissingBootstrap)?;
    if globals != bootstrap.globals {
        return Err(CanonicalGlobalTypeInitializationError::InvalidGlobals(
            globals,
        ));
    }

    set_resolved_value_type(
        store,
        bootstrap.undefined_symbol,
        bootstrap.undefined_widening_type,
    )?;

    let mut resolver = GlobalTypeResolver {
        store,
        host,
        globals,
        empty_object_type: bootstrap.empty_object_type,
        empty_generic_type: bootstrap.empty_generic_type,
        diagnostics: Vec::new(),
    };
    let arguments_type = resolver.resolve("IArguments", 0, true)?;
    set_resolved_value_type(resolver.store, bootstrap.arguments_symbol, arguments_type)?;
    set_resolved_value_type(
        resolver.store,
        bootstrap.unknown_symbol,
        bootstrap.error_type,
    )?;
    let global_this_value_type = resolver
        .store
        .alloc_plain_object_type(ObjectFlags::ANONYMOUS, Some(bootstrap.global_this_symbol))
        .ok_or(CanonicalGlobalTypeInitializationError::InvalidAnonymousType)?;
    set_resolved_value_type(
        resolver.store,
        bootstrap.global_this_symbol,
        global_this_value_type,
    )?;

    let array_type = resolver.resolve("Array", 1, true)?;
    let object_type = resolver.resolve("Object", 0, true)?;
    let global_object_no_base_plan = preflight_global_object_no_base(
        resolver.store,
        resolver.host,
        resolver.globals,
        object_type,
    )?;
    let function_type = resolver.resolve("Function", 0, true)?;
    let callable_function_type = if strict_bind_call_apply {
        resolver.resolve("CallableFunction", 0, true)?
    } else {
        function_type
    };
    let newable_function_type = if strict_bind_call_apply {
        resolver.resolve("NewableFunction", 0, true)?
    } else {
        function_type
    };
    let string_type = resolver.resolve("String", 0, true)?;
    let number_type = resolver.resolve("Number", 0, true)?;
    let boolean_type = resolver.resolve("Boolean", 0, true)?;
    let regexp_type = resolver.resolve("RegExp", 0, true)?;
    let any_array_type = create_type_from_generic_global_type(
        resolver.store,
        array_type,
        bootstrap.any_type,
        ObjectFlags::NONE,
    )?;
    let mut auto_array_type = create_type_from_generic_global_type(
        resolver.store,
        array_type,
        bootstrap.auto_type,
        ObjectFlags::NONE,
    )?;
    if auto_array_type == bootstrap.empty_object_type {
        auto_array_type = resolver
            .store
            .alloc_plain_object_type(ObjectFlags::ANONYMOUS, None)
            .ok_or(CanonicalGlobalTypeInitializationError::InvalidAnonymousType)?;
        if !resolver.store.set_structured_type_members(
            auto_array_type,
            None,
            None,
            None,
            None,
            None,
        ) {
            return Err(
                CanonicalGlobalTypeInitializationError::InvalidAnonymousTypeMembers(
                    auto_array_type,
                ),
            );
        }
    }
    let mut readonly_array_type = resolver.resolve("ReadonlyArray", 1, false)?;
    if readonly_array_type == bootstrap.empty_generic_type {
        readonly_array_type = array_type;
    }
    let any_readonly_array_type = create_type_from_generic_global_type(
        resolver.store,
        readonly_array_type,
        bootstrap.any_type,
        ObjectFlags::NONE,
    )?;
    let this_type = resolver.resolve("ThisType", 1, false)?;

    commit_global_object_no_base(resolver.store, global_object_no_base_plan)?;

    Ok(CanonicalGlobalTypes {
        arguments_type,
        global_this_value_type,
        array_type,
        object_type,
        function_type,
        callable_function_type,
        newable_function_type,
        string_type,
        number_type,
        boolean_type,
        regexp_type,
        any_array_type,
        auto_array_type,
        readonly_array_type,
        any_readonly_array_type,
        this_type,
        diagnostics: resolver.diagnostics,
    })
}

/// Checks the optional `Iterable` declaration and cache without creating types.
pub(super) fn global_iterable_type_requires_protocol(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
) -> Result<bool, CanonicalGlobalTypeInitializationError> {
    optional_global_type_has_arity(store, host, "Iterable", 3)
}

/// Validates an optional global identity without publishing declaration caches.
pub(super) fn optional_global_type_has_arity(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    name: &str,
    expected_arity: usize,
) -> Result<bool, CanonicalGlobalTypeInitializationError> {
    let bootstrap = store
        .intrinsic_bootstrap()
        .ok_or(CanonicalGlobalTypeInitializationError::MissingBootstrap)?;
    if store.symbol_table(bootstrap.globals).is_none() {
        return Err(CanonicalGlobalTypeInitializationError::InvalidGlobals(
            bootstrap.globals,
        ));
    }
    let symbol = {
        let mut resolver_host = host.name_resolver_host(store)?;
        resolve_global_name(
            store.symbol_store(),
            &mut resolver_host,
            name,
            SymbolFlags::TYPE,
            None,
            false,
            false,
        )?
    };
    let Some(symbol) = symbol else {
        return Ok(false);
    };
    let symbol = store.get_merged_symbol(symbol).ok_or(
        CanonicalGlobalTypeInitializationError::InvalidSymbol(symbol),
    )?;
    let record =
        store
            .symbol(symbol)
            .ok_or(CanonicalGlobalTypeInitializationError::InvalidSymbol(
                symbol,
            ))?;
    let flags = record.flags();
    if !flags.intersects(SymbolFlags::CLASS | SymbolFlags::INTERFACE) {
        return Ok(false);
    }
    if super::declared::malformed_alias_merge(flags) {
        return Err(DeclaredTypeError::Unavailable(
            super::declared::DeclaredTypeUnavailable::AliasMergedWithDeclaredSymbol(symbol),
        )
        .into());
    }
    let arity =
        super::declared::preflight_class_or_interface_reference(store, host, symbol, flags)?;
    let declarations = record
        .declarations()
        .filter(|declarations| !declarations.is_empty())
        .ok_or(CanonicalGlobalTypeInitializationError::InvalidSymbol(
            symbol,
        ))?;
    let mut checked = HashSet::new();
    let mut parameters = HashSet::new();
    let mut has_class = false;
    let mut has_interface = false;
    for declaration in declarations {
        let node = super::declared::preflight_node(store, host, *declaration)?;
        if !host.symbol_matches(store, *declaration, symbol) {
            return Err(CanonicalGlobalTypeInitializationError::InvalidSymbol(
                symbol,
            ));
        }
        let declared_parameters = match &node.data {
            NodeData::ClassDeclaration(data) if node.kind == SyntaxKind::ClassDeclaration => {
                has_class = true;
                data.type_parameters.as_ref()
            }
            NodeData::ClassExpression(data) if node.kind == SyntaxKind::ClassExpression => {
                has_class = true;
                data.type_parameters.as_ref()
            }
            NodeData::InterfaceDeclaration(data)
                if node.kind == SyntaxKind::InterfaceDeclaration =>
            {
                has_interface = true;
                data.type_parameters.as_ref()
            }
            NodeData::TypeAliasDeclaration(_) => {
                return Err(CanonicalGlobalTypeInitializationError::InvalidSymbol(
                    symbol,
                ));
            }
            _ if matches!(
                node.kind,
                SyntaxKind::ClassDeclaration
                    | SyntaxKind::ClassExpression
                    | SyntaxKind::InterfaceDeclaration
            ) =>
            {
                return Err(CanonicalGlobalTypeInitializationError::InvalidSymbol(
                    symbol,
                ));
            }
            _ => continue,
        };
        parameters.extend(super::declared::explicit_type_parameter_symbols(
            store,
            host,
            *declaration,
            declared_parameters,
            &mut checked,
        )?);
    }
    let cached_arity = store
        .declared_type_links(symbol)
        .and_then(|links| links.declared_type)
        .map(|type_| interface_arity(store, type_))
        .transpose()?;
    if flags.contains(SymbolFlags::CLASS) != has_class
        || !has_class && !has_interface
        || arity != parameters.len()
        || cached_arity.is_some_and(|cached| cached != parameters.len())
    {
        return Err(CanonicalGlobalTypeInitializationError::InvalidSymbol(
            symbol,
        ));
    }
    Ok(arity == expected_arity)
}

/// Resolves an optional global through the same kind and arity rules as initialization.
pub(super) fn resolve_optional_global_type(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    name: &str,
    arity: usize,
) -> Result<Option<TypeId>, CanonicalGlobalTypeInitializationError> {
    if !optional_global_type_has_arity(store, host, name, arity)? {
        return Ok(None);
    }
    let bootstrap = store
        .intrinsic_bootstrap()
        .ok_or(CanonicalGlobalTypeInitializationError::MissingBootstrap)?;
    let mut resolver = GlobalTypeResolver {
        globals: bootstrap.globals,
        empty_object_type: bootstrap.empty_object_type,
        empty_generic_type: bootstrap.empty_generic_type,
        store,
        host,
        diagnostics: Vec::new(),
    };
    resolver.resolve(name, arity, false).map(Some)
}

/// Uses the ordinary global resolver and retains proof for a lazy required demand.
pub(super) fn resolve_required_global_type(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    name: &str,
    arity: usize,
) -> Result<ResolvedGlobalType, CanonicalGlobalTypeInitializationError> {
    let before = required_global_type_proof(store, host, name, arity)?;
    let bootstrap = store
        .intrinsic_bootstrap()
        .ok_or(CanonicalGlobalTypeInitializationError::MissingBootstrap)?;
    let mut resolver = GlobalTypeResolver {
        globals: bootstrap.globals,
        empty_object_type: bootstrap.empty_object_type,
        empty_generic_type: bootstrap.empty_generic_type,
        store,
        host,
        diagnostics: Vec::new(),
    };
    let type_ = resolver.resolve(name, arity, true)?;
    let mut diagnostics = resolver.diagnostics;
    let proof = required_global_type_proof(store, host, name, arity)?;
    if before.globals != proof.globals
        || before.symbol.as_ref().map(|symbol| symbol.symbol)
            != proof.symbol.as_ref().map(|symbol| symbol.symbol)
    {
        return Err(CanonicalGlobalTypeInitializationError::InvalidGlobals(
            proof.globals,
        ));
    }
    for diagnostic in &mut diagnostics {
        let Some(declaration) = diagnostic.node else {
            continue;
        };
        let symbol = proof
            .symbol
            .as_ref()
            .ok_or(CanonicalGlobalTypeInitializationError::InvalidType(type_))?
            .symbol;
        let invalid = || CanonicalGlobalTypeInitializationError::InvalidSymbol(symbol);
        let record = host.node(declaration).ok_or_else(invalid)?;
        let name = match &record.data {
            NodeData::ClassDeclaration(class) => class.name,
            NodeData::InterfaceDeclaration(interface) => Some(interface.name),
            NodeData::TypeAliasDeclaration(alias) => Some(alias.name),
            NodeData::EnumDeclaration(enumeration) => Some(enumeration.name),
            _ => None,
        }
        .ok_or_else(invalid)?;
        let name = NodeRef::new(declaration.arena, declaration.file, name);
        if !host.node(name).is_some_and(|name| {
            name.parent == Some(declaration.node)
                && matches!(&name.data, NodeData::Identifier(identifier) if identifier.text == proof.name)
        }) {
            return Err(invalid());
        }
        diagnostic.node = Some(name);
    }
    Ok(ResolvedGlobalType {
        type_,
        diagnostics,
        proof,
    })
}

fn required_global_type_proof(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    name: &str,
    arity: usize,
) -> Result<RequiredGlobalTypeProof, CanonicalGlobalTypeInitializationError> {
    let globals = store
        .intrinsic_bootstrap()
        .ok_or(CanonicalGlobalTypeInitializationError::MissingBootstrap)?
        .globals;
    if store.symbol_table(globals).is_none() {
        return Err(CanonicalGlobalTypeInitializationError::InvalidGlobals(
            globals,
        ));
    }
    let symbol = {
        let mut resolver_host = host.name_resolver_host(store)?;
        resolve_global_name(
            store.symbol_store(),
            &mut resolver_host,
            name,
            SymbolFlags::TYPE,
            None,
            false,
            false,
        )?
    };
    let symbol = symbol
        .map(|symbol| {
            let invalid = || CanonicalGlobalTypeInitializationError::InvalidSymbol(symbol);
            let record = store.symbol(symbol).ok_or_else(invalid)?;
            if store.get_merged_symbol(symbol) != Some(symbol)
                || record.name().as_utf8() != Some(name)
                || !store.source_merged_symbol_declarations_match(symbol)
            {
                return Err(invalid());
            }
            let declarations = record
                .declarations()
                .filter(|declarations| !declarations.is_empty())
                .ok_or_else(invalid)?;
            if declarations.iter().any(|declaration| {
                host.node(*declaration).is_none()
                    || !host.symbol_matches(store, *declaration, symbol)
            }) {
                return Err(invalid());
            }
            for declaration in declarations {
                validate_required_global_declaration(store, host, *declaration, symbol, name)?;
            }
            let declared_type = if record
                .flags()
                .intersects(SymbolFlags::CLASS | SymbolFlags::INTERFACE)
            {
                optional_global_type_has_arity(store, host, name, arity)?;
                let declared = store
                    .declared_type_links(symbol)
                    .and_then(|links| links.declared_type);
                if let Some(type_) = declared
                    && store
                        .type_payload(type_)
                        .and_then(super::type_records::TypeRecord::symbol)
                        != Some(symbol)
                {
                    return Err(CanonicalGlobalTypeInitializationError::InvalidType(type_));
                }
                declared
            } else {
                None
            };
            Ok(RequiredGlobalSymbolProof {
                symbol,
                flags: record.flags(),
                declarations: declarations.to_vec(),
                declared_type,
            })
        })
        .transpose()?;
    Ok(RequiredGlobalTypeProof {
        globals,
        name: name.to_owned(),
        arity,
        symbol,
    })
}

fn validate_required_global_declaration(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    declaration: NodeRef,
    symbol: SemanticSymbolId,
    expected_name: &str,
) -> Result<(), CanonicalGlobalTypeInitializationError> {
    let invalid = || CanonicalGlobalTypeInitializationError::InvalidSymbol(symbol);
    let record = host.node(declaration).ok_or_else(invalid)?;
    let source_parent = record.parent.map_or(SourceNodeParent::Root, |parent| {
        SourceNodeParent::Parent(NodeRef::new(declaration.arena, declaration.file, parent))
    });
    if store.source_node_kind(declaration) != Some(record.kind)
        || store.source_node_start(declaration) != Some(record.range.start.get())
        || store.source_node_parent(declaration) != Some(source_parent)
        || !record.data.matches_syntax_kind(record.kind)
    {
        return Err(invalid());
    }
    let name = match &record.data {
        NodeData::ClassDeclaration(class) => class.name,
        NodeData::ClassExpression(class) => class.name,
        NodeData::InterfaceDeclaration(interface) => Some(interface.name),
        NodeData::TypeAliasDeclaration(alias) => Some(alias.name),
        NodeData::EnumDeclaration(enumeration) => Some(enumeration.name),
        NodeData::ModuleDeclaration(module) => Some(module.name),
        NodeData::FunctionDeclaration(function) => function.name,
        NodeData::VariableDeclaration(variable) => Some(variable.name),
        NodeData::BindingElement(binding) => binding.name,
        _ => None,
    }
    .ok_or_else(invalid)?;
    let name = NodeRef::new(declaration.arena, declaration.file, name);
    if store.source_identifier_text(name) != Some(expected_name)
        || store.source_node_parent(name) != Some(SourceNodeParent::Parent(declaration))
    {
        return Err(invalid());
    }
    let mut children = Vec::new();
    record.for_each_child(|child| {
        children.push(NodeRef::new(declaration.arena, declaration.file, child));
    });
    children.sort_unstable();
    if store.source_direct_children(declaration).as_deref() != Some(children.as_slice()) {
        return Err(invalid());
    }
    for child in children {
        let child_record = host.node(child).ok_or_else(invalid)?;
        if store.source_node_kind(child) != Some(child_record.kind)
            || store.source_node_start(child) != Some(child_record.range.start.get())
            || child_record.parent != Some(declaration.node)
            || !child_record.data.matches_syntax_kind(child_record.kind)
            || store.source_identifier_text(child).is_some_and(|expected| {
                !matches!(&child_record.data,
                    NodeData::Identifier(identifier) if identifier.text == expected)
            })
        {
            return Err(invalid());
        }
    }
    Ok(())
}

/// Proves the pinned no-heritage `Object` fast path without resolving any
/// heritage expressions. The proof is deliberately restricted to a real,
/// non-generic merged interface; value-side `var Object` declarations do not
/// contribute bases and are ignored.
fn preflight_global_object_no_base(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    globals: SymbolTableId,
    object_type: TypeId,
) -> Result<GlobalObjectNoBasePlan, CanonicalGlobalTypeInitializationError> {
    let object_record = store.type_payload(object_type).ok_or(
        CanonicalGlobalTypeInitializationError::InvalidType(object_type),
    )?;
    let TypeData::Interface(interface) = object_record.data() else {
        // Missing, wrong-kind, and wrong-arity globals use the pinned empty
        // object fallback and cannot establish a fact about global Object.
        return Ok(GlobalObjectNoBasePlan::NoPublish);
    };
    let object_origin = object_record.object_flags() & ObjectFlags::CLASS_OR_INTERFACE;
    let symbol = object_record.symbol().ok_or(
        CanonicalGlobalTypeInitializationError::InvalidGlobalObjectBaseResolution(object_type),
    )?;
    let raw_global = store
        .symbol_table(globals)
        .ok_or(CanonicalGlobalTypeInitializationError::InvalidGlobals(
            globals,
        ))?
        .get_source("Object")
        .ok_or(
            CanonicalGlobalTypeInitializationError::InvalidGlobalObjectBaseResolution(object_type),
        )?;
    let global_symbol = store.get_merged_symbol(raw_global).ok_or(
        CanonicalGlobalTypeInitializationError::InvalidSymbol(raw_global),
    )?;
    if symbol != global_symbol {
        return Err(
            CanonicalGlobalTypeInitializationError::InvalidGlobalObjectBaseResolution(object_type),
        );
    }
    let symbol_record =
        store
            .symbol(symbol)
            .ok_or(CanonicalGlobalTypeInitializationError::InvalidSymbol(
                symbol,
            ))?;
    let has_exact_interface_type_side =
        (symbol_record.flags() & SymbolFlags::TYPE) == SymbolFlags::INTERFACE;
    let declarations = symbol_record.declarations().ok_or(
        CanonicalGlobalTypeInitializationError::InvalidGlobalObjectBaseResolution(object_type),
    )?;
    if declarations.is_empty() {
        return Err(
            CanonicalGlobalTypeInitializationError::InvalidGlobalObjectBaseResolution(object_type),
        );
    }

    let mut saw_interface = false;
    let mut saw_interface_heritage = false;
    let mut declarations_prove_no_bases = true;
    for declaration in declarations {
        let node = host.node(*declaration).ok_or(
            CanonicalGlobalTypeInitializationError::InvalidGlobalObjectDeclaration(*declaration),
        )?;
        if !host.symbol_matches(store, *declaration, symbol) {
            return Err(
                CanonicalGlobalTypeInitializationError::InvalidGlobalObjectDeclaration(
                    *declaration,
                ),
            );
        }
        match (node.kind, &node.data) {
            (SyntaxKind::InterfaceDeclaration, NodeData::InterfaceDeclaration(interface)) => {
                saw_interface = true;
                let has_heritage = interface.heritage_clauses.is_some();
                if has_heritage {
                    saw_interface_heritage = true;
                }
                if interface.type_parameters.is_some() || has_heritage {
                    declarations_prove_no_bases = false;
                }
            }
            (SyntaxKind::VariableDeclaration, NodeData::VariableDeclaration(_)) => {
                // `declare var Object` is the value-side constructor and does
                // not participate in interface base resolution.
            }
            (SyntaxKind::InterfaceDeclaration | SyntaxKind::VariableDeclaration, _) => {
                return Err(
                    CanonicalGlobalTypeInitializationError::InvalidGlobalObjectDeclaration(
                        *declaration,
                    ),
                );
            }
            _ => declarations_prove_no_bases = false,
        }
    }
    if has_exact_interface_type_side && !saw_interface {
        return Err(
            CanonicalGlobalTypeInitializationError::InvalidGlobalObjectBaseResolution(object_type),
        );
    }
    if !has_exact_interface_type_side || !declarations_prove_no_bases {
        // A class is both a type and a value, but it is not evidence for the
        // interface-only no-heritage result. Other valid unsupported merged
        // forms are equally conservative.
        if object_origin == ObjectFlags::CLASS {
            return Ok(GlobalObjectNoBasePlan::NoPublish);
        }
        if object_origin != ObjectFlags::INTERFACE {
            return Err(
                CanonicalGlobalTypeInitializationError::InvalidGlobalObjectBaseResolution(
                    object_type,
                ),
            );
        }
        return match global_object_base_resolution_state(interface) {
            GlobalObjectBaseResolutionState::Cold => Ok(GlobalObjectNoBasePlan::NoPublish),
            GlobalObjectBaseResolutionState::ResolvedBases if saw_interface_heritage => {
                Ok(GlobalObjectNoBasePlan::NoPublish)
            }
            GlobalObjectBaseResolutionState::NoBases
            | GlobalObjectBaseResolutionState::ResolvedBases
            | GlobalObjectBaseResolutionState::Invalid => Err(
                CanonicalGlobalTypeInitializationError::InvalidGlobalObjectBaseResolution(
                    object_type,
                ),
            ),
        };
    }
    if object_origin != ObjectFlags::INTERFACE {
        return Err(
            CanonicalGlobalTypeInitializationError::InvalidGlobalObjectBaseResolution(object_type),
        );
    }

    match global_object_base_resolution_state(interface) {
        GlobalObjectBaseResolutionState::NoBases => Ok(GlobalObjectNoBasePlan::NoPublish),
        GlobalObjectBaseResolutionState::Cold => Ok(GlobalObjectNoBasePlan::Publish(object_type)),
        GlobalObjectBaseResolutionState::ResolvedBases
        | GlobalObjectBaseResolutionState::Invalid => Err(
            CanonicalGlobalTypeInitializationError::InvalidGlobalObjectBaseResolution(object_type),
        ),
    }
}

/// Publishes only after all other fallible global-library initialization has
/// completed, so a later failure cannot leave behind this newly resolved fact.
fn commit_global_object_no_base(
    store: &mut CanonicalTypeMapperStore,
    plan: GlobalObjectNoBasePlan,
) -> Result<(), CanonicalGlobalTypeInitializationError> {
    let GlobalObjectNoBasePlan::Publish(object_type) = plan else {
        return Ok(());
    };
    let record = store.type_payload(object_type).ok_or(
        CanonicalGlobalTypeInitializationError::InvalidType(object_type),
    )?;
    let TypeData::Interface(interface) = record.data() else {
        return Err(
            CanonicalGlobalTypeInitializationError::InvalidGlobalObjectBaseResolution(object_type),
        );
    };
    match global_object_base_resolution_state(interface) {
        // An already-warm cache is valid and must retain its member resolution
        // state.
        GlobalObjectBaseResolutionState::NoBases => Ok(()),
        GlobalObjectBaseResolutionState::Cold
            if store.publish_interface_no_base_resolution(object_type) =>
        {
            Ok(())
        }
        GlobalObjectBaseResolutionState::Cold
        | GlobalObjectBaseResolutionState::ResolvedBases
        | GlobalObjectBaseResolutionState::Invalid => Err(
            CanonicalGlobalTypeInitializationError::InvalidGlobalObjectBaseResolution(object_type),
        ),
    }
}

fn global_object_base_resolution_state(
    interface: &super::type_records::InterfaceTypeData,
) -> GlobalObjectBaseResolutionState {
    match (
        interface.base_types_resolved,
        interface.resolved_base_constructor_type,
        interface.resolved_base_types.as_deref(),
    ) {
        (false, None, None) => GlobalObjectBaseResolutionState::Cold,
        (true, None, None) => GlobalObjectBaseResolutionState::NoBases,
        (true, None, Some(bases)) if !bases.is_empty() => {
            GlobalObjectBaseResolutionState::ResolvedBases
        }
        _ => GlobalObjectBaseResolutionState::Invalid,
    }
}

fn interface_arity(
    store: &CanonicalTypeMapperStore,
    type_id: TypeId,
) -> Result<usize, CanonicalGlobalTypeInitializationError> {
    let record = store
        .type_payload(type_id)
        .ok_or(CanonicalGlobalTypeInitializationError::InvalidType(type_id))?;
    let TypeData::Interface(interface) = record.data() else {
        return Err(CanonicalGlobalTypeInitializationError::InvalidType(type_id));
    };
    Ok(interface
        .all_type_parameters
        .as_ref()
        .map_or(0, |parameters| parameters.len() - 1))
}

fn global_type_declaration(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    symbol: SemanticSymbolId,
) -> Option<NodeRef> {
    store
        .symbol(symbol)?
        .declarations()?
        .iter()
        .copied()
        .find(|declaration| {
            host.node(*declaration).is_some_and(|node| {
                matches!(
                    node.kind,
                    SyntaxKind::ClassDeclaration
                        | SyntaxKind::InterfaceDeclaration
                        | SyntaxKind::EnumDeclaration
                        | SyntaxKind::TypeAliasDeclaration
                )
            })
        })
}

fn set_resolved_value_type(
    store: &mut CanonicalTypeMapperStore,
    symbol: SemanticSymbolId,
    resolved_type: TypeId,
) -> Result<(), CanonicalGlobalTypeInitializationError> {
    let mut links = store
        .value_symbol_links(symbol)
        .cloned()
        .unwrap_or_else(ValueSymbolLinks::default);
    links.resolved_type = Some(resolved_type);
    if store.set_value_symbol_links(symbol, links) {
        Ok(())
    } else {
        Err(CanonicalGlobalTypeInitializationError::InvalidValueSymbolLinks(symbol))
    }
}

/// Validates one authoritative generic-global target and its complete
/// target-local instantiation cache. The returned type is the pinned missing
/// or malformed-library fallback; `None` means the target is an initialized
/// one-parameter class or interface.
///
/// Validation is intentionally read-only so callers can reject a poisoned
/// retained target before resolving an argument node or allocating a new
/// reference identity.
#[allow(clippy::too_many_lines)] // One complete target-and-cache invariant matrix.
pub(super) fn preflight_generic_global_type_target(
    store: &CanonicalTypeMapperStore,
    target: TypeId,
) -> Result<Option<TypeId>, CanonicalGlobalTypeInitializationError> {
    let bootstrap = store
        .intrinsic_bootstrap()
        .ok_or(CanonicalGlobalTypeInitializationError::MissingBootstrap)?;
    if target == bootstrap.empty_generic_type {
        return Ok(Some(bootstrap.empty_object_type));
    }

    let target_record = store
        .type_payload(target)
        .ok_or(CanonicalGlobalTypeInitializationError::InvalidType(target))?;
    let TypeData::Interface(interface) = target_record.data() else {
        return Err(CanonicalGlobalTypeInitializationError::InvalidGenericTarget(target));
    };
    let Some(type_arguments) = interface.reference.resolved_type_arguments.as_deref() else {
        return Err(CanonicalGlobalTypeInitializationError::InvalidGenericTarget(target));
    };
    let Some(all_type_parameters) = interface.all_type_parameters.as_deref() else {
        return Err(CanonicalGlobalTypeInitializationError::InvalidGenericTarget(target));
    };
    let TypeCacheState::Allocated(instantiations) = &interface.reference.object.instantiations
    else {
        return Err(CanonicalGlobalTypeInitializationError::InvalidGenericTarget(target));
    };
    let target_symbol = target_record
        .symbol()
        .ok_or(CanonicalGlobalTypeInitializationError::InvalidGenericTarget(target))?;
    let target_origin = target_record.object_flags() & ObjectFlags::CLASS_OR_INTERFACE;
    let target_allowed_flags = ObjectFlags::CLASS_OR_INTERFACE
        | ObjectFlags::REFERENCE
        | ObjectFlags::PROPAGATING_FLAGS
        | ObjectFlags::COULD_CONTAIN_TYPE_VARIABLES_COMPUTED
        | ObjectFlags::COULD_CONTAIN_TYPE_VARIABLES
        | ObjectFlags::MEMBERS_RESOLVED
        | ObjectFlags::CONTAINS_SPREAD
        | ObjectFlags::OBJECT_REST_TYPE
        | ObjectFlags::IDENTICAL_BASE_TYPE_CALCULATED
        | ObjectFlags::IDENTICAL_BASE_TYPE_EXISTS
        | ObjectFlags::UNRESOLVED_MEMBERS;
    if target_record.flags() != TypeFlags::OBJECT
        || !matches!(target_origin, ObjectFlags::CLASS | ObjectFlags::INTERFACE)
        || !target_record
            .object_flags()
            .contains(ObjectFlags::REFERENCE)
        || !(target_record.object_flags() & !target_allowed_flags).is_empty()
        || type_arguments.len() != 1
        || all_type_parameters.len() != 2
        || all_type_parameters.first() != type_arguments.first()
        || all_type_parameters.last().copied() != interface.this_type
        || interface.outer_type_parameter_count != 0
        || interface.reference.object.target != Some(target)
        || interface.reference.object.mapper.is_some()
        || interface.reference.node.is_some()
        || target_record.alias().is_some()
        || cached_ordinary_type_parameter_owner(store, type_arguments[0]).is_none()
    {
        return Err(CanonicalGlobalTypeInitializationError::InvalidGenericTarget(target));
    }
    let this_type = interface
        .this_type
        .expect("the validated all-type-parameter tail is the this type");
    let Some(this_record) = store.type_payload(this_type) else {
        return Err(CanonicalGlobalTypeInitializationError::InvalidGenericTarget(target));
    };
    let this_flags = this_record.object_flags();
    let resolved_type_parameter_flags = ObjectFlags::COULD_CONTAIN_TYPE_VARIABLES_COMPUTED
        | ObjectFlags::COULD_CONTAIN_TYPE_VARIABLES;
    if this_record.flags() != TypeFlags::TYPE_PARAMETER
        || !(this_flags == ObjectFlags::NONE || this_flags == resolved_type_parameter_flags)
        || this_record.symbol() != Some(target_symbol)
        || this_record.alias().is_some()
        || !matches!(
            this_record.data(),
            TypeData::TypeParameter(data)
                if data.is_this_type
                    && data.constraint == Some(target)
                    && data.target.is_none()
                    && data.mapper.is_none()
        )
    {
        return Err(CanonicalGlobalTypeInitializationError::InvalidGenericTarget(target));
    }

    let identity_key = type_list_key(type_arguments);
    if instantiations.get(&identity_key) != Some(&target) {
        return Err(CanonicalGlobalTypeInitializationError::InvalidInstantiationCache(target));
    }
    for (key, instantiation) in instantiations {
        if *instantiation == target {
            if *key != identity_key {
                return Err(
                    CanonicalGlobalTypeInitializationError::InvalidInstantiationCache(target),
                );
            }
            continue;
        }
        let record = store
            .type_payload(*instantiation)
            .ok_or(CanonicalGlobalTypeInitializationError::InvalidInstantiationCache(target))?;
        let TypeData::TypeReference(reference) = record.data() else {
            return Err(CanonicalGlobalTypeInitializationError::InvalidInstantiationCache(target));
        };
        let Some(arguments) = reference.resolved_type_arguments.as_deref() else {
            return Err(CanonicalGlobalTypeInitializationError::InvalidInstantiationCache(target));
        };
        let propagating_flags = arguments.iter().fold(ObjectFlags::NONE, |flags, argument| {
            flags
                | store
                    .type_payload(*argument)
                    .map_or(ObjectFlags::NONE, |record| {
                        record.object_flags() & ObjectFlags::PROPAGATING_FLAGS
                    })
        });
        let allowed_flags = ObjectFlags::REFERENCE
            | ObjectFlags::FROM_TYPE_NODE
            | ObjectFlags::PROPAGATING_FLAGS
            | ObjectFlags::COULD_CONTAIN_TYPE_VARIABLES_COMPUTED
            | ObjectFlags::COULD_CONTAIN_TYPE_VARIABLES
            | ObjectFlags::MEMBERS_RESOLVED
            | ObjectFlags::CONTAINS_SPREAD
            | ObjectFlags::OBJECT_REST_TYPE
            | ObjectFlags::IDENTICAL_BASE_TYPE_CALCULATED
            | ObjectFlags::IDENTICAL_BASE_TYPE_EXISTS
            | ObjectFlags::UNRESOLVED_MEMBERS;
        if arguments.len() != 1
            || arguments
                .iter()
                .any(|argument| store.type_payload(*argument).is_none())
            || *key != type_list_key(arguments)
            || reference.object.target != Some(target)
            || reference.object.mapper.is_some()
            || reference.object.instantiations != TypeCacheState::Unallocated
            || reference.node.is_some()
            || record.alias().is_some()
            || record.symbol() != target_record.symbol()
            || !record
                .object_flags()
                .contains(ObjectFlags::REFERENCE | propagating_flags)
            || !(record.object_flags() & !allowed_flags).is_empty()
        {
            return Err(CanonicalGlobalTypeInitializationError::InvalidInstantiationCache(target));
        }
    }
    Ok(None)
}

/// Validates the authoritative generic target shell used by one relation
/// lookup without scanning unrelated target-local instantiations.
///
/// The relation path separately records and validates each exact `(target,
/// key)` entry it consumes. Shell replacement invalidates the broad target
/// observation, while ordinary target-cache insertion invalidates only an
/// observed exact key (or an explicitly map-wide reader).
pub(super) fn preflight_relation_generic_global_type_target(
    store: &CanonicalTypeMapperStore,
    target: TypeId,
) -> Result<Option<TypeId>, CanonicalGlobalTypeInitializationError> {
    let bootstrap = store
        .intrinsic_bootstrap()
        .ok_or(CanonicalGlobalTypeInitializationError::MissingBootstrap)?;
    if target == bootstrap.empty_generic_type {
        return Ok(Some(bootstrap.empty_object_type));
    }

    let target_record = store
        .type_payload(target)
        .ok_or(CanonicalGlobalTypeInitializationError::InvalidType(target))?;
    let TypeData::Interface(interface) = target_record.data() else {
        return Err(CanonicalGlobalTypeInitializationError::InvalidGenericTarget(target));
    };
    let Some(type_arguments) = interface.reference.resolved_type_arguments.as_deref() else {
        return Err(CanonicalGlobalTypeInitializationError::InvalidGenericTarget(target));
    };
    let Some(all_type_parameters) = interface.all_type_parameters.as_deref() else {
        return Err(CanonicalGlobalTypeInitializationError::InvalidGenericTarget(target));
    };
    let TypeCacheState::Allocated(_) = &interface.reference.object.instantiations else {
        return Err(CanonicalGlobalTypeInitializationError::InvalidGenericTarget(target));
    };
    let target_symbol = target_record
        .symbol()
        .ok_or(CanonicalGlobalTypeInitializationError::InvalidGenericTarget(target))?;
    let target_origin = target_record.object_flags() & ObjectFlags::CLASS_OR_INTERFACE;
    let target_allowed_flags = ObjectFlags::CLASS_OR_INTERFACE
        | ObjectFlags::REFERENCE
        | ObjectFlags::PROPAGATING_FLAGS
        | ObjectFlags::COULD_CONTAIN_TYPE_VARIABLES_COMPUTED
        | ObjectFlags::COULD_CONTAIN_TYPE_VARIABLES
        | ObjectFlags::MEMBERS_RESOLVED
        | ObjectFlags::CONTAINS_SPREAD
        | ObjectFlags::OBJECT_REST_TYPE
        | ObjectFlags::IDENTICAL_BASE_TYPE_CALCULATED
        | ObjectFlags::IDENTICAL_BASE_TYPE_EXISTS
        | ObjectFlags::UNRESOLVED_MEMBERS;
    if target_record.flags() != TypeFlags::OBJECT
        || !matches!(target_origin, ObjectFlags::CLASS | ObjectFlags::INTERFACE)
        || !target_record
            .object_flags()
            .contains(ObjectFlags::REFERENCE)
        || !(target_record.object_flags() & !target_allowed_flags).is_empty()
        || type_arguments.len() != 1
        || all_type_parameters.len() != 2
        || all_type_parameters.first() != type_arguments.first()
        || all_type_parameters.last().copied() != interface.this_type
        || interface.outer_type_parameter_count != 0
        || interface.reference.object.target != Some(target)
        || interface.reference.object.mapper.is_some()
        || interface.reference.node.is_some()
        || target_record.alias().is_some()
        || cached_ordinary_type_parameter_owner(store, type_arguments[0]).is_none()
    {
        return Err(CanonicalGlobalTypeInitializationError::InvalidGenericTarget(target));
    }
    let this_type = interface
        .this_type
        .expect("the validated all-type-parameter tail is the this type");
    let Some(this_record) = store.type_payload(this_type) else {
        return Err(CanonicalGlobalTypeInitializationError::InvalidGenericTarget(target));
    };
    let this_flags = this_record.object_flags();
    let resolved_type_parameter_flags = ObjectFlags::COULD_CONTAIN_TYPE_VARIABLES_COMPUTED
        | ObjectFlags::COULD_CONTAIN_TYPE_VARIABLES;
    if this_record.flags() != TypeFlags::TYPE_PARAMETER
        || !(this_flags == ObjectFlags::NONE || this_flags == resolved_type_parameter_flags)
        || this_record.symbol() != Some(target_symbol)
        || this_record.alias().is_some()
        || !matches!(
            this_record.data(),
            TypeData::TypeParameter(data)
                if data.is_this_type
                    && data.constraint == Some(target)
                    && data.target.is_none()
                    && data.mapper.is_none()
        )
        || store.relation_object_instantiation(target, type_list_key(type_arguments))
            != Some(target)
    {
        return Err(CanonicalGlobalTypeInitializationError::InvalidGenericTarget(target));
    }
    Ok(None)
}

/// Returns whether `instantiation` is the canonical result owned by `target`.
/// The malformed-library fallback is canonical only for the exact intrinsic
/// empty-object identity; initialized targets accept only values present in
/// their validated target-local cache.
pub(super) fn validate_generic_global_type_instantiation(
    store: &CanonicalTypeMapperStore,
    target: TypeId,
    instantiation: TypeId,
) -> Result<(), CanonicalGlobalTypeInitializationError> {
    if let Some(fallback) = preflight_generic_global_type_target(store, target)? {
        return if instantiation == fallback {
            Ok(())
        } else {
            Err(CanonicalGlobalTypeInitializationError::InvalidInstantiationCache(target))
        };
    }
    let TypeData::Interface(interface) = store
        .type_payload(target)
        .expect("the generic-global target was preflighted")
        .data()
    else {
        unreachable!("the generic-global target changed after preflight")
    };
    let TypeCacheState::Allocated(instantiations) = &interface.reference.object.instantiations
    else {
        unreachable!("the generic-global cache changed after preflight")
    };
    if instantiations
        .values()
        .any(|cached| *cached == instantiation)
    {
        Ok(())
    } else {
        Err(CanonicalGlobalTypeInitializationError::InvalidInstantiationCache(target))
    }
}

/// Creates or reuses the pinned one-argument reference for an authoritative
/// generic global. Identity is owned solely by the target's instantiation map
/// and keyed by the exact ordered type-argument list. `creation_flags` are
/// applied only when this call wins the first allocation for that key.
pub(super) fn create_type_from_generic_global_type(
    store: &mut CanonicalTypeMapperStore,
    target: TypeId,
    type_argument: TypeId,
    creation_flags: ObjectFlags,
) -> Result<TypeId, CanonicalGlobalTypeInitializationError> {
    if let Some(fallback) = preflight_generic_global_type_target(store, target)? {
        return Ok(fallback);
    }
    let key = type_list_key(&[type_argument]);
    let target_record = store
        .type_payload(target)
        .ok_or(CanonicalGlobalTypeInitializationError::InvalidType(target))?;
    let TypeData::Interface(interface) = target_record.data() else {
        return Err(CanonicalGlobalTypeInitializationError::InvalidGenericTarget(target));
    };
    let TypeCacheState::Allocated(instantiations) = &interface.reference.object.instantiations
    else {
        unreachable!("the generic-global target changed after preflight")
    };
    if let Some(existing) = instantiations.get(&key) {
        return Ok(*existing);
    }
    if !(creation_flags & !ObjectFlags::FROM_TYPE_NODE).is_empty() {
        return Err(CanonicalGlobalTypeInitializationError::InvalidTypeReference(target));
    }
    let symbol = target_record.symbol();
    let argument_flags = store
        .type_payload(type_argument)
        .ok_or(CanonicalGlobalTypeInitializationError::InvalidType(
            type_argument,
        ))?
        .object_flags()
        & ObjectFlags::PROPAGATING_FLAGS;
    if !store.try_reserve_object_instantiations(target, 1) {
        return Err(CanonicalGlobalTypeInitializationError::InvalidInstantiationCache(target));
    }
    let reference = store
        .alloc_type_reference(argument_flags | creation_flags, symbol)
        .ok_or(CanonicalGlobalTypeInitializationError::InvalidTypeReference(target))?;
    assert!(store.set_object_target_and_mapper(reference, Some(target), None));
    assert!(store.set_type_reference_resolution(reference, None, Some(vec![type_argument]),));
    let canonical = store
        .insert_object_instantiation(target, key, reference)
        .expect("the preflighted generic-global target accepts its reference");
    assert_eq!(canonical, reference);
    Ok(canonical)
}
