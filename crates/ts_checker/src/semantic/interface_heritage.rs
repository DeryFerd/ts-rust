//! Exact syntax and symbol plan for the first interface-heritage slice.
//!
//! This module admits ordered nongeneric interface bases, including merged
//! declarations and authenticated namespace exports. Generic heritage keeps
//! its one-or-two-base limit, forwarded generic type
//! parameters, concrete generic arguments, trailing defaults, bounded base
//! chains, and
//! merged default-library DOM interface/value identities.
//! React namespace bases also retain bounded nested forwarded interface
//! arguments and authenticated deferred generic constraints.
//! Authenticated React node arrays retain their default-library `Array<T>`
//! heritage without expanding recursive members.
//! Alias bases use the normal type-reference query before member resolution.
//! The exact `Record<string, any>` path retains its existing authentication.
//! Every base is resolved before publication so member construction retains
//! its declaration identity and, for mapped bases, its source type arguments.

use std::collections::HashSet;

use ts_ast::{NodeData, NodeList, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalNameResolutionError, CanonicalNameResolver, CanonicalNameResolverHost,
    CanonicalNameResolverOptions, CanonicalResolutionLocation, CheckFlags, EscapedName,
    EscapedNameRef, InternalSymbolName, SemanticSymbolId, SymbolFlags, SymbolStore, SymbolTableId,
    canonical_has_syntactic_modifier,
};

use super::{
    CanonicalGlobalTypes, CanonicalTypeMapperStore, DeclaredTypeHost, TypeData, TypeId,
    array_types::CanonicalArrayTargets,
    conditional_types::{
        ConditionalBranchSource, ConditionalQueryKey, ConditionalSourceQueryRequest,
        ConditionalSourceResultProof, conditional_query_alias_with_array_targets,
        conditional_source_query_request, validate_source_conditional_result,
    },
    declared::{
        DeclaredTypeError, DeclaredTypeUnavailable, explicit_type_parameter_symbols, preflight_node,
    },
    global_types::preflight_generic_global_type_target,
    mapped_types::plan_mapped_type_declaration,
    name_resolution::ProductionNameResolverHost,
    object_aliases::{
        property_object_alias_identity_source_header, property_object_alias_source_header,
    },
    store::{PlainInterfaceHeritageFacts, SourceNodeParent},
    type_nodes::TypeNodeUnavailable,
    types::{ObjectFlags, TypeFlags},
};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum DirectInterfaceBaseKind {
    Interface,
    DefaultLibraryInterface,
    DefaultLibraryArray,
    RecordMappedAlias,
    NongenericTypeLiteralAlias,
    InstantiatedTypeAlias,
}

impl DirectInterfaceBaseKind {
    pub(super) const fn is_instantiated_alias(self) -> bool {
        matches!(self, Self::InstantiatedTypeAlias | Self::RecordMappedAlias)
    }
}

/// Source bindings only. A header does not complete a base or its members.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct SourceInterfaceHeritageHeader {
    owner_symbol: SemanticSymbolId,
    owner_declarations: Vec<NodeRef>,
    bases: Vec<SourceInterfaceHeritageBase>,
}

impl SourceInterfaceHeritageHeader {
    pub(super) const fn owner_symbol(&self) -> SemanticSymbolId {
        self.owner_symbol
    }

    pub(super) fn owner_declarations(&self) -> &[NodeRef] {
        &self.owner_declarations
    }

    pub(super) fn bases(&self) -> &[SourceInterfaceHeritageBase] {
        &self.bases
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct SourceInterfaceHeritageBase {
    declaration: NodeRef,
    clause: NodeRef,
    node: NodeRef,
    expression: NodeRef,
    symbol: SemanticSymbolId,
    alias: Option<SourceInterfaceAliasBaseRequest>,
    resolution: SourceInterfaceHeritageResolution,
    import: Option<super::source_imports::SourceInterfaceHeritageImport>,
}

impl SourceInterfaceHeritageBase {
    pub(super) const fn declaration(&self) -> NodeRef {
        self.declaration
    }

    pub(super) const fn clause(&self) -> NodeRef {
        self.clause
    }

    pub(super) const fn node(&self) -> NodeRef {
        self.node
    }

    pub(super) const fn expression(&self) -> NodeRef {
        self.expression
    }

    pub(super) const fn symbol(&self) -> SemanticSymbolId {
        self.symbol
    }

    pub(super) const fn alias(&self) -> Option<&SourceInterfaceAliasBaseRequest> {
        self.alias.as_ref()
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct SourceInterfaceAliasBaseRequest {
    symbol: SemanticSymbolId,
    declaration: NodeRef,
    rhs: NodeRef,
    root: NodeRef,
    wrappers: Vec<NodeRef>,
    reference: Option<NodeRef>,
    arguments: Vec<NodeRef>,
}

impl SourceInterfaceAliasBaseRequest {
    pub(super) const fn symbol(&self) -> SemanticSymbolId {
        self.symbol
    }

    pub(super) const fn declaration(&self) -> NodeRef {
        self.declaration
    }

    pub(super) const fn rhs(&self) -> NodeRef {
        self.rhs
    }

    pub(super) const fn root(&self) -> NodeRef {
        self.root
    }

    pub(super) fn wrappers(&self) -> &[NodeRef] {
        &self.wrappers
    }

    pub(super) const fn reference(&self) -> Option<NodeRef> {
        self.reference
    }

    pub(super) fn arguments(&self) -> &[NodeRef] {
        &self.arguments
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct SourceInterfaceHeritageResolution {
    globals: Option<SymbolTableId>,
    scopes: Vec<(NodeRef, Option<SymbolTableId>)>,
    lookups: Vec<SourceInterfaceHeritageLookupRead>,
    declarations: Vec<SourceInterfaceHeritageDeclarationRead>,
    direct_reads: Vec<SourceInterfaceHeritageTableRead>,
}

/// The original lexical binding, before an import target is followed.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct SourceHeritageTypeBinding {
    symbol: SemanticSymbolId,
    resolution: SourceInterfaceHeritageResolution,
}

impl SourceHeritageTypeBinding {
    pub(super) const fn symbol(&self) -> SemanticSymbolId {
        self.symbol
    }

    pub(super) fn validate_import_target(
        &self,
        store: &CanonicalTypeMapperStore,
        expression: NodeRef,
        target: SemanticSymbolId,
    ) -> bool {
        store
            .symbol(self.symbol)
            .is_some_and(|record| record.flags() == SymbolFlags::ALIAS)
            && validate_source_heritage_identifier_resolution(
                store,
                &self.resolution,
                expression,
                self.symbol,
                target,
                true,
            )
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct SourceInterfaceHeritageTableRead {
    table: SymbolTableId,
    name: EscapedName,
    raw_entry: Option<SemanticSymbolId>,
    canonical_entry: Option<SemanticSymbolId>,
    raw_flags: Option<SymbolFlags>,
    flags: Option<SymbolFlags>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct SourceInterfaceHeritageLookupRead {
    entry: SourceInterfaceHeritageTableRead,
    meaning: SymbolFlags,
    result: Option<SemanticSymbolId>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct SourceInterfaceHeritageDeclarationRead {
    declaration: NodeRef,
    local: bool,
    binding: Option<[Option<SemanticSymbolId>; 2]>,
    result: Option<SemanticSymbolId>,
    flags: Option<SymbolFlags>,
    members: Option<SymbolTableId>,
    exports: Option<SymbolTableId>,
}

/// The active query lends this proof. No part of it enters the heritage map.
#[derive(Clone, Copy)]
pub(super) struct SourceInterfaceHeritageQueryContext<'a> {
    pub(super) array_targets: Option<CanonicalArrayTargets>,
    pub(super) globals: &'a CanonicalGlobalTypes,
    pub(super) source: &'a dyn ConditionalBranchSource,
    pub(super) conditional_results: &'a [ConditionalSourceResultProof],
}

pub(super) enum SourceInterfaceAliasBaseState {
    Pending {
        edges: Vec<TypeId>,
        conditional: Option<ConditionalSourceQueryRequest>,
    },
    Ready {
        type_: TypeId,
        edges: Vec<TypeId>,
    },
}

/// The original table entry and its current canonical symbol, not an alias target.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct SourceLocalNamespaceBinding {
    raw_symbol: SemanticSymbolId,
    symbol: SemanticSymbolId,
}

impl SourceLocalNamespaceBinding {
    pub(super) const fn raw_symbol(&self) -> SemanticSymbolId {
        self.raw_symbol
    }

    pub(super) const fn symbol(&self) -> SemanticSymbolId {
        self.symbol
    }
}

#[derive(Debug)]
pub(super) enum SourceLocalNamespaceLookup {
    Local(SourceLocalNamespaceBinding),
    LocalAliasPending {
        binding: SourceLocalNamespaceBinding,
        error: CanonicalNameResolutionError,
    },
    NoLocalNamespace,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct DirectInterfaceDefaultArgument {
    pub index: usize,
    pub parameter: SemanticSymbolId,
    pub declaration: NodeRef,
    pub node: NodeRef,
    pub argument: NodeRef,
    pub earlier_parameter: Option<SemanticSymbolId>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct DirectInterfaceBasePlan {
    pub node: NodeRef,
    #[allow(dead_code)] // Retained as the instantiation diagnostic anchor.
    pub expression: NodeRef,
    pub symbol: SemanticSymbolId,
    pub kind: DirectInterfaceBaseKind,
    pub type_arguments: Vec<NodeRef>,
    pub defaults: Vec<DirectInterfaceDefaultArgument>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct DirectInterfaceHeritagePlan {
    pub clause: NodeRef,
    pub bases: Vec<DirectInterfaceBasePlan>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum DirectInterfaceHeritageError {
    Invalid,
    Unsupported { node: NodeRef, kind: SyntaxKind },
}

pub(super) const MAX_INTERFACE_HERITAGE_DEPTH: usize = 16;
const MAX_REACT_FORWARDED_INTERFACE_ARGUMENT_DEPTH: usize = 3;

fn source_heritage_error(node: NodeRef) -> DeclaredTypeError {
    DeclaredTypeUnavailable::DeclarationSymbolMismatch(node).into()
}

pub(super) fn source_interface_alias_base_request(
    store: &CanonicalTypeMapperStore,
    symbol: SemanticSymbolId,
) -> Result<Option<SourceInterfaceAliasBaseRequest>, DeclaredTypeError> {
    let source = property_object_alias_identity_source_header(store, symbol)
        .map_err(|_| DeclaredTypeUnavailable::MissingDeclarations(symbol))?;
    if !source.parameters.is_empty() {
        return Ok(None);
    }
    let declaration = source.alias_declaration;
    let rhs = store
        .source_direct_type_annotation(declaration)
        .ok_or_else(|| source_heritage_error(declaration))?;
    let mut root = rhs;
    let mut wrappers = Vec::new();
    while store.source_node_kind(root) == Some(SyntaxKind::ParenthesizedType) {
        if wrappers.len() >= MAX_INTERFACE_HERITAGE_DEPTH {
            return Ok(None);
        }
        let children = store
            .source_direct_children(root)
            .ok_or_else(|| source_heritage_error(root))?;
        let [child] = children.as_slice() else {
            return Err(source_heritage_error(root));
        };
        if store.source_node_parent(*child) != Some(SourceNodeParent::Parent(root)) {
            return Err(source_heritage_error(root));
        }
        wrappers.push(root);
        root = *child;
    }
    if !matches!(
        store.source_node_kind(root),
        Some(SyntaxKind::TypeLiteral | SyntaxKind::ConditionalType)
    ) {
        return Ok(None);
    }
    if store.source_node_kind(root) == Some(SyntaxKind::TypeLiteral)
        && store.source_direct_children(root).is_none_or(|children| {
            children.iter().any(|member| {
                !matches!(
                    store.source_node_kind(*member),
                    Some(SyntaxKind::PropertyDeclaration | SyntaxKind::PropertySignature)
                )
            })
        })
    {
        return Ok(None);
    }
    Ok(Some(SourceInterfaceAliasBaseRequest {
        symbol,
        declaration,
        rhs,
        root,
        wrappers,
        reference: None,
        arguments: Vec::new(),
    }))
}

/// Retains the written arguments separately from the alias's source formals.
pub(super) fn source_interface_alias_reference_request(
    store: &CanonicalTypeMapperStore,
    symbol: SemanticSymbolId,
    reference: NodeRef,
) -> Result<SourceInterfaceAliasBaseRequest, DeclaredTypeError> {
    let invalid = || source_heritage_error(reference);
    let source =
        property_object_alias_identity_source_header(store, symbol).map_err(|_| invalid())?;
    let rhs = store
        .source_direct_type_annotation(source.alias_declaration)
        .ok_or_else(invalid)?;
    let children = store
        .source_direct_children(reference)
        .ok_or_else(invalid)?;
    let [expression, arguments @ ..] = children.as_slice() else {
        return Err(invalid());
    };
    if store.source_node_kind(reference) != Some(SyntaxKind::ExpressionWithTypeArguments)
        || store.source_node_kind(*expression) != Some(SyntaxKind::Identifier)
        || children.iter().any(|child| {
            store.source_node_parent(*child) != Some(SourceNodeParent::Parent(reference))
        })
    {
        return Err(invalid());
    }
    Ok(SourceInterfaceAliasBaseRequest {
        symbol,
        declaration: source.alias_declaration,
        rhs,
        root: reference,
        wrappers: Vec::new(),
        reference: Some(reference),
        arguments: arguments.to_vec(),
    })
}

fn source_heritage_table_read(
    store: &CanonicalTypeMapperStore,
    table: SymbolTableId,
    name: EscapedNameRef<'_>,
) -> Option<SourceInterfaceHeritageTableRead> {
    let raw_entry = store.symbol_table(table)?.get(name);
    let canonical_entry = match raw_entry {
        Some(raw) => Some(store.get_merged_symbol(raw)?),
        None => None,
    };
    let raw_flags = match raw_entry {
        Some(raw) => Some(store.symbol(raw)?.flags()),
        None => None,
    };
    let flags = match canonical_entry {
        Some(symbol) => Some(store.symbol(symbol)?.flags()),
        None => None,
    };
    Some(SourceInterfaceHeritageTableRead {
        table,
        name: name.to_owned(),
        raw_entry,
        canonical_entry,
        raw_flags,
        flags,
    })
}

#[derive(Clone, Copy, Eq, PartialEq)]
enum SourceHeritageTableOwner {
    Locals(NodeRef),
    Members(SemanticSymbolId),
    Exports(SemanticSymbolId),
}

fn source_heritage_original_binding(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    declaration: NodeRef,
) -> Option<[Option<SemanticSymbolId>; 2]> {
    let bound = host.bound_file(declaration)?;
    let binding = [bound.symbol(declaration), bound.local_symbol(declaration)];
    (store.source_is_typescript(declaration)
        && store.symbol_store().source_binding_symbols(declaration)
            == binding.iter().any(Option::is_some).then_some(binding))
    .then_some(binding)
}

fn source_heritage_original_declaration_read(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    declaration: NodeRef,
    local: bool,
) -> Option<SourceInterfaceHeritageDeclarationRead> {
    let binding = source_heritage_original_binding(store, host, declaration)?;
    let raw = binding[usize::from(local)]?;
    let result = store.get_merged_symbol(raw)?;
    let record = store.symbol(result)?;
    (store.source_raw_symbol_declarations_match(raw)
        && store.source_symbol_export_table_matches(raw)
        && store.source_merged_symbol_declarations_match(result)
        && store.source_declaration_belongs_to_symbol(declaration, result))
    .then_some(SourceInterfaceHeritageDeclarationRead {
        declaration,
        local,
        binding: Some(binding),
        result: Some(result),
        flags: Some(record.flags()),
        members: record.members(),
        exports: record.exports(),
    })
}

fn source_heritage_local_scope(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    declaration: NodeRef,
    binding: [Option<SemanticSymbolId>; 2],
) -> Option<NodeRef> {
    let (arena, bound) = host.source(declaration)?;
    match store.source_node_kind(declaration)? {
        SyntaxKind::ClassDeclaration
        | SyntaxKind::InterfaceDeclaration
        | SyntaxKind::TypeAliasDeclaration
        | SyntaxKind::FunctionDeclaration
        | SyntaxKind::EnumDeclaration => bound.block_scope_container(declaration),
        SyntaxKind::VariableDeclaration | SyntaxKind::BindingElement => {
            let symbol = store.get_merged_symbol(binding[0]?)?;
            if store
                .source_symbol_flags(symbol)?
                .contains(SymbolFlags::BLOCK_SCOPED_VARIABLE)
            {
                bound.block_scope_container(declaration)
            } else {
                bound.container(declaration)
            }
        }
        SyntaxKind::ImportEqualsDeclaration
            if canonical_has_syntactic_modifier(
                arena,
                declaration.node,
                SyntaxKind::ExportKeyword,
            ) =>
        {
            None
        }
        SyntaxKind::TypeParameter
            if matches!(store.source_node_parent(declaration), Some(SourceNodeParent::Parent(parent))
                if store.source_node_kind(parent) == Some(SyntaxKind::InferType)) =>
        {
            None
        }
        SyntaxKind::Parameter
        | SyntaxKind::TypeParameter
        | SyntaxKind::ModuleDeclaration
        | SyntaxKind::ImportEqualsDeclaration
        | SyntaxKind::ImportClause
        | SyntaxKind::ImportSpecifier
        | SyntaxKind::NamespaceImport => bound.container(declaration),
        _ => None,
    }
}

fn source_heritage_contributes_to_owner_table(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    declaration: NodeRef,
    binding: [Option<SemanticSymbolId>; 2],
    owner: SourceHeritageTableOwner,
    containers: &[NodeRef],
) -> bool {
    let Some((arena, bound)) = host.source(declaration) else {
        return false;
    };
    if bound
        .container(declaration)
        .is_none_or(|container| !containers.contains(&container))
    {
        return false;
    }
    let is_static =
        canonical_has_syntactic_modifier(arena, declaration.node, SyntaxKind::StaticKeyword);
    match owner {
        SourceHeritageTableOwner::Locals(_) => false,
        SourceHeritageTableOwner::Members(_) => {
            !is_static
                && matches!(
                    store.source_node_kind(declaration),
                    Some(
                        SyntaxKind::TypeParameter
                            | SyntaxKind::PropertyDeclaration
                            | SyntaxKind::PropertySignature
                            | SyntaxKind::MethodDeclaration
                            | SyntaxKind::MethodSignature
                            | SyntaxKind::Constructor
                            | SyntaxKind::GetAccessor
                            | SyntaxKind::SetAccessor
                            | SyntaxKind::CallSignature
                            | SyntaxKind::ConstructSignature
                            | SyntaxKind::IndexSignature
                    )
                )
        }
        SourceHeritageTableOwner::Exports(_) => {
            binding[1].is_some()
                || is_static
                || matches!(
                    store.source_node_kind(declaration),
                    Some(
                        SyntaxKind::ExportSpecifier
                            | SyntaxKind::NamespaceExport
                            | SyntaxKind::ExportDeclaration
                            | SyntaxKind::ExportAssignment
                            | SyntaxKind::EnumMember
                    )
                )
                || store.source_node_is_exported(declaration) == Some(true)
        }
    }
}

fn source_heritage_global_entry_is_exact(
    store: &CanonicalTypeMapperStore,
    read: &SourceInterfaceHeritageTableRead,
) -> bool {
    let Some(globals) = store.source_global_bindings() else {
        return false;
    };
    if globals.table != read.table {
        return false;
    }
    match (globals.get(read.name.as_ref()), read.raw_entry) {
        (None, None) => true,
        (Some(binding), Some(raw)) => {
            binding.table_symbol == raw
                && Some(binding.symbol) == read.canonical_entry
                && Some(binding.flags) == read.flags
                && store.source_merged_symbol_declarations_match(binding.symbol)
        }
        _ => false,
    }
}

/// Checks the original matching declarations, including an original miss.
/// The normal resolver still owns lookup order and meaning selection.
#[allow(clippy::too_many_lines)]
fn retain_source_heritage_table_origins(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    expression: NodeRef,
    reads: &mut SourceInterfaceHeritageResolution,
) -> Result<(), DeclaredTypeError> {
    let invalid = || source_heritage_error(expression);
    let entries: Vec<_> = reads
        .lookups
        .iter()
        .map(|read| read.entry.clone())
        .chain(reads.direct_reads.iter().cloned())
        .collect();
    let callback_declarations = reads.declarations.clone();
    for entry in entries {
        if Some(entry.table) == reads.globals {
            if !source_heritage_global_entry_is_exact(store, &entry) {
                return Err(invalid());
            }
            continue;
        }
        let mut owners = Vec::new();
        for &(scope, locals) in &reads.scopes {
            if locals == Some(entry.table) {
                owners.push(SourceHeritageTableOwner::Locals(scope));
            }
        }
        for read in &callback_declarations {
            let Some(symbol) = read.result else {
                continue;
            };
            for (table, owner) in [
                (read.members, SourceHeritageTableOwner::Members(symbol)),
                (read.exports, SourceHeritageTableOwner::Exports(symbol)),
            ] {
                if table == Some(entry.table) && !owners.contains(&owner) {
                    owners.push(owner);
                }
            }
        }
        let [owner] = owners.as_slice() else {
            return Err(invalid());
        };
        let containers = match *owner {
            SourceHeritageTableOwner::Locals(scope) => vec![scope],
            SourceHeritageTableOwner::Members(symbol)
            | SourceHeritageTableOwner::Exports(symbol) => {
                if !store.source_merged_symbol_declarations_match(symbol) {
                    return Err(invalid());
                }
                store
                    .symbol(symbol)
                    .and_then(|record| record.declarations())
                    .ok_or_else(invalid)?
                    .to_vec()
            }
        };
        let mut files = HashSet::new();
        let mut original_entries = Vec::new();
        for &container in &containers {
            let (_, bound) = host.source(container).ok_or_else(invalid)?;
            if !files.insert(container.file) {
                continue;
            }
            for declaration in bound.traversal_order() {
                let binding = source_heritage_original_binding(store, host, declaration)
                    .ok_or_else(invalid)?;
                let local =
                    matches!(owner, SourceHeritageTableOwner::Locals(_)) && binding[1].is_some();
                let Some(raw) = binding[usize::from(local)] else {
                    continue;
                };
                let record = store.symbol(raw).ok_or_else(invalid)?;
                if record.name() != entry.name.as_ref() {
                    continue;
                }
                let witness =
                    source_heritage_original_declaration_read(store, host, declaration, local)
                        .ok_or_else(invalid)?;
                let contributes = match *owner {
                    SourceHeritageTableOwner::Locals(scope) => {
                        source_heritage_local_scope(store, host, declaration, binding)
                            == Some(scope)
                            && bound.locals(scope) == Some(entry.table)
                    }
                    _ => source_heritage_contributes_to_owner_table(
                        store,
                        host,
                        declaration,
                        binding,
                        *owner,
                        &containers,
                    ),
                };
                if !contributes {
                    continue;
                }
                original_entries.push(raw);
                if !reads.declarations.contains(&witness) {
                    reads.declarations.push(witness);
                }
            }
        }
        if original_entries.is_empty() {
            if entry.raw_entry.is_some() {
                return Err(invalid());
            }
        } else {
            let canonical = store
                .get_merged_symbol(original_entries[0])
                .ok_or_else(invalid)?;
            if original_entries
                .iter()
                .any(|raw| store.get_merged_symbol(*raw) != Some(canonical))
                || entry.canonical_entry != Some(canonical)
                || entry.raw_entry.is_none_or(|raw| {
                    !original_entries.contains(&raw)
                        && (matches!(owner, SourceHeritageTableOwner::Locals(_))
                            || raw != canonical)
                })
            {
                return Err(invalid());
            }
        }
    }
    Ok(())
}

struct SourceHeritageResolver<'store, 'arena> {
    inner: ProductionNameResolverHost<'store, 'arena>,
    store: &'store CanonicalTypeMapperStore,
    name: EscapedName,
    reads: SourceInterfaceHeritageResolution,
    invalid: bool,
}

impl SourceHeritageResolver<'_, '_> {
    fn record_declaration(
        &mut self,
        declaration: NodeRef,
        local: bool,
        result: Option<SemanticSymbolId>,
    ) {
        let record = result.and_then(|symbol| self.store.symbol(symbol));
        if result.is_some() && record.is_none() {
            self.invalid = true;
        }
        let exports = record.and_then(|record| record.exports());
        self.reads
            .declarations
            .push(SourceInterfaceHeritageDeclarationRead {
                declaration,
                local,
                binding: self
                    .store
                    .symbol_store()
                    .source_binding_symbols(declaration),
                result,
                flags: record.map(|record| record.flags()),
                members: record.and_then(|record| record.members()),
                exports,
            });
        if let Some(exports) = exports
            && matches!(
                self.store.source_node_kind(declaration),
                Some(SyntaxKind::SourceFile | SyntaxKind::ModuleDeclaration)
            )
        {
            for name in [InternalSymbolName::Default.as_ref(), self.name.as_ref()] {
                if let Some(read) = source_heritage_table_read(self.store, exports, name) {
                    self.reads.direct_reads.push(read);
                } else {
                    self.invalid = true;
                }
            }
        }
    }
}

impl CanonicalNameResolverHost for SourceHeritageResolver<'_, '_> {
    fn compiler_options(&self) -> CanonicalNameResolverOptions {
        self.inner.compiler_options()
    }

    fn get_symbol_of_declaration(&mut self, declaration: NodeRef) -> Option<SemanticSymbolId> {
        let result = self.inner.get_symbol_of_declaration(declaration);
        self.record_declaration(declaration, false, result);
        result
    }

    fn get_local_symbol_of_declaration(
        &mut self,
        declaration: NodeRef,
    ) -> Option<SemanticSymbolId> {
        let result = self.inner.get_local_symbol_of_declaration(declaration);
        self.record_declaration(declaration, true, result);
        result
    }

    fn lookup(
        &mut self,
        symbols: &SymbolStore,
        table: SymbolTableId,
        name: EscapedNameRef<'_>,
        meaning: SymbolFlags,
    ) -> Result<Option<SemanticSymbolId>, CanonicalNameResolutionError> {
        let entry = source_heritage_table_read(self.store, table, name)
            .ok_or(CanonicalNameResolutionError::InvalidHostTable(table))?;
        let result = self.inner.lookup(symbols, table, name, meaning);
        self.reads.lookups.push(SourceInterfaceHeritageLookupRead {
            entry,
            meaning,
            result: result.as_ref().ok().copied().flatten(),
        });
        result
    }

    fn globals(&self) -> Option<SymbolTableId> {
        self.inner.globals()
    }

    fn arguments_symbol(&mut self, store: &SymbolStore) -> Option<SemanticSymbolId> {
        self.inner.arguments_symbol(store)
    }

    fn require_symbol(&mut self, store: &SymbolStore) -> Option<SemanticSymbolId> {
        self.inner.require_symbol(store)
    }

    fn foreign_declaration_kind(&mut self, declaration: NodeRef) -> Option<SyntaxKind> {
        self.inner.foreign_declaration_kind(declaration)
    }

    fn foreign_declaration_parent(&mut self, declaration: NodeRef) -> Option<NodeRef> {
        self.inner.foreign_declaration_parent(declaration)
    }

    fn foreign_declaration_has_syntactic_modifier(
        &mut self,
        declaration: NodeRef,
        modifier: SyntaxKind,
    ) -> Option<bool> {
        self.inner
            .foreign_declaration_has_syntactic_modifier(declaration, modifier)
    }
}

#[allow(clippy::type_complexity)] // Keep the original resolver outcome separate from its source proof.
fn resolve_source_identifier_with_origins(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    expression: NodeRef,
    meaning: SymbolFlags,
    exclude_globals: bool,
) -> Result<
    (
        Result<Option<SemanticSymbolId>, CanonicalNameResolutionError>,
        SourceInterfaceHeritageResolution,
    ),
    DeclaredTypeError,
> {
    let node = preflight_node(store, host, expression)?;
    let NodeData::Identifier(identifier) = &node.data else {
        return Err(source_heritage_error(expression));
    };
    let (arena, bound) = host
        .source(expression)
        .ok_or_else(|| source_heritage_error(expression))?;
    let inner = host.name_resolver_host(store)?;
    let globals = inner.globals();
    let mut scopes = Vec::new();
    let mut current = Some(expression);
    let mut seen = HashSet::new();
    while let Some(scope) = current {
        if !seen.insert(scope) {
            return Err(source_heritage_error(expression));
        }
        let record = preflight_node(store, host, scope)?;
        scopes.push((scope, bound.locals(scope)));
        current = record
            .parent
            .map(|parent| NodeRef::new(scope.arena, scope.file, parent));
    }
    let mut resolver_host = SourceHeritageResolver {
        inner,
        store,
        name: EscapedName::source(&identifier.text),
        reads: SourceInterfaceHeritageResolution {
            globals,
            scopes,
            lookups: Vec::new(),
            declarations: Vec::new(),
            direct_reads: Vec::new(),
        },
        invalid: false,
    };
    let resolved =
        CanonicalNameResolver::new(arena, bound, store.symbol_store(), &mut resolver_host)?
            .resolve(
                Some(CanonicalResolutionLocation::Bound(expression)),
                &identifier.text,
                meaning,
                None,
                false,
                exclude_globals,
            );
    if resolver_host.invalid {
        return Err(source_heritage_error(expression));
    }
    retain_source_heritage_table_origins(store, host, expression, &mut resolver_host.reads)?;
    Ok((resolved, resolver_host.reads))
}

fn try_resolve_source_heritage_base(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    expression: NodeRef,
) -> Result<Option<(SemanticSymbolId, SourceInterfaceHeritageResolution)>, DeclaredTypeError> {
    let (resolved, reads) = resolve_source_identifier_with_origins(
        store,
        host,
        expression,
        SymbolFlags::TYPE | SymbolFlags::ALIAS,
        false,
    )?;
    let Some(symbol) = resolved
        .ok()
        .flatten()
        .and_then(|symbol| store.get_merged_symbol(symbol))
    else {
        return Ok(None);
    };
    Ok(Some((symbol, reads)))
}

/// Finds the original type binding without following a mutable import target.
pub(super) fn resolve_source_heritage_type_binding(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    expression: NodeRef,
) -> Result<Option<SemanticSymbolId>, DeclaredTypeError> {
    let (resolved, _) = resolve_source_identifier_with_origins(
        store,
        host,
        expression,
        SymbolFlags::TYPE | SymbolFlags::ALIAS,
        false,
    )?;
    resolved.map_err(DeclaredTypeError::from)
}

/// Retains the same source lookup for a separately authenticated import target.
pub(super) fn plan_source_heritage_type_binding(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    expression: NodeRef,
) -> Result<Option<SourceHeritageTypeBinding>, DeclaredTypeError> {
    Ok(try_resolve_source_heritage_base(store, host, expression)?.map(
        |(symbol, resolution)| SourceHeritageTypeBinding { symbol, resolution },
    ))
}

/// Proves the local namespace lookup before a caller considers a global entry.
/// An alias binding still needs the existing import resolver's target proof.
pub(super) fn resolve_source_local_namespace_binding(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    identifier: NodeRef,
) -> Result<SourceLocalNamespaceLookup, DeclaredTypeError> {
    let (resolved, reads) = resolve_source_identifier_with_origins(
        store,
        host,
        identifier,
        SymbolFlags::NAMESPACE,
        true,
    )?;
    let invalid = || source_heritage_error(identifier);
    let (resolved, pending_alias) = match resolved {
        Ok(resolved) => (resolved, None),
        Err(error @ CanonicalNameResolutionError::AliasResolutionUnavailable(alias)) => {
            (None, Some((alias, error)))
        }
        Err(error) => return Err(error.into()),
    };
    for (index, read) in reads.lookups.iter().enumerate() {
        if read.result.is_none()
            && read
                .entry
                .flags
                .is_some_and(|flags| flags.contains(SymbolFlags::ALIAS))
        {
            let alias = read.entry.canonical_entry.ok_or_else(invalid)?;
            if index + 1 != reads.lookups.len()
                || pending_alias.as_ref().map(|(symbol, _)| *symbol) != Some(alias)
            {
                return Err(CanonicalNameResolutionError::AliasResolutionUnavailable(alias).into());
            }
        }
    }
    if let Some((alias, error)) = pending_alias {
        let read = reads.lookups.last().ok_or_else(invalid)?;
        if read.entry.canonical_entry != Some(alias)
            || read.result.is_some()
            || read
                .entry
                .flags
                .is_none_or(|flags| !flags.contains(SymbolFlags::ALIAS))
        {
            return Err(invalid());
        }
        return Ok(SourceLocalNamespaceLookup::LocalAliasPending {
            binding: SourceLocalNamespaceBinding {
                raw_symbol: read.entry.raw_entry.ok_or_else(invalid)?,
                symbol: alias,
            },
            error,
        });
    }
    let Some(resolved) = resolved else {
        return Ok(SourceLocalNamespaceLookup::NoLocalNamespace);
    };
    let symbol = store.get_merged_symbol(resolved).ok_or_else(invalid)?;
    let entry = reads
        .lookups
        .iter()
        .rev()
        .find(|read| {
            read.result
                .and_then(|result| store.get_merged_symbol(result))
                == Some(symbol)
                && read.entry.canonical_entry == Some(symbol)
        })
        .map(|read| &read.entry)
        .or_else(|| {
            reads.direct_reads.iter().rev().find(|read| {
                read.raw_entry == Some(resolved) && read.canonical_entry == Some(symbol)
            })
        })
        .ok_or_else(invalid)?;
    Ok(SourceLocalNamespaceLookup::Local(
        SourceLocalNamespaceBinding {
            raw_symbol: entry.raw_entry.ok_or_else(invalid)?,
            symbol,
        },
    ))
}

fn source_heritage_owner_is_exact(
    store: &CanonicalTypeMapperStore,
    owner: SemanticSymbolId,
    declarations: &[NodeRef],
) -> bool {
    let Some(record) = store.symbol(owner) else {
        return false;
    };
    if store.get_merged_symbol(owner) != Some(owner)
        || record.declarations() != Some(declarations)
        || declarations.is_empty()
        || record.check_flags() != CheckFlags::NONE
        || !store.source_merged_symbol_declarations_match(owner)
    {
        return false;
    }
    if super::object_members::source_interface_uses_legacy_single_script_value_owner(store, owner) {
        return super::object_members::authenticated_nongeneric_global_interface_owner(
            store, owner,
        );
    }
    match store.source_global_interface_value_owner(owner) {
        Ok(Some(proof)) => proof.declarations() == declarations,
        Err(_) => false,
        Ok(None) => {
            if record.flags().without(SymbolFlags::TRANSIENT) != SymbolFlags::INTERFACE
                || record.value_declaration().is_some()
                || record.exports().is_some()
                || record.export_symbol().is_some()
            {
                return false;
            }
            if let Some(globals) = store.source_global_bindings()
                && let Some(binding) = globals.get(record.name())
                && binding.symbol == owner
                && (binding.declarations() != Some(declarations)
                    || binding.flags != record.flags()
                    || store.get_merged_symbol(binding.table_symbol) != Some(owner)
                    || store
                        .symbol_table(globals.table)
                        .and_then(|table| table.get(record.name()))
                        != Some(binding.table_symbol))
            {
                return false;
            }
            declarations.iter().all(|declaration| {
                store.source_node_kind(*declaration) == Some(SyntaxKind::InterfaceDeclaration)
                    && store.source_declaration_belongs_to_symbol(*declaration, owner)
                    && store.source_is_typescript(*declaration)
            })
        }
    }
}

/// Plans only the new nongeneric source-alias family. Legacy heritage stays separate.
#[allow(clippy::too_many_lines)] // Keep original lookup proof before target eligibility.
pub(super) fn plan_source_interface_heritage_header(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    owner: SemanticSymbolId,
) -> Result<Option<SourceInterfaceHeritageHeader>, DeclaredTypeError> {
    let Some(record) = store.symbol(owner) else {
        return Ok(None);
    };
    let Some(declarations) = record.declarations() else {
        return Ok(None);
    };
    let not_source_alias_heritage = || {
        if store
            .declared_type_links(owner)
            .and_then(|links| links.declared_type)
            .and_then(|type_| store.source_interface_heritage_header(type_))
            .is_some()
        {
            Err(DeclaredTypeUnavailable::MissingDeclarations(owner).into())
        } else {
            Ok(None)
        }
    };
    if !record.flags().contains(SymbolFlags::INTERFACE)
        || record.flags().contains(SymbolFlags::CLASS)
    {
        return not_source_alias_heritage();
    }
    let mut bases = Vec::new();
    for &declaration in declarations {
        let record = preflight_node(store, host, declaration)?;
        if record.kind == SyntaxKind::VariableDeclaration {
            continue;
        }
        let NodeData::InterfaceDeclaration(interface) = &record.data else {
            return Err(source_heritage_error(declaration));
        };
        if interface.type_parameters.is_some() {
            return not_source_alias_heritage();
        }
        let Some(clauses) = interface.heritage_clauses.as_ref() else {
            continue;
        };
        // Check original plain bindings before the current target can change
        // eligibility. Qualified and generic legacy heritage keeps its path.
        let mut resolutions = Vec::new();
        if let Some(PlainInterfaceHeritageFacts::Plain { bases, .. }) =
            store.source_plain_interface_heritage(declaration)
        {
            for base in bases {
                let expression = NodeRef::new(declaration.arena, declaration.file, base.name);
                resolutions.push((
                    expression,
                    try_resolve_source_heritage_base(store, host, expression)?,
                ));
            }
        }
        let planned = match plan_direct_interface_heritage(store, host, declaration, owner, clauses)
        {
            Ok(planned) => planned,
            Err(DirectInterfaceHeritageError::Unsupported { .. }) => {
                return not_source_alias_heritage();
            }
            Err(DirectInterfaceHeritageError::Invalid) => {
                return Err(source_heritage_error(declaration));
            }
        };
        if declarations == [declaration]
            && planned.bases.iter().all(|base| {
                base.kind == DirectInterfaceBaseKind::Interface
                    && base.type_arguments.is_empty()
                    && base.defaults.is_empty()
                    && store.source_node_kind(base.expression) == Some(SyntaxKind::Identifier)
            })
        {
            for base in &planned.bases {
                if super::source_imports::plan_source_interface_heritage_type_import(
                    store,
                    host,
                    declaration,
                    owner,
                    base.node,
                )
                .map_err(|_| source_heritage_error(base.expression))?
                    == Some(base.symbol)
                {
                    // Import proof belongs to the direct planner, not this source-alias header.
                    return not_source_alias_heritage();
                }
            }
        }
        for base in planned.bases {
            if !matches!(
                base.kind,
                DirectInterfaceBaseKind::Interface
                    | DirectInterfaceBaseKind::NongenericTypeLiteralAlias
                    | DirectInterfaceBaseKind::InstantiatedTypeAlias
                    | DirectInterfaceBaseKind::RecordMappedAlias
            ) || !base.kind.is_instantiated_alias() && !base.type_arguments.is_empty()
                || !base.defaults.is_empty()
                || store.source_node_kind(base.expression) != Some(SyntaxKind::Identifier)
            {
                return not_source_alias_heritage();
            }
            let resolution = resolutions
                .iter_mut()
                .find(|(expression, _)| *expression == base.expression)
                .and_then(|(_, resolution)| resolution.take());
            let (symbol, resolution) = match resolution {
                Some(resolution) => resolution,
                None if base.kind.is_instantiated_alias() => {
                    try_resolve_source_heritage_base(store, host, base.expression)?
                        .ok_or_else(|| source_heritage_error(base.expression))?
                }
                None => return Err(source_heritage_error(base.expression)),
            };
            let import = super::source_imports::plan_source_interface_heritage_import(
                store,
                host,
                declaration,
                owner,
                base.node,
            )
            .map_err(|_| source_heritage_error(base.expression))?;
            let expected_binding = import
                .as_ref()
                .map_or(base.symbol, |import| import.alias_symbol());
            if symbol != expected_binding
                || import
                    .as_ref()
                    .is_some_and(|import| import.target_symbol() != base.symbol)
            {
                return Err(source_heritage_error(base.expression));
            }
            let alias = if base.kind.is_instantiated_alias() {
                Some(source_interface_alias_reference_request(
                    store,
                    base.symbol,
                    base.node,
                )?)
            } else if base.kind == DirectInterfaceBaseKind::NongenericTypeLiteralAlias {
                Some(
                    source_interface_alias_base_request(store, base.symbol)?
                        .ok_or_else(|| source_heritage_error(base.expression))?,
                )
            } else {
                None
            };
            bases.push(SourceInterfaceHeritageBase {
                declaration,
                clause: planned.clause,
                node: base.node,
                expression: base.expression,
                symbol: base.symbol,
                alias,
                resolution,
                import,
            });
        }
    }
    if !bases.iter().any(|base| base.alias.is_some()) {
        return not_source_alias_heritage();
    }
    if !source_heritage_owner_is_exact(store, owner, declarations) {
        return Err(DeclaredTypeUnavailable::MissingDeclarations(owner).into());
    }
    Ok(Some(SourceInterfaceHeritageHeader {
        owner_symbol: owner,
        owner_declarations: declarations.to_vec(),
        bases,
    }))
}

fn validate_source_heritage_resolution(
    store: &CanonicalTypeMapperStore,
    base: &SourceInterfaceHeritageBase,
) -> bool {
    if base.import.as_ref().is_some_and(|import| {
        import.target_symbol() != base.symbol || import.validate_current(store, base.node).is_err()
    }) {
        return false;
    }
    let binding = base
        .import
        .as_ref()
        .map_or(base.symbol, |import| import.alias_symbol());
    validate_source_heritage_identifier_resolution(
        store,
        &base.resolution,
        base.expression,
        binding,
        base.symbol,
        base.import.is_some(),
    )
}

fn validate_source_heritage_identifier_resolution(
    store: &CanonicalTypeMapperStore,
    reads: &SourceInterfaceHeritageResolution,
    expression: NodeRef,
    binding: SemanticSymbolId,
    target: SemanticSymbolId,
    imported: bool,
) -> bool {
    if reads.globals
        != store
            .intrinsic_bootstrap()
            .map(|bootstrap| bootstrap.globals)
        || reads.scopes.first().map(|(node, _)| *node) != Some(expression)
        || reads.scopes.is_empty()
    {
        return false;
    }
    let mut tables = HashSet::new();
    if let Some(globals) = reads.globals {
        tables.insert(globals);
    }
    for (index, &(node, locals)) in reads.scopes.iter().enumerate() {
        if !store.source_is_typescript(node)
            || store.source_node_kind(node).is_none()
            || store.source_node_parent(node)
                != Some(match reads.scopes.get(index + 1) {
                    Some((parent, _)) => SourceNodeParent::Parent(*parent),
                    None => SourceNodeParent::Root,
                })
            || locals.is_some_and(|locals| store.symbol_table(locals).is_none())
        {
            return false;
        }
        if let Some(locals) = locals {
            tables.insert(locals);
        }
    }
    for read in &reads.declarations {
        if store
            .symbol_store()
            .source_binding_symbols(read.declaration)
            != read.binding
            || read.binding.is_some_and(|binding| {
                binding[usize::from(read.local)].is_some_and(|raw| {
                    !store.source_raw_symbol_declarations_match(raw)
                        || !store.source_symbol_export_table_matches(raw)
                })
            })
        {
            return false;
        }
        let expected = match read.binding {
            Some(bindings) => {
                bindings[usize::from(read.local)].and_then(|symbol| store.get_merged_symbol(symbol))
            }
            None if !read.local => store.source_declaration_symbol(read.declaration),
            None => None,
        };
        let record = read.result.and_then(|symbol| store.symbol(symbol));
        if expected != read.result
            || record.map(|record| record.flags()) != read.flags
            || record.and_then(|record| record.members()) != read.members
            || record.and_then(|record| record.exports()) != read.exports
            || read.result.is_some_and(|symbol| {
                !store.source_declaration_belongs_to_symbol(read.declaration, symbol)
                    || !store.source_merged_symbol_declarations_match(symbol)
            })
        {
            return false;
        }
        tables.extend(read.members);
        tables.extend(read.exports);
    }
    let valid_entry = |read: &SourceInterfaceHeritageTableRead| {
        if !tables.contains(&read.table)
            || source_heritage_table_read(store, read.table, read.name.as_ref()).as_ref()
                != Some(read)
        {
            return false;
        }
        if Some(read.table) == reads.globals && !source_heritage_global_entry_is_exact(store, read)
        {
            return false;
        }
        read.canonical_entry.is_none_or(|symbol| {
            store.source_merged_symbol_declarations_match(symbol)
                || store.source_symbol_declarations_match(symbol)
        })
    };
    if !reads.direct_reads.iter().all(valid_entry) {
        return false;
    }
    for read in &reads.lookups {
        if !valid_entry(&read.entry)
            // Imported aliases need the import resolver's own source receipt.
            || read.entry.flags.is_some_and(|flags| flags.contains(SymbolFlags::ALIAS))
                && (!imported || read.entry.canonical_entry != Some(binding))
        {
            return false;
        }
        let expected = read.entry.canonical_entry.filter(|_| {
            read.meaning.intersects(SymbolFlags::ALL)
                && read
                    .entry
                    .flags
                    .is_some_and(|flags| flags.intersects(read.meaning))
        });
        if read.result != expected {
            return false;
        }
    }
    reads
        .lookups
        .iter()
        .any(|read| read.result == Some(binding))
        && store
            .symbol_node_links(expression)
            .is_none_or(|links| {
                links
                    .resolved_symbol
                    .is_none_or(|symbol| symbol == target || symbol == binding)
            })
}

fn source_alias_cached_identity(
    store: &CanonicalTypeMapperStore,
    request: &SourceInterfaceAliasBaseRequest,
) -> Result<Option<TypeId>, DeclaredTypeError> {
    let invalid = || source_heritage_error(request.rhs);
    if source_interface_alias_base_request(store, request.symbol)?.as_ref() != Some(request) {
        return Err(invalid());
    }
    if store
        .declared_type_links(request.symbol)
        .is_some_and(|links| links != &super::links::DeclaredTypeLinks::default())
        || store
            .value_symbol_links(request.symbol)
            .is_some_and(|links| links != &super::links::ValueSymbolLinks::default())
    {
        return Err(invalid());
    }
    let links = store.type_alias_links(request.symbol);
    if links.is_some_and(|links| {
        links.type_parameters.is_some()
            || links.instantiations.is_some()
            || links.is_constructor_declared_property
    }) {
        return Err(invalid());
    }
    let mut result = None;
    for node in std::iter::once(request.root).chain(request.wrappers.iter().copied()) {
        if let Some(links) = store.type_node_links(node) {
            if links.outer_type_parameters.is_some() {
                return Err(invalid());
            }
            if let Some(type_) = links.resolved_type {
                if store.type_payload(type_).is_none()
                    || result.is_some_and(|expected| expected != type_)
                {
                    return Err(invalid());
                }
                result = Some(type_);
            }
        }
    }
    let root = store
        .type_node_links(request.root)
        .and_then(|links| links.resolved_type);
    if result.is_some() && root != result
        || links
            .and_then(|links| links.declared_type)
            .is_some_and(|type_| {
                Some(type_) != root
                    || store
                        .type_node_links(request.rhs)
                        .and_then(|links| links.resolved_type)
                        != Some(type_)
            })
    {
        return Err(invalid());
    }
    Ok(result)
}

fn source_alias_base_metadata(
    store: &CanonicalTypeMapperStore,
    request: &SourceInterfaceAliasBaseRequest,
    array_targets: Option<CanonicalArrayTargets>,
    query: Option<&SourceInterfaceHeritageQueryContext<'_>>,
) -> Result<
    (
        Option<TypeId>,
        Vec<TypeId>,
        Option<ConditionalSourceQueryRequest>,
    ),
    DeclaredTypeError,
> {
    if request.reference.is_some() {
        let cached = cached_interface_alias_reference_with_query_context(
            store,
            request,
            array_targets,
            query,
        )?;
        return Ok((cached, cached.into_iter().collect(), None));
    }
    let invalid = || source_heritage_error(request.rhs);
    let cached = source_alias_cached_identity(store, request)?;
    let mut edges = Vec::new();
    let conditional = if store.source_node_kind(request.root) == Some(SyntaxKind::ConditionalType) {
        let metadata = conditional_source_query_request(
            store,
            ConditionalQueryKey::Node(request.root),
            array_targets,
        )
        .map_err(|_| invalid())?;
        if cached.is_some() != metadata.is_some() {
            return Err(invalid());
        }
        if let Some(metadata) = metadata.as_ref() {
            if metadata.source_node() != request.root {
                return Err(invalid());
            }
            edges.extend(metadata.identity_type_edges());
        }
        metadata
    } else {
        if let Some(type_) = cached {
            let record = store.type_payload(type_).ok_or_else(invalid)?;
            let owner = record
                .symbol()
                .and_then(|owner| store.symbol(owner))
                .ok_or_else(invalid)?;
            if owner.declarations() != Some(&[request.root])
                || record
                    .alias()
                    .and_then(|alias| store.type_alias(alias))
                    .is_none_or(|alias| {
                        alias.symbol() != Some(request.symbol)
                            || alias
                                .type_arguments()
                                .is_some_and(|arguments| !arguments.is_empty())
                    })
                || !matches!(
                    super::object_members::validate_resolved_declared_property_object(store, type_),
                    super::object_members::DeclaredPropertyObjectValidation::Valid(
                        super::object_members::DeclaredPropertyObjectProof::TypeLiteral
                    )
                )
            {
                return Err(invalid());
            }
            match super::object_members::validate_resolved_declared_property_type_graph(
                store, type_,
            ) {
                super::object_members::DeclaredPropertyTypeGraphValidation::Traversable(
                    properties,
                ) => edges.extend(properties),
                _ => return Err(invalid()),
            }
            edges.push(type_);
        }
        None
    };
    Ok((cached, edges, conditional))
}

/// A cached root can be pending. Only the real query can supply missing source authority.
pub(super) fn source_interface_alias_base_state(
    store: &CanonicalTypeMapperStore,
    request: &SourceInterfaceAliasBaseRequest,
    array_targets: Option<CanonicalArrayTargets>,
    query: Option<&SourceInterfaceHeritageQueryContext<'_>>,
) -> Result<SourceInterfaceAliasBaseState, DeclaredTypeError> {
    let invalid = || source_heritage_error(request.rhs);
    let (cached, mut edges, conditional) =
        source_alias_base_metadata(store, request, array_targets, query)?;
    if request.reference.is_some() {
        let Some(type_) = cached else {
            return Ok(SourceInterfaceAliasBaseState::Pending { edges, conditional });
        };
        if !interface_base_has_statically_known_members(store, type_)? {
            return Err(TypeNodeUnavailable::UnsupportedSyntax {
                node: request.root,
                kind: SyntaxKind::ExpressionWithTypeArguments,
            }
            .into());
        }
        if interface_alias_base_members_with_query_context(store, type_, array_targets, query)?
            .is_none()
        {
            return Ok(SourceInterfaceAliasBaseState::Pending { edges, conditional });
        }
        return Ok(SourceInterfaceAliasBaseState::Ready { type_, edges });
    }
    if store.source_node_kind(request.root) == Some(SyntaxKind::ConditionalType) {
        if let Some(metadata) = conditional.as_ref() {
            if metadata.requires_source_result_proof() {
                let Some(query) = query else {
                    return Ok(SourceInterfaceAliasBaseState::Pending { edges, conditional });
                };
                if query.array_targets != array_targets
                    || query.array_targets
                        != Some(CanonicalArrayTargets::from_global_types(query.globals))
                {
                    return Err(invalid());
                }
                let mut matches = query
                    .conditional_results
                    .iter()
                    .filter(|proof| metadata.matches_result_proof(proof));
                let Some(proof) = matches.next() else {
                    return Ok(SourceInterfaceAliasBaseState::Pending { edges, conditional });
                };
                if matches.next().is_some() || Some(proof.result()) != cached {
                    return Err(invalid());
                }
                validate_source_conditional_result(store, proof, query.globals, query.source)
                    .map_err(|_| invalid())?;
                // A callback can invalidate a binding or a populated cache.
                if source_alias_cached_identity(store, request)? != cached
                    || conditional_source_query_request(
                        store,
                        ConditionalQueryKey::Node(request.root),
                        array_targets,
                    )
                    .map_err(|_| invalid())?
                    .is_none_or(|current| !current.matches_result_proof(proof))
                {
                    return Err(invalid());
                }
            } else {
                let alias =
                    conditional_query_alias_with_array_targets(store, request.root, array_targets)
                        .map_err(|_| invalid())?
                        .ok_or_else(invalid)?;
                if store.type_alias(alias).is_none_or(|alias| {
                    alias.symbol() != Some(request.symbol)
                        || alias
                            .type_arguments()
                            .is_some_and(|arguments| !arguments.is_empty())
                }) {
                    return Err(invalid());
                }
            }
        }
    }
    let Some(type_) = cached else {
        return Ok(SourceInterfaceAliasBaseState::Pending { edges, conditional });
    };
    if !matches!(
        super::object_members::validate_resolved_declared_property_object(store, type_),
        super::object_members::DeclaredPropertyObjectValidation::Valid(
            super::object_members::DeclaredPropertyObjectProof::TypeLiteral
        )
    ) {
        return Err(TypeNodeUnavailable::UnsupportedSyntax {
            node: request.root,
            kind: store.source_node_kind(request.root).ok_or_else(invalid)?,
        }
        .into());
    }
    match array_targets {
        Some(targets) => store.validate_cached_array_capability_with_array_targets(targets, type_),
        None => store.validate_cached_array_capability(type_),
    }
    .map_err(|_| invalid())?;
    edges.push(type_);
    if store
        .type_alias_links(request.symbol)
        .and_then(|links| links.declared_type)
        != Some(type_)
    {
        return Ok(SourceInterfaceAliasBaseState::Pending { edges, conditional });
    }
    Ok(SourceInterfaceAliasBaseState::Ready { type_, edges })
}

/// Replays the canonical alias cache with the source formals in declaration order.
pub(super) fn cached_interface_alias_reference(
    store: &CanonicalTypeMapperStore,
    request: &SourceInterfaceAliasBaseRequest,
    array_targets: Option<CanonicalArrayTargets>,
) -> Result<Option<TypeId>, DeclaredTypeError> {
    cached_interface_alias_reference_with_query_context(store, request, array_targets, None)
}

pub(super) fn cached_interface_alias_reference_with_query_context(
    store: &CanonicalTypeMapperStore,
    request: &SourceInterfaceAliasBaseRequest,
    array_targets: Option<CanonicalArrayTargets>,
    query: Option<&SourceInterfaceHeritageQueryContext<'_>>,
) -> Result<Option<TypeId>, DeclaredTypeError> {
    cached_interface_alias_reference_worker(store, request, array_targets, query, false)
        .map(|(type_, _)| type_)
}

pub(super) fn interface_alias_reference_source_proof_is_pending(
    store: &CanonicalTypeMapperStore,
    request: &SourceInterfaceAliasBaseRequest,
    array_targets: Option<CanonicalArrayTargets>,
    query: &SourceInterfaceHeritageQueryContext<'_>,
) -> Result<bool, DeclaredTypeError> {
    cached_interface_alias_reference_worker(store, request, array_targets, Some(query), true)
        .map(|(_, pending)| pending)
}

fn cached_interface_alias_reference_worker(
    store: &CanonicalTypeMapperStore,
    request: &SourceInterfaceAliasBaseRequest,
    array_targets: Option<CanonicalArrayTargets>,
    query: Option<&SourceInterfaceHeritageQueryContext<'_>>,
    allow_source_pending: bool,
) -> Result<(Option<TypeId>, bool), DeclaredTypeError> {
    let invalid = || source_heritage_error(request.root);
    if query.is_some_and(|query| {
        query.array_targets != array_targets
            || array_targets != Some(CanonicalArrayTargets::from_global_types(query.globals))
    }) {
        return Err(invalid());
    }
    let reference = request.reference.ok_or_else(invalid)?;
    if source_interface_alias_reference_request(store, request.symbol, reference)? != *request {
        return Err(invalid());
    }
    let Some(type_) = store
        .type_node_links(reference)
        .and_then(|links| links.resolved_type)
    else {
        return Ok((None, false));
    };
    if store
        .symbol_node_links(reference)
        .and_then(|links| links.resolved_symbol)
        != Some(request.symbol)
    {
        return Err(invalid());
    }
    let source = property_object_alias_identity_source_header(store, request.symbol)
        .map_err(|_| invalid())?;
    let links = store.type_alias_links(request.symbol).ok_or_else(invalid)?;
    let declared = links.declared_type.ok_or_else(invalid)?;
    if super::object_members::cached_planned_type_identity(store, request.rhs) != Some(declared) {
        return Err(invalid());
    }
    let parameters = links.type_parameters.as_deref().unwrap_or_default();
    if parameters.len() != source.parameters.len()
        || parameters
            .iter()
            .zip(&source.parameters)
            .any(|(&type_, &(_, symbol))| {
                super::declared::cached_ordinary_type_parameter_owner(store, type_) != Some(symbol)
            })
    {
        return Err(invalid());
    }
    let mut arguments = request
        .arguments
        .iter()
        .map(|node| {
            super::object_members::cached_planned_type_identity(store, *node).ok_or_else(invalid)
        })
        .collect::<Result<Vec<_>, _>>()?;
    if store
        .intrinsic_bootstrap()
        .is_some_and(|types| types.error_type == type_)
    {
        let mut required = 0;
        for (index, &(declaration, _)) in source.parameters.iter().enumerate() {
            let annotations = store
                .source_type_parameter_annotations(declaration)
                .ok_or_else(invalid)?;
            if annotations.default_type.is_none() {
                required = index + 1;
            }
        }
        if arguments.len() < required || arguments.len() > parameters.len() {
            return Ok((Some(type_), false));
        }
    }
    let provided = arguments.clone();
    if arguments.len() > parameters.len() {
        return Err(invalid());
    }
    for &(parameter, _) in source.parameters.iter().skip(arguments.len()) {
        let default = store
            .source_type_parameter_annotations(parameter)
            .and_then(|annotations| annotations.default_type)
            .and_then(|node| super::object_members::cached_planned_type_identity(store, node))
            .ok_or_else(invalid)?;
        let value = match query {
            Some(query) => super::instantiate::cached_instantiation_with_vector_and_source(
                store,
                default,
                &parameters[..arguments.len()],
                &arguments,
                query.globals,
                query.source,
            ),
            None => super::instantiate::cached_instantiation_with_vector(
                store,
                default,
                &parameters[..arguments.len()],
                &arguments,
                array_targets,
                None,
            ),
        }
        .map_err(|_| invalid())?;
        let value = value.ok_or_else(invalid)?;
        arguments.push(value);
    }
    if parameters.is_empty() {
        return if declared == type_ && links.instantiations.is_none() {
            Ok((Some(type_), false))
        } else {
            Err(invalid())
        };
    }
    let key = super::type_nodes::type_alias_instantiation_cache_key(&provided, None);
    if links
        .instantiations
        .as_ref()
        .and_then(|instances| instances.get(&key))
        != Some(&type_)
    {
        return Err(invalid());
    }
    if allow_source_pending
        && let Some(query) = query
        && let Some(record) = store.type_payload(type_)
        && matches!(record.data(), TypeData::Mapped(_))
    {
        let identity = record
            .alias()
            .and_then(|alias| store.type_alias(alias))
            .ok_or_else(invalid)?;
        if identity.symbol() != Some(request.symbol)
            || identity.type_arguments() != Some(arguments.as_slice())
        {
            return Err(invalid());
        }
        if super::mapped_types::mapped_alias_source_proof_is_pending(
            store,
            type_,
            query.globals,
            query.source,
        )
        .map_err(|_| invalid())?
        {
            return Ok((Some(type_), true));
        }
    }
    let instantiated = match query {
        Some(query) => super::instantiate::cached_instantiation_with_vector_and_source(
            store,
            declared,
            parameters,
            &arguments,
            query.globals,
            query.source,
        ),
        None => super::instantiate::cached_instantiation_with_vector(
            store,
            declared,
            parameters,
            &arguments,
            array_targets,
            None,
        ),
    }
    .map_err(|_| invalid())?;
    if instantiated != Some(type_) {
        return Err(invalid());
    }
    Ok((Some(type_), false))
}

fn interface_alias_result_is_ignored(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
) -> Result<bool, DeclaredTypeError> {
    if store
        .intrinsic_bootstrap()
        .is_some_and(|types| types.error_type == type_)
    {
        return Ok(true);
    }
    Ok(!interface_base_has_statically_known_members(store, type_)?)
}

pub(super) fn source_interface_alias_base_is_ignored(
    store: &CanonicalTypeMapperStore,
    request: &SourceInterfaceAliasBaseRequest,
    array_targets: Option<CanonicalArrayTargets>,
) -> Result<bool, DeclaredTypeError> {
    source_interface_alias_base_is_ignored_with_query_context(store, request, array_targets, None)
}

pub(super) fn source_interface_alias_base_is_ignored_with_query_context(
    store: &CanonicalTypeMapperStore,
    request: &SourceInterfaceAliasBaseRequest,
    array_targets: Option<CanonicalArrayTargets>,
    query: Option<&SourceInterfaceHeritageQueryContext<'_>>,
) -> Result<bool, DeclaredTypeError> {
    if request.reference.is_none() {
        return Ok(false);
    }
    match cached_interface_alias_reference_with_query_context(store, request, array_targets, query)?
    {
        Some(type_) => interface_alias_result_is_ignored(store, type_),
        None => Ok(false),
    }
}

/// Invalid bases remain in the source plan but do not contribute members.
/// A missing query result cannot authorize removal from the base list.
pub(super) fn effective_interface_heritage_bases<'a>(
    store: &CanonicalTypeMapperStore,
    plan: &'a DirectInterfaceHeritagePlan,
    array_targets: Option<CanonicalArrayTargets>,
) -> Result<Vec<&'a DirectInterfaceBasePlan>, DeclaredTypeError> {
    effective_interface_heritage_bases_with_query_context(store, plan, array_targets, None)
}

pub(super) fn effective_interface_heritage_bases_with_query_context<'a>(
    store: &CanonicalTypeMapperStore,
    plan: &'a DirectInterfaceHeritagePlan,
    array_targets: Option<CanonicalArrayTargets>,
    query: Option<&SourceInterfaceHeritageQueryContext<'_>>,
) -> Result<Vec<&'a DirectInterfaceBasePlan>, DeclaredTypeError> {
    let mut bases = Vec::with_capacity(plan.bases.len());
    for base in &plan.bases {
        if base.kind.is_instantiated_alias() {
            let request = source_interface_alias_reference_request(store, base.symbol, base.node)?;
            if request.arguments() != base.type_arguments.as_slice() || !base.defaults.is_empty() {
                return Err(source_heritage_error(base.node));
            }
            if source_interface_alias_base_is_ignored_with_query_context(
                store,
                &request,
                array_targets,
                query,
            )? {
                continue;
            }
        }
        bases.push(base);
    }
    Ok(bases)
}

pub(super) fn effective_source_interface_heritage_bases<'a>(
    store: &CanonicalTypeMapperStore,
    header: &'a SourceInterfaceHeritageHeader,
    array_targets: Option<CanonicalArrayTargets>,
) -> Result<Vec<&'a SourceInterfaceHeritageBase>, DeclaredTypeError> {
    effective_source_interface_heritage_bases_with_query_context(store, header, array_targets, None)
}

pub(super) fn effective_source_interface_heritage_bases_with_query_context<'a>(
    store: &CanonicalTypeMapperStore,
    header: &'a SourceInterfaceHeritageHeader,
    array_targets: Option<CanonicalArrayTargets>,
    query: Option<&SourceInterfaceHeritageQueryContext<'_>>,
) -> Result<Vec<&'a SourceInterfaceHeritageBase>, DeclaredTypeError> {
    let mut bases = Vec::with_capacity(header.bases.len());
    for base in &header.bases {
        if let Some(request) = base.alias.as_ref()
            && source_interface_alias_base_is_ignored_with_query_context(
                store,
                request,
                array_targets,
                query,
            )?
        {
            continue;
        }
        bases.push(base);
    }
    Ok(bases)
}

/// The native base rule depends on mapped keys, not on property value parameters.
pub(super) fn interface_base_has_statically_known_members(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
) -> Result<bool, DeclaredTypeError> {
    fn visit(
        store: &CanonicalTypeMapperStore,
        type_: TypeId,
        active: &mut HashSet<TypeId>,
    ) -> Result<bool, DeclaredTypeError> {
        let invalid = || {
            DeclaredTypeError::from(TypeNodeUnavailable::UnsupportedIntersectionConstituentType(
                type_,
            ))
        };
        if active.len() >= MAX_INTERFACE_HERITAGE_DEPTH || !active.insert(type_) {
            return Err(invalid());
        }
        let record = store.type_payload(type_).ok_or_else(invalid)?;
        let valid = match record.data() {
            TypeData::TypeParameter(parameter) => {
                let bootstrap = store.intrinsic_bootstrap().ok_or_else(invalid)?;
                if let Some(constraint) = parameter.constraint.filter(|constraint| {
                    *constraint != type_
                        && *constraint != bootstrap.no_constraint_type
                        && *constraint != bootstrap.circular_constraint_type
                }) {
                    visit(store, constraint, active)?
                } else {
                    false
                }
            }
            TypeData::Intersection(intersection) => {
                let mut valid = !record
                    .object_flags()
                    .contains(ObjectFlags::IS_NEVER_INTERSECTION);
                for &part in &intersection.intersection.types {
                    valid &= visit(store, part, active)?;
                }
                valid
            }
            TypeData::Mapped(mapped) => {
                let constraint = mapped.constraint_type.ok_or_else(invalid)?;
                let mut keys = vec![constraint];
                let mut seen = HashSet::new();
                let mut generic = false;
                while let Some(key) = keys.pop() {
                    if !seen.insert(key) {
                        continue;
                    }
                    let key = store.type_payload(key).ok_or_else(invalid)?;
                    generic |= key
                        .flags()
                        .intersects(TypeFlags::INSTANTIABLE_NON_PRIMITIVE | TypeFlags::INDEX);
                    match key.data() {
                        TypeData::Union(union) => keys.extend_from_slice(&union.union.types),
                        TypeData::Intersection(intersection) => {
                            keys.extend_from_slice(&intersection.intersection.types)
                        }
                        TypeData::TemplateLiteral(template) => {
                            keys.extend_from_slice(&template.types)
                        }
                        TypeData::StringMapping(mapping) => keys.push(mapping.target),
                        _ => {}
                    }
                }
                if !generic && mapped.name_type.is_some() {
                    super::mapped_types::plan_mapped_type_keys(store, type_)
                        .map_err(|_| invalid())?;
                }
                !generic
            }
            _ => record
                .flags()
                .intersects(TypeFlags::OBJECT | TypeFlags::NON_PRIMITIVE | TypeFlags::ANY),
        };
        assert!(active.remove(&type_));
        Ok(valid)
    }
    visit(store, type_, &mut HashSet::new())
}

pub(super) struct InterfaceAliasBaseMembers {
    pub(super) properties: Vec<SemanticSymbolId>,
    pub(super) indexes: Vec<super::IndexInfoId>,
}

/// Proves the written alias request before exposing its completed members.
pub(super) fn validated_instantiated_interface_base_members(
    store: &CanonicalTypeMapperStore,
    base: &DirectInterfaceBasePlan,
    type_: TypeId,
    array_targets: Option<CanonicalArrayTargets>,
    query: Option<&SourceInterfaceHeritageQueryContext<'_>>,
) -> Option<InterfaceAliasBaseMembers> {
    if !base.kind.is_instantiated_alias() || !base.defaults.is_empty() {
        return None;
    }
    let request = source_interface_alias_reference_request(store, base.symbol, base.node).ok()?;
    if request.arguments() != base.type_arguments.as_slice()
        || !matches!(source_interface_alias_base_state(store, &request, array_targets, query).ok()?,
            SourceInterfaceAliasBaseState::Ready { type_: result, .. } if result == type_)
    {
        return None;
    }
    interface_alias_base_members_with_query_context(store, type_, array_targets, query).ok()?
}

/// Reads only members proved by their existing object, mapped, or intersection provider.
pub(super) fn interface_alias_base_members(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
    array_targets: Option<CanonicalArrayTargets>,
) -> Result<Option<InterfaceAliasBaseMembers>, DeclaredTypeError> {
    interface_alias_base_members_with_query_context(store, type_, array_targets, None)
}

pub(super) fn interface_alias_base_members_with_query_context(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
    array_targets: Option<CanonicalArrayTargets>,
    query: Option<&SourceInterfaceHeritageQueryContext<'_>>,
) -> Result<Option<InterfaceAliasBaseMembers>, DeclaredTypeError> {
    let invalid = || {
        DeclaredTypeError::from(TypeNodeUnavailable::UnsupportedIntersectionConstituentType(
            type_,
        ))
    };
    let record = store.type_payload(type_).ok_or_else(invalid)?;
    let properties = match record.data() {
        TypeData::Mapped(_) => {
            let Some(members) = store
                .validate_mapped_type_relation_endpoint_with_source(
                    type_,
                    array_targets,
                    query.map(|query| (query.globals, query.source)),
                )
                .map_err(|_| invalid())?
            else {
                return Ok(None);
            };
            members.properties().to_vec()
        }
        TypeData::Intersection(_) => {
            if !record
                .object_flags()
                .contains(ObjectFlags::MEMBERS_RESOLVED)
            {
                store
                    .validate_deferred_intersection_type_with_array_targets(type_, array_targets)
                    .map_err(|_| invalid())?;
                return Ok(None);
            }
            let projection = store
                .validate_intersection_type_with_array_targets(type_, array_targets)
                .map_err(|_| invalid())?;
            if projection.reduced_to_never {
                return Err(invalid());
            }
            projection.properties
        }
        _ if super::object_aliases::source_property_object_projection(store, type_)
            .map_err(|_| invalid())?
            .is_some() =>
        {
            let Some(members) = super::instantiated_members::validate_property_object_alias_members_with_array_targets(
                store, type_, array_targets,
            ).map_err(|_| invalid())? else { return Ok(None); };
            members.properties
        }
        _ if super::reference_types::validate_direct_generic_reference(store, type_).is_ok() => {
            let Some(members) = super::instantiated_members::validate_generic_interface_members(
                store,
                type_,
                array_targets,
            )
            .map_err(|_| invalid())?
            else {
                return Ok(None);
            };
            members.properties().to_vec()
        }
        _ if matches!(
            super::object_members::validate_resolved_declared_property_object(store, type_),
            super::object_members::DeclaredPropertyObjectValidation::Valid(_)
        ) =>
        {
            record
                .data()
                .structured()
                .ok_or_else(invalid)?
                .properties
                .clone()
                .unwrap_or_default()
        }
        _ => return Err(invalid()),
    };
    let structured = record.data().structured().ok_or_else(invalid)?;
    if structured.call_signature_count != 0
        || structured
            .signatures
            .as_ref()
            .is_some_and(|signatures| !signatures.is_empty())
    {
        return Err(invalid());
    }
    Ok(Some(InterfaceAliasBaseMembers {
        properties,
        indexes: structured.index_infos.clone().unwrap_or_default(),
    }))
}

/// Uses the existing member providers with the caller's instantiation budget.
pub(super) fn resolve_interface_alias_base_members(
    store: &mut CanonicalTypeMapperStore,
    type_: TypeId,
    array_targets: Option<CanonicalArrayTargets>,
    session: &mut super::instantiate::InstantiationSession,
) -> Result<InterfaceAliasBaseMembers, DeclaredTypeError> {
    resolve_interface_alias_base_members_with_query_context(
        store,
        type_,
        array_targets,
        session,
        None,
    )
}

pub(super) fn resolve_interface_alias_base_members_with_query_context(
    store: &mut CanonicalTypeMapperStore,
    type_: TypeId,
    array_targets: Option<CanonicalArrayTargets>,
    session: &mut super::instantiate::InstantiationSession,
    query: Option<&SourceInterfaceHeritageQueryContext<'_>>,
) -> Result<InterfaceAliasBaseMembers, DeclaredTypeError> {
    fn resolve(
        store: &mut CanonicalTypeMapperStore,
        type_: TypeId,
        array_targets: Option<CanonicalArrayTargets>,
        session: &mut super::instantiate::InstantiationSession,
        active: &mut HashSet<TypeId>,
        query: Option<&SourceInterfaceHeritageQueryContext<'_>>,
    ) -> Result<(), DeclaredTypeError> {
        let invalid = || {
            DeclaredTypeError::from(TypeNodeUnavailable::UnsupportedIntersectionConstituentType(
                type_,
            ))
        };
        if active.len() >= MAX_INTERFACE_HERITAGE_DEPTH || !active.insert(type_) {
            return Err(invalid());
        }
        let record = store.type_payload(type_).ok_or_else(invalid)?;
        if let TypeData::Intersection(intersection) = record.data() {
            let types = intersection.intersection.types.clone();
            for part in types {
                resolve(store, part, array_targets, session, active, query)?;
            }
            store
                .materialize_deferred_intersection_type_with_array_targets(type_, array_targets)
                .map_err(|_| invalid())?;
        } else if matches!(record.data(), TypeData::Mapped(_)) {
            let members = store
                .resolve_mapped_type_members_with_session(
                    type_,
                    super::mapped_types::MappedTypeModifiers::NONE,
                    session,
                )
                .map_err(|_| invalid())?;
            for &property in members.properties() {
                store
                    .resolve_mapped_symbol_type_with_session(property, session)
                    .map_err(|_| invalid())?;
            }
        } else if super::object_aliases::source_property_object_projection(store, type_)
            .map_err(|_| invalid())?
            .is_some()
        {
            super::instantiated_members::resolve_property_object_alias_members_with_array_targets(
                store,
                type_,
                array_targets,
            )
            .map_err(|_| invalid())?;
        } else if super::reference_types::validate_direct_generic_reference(store, type_).is_ok() {
            let members =
                super::instantiated_members::resolve_members_with_array_targets_and_session(
                    store,
                    type_,
                    array_targets,
                    session,
                )
                .map_err(|_| invalid())?;
            for &property in members.properties() {
                super::instantiated_members::demand_instantiated_property_type(
                    store,
                    type_,
                    property,
                    array_targets,
                    session,
                )
                .map_err(|_| invalid())?;
            }
        }
        interface_alias_base_members_with_query_context(store, type_, array_targets, query)?
            .ok_or_else(invalid)?;
        assert!(active.remove(&type_));
        Ok(())
    }
    resolve(
        store,
        type_,
        array_targets,
        session,
        &mut HashSet::new(),
        query,
    )?;
    interface_alias_base_members_with_query_context(store, type_, array_targets, query)?
        .ok_or_else(|| TypeNodeUnavailable::UnsupportedIntersectionConstituentType(type_).into())
}

/// Rechecks source and all populated cache metadata, without completing a base.
pub(super) fn validate_source_interface_heritage_header(
    store: &CanonicalTypeMapperStore,
    actual_type: TypeId,
    header: &SourceInterfaceHeritageHeader,
    array_targets: Option<CanonicalArrayTargets>,
) -> Result<Vec<TypeId>, DeclaredTypeError> {
    validate_source_interface_heritage_header_with_query_context(
        store,
        actual_type,
        header,
        array_targets,
        None,
    )
}

pub(super) fn validate_source_interface_heritage_header_with_query_context(
    store: &CanonicalTypeMapperStore,
    actual_type: TypeId,
    header: &SourceInterfaceHeritageHeader,
    array_targets: Option<CanonicalArrayTargets>,
    query: Option<&SourceInterfaceHeritageQueryContext<'_>>,
) -> Result<Vec<TypeId>, DeclaredTypeError> {
    validate_source_interface_heritage_header_worker(
        store,
        actual_type,
        header,
        array_targets,
        query,
        false,
    )
}

/// Checks cache dependencies without granting access to a pending alias value.
pub(super) fn validate_source_interface_heritage_cache_edges(
    store: &CanonicalTypeMapperStore,
    actual_type: TypeId,
    header: &SourceInterfaceHeritageHeader,
    array_targets: Option<CanonicalArrayTargets>,
    query: Option<&SourceInterfaceHeritageQueryContext<'_>>,
) -> Result<Vec<TypeId>, DeclaredTypeError> {
    validate_source_interface_heritage_header_worker(
        store,
        actual_type,
        header,
        array_targets,
        query,
        true,
    )
}

fn validate_source_interface_heritage_header_worker(
    store: &CanonicalTypeMapperStore,
    actual_type: TypeId,
    header: &SourceInterfaceHeritageHeader,
    array_targets: Option<CanonicalArrayTargets>,
    query: Option<&SourceInterfaceHeritageQueryContext<'_>>,
    allow_source_pending: bool,
) -> Result<Vec<TypeId>, DeclaredTypeError> {
    let invalid = || {
        DeclaredTypeError::from(DeclaredTypeUnavailable::InvalidCachedDeclaredType {
            symbol: header.owner_symbol,
            declared_type: actual_type,
        })
    };
    if !source_heritage_owner_is_exact(store, header.owner_symbol, &header.owner_declarations)
        || !super::structured_members::nongeneric_interface_heritage_type_is_exact(
            store,
            actual_type,
        )
        || store
            .type_payload(actual_type)
            .and_then(|record| record.symbol())
            != Some(header.owner_symbol)
        || !matches!(store.type_payload(actual_type).map(|record| record.data()),
            Some(TypeData::Interface(interface)) if interface.this_type.is_some())
        || super::reference_types::validate_nongeneric_interface_argument_origin(store, actual_type)
            .is_err()
        || !header.bases.iter().any(|base| base.alias.is_some())
    {
        return Err(invalid());
    }
    let mut expected_nodes = Vec::new();
    for &declaration in &header.owner_declarations {
        if store.source_node_kind(declaration) == Some(SyntaxKind::VariableDeclaration) {
            continue;
        }
        let children = store
            .source_direct_children(declaration)
            .ok_or_else(invalid)?;
        if children
            .iter()
            .any(|child| store.source_node_kind(*child) == Some(SyntaxKind::TypeParameter))
        {
            return Err(invalid());
        }
        for clause in children
            .into_iter()
            .filter(|child| store.source_node_kind(*child) == Some(SyntaxKind::HeritageClause))
        {
            for node in store.source_direct_children(clause).ok_or_else(invalid)? {
                expected_nodes.push((declaration, clause, node));
            }
        }
    }
    if expected_nodes.len() != header.bases.len() {
        return Err(invalid());
    }
    let mut edges = Vec::new();
    let mut cached_bases = Vec::new();
    for ((declaration, clause, node), base) in expected_nodes.into_iter().zip(&header.bases) {
        let expected_children = std::iter::once(base.expression)
            .chain(
                base.alias
                    .as_ref()
                    .into_iter()
                    .flat_map(|alias| alias.arguments.iter().copied()),
            )
            .collect::<Vec<_>>();
        if (base.declaration, base.clause, base.node) != (declaration, clause, node)
            || base.symbol == header.owner_symbol
            || store.source_node_kind(node) != Some(SyntaxKind::ExpressionWithTypeArguments)
            || store.source_node_kind(base.expression) != Some(SyntaxKind::Identifier)
            || store.source_node_parent(clause) != Some(SourceNodeParent::Parent(declaration))
            || store.source_node_parent(node) != Some(SourceNodeParent::Parent(clause))
            || store.source_node_parent(base.expression) != Some(SourceNodeParent::Parent(node))
            || store.source_direct_children(node).as_deref() != Some(expected_children.as_slice())
            || !validate_source_heritage_resolution(store, base)
        {
            return Err(invalid());
        }
        let cached = if let Some(request) = &base.alias {
            if request.symbol != base.symbol {
                return Err(invalid());
            }
            if allow_source_pending && request.reference.is_some() {
                let (cached, _) = cached_interface_alias_reference_worker(
                    store,
                    request,
                    array_targets,
                    query,
                    true,
                )?;
                edges.extend(cached);
                cached
            } else {
                let (cached, pending, _) =
                    source_alias_base_metadata(store, request, array_targets, query)?;
                edges.extend(pending);
                cached
            }
        } else {
            let owner = store.symbol(base.symbol).ok_or_else(invalid)?;
            let declarations = owner.declarations().ok_or_else(invalid)?;
            if !source_heritage_owner_is_exact(store, base.symbol, declarations) {
                return Err(invalid());
            }
            let cached = store
                .declared_type_links(base.symbol)
                .and_then(|links| links.declared_type);
            if let Some(type_) = cached {
                if store.type_payload(type_).and_then(|record| record.symbol()) != Some(base.symbol)
                    || !super::structured_members::nongeneric_interface_heritage_type_is_exact(
                        store, type_,
                    )
                {
                    return Err(invalid());
                }
                edges.push(type_);
            }
            cached
        };
        for node in [base.node, base.expression] {
            if store.type_node_links(node).is_some_and(|links| {
                links.outer_type_parameters.is_some()
                    || links
                        .resolved_type
                        .is_some_and(|type_| Some(type_) != cached)
            }) {
                return Err(invalid());
            }
        }
        if base
            .alias
            .as_ref()
            .is_some_and(|alias| alias.reference.is_some())
            && let Some(type_) = cached
            && interface_alias_result_is_ignored(store, type_)?
        {
            continue;
        }
        cached_bases.push((base.symbol, cached));
    }
    let TypeData::Interface(interface) =
        store.type_payload(actual_type).ok_or_else(invalid)?.data()
    else {
        return Err(invalid());
    };
    edges.extend(interface.this_type);
    edges.extend(interface.reference.object.target);
    edges.extend(
        interface
            .reference
            .resolved_type_arguments
            .iter()
            .flatten()
            .copied(),
    );
    if let Some(complete) = store.direct_interface_heritage_provenance(actual_type) {
        if complete.owner_symbol != header.owner_symbol
            || complete.source.as_ref() != Some(header)
            || complete.bases.len() != cached_bases.len()
            || !complete.bases.iter().zip(&cached_bases).all(
                |(&(symbol, type_), &(expected, cached))| {
                    symbol == expected && cached == Some(type_)
                },
            )
            || interface.resolved_base_types.as_deref()
                != Some(
                    complete
                        .bases
                        .iter()
                        .map(|(_, type_)| *type_)
                        .collect::<Vec<_>>()
                        .as_slice(),
                )
            || !interface.base_types_resolved
        {
            return Err(invalid());
        }
    } else if interface.resolved_base_types.is_some() || interface.base_types_resolved {
        return Err(invalid());
    }
    Ok(edges)
}

/// Full publication uses the same header after the normal base queries finish.
pub(super) fn validate_source_interface_heritage_complete_bases(
    store: &CanonicalTypeMapperStore,
    actual_type: TypeId,
    header: &SourceInterfaceHeritageHeader,
    bases: &[(SemanticSymbolId, TypeId)],
    array_targets: Option<CanonicalArrayTargets>,
    query: Option<&SourceInterfaceHeritageQueryContext<'_>>,
) -> Result<(), DeclaredTypeError> {
    let invalid = || {
        DeclaredTypeError::from(DeclaredTypeUnavailable::InvalidCachedDeclaredType {
            symbol: header.owner_symbol,
            declared_type: actual_type,
        })
    };
    validate_source_interface_heritage_header_with_query_context(
        store,
        actual_type,
        header,
        array_targets,
        query,
    )?;
    let source_bases = effective_source_interface_heritage_bases_with_query_context(
        store,
        header,
        array_targets,
        query,
    )?;
    if bases.len() != source_bases.len() {
        return Err(invalid());
    }
    let mut symbols = std::collections::HashMap::new();
    let mut types = HashSet::new();
    for (row, &(symbol, type_)) in source_bases.into_iter().zip(bases) {
        if row.symbol != symbol || type_ == actual_type {
            return Err(invalid());
        }
        let later_distinct = !symbols.is_empty() && !symbols.contains_key(&symbol);
        if let Some(previous) = symbols.insert(symbol, type_) {
            if previous != type_ {
                return Err(invalid());
            }
        } else if !types.insert(type_) {
            return Err(invalid());
        }
        if let Some(request) = &row.alias {
            if !matches!(source_interface_alias_base_state(store, request, array_targets, query)?,
                SourceInterfaceAliasBaseState::Ready { type_: result, .. } if result == type_)
            {
                return Err(invalid());
            }
        } else if store
            .declared_type_links(symbol)
            .and_then(|links| links.declared_type)
            != Some(type_)
            || store.type_payload(type_).and_then(|record| record.symbol()) != Some(symbol)
            || !super::structured_members::nongeneric_interface_heritage_type_is_exact(store, type_)
            || later_distinct
                && !super::structured_members::distinct_later_interface_base_is_supported(
                    store, symbol, type_,
                )
        {
            return Err(invalid());
        }
    }
    // Recheck the source receipt after the borrowed conditional validators return.
    validate_source_interface_heritage_header_with_query_context(
        store,
        actual_type,
        header,
        array_targets,
        query,
    )?;
    Ok(())
}

pub(super) fn plan_direct_interface_heritage(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    declaration: NodeRef,
    owner: SemanticSymbolId,
    clauses: &NodeList,
) -> Result<DirectInterfaceHeritagePlan, DirectInterfaceHeritageError> {
    plan_direct_interface_heritage_inner(
        store,
        host,
        declaration,
        owner,
        clauses,
        &mut HashSet::from([owner]),
        0,
    )
}

/// Proves that an expression-with-arguments is a written interface alias base.
pub(super) fn plan_interface_alias_base_reference(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    node: NodeRef,
) -> Result<Option<DirectInterfaceBasePlan>, DirectInterfaceHeritageError> {
    Ok(plan_interface_type_base_reference(store, host, node)?
        .filter(|base| base.kind.is_instantiated_alias()))
}

pub(super) fn plan_interface_type_base_reference(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    node: NodeRef,
) -> Result<Option<DirectInterfaceBasePlan>, DirectInterfaceHeritageError> {
    let invalid = || DirectInterfaceHeritageError::Invalid;
    let record = preflight_node(store, host, node).map_err(|_| invalid())?;
    let clause = record
        .parent
        .map(|parent| NodeRef::new(node.arena, node.file, parent))
        .ok_or_else(invalid)?;
    let clause_record = preflight_node(store, host, clause).map_err(|_| invalid())?;
    let declaration = clause_record
        .parent
        .map(|parent| NodeRef::new(node.arena, node.file, parent))
        .ok_or_else(invalid)?;
    let record = preflight_node(store, host, declaration).map_err(|_| invalid())?;
    let NodeData::InterfaceDeclaration(interface) = &record.data else {
        return Ok(None);
    };
    let owner = host
        .bound_file(declaration)
        .and_then(|bound| bound.symbol(declaration))
        .and_then(|symbol| store.get_merged_symbol(symbol))
        .ok_or_else(invalid)?;
    let clauses = interface.heritage_clauses.as_ref().ok_or_else(invalid)?;
    let plan = plan_direct_interface_heritage(store, host, declaration, owner, clauses)?;
    Ok(plan
        .bases
        .into_iter()
        .find(|base| {
            base.node == node
                && (base.kind.is_instantiated_alias()
                    || base.kind == DirectInterfaceBaseKind::Interface
                        && !base.type_arguments.is_empty())
        }))
}

fn plan_direct_interface_heritage_inner(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    declaration: NodeRef,
    owner: SemanticSymbolId,
    clauses: &NodeList,
    active: &mut HashSet<SemanticSymbolId>,
    depth: usize,
) -> Result<DirectInterfaceHeritagePlan, DirectInterfaceHeritageError> {
    if !active.contains(&owner) {
        return Err(DirectInterfaceHeritageError::Invalid);
    }
    if depth >= MAX_INTERFACE_HERITAGE_DEPTH {
        return Err(DirectInterfaceHeritageError::Unsupported {
            node: declaration,
            kind: SyntaxKind::InterfaceDeclaration,
        });
    }
    let [clause_id] = clauses.nodes.as_slice() else {
        return Err(DirectInterfaceHeritageError::Unsupported {
            node: declaration,
            kind: SyntaxKind::InterfaceDeclaration,
        });
    };
    let clause = NodeRef::new(declaration.arena, declaration.file, *clause_id);
    let clause_record =
        preflight_node(store, host, clause).map_err(|_| DirectInterfaceHeritageError::Invalid)?;
    let NodeData::HeritageClause(clause_data) = &clause_record.data else {
        return Err(DirectInterfaceHeritageError::Invalid);
    };
    if clauses.has_trailing_comma
        || clause_record.kind != SyntaxKind::HeritageClause
        || clause_record.parent != Some(declaration.node)
        || clause_data.token != SyntaxKind::ExtendsKeyword
        || clause_data.facts != 0
        || clause_data.types.nodes.is_empty()
        || clause_data.types.has_trailing_comma
    {
        return Err(DirectInterfaceHeritageError::Invalid);
    }
    let multiple_nongeneric_bases = clause_data.types.nodes.len() > 2;
    if multiple_nongeneric_bases {
        let declaration_record = preflight_node(store, host, declaration)
            .map_err(|_| DirectInterfaceHeritageError::Invalid)?;
        let owner_record = store
            .symbol(owner)
            .ok_or(DirectInterfaceHeritageError::Invalid)?;
        if !matches!(&declaration_record.data,
            NodeData::InterfaceDeclaration(interface) if interface.type_parameters.is_none())
            || owner_record.flags().contains(SymbolFlags::CLASS)
        {
            return Err(DirectInterfaceHeritageError::Unsupported {
                node: clause,
                kind: SyntaxKind::HeritageClause,
            });
        }
    }

    let mut bases = Vec::with_capacity(clause_data.types.nodes.len());
    let mut seen_nodes = HashSet::with_capacity(clause_data.types.nodes.len());
    let mut seen_symbols = HashSet::with_capacity(clause_data.types.nodes.len());
    let mut previous_end = clause_data.types.range.start;
    for base_id in &clause_data.types.nodes {
        let node = NodeRef::new(declaration.arena, declaration.file, *base_id);
        let node_record =
            preflight_node(store, host, node).map_err(|_| DirectInterfaceHeritageError::Invalid)?;
        let NodeData::ExpressionWithTypeArguments(base) = &node_record.data else {
            return Err(DirectInterfaceHeritageError::Unsupported {
                node,
                kind: node_record.kind,
            });
        };
        if node_record.kind != SyntaxKind::ExpressionWithTypeArguments
            || node_record.parent != Some(clause.node)
            || node_record.range.start < previous_end
            || node_record.range.start < clause_data.types.range.start
            || node_record.range.end > clause_data.types.range.end
            || base.facts != 0
            || !seen_nodes.insert(node)
        {
            return Err(DirectInterfaceHeritageError::Invalid);
        }
        previous_end = node_record.range.end;

        let expression = NodeRef::new(declaration.arena, declaration.file, base.expression);
        let expression_record = preflight_node(store, host, expression)
            .map_err(|_| DirectInterfaceHeritageError::Invalid)?;
        let identifier = match &expression_record.data {
            NodeData::Identifier(identifier)
                if expression_record.kind == SyntaxKind::Identifier =>
            {
                Some(identifier)
            }
            NodeData::PropertyAccessExpression(_)
                if expression_record.kind == SyntaxKind::PropertyAccessExpression =>
            {
                None
            }
            NodeData::QualifiedName(_) if expression_record.kind == SyntaxKind::QualifiedName => {
                None
            }
            _ => {
                return Err(DirectInterfaceHeritageError::Unsupported {
                    node: expression,
                    kind: expression_record.kind,
                });
            }
        };
        if expression_record.parent != Some(node.node)
            || expression_record.range.start < node_record.range.start
            || expression_record.range.end > node_record.range.end
        {
            return Err(DirectInterfaceHeritageError::Invalid);
        }

        let resolved = if let Some(imported) = identifier
            .map(|_| {
                super::source_imports::plan_source_interface_heritage_type_import(
                    store,
                    host,
                    declaration,
                    owner,
                    node,
                )
            })
            .transpose()
            .map_err(|error| match error {
                super::source_imports::SourceImportError::Unsupported(_) => {
                    DirectInterfaceHeritageError::Unsupported {
                        node,
                        kind: node_record.kind,
                    }
                }
                _ => DirectInterfaceHeritageError::Invalid,
            })?
            .flatten()
        {
            Some(imported)
        } else if let Some(identifier) = identifier {
            let (arena, bound) = host
                .source(expression)
                .ok_or(DirectInterfaceHeritageError::Invalid)?;
            let mut callback_host = host
                .name_resolver_host(store)
                .map_err(|_| DirectInterfaceHeritageError::Invalid)?;
            let resolved =
                CanonicalNameResolver::new(arena, bound, store.symbol_store(), &mut callback_host)
                    .map_err(|_| DirectInterfaceHeritageError::Invalid)?
                    .resolve(
                        Some(CanonicalResolutionLocation::Bound(expression)),
                        &identifier.text,
                        SymbolFlags::TYPE,
                        None,
                        false,
                        false,
                    );
            match resolved {
                Ok(symbol) => symbol,
                Err(CanonicalNameResolutionError::AliasResolutionUnavailable(alias)) => {
                    // A real ambient class is outside the source-alias header.
                    // Member demand keeps the class-base limit below.
                    Some(
                        super::source_imports::authenticated_ambient_module_import_alias_target(
                            store, host, expression, alias,
                        )
                        .filter(|target| {
                            store.symbol(*target).is_some_and(|record| {
                                record.flags().contains(SymbolFlags::CLASS)
                            })
                        })
                        .ok_or(DirectInterfaceHeritageError::Invalid)?,
                    )
                }
                Err(_) => return Err(DirectInterfaceHeritageError::Invalid),
            }
        } else {
            Some(resolve_qualified_interface_base(store, host, expression)?)
        };
        let raw = resolved.ok_or(DirectInterfaceHeritageError::Invalid)?;
        let symbol = store
            .get_merged_symbol(raw)
            .ok_or(DirectInterfaceHeritageError::Invalid)?;
        let symbol_record = store
            .symbol(symbol)
            .ok_or(DirectInterfaceHeritageError::Invalid)?;
        let Some(base_declarations) = symbol_record
            .declarations()
            .filter(|declarations| !declarations.is_empty())
        else {
            return Err(DirectInterfaceHeritageError::Unsupported {
                node: expression,
                kind: SyntaxKind::Identifier,
            });
        };
        if active.contains(&symbol) || !seen_symbols.insert(symbol) {
            return Err(DirectInterfaceHeritageError::Unsupported {
                node: expression,
                kind: expression_record.kind,
            });
        }
        let react_array_arguments = match (identifier, base.type_arguments.as_ref()) {
            (Some(identifier), Some(arguments)) if identifier.text == "Array" => {
                authenticate_react_default_library_array_base(
                    store,
                    host,
                    (declaration, owner),
                    (symbol, base_declarations),
                    node,
                    arguments,
                )?
            }
            _ => None,
        };
        let alias_kind = if symbol_record.flags() == SymbolFlags::TYPE_ALIAS {
            if identifier.is_none() {
                return Err(DirectInterfaceHeritageError::Unsupported {
                    node: expression,
                    kind: expression_record.kind,
                });
            }
            let record_arguments = base.type_arguments.as_ref().is_some_and(|arguments| {
                matches!(arguments.nodes.as_slice(), [key, value]
                    if store.source_node_kind(NodeRef::new(node.arena, node.file, *key))
                        == Some(SyntaxKind::StringKeyword)
                        && store.source_node_kind(NodeRef::new(node.arena, node.file, *value))
                            == Some(SyntaxKind::AnyKeyword))
            });
            if identifier.is_some_and(|identifier| identifier.text == "Record")
                && record_arguments
                && clause_data.types.nodes.len() == 1
                && authenticate_record_mapped_alias(store, host, symbol, base_declarations)?
            {
                Some(DirectInterfaceBaseKind::RecordMappedAlias)
            } else if base.type_arguments.is_none()
                && matches!(
                    source_interface_alias_base_request(store, symbol),
                    Ok(Some(_))
                )
                && matches!(
                    preflight_node(store, host, declaration).map(|record| &record.data),
                    Ok(NodeData::InterfaceDeclaration(interface)) if interface.type_parameters.is_none()
                )
            {
                Some(DirectInterfaceBaseKind::NongenericTypeLiteralAlias)
            } else {
                source_interface_alias_reference_request(store, symbol, node)
                    .map_err(|_| DirectInterfaceHeritageError::Invalid)?;
                Some(DirectInterfaceBaseKind::InstantiatedTypeAlias)
            }
        } else {
            None
        };
        let (type_arguments, defaults) =
            match (base.type_arguments.as_ref(), react_array_arguments.as_ref()) {
                (Some(_), Some(arguments)) => (arguments.clone(), Vec::new()),
                (Some(arguments), _)
                    if alias_kind == Some(DirectInterfaceBaseKind::RecordMappedAlias) =>
                {
                    (
                        plan_record_type_arguments(store, host, node, arguments)?,
                        Vec::new(),
                    )
                }
                (arguments, _)
                    if alias_kind == Some(DirectInterfaceBaseKind::InstantiatedTypeAlias) =>
                {
                    (
                        plan_alias_base_arguments(store, host, node, arguments)?,
                        Vec::new(),
                    )
                }
                (arguments, _)
                    if symbol_record.flags().without(SymbolFlags::TRANSIENT)
                        == SymbolFlags::INTERFACE =>
                {
                    plan_interface_type_arguments(
                        store,
                        host,
                        declaration,
                        owner,
                        node,
                        symbol,
                        base_declarations,
                        arguments,
                    )?
                }
                (None, _) => (Vec::new(), Vec::new()),
                (Some(_), _) => {
                    return Err(DirectInterfaceHeritageError::Unsupported {
                        node,
                        kind: SyntaxKind::ExpressionWithTypeArguments,
                    });
                }
            };
        if let Some(kind) = alias_kind {
            bases.push(DirectInterfaceBasePlan {
                node,
                expression,
                symbol,
                kind,
                type_arguments,
                defaults,
            });
            continue;
        }
        if react_array_arguments.is_some() {
            bases.push(DirectInterfaceBasePlan {
                node,
                expression,
                symbol,
                kind: DirectInterfaceBaseKind::DefaultLibraryArray,
                type_arguments,
                defaults,
            });
            continue;
        }
        let interface_value_base =
            symbol_record.flags().without(SymbolFlags::TRANSIENT) != SymbolFlags::INTERFACE;
        if interface_value_base {
            if authenticate_default_library_interface_base(store, host, symbol, base_declarations)?
            {
                bases.push(DirectInterfaceBasePlan {
                    node,
                    expression,
                    symbol,
                    kind: DirectInterfaceBaseKind::DefaultLibraryInterface,
                    type_arguments,
                    defaults,
                });
                continue;
            }
            if !super::object_members::authenticated_nongeneric_global_interface_owner(
                store, symbol,
            ) {
                return Err(DirectInterfaceHeritageError::Unsupported {
                    node: expression,
                    kind: expression_record.kind,
                });
            }
            if super::declared::preflight_class_or_interface_reference(
                store,
                host,
                symbol,
                symbol_record.flags(),
            )
            .map_err(|_| DirectInterfaceHeritageError::Invalid)?
                != 0
            {
                return Err(DirectInterfaceHeritageError::Invalid);
            }
        }
        let mixed_base_owner = if interface_value_base
            && !super::object_members::source_interface_uses_legacy_single_script_value_owner(
                store, symbol,
            ) {
            store
                .source_global_interface_value_owner(symbol)
                .map_err(|_| DirectInterfaceHeritageError::Invalid)?
        } else {
            None
        };
        let mut seen_declarations = HashSet::with_capacity(base_declarations.len());
        for &base_declaration in base_declarations {
            let base_declaration_record = preflight_node(store, host, base_declaration)
                .map_err(|_| DirectInterfaceHeritageError::Invalid)?;
            if interface_value_base
                && mixed_base_owner.as_ref().map_or(
                    symbol_record.value_declaration() == Some(base_declaration),
                    |proof| proof.variables().contains(&base_declaration),
                )
            {
                if base_declaration_record.kind != SyntaxKind::VariableDeclaration
                    || !matches!(
                        &base_declaration_record.data,
                        NodeData::VariableDeclaration(_)
                    )
                    || !host.symbol_matches(store, base_declaration, symbol)
                {
                    return Err(DirectInterfaceHeritageError::Invalid);
                }
                continue;
            }
            let NodeData::InterfaceDeclaration(base_interface) = &base_declaration_record.data
            else {
                return Err(DirectInterfaceHeritageError::Unsupported {
                    node: expression,
                    kind: expression_record.kind,
                });
            };
            if base_declaration_record.kind != SyntaxKind::InterfaceDeclaration
                || base_interface.type_parameters.is_some() == type_arguments.is_empty()
                || !host.symbol_matches(store, base_declaration, symbol)
            {
                return Err(DirectInterfaceHeritageError::Unsupported {
                    node: expression,
                    kind: expression_record.kind,
                });
            }
            if !seen_declarations.insert(base_declaration) {
                return Err(DirectInterfaceHeritageError::Invalid);
            }
            if let Some(inherited) = base_interface.heritage_clauses.as_ref() {
                if !active.insert(symbol) {
                    return Err(DirectInterfaceHeritageError::Unsupported {
                        node: expression,
                        kind: expression_record.kind,
                    });
                }
                let planned = plan_direct_interface_heritage_inner(
                    store,
                    host,
                    base_declaration,
                    symbol,
                    inherited,
                    active,
                    depth + 1,
                );
                assert!(active.remove(&symbol));
                let planned = planned?;
                if planned.bases.iter().any(|base| {
                    !matches!(
                        base.kind,
                        DirectInterfaceBaseKind::Interface
                            | DirectInterfaceBaseKind::NongenericTypeLiteralAlias
                            | DirectInterfaceBaseKind::InstantiatedTypeAlias
                            | DirectInterfaceBaseKind::RecordMappedAlias
                    )
                }) {
                    return Err(DirectInterfaceHeritageError::Unsupported {
                        node: expression,
                        kind: expression_record.kind,
                    });
                }
            }
        }
        bases.push(DirectInterfaceBasePlan {
            node,
            expression,
            symbol,
            kind: DirectInterfaceBaseKind::Interface,
            type_arguments,
            defaults,
        });
    }

    if multiple_nongeneric_bases
        && bases.iter().any(|base| {
            !matches!(
                base.kind,
                DirectInterfaceBaseKind::Interface
                    | DirectInterfaceBaseKind::NongenericTypeLiteralAlias
            ) || !base.type_arguments.is_empty()
                || !base.defaults.is_empty()
        })
    {
        return Err(DirectInterfaceHeritageError::Unsupported {
            node: clause,
            kind: SyntaxKind::HeritageClause,
        });
    }
    Ok(DirectInterfaceHeritagePlan { clause, bases })
}

/// Type arguments are checked by the normal alias query, including defaults and bounds.
fn plan_alias_base_arguments(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    node: NodeRef,
    arguments: Option<&NodeList>,
) -> Result<Vec<NodeRef>, DirectInterfaceHeritageError> {
    let invalid = || DirectInterfaceHeritageError::Invalid;
    let Some(arguments) = arguments else {
        return Ok(Vec::new());
    };
    let record = preflight_node(store, host, node).map_err(|_| invalid())?;
    let NodeData::ExpressionWithTypeArguments(base) = &record.data else {
        return Err(invalid());
    };
    let expression = NodeRef::new(node.arena, node.file, base.expression);
    let mut previous_end = preflight_node(store, host, expression)
        .map_err(|_| invalid())?
        .range
        .end;
    if arguments.nodes.is_empty()
        || arguments.has_trailing_comma
        || arguments.range.start < previous_end
        || arguments.range.end != record.range.end
    {
        return Err(invalid());
    }
    let mut result = Vec::with_capacity(arguments.nodes.len());
    for argument in &arguments.nodes {
        let argument = NodeRef::new(node.arena, node.file, *argument);
        let record = preflight_node(store, host, argument).map_err(|_| invalid())?;
        if record.parent != Some(node.node)
            || record.range.start < previous_end
            || record.range.start <= arguments.range.start
            || record.range.end >= arguments.range.end
            || result.contains(&argument)
        {
            return Err(invalid());
        }
        previous_end = record.range.end;
        result.push(argument);
    }
    Ok(result)
}

#[allow(clippy::too_many_arguments)] // Both interface owners and their exact syntax remain explicit.
fn plan_interface_type_arguments(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    declaration: NodeRef,
    owner: SemanticSymbolId,
    node: NodeRef,
    base: SemanticSymbolId,
    base_declarations: &[NodeRef],
    arguments: Option<&NodeList>,
) -> Result<(Vec<NodeRef>, Vec<DirectInterfaceDefaultArgument>), DirectInterfaceHeritageError> {
    let unsupported = || DirectInterfaceHeritageError::Unsupported {
        node,
        kind: SyntaxKind::ExpressionWithTypeArguments,
    };
    let owner_record = preflight_node(store, host, declaration)
        .map_err(|_| DirectInterfaceHeritageError::Invalid)?;
    let NodeData::InterfaceDeclaration(interface) = &owner_record.data else {
        return Err(DirectInterfaceHeritageError::Invalid);
    };
    let parameters = interface.type_parameters.as_ref();
    let owner_symbol = store
        .symbol(owner)
        .ok_or(DirectInterfaceHeritageError::Invalid)?;
    let merged_nongeneric_class = owner_symbol.flags()
        == SymbolFlags::CLASS | SymbolFlags::INTERFACE
        && parameters.is_none()
        && arguments.is_none()
        && owner_symbol
            .value_declaration()
            .is_some_and(|class_declaration| {
                class_declaration.is_for(declaration.arena, declaration.file)
                    && owner_symbol.declarations().is_some_and(|declarations| {
                        declarations.len() == 2
                            && declarations.contains(&class_declaration)
                            && declarations.contains(&declaration)
                    })
                    && host.symbol_matches(store, class_declaration, owner)
                    && preflight_node(store, host, class_declaration).is_ok_and(|record| {
                        record.kind == SyntaxKind::ClassDeclaration
                            && record.parent == owner_record.parent
                            && matches!(&record.data, NodeData::ClassDeclaration(class)
                            if class.type_parameters.is_none())
                    })
            });
    let merged_nongeneric_value = parameters.is_none()
        && arguments.is_none()
        && owner_symbol.flags().without(SymbolFlags::TRANSIENT)
            == SymbolFlags::INTERFACE | SymbolFlags::FUNCTION_SCOPED_VARIABLE
        && owner_symbol
            .declarations()
            .is_some_and(|declarations| declarations.contains(&declaration))
        && (authenticate_default_library_interface_base(
            store,
            host,
            owner,
            owner_symbol
                .declarations()
                .ok_or(DirectInterfaceHeritageError::Invalid)?,
        )? || super::object_members::authenticated_nongeneric_global_interface_owner(
            store, owner,
        ));
    if owner_record.kind != SyntaxKind::InterfaceDeclaration
        || owner_record.flags.0 != 0
        || !host.symbol_matches(store, declaration, owner)
        || owner_symbol.flags().without(SymbolFlags::TRANSIENT) != SymbolFlags::INTERFACE
            && !merged_nongeneric_class
            && !merged_nongeneric_value
        || owner_symbol.check_flags() != CheckFlags::NONE
        || parameters.is_some_and(|parameters| parameters.nodes.is_empty())
        || arguments
            .is_some_and(|arguments| arguments.has_trailing_comma || arguments.nodes.is_empty())
    {
        return Err(unsupported());
    }

    let mut checked_parameters = HashSet::new();
    let owner_parameters = explicit_type_parameter_symbols(
        store,
        host,
        declaration,
        parameters,
        &mut checked_parameters,
    )
    .map_err(|_| DirectInterfaceHeritageError::Invalid)?;
    if owner_parameters.len() != parameters.map_or(0, |parameters| parameters.nodes.len()) {
        return Err(unsupported());
    }
    if let Some(parameters) = parameters {
        for (parameter, symbol) in parameters.nodes.iter().zip(&owner_parameters) {
            authenticate_heritage_type_parameter(
                store,
                host,
                declaration,
                owner,
                NodeRef::new(declaration.arena, declaration.file, *parameter),
                *symbol,
                node,
            )?;
        }
    }
    let react_namespace = authenticated_react_generic_heritage_namespace(store, owner, base);

    let mut shared_base_parameters: Option<Vec<SemanticSymbolId>> = None;
    let mut defaults: Vec<Option<NodeRef>> = Vec::new();
    for &base_declaration in base_declarations {
        let record = preflight_node(store, host, base_declaration)
            .map_err(|_| DirectInterfaceHeritageError::Invalid)?;
        let NodeData::InterfaceDeclaration(interface) = &record.data else {
            return Err(unsupported());
        };
        let base_parameters = interface.type_parameters.as_ref();
        if record.kind != SyntaxKind::InterfaceDeclaration
            || record.flags.0 != 0
            || !host.symbol_matches(store, base_declaration, base)
            || base_parameters.is_some_and(|parameters| parameters.nodes.is_empty())
        {
            return Err(unsupported());
        }
        let symbols = explicit_type_parameter_symbols(
            store,
            host,
            base_declaration,
            base_parameters,
            &mut checked_parameters,
        )
        .map_err(|_| DirectInterfaceHeritageError::Invalid)?;
        if symbols.len() != base_parameters.map_or(0, |parameters| parameters.nodes.len())
            || shared_base_parameters
                .as_ref()
                .is_some_and(|expected| expected != &symbols)
        {
            return Err(unsupported());
        }
        if shared_base_parameters.is_none() {
            defaults.resize(symbols.len(), None);
        }
        let parameter_nodes =
            base_parameters.map_or(&[][..], |parameters| parameters.nodes.as_slice());
        for (index, (parameter, symbol)) in parameter_nodes.iter().zip(&symbols).enumerate() {
            let parameter = NodeRef::new(base_declaration.arena, base_declaration.file, *parameter);
            authenticate_heritage_type_parameter(
                store,
                host,
                base_declaration,
                base,
                parameter,
                *symbol,
                node,
            )?;
            let parameter_record = preflight_node(store, host, parameter)
                .map_err(|_| DirectInterfaceHeritageError::Invalid)?;
            let NodeData::TypeParameterDeclaration(data) = &parameter_record.data else {
                return Err(DirectInterfaceHeritageError::Invalid);
            };
            if let Some(default) = data.default_type {
                let default = NodeRef::new(parameter.arena, parameter.file, default);
                if react_namespace.is_none() && !owner_parameters.is_empty() {
                    authenticate_concrete_interface_type_argument(store, host, default, 0)?;
                    if heritage_argument_references_parameters(
                        store,
                        host,
                        default,
                        &symbols[index..],
                        0,
                    )? {
                        return Err(unsupported());
                    }
                }
                if let Some(previous) = defaults[index]
                    && !equivalent_heritage_type_argument(store, host, previous, default, 0)?
                {
                    return Err(unsupported());
                }
                defaults[index].get_or_insert(default);
            }
        }
        if shared_base_parameters.is_none() {
            shared_base_parameters = Some(symbols);
        }
    }
    let base_parameters = shared_base_parameters.ok_or_else(unsupported)?;
    let supplied = arguments.map_or(&[][..], |arguments| arguments.nodes.as_slice());
    let minimum = defaults
        .iter()
        .rposition(Option::is_none)
        .map_or(0, |index| index + 1);
    if supplied.len() < minimum || supplied.len() > base_parameters.len() {
        return Err(unsupported());
    }

    let record =
        preflight_node(store, host, node).map_err(|_| DirectInterfaceHeritageError::Invalid)?;
    let NodeData::ExpressionWithTypeArguments(expression) = &record.data else {
        return Err(DirectInterfaceHeritageError::Invalid);
    };
    let expression_node = NodeRef::new(node.arena, node.file, expression.expression);
    let expression_record = preflight_node(store, host, expression_node)
        .map_err(|_| DirectInterfaceHeritageError::Invalid)?;
    if arguments.is_some_and(|arguments| {
        arguments.range.start < expression_record.range.end
            || arguments.range.end != record.range.end
            || arguments.range.start >= arguments.range.end
    }) {
        return Err(DirectInterfaceHeritageError::Invalid);
    }

    let mut planned = Vec::with_capacity(base_parameters.len());
    let mut previous_end = expression_record.range.end;
    for argument in supplied {
        let argument = NodeRef::new(node.arena, node.file, *argument);
        let argument_record = preflight_node(store, host, argument)
            .map_err(|_| DirectInterfaceHeritageError::Invalid)?;
        if argument_record.flags.0 != 0
            || argument_record.parent != Some(node.node)
            || argument_record.range.start < previous_end
            || arguments.is_some_and(|arguments| {
                argument_record.range.start <= arguments.range.start
                    || argument_record.range.end >= arguments.range.end
            })
            || planned.contains(&argument)
        {
            return Err(DirectInterfaceHeritageError::Invalid);
        }
        authenticate_concrete_interface_type_argument(store, host, argument, 0)?;
        if !owner_parameters.is_empty()
            && matches!(
                &argument_record.data,
                NodeData::TypeReferenceNode(reference) if reference.type_arguments.is_some()
            )
            && let Some(namespace) = react_namespace
        {
            authenticate_react_forwarded_interface_argument(
                store,
                host,
                argument,
                node,
                (namespace, owner),
                &owner_parameters,
                0,
            )?;
        }
        previous_end = argument_record.range.end;
        planned.push(argument);
    }
    let mut planned_defaults = Vec::new();
    for (index, default) in defaults.iter().enumerate().skip(planned.len()) {
        let default = default.ok_or_else(unsupported)?;
        let (argument, earlier_parameter) =
            plan_heritage_default_argument(store, host, default, &base_parameters, &planned)?;
        let declaration = preflight_node(store, host, default)
            .map_err(|_| DirectInterfaceHeritageError::Invalid)?
            .parent
            .map(|parent| NodeRef::new(default.arena, default.file, parent))
            .ok_or(DirectInterfaceHeritageError::Invalid)?;
        let planned_default = DirectInterfaceDefaultArgument {
            index,
            parameter: base_parameters[index],
            declaration,
            node: default,
            argument,
            earlier_parameter,
        };
        let resolved = store.declared_type_links(owner)
            .and_then(|links| links.declared_type)
            .and_then(|type_| store.type_payload(type_))
            .is_some_and(|record| matches!(record.data(), TypeData::Interface(interface) if interface.base_types_resolved));
        validate_heritage_default_cache(store, &planned_default, resolved)?;
        planned_defaults.push(planned_default);
        planned.push(argument);
    }
    Ok((planned, planned_defaults))
}

pub(super) fn validate_heritage_default_cache(
    store: &CanonicalTypeMapperStore,
    default: &DirectInterfaceDefaultArgument,
    require_resolved: bool,
) -> Result<(), DirectInterfaceHeritageError> {
    if store.source_node_kind(default.declaration) != Some(SyntaxKind::TypeParameter)
        || store.source_node_parent(default.node)
            != Some(super::store::SourceNodeParent::Parent(default.declaration))
        || store
            .symbol(default.parameter)
            .and_then(|owner| owner.declarations())
            .is_none_or(|declarations| !declarations.contains(&default.declaration))
    {
        return Err(DirectInterfaceHeritageError::Invalid);
    }
    let expected = if let Some(earlier) = default.earlier_parameter {
        store
            .declared_type_links(earlier)
            .and_then(|links| links.declared_type)
    } else {
        super::object_members::cached_planned_type_identity(store, default.node)
    };
    if require_resolved
        && expected.is_none_or(|expected| {
            !store.source_direct_type_annotation_is_exact(default.node, expected)
        })
        || store.type_node_links(default.node).is_some_and(|links| {
            links
                != &super::TypeNodeLinks {
                    resolved_type: links.resolved_type,
                    ..super::TypeNodeLinks::default()
                }
                || links
                    .resolved_type
                    .is_some_and(|cached| Some(cached) != expected)
        })
    {
        return Err(DirectInterfaceHeritageError::Invalid);
    }
    if default.earlier_parameter.is_some_and(|expected| {
        store
            .symbol_node_links(default.node)
            .and_then(|links| links.resolved_symbol)
            .is_some_and(|symbol| store.get_merged_symbol(symbol) != Some(expected))
    }) {
        return Err(DirectInterfaceHeritageError::Invalid);
    }
    if let Some(parameter) = store
        .declared_type_links(default.parameter)
        .and_then(|links| links.declared_type)
    {
        let Some(TypeData::TypeParameter(data)) = store
            .type_payload(parameter)
            .map(super::type_records::TypeRecord::data)
        else {
            return Err(DirectInterfaceHeritageError::Invalid);
        };
        if super::declared::cached_ordinary_type_parameter_owner(store, parameter)
            != Some(default.parameter)
            || data
                .resolved_default_type
                .is_some_and(|cached| Some(cached) != expected)
            || require_resolved && data.resolved_default_type != expected
        {
            return Err(DirectInterfaceHeritageError::Invalid);
        }
    } else if require_resolved {
        return Err(DirectInterfaceHeritageError::Invalid);
    }
    Ok(())
}

fn equivalent_heritage_type_argument(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    left: NodeRef,
    right: NodeRef,
    depth: usize,
) -> Result<bool, DirectInterfaceHeritageError> {
    if depth >= MAX_INTERFACE_HERITAGE_DEPTH {
        return Ok(false);
    }
    let left_record =
        preflight_node(store, host, left).map_err(|_| DirectInterfaceHeritageError::Invalid)?;
    let right_record =
        preflight_node(store, host, right).map_err(|_| DirectInterfaceHeritageError::Invalid)?;
    if left_record.flags.0 != 0 || right_record.flags.0 != 0 {
        return Err(DirectInterfaceHeritageError::Invalid);
    }
    if left_record.kind.is_keyword_type() {
        return Ok(left_record.kind == right_record.kind
            && matches!(left_record.data, NodeData::KeywordTypeNode(_))
            && matches!(right_record.data, NodeData::KeywordTypeNode(_)));
    }
    let (NodeData::TypeReferenceNode(left_data), NodeData::TypeReferenceNode(right_data)) =
        (&left_record.data, &right_record.data)
    else {
        return Ok(false);
    };
    authenticate_concrete_interface_type_argument(store, host, left, depth)?;
    authenticate_concrete_interface_type_argument(store, host, right, depth)?;
    let mut resolver = host
        .name_resolver_host(store)
        .map_err(|_| DirectInterfaceHeritageError::Invalid)?;
    let left_symbol = resolver
        .resolve_entity_name(
            NodeRef::new(left.arena, left.file, left_data.type_name),
            SymbolFlags::TYPE,
        )
        .map_err(|_| DirectInterfaceHeritageError::Invalid)?
        .and_then(|symbol| store.get_merged_symbol(symbol));
    let right_symbol = resolver
        .resolve_entity_name(
            NodeRef::new(right.arena, right.file, right_data.type_name),
            SymbolFlags::TYPE,
        )
        .map_err(|_| DirectInterfaceHeritageError::Invalid)?
        .and_then(|symbol| store.get_merged_symbol(symbol));
    if left_symbol.is_none() || left_symbol != right_symbol {
        return Ok(false);
    }
    let left_arguments = left_data
        .type_arguments
        .as_ref()
        .map_or(&[][..], |arguments| arguments.nodes.as_slice());
    let right_arguments = right_data
        .type_arguments
        .as_ref()
        .map_or(&[][..], |arguments| arguments.nodes.as_slice());
    if left_arguments.len() != right_arguments.len() {
        return Ok(false);
    }
    for (left_argument, right_argument) in left_arguments.iter().zip(right_arguments) {
        if !equivalent_heritage_type_argument(
            store,
            host,
            NodeRef::new(left.arena, left.file, *left_argument),
            NodeRef::new(right.arena, right.file, *right_argument),
            depth + 1,
        )? {
            return Ok(false);
        }
    }
    Ok(true)
}

fn plan_heritage_default_argument(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    default: NodeRef,
    parameters: &[SemanticSymbolId],
    arguments: &[NodeRef],
) -> Result<(NodeRef, Option<SemanticSymbolId>), DirectInterfaceHeritageError> {
    authenticate_concrete_interface_type_argument(store, host, default, 0)?;
    let unsupported = || DirectInterfaceHeritageError::Unsupported {
        node: default,
        kind: store
            .source_node_kind(default)
            .unwrap_or(SyntaxKind::TypeReference),
    };
    let record =
        preflight_node(store, host, default).map_err(|_| DirectInterfaceHeritageError::Invalid)?;
    if let NodeData::TypeReferenceNode(reference) = &record.data {
        let mut resolver = host
            .name_resolver_host(store)
            .map_err(|_| DirectInterfaceHeritageError::Invalid)?;
        let symbol = resolver
            .resolve_entity_name(
                NodeRef::new(default.arena, default.file, reference.type_name),
                SymbolFlags::TYPE,
            )
            .map_err(|_| unsupported())?
            .and_then(|symbol| store.get_merged_symbol(symbol))
            .ok_or_else(unsupported)?;
        if let Some(position) = parameters.iter().position(|parameter| *parameter == symbol) {
            // A direct default reuses the earlier argument. Nested substitutions need a mapper.
            return arguments
                .get(position)
                .copied()
                .map(|argument| (argument, Some(symbol)))
                .ok_or_else(unsupported);
        }
    }
    if heritage_argument_references_parameters(store, host, default, parameters, 0)? {
        return Err(unsupported());
    }
    Ok((default, None))
}

fn heritage_argument_references_parameters(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    argument: NodeRef,
    parameters: &[SemanticSymbolId],
    depth: usize,
) -> Result<bool, DirectInterfaceHeritageError> {
    if depth >= MAX_INTERFACE_HERITAGE_DEPTH {
        return Err(DirectInterfaceHeritageError::Unsupported {
            node: argument,
            kind: SyntaxKind::TypeReference,
        });
    }
    let record =
        preflight_node(store, host, argument).map_err(|_| DirectInterfaceHeritageError::Invalid)?;
    let NodeData::TypeReferenceNode(reference) = &record.data else {
        return Ok(false);
    };
    let mut resolver = host
        .name_resolver_host(store)
        .map_err(|_| DirectInterfaceHeritageError::Invalid)?;
    let symbol = resolver
        .resolve_entity_name(
            NodeRef::new(argument.arena, argument.file, reference.type_name),
            SymbolFlags::TYPE,
        )
        .map_err(|_| DirectInterfaceHeritageError::Invalid)?
        .and_then(|symbol| store.get_merged_symbol(symbol))
        .ok_or(DirectInterfaceHeritageError::Invalid)?;
    if parameters.contains(&symbol) {
        return Ok(true);
    }
    if let Some(arguments) = reference.type_arguments.as_ref() {
        for nested in &arguments.nodes {
            if heritage_argument_references_parameters(
                store,
                host,
                NodeRef::new(argument.arena, argument.file, *nested),
                parameters,
                depth + 1,
            )? {
                return Ok(true);
            }
        }
    }
    Ok(false)
}

fn authenticated_react_generic_heritage_namespace(
    store: &CanonicalTypeMapperStore,
    owner: SemanticSymbolId,
    base: SemanticSymbolId,
) -> Option<SemanticSymbolId> {
    let namespace = store.get_parent_of_symbol(owner)?;
    let namespace_record = store.symbol(namespace)?;
    let exports = namespace_record
        .exports()
        .and_then(|exports| store.symbol_table(exports))?;
    if namespace_record.name().as_utf8() != Some("React")
        || !namespace_record.flags().intersects(SymbolFlags::NAMESPACE)
        || namespace_record.check_flags() != CheckFlags::NONE
        || store.get_merged_symbol(namespace) != Some(namespace)
        || store.get_parent_of_symbol(base) != Some(namespace)
        || [owner, base].into_iter().any(|symbol| {
            store.symbol(symbol).is_none_or(|record| {
                record.flags().without(SymbolFlags::TRANSIENT) != SymbolFlags::INTERFACE
                    || record.check_flags() != CheckFlags::NONE
                    || exports
                        .get(record.name())
                        .and_then(|export| store.get_merged_symbol(export))
                        != Some(symbol)
            })
        })
    {
        return None;
    }
    Some(namespace)
}

#[allow(clippy::too_many_arguments)] // Nested arguments retain their exact React namespace and owner.
fn authenticate_react_forwarded_interface_argument(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    argument: NodeRef,
    heritage: NodeRef,
    (namespace, owner): (SemanticSymbolId, SemanticSymbolId),
    owner_parameters: &[SemanticSymbolId],
    depth: usize,
) -> Result<(), DirectInterfaceHeritageError> {
    let unsupported = || DirectInterfaceHeritageError::Unsupported {
        node: heritage,
        kind: SyntaxKind::ExpressionWithTypeArguments,
    };
    if depth >= MAX_REACT_FORWARDED_INTERFACE_ARGUMENT_DEPTH {
        return Err(unsupported());
    }
    let record =
        preflight_node(store, host, argument).map_err(|_| DirectInterfaceHeritageError::Invalid)?;
    let NodeData::TypeReferenceNode(reference) = &record.data else {
        return Err(unsupported());
    };
    let name = NodeRef::new(argument.arena, argument.file, reference.type_name);
    let name_record =
        preflight_node(store, host, name).map_err(|_| DirectInterfaceHeritageError::Invalid)?;
    let NodeData::Identifier(identifier) = &name_record.data else {
        return Err(unsupported());
    };
    if record.kind != SyntaxKind::TypeReference
        || record.flags.0 != 0
        || name_record.kind != SyntaxKind::Identifier
        || name_record.flags.0 != 0
        || name_record.parent != Some(argument.node)
        || identifier.flow_node.is_some()
    {
        return Err(unsupported());
    }
    let mut resolver = host
        .name_resolver_host(store)
        .map_err(|_| DirectInterfaceHeritageError::Invalid)?;
    let symbol = resolver
        .resolve_entity_name(name, SymbolFlags::TYPE)
        .map_err(|_| unsupported())?
        .and_then(|symbol| store.get_merged_symbol(symbol))
        .ok_or_else(unsupported)?;
    if store
        .symbol(symbol)
        .and_then(|symbol| symbol.name().as_utf8())
        != Some(identifier.text.as_str())
    {
        return Err(unsupported());
    }

    let Some(arguments) = reference.type_arguments.as_ref() else {
        return if owner_parameters.contains(&symbol)
            && store.get_parent_of_symbol(symbol) == Some(owner)
        {
            Ok(())
        } else {
            Err(unsupported())
        };
    };
    let Some(interface) = store.symbol(symbol) else {
        return Err(DirectInterfaceHeritageError::Invalid);
    };
    let exported = store
        .symbol(namespace)
        .and_then(ts_binder::semantic::Symbol::exports)
        .and_then(|exports| store.symbol_table(exports))
        .and_then(|exports| exports.get(interface.name()))
        .and_then(|export| store.get_merged_symbol(export));
    if symbol == owner
        || store.get_parent_of_symbol(symbol) != Some(namespace)
        || interface.flags().without(SymbolFlags::TRANSIENT) != SymbolFlags::INTERFACE
        || interface.check_flags() != CheckFlags::NONE
        || exported != Some(symbol)
        || arguments.nodes.is_empty()
        || arguments.has_trailing_comma
    {
        return Err(unsupported());
    }
    for nested in &arguments.nodes {
        let nested = NodeRef::new(argument.arena, argument.file, *nested);
        if preflight_node(store, host, nested)
            .map_err(|_| DirectInterfaceHeritageError::Invalid)?
            .parent
            != Some(argument.node)
        {
            return Err(DirectInterfaceHeritageError::Invalid);
        }
        authenticate_react_forwarded_interface_argument(
            store,
            host,
            nested,
            heritage,
            (namespace, owner),
            owner_parameters,
            depth + 1,
        )?;
    }
    Ok(())
}

#[allow(clippy::too_many_arguments)] // Concrete instantiation retains both canonical owners.
fn plan_concrete_interface_type_arguments(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    declaration: NodeRef,
    owner: SemanticSymbolId,
    node: NodeRef,
    base: SemanticSymbolId,
    base_declarations: &[NodeRef],
    arguments: &NodeList,
) -> Result<Vec<NodeRef>, DirectInterfaceHeritageError> {
    let unsupported = || DirectInterfaceHeritageError::Unsupported {
        node,
        kind: SyntaxKind::ExpressionWithTypeArguments,
    };
    let owner_record = preflight_node(store, host, declaration)
        .map_err(|_| DirectInterfaceHeritageError::Invalid)?;
    let NodeData::InterfaceDeclaration(interface) = &owner_record.data else {
        return Err(DirectInterfaceHeritageError::Invalid);
    };
    let owner_symbol = store
        .symbol(owner)
        .ok_or(DirectInterfaceHeritageError::Invalid)?;
    if owner_record.kind != SyntaxKind::InterfaceDeclaration
        || owner_record.flags.0 != 0
        || interface.type_parameters.is_some()
        || !host.symbol_matches(store, declaration, owner)
        || owner_symbol.flags().without(SymbolFlags::TRANSIENT) != SymbolFlags::INTERFACE
        || owner_symbol.check_flags() != CheckFlags::NONE
        || arguments.nodes.is_empty()
        || arguments.has_trailing_comma
    {
        return Err(unsupported());
    }

    let mut checked_parameters = HashSet::new();
    let mut shared_base_parameters: Option<Vec<SemanticSymbolId>> = None;
    for &base_declaration in base_declarations {
        let record = preflight_node(store, host, base_declaration)
            .map_err(|_| DirectInterfaceHeritageError::Invalid)?;
        let NodeData::InterfaceDeclaration(interface) = &record.data else {
            return Err(unsupported());
        };
        let Some(parameters) = interface.type_parameters.as_ref() else {
            return Err(unsupported());
        };
        if record.kind != SyntaxKind::InterfaceDeclaration
            || record.flags.0 != 0
            || !host.symbol_matches(store, base_declaration, base)
            || parameters.has_trailing_comma
            || parameters.nodes.len() != arguments.nodes.len()
        {
            return Err(unsupported());
        }
        let symbols = explicit_type_parameter_symbols(
            store,
            host,
            base_declaration,
            Some(parameters),
            &mut checked_parameters,
        )
        .map_err(|_| DirectInterfaceHeritageError::Invalid)?;
        if symbols.len() != arguments.nodes.len()
            || shared_base_parameters
                .as_ref()
                .is_some_and(|expected| expected != &symbols)
        {
            return Err(unsupported());
        }
        for (parameter, symbol) in parameters.nodes.iter().zip(&symbols) {
            authenticate_heritage_type_parameter(
                store,
                host,
                base_declaration,
                base,
                NodeRef::new(base_declaration.arena, base_declaration.file, *parameter),
                *symbol,
                node,
            )?;
        }
        if shared_base_parameters.is_none() {
            shared_base_parameters = Some(symbols);
        }
    }

    let record =
        preflight_node(store, host, node).map_err(|_| DirectInterfaceHeritageError::Invalid)?;
    let NodeData::ExpressionWithTypeArguments(expression) = &record.data else {
        return Err(DirectInterfaceHeritageError::Invalid);
    };
    let expression_node = NodeRef::new(node.arena, node.file, expression.expression);
    let expression_record = preflight_node(store, host, expression_node)
        .map_err(|_| DirectInterfaceHeritageError::Invalid)?;
    if arguments.range.start < expression_record.range.end
        || arguments.range.end != record.range.end
        || arguments.range.start >= arguments.range.end
    {
        return Err(DirectInterfaceHeritageError::Invalid);
    }

    let mut planned = Vec::with_capacity(arguments.nodes.len());
    let mut previous_end = expression_record.range.end;
    for argument in &arguments.nodes {
        let argument = NodeRef::new(node.arena, node.file, *argument);
        let argument_record = preflight_node(store, host, argument)
            .map_err(|_| DirectInterfaceHeritageError::Invalid)?;
        if argument_record.parent != Some(node.node)
            || argument_record.range.start < previous_end
            || argument_record.range.start <= arguments.range.start
            || argument_record.range.end >= arguments.range.end
            || planned.contains(&argument)
        {
            return Err(DirectInterfaceHeritageError::Invalid);
        }
        authenticate_concrete_interface_type_argument(store, host, argument, 0)?;
        previous_end = argument_record.range.end;
        planned.push(argument);
    }
    Ok(planned)
}

#[allow(clippy::too_many_lines)] // Interface and alias parameters keep their separate source owners.
fn authenticate_concrete_interface_type_argument(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    argument: NodeRef,
    depth: usize,
) -> Result<(), DirectInterfaceHeritageError> {
    let unsupported = || DirectInterfaceHeritageError::Unsupported {
        node: argument,
        kind: store
            .source_node_kind(argument)
            .unwrap_or(SyntaxKind::ExpressionWithTypeArguments),
    };
    if depth >= MAX_INTERFACE_HERITAGE_DEPTH {
        return Err(unsupported());
    }
    let record =
        preflight_node(store, host, argument).map_err(|_| DirectInterfaceHeritageError::Invalid)?;
    if record.flags.0 != 0 {
        return Err(DirectInterfaceHeritageError::Invalid);
    }
    let NodeData::TypeReferenceNode(reference) = &record.data else {
        return if record.kind.is_keyword_type()
            && matches!(record.data, NodeData::KeywordTypeNode(_))
        {
            Ok(())
        } else {
            Err(unsupported())
        };
    };
    if record.kind != SyntaxKind::TypeReference {
        return Err(DirectInterfaceHeritageError::Invalid);
    }

    let name = NodeRef::new(argument.arena, argument.file, reference.type_name);
    let name_record =
        preflight_node(store, host, name).map_err(|_| DirectInterfaceHeritageError::Invalid)?;
    let valid_name = match &name_record.data {
        NodeData::Identifier(identifier) => {
            name_record.kind == SyntaxKind::Identifier
                && identifier.flow_node.is_none()
                && !identifier.text.is_empty()
        }
        NodeData::QualifiedName(qualified) => {
            name_record.kind == SyntaxKind::QualifiedName
                && qualified.flow_node.is_none()
                && qualified.facts == 0
        }
        _ => false,
    };
    if name_record.flags.0 != 0 || name_record.parent != Some(argument.node) || !valid_name {
        return Err(unsupported());
    }
    let mut callback_host = host
        .name_resolver_host(store)
        .map_err(|_| DirectInterfaceHeritageError::Invalid)?;
    let symbol = callback_host
        .resolve_entity_name(name, SymbolFlags::TYPE)
        .map_err(|_| unsupported())?
        .and_then(|symbol| store.get_merged_symbol(symbol))
        .ok_or_else(unsupported)?;
    let owner = store
        .symbol(symbol)
        .ok_or(DirectInterfaceHeritageError::Invalid)?;
    if !owner.flags().intersects(SymbolFlags::TYPE) {
        return Err(unsupported());
    }

    if let Some(arguments) = reference.type_arguments.as_ref() {
        if owner.flags() == SymbolFlags::TYPE_ALIAS {
            authenticate_property_object_alias_argument(
                store, host, argument, name, symbol, arguments,
            )?;
        } else {
            let declarations = owner.declarations().ok_or_else(unsupported)?;
            let Some(declaration) = declarations.iter().find_map(|declaration| {
                let record = host.node(*declaration)?;
                let NodeData::InterfaceDeclaration(interface) = &record.data else {
                    return None;
                };
                Some((*declaration, interface.type_parameters.as_ref()?))
            }) else {
                return Err(unsupported());
            };
            if arguments.nodes.is_empty()
                || arguments.has_trailing_comma
                || declaration.1.nodes.len() != arguments.nodes.len()
                || !host.symbol_matches(store, declaration.0, symbol)
                || arguments.range.start < name_record.range.end
                || arguments.range.end != record.range.end
            {
                return Err(unsupported());
            }
            let mut checked_parameters = HashSet::new();
            let parameters = explicit_type_parameter_symbols(
                store,
                host,
                declaration.0,
                Some(declaration.1),
                &mut checked_parameters,
            )
            .map_err(|_| DirectInterfaceHeritageError::Invalid)?;
            if parameters.len() != arguments.nodes.len() {
                return Err(unsupported());
            }
            for (parameter, parameter_symbol) in declaration.1.nodes.iter().zip(&parameters) {
                authenticate_heritage_type_parameter(
                    store,
                    host,
                    declaration.0,
                    symbol,
                    NodeRef::new(declaration.0.arena, declaration.0.file, *parameter),
                    *parameter_symbol,
                    argument,
                )?;
            }
        }
        let mut previous_end = name_record.range.end;
        for nested in &arguments.nodes {
            let nested = NodeRef::new(argument.arena, argument.file, *nested);
            let nested_record = preflight_node(store, host, nested)
                .map_err(|_| DirectInterfaceHeritageError::Invalid)?;
            if nested_record.parent != Some(argument.node)
                || nested_record.range.start < previous_end
                || nested_record.range.start <= arguments.range.start
                || nested_record.range.end >= arguments.range.end
            {
                return Err(DirectInterfaceHeritageError::Invalid);
            }
            authenticate_concrete_interface_type_argument(store, host, nested, depth + 1)?;
            previous_end = nested_record.range.end;
        }
    }
    Ok(())
}

fn authenticate_property_object_alias_argument(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    argument: NodeRef,
    name: NodeRef,
    symbol: SemanticSymbolId,
    arguments: &NodeList,
) -> Result<(), DirectInterfaceHeritageError> {
    let unsupported = || DirectInterfaceHeritageError::Unsupported {
        node: argument,
        kind: SyntaxKind::TypeReference,
    };
    let Some([declaration]) = store
        .symbol(symbol)
        .and_then(ts_binder::semantic::Symbol::declarations)
    else {
        return Err(unsupported());
    };
    let record = preflight_node(store, host, *declaration)
        .map_err(|_| DirectInterfaceHeritageError::Invalid)?;
    let NodeData::TypeAliasDeclaration(alias) = &record.data else {
        return Err(unsupported());
    };
    let Some(parameters) = alias.type_parameters.as_ref() else {
        return Err(unsupported());
    };
    if record.kind != SyntaxKind::TypeAliasDeclaration
        || record.flags.0 != 0
        || !host.symbol_matches(store, *declaration, symbol)
    {
        return Err(unsupported());
    }
    let mut rhs = NodeRef::new(declaration.arena, declaration.file, alias.type_);
    let mut seen = HashSet::new();
    loop {
        if !seen.insert(rhs) {
            return Err(DirectInterfaceHeritageError::Invalid);
        }
        let record =
            preflight_node(store, host, rhs).map_err(|_| DirectInterfaceHeritageError::Invalid)?;
        if record.kind != SyntaxKind::ParenthesizedType {
            break;
        }
        let NodeData::ParenthesizedTypeNode(wrapper) = &record.data else {
            return Err(DirectInterfaceHeritageError::Invalid);
        };
        if record.flags.0 != 0 {
            return Err(DirectInterfaceHeritageError::Invalid);
        }
        rhs = NodeRef::new(rhs.arena, rhs.file, wrapper.type_);
    }
    let header = property_object_alias_source_header(store, rhs)
        .map_err(|_| DirectInterfaceHeritageError::Invalid)?
        .ok_or_else(unsupported)?;
    let name_record =
        preflight_node(store, host, name).map_err(|_| DirectInterfaceHeritageError::Invalid)?;
    let argument_record =
        preflight_node(store, host, argument).map_err(|_| DirectInterfaceHeritageError::Invalid)?;
    if arguments.nodes.is_empty()
        || arguments.has_trailing_comma
        || parameters.nodes.len() != arguments.nodes.len()
        || header.parameters.len() != arguments.nodes.len()
        || header.alias_declaration != *declaration
        || header.alias_symbol != symbol
        || arguments.range.start < name_record.range.end
        || arguments.range.end != argument_record.range.end
    {
        return Err(unsupported());
    }
    let mut checked_parameters = HashSet::new();
    let symbols = explicit_type_parameter_symbols(
        store,
        host,
        *declaration,
        Some(parameters),
        &mut checked_parameters,
    )
    .map_err(|_| DirectInterfaceHeritageError::Invalid)?;
    if symbols.len() != header.parameters.len()
        || parameters
            .nodes
            .iter()
            .zip(&symbols)
            .zip(&header.parameters)
            .any(
                |((&parameter, &symbol), &(source_parameter, source_symbol))| {
                    NodeRef::new(declaration.arena, declaration.file, parameter) != source_parameter
                        || symbol != source_symbol
                },
            )
    {
        return Err(DirectInterfaceHeritageError::Invalid);
    }
    Ok(())
}

#[allow(clippy::too_many_arguments)] // The declaration, canonical owner, and failure anchor differ.
fn authenticate_heritage_type_parameter(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    declaration: NodeRef,
    owner: SemanticSymbolId,
    parameter: NodeRef,
    symbol: SemanticSymbolId,
    heritage: NodeRef,
) -> Result<NodeRef, DirectInterfaceHeritageError> {
    let unsupported = || DirectInterfaceHeritageError::Unsupported {
        node: heritage,
        kind: SyntaxKind::ExpressionWithTypeArguments,
    };
    let record = preflight_node(store, host, parameter)
        .map_err(|_| DirectInterfaceHeritageError::Invalid)?;
    let NodeData::TypeParameterDeclaration(data) = &record.data else {
        return Err(DirectInterfaceHeritageError::Invalid);
    };
    let name = NodeRef::new(parameter.arena, parameter.file, data.name);
    let name_record =
        preflight_node(store, host, name).map_err(|_| DirectInterfaceHeritageError::Invalid)?;
    let NodeData::Identifier(identifier) = &name_record.data else {
        return Err(DirectInterfaceHeritageError::Invalid);
    };
    let symbol_record = store
        .symbol(symbol)
        .ok_or(DirectInterfaceHeritageError::Invalid)?;
    let members = store
        .symbol(owner)
        .and_then(ts_binder::semantic::Symbol::members)
        .and_then(|members| store.symbol_table(members));
    if record.kind != SyntaxKind::TypeParameter
        || record.flags.0 != 0
        || record.parent != Some(declaration.node)
        || data.expression.is_some()
        || data.modifiers.is_some()
        || data.symbol.is_some()
        || name_record.kind != SyntaxKind::Identifier
        || name_record.flags.0 != 0
        || name_record.parent != Some(parameter.node)
        || identifier.flow_node.is_some()
        || identifier.text.is_empty()
        || symbol_record.flags().without(SymbolFlags::TRANSIENT) != SymbolFlags::TYPE_PARAMETER
        || symbol_record.check_flags() != CheckFlags::NONE
        || symbol_record.name().as_utf8() != Some(identifier.text.as_str())
        || !host.symbol_matches(store, parameter, symbol)
        || store.get_parent_of_symbol(symbol) != Some(owner)
        || members
            .and_then(|members| members.get(symbol_record.name()))
            .and_then(|member| store.get_merged_symbol(member))
            != Some(symbol)
    {
        return Err(unsupported());
    }
    for annotation in [data.constraint, data.default_type].into_iter().flatten() {
        let annotation = NodeRef::new(parameter.arena, parameter.file, annotation);
        let annotation_record = preflight_node(store, host, annotation)
            .map_err(|_| DirectInterfaceHeritageError::Invalid)?;
        if annotation_record.parent != Some(parameter.node)
            || annotation_record.range.start < record.range.start
            || annotation_record.range.end > record.range.end
        {
            return Err(DirectInterfaceHeritageError::Invalid);
        }
    }
    Ok(name)
}

#[allow(clippy::too_many_lines)] // React ownership and the merged global Array are one proof.
fn authenticate_react_default_library_array_base(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    (declaration, owner): (NodeRef, SemanticSymbolId),
    (base, base_declarations): (SemanticSymbolId, &[NodeRef]),
    node: NodeRef,
    type_argument_list: &NodeList,
) -> Result<Option<Vec<NodeRef>>, DirectInterfaceHeritageError> {
    let derived = store
        .symbol(owner)
        .ok_or(DirectInterfaceHeritageError::Invalid)?;
    let Some(namespace) = store.get_parent_of_symbol(owner) else {
        return Ok(None);
    };
    let Some(namespace_owner) = store.symbol(namespace) else {
        return Err(DirectInterfaceHeritageError::Invalid);
    };
    let Some(exports) = namespace_owner
        .exports()
        .and_then(|exports| store.symbol_table(exports))
    else {
        return Ok(None);
    };
    let Some(bound) = host.bound_file(declaration) else {
        return Err(DirectInterfaceHeritageError::Invalid);
    };
    let Some(facts) = bound.source_facts() else {
        return Err(DirectInterfaceHeritageError::Invalid);
    };
    let derived_record = preflight_node(store, host, declaration)
        .map_err(|_| DirectInterfaceHeritageError::Invalid)?;
    let NodeData::InterfaceDeclaration(interface) = &derived_record.data else {
        return Ok(None);
    };
    if !facts.is_declaration_file()
        || facts.is_default_library()
        || derived_record.kind != SyntaxKind::InterfaceDeclaration
        || derived_record.flags.0 != 0
        || interface.type_parameters.is_some()
        || !interface.members.nodes.is_empty()
        || !host.symbol_matches(store, declaration, owner)
        || derived.flags().without(SymbolFlags::TRANSIENT) != SymbolFlags::INTERFACE
        || derived.check_flags() != CheckFlags::NONE
        || derived.name().as_utf8() != Some("ReactNodeArray")
        || derived.declarations() != Some(&[declaration])
        || !namespace_owner.flags().intersects(SymbolFlags::NAMESPACE)
        || namespace_owner.name().as_utf8() != Some("React")
        || exports
            .get_source("ReactNodeArray")
            .and_then(|symbol| store.get_merged_symbol(symbol))
            != Some(owner)
    {
        return Ok(None);
    }

    let Some(block_id) = derived_record.parent else {
        return Ok(None);
    };
    let block = NodeRef::new(declaration.arena, declaration.file, block_id);
    let block_record =
        preflight_node(store, host, block).map_err(|_| DirectInterfaceHeritageError::Invalid)?;
    let NodeData::ModuleBlock(module_block) = &block_record.data else {
        return Ok(None);
    };
    let Some(namespace_id) = block_record.parent else {
        return Ok(None);
    };
    let namespace_declaration = NodeRef::new(block.arena, block.file, namespace_id);
    let namespace_record = preflight_node(store, host, namespace_declaration)
        .map_err(|_| DirectInterfaceHeritageError::Invalid)?;
    let NodeData::ModuleDeclaration(namespace_data) = &namespace_record.data else {
        return Ok(None);
    };
    let namespace_name = NodeRef::new(
        namespace_declaration.arena,
        namespace_declaration.file,
        namespace_data.name,
    );
    let namespace_name_record = preflight_node(store, host, namespace_name)
        .map_err(|_| DirectInterfaceHeritageError::Invalid)?;
    if block_record.kind != SyntaxKind::ModuleBlock
        || module_block
            .statements
            .nodes
            .iter()
            .filter(|candidate| **candidate == declaration.node)
            .count()
            != 1
        || namespace_record.kind != SyntaxKind::ModuleDeclaration
        || namespace_data.keyword != SyntaxKind::NamespaceKeyword
        || namespace_data.body != Some(block.node)
        || namespace_name_record.kind != SyntaxKind::Identifier
        || namespace_name_record.parent != Some(namespace_declaration.node)
        || !matches!(
            &namespace_name_record.data,
            NodeData::Identifier(identifier)
                if identifier.flow_node.is_none() && identifier.text == "React"
        )
        || bound
            .symbol(namespace_declaration)
            .and_then(|symbol| store.get_merged_symbol(symbol))
            != Some(namespace)
    {
        return Ok(None);
    }

    let global = store
        .intrinsic_bootstrap()
        .and_then(|bootstrap| store.symbol_table(bootstrap.globals));
    let owner_is_global = global
        .and_then(|globals| globals.get_source("React"))
        .and_then(|symbol| store.get_merged_symbol(symbol))
        == Some(namespace);
    if !owner_is_global {
        let Some(module_block_id) = namespace_record.parent else {
            return Ok(None);
        };
        let module_block = NodeRef::new(
            namespace_declaration.arena,
            namespace_declaration.file,
            module_block_id,
        );
        let module_block_record = preflight_node(store, host, module_block)
            .map_err(|_| DirectInterfaceHeritageError::Invalid)?;
        let Some(module_id) = module_block_record.parent else {
            return Ok(None);
        };
        let module = NodeRef::new(module_block.arena, module_block.file, module_id);
        let module_record = preflight_node(store, host, module)
            .map_err(|_| DirectInterfaceHeritageError::Invalid)?;
        let NodeData::ModuleDeclaration(module_data) = &module_record.data else {
            return Ok(None);
        };
        let name = NodeRef::new(module.arena, module.file, module_data.name);
        let name_record =
            preflight_node(store, host, name).map_err(|_| DirectInterfaceHeritageError::Invalid)?;
        if module_block_record.kind != SyntaxKind::ModuleBlock
            || module_record.kind != SyntaxKind::ModuleDeclaration
            || module_record.parent != Some(bound.source_file().node)
            || module_data.keyword != SyntaxKind::ModuleKeyword
            || module_data.body != Some(module_block.node)
            || name_record.kind != SyntaxKind::StringLiteral
            || name_record.parent != Some(module.node)
            || !matches!(&name_record.data, NodeData::StringLiteral(name) if name.text == "react")
            || bound
                .locals(module)
                .and_then(|locals| store.symbol_table(locals))
                .and_then(|locals| locals.get_source("React"))
                .and_then(|symbol| store.get_merged_symbol(symbol))
                != Some(namespace)
        {
            return Ok(None);
        }
    }

    let array = store
        .symbol(base)
        .ok_or(DirectInterfaceHeritageError::Invalid)?;
    if array.name().as_utf8() != Some("Array")
        || array.flags().without(SymbolFlags::TRANSIENT)
            != SymbolFlags::INTERFACE | SymbolFlags::FUNCTION_SCOPED_VARIABLE
        || array.check_flags() != CheckFlags::NONE
        || array.parent().is_some()
        || array.exports().is_some()
        || array.export_symbol().is_some()
        || store.get_merged_symbol(base) != Some(base)
        || global
            .and_then(|globals| globals.get_source("Array"))
            .and_then(|symbol| store.get_merged_symbol(symbol))
            != Some(base)
    {
        return Ok(None);
    }
    let Some(target) = store
        .declared_type_links(base)
        .and_then(|links| links.declared_type)
    else {
        return Ok(None);
    };
    if preflight_generic_global_type_target(store, target)
        .map_err(|_| DirectInterfaceHeritageError::Invalid)?
        .is_some()
        || store
            .type_payload(target)
            .and_then(super::type_records::TypeRecord::symbol)
            .and_then(|symbol| store.get_merged_symbol(symbol))
            != Some(base)
    {
        return Ok(None);
    }

    let mut interface_declarations = Vec::new();
    let mut seen = HashSet::with_capacity(base_declarations.len());
    let mut value = None;
    for &candidate in base_declarations {
        let Some(candidate_bound) = host.bound_file(candidate) else {
            return Err(DirectInterfaceHeritageError::Invalid);
        };
        let Some(candidate_facts) = candidate_bound.source_facts() else {
            return Err(DirectInterfaceHeritageError::Invalid);
        };
        let candidate_record = preflight_node(store, host, candidate)
            .map_err(|_| DirectInterfaceHeritageError::Invalid)?;
        if !seen.insert(candidate)
            || !candidate_facts.is_default_library()
            || !candidate_facts.is_declaration_file()
            || candidate_facts.is_javascript_file()
            || candidate_facts.is_external_or_common_js_module()
            || !host.symbol_matches(store, candidate, base)
        {
            return Ok(None);
        }
        match &candidate_record.data {
            NodeData::InterfaceDeclaration(interface)
                if candidate_record.kind == SyntaxKind::InterfaceDeclaration
                    && candidate_record.flags.0 == 0
                    && candidate_record.parent == Some(candidate_bound.source_file().node)
                    && interface
                        .type_parameters
                        .as_ref()
                        .is_some_and(|parameters| {
                            parameters.nodes.len() == 1 && !parameters.has_trailing_comma
                        })
                    && interface.flow_node.is_none()
                    && interface.local_symbol.is_none()
                    && interface.symbol.is_none() =>
            {
                interface_declarations.push(candidate);
            }
            NodeData::VariableDeclaration(variable)
                if candidate_record.kind == SyntaxKind::VariableDeclaration
                    && candidate_record.flags.0 == 0
                    && variable.initializer.is_none()
                    && variable.exclamation_token.is_none()
                    && variable.local_symbol.is_none()
                    && variable.symbol.is_none()
                    && variable.facts == 0
                    && value.replace(candidate).is_none() =>
            {
                if !authenticated_default_library_value_declaration(
                    store,
                    host,
                    candidate,
                    candidate_bound.source_file(),
                )? {
                    return Ok(None);
                }
            }
            _ => return Ok(None),
        }
    }
    if interface_declarations.is_empty() || array.value_declaration() != value {
        return Ok(None);
    }

    let planned = plan_concrete_interface_type_arguments(
        store,
        host,
        declaration,
        owner,
        node,
        base,
        &interface_declarations,
        type_argument_list,
    )?;
    let [argument] = planned.as_slice() else {
        return Ok(None);
    };
    let argument_record = preflight_node(store, host, *argument)
        .map_err(|_| DirectInterfaceHeritageError::Invalid)?;
    let NodeData::TypeReferenceNode(reference) = &argument_record.data else {
        return Ok(None);
    };
    let name = NodeRef::new(argument.arena, argument.file, reference.type_name);
    let name_record =
        preflight_node(store, host, name).map_err(|_| DirectInterfaceHeritageError::Invalid)?;
    let Some(react_node) = exports
        .get_source("ReactNode")
        .and_then(|symbol| store.get_merged_symbol(symbol))
    else {
        return Ok(None);
    };
    let Some(alias) = store.symbol(react_node) else {
        return Err(DirectInterfaceHeritageError::Invalid);
    };
    let mut resolver = host
        .name_resolver_host(store)
        .map_err(|_| DirectInterfaceHeritageError::Invalid)?;
    if argument_record.kind != SyntaxKind::TypeReference
        || reference.type_arguments.is_some()
        || name_record.kind != SyntaxKind::Identifier
        || name_record.parent != Some(argument.node)
        || !matches!(
            &name_record.data,
            NodeData::Identifier(identifier)
                if identifier.flow_node.is_none() && identifier.text == "ReactNode"
        )
        || !alias.flags().contains(SymbolFlags::TYPE_ALIAS)
        || alias
            .flags()
            .without(SymbolFlags::TYPE_ALIAS | SymbolFlags::TRANSIENT)
            != SymbolFlags::NONE
        || alias.check_flags() != CheckFlags::NONE
        || store.get_parent_of_symbol(react_node) != Some(namespace)
        || resolver
            .resolve_entity_name(name, SymbolFlags::TYPE)
            .map_err(|_| DirectInterfaceHeritageError::Invalid)?
            .and_then(|symbol| store.get_merged_symbol(symbol))
            != Some(react_node)
    {
        return Ok(None);
    }
    Ok(Some(planned))
}

fn authenticate_default_library_interface_base(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    symbol: SemanticSymbolId,
    declarations: &[NodeRef],
) -> Result<bool, DirectInterfaceHeritageError> {
    let owner = store
        .symbol(symbol)
        .ok_or(DirectInterfaceHeritageError::Invalid)?;
    let Some(name) = owner.name().as_utf8() else {
        return Ok(false);
    };
    let flags = owner.flags().without(SymbolFlags::TRANSIENT);
    let global = store
        .intrinsic_bootstrap()
        .and_then(|bootstrap| store.symbol_table(bootstrap.globals))
        .and_then(|globals| globals.get(owner.name()))
        .and_then(|global| store.get_merged_symbol(global));
    if !(name.starts_with("HTML") || name.starts_with("SVG"))
        || !name.ends_with("Element")
        || flags != SymbolFlags::INTERFACE | SymbolFlags::FUNCTION_SCOPED_VARIABLE
        || owner.check_flags() != CheckFlags::NONE
        || owner.parent().is_some()
        || owner.exports().is_some()
        || owner.export_symbol().is_some()
        || store.get_merged_symbol(symbol) != Some(symbol)
        || global != Some(symbol)
    {
        return Ok(false);
    }

    let mut seen = HashSet::with_capacity(declarations.len());
    let mut has_interface = false;
    let mut value_declaration = None;
    for &declaration in declarations {
        let bound = host
            .bound_file(declaration)
            .ok_or(DirectInterfaceHeritageError::Invalid)?;
        let Some(facts) = bound.source_facts() else {
            return Err(DirectInterfaceHeritageError::Invalid);
        };
        let record = preflight_node(store, host, declaration)
            .map_err(|_| DirectInterfaceHeritageError::Invalid)?;
        if !seen.insert(declaration)
            || !facts.is_default_library()
            || !facts.is_declaration_file()
            || facts.is_javascript_file()
            || facts.is_external_or_common_js_module()
            || !host.symbol_matches(store, declaration, symbol)
        {
            return Ok(false);
        }

        let declaration_name = match &record.data {
            NodeData::InterfaceDeclaration(interface)
                if record.kind == SyntaxKind::InterfaceDeclaration
                    && record.flags.0 == 0
                    && record.parent == Some(bound.source_file().node)
                    && interface.type_parameters.is_none()
                    && interface.flow_node.is_none()
                    && interface.local_symbol.is_none()
                    && interface.symbol.is_none()
                    && !interface.members.has_trailing_comma =>
            {
                has_interface = true;
                interface.name
            }
            NodeData::VariableDeclaration(variable)
                if record.kind == SyntaxKind::VariableDeclaration
                    && record.flags.0 == 0
                    && variable.initializer.is_none()
                    && variable.exclamation_token.is_none()
                    && variable.local_symbol.is_none()
                    && variable.symbol.is_none()
                    && variable.facts == 0
                    && value_declaration.replace(declaration).is_none() =>
            {
                if !authenticated_default_library_value_declaration(
                    store,
                    host,
                    declaration,
                    bound.source_file(),
                )? {
                    return Ok(false);
                }
                variable.name
            }
            _ => return Ok(false),
        };
        let declaration_name = NodeRef::new(declaration.arena, declaration.file, declaration_name);
        let declaration_name_record = preflight_node(store, host, declaration_name)
            .map_err(|_| DirectInterfaceHeritageError::Invalid)?;
        if declaration_name_record.kind != SyntaxKind::Identifier
            || declaration_name_record.flags.0 != 0
            || declaration_name_record.parent != Some(declaration.node)
            || !matches!(
                &declaration_name_record.data,
                NodeData::Identifier(identifier)
                    if identifier.flow_node.is_none() && identifier.text == name
            )
        {
            return Ok(false);
        }
    }
    if !has_interface
        || value_declaration.is_none()
        || owner.value_declaration() != value_declaration
    {
        return Ok(false);
    }

    if let Some(links) = store.declared_type_links(symbol) {
        let Some(type_) = links.declared_type else {
            return Ok(false);
        };
        let Some(record) = store.type_payload(type_) else {
            return Ok(false);
        };
        let TypeData::Interface(interface) = record.data() else {
            return Ok(false);
        };
        if !record.object_flags().contains(ObjectFlags::INTERFACE)
            || record.object_flags().contains(ObjectFlags::CLASS)
            || record.symbol() != Some(symbol)
            || record.alias().is_some()
            || interface.outer_type_parameter_count != 0
            || interface
                .reference
                .resolved_type_arguments
                .as_ref()
                .is_some_and(|arguments| !arguments.is_empty())
        {
            return Ok(false);
        }
    }
    Ok(true)
}

fn authenticated_default_library_value_declaration(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    declaration: NodeRef,
    source: NodeRef,
) -> Result<bool, DirectInterfaceHeritageError> {
    let record = preflight_node(store, host, declaration)
        .map_err(|_| DirectInterfaceHeritageError::Invalid)?;
    let Some(list) = record
        .parent
        .map(|parent| NodeRef::new(declaration.arena, declaration.file, parent))
    else {
        return Ok(false);
    };
    let list_record =
        preflight_node(store, host, list).map_err(|_| DirectInterfaceHeritageError::Invalid)?;
    let NodeData::VariableDeclarationList(variables) = &list_record.data else {
        return Ok(false);
    };
    let Some(statement) = list_record
        .parent
        .map(|parent| NodeRef::new(list.arena, list.file, parent))
    else {
        return Ok(false);
    };
    let statement_record = preflight_node(store, host, statement)
        .map_err(|_| DirectInterfaceHeritageError::Invalid)?;
    let NodeData::VariableStatement(variable_statement) = &statement_record.data else {
        return Ok(false);
    };
    let Some(modifiers) = variable_statement.modifiers.as_ref() else {
        return Ok(false);
    };
    let [modifier] = modifiers.list.nodes.as_slice() else {
        return Ok(false);
    };
    let modifier = NodeRef::new(statement.arena, statement.file, *modifier);
    let modifier_record =
        preflight_node(store, host, modifier).map_err(|_| DirectInterfaceHeritageError::Invalid)?;
    Ok(list_record.kind == SyntaxKind::VariableDeclarationList
        && list_record.flags.0 == 0
        && variables
            .declarations
            .nodes
            .iter()
            .filter(|candidate| **candidate == declaration.node)
            .count()
            == 1
        && statement_record.kind == SyntaxKind::VariableStatement
        && statement_record.flags.0 == 0
        && statement_record.parent == Some(source.node)
        && variable_statement.declaration_list == list.node
        && modifiers.flags.0 == 0
        && !modifiers.list.has_trailing_comma
        && modifier_record.kind == SyntaxKind::DeclareKeyword
        && modifier_record.flags.0 == 0
        && modifier_record.parent == Some(statement.node))
}

fn resolve_qualified_interface_base(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    expression: NodeRef,
) -> Result<SemanticSymbolId, DirectInterfaceHeritageError> {
    let record = preflight_node(store, host, expression)
        .map_err(|_| DirectInterfaceHeritageError::Invalid)?;
    let (namespace_id, name_id) = match &record.data {
        NodeData::PropertyAccessExpression(access)
            if record.kind == SyntaxKind::PropertyAccessExpression
                && access.flow_node.is_none()
                && access.question_dot_token.is_none()
                && access.facts == 0 =>
        {
            (access.expression, access.name)
        }
        NodeData::QualifiedName(qualified)
            if record.kind == SyntaxKind::QualifiedName
                && qualified.flow_node.is_none()
                && qualified.facts == 0 =>
        {
            (qualified.left, qualified.right)
        }
        _ => return Err(DirectInterfaceHeritageError::Invalid),
    };
    let namespace_expression = NodeRef::new(expression.arena, expression.file, namespace_id);
    let namespace_record = preflight_node(store, host, namespace_expression)
        .map_err(|_| DirectInterfaceHeritageError::Invalid)?;
    let name = NodeRef::new(expression.arena, expression.file, name_id);
    let name_record =
        preflight_node(store, host, name).map_err(|_| DirectInterfaceHeritageError::Invalid)?;
    let NodeData::Identifier(identifier) = &name_record.data else {
        return Err(DirectInterfaceHeritageError::Unsupported {
            node: name,
            kind: name_record.kind,
        });
    };
    if record.flags.0 != 0
        || name_record.kind != SyntaxKind::Identifier
        || name_record.flags.0 != 0
        || name_record.parent != Some(expression.node)
        || identifier.flow_node.is_some()
        || namespace_record.range.end > name_record.range.start
        || name_record.range.end > record.range.end
    {
        return Err(DirectInterfaceHeritageError::Invalid);
    }

    let namespace = authenticate_namespace_expression(
        store,
        host,
        namespace_expression,
        expression,
        &mut HashSet::new(),
    )?;
    let mut callback_host = host
        .name_resolver_host(store)
        .map_err(|_| DirectInterfaceHeritageError::Invalid)?;
    let symbol = callback_host
        .resolve_entity_name(expression, SymbolFlags::TYPE)
        .map_err(|_| DirectInterfaceHeritageError::Unsupported {
            node: expression,
            kind: record.kind,
        })?
        .and_then(|symbol| store.get_merged_symbol(symbol))
        .ok_or(DirectInterfaceHeritageError::Unsupported {
            node: expression,
            kind: record.kind,
        })?;
    if !authenticated_namespace_export(store, namespace, &identifier.text, symbol) {
        return Err(DirectInterfaceHeritageError::Unsupported {
            node: expression,
            kind: record.kind,
        });
    }
    Ok(symbol)
}

fn authenticate_namespace_expression(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    expression: NodeRef,
    parent: NodeRef,
    visited: &mut HashSet<NodeRef>,
) -> Result<SemanticSymbolId, DirectInterfaceHeritageError> {
    let record = preflight_node(store, host, expression)
        .map_err(|_| DirectInterfaceHeritageError::Invalid)?;
    let parent_record =
        preflight_node(store, host, parent).map_err(|_| DirectInterfaceHeritageError::Invalid)?;
    if record.parent != Some(parent.node)
        || record.flags.0 != 0
        || record.range.start < parent_record.range.start
        || record.range.end > parent_record.range.end
        || !visited.insert(expression)
    {
        return Err(DirectInterfaceHeritageError::Invalid);
    }

    let segment = match &record.data {
        NodeData::Identifier(identifier)
            if record.kind == SyntaxKind::Identifier && identifier.flow_node.is_none() =>
        {
            None
        }
        NodeData::PropertyAccessExpression(access)
            if record.kind == SyntaxKind::PropertyAccessExpression
                && access.flow_node.is_none()
                && access.question_dot_token.is_none()
                && access.facts == 0 =>
        {
            Some((access.expression, access.name))
        }
        NodeData::QualifiedName(qualified)
            if record.kind == SyntaxKind::QualifiedName
                && qualified.flow_node.is_none()
                && qualified.facts == 0 =>
        {
            Some((qualified.left, qualified.right))
        }
        _ => {
            return Err(DirectInterfaceHeritageError::Unsupported {
                node: expression,
                kind: record.kind,
            });
        }
    };
    let prefix = if let Some((left, name)) = segment {
        let left = NodeRef::new(expression.arena, expression.file, left);
        let left_record =
            preflight_node(store, host, left).map_err(|_| DirectInterfaceHeritageError::Invalid)?;
        let name = NodeRef::new(expression.arena, expression.file, name);
        let name_record =
            preflight_node(store, host, name).map_err(|_| DirectInterfaceHeritageError::Invalid)?;
        let NodeData::Identifier(identifier) = &name_record.data else {
            return Err(DirectInterfaceHeritageError::Unsupported {
                node: name,
                kind: name_record.kind,
            });
        };
        if name_record.kind != SyntaxKind::Identifier
            || name_record.flags.0 != 0
            || name_record.parent != Some(expression.node)
            || identifier.flow_node.is_some()
            || left_record.range.end > name_record.range.start
            || name_record.range.end > record.range.end
        {
            return Err(DirectInterfaceHeritageError::Invalid);
        }
        Some((
            authenticate_namespace_expression(store, host, left, expression, visited)?,
            identifier.text.as_str(),
        ))
    } else {
        None
    };

    let mut callback_host = host
        .name_resolver_host(store)
        .map_err(|_| DirectInterfaceHeritageError::Invalid)?;
    let symbol = callback_host
        .resolve_entity_name(expression, SymbolFlags::NAMESPACE)
        .map_err(|_| DirectInterfaceHeritageError::Unsupported {
            node: expression,
            kind: record.kind,
        })?
        .and_then(|symbol| store.get_merged_symbol(symbol))
        .ok_or(DirectInterfaceHeritageError::Unsupported {
            node: expression,
            kind: record.kind,
        })?;
    if store
        .symbol(symbol)
        .is_none_or(|namespace| !namespace.flags().intersects(SymbolFlags::MODULE))
        || prefix.is_some_and(|(owner, name)| {
            !authenticated_namespace_export(store, owner, name, symbol)
        })
    {
        return Err(DirectInterfaceHeritageError::Unsupported {
            node: expression,
            kind: record.kind,
        });
    }
    Ok(symbol)
}

fn authenticated_namespace_export(
    store: &CanonicalTypeMapperStore,
    namespace: SemanticSymbolId,
    name: &str,
    symbol: SemanticSymbolId,
) -> bool {
    let Some(owner) = store.symbol(namespace) else {
        return false;
    };
    let exports = store
        .module_symbol_links(namespace)
        .and_then(|links| links.resolved_exports)
        .or_else(|| owner.exports());
    exports
        .and_then(|exports| store.symbol_table(exports))
        .and_then(|exports| exports.get_source(name))
        .and_then(|export| store.get_merged_symbol(export))
        == Some(symbol)
        && store.get_parent_of_symbol(symbol) == Some(namespace)
        && store
            .symbol(symbol)
            .and_then(|symbol| symbol.name().as_utf8())
            == Some(name)
}

fn plan_record_type_arguments(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    node: NodeRef,
    arguments: &NodeList,
) -> Result<Vec<NodeRef>, DirectInterfaceHeritageError> {
    let record =
        preflight_node(store, host, node).map_err(|_| DirectInterfaceHeritageError::Invalid)?;
    let NodeData::ExpressionWithTypeArguments(base) = &record.data else {
        return Err(DirectInterfaceHeritageError::Invalid);
    };
    let expression = NodeRef::new(node.arena, node.file, base.expression);
    let expression_record = preflight_node(store, host, expression)
        .map_err(|_| DirectInterfaceHeritageError::Invalid)?;
    if arguments.nodes.len() != 2 {
        return Err(DirectInterfaceHeritageError::Unsupported {
            node,
            kind: SyntaxKind::ExpressionWithTypeArguments,
        });
    }
    if arguments.has_trailing_comma
        || arguments.range.start < expression_record.range.end
        || arguments.range.end != record.range.end
        || arguments.range.start >= arguments.range.end
    {
        return Err(DirectInterfaceHeritageError::Invalid);
    }

    let mut nodes = Vec::with_capacity(arguments.nodes.len());
    let mut previous_end = expression_record.range.end;
    for (argument, expected_kind) in arguments
        .nodes
        .iter()
        .zip([SyntaxKind::StringKeyword, SyntaxKind::AnyKeyword])
    {
        let argument = NodeRef::new(node.arena, node.file, *argument);
        let argument_record = preflight_node(store, host, argument)
            .map_err(|_| DirectInterfaceHeritageError::Invalid)?;
        if argument_record.parent != Some(node.node)
            || argument_record.range.start < previous_end
            || argument_record.range.start <= arguments.range.start
            || argument_record.range.end >= arguments.range.end
            || argument_record.range.start < record.range.start
            || argument_record.range.end > record.range.end
            || nodes.contains(&argument)
        {
            return Err(DirectInterfaceHeritageError::Invalid);
        }
        if argument_record.kind != expected_kind {
            return Err(DirectInterfaceHeritageError::Unsupported {
                node: argument,
                kind: argument_record.kind,
            });
        }
        previous_end = argument_record.range.end;
        nodes.push(argument);
    }
    Ok(nodes)
}

fn authenticate_record_mapped_alias(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    symbol: SemanticSymbolId,
    declarations: &[NodeRef],
) -> Result<bool, DirectInterfaceHeritageError> {
    let [declaration] = declarations else {
        return Ok(false);
    };
    let record = preflight_node(store, host, *declaration)
        .map_err(|_| DirectInterfaceHeritageError::Invalid)?;
    let NodeData::TypeAliasDeclaration(alias) = &record.data else {
        return Ok(false);
    };
    let Some(parameters) = alias.type_parameters.as_ref() else {
        return Ok(false);
    };
    if record.kind != SyntaxKind::TypeAliasDeclaration
        || !host.symbol_matches(store, *declaration, symbol)
        || parameters.nodes.len() != 2
        || parameters.has_trailing_comma
    {
        return Ok(false);
    }
    let name = NodeRef::new(declaration.arena, declaration.file, alias.name);
    let name_record =
        preflight_node(store, host, name).map_err(|_| DirectInterfaceHeritageError::Invalid)?;
    if name_record.parent != Some(declaration.node)
        || !matches!(&name_record.data, NodeData::Identifier(name) if name.text == "Record")
    {
        return Ok(false);
    }

    let mut parameter_symbols = Vec::with_capacity(parameters.nodes.len());
    let mut key_constraint = None;
    for (index, parameter) in parameters.nodes.iter().enumerate() {
        let parameter = NodeRef::new(declaration.arena, declaration.file, *parameter);
        let parameter_record = preflight_node(store, host, parameter)
            .map_err(|_| DirectInterfaceHeritageError::Invalid)?;
        let NodeData::TypeParameterDeclaration(data) = &parameter_record.data else {
            return Ok(false);
        };
        let parameter_symbol = host
            .bound_file(parameter)
            .and_then(|bound| bound.symbol(parameter))
            .and_then(|parameter_symbol| store.get_merged_symbol(parameter_symbol));
        if parameter_record.kind != SyntaxKind::TypeParameter
            || parameter_record.parent != Some(declaration.node)
            || data.default_type.is_some()
            || data.expression.is_some()
            || parameter_symbol.is_none_or(|parameter_symbol| {
                !host.symbol_matches(store, parameter, parameter_symbol)
                    || store.symbol(parameter_symbol).is_none_or(|record| {
                        record.flags() != SymbolFlags::TYPE_PARAMETER
                            || record.declarations() != Some(std::slice::from_ref(&parameter))
                    })
            })
        {
            return Ok(false);
        }
        match (index, data.constraint) {
            (0, Some(constraint)) => {
                key_constraint = Some(NodeRef::new(
                    declaration.arena,
                    declaration.file,
                    constraint,
                ));
            }
            (1, None) => {}
            _ => return Ok(false),
        }
        parameter_symbols.push(parameter_symbol.expect("a parameter symbol was authenticated"));
    }
    if parameter_symbols[0] == parameter_symbols[1] {
        return Ok(false);
    }

    let constraint = key_constraint.expect("the first parameter constraint was authenticated");
    let constraint_record = preflight_node(store, host, constraint)
        .map_err(|_| DirectInterfaceHeritageError::Invalid)?;
    let NodeData::TypeOperatorNode(operator) = &constraint_record.data else {
        return Ok(false);
    };
    let key_parameter = NodeRef::new(declaration.arena, declaration.file, parameters.nodes[0]);
    let operand = NodeRef::new(constraint.arena, constraint.file, operator.type_);
    let operand_record =
        preflight_node(store, host, operand).map_err(|_| DirectInterfaceHeritageError::Invalid)?;
    if constraint_record.kind != SyntaxKind::TypeOperator
        || constraint_record.parent != Some(key_parameter.node)
        || operator.operator != SyntaxKind::KeyOfKeyword
        || operand_record.kind != SyntaxKind::AnyKeyword
        || operand_record.parent != Some(constraint.node)
    {
        return Ok(false);
    }

    let mapped_node = NodeRef::new(declaration.arena, declaration.file, alias.type_);
    let mapped_record = preflight_node(store, host, mapped_node)
        .map_err(|_| DirectInterfaceHeritageError::Invalid)?;
    if mapped_record.parent != Some(declaration.node) {
        return Ok(false);
    }
    let Ok(mapped) = plan_mapped_type_declaration(store, host, mapped_node) else {
        return Ok(false);
    };
    let Some(template) = mapped.template() else {
        return Ok(false);
    };
    if mapped.name_type().is_some()
        || mapped.modifiers_source().is_some()
        || mapped.modifiers().bits() != 0
    {
        return Ok(false);
    }
    for (reference, expected) in [
        (mapped.constraint(), parameter_symbols[0]),
        (template, parameter_symbols[1]),
    ] {
        let reference_record = preflight_node(store, host, reference)
            .map_err(|_| DirectInterfaceHeritageError::Invalid)?;
        let NodeData::TypeReferenceNode(data) = &reference_record.data else {
            return Ok(false);
        };
        let reference_name = NodeRef::new(reference.arena, reference.file, data.type_name);
        let reference_name_record = preflight_node(store, host, reference_name)
            .map_err(|_| DirectInterfaceHeritageError::Invalid)?;
        if reference_record.kind != SyntaxKind::TypeReference
            || data.type_arguments.is_some()
            || reference_name_record.parent != Some(reference.node)
            || !matches!(reference_name_record.data, NodeData::Identifier(_))
        {
            return Ok(false);
        }
        let mut callback_host = host
            .name_resolver_host(store)
            .map_err(|_| DirectInterfaceHeritageError::Invalid)?;
        let resolved = callback_host
            .resolve_entity_name(reference_name, SymbolFlags::TYPE)
            .map_err(|_| DirectInterfaceHeritageError::Invalid)?
            .and_then(|resolved| store.get_merged_symbol(resolved));
        if resolved != Some(expected) {
            return Ok(false);
        }
    }
    Ok(true)
}

#[cfg(test)]
mod tests {
    use ts_ast::FileId;
    use ts_binder::{
        CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
        EscapedName, InternalSymbolName,
    };
    use ts_parser::{ParseResult, parse_source_file};

    use super::*;
    use crate::semantic::{
        AliasTargetState, CanonicalCheckerContext, CanonicalCheckerDiagnostics,
        CanonicalCheckerOptions, TypeData,
        bootstrap::{IntrinsicBootstrapOptions, LiteralTypeCacheError},
        production::GlobalMergeCompletion,
        reference_types::{
            validate_direct_generic_reference, validate_nongeneric_interface_argument_origin,
        },
        type_nodes::CanonicalTypeQuery,
    };

    fn checker_context(parsed: &ParseResult, file: FileId) -> CanonicalCheckerContext<'_> {
        checker_context_with_options(parsed, file, CanonicalCheckerOptions::default())
    }

    fn checker_context_with_options(
        parsed: &ParseResult,
        file: FileId,
        options: CanonicalCheckerOptions,
    ) -> CanonicalCheckerContext<'_> {
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source("\"/project/merged-interface-heritage.ts\""),
                    CanonicalSourceLanguage::TypeScript,
                    false,
                    CanonicalModuleState::Script,
                ),
            )
            .unwrap();
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
        CanonicalCheckerContext::new(binder.finish(), vec![(file, &parsed.arena)], options).unwrap()
    }

    fn source_alias_in_test(
        parsed: &ParseResult,
        file: FileId,
        context: &CanonicalCheckerContext<'_>,
        name: &str,
    ) -> (SemanticSymbolId, NodeRef) {
        let (declaration, rhs) = parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                let NodeData::TypeAliasDeclaration(alias) = &record.data else {
                    return None;
                };
                let NodeData::Identifier(identifier) = &parsed.arena.get(alias.name)?.data else {
                    return None;
                };
                (identifier.text == name).then_some((
                    NodeRef::new(parsed.arena.id(), file, node),
                    NodeRef::new(parsed.arena.id(), file, alias.type_),
                ))
            })
            .unwrap();
        let raw = context.file(file).unwrap().1.symbol(declaration).unwrap();
        (context.store().get_merged_symbol(raw).unwrap(), rhs)
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Keep each original scope and its damage/restore checks together.
    fn source_local_namespace_bindings_keep_original_scopes_and_alias_misses() {
        let parsed = parse_source_file(concat!(
            "export {};\n",
            "namespace NS { export interface Value {} }\n",
            "namespace Other { export interface Value {} }\n",
            "declare const valueOnly: number; type OuterRead = NS.Value;\n",
            "namespace Near { namespace NS { export interface Value {} }\n",
            "type NearRead = NS.Value; }\n",
            "namespace WrongMeaning { declare const NS: number;\n",
            "type ThroughRead = NS.Value; }\n",
            "type GlobalRead = GlobalOnly.Value;\n",
            "import Pending = require(\"missing\"); type PendingRead = Pending.Value;\n",
            "namespace AliasMiss { import NS = require(\"missing\");\n",
            "type AliasRead = NS.Value; }\n",
        ));
        let foreign = parse_source_file("export {}; namespace NS { export interface Value {} }");
        let globals = parse_source_file("declare namespace GlobalOnly { interface Value {} }");
        let file = FileId::new(203_201);
        let foreign_file = FileId::new(203_202);
        let globals_file = FileId::new(203_203);
        let sources = [
            (file, &parsed, CanonicalModuleState::External),
            (foreign_file, &foreign, CanonicalModuleState::External),
            (globals_file, &globals, CanonicalModuleState::Script),
        ];
        let mut binder = CanonicalBinder::new();
        for (file, parsed, module) in sources {
            assert!(parsed.diagnostics.is_empty());
            binder
                .bind_source_file_with_facts(
                    &parsed.arena,
                    parsed.source_file,
                    file,
                    CanonicalSourceFileFacts::new(
                        EscapedName::source(format!(
                            "\"/project/local-namespace-{}.ts\"",
                            file.index()
                        )),
                        CanonicalSourceLanguage::TypeScript,
                        false,
                        module,
                    ),
                )
                .unwrap();
            binder
                .bind_typescript_declaration_slice(&parsed.arena, file)
                .unwrap();
        }
        let mut context = CanonicalCheckerContext::new(
            binder.finish(),
            sources
                .iter()
                .map(|(file, parsed, _)| (*file, &parsed.arena))
                .collect(),
            CanonicalCheckerOptions::default(),
        )
        .unwrap();
        let bound = context.file(file).unwrap().1.clone();
        let foreign_bound = context.file(foreign_file).unwrap().1.clone();
        let globals_bound = context.file(globals_file).unwrap().1.clone();
        let host = DeclaredTypeHost::new_after_global_merge(
            [
                (&parsed.arena, &bound),
                (&foreign.arena, &foreign_bound),
                (&globals.arena, &globals_bound),
            ],
            GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
        )
        .unwrap();
        let module = |name: &str, container: NodeRef| {
            parsed
                .arena
                .iter()
                .find_map(|(node, record)| {
                    let NodeData::ModuleDeclaration(module) = &record.data else {
                        return None;
                    };
                    let NodeData::Identifier(identifier) = &parsed.arena.get(module.name)?.data
                    else {
                        return None;
                    };
                    let declaration = NodeRef::new(parsed.arena.id(), file, node);
                    (identifier.text == name && bound.container(declaration) == Some(container))
                        .then_some(declaration)
                })
                .unwrap()
        };
        let outer_declaration = module("NS", bound.source_file());
        let near_container = module("Near", bound.source_file());
        let near_declaration = module("NS", near_container);
        let alias_container = module("AliasMiss", bound.source_file());
        let root_locals = bound.locals(bound.source_file()).unwrap();
        let near_locals = bound.locals(near_container).unwrap();
        let alias_locals = bound.locals(alias_container).unwrap();
        let root_table = context.store().symbol_table(root_locals).unwrap();
        let outer_raw = root_table.get_source("NS").unwrap();
        let other_raw = root_table.get_source("Other").unwrap();
        let value_raw = root_table.get_source("valueOnly").unwrap();
        let pending_raw = root_table.get_source("Pending").unwrap();
        let near_raw = context
            .store()
            .symbol_table(near_locals)
            .unwrap()
            .get_source("NS")
            .unwrap();
        let inner_alias_raw = context
            .store()
            .symbol_table(alias_locals)
            .unwrap()
            .get_source("NS")
            .unwrap();
        let foreign_raw = context
            .store()
            .symbol_table(foreign_bound.locals(foreign_bound.source_file()).unwrap())
            .unwrap()
            .get_source("NS")
            .unwrap();
        assert_eq!(bound.symbol(outer_declaration), Some(outer_raw));
        assert_eq!(bound.symbol(near_declaration), Some(near_raw));
        let outer = context.store().get_merged_symbol(outer_raw).unwrap();
        let near = context.store().get_merged_symbol(near_raw).unwrap();
        let value = context.store().get_merged_symbol(value_raw).unwrap();
        let pending = context.store().get_merged_symbol(pending_raw).unwrap();
        let inner_alias = context.store().get_merged_symbol(inner_alias_raw).unwrap();
        assert_ne!(outer, near);
        assert_ne!(outer_raw, foreign_raw);
        assert_eq!(
            context.store().symbol(outer_raw).unwrap().name(),
            context.store().symbol(foreign_raw).unwrap().name(),
        );
        let [
            outer_name,
            near_name,
            through_name,
            global_name,
            pending_name,
            alias_name,
        ] = [
            "OuterRead",
            "NearRead",
            "ThroughRead",
            "GlobalRead",
            "PendingRead",
            "AliasRead",
        ]
        .map(|name| {
            let (_, rhs) = source_alias_in_test(&parsed, file, &context, name);
            let NodeData::TypeReferenceNode(reference) = &parsed.arena.get(rhs.node).unwrap().data
            else {
                panic!("the source alias has a qualified type reference");
            };
            let NodeData::QualifiedName(qualified) =
                &parsed.arena.get(reference.type_name).unwrap().data
            else {
                panic!("the source reference has an actual left identifier");
            };
            let left = NodeRef::new(parsed.arena.id(), file, qualified.left);
            assert_eq!(
                context.store().source_node_kind(left),
                Some(SyntaxKind::Identifier),
            );
            left
        });
        assert!(
            context
                .store()
                .source_global_bindings()
                .unwrap()
                .get(EscapedName::source("GlobalOnly").as_ref())
                .is_some()
        );
        let source_nodes: Vec<_> = sources
            .iter()
            .flat_map(|(file, parsed, _)| {
                parsed
                    .arena
                    .iter()
                    .map(move |(node, _)| NodeRef::new(parsed.arena.id(), *file, node))
            })
            .collect();
        let mut source_symbols = Vec::new();
        let mut source_tables = Vec::new();
        for bound in [&bound, &foreign_bound, &globals_bound] {
            for node in bound.traversal_order() {
                if let Some(table) = bound.locals(node)
                    && !source_tables.contains(&table)
                {
                    source_tables.push(table);
                }
                for symbol in [bound.symbol(node), bound.local_symbol(node)]
                    .into_iter()
                    .flatten()
                {
                    if !source_symbols.contains(&symbol) {
                        source_symbols.push(symbol);
                    }
                    let record = context.store().symbol(symbol).unwrap();
                    for table in [record.members(), record.exports()].into_iter().flatten() {
                        if !source_tables.contains(&table) {
                            source_tables.push(table);
                        }
                    }
                }
            }
        }
        let snapshot = |store: &CanonicalTypeMapperStore| {
            (
                store.type_len(),
                store.symbol_len(),
                store.signature_len(),
                store.mapper_len(),
                store.symbol_store().symbol_table_len(),
                store.checker_link_allocated_lengths(),
                source_nodes
                    .iter()
                    .map(|node| {
                        (
                            store.type_node_links(*node).cloned(),
                            store.symbol_node_links(*node).cloned(),
                            store.signature_links(*node).cloned(),
                        )
                    })
                    .collect::<Vec<_>>(),
                source_symbols
                    .iter()
                    .map(|symbol| {
                        (
                            store.declared_type_links(*symbol).cloned(),
                            store.type_alias_links(*symbol).cloned(),
                            store.value_symbol_links(*symbol).cloned(),
                            store.alias_symbol_links(*symbol).cloned(),
                        )
                    })
                    .collect::<Vec<_>>(),
                source_tables
                    .iter()
                    .map(|table| {
                        store
                            .symbol_table(*table)
                            .unwrap()
                            .iter()
                            .map(|(name, symbol)| (name.to_owned(), symbol))
                            .collect::<Vec<_>>()
                    })
                    .collect::<Vec<_>>(),
            )
        };
        let pristine = snapshot(context.store());
        for _ in 0..2 {
            for (name, raw, symbol) in [
                (outer_name, outer_raw, outer),
                (near_name, near_raw, near),
                (through_name, outer_raw, outer),
            ] {
                let SourceLocalNamespaceLookup::Local(binding) =
                    resolve_source_local_namespace_binding(context.store(), &host, name).unwrap()
                else {
                    panic!("the original namespace binding stays local");
                };
                assert_eq!(binding.raw_symbol(), raw);
                assert_eq!(binding.symbol(), symbol);
                assert_eq!(snapshot(context.store()), pristine);
            }
            assert!(matches!(
                resolve_source_local_namespace_binding(context.store(), &host, global_name),
                Ok(SourceLocalNamespaceLookup::NoLocalNamespace),
            ));
            assert_eq!(snapshot(context.store()), pristine);
        }

        for replacement in [outer_raw, other_raw, foreign_raw, value_raw] {
            assert_eq!(
                context.store_mut_for_test().insert_symbol(
                    near_locals,
                    EscapedName::source("NS"),
                    replacement,
                ),
                Some(Some(near_raw)),
            );
            let damaged = snapshot(context.store());
            for _ in 0..2 {
                assert_eq!(
                    resolve_source_local_namespace_binding(context.store(), &host, near_name)
                        .unwrap_err(),
                    source_heritage_error(near_name),
                );
                assert_eq!(snapshot(context.store()), damaged);
            }
            assert_eq!(
                context.store_mut_for_test().insert_symbol(
                    near_locals,
                    EscapedName::source("NS"),
                    near_raw,
                ),
                Some(Some(replacement)),
            );
            assert_eq!(snapshot(context.store()), pristine);
            let SourceLocalNamespaceLookup::Local(binding) =
                resolve_source_local_namespace_binding(context.store(), &host, near_name).unwrap()
            else {
                panic!("the restored near namespace stays local");
            };
            assert_eq!(binding.symbol(), near);
            assert_eq!(snapshot(context.store()), pristine);
        }

        // These are receipt-verifier controls, not live table-entry removals.
        for (name, table, remove) in [
            (near_name, near_locals, true),
            (global_name, root_locals, false),
        ] {
            let (result, mut reads) = resolve_source_identifier_with_origins(
                context.store(),
                &host,
                name,
                SymbolFlags::NAMESPACE,
                true,
            )
            .unwrap();
            assert_eq!(result, Ok(remove.then_some(near)));
            let original = reads.clone();
            let read = reads
                .lookups
                .iter_mut()
                .find(|read| read.entry.table == table)
                .unwrap();
            assert_eq!(read.entry.raw_entry, remove.then_some(near_raw));
            let replacement = (!remove).then_some(foreign_raw);
            read.entry.raw_entry = replacement;
            read.entry.canonical_entry =
                replacement.and_then(|symbol| context.store().get_merged_symbol(symbol));
            read.entry.raw_flags =
                replacement.map(|symbol| context.store().symbol(symbol).unwrap().flags());
            read.entry.flags = read
                .entry
                .canonical_entry
                .map(|symbol| context.store().symbol(symbol).unwrap().flags());
            read.result = read.entry.canonical_entry;
            for _ in 0..2 {
                assert_eq!(
                    retain_source_heritage_table_origins(context.store(), &host, name, &mut reads),
                    Err(source_heritage_error(name)),
                );
                assert_eq!(snapshot(context.store()), pristine);
            }
            reads = original.clone();
            assert_eq!(
                retain_source_heritage_table_origins(context.store(), &host, name, &mut reads),
                Ok(()),
            );
            assert_eq!(reads, original);
            assert_eq!(snapshot(context.store()), pristine);
        }

        for (name, raw, alias, farther) in [
            (pending_name, pending_raw, pending, None),
            (alias_name, inner_alias_raw, inner_alias, Some(outer)),
        ] {
            let SourceLocalNamespaceLookup::LocalAliasPending { binding, error } =
                resolve_source_local_namespace_binding(context.store(), &host, name).unwrap()
            else {
                panic!("the original import still needs its real alias resolver");
            };
            assert_eq!(binding.raw_symbol(), raw);
            assert_eq!(binding.symbol(), alias);
            assert_eq!(
                error,
                CanonicalNameResolutionError::AliasResolutionUnavailable(alias),
            );
            let original = context
                .store()
                .alias_symbol_links(alias)
                .cloned()
                .unwrap_or_default();
            // Reserve only the empty link slot so each negative restores exactly.
            assert!(
                context
                    .store_mut_for_test()
                    .set_alias_symbol_links(alias, original.clone())
            );
            let clean = snapshot(context.store());
            for target in [AliasTargetState::Unknown, AliasTargetState::Resolved(value)] {
                let mut links = original.clone();
                links.alias_target = target;
                assert!(
                    context
                        .store_mut_for_test()
                        .set_alias_symbol_links(alias, links)
                );
                let damaged = snapshot(context.store());
                for _ in 0..2 {
                    let (result, _) = resolve_source_identifier_with_origins(
                        context.store(),
                        &host,
                        name,
                        SymbolFlags::NAMESPACE,
                        true,
                    )
                    .unwrap();
                    assert_eq!(result, Ok(farther));
                    assert_eq!(
                        resolve_source_local_namespace_binding(context.store(), &host, name)
                            .unwrap_err(),
                        DeclaredTypeError::from(
                            CanonicalNameResolutionError::AliasResolutionUnavailable(alias),
                        ),
                    );
                    assert_eq!(snapshot(context.store()), damaged);
                }
                assert!(
                    context
                        .store_mut_for_test()
                        .set_alias_symbol_links(alias, original.clone())
                );
                assert_eq!(snapshot(context.store()), clean);
                let SourceLocalNamespaceLookup::LocalAliasPending { binding, error } =
                    resolve_source_local_namespace_binding(context.store(), &host, name).unwrap()
                else {
                    panic!("restoration must not resolve or complete the import");
                };
                assert_eq!(binding.raw_symbol(), raw);
                assert_eq!(binding.symbol(), alias);
                assert_eq!(
                    error,
                    CanonicalNameResolutionError::AliasResolutionUnavailable(alias),
                );
                assert_eq!(snapshot(context.store()), clean);
            }
        }
        assert!(context.diagnostics().is_empty());
    }

    #[allow(clippy::too_many_lines)] // Keep the original bindings and each cold restore together.
    fn check_cold_source_alias_lookup_origins() {
        let parsed = parse_source_file(concat!(
            "export {}; type Left = { left: number }; type Right = { right: string };\n",
            "type Outside = number; declare const shadow: number;\n",
            "interface Derived extends Left { own: number }\n",
        ));
        let foreign = parse_source_file("export {}; type Left = { foreign: boolean };");
        let globals = parse_source_file("type Left = { fallback: boolean };");
        let file = FileId::new(203_187);
        let foreign_file = FileId::new(203_188);
        let globals_file = FileId::new(203_189);
        let sources = [
            (file, &parsed, CanonicalModuleState::External),
            (foreign_file, &foreign, CanonicalModuleState::External),
            (globals_file, &globals, CanonicalModuleState::Script),
        ];
        let mut binder = CanonicalBinder::new();
        for (file, parsed, module) in sources {
            assert!(parsed.diagnostics.is_empty());
            binder
                .bind_source_file_with_facts(
                    &parsed.arena,
                    parsed.source_file,
                    file,
                    CanonicalSourceFileFacts::new(
                        EscapedName::source(format!(
                            "\"/project/cold-heritage-{}.ts\"",
                            file.index()
                        )),
                        CanonicalSourceLanguage::TypeScript,
                        false,
                        module,
                    ),
                )
                .unwrap();
            binder
                .bind_typescript_declaration_slice(&parsed.arena, file)
                .unwrap();
        }
        let mut context = CanonicalCheckerContext::new(
            binder.finish(),
            sources
                .iter()
                .map(|(file, parsed, _)| (*file, &parsed.arena))
                .collect(),
            CanonicalCheckerOptions::default(),
        )
        .unwrap();
        let bound = context.file(file).unwrap().1.clone();
        let foreign_bound = context.file(foreign_file).unwrap().1.clone();
        let globals_bound = context.file(globals_file).unwrap().1.clone();
        let host = DeclaredTypeHost::new_after_global_merge(
            [
                (&parsed.arena, &bound),
                (&foreign.arena, &foreign_bound),
                (&globals.arena, &globals_bound),
            ],
            GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
        )
        .unwrap();
        let owner = interface_symbol(&parsed, file, &context, "Derived");
        let flags = context.store().symbol(owner).unwrap().flags();
        let type_ = super::super::declared::get_declared_class_interface_or_type_parameter(
            context.store_mut_for_test(),
            &host,
            owner,
            flags,
        )
        .unwrap()
        .unwrap();
        let (left, left_rhs) = source_alias_in_test(&parsed, file, &context, "Left");
        let (right, _) = source_alias_in_test(&parsed, file, &context, "Right");
        let (outside, _) = source_alias_in_test(&parsed, file, &context, "Outside");
        let (foreign_left, _) = source_alias_in_test(&foreign, foreign_file, &context, "Left");
        let (global_left, _) = source_alias_in_test(&globals, globals_file, &context, "Left");
        assert_ne!(left, foreign_left);
        assert_ne!(left, global_left);
        assert_eq!(
            context.store().symbol(left).unwrap().name(),
            context.store().symbol(foreign_left).unwrap().name(),
        );
        let locals = bound.locals(bound.source_file()).unwrap();
        let table = context.store().symbol_table(locals).unwrap();
        let original = table.get_source("Left").unwrap();
        let shadow = table.get_source("shadow").unwrap();
        assert_eq!(context.store().get_merged_symbol(original), Some(left));
        let declaration = context
            .store()
            .symbol(owner)
            .unwrap()
            .declarations()
            .unwrap()[0];
        let Some(PlainInterfaceHeritageFacts::Plain { bases, .. }) =
            context.store().source_plain_interface_heritage(declaration)
        else {
            panic!("the real Derived declaration has one plain base");
        };
        let expression = NodeRef::new(declaration.arena, declaration.file, bases[0].name);
        let expected = Err(source_heritage_error(expression));
        let snapshot = |store: &CanonicalTypeMapperStore| {
            (
                store.type_len(),
                store.symbol_len(),
                store.signature_len(),
                store.mapper_len(),
                store.symbol_store().symbol_table_len(),
                store.checker_link_allocated_lengths(),
                store.type_payload(type_).map(|record| {
                    let TypeData::Interface(data) = record.data() else {
                        panic!("the declared owner keeps its interface record");
                    };
                    (
                        record.id(),
                        record.flags(),
                        record.object_flags(),
                        record.symbol(),
                        record.alias(),
                        data.clone(),
                    )
                }),
                store.type_node_links(left_rhs).cloned(),
                store.type_alias_links(left).cloned(),
                store.symbol_node_links(expression).cloned(),
                store.source_interface_heritage_header(type_).cloned(),
                store.direct_interface_heritage_provenance(type_).cloned(),
            )
        };
        assert!(
            context
                .store()
                .source_interface_heritage_header(type_)
                .is_none()
        );
        for replacement in [right, foreign_left, shadow, outside] {
            assert_eq!(
                context.store_mut_for_test().insert_symbol(
                    locals,
                    EscapedName::source("Left"),
                    replacement,
                ),
                Some(Some(original)),
            );
            let damaged = snapshot(context.store());
            for _ in 0..2 {
                assert_eq!(
                    plan_source_interface_heritage_header(context.store(), &host, owner),
                    expected,
                );
                assert_eq!(snapshot(context.store()), damaged);
            }
            assert_eq!(
                context.store_mut_for_test().insert_symbol(
                    locals,
                    EscapedName::source("Left"),
                    original,
                ),
                Some(Some(replacement)),
            );
            let restored = snapshot(context.store());
            let header = plan_source_interface_heritage_header(context.store(), &host, owner)
                .unwrap()
                .unwrap();
            assert_eq!(header.bases()[0].symbol(), left);
            assert_eq!(header.bases()[0].alias().unwrap().root(), left_rhs);
            assert_eq!(snapshot(context.store()), restored);
        }
        let header = plan_source_interface_heritage_header(context.store(), &host, owner)
            .unwrap()
            .unwrap();
        let targets = Some(CanonicalArrayTargets::from_global_types(
            context.global_types(),
        ));
        assert!(
            validate_source_interface_heritage_header(context.store(), type_, &header, targets)
                .is_ok()
        );
        assert!(context.store().type_node_links(left_rhs).is_none());
        assert!(context.store().type_alias_links(left).is_none());
        // This table originally has no Left. Even an ignored type alias entry
        // must not become an authentic negative lookup before publication.
        let members = context.store().symbol(owner).unwrap().members().unwrap();
        assert_eq!(
            context.store_mut_for_test().insert_symbol(
                members,
                EscapedName::source("Left"),
                foreign_left,
            ),
            Some(None),
        );
        let damaged = snapshot(context.store());
        for _ in 0..2 {
            assert_eq!(
                plan_source_interface_heritage_header(context.store(), &host, owner),
                expected,
            );
            assert_eq!(snapshot(context.store()), damaged);
        }
        assert!(
            context
                .store()
                .source_interface_heritage_header(type_)
                .is_none()
        );
        assert!(
            context
                .store()
                .direct_interface_heritage_provenance(type_)
                .is_none()
        );
        assert!(context.diagnostics().is_empty());
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Keep the source and cache damage/restore pairs together.
    fn source_alias_heritage_rechecks_lookup_misses_and_cached_results() {
        check_cold_source_alias_lookup_origins();
        let parsed = parse_source_file(concat!(
            "type Extra = { extra: number }; type Other = { other: string };\n",
            "interface Base { base: boolean } interface AlternateBase { alternate: string }\n",
            "interface Derived extends Base, Extra { Extra: string; own: number }\n",
            "declare const value: Derived; const read: number = value.extra;\n",
        ));
        assert!(parsed.diagnostics.is_empty());
        let file = FileId::new(203_181);
        let mut context = checker_context(&parsed, file);
        let owner = interface_symbol(&parsed, file, &context, "Derived");
        let bound = context.file(file).unwrap().1.clone();
        let host = DeclaredTypeHost::new_after_global_merge(
            [(&parsed.arena, &bound)],
            GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
        )
        .unwrap();
        let flags = context.store().symbol(owner).unwrap().flags();
        let type_ = super::super::declared::get_declared_class_interface_or_type_parameter(
            context.store_mut_for_test(),
            &host,
            owner,
            flags,
        )
        .unwrap()
        .unwrap();
        let base = interface_symbol(&parsed, file, &context, "Base");
        let alternate = interface_symbol(&parsed, file, &context, "AlternateBase");
        context.get_declared_type_of_symbol(base).unwrap();
        let alternate_type = context.get_declared_type_of_symbol(alternate).unwrap();
        let targets = Some(CanonicalArrayTargets::from_global_types(
            context.global_types(),
        ));
        let cold_header = plan_source_interface_heritage_header(context.store(), &host, owner)
            .unwrap()
            .unwrap();
        let expected =
            DeclaredTypeError::from(DeclaredTypeUnavailable::InvalidCachedDeclaredType {
                symbol: owner,
                declared_type: type_,
            });
        let base_links = context.store().declared_type_links(base).unwrap().clone();
        let mut wrong_base = base_links.clone();
        wrong_base.declared_type = Some(alternate_type);
        assert!(
            context
                .store_mut_for_test()
                .set_declared_type_links(base, wrong_base)
        );
        let cold_snapshot = |store: &CanonicalTypeMapperStore| {
            (
                store.type_len(),
                store.symbol_len(),
                store.signature_len(),
                store.symbol_store().symbol_table_len(),
                store.checker_link_allocated_lengths(),
                store.declared_type_links(base).cloned(),
                store.type_payload(type_).map(|record| {
                    let TypeData::Interface(data) = record.data() else {
                        panic!("the declared owner keeps its interface record");
                    };
                    (
                        record.id(),
                        record.flags(),
                        record.object_flags(),
                        record.symbol(),
                        record.alias(),
                        data.clone(),
                    )
                }),
                store.source_interface_heritage_header(type_).cloned(),
                store.direct_interface_heritage_provenance(type_).cloned(),
            )
        };
        let damaged = cold_snapshot(context.store());
        assert_eq!(
            validate_source_interface_heritage_header(
                context.store(),
                type_,
                &cold_header,
                targets
            ),
            Err(expected)
        );
        assert!(
            !context
                .store_mut_for_test()
                .publish_source_interface_heritage_header(type_, cold_header.clone(), targets)
        );
        assert_eq!(cold_snapshot(context.store()), damaged);
        assert!(
            context
                .store_mut_for_test()
                .set_declared_type_links(base, base_links)
        );
        assert!(
            context
                .store_mut_for_test()
                .publish_source_interface_heritage_header(type_, cold_header, targets)
        );
        context.check_source_file(file).unwrap();
        assert_eq!(context.get_declared_type_of_symbol(owner), Ok(type_));
        let (alias, rhs) = source_alias_in_test(&parsed, file, &context, "Extra");
        let (other, _) = source_alias_in_test(&parsed, file, &context, "Other");
        let other_type = context.get_declared_type_of_symbol(other).unwrap();
        let header = context
            .store()
            .source_interface_heritage_header(type_)
            .unwrap()
            .clone();
        let complete = context
            .store()
            .direct_interface_heritage_provenance(type_)
            .unwrap()
            .clone();
        assert_eq!(header.owner_symbol(), owner);
        assert_eq!(header.bases().len(), 2);
        assert!(header.bases()[0].alias().is_none());
        assert_eq!(header.bases()[1].alias().unwrap().symbol(), alias);
        assert!(
            validate_source_interface_heritage_complete_bases(
                context.store(),
                type_,
                &header,
                &complete.bases,
                targets,
                None,
            )
            .is_ok()
        );
        let snapshot = |store: &CanonicalTypeMapperStore| {
            (
                store.type_len(),
                store.symbol_len(),
                store.signature_len(),
                store.mapper_len(),
                store.symbol_store().symbol_table_len(),
                store.checker_link_allocated_lengths(),
                store.type_payload(type_).map(|record| {
                    let TypeData::Interface(data) = record.data() else {
                        panic!("the declared owner keeps its interface record");
                    };
                    (
                        record.id(),
                        record.flags(),
                        record.object_flags(),
                        record.symbol(),
                        record.alias(),
                        data.clone(),
                    )
                }),
                store.type_node_links(rhs).cloned(),
                store.type_alias_links(alias).cloned(),
                store.direct_interface_heritage_provenance(type_).cloned(),
            )
        };
        // The member is a real wrong-meaning lookup before the global alias.
        let lookup = header.bases()[1]
            .resolution
            .lookups
            .iter()
            .find(|read| {
                read.entry.name.as_ref() == EscapedNameRef::source("Extra")
                    && read.entry.raw_entry.is_some()
                    && read.result.is_none()
            })
            .unwrap();
        let previous = lookup.entry.raw_entry.unwrap();
        assert_eq!(
            context.store_mut_for_test().insert_symbol(
                lookup.entry.table,
                EscapedName::source("Extra"),
                other,
            ),
            Some(Some(previous))
        );
        let damaged = snapshot(context.store());
        for _ in 0..2 {
            assert_eq!(
                validate_source_interface_heritage_header(context.store(), type_, &header, targets),
                Err(expected)
            );
            assert_eq!(snapshot(context.store()), damaged);
        }
        assert_eq!(
            context.store_mut_for_test().insert_symbol(
                lookup.entry.table,
                EscapedName::source("Extra"),
                previous,
            ),
            Some(Some(other))
        );
        let root_links = context.store().type_node_links(rhs).unwrap().clone();
        let mut wrong_root = root_links.clone();
        wrong_root.resolved_type = Some(other_type);
        assert!(
            context
                .store_mut_for_test()
                .set_type_node_links(rhs, wrong_root)
        );
        let damaged = snapshot(context.store());
        assert_eq!(
            validate_source_interface_heritage_header(context.store(), type_, &header, targets),
            Err(source_heritage_error(rhs))
        );
        assert_eq!(snapshot(context.store()), damaged);
        assert!(
            context
                .store_mut_for_test()
                .set_type_node_links(rhs, root_links)
        );
        let alias_links = context.store().type_alias_links(alias).unwrap().clone();
        let mut wrong_alias = alias_links.clone();
        wrong_alias.type_parameters = Some(Vec::new());
        assert!(
            context
                .store_mut_for_test()
                .set_type_alias_links(alias, wrong_alias)
        );
        let damaged = snapshot(context.store());
        assert_eq!(
            validate_source_interface_heritage_header(context.store(), type_, &header, targets),
            Err(source_heritage_error(rhs))
        );
        assert_eq!(snapshot(context.store()), damaged);
        assert!(
            context
                .store_mut_for_test()
                .set_type_alias_links(alias, alias_links)
        );
        let mut reordered = header.clone();
        reordered.bases.swap(0, 1);
        let restored = snapshot(context.store());
        assert_eq!(
            validate_source_interface_heritage_header(context.store(), type_, &reordered, targets),
            Err(expected)
        );
        assert_eq!(snapshot(context.store()), restored);
        assert!(
            validate_source_interface_heritage_complete_bases(
                context.store(),
                type_,
                &header,
                &complete.bases,
                targets,
                None,
            )
            .is_ok()
        );
        context.recheck_source_file(file).unwrap();
        assert_eq!(snapshot(context.store()), restored);
        assert!(context.diagnostics().is_empty());
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Keep both real alias roots and their independent replay together.
    fn source_alias_roots_keep_pending_and_shared_empty_identity_distinct() {
        let parsed = parse_source_file(concat!(
            "type Left = string extends string ? {} : { left: number };\n",
            "type Right = number extends number ? {} : { right: string };\n",
            "interface First extends Left { first: number }\n",
            "interface Second extends Right { second: number }\n",
        ));
        assert!(parsed.diagnostics.is_empty());
        let file = FileId::new(203_182);
        let mut context = checker_context(&parsed, file);
        let (left, left_root) = source_alias_in_test(&parsed, file, &context, "Left");
        let (right, right_root) = source_alias_in_test(&parsed, file, &context, "Right");
        let targets = Some(CanonicalArrayTargets::from_global_types(
            context.global_types(),
        ));
        let left_request = source_interface_alias_base_request(context.store(), left)
            .unwrap()
            .unwrap();
        let right_request = source_interface_alias_base_request(context.store(), right)
            .unwrap()
            .unwrap();
        let empty = context
            .store()
            .intrinsic_bootstrap()
            .unwrap()
            .empty_type_literal_type;
        for (symbol, root, request) in [
            (left, left_root, &left_request),
            (right, right_root, &right_request),
        ] {
            assert_eq!(context.get_type_from_type_node(root), Ok(empty));
            assert!(
                context
                    .store()
                    .type_alias_links(symbol)
                    .is_none_or(|links| links.declared_type.is_none())
            );
            assert!(matches!(
                source_interface_alias_base_state(context.store(), request, targets, None),
                Ok(SourceInterfaceAliasBaseState::Pending {
                    conditional: Some(_),
                    ..
                })
            ));
            assert_eq!(context.get_declared_type_of_symbol(symbol), Ok(empty));
            assert!(
                matches!(source_interface_alias_base_state(context.store(), request, targets, None),
                Ok(SourceInterfaceAliasBaseState::Ready { type_, .. }) if type_ == empty)
            );
        }
        assert_ne!(left_request, right_request);
        assert_ne!(left_request.root(), right_request.root());
        let mut wrong_root_owner = left_request.clone();
        wrong_root_owner.symbol = right;
        assert!(
            source_interface_alias_base_state(context.store(), &wrong_root_owner, targets, None)
                .is_err()
        );
        let first = interface_symbol(&parsed, file, &context, "First");
        let second = interface_symbol(&parsed, file, &context, "Second");
        let types = [
            context.get_declared_type_of_symbol(first).unwrap(),
            context.get_declared_type_of_symbol(second).unwrap(),
        ];
        for type_ in types {
            let record = context.store().type_payload(type_).unwrap();
            let TypeData::Interface(cold) = record.data() else {
                panic!("the declared identity must remain the real interface");
            };
            assert!(cold.this_type.is_some());
            assert!(!cold.base_types_resolved);
            assert!(!cold.declared_members_resolved);
            assert!(cold.resolved_base_types.is_none());
            assert_eq!(cold.reference.object.structured, Default::default());
            assert!(
                context
                    .store()
                    .source_interface_heritage_header(type_)
                    .is_some()
            );
            assert!(
                context
                    .store()
                    .direct_interface_heritage_provenance(type_)
                    .is_none()
            );
            // The normal relation must complete the header before its identity shortcut.
            assert_eq!(context.is_type_assignable_to(type_, type_), Ok(true));
            let header = context
                .store()
                .source_interface_heritage_header(type_)
                .unwrap();
            let complete = context
                .store()
                .direct_interface_heritage_provenance(type_)
                .unwrap();
            assert_eq!(complete.bases[0].1, empty);
            assert!(
                validate_source_interface_heritage_complete_bases(
                    context.store(),
                    type_,
                    header,
                    &complete.bases,
                    targets,
                    None
                )
                .is_ok()
            );
        }
        let warm = (
            context.store().type_len(),
            context.store().conditional_root_len(),
            context.store().checker_link_allocated_lengths(),
        );
        for (symbol, root, request) in [
            (left, left_root, &left_request),
            (right, right_root, &right_request),
        ] {
            assert_eq!(context.get_declared_type_of_symbol(symbol), Ok(empty));
            assert_eq!(context.get_type_from_type_node(root), Ok(empty));
            assert!(
                matches!(source_interface_alias_base_state(context.store(), request, targets, None),
                Ok(SourceInterfaceAliasBaseState::Ready { type_, .. }) if type_ == empty)
            );
        }
        assert_eq!(
            (
                context.store().type_len(),
                context.store().conditional_root_len(),
                context.store().checker_link_allocated_lengths()
            ),
            warm
        );
        assert!(context.diagnostics().is_empty());
    }

    #[test]
    fn source_alias_literal_ready_rechecks_the_current_array_targets() {
        let parsed = parse_source_file(concat!(
            "interface Array<T> {} interface ReadonlyArray<T> {}\n",
            "type Items = { values: number[] }; interface Derived extends Items { own: number }\n",
        ));
        assert!(parsed.diagnostics.is_empty());
        let file = FileId::new(203_183);
        let mut context = checker_context(&parsed, file);
        let (owner, _) = source_alias_in_test(&parsed, file, &context, "Items");
        let result = context.get_declared_type_of_symbol(owner).unwrap();
        let request = source_interface_alias_base_request(context.store(), owner)
            .unwrap()
            .unwrap();
        let targets = CanonicalArrayTargets::from_global_types(context.global_types());
        let wrong = CanonicalArrayTargets::for_test(
            context.global_types().readonly_array_type,
            context.global_types().array_type,
        );
        let warm = (
            context.store().type_len(),
            context.store().signature_len(),
            context.store().mapper_len(),
            context.store().checker_link_allocated_lengths(),
        );
        assert!(
            matches!(source_interface_alias_base_state(context.store(), &request, Some(targets), None),
            Ok(SourceInterfaceAliasBaseState::Ready { type_, .. }) if type_ == result)
        );
        assert!(
            source_interface_alias_base_state(context.store(), &request, Some(wrong), None)
                .is_err()
        );
        assert!(source_interface_alias_base_state(context.store(), &request, None, None).is_err());
        assert!(
            matches!(source_interface_alias_base_state(context.store(), &request, Some(targets), None),
            Ok(SourceInterfaceAliasBaseState::Ready { type_, .. }) if type_ == result)
        );
        assert_eq!(
            (
                context.store().type_len(),
                context.store().signature_len(),
                context.store().mapper_len(),
                context.store().checker_link_allocated_lengths()
            ),
            warm
        );
        assert!(context.diagnostics().is_empty());
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Check the override boundary before any member publication.
    fn source_alias_overrides_require_exact_nonobject_types_before_publication() {
        use crate::semantic::{
            declared::get_declared_class_interface_or_type_parameter,
            object_members::{self, PropertyObjectError},
            structured_members::resolve_direct_interface_members_with_query_context,
        };

        for (base_text, own_text, accepted) in [
            ("number", "number", true),
            ("Plain", "Plain", false),
            ("Plain", "Inherited", false),
        ] {
            let parsed = parse_source_file(&format!(
                "interface Plain {{ value: number }}\n\
                 interface Base<T> {{ value: T }}\n\
                 interface Inherited extends Base<number> {{}}\n\
                 type Added = {{ item: {base_text} }};\n\
                 interface Derived extends Added {{ item: {own_text} }}\n"
            ));
            assert!(parsed.diagnostics.is_empty());
            let file = FileId::new(203_186);
            let mut context = checker_context(&parsed, file);
            let owner = interface_symbol(&parsed, file, &context, "Derived");
            let (alias, _) = source_alias_in_test(&parsed, file, &context, "Added");
            let own_type = if own_text == "number" {
                context.store().intrinsic_bootstrap().unwrap().number_type
            } else {
                let symbol = interface_symbol(&parsed, file, &context, own_text);
                context.get_declared_type_of_symbol(symbol).unwrap()
            };
            let alias_type = context.get_declared_type_of_symbol(alias).unwrap();
            let bound = context.file(file).unwrap().1.clone();
            let host = DeclaredTypeHost::new_after_global_merge(
                [(&parsed.arena, &bound)],
                GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
            )
            .unwrap();
            let flags = context.store().symbol(owner).unwrap().flags();
            let type_ = get_declared_class_interface_or_type_parameter(
                context.store_mut_for_test(),
                &host,
                owner,
                flags,
            )
            .unwrap()
            .unwrap();
            let targets = Some(CanonicalArrayTargets::from_global_types(
                context.global_types(),
            ));
            let plan = object_members::plan_interface(context.store(), &host, owner).unwrap();
            let header = plan_source_interface_heritage_header(context.store(), &host, owner)
                .unwrap()
                .unwrap();
            assert!(
                context
                    .store_mut_for_test()
                    .publish_source_interface_heritage_header(type_, header, targets)
            );
            let property = &plan.properties[0];
            let expected = if accepted {
                Ok(type_)
            } else {
                Err(PropertyObjectError::UnsupportedMember {
                    node: property.declaration,
                    kind: SyntaxKind::PropertySignature,
                })
            };
            let snapshot = |store: &CanonicalTypeMapperStore| {
                (
                    store.type_len(),
                    store.symbol_len(),
                    store.signature_len(),
                    store.mapper_len(),
                    store.symbol_store().symbol_table_len(),
                    store.checker_link_allocated_lengths(),
                    store.type_payload(type_).map(|record| {
                        let TypeData::Interface(data) = record.data() else {
                            panic!("the declared owner keeps its interface record");
                        };
                        (
                            record.id(),
                            record.flags(),
                            record.object_flags(),
                            record.symbol(),
                            record.alias(),
                            data.clone(),
                        )
                    }),
                    store.value_symbol_links(property.symbol).cloned(),
                    store.source_interface_heritage_header(type_).cloned(),
                    store.direct_interface_heritage_provenance(type_).cloned(),
                )
            };
            let before = snapshot(context.store());
            assert_eq!(
                resolve_direct_interface_members_with_query_context(
                    context.store_mut_for_test(),
                    &plan,
                    type_,
                    &[own_type],
                    &[alias_type],
                    targets,
                    None,
                ),
                expected,
            );
            if !accepted {
                assert_eq!(snapshot(context.store()), before);
                assert!(
                    context
                        .store()
                        .direct_interface_heritage_provenance(type_)
                        .is_none()
                );
            }
            let warm = snapshot(context.store());
            assert_eq!(
                resolve_direct_interface_members_with_query_context(
                    context.store_mut_for_test(),
                    &plan,
                    type_,
                    &[own_type],
                    &[alias_type],
                    targets,
                    None,
                ),
                expected,
            );
            assert_eq!(snapshot(context.store()), warm);
            assert!(context.diagnostics().is_empty());
        }
    }

    #[test]
    fn inherited_optional_methods_preserve_source_signatures_cold_and_warm() {
        for exact_optional_property_types in [false, true] {
            for member in [
                "read?(): number",
                "read(value?: number): number",
                "read(value?: number | string): number",
                "read(value?: null): number",
            ] {
                let parsed = parse_source_file(&format!(
                    "interface Base {{ {member} }} interface Derived extends Base {{}}"
                ));
                assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
                let file = FileId::new(8_600);
                let mut context = checker_context_with_options(
                    &parsed,
                    file,
                    CanonicalCheckerOptions {
                        intrinsic: IntrinsicBootstrapOptions {
                            strict_null_checks: true,
                            exact_optional_property_types,
                        },
                        ..CanonicalCheckerOptions::default()
                    },
                );
                let derived = interface_symbol(&parsed, file, &context, "Derived");
                let target = context.get_declared_type_of_symbol(derived).unwrap();
                assert_eq!(
                    crate::semantic::structured_members::validate_interface_heritage_members(
                        context.store(),
                        target,
                    ),
                    crate::semantic::structured_members::InterfaceHeritageMembersValidation::Valid,
                    "{member}",
                );
                context.check_source_file(file).unwrap();
                assert!(context.diagnostics().is_empty());
                let warm = (
                    context.store().type_len(),
                    context.store().signature_len(),
                    context.store().mapper_len(),
                    context.store().checker_link_allocated_lengths(),
                );
                assert_eq!(context.get_declared_type_of_symbol(derived), Ok(target));
                context.recheck_source_file(file).unwrap();
                assert_eq!(
                    (
                        context.store().type_len(),
                        context.store().signature_len(),
                        context.store().mapper_len(),
                        context.store().checker_link_allocated_lengths(),
                    ),
                    warm,
                    "{member}",
                );
            }
        }
    }

    #[test]
    fn inherited_optional_methods_reject_missing_and_uncached_wrappers() {
        for exact_optional_property_types in [false, true] {
            let parsed = parse_source_file(concat!(
                "interface Base { read?(): number; parameter(value?: number): number } ",
                "interface Derived extends Base {}",
            ));
            let file = FileId::new(8_601);
            let mut context = checker_context_with_options(
                &parsed,
                file,
                CanonicalCheckerOptions {
                    intrinsic: IntrinsicBootstrapOptions {
                        strict_null_checks: true,
                        exact_optional_property_types,
                    },
                    ..CanonicalCheckerOptions::default()
                },
            );
            let base = interface_symbol(&parsed, file, &context, "Base");
            let derived = interface_symbol(&parsed, file, &context, "Derived");
            let target = context.get_declared_type_of_symbol(derived).unwrap();
            let members = context.store().symbol(base).unwrap().members().unwrap();
            let table = context.store().symbol_table(members).unwrap();
            let (method, parameter_method) = (
                table.get_source("read").unwrap(),
                table.get_source("parameter").unwrap(),
            );
            let original = context.store().value_symbol_links(method).unwrap().clone();
            let value = original.resolved_type.unwrap();
            let record = context.store().type_payload(value).unwrap();
            let TypeData::Union(union) = record.data() else {
                panic!("an optional method must retain its union wrapper")
            };
            let flags = record.object_flags();
            let types = union.union.types.clone();
            let sentinel = context
                .store()
                .intrinsic_bootstrap()
                .unwrap()
                .undefined_or_missing_type;
            let callable = *types.iter().find(|type_| **type_ != sentinel).unwrap();
            let forged = context
                .store_mut_for_test()
                .alloc_union_type(flags, types)
                .unwrap();
            let parameter_value = context
                .store()
                .value_symbol_links(parameter_method)
                .unwrap()
                .resolved_type
                .unwrap();
            let signature = crate::semantic::structured_members::valid_interface_method_value(
                context.store(),
                parameter_method,
                parameter_value,
            )
            .unwrap();
            let parameter = context.store().signature(signature).unwrap().parameters()[0];
            let original_parameter = context
                .store()
                .value_symbol_links(parameter)
                .unwrap()
                .clone();
            let number = context.store().intrinsic_bootstrap().unwrap().number_type;
            let warm = (
                context.store().type_len(),
                context.store().signature_len(),
                context.store().mapper_len(),
                context.store().checker_link_allocated_lengths(),
            );
            for (symbol, replacement, restore) in [
                (method, callable, original.clone()),
                (method, forged, original.clone()),
                (parameter, number, original_parameter),
            ] {
                let mut changed = restore.clone();
                changed.resolved_type = Some(replacement);
                assert!(
                    context
                        .store_mut_for_test()
                        .set_value_symbol_links(symbol, changed)
                );
                assert!(context.get_declared_type_of_symbol(derived).is_err());
                assert_eq!(
                    (
                        context.store().type_len(),
                        context.store().signature_len(),
                        context.store().mapper_len(),
                        context.store().checker_link_allocated_lengths(),
                    ),
                    warm,
                );
                assert!(
                    context
                        .store_mut_for_test()
                        .set_value_symbol_links(symbol, restore)
                );
                assert_eq!(context.get_declared_type_of_symbol(derived), Ok(target));
            }
        }
    }

    fn interface_symbol(
        parsed: &ParseResult,
        file: FileId,
        context: &CanonicalCheckerContext<'_>,
        expected: &str,
    ) -> SemanticSymbolId {
        let declaration = parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                let NodeData::InterfaceDeclaration(interface) = &record.data else {
                    return None;
                };
                let NodeData::Identifier(name) = &parsed.arena.get(interface.name)?.data else {
                    return None;
                };
                (name.text == expected).then_some(NodeRef::new(parsed.arena.id(), file, node))
            })
            .unwrap();
        let symbol = context.file(file).unwrap().1.symbol(declaration).unwrap();
        context.store().get_merged_symbol(symbol).unwrap()
    }

    fn heritage_plan(
        parsed: &ParseResult,
        file: FileId,
        context: &CanonicalCheckerContext<'_>,
        expected: &str,
    ) -> Result<DirectInterfaceHeritagePlan, DirectInterfaceHeritageError> {
        let declaration = parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                let NodeData::InterfaceDeclaration(interface) = &record.data else {
                    return None;
                };
                let NodeData::Identifier(name) = &parsed.arena.get(interface.name)?.data else {
                    return None;
                };
                (name.text == expected).then_some(NodeRef::new(parsed.arena.id(), file, node))
            })
            .unwrap();
        let NodeData::InterfaceDeclaration(interface) =
            &parsed.arena.get(declaration.node).unwrap().data
        else {
            unreachable!("the declaration was selected by its interface payload")
        };
        let sources = context
            .file_order()
            .iter()
            .map(|file| context.file(*file).unwrap())
            .collect::<Vec<_>>();
        let host = DeclaredTypeHost::new_after_global_merge(
            sources,
            GlobalMergeCompletion::for_test(context.options().name_resolution),
        )
        .unwrap();
        plan_direct_interface_heritage(
            context.store(),
            &host,
            declaration,
            interface_symbol(parsed, file, context, expected),
            interface.heritage_clauses.as_ref().unwrap(),
        )
    }

    fn default_library_heritage_context<'arena>(
        library: &'arena ParseResult,
        source: &'arena ParseResult,
        default_library: bool,
    ) -> (CanonicalCheckerContext<'arena>, FileId, FileId) {
        let library_file = FileId::new(8_470);
        let source_file = FileId::new(8_471);
        let mut binder = CanonicalBinder::new();
        for (parsed, file, is_default_library) in [
            (library, library_file, default_library),
            (source, source_file, false),
        ] {
            binder
                .bind_source_file_with_facts(
                    &parsed.arena,
                    parsed.source_file,
                    file,
                    CanonicalSourceFileFacts::new_with_default_library(
                        EscapedName::source(format!("\"/dom-heritage-{}.d.ts\"", file.index())),
                        CanonicalSourceLanguage::TypeScript,
                        true,
                        is_default_library,
                        CanonicalModuleState::Script,
                    ),
                )
                .unwrap();
            binder
                .bind_typescript_declaration_slice(&parsed.arena, file)
                .unwrap();
        }
        let context = CanonicalCheckerContext::new(
            binder.finish(),
            vec![(library_file, &library.arena), (source_file, &source.arena)],
            CanonicalCheckerOptions::default(),
        )
        .unwrap();
        (context, library_file, source_file)
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Keep Array, React exports, private aliases, and warm identity together.
    fn default_library_array_bases_keep_recursive_react_module_nodes_lazy() {
        let library = parse_source_file(concat!(
            "interface Array<Value> { length: number }\n",
            "declare var Array: any;\n",
            "interface ReadonlyArray<Value> {}\n",
        ));
        let source = parse_source_file(concat!(
            "declare module 'react' {\n",
            "  export = React;\n",
            "  namespace React {\n",
            "    type Key = string | number;\n",
            "    interface ComponentClass<Props> {}\n",
            "    interface SFC<Props> {}\n",
            "    interface ReactElement<Props> {\n",
            "      type: string | ComponentClass<Props> | SFC<Props>;\n",
            "      props: Props;\n",
            "      key: Key | null;\n",
            "    }\n",
            "    interface ReactNodeArray extends Array<ReactNode> {}\n",
            "    type ReactFragment = {} | ReactNodeArray;\n",
            "    interface ReactPortal extends ReactElement<any> {\n",
            "      key: Key | null;\n",
            "      children: ReactNode;\n",
            "    }\n",
            "    type ReactNode = ReactElement<any> | ReactFragment | ReactPortal | ",
            "string | number | boolean | null | undefined;\n",
            "  }\n",
            "  type MergePropTypes<Props, Inferred> = Props & Inferred;\n",
            "}\n",
        ));
        assert!(library.diagnostics.is_empty(), "{:?}", library.diagnostics);
        assert!(source.diagnostics.is_empty(), "{:?}", source.diagnostics);
        let (mut context, library_file, source_file) =
            default_library_heritage_context(&library, &source, true);
        let array = interface_symbol(&library, library_file, &context, "Array");
        let react_array = interface_symbol(&source, source_file, &context, "ReactNodeArray");
        let portal = interface_symbol(&source, source_file, &context, "ReactPortal");
        let namespace = context.store().get_parent_of_symbol(react_array).unwrap();
        let exports = context
            .store()
            .symbol(namespace)
            .and_then(ts_binder::semantic::Symbol::exports)
            .unwrap();
        let react_node = context
            .store()
            .symbol_table(exports)
            .and_then(|exports| exports.get_source("ReactNode"))
            .unwrap();
        let module = source
            .arena
            .iter()
            .find_map(|(node, record)| {
                let NodeData::ModuleDeclaration(module) = &record.data else {
                    return None;
                };
                matches!(
                    source.arena.get(module.name).map(|name| &name.data),
                    Some(NodeData::StringLiteral(name)) if name.text == "react"
                )
                .then_some(NodeRef::new(source.arena.id(), source_file, node))
            })
            .unwrap();
        let source_bound = context.file(source_file).unwrap().1.clone();
        let module_symbol = source_bound.symbol(module).unwrap();
        let module_exports = context
            .store()
            .symbol(module_symbol)
            .and_then(ts_binder::semantic::Symbol::exports)
            .unwrap();
        let export_assignment = context
            .store()
            .symbol_table(module_exports)
            .and_then(|exports| exports.get(InternalSymbolName::ExportEquals.as_ref()))
            .unwrap();
        let private_alias = source_bound
            .locals(module)
            .and_then(|locals| context.store().symbol_table(locals))
            .and_then(|locals| locals.get_source("MergePropTypes"))
            .unwrap();
        assert_eq!(
            context.store().symbol(array).unwrap().flags(),
            SymbolFlags::INTERFACE | SymbolFlags::FUNCTION_SCOPED_VARIABLE,
        );
        assert_eq!(
            context
                .store()
                .declared_type_links(array)
                .and_then(|links| links.declared_type),
            Some(context.global_types().array_type),
        );
        assert!(
            context
                .store()
                .symbol(private_alias)
                .unwrap()
                .parent()
                .is_none()
        );
        assert!(
            context
                .store()
                .symbol_table(module_exports)
                .and_then(|exports| exports.get_source("MergePropTypes"))
                .is_none()
        );
        let cold = (
            context.store().type_len(),
            context.store().signature_len(),
            context.store().symbol_store().symbol_table_len(),
            context.store().checker_link_allocated_lengths(),
        );

        let planned = heritage_plan(&source, source_file, &context, "ReactNodeArray").unwrap();
        let [inherited] = planned.bases.as_slice() else {
            panic!("ReactNodeArray must retain the one default-library Array base")
        };
        assert_eq!(inherited.symbol, array);
        assert_eq!(inherited.kind, DirectInterfaceBaseKind::DefaultLibraryArray);
        let [argument] = inherited.type_arguments.as_slice() else {
            panic!("the Array base must retain its recursive ReactNode argument")
        };
        assert_eq!(
            source.arena.get(argument.node).unwrap().kind,
            SyntaxKind::TypeReference,
        );
        let library_bound = context.file(library_file).unwrap().1.clone();
        let host = DeclaredTypeHost::new_after_global_merge(
            [
                (&library.arena, &library_bound),
                (&source.arena, &source_bound),
            ],
            GlobalMergeCompletion::for_test(context.options().name_resolution),
        )
        .unwrap();
        let properties =
            crate::semantic::object_members::plan_interface(context.store(), &host, react_array)
                .unwrap();
        assert!(properties.properties.is_empty());
        assert_eq!(properties.heritage.as_ref(), Some(&planned));
        let portal_plan =
            crate::semantic::object_members::plan_interface(context.store(), &host, portal)
                .unwrap();
        assert_eq!(
            portal_plan
                .properties
                .iter()
                .map(|property| property.name.as_utf8().unwrap())
                .collect::<Vec<_>>(),
            ["key", "children"],
        );
        assert!(
            crate::semantic::object_members::authenticated_react_portal_interface(
                context.store(),
                &host,
                &portal_plan,
            )
            .unwrap()
        );
        assert_eq!(
            (
                context.store().type_len(),
                context.store().signature_len(),
                context.store().symbol_store().symbol_table_len(),
                context.store().checker_link_allocated_lengths(),
            ),
            cold,
        );

        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        let options = context.options();
        let resolved = CanonicalTypeQuery::new(
            context.store_mut_for_test(),
            &host,
            options,
            &mut diagnostics,
        )
        .unwrap()
        .get_declared_type_of_symbol(react_node)
        .unwrap();
        assert!(context.store().type_payload(resolved).is_some());
        let array_shell = context
            .store()
            .declared_type_links(react_array)
            .and_then(|links| links.declared_type)
            .unwrap();
        let array_record = context.store().type_payload(array_shell).unwrap();
        let TypeData::Interface(interface) = array_record.data() else {
            panic!("ReactNodeArray must retain an authenticated interface shell")
        };
        assert_eq!(
            array_record.object_flags(),
            ObjectFlags::INTERFACE | ObjectFlags::REFERENCE,
        );
        assert!(
            validate_nongeneric_interface_argument_origin(context.store(), array_shell).is_ok()
        );
        assert!(!interface.base_types_resolved);
        assert!(!interface.declared_members_resolved);
        assert_eq!(
            context.store().validate_union_constituent(array_shell),
            Ok(())
        );
        let portal_shell = context
            .store()
            .declared_type_links(portal)
            .and_then(|links| links.declared_type)
            .unwrap();
        let portal_record = context.store().type_payload(portal_shell).unwrap();
        let TypeData::Interface(portal_data) = portal_record.data() else {
            panic!("ReactPortal must retain an authenticated interface shell")
        };
        assert_eq!(
            portal_record.object_flags(),
            ObjectFlags::INTERFACE | ObjectFlags::REFERENCE,
        );
        assert!(!portal_data.base_types_resolved);
        assert!(!portal_data.declared_members_resolved);
        assert_eq!(
            context.store().validate_union_constituent(portal_shell),
            Ok(())
        );
        assert!(portal_plan.properties.iter().all(|property| {
            context
                .store()
                .value_symbol_links(property.symbol)
                .is_none()
        }));
        assert!(
            context
                .store()
                .alias_symbol_links(export_assignment)
                .is_none_or(|links| links.alias_target == AliasTargetState::Resolved(namespace))
        );
        assert!(context.store().type_alias_links(private_alias).is_none());
        let warm = (
            context.store().type_len(),
            context.store().signature_len(),
            context.store().symbol_store().symbol_table_len(),
            context.store().checker_link_allocated_lengths(),
        );
        assert_eq!(
            CanonicalTypeQuery::new(
                context.store_mut_for_test(),
                &host,
                options,
                &mut diagnostics,
            )
            .unwrap()
            .get_declared_type_of_symbol(react_node),
            Ok(resolved),
        );
        assert_eq!(
            (
                context.store().type_len(),
                context.store().signature_len(),
                context.store().symbol_store().symbol_table_len(),
                context.store().checker_link_allocated_lengths(),
            ),
            warm,
        );
        assert!(diagnostics.is_empty());

        assert!(context.store_mut_for_test().set_interface_base_resolution(
            array_shell,
            true,
            None,
            None
        ));
        assert_eq!(
            context.store().validate_union_constituent(array_shell),
            Err(LiteralTypeCacheError::InvalidCachedUnion(array_shell)),
        );
        assert!(context.store_mut_for_test().set_interface_base_resolution(
            portal_shell,
            true,
            None,
            None
        ));
        assert_eq!(
            context.store().validate_union_constituent(portal_shell),
            Err(LiteralTypeCacheError::InvalidCachedUnion(portal_shell)),
        );
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Keep portal ownership, generic base, and warm union identity together.
    fn react_portal_generic_base_preserves_binder_properties_and_lazy_union_identity() {
        let library = parse_source_file(concat!(
            "interface Array<Value> { length: number }\n",
            "declare var Array: any;\n",
            "interface ReadonlyArray<Value> {}\n",
        ));
        let source = parse_source_file(concat!(
            "declare module 'react' {\n",
            "  export = React;\n",
            "  namespace React {\n",
            "    type Key = string | number;\n",
            "    interface ComponentClass<Props> {}\n",
            "    interface SFC<Props> {}\n",
            "    interface ReactElement<Props> {\n",
            "      type: string | ComponentClass<Props> | SFC<Props>;\n",
            "      props: Props;\n",
            "      key: Key | null;\n",
            "    }\n",
            "    interface ReactPortal extends ReactElement<any> {\n",
            "      key: Key | null;\n",
            "      children: ReactNode;\n",
            "    }\n",
            "    type ReactNode = ReactElement<any> | ReactPortal | string;\n",
            "  }\n",
            "  type MergePropTypes<Props, Inferred> = Props & Inferred;\n",
            "}\n",
        ));
        assert!(library.diagnostics.is_empty(), "{:?}", library.diagnostics);
        assert!(source.diagnostics.is_empty(), "{:?}", source.diagnostics);
        let (mut context, library_file, source_file) =
            default_library_heritage_context(&library, &source, true);
        let element = interface_symbol(&source, source_file, &context, "ReactElement");
        let portal = interface_symbol(&source, source_file, &context, "ReactPortal");
        let planned = heritage_plan(&source, source_file, &context, "ReactPortal").unwrap();
        let [base] = planned.bases.as_slice() else {
            panic!("ReactPortal must retain its single ReactElement<any> base")
        };
        assert_eq!(base.symbol, element);
        assert_eq!(base.type_arguments.len(), 1);
        let library_bound = context.file(library_file).unwrap().1.clone();
        let source_bound = context.file(source_file).unwrap().1.clone();
        let host = DeclaredTypeHost::new_after_global_merge(
            [
                (&library.arena, &library_bound),
                (&source.arena, &source_bound),
            ],
            GlobalMergeCompletion::for_test(context.options().name_resolution),
        )
        .unwrap();
        let cold = (
            context.store().type_len(),
            context.store().signature_len(),
            context.store().symbol_store().symbol_table_len(),
            context.store().checker_link_allocated_lengths(),
        );

        let properties =
            crate::semantic::object_members::plan_interface(context.store(), &host, portal)
                .unwrap();
        assert_eq!(properties.heritage.as_ref(), Some(&planned));
        assert_eq!(
            properties
                .properties
                .iter()
                .map(|property| property.name.as_utf8().unwrap())
                .collect::<Vec<_>>(),
            ["key", "children"],
        );
        assert!(
            crate::semantic::object_members::authenticated_react_portal_interface(
                context.store(),
                &host,
                &properties,
            )
            .unwrap()
        );
        assert_eq!(
            (
                context.store().type_len(),
                context.store().signature_len(),
                context.store().symbol_store().symbol_table_len(),
                context.store().checker_link_allocated_lengths(),
            ),
            cold,
        );

        let namespace = context.store().get_parent_of_symbol(portal).unwrap();
        let react_node = context
            .store()
            .symbol(namespace)
            .and_then(ts_binder::semantic::Symbol::exports)
            .and_then(|exports| context.store().symbol_table(exports))
            .and_then(|exports| exports.get_source("ReactNode"))
            .unwrap();
        let options = context.options();
        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        let resolved = CanonicalTypeQuery::new(
            context.store_mut_for_test(),
            &host,
            options,
            &mut diagnostics,
        )
        .unwrap()
        .get_declared_type_of_symbol(react_node)
        .unwrap();
        let shell = context
            .store()
            .declared_type_links(portal)
            .and_then(|links| links.declared_type)
            .unwrap();
        assert_eq!(context.store().validate_union_constituent(shell), Ok(()));
        let warm = (
            context.store().type_len(),
            context.store().signature_len(),
            context.store().checker_link_allocated_lengths(),
        );
        assert_eq!(
            CanonicalTypeQuery::new(
                context.store_mut_for_test(),
                &host,
                options,
                &mut diagnostics,
            )
            .unwrap()
            .get_declared_type_of_symbol(react_node),
            Ok(resolved),
        );
        assert_eq!(
            (
                context.store().type_len(),
                context.store().signature_len(),
                context.store().checker_link_allocated_lengths(),
            ),
            warm,
        );
        assert!(diagnostics.is_empty());
    }

    #[test]
    fn react_array_heritage_rejects_non_default_library_lookalikes_without_publication() {
        let library = parse_source_file(concat!(
            "interface Array<Value> { length: number }\n",
            "declare var Array: any;\n",
            "interface ReadonlyArray<Value> {}\n",
        ));
        let source = parse_source_file(concat!(
            "declare namespace React {\n",
            "  interface ReactNodeArray extends Array<ReactNode> {}\n",
            "  type ReactNode = string | ReactNodeArray;\n",
            "}\n",
        ));
        let (context, _, source_file) = default_library_heritage_context(&library, &source, false);
        let cold = (
            context.store().type_len(),
            context.store().signature_len(),
            context.store().symbol_store().symbol_table_len(),
            context.store().checker_link_allocated_lengths(),
        );

        assert!(matches!(
            heritage_plan(&source, source_file, &context, "ReactNodeArray"),
            Err(DirectInterfaceHeritageError::Unsupported {
                kind: SyntaxKind::ExpressionWithTypeArguments,
                ..
            })
        ));
        assert_eq!(
            (
                context.store().type_len(),
                context.store().signature_len(),
                context.store().symbol_store().symbol_table_len(),
                context.store().checker_link_allocated_lengths(),
            ),
            cold,
        );
    }

    #[test]
    fn default_library_dom_interface_value_bases_remain_cold_and_canonical() {
        let library = parse_source_file(concat!(
            "interface DomRoot { root: string }\n",
            "interface DomExtra {}\n",
            "interface DomMore {}\n",
            "interface HTMLElement extends DomRoot, DomExtra, DomMore {\n",
            "  addEventListener(value: string): void;\n",
            "}\n",
            "declare var HTMLElement: unknown;\n",
        ));
        let source = parse_source_file("interface HTMLWebViewElement extends HTMLElement {}\n");
        assert!(library.diagnostics.is_empty(), "{:?}", library.diagnostics);
        assert!(source.diagnostics.is_empty(), "{:?}", source.diagnostics);
        let (mut context, library_file, source_file) =
            default_library_heritage_context(&library, &source, true);
        let base = interface_symbol(&library, library_file, &context, "HTMLElement");
        let cold = (
            context.store().type_len(),
            context.store().signature_len(),
            context.store().symbol_store().symbol_table_len(),
            context.store().checker_link_allocated_lengths(),
        );

        let planned = heritage_plan(&source, source_file, &context, "HTMLWebViewElement").unwrap();
        let [inherited] = planned.bases.as_slice() else {
            panic!("the default-library DOM interface must remain the sole direct base")
        };
        assert_eq!(inherited.symbol, base);
        assert_eq!(
            inherited.kind,
            DirectInterfaceBaseKind::DefaultLibraryInterface
        );
        assert!(inherited.type_arguments.is_empty());
        assert_eq!(
            context.store().symbol(base).unwrap().flags(),
            SymbolFlags::INTERFACE | SymbolFlags::FUNCTION_SCOPED_VARIABLE
        );
        assert!(context.store().declared_type_links(base).is_none());
        assert_eq!(
            (
                context.store().type_len(),
                context.store().signature_len(),
                context.store().symbol_store().symbol_table_len(),
                context.store().checker_link_allocated_lengths(),
            ),
            cold
        );
        assert_eq!(
            heritage_plan(&source, source_file, &context, "HTMLWebViewElement").unwrap(),
            planned
        );

        assert!(context.store_mut_for_test().set_symbol_flags(
            base,
            SymbolFlags::INTERFACE | SymbolFlags::FUNCTION_SCOPED_VARIABLE | SymbolFlags::TRANSIENT,
            CheckFlags::NONE,
        ));
        let transient_state = (
            context.store().type_len(),
            context.store().signature_len(),
            context.store().symbol_store().symbol_table_len(),
            context.store().checker_link_allocated_lengths(),
        );
        assert_eq!(
            heritage_plan(&source, source_file, &context, "HTMLWebViewElement").unwrap(),
            planned
        );
        assert_eq!(
            (
                context.store().type_len(),
                context.store().signature_len(),
                context.store().symbol_store().symbol_table_len(),
                context.store().checker_link_allocated_lengths(),
            ),
            transient_state
        );
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Keep the ordinary source case beside the provenance checks.
    fn default_library_dom_interface_bases_reject_forged_provenance() {
        let library = parse_source_file(concat!(
            "interface HTMLElement { value: string }\n",
            "declare var HTMLElement: unknown;\n",
        ));
        let source = parse_source_file("interface HTMLWebViewElement extends HTMLElement {}\n");
        assert!(library.diagnostics.is_empty(), "{:?}", library.diagnostics);
        assert!(source.diagnostics.is_empty(), "{:?}", source.diagnostics);
        let source_edges = source
            .arena
            .iter()
            .filter_map(|(node, record)| {
                let NodeData::ExpressionWithTypeArguments(base) = &record.data else {
                    return None;
                };
                Some((node, base.expression, record.parent?))
            })
            .collect::<Vec<_>>();
        let [(edge, expression, clause)] = source_edges.as_slice() else {
            panic!("the source must retain its one written heritage edge");
        };

        for corruption in 0..4 {
            let (mut context, library_file, source_file) =
                default_library_heritage_context(&library, &source, corruption != 0);
            let base = interface_symbol(&library, library_file, &context, "HTMLElement");
            match corruption {
                0 => {}
                1 => {
                    assert!(context.store_mut_for_test().set_symbol_flags(
                        base,
                        SymbolFlags::INTERFACE
                            | SymbolFlags::FUNCTION_SCOPED_VARIABLE
                            | SymbolFlags::CLASS,
                        CheckFlags::NONE,
                    ));
                }
                2 => {
                    let declarations = context
                        .store()
                        .symbol(base)
                        .unwrap()
                        .declarations()
                        .unwrap()
                        .to_vec();
                    assert!(context.store_mut_for_test().set_symbol_declarations(
                        base,
                        Some(declarations),
                        None,
                    ));
                }
                3 => {
                    let declarations = context
                        .store()
                        .symbol(base)
                        .unwrap()
                        .declarations()
                        .unwrap()
                        .iter()
                        .copied()
                        .filter(|declaration| {
                            context.store().source_node_kind(*declaration)
                                == Some(SyntaxKind::InterfaceDeclaration)
                        })
                        .collect::<Vec<_>>();
                    assert!(context.store_mut_for_test().set_symbol_declarations(
                        base,
                        Some(declarations),
                        None,
                    ));
                }
                _ => unreachable!("the provenance matrix has four cases"),
            }
            let before = (
                context.store().type_len(),
                context.store().signature_len(),
                context.store().symbol_store().symbol_table_len(),
                context.store().checker_link_allocated_lengths(),
            );
            let result = heritage_plan(&source, source_file, &context, "HTMLWebViewElement");
            if corruption == 0 {
                let plan = result.unwrap();
                assert_eq!(plan.bases.len(), 1);
                let inherited = &plan.bases[0];
                assert_eq!(inherited.kind, DirectInterfaceBaseKind::Interface);
                assert_eq!(inherited.symbol, base);
                assert!(inherited.type_arguments.is_empty());
                assert!(inherited.defaults.is_empty());
                assert_eq!(
                    plan.clause,
                    NodeRef::new(source.arena.id(), source_file, *clause),
                );
                assert_eq!(
                    inherited.node,
                    NodeRef::new(source.arena.id(), source_file, *edge),
                );
                assert_eq!(
                    inherited.expression,
                    NodeRef::new(source.arena.id(), source_file, *expression),
                );
                assert_eq!(
                    context.store().source_identifier_text(inherited.expression),
                    Some("HTMLElement"),
                );
                assert!(context.store().declared_type_links(base).is_none());
                assert!(context.store().value_symbol_links(base).is_none());
            } else {
                assert!(
                    matches!(
                        result,
                        Err(DirectInterfaceHeritageError::Unsupported { .. })
                    ),
                    "corruption {corruption} accepted a forged DOM base"
                );
            }
            assert_eq!(
                (
                    context.store().type_len(),
                    context.store().signature_len(),
                    context.store().symbol_store().symbol_table_len(),
                    context.store().checker_link_allocated_lengths(),
                ),
                before,
                "corruption {corruption} published checker state"
            );
        }
    }

    #[test]
    fn qualified_namespace_bases_preserve_export_ownership_and_warm_state() {
        let cases = [
            (
                concat!(
                    "namespace Types { export interface Base { value: number } }\n",
                    "interface Derived extends Types.Base { own: number }\n",
                ),
                "Types",
            ),
            (
                concat!(
                    "namespace Outer { export namespace Inner { ",
                    "export interface Base { value: number } } }\n",
                    "interface Derived extends Outer.Inner.Base { own: number }\n",
                ),
                "Inner",
            ),
            (
                concat!(
                    "namespace Types { export interface Base<Value> { value: Value } }\n",
                    "interface Derived extends Types.Base<number> { own: number }\n",
                ),
                "Types",
            ),
        ];

        for (index, (source, expected_owner)) in cases.into_iter().enumerate() {
            let parsed = parse_source_file(source);
            assert!(
                parsed.diagnostics.is_empty(),
                "{index}: {:?}",
                parsed.diagnostics
            );
            let file = FileId::new(8_430 + u32::try_from(index).unwrap());
            let context = checker_context(&parsed, file);
            let cold = (
                context.store().type_len(),
                context.store().signature_len(),
                context.store().symbol_store().symbol_table_len(),
                context.store().checker_link_allocated_lengths(),
            );

            let first = heritage_plan(&parsed, file, &context, "Derived").unwrap();
            let [base] = first.bases.as_slice() else {
                panic!("{index}: a qualified interface has one authenticated base")
            };
            assert_eq!(base.kind, DirectInterfaceBaseKind::Interface);
            assert_eq!(base.type_arguments.len(), usize::from(index == 2));
            assert_eq!(
                parsed.arena.get(base.expression.node).unwrap().kind,
                SyntaxKind::QualifiedName
            );
            assert_eq!(
                base.symbol,
                interface_symbol(&parsed, file, &context, "Base")
            );
            assert_eq!(
                context
                    .store()
                    .get_parent_of_symbol(base.symbol)
                    .and_then(|owner| context.store().symbol(owner))
                    .and_then(|owner| owner.name().as_utf8()),
                Some(expected_owner)
            );
            assert_eq!(
                heritage_plan(&parsed, file, &context, "Derived").unwrap(),
                first
            );
            assert_eq!(
                (
                    context.store().type_len(),
                    context.store().signature_len(),
                    context.store().symbol_store().symbol_table_len(),
                    context.store().checker_link_allocated_lengths(),
                ),
                cold,
                "{index}: qualified heritage planning published checker state"
            );
        }
    }

    #[test]
    fn qualified_namespace_bases_reject_private_and_class_exports() {
        let cases = [
            concat!(
                "namespace Types { interface Hidden { value: number } }\n",
                "interface Derived extends Types.Hidden { own: number }\n",
            ),
            concat!(
                "namespace Types { export class Base {} }\n",
                "interface Derived extends Types.Base { own: number }\n",
            ),
        ];

        for (index, source) in cases.into_iter().enumerate() {
            let parsed = parse_source_file(source);
            assert!(
                parsed.diagnostics.is_empty(),
                "{index}: {:?}",
                parsed.diagnostics
            );
            let file = FileId::new(8_440 + u32::try_from(index).unwrap());
            let context = checker_context(&parsed, file);
            assert!(
                matches!(
                    heritage_plan(&parsed, file, &context, "Derived"),
                    Err(DirectInterfaceHeritageError::Unsupported { .. })
                ),
                "{index}: {source}"
            );
        }
    }

    #[test]
    fn qualified_namespace_bases_reject_forged_export_owners() {
        let parsed = parse_source_file(concat!(
            "namespace Types { export interface Base { value: number } }\n",
            "namespace Other { export interface Foreign { value: number } }\n",
            "interface Derived extends Types.Base { own: number }\n",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(8_450);
        let mut context = checker_context(&parsed, file);
        let original = interface_symbol(&parsed, file, &context, "Base");
        let foreign = interface_symbol(&parsed, file, &context, "Foreign");
        let namespace = context.store().get_parent_of_symbol(original).unwrap();
        let exports = context
            .store()
            .symbol(namespace)
            .unwrap()
            .exports()
            .unwrap();
        assert_eq!(
            context.store_mut_for_test().insert_symbol(
                exports,
                EscapedName::source("Base"),
                foreign
            ),
            Some(Some(original))
        );

        assert!(matches!(
            heritage_plan(&parsed, file, &context, "Derived"),
            Err(DirectInterfaceHeritageError::Unsupported { .. })
        ));
    }

    #[test]
    fn transitive_interface_bases_are_planned_without_publication() {
        let parsed = parse_source_file(concat!(
            "interface Root { first: number }\n",
            "interface Middle extends Root { second: string }\n",
            "interface Leaf extends Middle { third: boolean }\n",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(8_451);
        let context = checker_context(&parsed, file);
        let cold = (
            context.store().type_len(),
            context.store().signature_len(),
            context.store().symbol_store().symbol_table_len(),
            context.store().checker_link_allocated_lengths(),
        );

        let plan = heritage_plan(&parsed, file, &context, "Leaf").unwrap();
        let [base] = plan.bases.as_slice() else {
            panic!("a transitive chain retains only its direct base")
        };
        assert_eq!(
            base.symbol,
            interface_symbol(&parsed, file, &context, "Middle")
        );
        assert_eq!(base.kind, DirectInterfaceBaseKind::Interface);
        assert_eq!(
            (
                context.store().type_len(),
                context.store().signature_len(),
                context.store().symbol_store().symbol_table_len(),
                context.store().checker_link_allocated_lengths(),
            ),
            cold
        );
    }

    #[test]
    fn forward_interface_bases_preserve_named_method_symbols_without_publication() {
        let parsed = parse_source_file(concat!(
            "interface Derived extends Base { method(...args: any[]): void; }\n",
            "interface Base { method(...args: any[]): void; }\n",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(8_453);
        let context = checker_context(&parsed, file);
        let base = interface_symbol(&parsed, file, &context, "Base");
        let cold = (
            context.store().type_len(),
            context.store().signature_len(),
            context.store().symbol_store().symbol_table_len(),
            context.store().checker_link_allocated_lengths(),
        );

        let planned = heritage_plan(&parsed, file, &context, "Derived").unwrap();
        let [inherited] = planned.bases.as_slice() else {
            panic!("a forward-declared interface must retain its one direct base")
        };
        let method = context
            .store()
            .symbol(base)
            .and_then(ts_binder::semantic::Symbol::members)
            .and_then(|members| context.store().symbol_table(members))
            .and_then(|members| members.get_source("method"))
            .unwrap();
        assert_eq!(inherited.symbol, base);
        assert_eq!(inherited.kind, DirectInterfaceBaseKind::Interface);
        assert!(inherited.type_arguments.is_empty());
        assert_eq!(
            context.store().symbol(method).unwrap().flags(),
            SymbolFlags::METHOD
        );
        assert_eq!(context.store().get_parent_of_symbol(method), Some(base));
        assert_eq!(
            heritage_plan(&parsed, file, &context, "Derived").unwrap(),
            planned,
        );
        assert_eq!(
            (
                context.store().type_len(),
                context.store().signature_len(),
                context.store().symbol_store().symbol_table_len(),
                context.store().checker_link_allocated_lengths(),
            ),
            cold,
        );
    }

    #[test]
    fn forwarded_generic_interface_bases_preserve_ordered_type_arguments() {
        for (index, (source, expected_arguments)) in [
            (
                concat!(
                    "interface Derived<Value> extends Base<Value> { own: Value }\n",
                    "interface Base<Item> { inherited: Item }\n",
                ),
                &["Value"][..],
            ),
            (
                concat!(
                    "interface Derived<First, Second> extends Base<First, Second> {}\n",
                    "interface Base<Left, Right> { left: Left; right: Right }\n",
                ),
                &["First", "Second"][..],
            ),
            (
                concat!(
                    "interface Derived<Value extends string, Extra> extends Base<Value> {}\n",
                    "interface Base<Item> { inherited: Item }\n",
                ),
                &["Value"][..],
            ),
            (
                concat!(
                    "interface Derived<Value> extends Base<Value> { own: Value }\n",
                    "interface Base<Item> { first: Item }\n",
                    "interface Base<Item> { second: Item }\n",
                ),
                &["Value"][..],
            ),
        ]
        .into_iter()
        .enumerate()
        {
            let parsed = parse_source_file(source);
            assert!(
                parsed.diagnostics.is_empty(),
                "{index}: {:?}",
                parsed.diagnostics
            );
            let file = FileId::new(8_454 + u32::try_from(index).unwrap());
            let context = checker_context(&parsed, file);
            let base = interface_symbol(&parsed, file, &context, "Base");
            let cold = (
                context.store().type_len(),
                context.store().signature_len(),
                context.store().symbol_store().symbol_table_len(),
                context.store().checker_link_allocated_lengths(),
            );

            let planned = heritage_plan(&parsed, file, &context, "Derived").unwrap();
            let [inherited] = planned.bases.as_slice() else {
                panic!("{index}: a generic interface must retain one direct base")
            };
            assert_eq!(inherited.symbol, base);
            assert_eq!(inherited.kind, DirectInterfaceBaseKind::Interface);
            assert_eq!(
                inherited
                    .type_arguments
                    .iter()
                    .map(|argument| {
                        let NodeData::TypeReferenceNode(reference) =
                            &parsed.arena.get(argument.node).unwrap().data
                        else {
                            panic!("{index}: a generic argument must retain its type reference")
                        };
                        let NodeData::Identifier(name) =
                            &parsed.arena.get(reference.type_name).unwrap().data
                        else {
                            panic!("{index}: a forwarded argument must retain its parameter name")
                        };
                        name.text.as_str()
                    })
                    .collect::<Vec<_>>(),
                expected_arguments,
            );
            assert_eq!(
                heritage_plan(&parsed, file, &context, "Derived").unwrap(),
                planned,
            );
            assert_eq!(
                (
                    context.store().type_len(),
                    context.store().signature_len(),
                    context.store().symbol_store().symbol_table_len(),
                    context.store().checker_link_allocated_lengths(),
                ),
                cold,
                "{index}: generic heritage planning published checker state",
            );
        }
    }

    #[test]
    fn generic_heritage_accepts_concrete_reordered_and_repeated_arguments() {
        for (index, source) in [
            "interface Base<A> {} interface Derived<T> extends Base<string> {}",
            "interface Base<A, B> {} interface Derived<T, U> extends Base<U, T> {}",
            "interface Base<A, B> {} interface Derived<T> extends Base<T, T> {}",
            "interface Base<A, B> {} interface Derived<T> extends Base<string, T> {}",
            "interface Base<A, B, C> {} interface Derived<T, U> extends Base<T, string, U> {}",
            concat!(
                "interface Base<A, B, C, D, E> {} ",
                "interface Derived<T> extends Base<T, string, number, boolean, never> {}",
            ),
            concat!(
                "type Completion = undefined; ",
                "interface Base<A, B = any, C = unknown> {} ",
                "interface Derived<T = string> extends Base<T, Completion, unknown> {}",
            ),
        ]
        .into_iter()
        .enumerate()
        {
            let parsed = parse_source_file(source);
            assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
            let file = FileId::new(8_520 + u32::try_from(index).unwrap());
            let context = checker_context(&parsed, file);
            let before = (
                context.store().type_len(),
                context.store().mapper_len(),
                context.store().checker_link_allocated_lengths(),
            );
            let plan = heritage_plan(&parsed, file, &context, "Derived")
                .unwrap_or_else(|error| panic!("{source}: {error:?}"));
            let [base] = plan.bases.as_slice() else {
                panic!("one base was expected")
            };
            let NodeData::ExpressionWithTypeArguments(expression) =
                &parsed.arena.get(base.node.node).unwrap().data
            else {
                panic!("the base must retain its source syntax")
            };
            assert_eq!(
                base.type_arguments,
                expression
                    .type_arguments
                    .as_ref()
                    .unwrap()
                    .nodes
                    .iter()
                    .map(|argument| NodeRef::new(parsed.arena.id(), file, *argument))
                    .collect::<Vec<_>>()
            );
            assert_eq!(heritage_plan(&parsed, file, &context, "Derived"), Ok(plan));
            assert_eq!(
                (
                    context.store().type_len(),
                    context.store().mapper_len(),
                    context.store().checker_link_allocated_lengths(),
                ),
                before,
            );
        }
    }

    #[test]
    fn generic_heritage_fills_defaults_in_parameter_order() {
        for (index, (source, expected)) in [
            (
                concat!(
                    "interface Base<A, B = any, C = unknown> {} ",
                    "interface Derived<T> extends Base<T> {}",
                ),
                vec![
                    SyntaxKind::TypeReference,
                    SyntaxKind::AnyKeyword,
                    SyntaxKind::UnknownKeyword,
                ],
            ),
            (
                concat!(
                    "interface Base<A, B = A, C = B> {} ",
                    "interface Derived<T> extends Base<T> {}",
                ),
                vec![SyntaxKind::TypeReference; 3],
            ),
            (
                concat!(
                    "interface Base<A = number, B = A> {} ",
                    "interface Derived<T> extends Base {}",
                ),
                vec![SyntaxKind::NumberKeyword; 2],
            ),
            (
                concat!(
                    "interface Base<A = string> {} ",
                    "interface Derived extends Base {}",
                ),
                vec![SyntaxKind::StringKeyword],
            ),
            (
                concat!(
                    "type Completion = undefined; interface Base<A, B = Completion> {} ",
                    "interface Derived<T> extends Base<T> {}",
                ),
                vec![SyntaxKind::TypeReference; 2],
            ),
            (
                concat!(
                    "interface Base<A, B = unknown> {} interface Base<A, B> {} ",
                    "interface Derived<T> extends Base<T> {}",
                ),
                vec![SyntaxKind::TypeReference, SyntaxKind::UnknownKeyword],
            ),
        ]
        .into_iter()
        .enumerate()
        {
            let parsed = parse_source_file(source);
            assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
            let file = FileId::new(8_530 + u32::try_from(index).unwrap());
            let context = checker_context(&parsed, file);
            let before = (
                context.store().type_len(),
                context.store().mapper_len(),
                context.store().checker_link_allocated_lengths(),
            );
            let plan = heritage_plan(&parsed, file, &context, "Derived")
                .unwrap_or_else(|error| panic!("{source}: {error:?}"));
            let arguments = &plan.bases[0].type_arguments;
            assert_eq!(
                arguments
                    .iter()
                    .map(|argument| parsed.arena.get(argument.node).unwrap().kind)
                    .collect::<Vec<_>>(),
                expected,
            );
            if index == 1 || index == 2 {
                assert!(arguments.iter().all(|argument| *argument == arguments[0]));
            }
            assert_eq!(heritage_plan(&parsed, file, &context, "Derived"), Ok(plan));
            assert_eq!(
                (
                    context.store().type_len(),
                    context.store().mapper_len(),
                    context.store().checker_link_allocated_lengths(),
                ),
                before,
            );
        }
    }

    #[test]
    fn generic_heritage_rejects_unresolved_defaults_before_publication() {
        for (index, source) in [
            "interface Base<A, B> {} interface Derived<T> extends Base<T> {}",
            "interface Base<A, B = B> {} interface Derived<T> extends Base<T> {}",
            "interface Base<A, B = B> {} interface Derived<T> extends Base<T, string> {}",
            "interface Base<A, B = C, C = number> {} interface Derived<T> extends Base<T> {}",
            "interface Base<A, B = Missing> {} interface Derived<T> extends Base<T> {}",
            "interface Base<A, B = A[]> {} interface Derived<T> extends Base<T> {}",
            concat!(
                "interface Box<A> {} interface Base<A, B = Box<A>> {} ",
                "interface Derived<T> extends Base<T> {}",
            ),
            concat!(
                "interface Base<A, B = string> {} interface Base<A, B = number> {} ",
                "interface Derived<T> extends Base<T> {}",
            ),
        ]
        .into_iter()
        .enumerate()
        {
            let parsed = parse_source_file(source);
            assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
            let file = FileId::new(8_540 + u32::try_from(index).unwrap());
            let context = checker_context(&parsed, file);
            let before = (
                context.store().type_len(),
                context.store().mapper_len(),
                context.store().checker_link_allocated_lengths(),
            );
            assert!(
                matches!(
                    heritage_plan(&parsed, file, &context, "Derived"),
                    Err(DirectInterfaceHeritageError::Unsupported { .. })
                ),
                "{source}",
            );
            assert_eq!(
                (
                    context.store().type_len(),
                    context.store().mapper_len(),
                    context.store().checker_link_allocated_lengths(),
                ),
                before,
            );
        }
    }

    #[test]
    fn defaulted_iterator_heritage_keeps_default_library_members_lazy() {
        let library = parse_source_file(include_str!(
            "../../../ts_bundled/libs/lib.es2015.iterable.d.ts"
        ));
        let source = parse_source_file("");
        assert!(library.diagnostics.is_empty(), "{:?}", library.diagnostics);
        let (mut context, library_file, _) =
            default_library_heritage_context(&library, &source, true);
        let array = interface_symbol(&library, library_file, &context, "ArrayIterator");
        let iterator_object = interface_symbol(&library, library_file, &context, "IteratorObject");
        let iterator = interface_symbol(&library, library_file, &context, "Iterator");
        let target = context.get_declared_type_of_symbol(array).unwrap();
        let object_target = context
            .get_declared_type_of_symbol(iterator_object)
            .unwrap();
        let iterator_target = context.get_declared_type_of_symbol(iterator).unwrap();
        let own_arguments = validate_direct_generic_reference(context.store(), target)
            .unwrap()
            .type_arguments;
        let object_arguments = validate_direct_generic_reference(context.store(), object_target)
            .unwrap()
            .type_arguments;
        let TypeData::Interface(array_data) = context.store().type_payload(target).unwrap().data()
        else {
            panic!("the array iterator must retain its interface type")
        };
        let [base] = array_data.resolved_base_types.as_deref().unwrap() else {
            panic!("the array iterator must retain one base")
        };
        let base = *base;
        let reference = validate_direct_generic_reference(context.store(), base).unwrap();
        let bootstrap = context.store().intrinsic_bootstrap().unwrap();
        assert_eq!(reference.target, object_target);
        assert_eq!(
            reference.type_arguments,
            [own_arguments[0], bootstrap.any_type, bootstrap.unknown_type],
        );
        let TypeData::Interface(object_data) =
            context.store().type_payload(object_target).unwrap().data()
        else {
            panic!("the iterator object must retain its interface type")
        };
        let [inherited] = object_data.resolved_base_types.as_deref().unwrap() else {
            panic!("the iterator object must retain one base")
        };
        let inherited = validate_direct_generic_reference(context.store(), *inherited).unwrap();
        assert_eq!(inherited.target, iterator_target);
        assert_eq!(inherited.type_arguments, object_arguments);
        for type_ in [target, object_target, iterator_target] {
            let TypeData::Interface(data) = context.store().type_payload(type_).unwrap().data()
            else {
                panic!("the heritage graph must contain interface types")
            };
            assert!(!data.declared_members_resolved);
            assert!(data.reference.object.structured.properties.is_none());
            assert!(data.reference.object.structured.signatures.is_none());
        }
        let snapshot = |context: &CanonicalCheckerContext<'_>| {
            (
                context.store().type_len(),
                context.store().mapper_len(),
                context.store().signature_len(),
                context.store().checker_link_allocated_lengths(),
            )
        };
        let warm = snapshot(&context);
        assert_eq!(context.get_declared_type_of_symbol(array), Ok(target));
        assert_eq!(snapshot(&context), warm);
        assert!(context.store_mut_for_test().set_interface_base_resolution(
            target,
            true,
            None,
            Some(vec![object_target]),
        ));
        assert!(context.get_declared_type_of_symbol(array).is_err());
        assert_eq!(snapshot(&context), warm);
        assert!(context.store_mut_for_test().set_interface_base_resolution(
            target,
            true,
            None,
            Some(vec![base]),
        ));
        assert_eq!(context.get_declared_type_of_symbol(array), Ok(target));
        assert!(context.diagnostics().is_empty());
    }

    #[test]
    fn merged_nongeneric_class_heritage_keeps_base_argument_checks() {
        for (base, extension, expected_arguments) in [
            ("Base", "Base", Some(0)),
            ("Base<T>", "Base", None),
            ("Base<T = number>", "Base", Some(1)),
            ("Base<T = number>", "Base<number>", None),
        ] {
            let parsed = parse_source_file(&format!(
                "interface {base} {{}} \
                 class C extends null {{ constructor() {{ super(); }} }} \
                 interface C extends {extension} {{}}"
            ));
            assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
            let file = FileId::new(8_602);
            let context = checker_context(&parsed, file);
            let before = (
                context.store().type_len(),
                context.store().signature_len(),
                context.store().checker_link_allocated_lengths(),
            );
            let result = heritage_plan(&parsed, file, &context, "C");
            if let Some(expected) = expected_arguments {
                let plan = result.unwrap();
                assert_eq!(plan.bases.len(), 1);
                assert_eq!(plan.bases[0].type_arguments.len(), expected);
                assert_eq!(plan.bases[0].defaults.len(), expected);
            } else {
                assert!(
                    matches!(
                        result,
                        Err(DirectInterfaceHeritageError::Unsupported { .. })
                    ),
                    "{base} / {extension}: {result:?}",
                );
            }
            assert_eq!(
                (
                    context.store().type_len(),
                    context.store().signature_len(),
                    context.store().checker_link_allocated_lengths(),
                ),
                before,
            );
        }
    }

    #[test]
    fn default_library_interface_value_owners_keep_no_argument_heritage() {
        let library = parse_source_file(concat!(
            "interface ElementBase {} ",
            "interface HTMLAnchorElement extends ElementBase {} ",
            "declare var HTMLAnchorElement: unknown;",
        ));
        let source = parse_source_file("");
        let source_edges = library
            .arena
            .iter()
            .filter_map(|(node, record)| {
                let NodeData::ExpressionWithTypeArguments(base) = &record.data else {
                    return None;
                };
                Some((node, base.expression, record.parent?))
            })
            .collect::<Vec<_>>();
        let [(edge, expression, clause)] = source_edges.as_slice() else {
            panic!("the owner must retain its one written heritage edge");
        };
        for default_library in [false, true] {
            let (context, file, _) =
                default_library_heritage_context(&library, &source, default_library);
            let owner = interface_symbol(&library, file, &context, "HTMLAnchorElement");
            let base = interface_symbol(&library, file, &context, "ElementBase");
            let before = (
                context.store().type_len(),
                context.store().signature_len(),
                context.store().checker_link_allocated_lengths(),
            );
            let plan = heritage_plan(&library, file, &context, "HTMLAnchorElement").unwrap();
            assert_eq!(plan.bases.len(), 1);
            assert!(plan.bases[0].type_arguments.is_empty());
            let inherited = &plan.bases[0];
            assert_eq!(inherited.kind, DirectInterfaceBaseKind::Interface);
            assert_eq!(inherited.symbol, base);
            assert!(inherited.defaults.is_empty());
            assert_eq!(plan.clause, NodeRef::new(library.arena.id(), file, *clause),);
            assert_eq!(
                inherited.node,
                NodeRef::new(library.arena.id(), file, *edge),
            );
            assert_eq!(
                inherited.expression,
                NodeRef::new(library.arena.id(), file, *expression),
            );
            assert_eq!(
                context.store().source_identifier_text(inherited.expression),
                Some("ElementBase"),
            );
            assert!(context.store().declared_type_links(owner).is_none());
            assert!(context.store().value_symbol_links(owner).is_none());
            assert_eq!(
                (
                    context.store().type_len(),
                    context.store().signature_len(),
                    context.store().checker_link_allocated_lengths(),
                ),
                before,
            );
        }
    }

    #[test]
    fn heritage_primitive_defaults_validate_uncached_annotations() {
        for keyword in ["any", "unknown", "string"] {
            let parsed = parse_source_file(&format!(
                "interface Base<Value = {keyword}> {{ value: Value }} \
                 interface Derived extends Base {{}}"
            ));
            assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
            let file = FileId::new(8_603);
            let mut context = checker_context(&parsed, file);
            let owner = interface_symbol(&parsed, file, &context, "Derived");
            let target = context.get_declared_type_of_symbol(owner).unwrap();
            let plan = heritage_plan(&parsed, file, &context, "Derived").unwrap();
            let default = &plan.bases[0].defaults[0];
            let bootstrap = context.store().intrinsic_bootstrap().unwrap();
            let wrong = bootstrap.number_type;
            let expected = match keyword {
                "any" => bootstrap.any_type,
                "unknown" => bootstrap.unknown_type,
                "string" => bootstrap.string_type,
                _ => unreachable!(),
            };
            let parameter = context
                .get_declared_type_of_symbol(default.parameter)
                .unwrap();
            let TypeData::TypeParameter(data) =
                context.store().type_payload(parameter).unwrap().data()
            else {
                panic!("the default must retain its declared parameter")
            };
            assert_eq!(data.resolved_default_type, Some(expected));
            assert!(
                context
                    .store()
                    .source_direct_type_annotation_is_exact(default.node, expected)
            );
            assert!(context.store().type_node_links(default.node).is_none());
            let original = context
                .store()
                .type_node_links(default.node)
                .cloned()
                .unwrap_or_default();
            assert!(context.store_mut_for_test().set_type_node_links(
                default.node,
                super::super::TypeNodeLinks {
                    resolved_type: Some(wrong),
                    ..super::super::TypeNodeLinks::default()
                },
            ));
            let before = (
                context.store().type_len(),
                context.store().mapper_len(),
                context.store().checker_link_allocated_lengths(),
            );
            assert!(context.get_declared_type_of_symbol(owner).is_err());
            assert_eq!(
                (
                    context.store().type_len(),
                    context.store().mapper_len(),
                    context.store().checker_link_allocated_lengths(),
                ),
                before,
            );
            assert!(
                context
                    .store_mut_for_test()
                    .set_type_node_links(default.node, original)
            );
            assert_eq!(context.get_declared_type_of_symbol(owner), Ok(target));
        }
    }

    #[test]
    fn generic_heritage_defaults_retain_original_parameter_and_node_caches() {
        let parsed = parse_source_file(concat!(
            "interface Base<A, B = A> { value: B; } ",
            "interface Derived<T> extends Base<T> {} ",
            "declare const item: Derived<string>; const value = item.value;",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(8_551);
        let mut context = checker_context(&parsed, file);
        let derived = interface_symbol(&parsed, file, &context, "Derived");
        context.check_source_file(file).unwrap();
        let target = context.get_declared_type_of_symbol(derived).unwrap();
        let plan = heritage_plan(&parsed, file, &context, "Derived").unwrap();
        let default = &plan.bases[0].defaults[0];
        assert_ne!(default.node, default.argument);
        assert_eq!(default.index, 1);
        let parameter = context
            .get_declared_type_of_symbol(default.parameter)
            .unwrap();
        let expected = context
            .get_declared_type_of_symbol(default.earlier_parameter.unwrap())
            .unwrap();
        let TypeData::TypeParameter(data) = context.store().type_payload(parameter).unwrap().data()
        else {
            panic!("the default must retain its original parameter")
        };
        assert_eq!(data.resolved_default_type, Some(expected));
        assert_eq!(
            context
                .store()
                .type_node_links(default.node)
                .and_then(|links| links.resolved_type),
            Some(expected)
        );
        let resolution = (data.constraint, data.target, data.mapper);
        let original_links = context
            .store()
            .type_node_links(default.node)
            .unwrap()
            .clone();
        let wrong = context.store().intrinsic_bootstrap().unwrap().number_type;
        let warm = (
            context.store().type_len(),
            context.store().mapper_len(),
            context.store().checker_link_allocated_lengths(),
        );
        for poison_node in [false, true] {
            if poison_node {
                assert!(context.store_mut_for_test().set_type_node_links(
                    default.node,
                    super::super::TypeNodeLinks {
                        resolved_type: Some(wrong),
                        ..super::super::TypeNodeLinks::default()
                    }
                ));
            } else {
                assert!(context.store_mut_for_test().set_type_parameter_resolution(
                    parameter,
                    resolution.0,
                    resolution.1,
                    resolution.2,
                    Some(wrong)
                ));
            }
            assert!(context.get_declared_type_of_symbol(derived).is_err());
            assert_eq!(
                (
                    context.store().type_len(),
                    context.store().mapper_len(),
                    context.store().checker_link_allocated_lengths()
                ),
                warm
            );
            assert!(context.store_mut_for_test().set_type_parameter_resolution(
                parameter,
                resolution.0,
                resolution.1,
                resolution.2,
                Some(expected)
            ));
            assert!(
                context
                    .store_mut_for_test()
                    .set_type_node_links(default.node, original_links.clone())
            );
            assert_eq!(context.get_declared_type_of_symbol(derived), Ok(target));
        }
        assert!(context.diagnostics().is_empty());
    }

    #[test]
    fn generic_heritage_reordered_arguments_preserve_inherited_member_types() {
        let parsed = parse_source_file(concat!(
            "interface Base<A, B> { first: A; second: B; } ",
            "interface Derived<T, U> extends Base<U, T> {} ",
            "declare const item: Derived<string, number>; ",
            "const first: number = item.first; const second: string = item.second;",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(8_552);
        let mut context = checker_context(&parsed, file);
        context.check_source_file(file).unwrap();
        assert!(context.diagnostics().is_empty());
        let warm = (
            context.store().type_len(),
            context.store().mapper_len(),
            context.store().checker_link_allocated_lengths(),
        );
        context.recheck_source_file(file).unwrap();
        assert_eq!(
            (
                context.store().type_len(),
                context.store().mapper_len(),
                context.store().checker_link_allocated_lengths()
            ),
            warm
        );
        assert!(context.diagnostics().is_empty());
    }

    #[test]
    fn concrete_iterator_heritage_retains_inherited_next_mapper() {
        let parsed = parse_source_file(concat!(
            "interface Iterator<T, TReturn = any, TNext = any> { next(value: TNext): T; } ",
            "interface Derived extends Iterator<number, void, string> {}",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(8_550);
        let mut context = checker_context(&parsed, file);
        let iterator = interface_symbol(&parsed, file, &context, "Iterator");
        let derived = interface_symbol(&parsed, file, &context, "Derived");
        assert_concrete_iterator_next(&mut context, iterator, derived);
    }

    #[test]
    fn bundled_iterator_heritage_retains_inherited_next_mapper() {
        let library = parse_source_file(include_str!(
            "../../../ts_bundled/libs/lib.es2015.iterable.d.ts"
        ));
        let source =
            parse_source_file("interface Derived extends Iterator<number, void, string> {}");
        assert!(library.diagnostics.is_empty(), "{:?}", library.diagnostics);
        assert!(source.diagnostics.is_empty(), "{:?}", source.diagnostics);
        let (mut context, library_file, source_file) =
            default_library_heritage_context(&library, &source, true);
        let iterator = interface_symbol(&library, library_file, &context, "Iterator");
        let derived = interface_symbol(&source, source_file, &context, "Derived");
        assert_concrete_iterator_next(&mut context, iterator, derived);
    }

    fn assert_concrete_iterator_next(
        context: &mut CanonicalCheckerContext<'_>,
        iterator: SemanticSymbolId,
        derived: SemanticSymbolId,
    ) {
        let original_next = context
            .store()
            .symbol(iterator)
            .and_then(ts_binder::semantic::Symbol::members)
            .and_then(|members| context.store().symbol_table(members))
            .and_then(|members| members.get_source("next"))
            .unwrap();
        let target = context.get_declared_type_of_symbol(derived).unwrap();
        let TypeData::Interface(data) = context.store().type_payload(target).unwrap().data() else {
            panic!("Derived must retain its interface type")
        };
        let [base] = data.resolved_base_types.as_deref().unwrap() else {
            panic!("Derived must retain one iterator base")
        };
        let base = *base;
        let reference = validate_direct_generic_reference(context.store(), base).unwrap();
        let parameters = validate_direct_generic_reference(context.store(), reference.target)
            .unwrap()
            .type_arguments;
        let bootstrap = context.store().intrinsic_bootstrap().unwrap();
        let string = bootstrap.string_type;
        assert_eq!(
            reference.type_arguments,
            [bootstrap.number_type, bootstrap.void_type, string],
        );
        let inherited_next = data
            .reference
            .object
            .structured
            .members
            .and_then(|members| context.store().symbol_table(members))
            .and_then(|members| members.get_source("next"))
            .unwrap();
        assert!(
            context
                .store()
                .value_symbol_links(inherited_next)
                .unwrap()
                .resolved_type
                .is_none()
        );
        let next = context
            .store_mut_for_test()
            .resolve_generic_interface_property(base, "next", None)
            .unwrap()
            .unwrap();
        assert_eq!(next.symbol(), inherited_next);
        let links = context.store().value_symbol_links(next.symbol()).unwrap();
        assert_eq!(links.target, Some(original_next));
        assert_eq!(
            context
                .store()
                .map_type(links.mapper.unwrap(), parameters[2]),
            Some(string),
        );
        let TypeData::Interface(data) = context.store().type_payload(target).unwrap().data() else {
            panic!("Derived must retain its interface type")
        };
        assert!(
            data.reference
                .object
                .structured
                .properties
                .as_ref()
                .unwrap()
                .contains(&next.symbol())
        );
        let warm = (
            context.store().type_len(),
            context.store().mapper_len(),
            context.store().checker_link_allocated_lengths(),
        );
        assert_eq!(context.get_declared_type_of_symbol(derived), Ok(target));
        assert_eq!(
            context
                .store_mut_for_test()
                .resolve_generic_interface_property(base, "next", None),
            Ok(Some(next)),
        );
        assert_eq!(
            (
                context.store().type_len(),
                context.store().mapper_len(),
                context.store().checker_link_allocated_lengths(),
            ),
            warm,
        );
        assert!(context.diagnostics().is_empty());
    }

    #[test]
    fn reopened_generic_interface_bases_keep_multiple_heritage_bases_and_recursion_lazy() {
        let parsed = parse_source_file(concat!(
            "interface Array<Value> { length: number }\n",
            "type ReactNode = string | ReactNodeArray;\n",
            "interface ReactNodeArray extends Array<ReactNode> {}\n",
            "declare namespace React {\n",
            "  interface AriaAttributes { label?: string }\n",
            "  interface DOMAttributes<T> { children?: ReactNode; target?: T }\n",
            "  interface HTMLAttributes<T> ",
            "extends AriaAttributes, DOMAttributes<T> { id?: string }\n",
            "  interface HTMLAttributes<T> { title?: string }\n",
            "  interface InputHTMLAttributes<T> extends HTMLAttributes<T> { value?: string }\n",
            "}\n",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(8_480);
        let context = checker_context(&parsed, file);
        let html_attributes = interface_symbol(&parsed, file, &context, "HTMLAttributes");
        let aria_attributes = interface_symbol(&parsed, file, &context, "AriaAttributes");
        let dom_attributes = interface_symbol(&parsed, file, &context, "DOMAttributes");
        let array = interface_symbol(&parsed, file, &context, "Array");
        let initial_array_links = context.store().declared_type_links(array).cloned();
        let cold = (
            context.store().type_len(),
            context.store().signature_len(),
            context.store().symbol_store().symbol_table_len(),
            context.store().checker_link_allocated_lengths(),
        );

        let input = heritage_plan(&parsed, file, &context, "InputHTMLAttributes").unwrap();
        let [input_base] = input.bases.as_slice() else {
            panic!("a reopened generic interface must retain its canonical direct base")
        };
        assert_eq!(input_base.symbol, html_attributes);
        assert_eq!(input_base.kind, DirectInterfaceBaseKind::Interface);
        assert_eq!(input_base.type_arguments.len(), 1);

        let html = heritage_plan(&parsed, file, &context, "HTMLAttributes").unwrap();
        assert_eq!(
            html.bases
                .iter()
                .map(|base| (base.symbol, base.kind, base.type_arguments.len()))
                .collect::<Vec<_>>(),
            [
                (aria_attributes, DirectInterfaceBaseKind::Interface, 0),
                (dom_attributes, DirectInterfaceBaseKind::Interface, 1),
            ],
        );

        let recursive = heritage_plan(&parsed, file, &context, "ReactNodeArray").unwrap();
        let [recursive_base] = recursive.bases.as_slice() else {
            panic!("a recursive ReactNode argument must retain its direct array base")
        };
        assert_eq!(recursive_base.symbol, array);
        assert_eq!(recursive_base.kind, DirectInterfaceBaseKind::Interface);
        assert_eq!(recursive_base.type_arguments.len(), 1);

        assert_eq!(
            heritage_plan(&parsed, file, &context, "InputHTMLAttributes").unwrap(),
            input,
        );
        assert_eq!(
            heritage_plan(&parsed, file, &context, "HTMLAttributes").unwrap(),
            html,
        );
        assert_eq!(
            heritage_plan(&parsed, file, &context, "ReactNodeArray").unwrap(),
            recursive,
        );
        assert_eq!(
            (
                context.store().type_len(),
                context.store().signature_len(),
                context.store().symbol_store().symbol_table_len(),
                context.store().checker_link_allocated_lengths(),
            ),
            cold,
        );
        assert!(
            context
                .store()
                .declared_type_links(html_attributes)
                .is_none()
        );
        assert_eq!(
            context.store().declared_type_links(array),
            initial_array_links.as_ref(),
        );
    }

    #[test]
    fn reopened_generic_interface_heritage_cycles_remain_unsupported_without_publication() {
        let parsed = parse_source_file(concat!(
            "interface Left<T> extends Right<T> {}\n",
            "interface Left<T> { value?: T }\n",
            "interface Right<T> extends Left<T> {}\n",
            "interface Derived<T> extends Left<T> {}\n",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(8_481);
        let context = checker_context(&parsed, file);
        let cold = (
            context.store().type_len(),
            context.store().signature_len(),
            context.store().symbol_store().symbol_table_len(),
            context.store().checker_link_allocated_lengths(),
        );

        assert!(matches!(
            heritage_plan(&parsed, file, &context, "Derived"),
            Err(DirectInterfaceHeritageError::Unsupported { .. })
        ));
        assert_eq!(
            (
                context.store().type_len(),
                context.store().signature_len(),
                context.store().symbol_store().symbol_table_len(),
                context.store().checker_link_allocated_lengths(),
            ),
            cold,
        );
    }

    #[test]
    fn generic_interface_bases_preserve_mixed_primitive_arguments() {
        for (index, (source, expected)) in [
            (
                concat!(
                    "interface Derived<Value> extends Base<Value, string> {}\n",
                    "interface Base<First, Second> {}\n",
                ),
                vec![SyntaxKind::TypeReference, SyntaxKind::StringKeyword],
            ),
            (
                concat!(
                    "interface Derived<First, Second> ",
                    "extends Base<First, Second, string, number, never> {}\n",
                    "interface Base<A, B, C, D, E> {}\n",
                ),
                vec![
                    SyntaxKind::TypeReference,
                    SyntaxKind::TypeReference,
                    SyntaxKind::StringKeyword,
                    SyntaxKind::NumberKeyword,
                    SyntaxKind::NeverKeyword,
                ],
            ),
        ]
        .into_iter()
        .enumerate()
        {
            let parsed = parse_source_file(source);
            assert!(
                parsed.diagnostics.is_empty(),
                "{index}: {:?}",
                parsed.diagnostics,
            );
            let file = FileId::new(8_482 + u32::try_from(index).unwrap());
            let context = checker_context(&parsed, file);
            let cold = (
                context.store().type_len(),
                context.store().signature_len(),
                context.store().symbol_store().symbol_table_len(),
                context.store().checker_link_allocated_lengths(),
            );

            let planned = heritage_plan(&parsed, file, &context, "Derived").unwrap();
            let [base] = planned.bases.as_slice() else {
                panic!("{index}: transformed heritage must retain one authenticated base")
            };
            assert_eq!(base.kind, DirectInterfaceBaseKind::Interface);
            assert_eq!(
                base.type_arguments
                    .iter()
                    .map(|argument| parsed.arena.get(argument.node).unwrap().kind)
                    .collect::<Vec<_>>(),
                expected,
            );
            assert_eq!(
                heritage_plan(&parsed, file, &context, "Derived").unwrap(),
                planned,
            );
            assert_eq!(
                (
                    context.store().type_len(),
                    context.store().signature_len(),
                    context.store().symbol_store().symbol_table_len(),
                    context.store().checker_link_allocated_lengths(),
                ),
                cold,
                "{index}: transformed heritage planning published checker state",
            );
        }
    }

    #[test]
    fn forwarded_generic_interface_bases_reject_unverified_substitutions() {
        for (index, source) in [
            concat!(
                "interface Derived<Value> extends Base<Value[]> {}\n",
                "interface Base<Item> { inherited: Item }\n",
            ),
            concat!(
                "interface Derived<Value> extends Base<Value> {}\n",
                "interface Base<Item extends string> { inherited: Item }\n",
            ),
        ]
        .into_iter()
        .enumerate()
        {
            let parsed = parse_source_file(source);
            assert!(
                parsed.diagnostics.is_empty(),
                "{index}: {:?}",
                parsed.diagnostics
            );
            let file = FileId::new(8_456 + u32::try_from(index).unwrap());
            let context = checker_context(&parsed, file);
            let cold = (
                context.store().type_len(),
                context.store().signature_len(),
                context.store().symbol_store().symbol_table_len(),
                context.store().checker_link_allocated_lengths(),
            );

            assert!(
                matches!(
                    heritage_plan(&parsed, file, &context, "Derived"),
                    Err(DirectInterfaceHeritageError::Unsupported { .. })
                ),
                "{index}: {source}",
            );
            assert_eq!(
                (
                    context.store().type_len(),
                    context.store().signature_len(),
                    context.store().symbol_store().symbol_table_len(),
                    context.store().checker_link_allocated_lengths(),
                ),
                cold,
                "{index}: rejected generic heritage published checker state",
            );
        }
    }

    #[test]
    fn merged_transient_interface_bases_retain_their_canonical_identity() {
        let parsed = parse_source_file(concat!(
            "interface Derived extends Base { own: string }\n",
            "interface Base { first: number }\n",
            "interface Base { second: boolean }\n",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(8_462);
        let mut context = checker_context(&parsed, file);
        let base = interface_symbol(&parsed, file, &context, "Base");
        assert!(context.store_mut_for_test().set_symbol_flags(
            base,
            SymbolFlags::INTERFACE | SymbolFlags::TRANSIENT,
            CheckFlags::NONE,
        ));
        let cold = (
            context.store().type_len(),
            context.store().signature_len(),
            context.store().symbol_store().symbol_table_len(),
            context.store().checker_link_allocated_lengths(),
        );

        let planned = heritage_plan(&parsed, file, &context, "Derived").unwrap();
        let [inherited] = planned.bases.as_slice() else {
            panic!("a merged transient interface must retain one direct base")
        };
        assert_eq!(inherited.symbol, base);
        assert_eq!(inherited.kind, DirectInterfaceBaseKind::Interface);
        assert!(inherited.type_arguments.is_empty());
        assert_eq!(
            (
                context.store().type_len(),
                context.store().signature_len(),
                context.store().symbol_store().symbol_table_len(),
                context.store().checker_link_allocated_lengths(),
            ),
            cold,
        );
    }

    #[test]
    #[allow(clippy::too_many_lines)] // React base chains, nested arguments, and export poison share one proof.
    fn react_generic_heritage_authenticates_nested_forwarded_arguments_and_constraints() {
        let parsed = parse_source_file(concat!(
            "interface HTMLElement {}\n",
            "declare namespace React {\n",
            "  interface HTMLAttributes<T> {}\n",
            "  interface AllHTMLAttributes<T> extends HTMLAttributes<T> {}\n",
            "  interface DOMElement<P extends HTMLAttributes<T>, T extends HTMLElement> {}\n",
            "  interface DetailedReactHTMLElement<",
            "P extends HTMLAttributes<T>, T extends HTMLElement> ",
            "extends DOMElement<P, T> {}\n",
            "  interface ReactHTMLElement<T extends HTMLElement> ",
            "extends DetailedReactHTMLElement<AllHTMLAttributes<T>, T> {}\n",
            "  interface DetailedHTMLFactory<",
            "P extends HTMLAttributes<T>, T extends HTMLElement> {}\n",
            "  interface HTMLFactory<T extends HTMLElement> ",
            "extends DetailedHTMLFactory<AllHTMLAttributes<T>, T> {}\n",
            "}\n",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(8_490);
        let mut context = checker_context(&parsed, file);
        let wrapper = interface_symbol(&parsed, file, &context, "AllHTMLAttributes");
        let element_base = interface_symbol(&parsed, file, &context, "DetailedReactHTMLElement");
        let factory_base = interface_symbol(&parsed, file, &context, "DetailedHTMLFactory");
        let snapshot = |store: &CanonicalTypeMapperStore| {
            (
                store.type_len(),
                store.signature_len(),
                store.symbol_store().symbol_table_len(),
                store.checker_link_allocated_lengths(),
            )
        };
        let cold = snapshot(context.store());

        for (name, expected_base) in [
            ("ReactHTMLElement", element_base),
            ("HTMLFactory", factory_base),
        ] {
            let planned = heritage_plan(&parsed, file, &context, name).unwrap();
            let [base] = planned.bases.as_slice() else {
                panic!("{name}: React must retain its one nested generic base")
            };
            assert_eq!(base.symbol, expected_base);
            let [nested, forwarded] = base.type_arguments.as_slice() else {
                panic!("{name}: React must retain its wrapped and direct owner arguments")
            };
            let NodeData::TypeReferenceNode(nested_reference) =
                &parsed.arena.get(nested.node).unwrap().data
            else {
                panic!("{name}: the first base argument must remain a generic interface")
            };
            let [nested_parameter] = nested_reference
                .type_arguments
                .as_ref()
                .unwrap()
                .nodes
                .as_slice()
            else {
                panic!("{name}: the wrapped generic argument must retain one owner parameter")
            };
            assert_eq!(
                parsed.arena.get(*nested_parameter).unwrap().kind,
                SyntaxKind::TypeReference,
            );
            assert_eq!(
                parsed.arena.get(forwarded.node).unwrap().kind,
                SyntaxKind::TypeReference,
            );
            assert_eq!(heritage_plan(&parsed, file, &context, name), Ok(planned));
            assert_eq!(snapshot(context.store()), cold);
        }

        let namespace = context.store().get_parent_of_symbol(wrapper).unwrap();
        let exports = context
            .store()
            .symbol(namespace)
            .unwrap()
            .exports()
            .unwrap();
        assert_eq!(
            context.store_mut_for_test().insert_symbol(
                exports,
                EscapedName::source("AllHTMLAttributes"),
                element_base,
            ),
            Some(Some(wrapper)),
        );
        let poisoned = snapshot(context.store());
        assert!(matches!(
            heritage_plan(&parsed, file, &context, "ReactHTMLElement"),
            Err(DirectInterfaceHeritageError::Unsupported { .. })
        ));
        assert_eq!(snapshot(context.store()), poisoned);
        assert_eq!(
            context.store_mut_for_test().insert_symbol(
                exports,
                EscapedName::source("AllHTMLAttributes"),
                wrapper,
            ),
            Some(Some(element_base)),
        );
        assert!(heritage_plan(&parsed, file, &context, "ReactHTMLElement").is_ok());
    }

    #[test]
    fn react_mixin_heritage_uses_the_declared_lifecycle_default() {
        let parsed = parse_source_file(concat!(
            "declare namespace React { ",
            "interface ComponentLifecycle<P, S, SS = any> {} ",
            "interface Mixin<P, S> extends ComponentLifecycle<P, S> {} ",
            "}",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(8_491);
        let context = checker_context(&parsed, file);
        let lifecycle = interface_symbol(&parsed, file, &context, "ComponentLifecycle");
        let cold = (
            context.store().type_len(),
            context.store().signature_len(),
            context.store().symbol_store().symbol_table_len(),
            context.store().checker_link_allocated_lengths(),
        );

        let planned = heritage_plan(&parsed, file, &context, "Mixin").unwrap();
        let [base] = planned.bases.as_slice() else {
            panic!("Mixin must retain its single lifecycle base")
        };
        assert_eq!(base.symbol, lifecycle);
        assert_eq!(base.type_arguments.len(), 3);
        assert_eq!(
            parsed.arena.get(base.type_arguments[2].node).unwrap().kind,
            SyntaxKind::AnyKeyword,
        );
        assert_eq!(heritage_plan(&parsed, file, &context, "Mixin"), Ok(planned));
        assert_eq!(
            (
                context.store().type_len(),
                context.store().signature_len(),
                context.store().symbol_store().symbol_table_len(),
                context.store().checker_link_allocated_lengths(),
            ),
            cold,
        );
    }

    #[test]
    fn react_nested_generic_heritage_rejects_foreign_and_nonforwarded_arguments() {
        for (index, (source, owner)) in [
            (
                concat!(
                    "declare namespace Other { ",
                    "interface Wrapper<T> {} interface Base<P, T> {} ",
                    "interface Derived<T> extends Base<Wrapper<T>, T> {} ",
                    "}",
                ),
                "Derived",
            ),
            (
                concat!(
                    "interface Foreign<T> {} ",
                    "declare namespace React { ",
                    "interface Base<P, T> {} ",
                    "interface Derived<T> extends Base<Foreign<T>, T> {} ",
                    "}",
                ),
                "Derived",
            ),
            (
                concat!(
                    "declare namespace React { ",
                    "interface Wrapper<T> {} interface Base<P, T> {} ",
                    "interface Derived<T> extends Base<Wrapper<string>, T> {} ",
                    "}",
                ),
                "Derived",
            ),
            (
                concat!(
                    "declare namespace React { ",
                    "interface Wrapper<T> {} interface Base<P, T> {} ",
                    "interface Derived<T> ",
                    "extends Base<Wrapper<Wrapper<Wrapper<T>>>, T> {} ",
                    "}",
                ),
                "Derived",
            ),
        ]
        .into_iter()
        .enumerate()
        {
            let parsed = parse_source_file(source);
            assert!(
                parsed.diagnostics.is_empty(),
                "{index}: {:?}",
                parsed.diagnostics,
            );
            let file = FileId::new(8_491 + u32::try_from(index).unwrap());
            let context = checker_context(&parsed, file);
            let cold = (
                context.store().type_len(),
                context.store().signature_len(),
                context.store().symbol_store().symbol_table_len(),
                context.store().checker_link_allocated_lengths(),
            );

            assert!(
                matches!(
                    heritage_plan(&parsed, file, &context, owner),
                    Err(DirectInterfaceHeritageError::Unsupported { .. })
                ),
                "{index}: {source}",
            );
            assert_eq!(
                (
                    context.store().type_len(),
                    context.store().signature_len(),
                    context.store().symbol_store().symbol_table_len(),
                    context.store().checker_link_allocated_lengths(),
                ),
                cold,
                "{index}: rejected nested heritage published checker state",
            );
        }
    }

    #[test]
    fn concrete_namespace_interface_bases_keep_react_svg_arguments_lazy() {
        let parsed = parse_source_file(concat!(
            "interface Element {}\n",
            "interface SVGElement extends Element {}\n",
            "declare namespace React {\n",
            "  interface ReactElement<Props> { props: Props; }\n",
            "  interface SVGAttributes<T extends Element> { element?: T; }\n",
            "  interface DOMElement<Props extends SVGAttributes<T>, T extends Element> ",
            "extends ReactElement<Props> { type: string; }\n",
            "  interface ReactSVGElement ",
            "extends DOMElement<SVGAttributes<SVGElement>, SVGElement> { type: string; }\n",
            "  interface ReactPortal extends ReactElement<any> { children: string; }\n",
            "}\n",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(8_463);
        let context = checker_context(&parsed, file);
        let dom_element = interface_symbol(&parsed, file, &context, "DOMElement");
        let react_element = interface_symbol(&parsed, file, &context, "ReactElement");
        let cold = (
            context.store().type_len(),
            context.store().signature_len(),
            context.store().symbol_store().symbol_table_len(),
            context.store().checker_link_allocated_lengths(),
        );

        let svg = heritage_plan(&parsed, file, &context, "ReactSVGElement").unwrap();
        let [svg_base] = svg.bases.as_slice() else {
            panic!("ReactSVGElement must retain its instantiated DOMElement base")
        };
        assert_eq!(svg_base.symbol, dom_element);
        assert_eq!(svg_base.kind, DirectInterfaceBaseKind::Interface);
        assert_eq!(
            svg_base
                .type_arguments
                .iter()
                .map(|argument| parsed.arena.get(argument.node).unwrap().kind)
                .collect::<Vec<_>>(),
            [SyntaxKind::TypeReference, SyntaxKind::TypeReference],
        );

        let portal = heritage_plan(&parsed, file, &context, "ReactPortal").unwrap();
        let [portal_base] = portal.bases.as_slice() else {
            panic!("ReactPortal must retain its instantiated ReactElement base")
        };
        assert_eq!(portal_base.symbol, react_element);
        assert_eq!(portal_base.type_arguments.len(), 1);
        assert_eq!(
            parsed
                .arena
                .get(portal_base.type_arguments[0].node)
                .unwrap()
                .kind,
            SyntaxKind::AnyKeyword,
        );
        assert_eq!(
            (
                context.store().type_len(),
                context.store().signature_len(),
                context.store().symbol_store().symbol_table_len(),
                context.store().checker_link_allocated_lengths(),
            ),
            cold,
        );
    }

    #[test]
    fn concrete_interface_bases_reject_unresolved_and_malformed_type_arguments() {
        for (index, source) in [
            concat!(
                "interface Derived extends Base<Missing> {}\n",
                "interface Base<Value> { value: Value }\n",
            ),
            concat!(
                "interface Derived extends Base<number, string> {}\n",
                "interface Base<Value> { value: Value }\n",
            ),
            concat!(
                "interface Wrapped<Value> { value: Value }\n",
                "interface Derived extends Base<Wrapped<number, string>> {}\n",
                "interface Base<Value> { value: Value }\n",
            ),
            concat!(
                "interface Wrapped {}\n",
                "interface Derived extends Base<Wrapped<number>> {}\n",
                "interface Base<Value> { value: Value }\n",
            ),
        ]
        .into_iter()
        .enumerate()
        {
            let parsed = parse_source_file(source);
            assert!(
                parsed.diagnostics.is_empty(),
                "{index}: {:?}",
                parsed.diagnostics
            );
            let file = FileId::new(8_464 + u32::try_from(index).unwrap());
            let context = checker_context(&parsed, file);
            let cold = (
                context.store().type_len(),
                context.store().signature_len(),
                context.store().symbol_store().symbol_table_len(),
                context.store().checker_link_allocated_lengths(),
            );

            assert!(
                matches!(
                    heritage_plan(&parsed, file, &context, "Derived"),
                    Err(DirectInterfaceHeritageError::Unsupported { .. })
                ),
                "{index}: {source}",
            );
            assert_eq!(
                (
                    context.store().type_len(),
                    context.store().signature_len(),
                    context.store().symbol_store().symbol_table_len(),
                    context.store().checker_link_allocated_lengths(),
                ),
                cold,
                "{index}: rejected concrete heritage published checker state",
            );
        }
    }

    #[test]
    fn ordered_nongeneric_bases_keep_generic_class_and_duplicate_boundaries() {
        for (index, (source, kind)) in [
            (
                concat!(
                    "interface First {} interface Second {} interface Third {}\n",
                    "interface Derived<T> extends First, Second, Third {}\n",
                ),
                SyntaxKind::HeritageClause,
            ),
            (
                concat!(
                    "interface First {} interface Second {} interface Third<T> {}\n",
                    "interface Derived extends First, Second, Third<number> {}\n",
                ),
                SyntaxKind::HeritageClause,
            ),
            (
                concat!(
                    "interface First {} interface Second {} interface Third<T = number> {}\n",
                    "interface Derived extends First, Second, Third {}\n",
                ),
                SyntaxKind::HeritageClause,
            ),
            (
                concat!(
                    "interface First {} interface Second {} interface Third {}\n",
                    "class Derived {} interface Derived extends First, Second, Third {}\n",
                ),
                SyntaxKind::HeritageClause,
            ),
            (
                concat!(
                    "interface First {} interface Second {}\n",
                    "interface Derived extends First, Second, First {}\n",
                ),
                SyntaxKind::Identifier,
            ),
        ]
        .into_iter()
        .enumerate()
        {
            let parsed = parse_source_file(source);
            assert!(
                parsed.diagnostics.is_empty(),
                "{source}: {:?}",
                parsed.diagnostics
            );
            let file = FileId::new(202_820 + u32::try_from(index).unwrap());
            let context = checker_context(&parsed, file);
            let snapshot = || {
                (
                    context.store().type_len(),
                    context.store().symbol_len(),
                    context.store().signature_len(),
                    context.store().mapper_len(),
                    context.store().symbol_store().symbol_table_len(),
                    context.store().checker_link_allocated_lengths(),
                )
            };
            let cold = snapshot();
            let error = heritage_plan(&parsed, file, &context, "Derived").unwrap_err();
            assert!(
                matches!(error,
                DirectInterfaceHeritageError::Unsupported { kind: actual, .. } if actual == kind),
                "{source}: {error:?}"
            );
            assert_eq!(snapshot(), cold, "{source}");
            assert_eq!(
                heritage_plan(&parsed, file, &context, "Derived"),
                Err(error)
            );
            assert_eq!(snapshot(), cold, "{source}");
        }
    }

    #[test]
    fn transitive_interface_cycles_remain_unsupported() {
        let parsed = parse_source_file(concat!(
            "interface Left extends Right { first: number }\n",
            "interface Right extends Left { second: string }\n",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(8_452);
        let context = checker_context(&parsed, file);

        assert!(matches!(
            heritage_plan(&parsed, file, &context, "Left"),
            Err(DirectInterfaceHeritageError::Unsupported { .. })
        ));
    }

    #[test]
    fn record_mapped_alias_base_retains_authenticated_type_arguments() {
        let parsed = parse_source_file(concat!(
            "type Record<K extends keyof any, T> = { [P in K]: T };\n",
            "declare namespace JSX {\n",
            "  interface IntrinsicElements extends Record<string, any> {}\n",
            "}\n",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(8_403);
        let context = checker_context(&parsed, file);
        let cold = (
            context.store().type_len(),
            context.store().signature_len(),
            context.store().symbol_store().symbol_table_len(),
            context.store().checker_link_allocated_lengths(),
        );

        let plan = heritage_plan(&parsed, file, &context, "IntrinsicElements").unwrap();
        let [base] = plan.bases.as_slice() else {
            panic!("the mapped alias must remain the only direct base")
        };
        assert_eq!(base.kind, DirectInterfaceBaseKind::RecordMappedAlias);
        assert_eq!(
            base.type_arguments
                .iter()
                .map(|argument| parsed.arena.get(argument.node).unwrap().kind)
                .collect::<Vec<_>>(),
            [SyntaxKind::StringKeyword, SyntaxKind::AnyKeyword]
        );
        assert_eq!(
            context.store().symbol(base.symbol).unwrap().flags(),
            SymbolFlags::TYPE_ALIAS
        );
        assert_eq!(
            (
                context.store().type_len(),
                context.store().signature_len(),
                context.store().symbol_store().symbol_table_len(),
                context.store().checker_link_allocated_lengths(),
            ),
            cold
        );
    }

    #[test]
    fn record_mapped_alias_lookalikes_remain_unsupported() {
        let cases = [
            concat!(
                "type Record<K extends string, T> = { [P in K]: T };\n",
                "interface Derived extends Record<string, any> {}\n",
            ),
            concat!(
                "type Record<K extends keyof any, T = number> = { [P in K]: T };\n",
                "interface Derived extends Record<string, any> {}\n",
            ),
            concat!(
                "type Record<K extends keyof any, T> = { readonly [P in K]: T };\n",
                "interface Derived extends Record<string, any> {}\n",
            ),
            concat!(
                "type Record<K extends keyof any, T> = { [P in K]: K };\n",
                "interface Derived extends Record<string, any> {}\n",
            ),
            concat!(
                "type Record<K extends keyof any, T> = { [P in K]: T };\n",
                "interface Derived extends Record<string, number> {}\n",
            ),
        ];

        for (index, source) in cases.into_iter().enumerate() {
            let parsed = parse_source_file(source);
            assert!(
                parsed.diagnostics.is_empty(),
                "{index}: {:?}",
                parsed.diagnostics
            );
            let file = FileId::new(8_410 + u32::try_from(index).unwrap());
            let context = checker_context(&parsed, file);
            let cold = (
                context.store().type_len(),
                context.store().signature_len(),
                context.store().symbol_store().symbol_table_len(),
                context.store().checker_link_allocated_lengths(),
            );

            assert!(
                matches!(
                    heritage_plan(&parsed, file, &context, "Derived"),
                    Err(DirectInterfaceHeritageError::Unsupported { .. })
                ),
                "{index}: {source}"
            );
            assert_eq!(
                (
                    context.store().type_len(),
                    context.store().signature_len(),
                    context.store().symbol_store().symbol_table_len(),
                    context.store().checker_link_allocated_lengths(),
                ),
                cold,
                "{index}: {source}"
            );
        }
    }

    #[test]
    fn merged_interface_bases_preserve_member_order_and_warm_state() {
        let parsed = parse_source_file(concat!(
            "interface Base { first: string; shared: number }\n",
            "interface Base { shared: number; second: boolean }\n",
            "interface Derived extends Base { own: string }\n",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(8_401);
        let mut context = checker_context(&parsed, file);
        let base = interface_symbol(&parsed, file, &context, "Base");
        let derived = interface_symbol(&parsed, file, &context, "Derived");

        context.check_source_file(file).unwrap();

        let base_type = context
            .store()
            .declared_type_links(base)
            .and_then(|links| links.declared_type)
            .unwrap();
        let derived_type = context
            .store()
            .declared_type_links(derived)
            .and_then(|links| links.declared_type)
            .unwrap();
        let TypeData::Interface(interface) =
            context.store().type_payload(derived_type).unwrap().data()
        else {
            panic!("a derived interface must retain its interface type");
        };
        assert_eq!(
            interface.resolved_base_types.as_deref(),
            Some(&[base_type][..])
        );
        let property_names = interface
            .reference
            .object
            .structured
            .properties
            .as_deref()
            .unwrap()
            .iter()
            .map(|property| {
                context
                    .store()
                    .symbol(*property)
                    .and_then(|property| property.name().as_utf8())
                    .unwrap()
            })
            .collect::<Vec<_>>();
        assert_eq!(property_names, ["own", "first", "shared", "second"]);
        assert!(context.diagnostics().is_empty());

        let warm = (
            context.store().type_len(),
            context.store().signature_len(),
            context.store().symbol_store().symbol_table_len(),
            context.store().checker_link_allocated_lengths(),
            context.diagnostics().clone(),
        );
        context.recheck_source_file(file).unwrap();
        assert_eq!(
            (
                context.store().type_len(),
                context.store().signature_len(),
                context.store().symbol_store().symbol_table_len(),
                context.store().checker_link_allocated_lengths(),
                context.diagnostics().clone(),
            ),
            warm,
        );
    }

    #[test]
    fn merged_generic_interface_bases_preserve_inherited_proxy_identity() {
        let parsed = parse_source_file(concat!(
            "interface Base<T> { first: T }\n",
            "interface Base<T> { second: T }\n",
            "interface Derived extends Base<number> { own: boolean }\n",
            "interface Leaf extends Derived { first: number; extra: string }\n",
            "declare const item: Derived;\n",
            "declare const leaf: Leaf; const leafFirst: number = leaf.first;\n",
            "const leafSecond: number = leaf.second;\n",
            "const first: number = item.first; const second: number = item.second;\n",
            "const own: boolean = item.own;\n",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(8_402);
        let mut context = checker_context(&parsed, file);
        let base = interface_symbol(&parsed, file, &context, "Base");
        let derived = interface_symbol(&parsed, file, &context, "Derived");
        context.check_source_file(file).unwrap();
        let base_target = context.get_declared_type_of_symbol(base).unwrap();
        let target = context.get_declared_type_of_symbol(derived).unwrap();
        assert!(validate_nongeneric_interface_argument_origin(context.store(), target).is_ok());
        let TypeData::Interface(interface) = context.store().type_payload(target).unwrap().data()
        else {
            panic!("Derived must retain its interface identity")
        };
        assert!(interface.this_type.is_some());
        let [base_reference] = interface.resolved_base_types.as_deref().unwrap() else {
            panic!("Derived must retain one concrete base")
        };
        let base_reference = *base_reference;
        assert_eq!(
            validate_direct_generic_reference(context.store(), base_reference)
                .unwrap()
                .target,
            base_target
        );
        let properties = interface
            .reference
            .object
            .structured
            .properties
            .as_ref()
            .unwrap();
        assert_eq!(
            properties
                .iter()
                .map(|property| context
                    .store()
                    .symbol(*property)
                    .unwrap()
                    .name()
                    .as_utf8()
                    .unwrap())
                .collect::<Vec<_>>(),
            ["own", "first", "second"]
        );
        for property in &properties[1..] {
            let links = context.store().value_symbol_links(*property).unwrap();
            assert!(links.target.is_some());
            assert!(links.mapper.is_some());
            assert_eq!(
                links.resolved_type,
                Some(context.store().intrinsic_bootstrap().unwrap().number_type)
            );
        }
        let warm = (
            context.store().type_len(),
            context.store().signature_len(),
            context.store().symbol_store().symbol_table_len(),
            context.store().checker_link_allocated_lengths(),
        );

        context.recheck_source_file(file).unwrap();
        assert_eq!(
            (
                context.store().type_len(),
                context.store().signature_len(),
                context.store().symbol_store().symbol_table_len(),
                context.store().checker_link_allocated_lengths(),
            ),
            warm,
        );
        assert!(context.diagnostics().is_empty());
    }

    #[test]
    fn inherited_generic_property_reads_reject_proxy_cache_poison() {
        let parsed = parse_source_file(concat!(
            "interface Base<T> { value: T; } ",
            "interface Derived extends Base<number> {} ",
            "declare const item: Derived; const value: number = item.value;",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(8_553);
        let mut context = checker_context(&parsed, file);
        context.check_source_file(file).unwrap();
        let owner = interface_symbol(&parsed, file, &context, "Derived");
        let target = context.get_declared_type_of_symbol(owner).unwrap();
        let property = context
            .store_mut_for_test()
            .resolved_own_property(target, "value")
            .unwrap()
            .unwrap()
            .symbol;
        let original = context
            .store()
            .value_symbol_links(property)
            .unwrap()
            .clone();
        let string = context.store().intrinsic_bootstrap().unwrap().string_type;
        let warm = (
            context.store().type_len(),
            context.store().mapper_len(),
            context.store().checker_link_allocated_lengths(),
        );
        for poison_mapper in [false, true] {
            let mut poisoned = original.clone();
            if poison_mapper {
                poisoned.mapper = None;
            } else {
                poisoned.resolved_type = Some(string);
            }
            assert!(
                context
                    .store_mut_for_test()
                    .set_value_symbol_links(property, poisoned)
            );
            assert!(
                context
                    .store_mut_for_test()
                    .resolved_own_property(target, "value")
                    .is_err()
            );
            assert_eq!(
                (
                    context.store().type_len(),
                    context.store().mapper_len(),
                    context.store().checker_link_allocated_lengths()
                ),
                warm
            );
            assert!(
                context
                    .store_mut_for_test()
                    .set_value_symbol_links(property, original.clone())
            );
            assert_eq!(
                context
                    .store_mut_for_test()
                    .resolved_own_property(target, "value")
                    .unwrap()
                    .unwrap()
                    .symbol,
                property
            );
        }
        assert!(context.diagnostics().is_empty());
    }
}
