//! Declared class, interface, and type-parameter identities.
//!
//! This is the dependency-closed first cut of TypeScript-Go's
//! `getDeclaredTypeOfSymbol`, pinned to
//! `dc37b5249ab60e2bbce936f71b883e6c8136167e`. It deliberately implements
//! classes, interfaces whose `this` decision is dependency-closed, and ordinary
//! type parameters. Other declared families remain explicit unavailable
//! results, while symbols with no declared-type family retain the pinned
//! `errorType` fallback.
//!
//! The Go checker can follow mutable AST pointers directly. The Rust port
//! instead requires a provenance-bearing [`DeclaredTypeHost`] containing the
//! exact immutable arenas and canonical [`BoundFile`] side data. Construction
//! preflights the complete class/interface/type-parameter plan before the first
//! checker write; unsupported syntax and missing or foreign facts therefore
//! cannot leave a partially published semantic graph.

use std::collections::{BTreeMap, HashSet};

use ts_ast::{FileId, Node, NodeArena, NodeArenaId, NodeData, NodeList, NodeRef, SyntaxKind};
use ts_binder::{BoundFile, SemanticSymbolId, SymbolFlags};
use xxhash_rust::xxh3::Xxh3;

use super::{
    ids::TypeId,
    mapper::TypeMapper,
    store::SemanticStore,
    type_records::{CacheHashKey, InterfaceTypeData, TypeCacheState, TypeData, TypeRecord},
    types::{ObjectFlags, TypeFlags},
};

#[derive(Clone, Copy, Debug)]
struct DeclaredTypeSource<'a> {
    arena: &'a NodeArena,
    bound: &'a BoundFile,
}

/// Exact Program syntax and binder side data available to declared-type work.
///
/// Sources are borrowed rather than copied so node identity remains the
/// parser's identity. Every source must have completed canonical declaration
/// binding before it can enter the host.
#[derive(Debug, Default)]
pub struct DeclaredTypeHost<'a> {
    sources: BTreeMap<FileId, DeclaredTypeSource<'a>>,
}

/// A source rejected while constructing a [`DeclaredTypeHost`].
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum DeclaredTypeHostError {
    ArenaMismatch {
        file: FileId,
        expected: NodeArenaId,
        actual: NodeArenaId,
    },
    DeclarationsIncomplete(FileId),
    InvalidSourceFile(NodeRef),
    DuplicateFile(FileId),
}

impl std::fmt::Display for DeclaredTypeHostError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::ArenaMismatch { file, .. } => write!(
                formatter,
                "declared-type source {} uses a different AST arena",
                file.index()
            ),
            Self::DeclarationsIncomplete(file) => write!(
                formatter,
                "declared-type source {} has incomplete declaration bindings",
                file.index()
            ),
            Self::InvalidSourceFile(source) => write!(
                formatter,
                "declared-type source {} has an invalid source-file root",
                source.file.index()
            ),
            Self::DuplicateFile(file) => write!(
                formatter,
                "declared-type source {} was supplied more than once",
                file.index()
            ),
        }
    }
}

impl std::error::Error for DeclaredTypeHostError {}

impl<'a> DeclaredTypeHost<'a> {
    /// Retains a checked set of canonical Program sources.
    ///
    /// An empty host is valid for cached identities, unsupported declared
    /// families, and the ordinary `errorType` fallback.
    ///
    /// # Errors
    ///
    /// Returns a typed provenance error if a source has incomplete bindings,
    /// mismatched arena identity, an invalid root, or a duplicate file slot.
    pub fn new(
        sources: impl IntoIterator<Item = (&'a NodeArena, &'a BoundFile)>,
    ) -> Result<Self, DeclaredTypeHostError> {
        let mut host = Self::default();
        for (arena, bound) in sources {
            let file = bound.file_id();
            if arena.id() != bound.node_arena_id() {
                return Err(DeclaredTypeHostError::ArenaMismatch {
                    file,
                    expected: bound.node_arena_id(),
                    actual: arena.id(),
                });
            }
            if !bound.declarations_complete() {
                return Err(DeclaredTypeHostError::DeclarationsIncomplete(file));
            }
            let source = bound.source_file();
            if !source.is_for(arena.id(), file)
                || !bound.contains(source)
                || !matches!(
                    arena.get(source.node),
                    Some(Node {
                        kind: SyntaxKind::SourceFile,
                        parent: None,
                        data: NodeData::SourceFile(_),
                        ..
                    })
                )
            {
                return Err(DeclaredTypeHostError::InvalidSourceFile(source));
            }
            if host
                .sources
                .insert(file, DeclaredTypeSource { arena, bound })
                .is_some()
            {
                return Err(DeclaredTypeHostError::DuplicateFile(file));
            }
        }
        Ok(host)
    }

    fn node(&self, reference: NodeRef) -> Option<&Node> {
        let source = self.sources.get(&reference.file)?;
        if source.arena.id() != reference.arena || !source.bound.contains(reference) {
            return None;
        }
        source
            .arena
            .get(reference.node)
            .filter(|node| node.data.matches_syntax_kind(node.kind))
    }

    fn bound_file(&self, reference: NodeRef) -> Option<&BoundFile> {
        let source = self.sources.get(&reference.file)?;
        (source.arena.id() == reference.arena).then_some(source.bound)
    }

    fn symbol_matches(&self, node: NodeRef, symbol: SemanticSymbolId) -> bool {
        self.bound_file(node).is_some_and(|bound| {
            bound.symbol(node) == Some(symbol) || bound.local_symbol(node) == Some(symbol)
        })
    }
}

/// Declared families intentionally outside this cut.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum UnsupportedDeclaredTypeKind {
    TypeAlias,
    Enum,
    EnumMember,
    Alias,
}

/// An outer type-parameter source that requires checker functionality not yet
/// present in this dependency-closed cut.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum UnsupportedOuterTypeParameterContext {
    FunctionExpression,
    ArrowFunction,
    ObjectLiteralMethod,
    MappedType,
    ConditionalType,
    InferType,
}

/// Typed reason that an exact declared identity cannot yet be produced.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum DeclaredTypeUnavailable {
    IntrinsicBootstrapNotInitialized,
    SymbolNotOwned(SemanticSymbolId),
    UnsupportedDeclaredType(UnsupportedDeclaredTypeKind),
    AliasMergedWithDeclaredSymbol(SemanticSymbolId),
    MissingDeclarations(SemanticSymbolId),
    MissingValueDeclaration(SemanticSymbolId),
    MissingOrForeignFacts(NodeRef),
    DeclarationSymbolMismatch(NodeRef),
    InvalidClassDeclaration(NodeRef),
    InvalidInterfaceDeclaration(NodeRef),
    UnsupportedInterfaceHeritageResolution(NodeRef),
    InvalidTypeParameterSymbol(SemanticSymbolId),
    InvalidTypeParameterDeclaration(NodeRef),
    UnsupportedOuterTypeParameterContext {
        node: NodeRef,
        context: UnsupportedOuterTypeParameterContext,
    },
    InvalidCachedDeclaredType {
        symbol: SemanticSymbolId,
        declared_type: TypeId,
    },
}

/// Exact declared-type failure domain for the currently installed cut.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum DeclaredTypeError {
    Unavailable(DeclaredTypeUnavailable),
}

impl From<DeclaredTypeUnavailable> for DeclaredTypeError {
    fn from(unavailable: DeclaredTypeUnavailable) -> Self {
        Self::Unavailable(unavailable)
    }
}

impl std::fmt::Display for DeclaredTypeError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Unavailable(reason) => {
                write!(formatter, "declared type is unavailable: {reason:?}")
            }
        }
    }
}

impl std::error::Error for DeclaredTypeError {}

#[derive(Debug)]
struct ClassPlan {
    symbol: SemanticSymbolId,
    type_parameters: Vec<SemanticSymbolId>,
    outer_type_parameter_count: usize,
}

#[derive(Debug)]
struct InterfacePlan {
    symbol: SemanticSymbolId,
    type_parameters: Vec<SemanticSymbolId>,
    outer_type_parameter_count: usize,
    has_this_type: bool,
}

fn unavailable(reason: DeclaredTypeUnavailable) -> DeclaredTypeError {
    DeclaredTypeError::Unavailable(reason)
}

fn malformed_alias_merge(flags: SymbolFlags) -> bool {
    flags.contains(SymbolFlags::ALIAS) && flags.without(SymbolFlags::ALIAS) != SymbolFlags::NONE
}

fn ordinary_type_parameter_symbol_flags(flags: SymbolFlags) -> bool {
    flags.contains(SymbolFlags::TYPE_PARAMETER)
        && !flags.intersects(SymbolFlags::TYPE_PARAMETER_EXCLUDES)
        && !malformed_alias_merge(flags)
}

fn origin_type_parameter_object_flags(flags: ObjectFlags) -> bool {
    flags == ObjectFlags::NONE
        || flags
            == (ObjectFlags::COULD_CONTAIN_TYPE_VARIABLES_COMPUTED
                | ObjectFlags::COULD_CONTAIN_TYPE_VARIABLES)
}

fn cached_ordinary_type_parameter_owner(
    store: &SemanticStore<TypeRecord, TypeMapper>,
    declared_type: TypeId,
) -> Option<SemanticSymbolId> {
    let record = store.type_payload(declared_type)?;
    let TypeData::TypeParameter(data) = record.data() else {
        return None;
    };
    if record.flags() != TypeFlags::TYPE_PARAMETER
        || !origin_type_parameter_object_flags(record.object_flags())
        || record.alias().is_some()
        || data.is_this_type
        || data.target.is_some()
        || data.mapper.is_some()
    {
        return None;
    }
    let symbol = record.symbol()?;
    if !store
        .symbol(symbol)
        .is_some_and(|record| ordinary_type_parameter_symbol_flags(record.flags()))
        || store
            .declared_type_links(symbol)
            .and_then(|links| links.declared_type)
            != Some(declared_type)
    {
        return None;
    }
    Some(symbol)
}

fn cached_class_type(
    store: &SemanticStore<TypeRecord, TypeMapper>,
    symbol: SemanticSymbolId,
) -> Result<Option<TypeId>, DeclaredTypeError> {
    cached_class_or_interface_type(store, symbol, ObjectFlags::CLASS)
}

fn cached_interface_type(
    store: &SemanticStore<TypeRecord, TypeMapper>,
    symbol: SemanticSymbolId,
) -> Result<Option<TypeId>, DeclaredTypeError> {
    cached_class_or_interface_type(store, symbol, ObjectFlags::INTERFACE)
}

fn cached_class_or_interface_type(
    store: &SemanticStore<TypeRecord, TypeMapper>,
    symbol: SemanticSymbolId,
    origin: ObjectFlags,
) -> Result<Option<TypeId>, DeclaredTypeError> {
    // Like the class-only cut, a cached identity validates its complete
    // checker-owned graph but does not rederive host-owned declaration arity,
    // outer counts, or the interface's `this` decision. Cached calls may use an
    // empty host, so those remain the explicit cache/host trust boundary.
    let Some(declared_type) = store
        .declared_type_links(symbol)
        .and_then(|links| links.declared_type)
    else {
        return Ok(None);
    };
    let valid = store.type_payload(declared_type).is_some_and(|record| {
        fully_initialized_reference_origin_type(store, symbol, declared_type, origin, record)
            || origin == ObjectFlags::INTERFACE
                && fully_initialized_thisless_interface_type(symbol, record)
            || store.declared_type_initialization_in_progress(symbol)
                && uninitialized_class_or_interface_shell(symbol, origin, record)
    });
    if valid {
        Ok(Some(declared_type))
    } else {
        Err(unavailable(
            DeclaredTypeUnavailable::InvalidCachedDeclaredType {
                symbol,
                declared_type,
            },
        ))
    }
}

fn uninitialized_class_or_interface_shell(
    symbol: SemanticSymbolId,
    origin: ObjectFlags,
    record: &TypeRecord,
) -> bool {
    record.flags() == TypeFlags::OBJECT
        && record.object_flags() == origin
        && record.symbol() == Some(symbol)
        && record.alias().is_none()
        && matches!(record.data(), TypeData::Interface(data) if data == &InterfaceTypeData::default())
}

fn fully_initialized_thisless_interface_type(
    symbol: SemanticSymbolId,
    record: &TypeRecord,
) -> bool {
    if record.flags() != TypeFlags::OBJECT
        || record.object_flags() & ObjectFlags::OBJECT_TYPE_KIND_MASK != ObjectFlags::INTERFACE
        || record.symbol() != Some(symbol)
        || record.alias().is_some()
    {
        return false;
    }
    matches!(
        record.data(),
        TypeData::Interface(data)
            if data.all_type_parameters.is_none()
                && data.outer_type_parameter_count == 0
                && data.this_type.is_none()
                && data.reference.object.target.is_none()
                && data.reference.object.mapper.is_none()
                && data.reference.object.instantiations == TypeCacheState::Unallocated
                && data.reference.node.is_none()
                && data.reference.resolved_type_arguments.is_none()
    )
}

fn fully_initialized_reference_origin_type(
    store: &SemanticStore<TypeRecord, TypeMapper>,
    symbol: SemanticSymbolId,
    declared_type: TypeId,
    origin: ObjectFlags,
    record: &TypeRecord,
) -> bool {
    let opposite_origin = if origin == ObjectFlags::CLASS {
        ObjectFlags::INTERFACE
    } else {
        ObjectFlags::CLASS
    };
    if record.flags() != TypeFlags::OBJECT
        || record.object_flags() & ObjectFlags::OBJECT_TYPE_KIND_MASK
            != origin | ObjectFlags::REFERENCE
        || record.object_flags().contains(opposite_origin)
        || record.symbol() != Some(symbol)
        || record.alias().is_some()
    {
        return false;
    }
    let TypeData::Interface(data) = record.data() else {
        return false;
    };
    let (Some(all_type_parameters), Some(this_type), Some(resolved_type_arguments)) = (
        data.all_type_parameters.as_deref(),
        data.this_type,
        data.reference.resolved_type_arguments.as_deref(),
    ) else {
        return false;
    };
    if all_type_parameters.len() != resolved_type_arguments.len() + 1
        || all_type_parameters.last().copied() != Some(this_type)
        || &all_type_parameters[..resolved_type_arguments.len()] != resolved_type_arguments
        || resolved_type_arguments.contains(&this_type)
        || data.outer_type_parameter_count > resolved_type_arguments.len()
        || data.reference.object.target != Some(declared_type)
        || data.reference.object.mapper.is_some()
        || data.reference.node.is_some()
        || resolved_type_arguments
            .iter()
            .copied()
            .collect::<HashSet<_>>()
            .len()
            != resolved_type_arguments.len()
        || !resolved_type_arguments
            .iter()
            .all(|parameter| cached_ordinary_type_parameter_owner(store, *parameter).is_some())
        || !all_type_parameters
            .iter()
            .all(|parameter| store.type_payload(*parameter).is_some())
    {
        return false;
    }
    let Some(this_record) = store.type_payload(this_type) else {
        return false;
    };
    if this_record.flags() != TypeFlags::TYPE_PARAMETER
        || !origin_type_parameter_object_flags(this_record.object_flags())
        || this_record.alias().is_some()
        || this_record.symbol() != Some(symbol)
        || !matches!(
            this_record.data(),
            TypeData::TypeParameter(data)
                if data.is_this_type
                    && data.constraint == Some(declared_type)
                    && data.target.is_none()
                    && data.mapper.is_none()
        )
    {
        return false;
    }
    matches!(
        &data.reference.object.instantiations,
        TypeCacheState::Allocated(instantiations)
            if instantiations.get(&type_list_key(resolved_type_arguments))
                == Some(&declared_type)
    )
}

fn cached_type_parameter(
    store: &SemanticStore<TypeRecord, TypeMapper>,
    symbol: SemanticSymbolId,
) -> Result<Option<TypeId>, DeclaredTypeError> {
    let Some(declared_type) = store
        .declared_type_links(symbol)
        .and_then(|links| links.declared_type)
    else {
        return Ok(None);
    };
    let valid = cached_ordinary_type_parameter_owner(store, declared_type) == Some(symbol);
    if valid {
        Ok(Some(declared_type))
    } else {
        Err(unavailable(
            DeclaredTypeUnavailable::InvalidCachedDeclaredType {
                symbol,
                declared_type,
            },
        ))
    }
}

fn preflight_node<'a>(
    store: &SemanticStore<TypeRecord, TypeMapper>,
    host: &'a DeclaredTypeHost<'_>,
    node: NodeRef,
) -> Result<&'a Node, DeclaredTypeError> {
    if !store.contains_node_ref(node) {
        return Err(unavailable(DeclaredTypeUnavailable::MissingOrForeignFacts(
            node,
        )));
    }
    host.node(node)
        .ok_or_else(|| unavailable(DeclaredTypeUnavailable::MissingOrForeignFacts(node)))
}

fn preflight_type_parameter_symbol(
    store: &SemanticStore<TypeRecord, TypeMapper>,
    host: &DeclaredTypeHost<'_>,
    symbol: SemanticSymbolId,
    checked: &mut HashSet<SemanticSymbolId>,
) -> Result<(), DeclaredTypeError> {
    if !checked.insert(symbol) {
        return Ok(());
    }
    let record = store
        .symbol(symbol)
        .ok_or_else(|| unavailable(DeclaredTypeUnavailable::SymbolNotOwned(symbol)))?;
    let flags = record.flags();
    if malformed_alias_merge(flags) {
        return Err(unavailable(
            DeclaredTypeUnavailable::AliasMergedWithDeclaredSymbol(symbol),
        ));
    }
    if !ordinary_type_parameter_symbol_flags(flags) {
        return Err(unavailable(
            DeclaredTypeUnavailable::InvalidTypeParameterSymbol(symbol),
        ));
    }
    if cached_type_parameter(store, symbol)?.is_some() {
        return Ok(());
    }
    if let Some(value_declaration) = record.value_declaration() {
        return Err(unavailable(
            DeclaredTypeUnavailable::InvalidTypeParameterDeclaration(value_declaration),
        ));
    }
    let declarations = record
        .declarations()
        .filter(|declarations| !declarations.is_empty())
        .ok_or_else(|| unavailable(DeclaredTypeUnavailable::MissingDeclarations(symbol)))?;
    for declaration in declarations {
        let node = preflight_node(store, host, *declaration)?;
        if node.kind != SyntaxKind::TypeParameter
            || !matches!(node.data, NodeData::TypeParameterDeclaration(_))
            || node.parent.is_none()
        {
            return Err(unavailable(
                DeclaredTypeUnavailable::InvalidTypeParameterDeclaration(*declaration),
            ));
        }
        if !host.symbol_matches(*declaration, symbol) {
            return Err(unavailable(
                DeclaredTypeUnavailable::DeclarationSymbolMismatch(*declaration),
            ));
        }
    }
    Ok(())
}

fn push_unique(symbols: &mut Vec<SemanticSymbolId>, symbol: SemanticSymbolId) {
    if !symbols.contains(&symbol) {
        symbols.push(symbol);
    }
}

fn explicit_type_parameter_symbols(
    store: &SemanticStore<TypeRecord, TypeMapper>,
    host: &DeclaredTypeHost<'_>,
    container: NodeRef,
    parameters: Option<&NodeList>,
    checked: &mut HashSet<SemanticSymbolId>,
) -> Result<Vec<SemanticSymbolId>, DeclaredTypeError> {
    let mut result = Vec::new();
    let Some(parameters) = parameters else {
        return Ok(result);
    };
    for parameter in &parameters.nodes {
        let parameter = NodeRef::new(container.arena, container.file, *parameter);
        let node = preflight_node(store, host, parameter)?;
        if node.parent != Some(container.node)
            || node.kind != SyntaxKind::TypeParameter
            || !matches!(node.data, NodeData::TypeParameterDeclaration(_))
        {
            return Err(unavailable(
                DeclaredTypeUnavailable::InvalidTypeParameterDeclaration(parameter),
            ));
        }
        let symbol = host
            .bound_file(parameter)
            .and_then(|bound| bound.symbol(parameter))
            .ok_or_else(|| {
                unavailable(DeclaredTypeUnavailable::MissingOrForeignFacts(parameter))
            })?;
        preflight_type_parameter_symbol(store, host, symbol, checked)?;
        push_unique(&mut result, symbol);
    }
    Ok(result)
}

fn unsupported_outer_context(
    node: NodeRef,
    context: UnsupportedOuterTypeParameterContext,
) -> DeclaredTypeError {
    unavailable(DeclaredTypeUnavailable::UnsupportedOuterTypeParameterContext { node, context })
}

fn collect_outer_type_parameters(
    store: &SemanticStore<TypeRecord, TypeMapper>,
    host: &DeclaredTypeHost<'_>,
    declaration: NodeRef,
    checked: &mut HashSet<SemanticSymbolId>,
) -> Result<Vec<SemanticSymbolId>, DeclaredTypeError> {
    let mut current = declaration;
    let mut visited = HashSet::from([declaration]);
    let mut inner_to_outer = Vec::new();
    loop {
        let node = preflight_node(store, host, current)?;
        let Some(parent) = node.parent else {
            break;
        };
        let parent = NodeRef::new(current.arena, current.file, parent);
        if !visited.insert(parent) {
            return Err(unavailable(DeclaredTypeUnavailable::MissingOrForeignFacts(
                parent,
            )));
        }
        let parent_node = preflight_node(store, host, parent)?;
        let parameters = match &parent_node.data {
            NodeData::ClassDeclaration(data) => data.type_parameters.as_ref(),
            NodeData::ClassExpression(data) => data.type_parameters.as_ref(),
            NodeData::InterfaceDeclaration(data) => data.type_parameters.as_ref(),
            NodeData::CallSignatureDeclaration(data) => data.type_parameters.as_ref(),
            NodeData::ConstructSignatureDeclaration(data) => data.type_parameters.as_ref(),
            NodeData::MethodSignatureDeclaration(data) => data.type_parameters.as_ref(),
            NodeData::FunctionTypeNode(data) => data.type_parameters.as_ref(),
            NodeData::ConstructorTypeNode(data) => data.type_parameters.as_ref(),
            NodeData::FunctionDeclaration(data) => data.type_parameters.as_ref(),
            NodeData::MethodDeclaration(data) => {
                let is_object_literal_method = if let Some(grandparent) = parent_node.parent {
                    preflight_node(
                        store,
                        host,
                        NodeRef::new(parent.arena, parent.file, grandparent),
                    )?
                    .kind
                        == SyntaxKind::ObjectLiteralExpression
                } else {
                    false
                };
                if is_object_literal_method {
                    return Err(unsupported_outer_context(
                        parent,
                        UnsupportedOuterTypeParameterContext::ObjectLiteralMethod,
                    ));
                }
                data.type_parameters.as_ref()
            }
            NodeData::FunctionExpression(_) => {
                return Err(unsupported_outer_context(
                    parent,
                    UnsupportedOuterTypeParameterContext::FunctionExpression,
                ));
            }
            NodeData::ArrowFunction(_) => {
                return Err(unsupported_outer_context(
                    parent,
                    UnsupportedOuterTypeParameterContext::ArrowFunction,
                ));
            }
            NodeData::TypeAliasDeclaration(data) => data.type_parameters.as_ref(),
            NodeData::MappedTypeNode(_) => {
                return Err(unsupported_outer_context(
                    parent,
                    UnsupportedOuterTypeParameterContext::MappedType,
                ));
            }
            NodeData::ConditionalTypeNode(_) => {
                return Err(unsupported_outer_context(
                    parent,
                    UnsupportedOuterTypeParameterContext::ConditionalType,
                ));
            }
            NodeData::InferTypeNode(_) => {
                return Err(unsupported_outer_context(
                    parent,
                    UnsupportedOuterTypeParameterContext::InferType,
                ));
            }
            _ => {
                current = parent;
                continue;
            }
        };
        inner_to_outer.push(explicit_type_parameter_symbols(
            store, host, parent, parameters, checked,
        )?);
        current = parent;
    }

    let mut result = Vec::new();
    for group in inner_to_outer.into_iter().rev() {
        for symbol in group {
            push_unique(&mut result, symbol);
        }
    }
    Ok(result)
}

fn preflight_class_plan(
    store: &SemanticStore<TypeRecord, TypeMapper>,
    host: &DeclaredTypeHost<'_>,
    symbol: SemanticSymbolId,
) -> Result<ClassPlan, DeclaredTypeError> {
    let record = store
        .symbol(symbol)
        .ok_or_else(|| unavailable(DeclaredTypeUnavailable::SymbolNotOwned(symbol)))?;
    let declarations = record
        .declarations()
        .filter(|declarations| !declarations.is_empty())
        .ok_or_else(|| unavailable(DeclaredTypeUnavailable::MissingDeclarations(symbol)))?
        .to_vec();
    let value_declaration = record
        .value_declaration()
        .ok_or_else(|| unavailable(DeclaredTypeUnavailable::MissingValueDeclaration(symbol)))?;
    if !declarations.contains(&value_declaration) {
        return Err(unavailable(DeclaredTypeUnavailable::MissingOrForeignFacts(
            value_declaration,
        )));
    }

    let value_node = preflight_node(store, host, value_declaration)?;
    if !host.symbol_matches(value_declaration, symbol) {
        return Err(unavailable(
            DeclaredTypeUnavailable::DeclarationSymbolMismatch(value_declaration),
        ));
    }
    if !matches!(
        value_node.data,
        NodeData::ClassDeclaration(_) | NodeData::ClassExpression(_)
    ) {
        return Err(unavailable(
            DeclaredTypeUnavailable::InvalidClassDeclaration(value_declaration),
        ));
    }

    let mut checked = HashSet::new();
    let mut type_parameters =
        collect_outer_type_parameters(store, host, value_declaration, &mut checked)?;
    let outer_type_parameter_count = type_parameters.len();
    let mut saw_class = false;
    for declaration in declarations {
        let node = preflight_node(store, host, declaration)?;
        if !host.symbol_matches(declaration, symbol) {
            return Err(unavailable(
                DeclaredTypeUnavailable::DeclarationSymbolMismatch(declaration),
            ));
        }
        let parameters = match &node.data {
            NodeData::ClassDeclaration(data) => {
                saw_class = true;
                data.type_parameters.as_ref()
            }
            NodeData::ClassExpression(data) => {
                saw_class = true;
                data.type_parameters.as_ref()
            }
            NodeData::InterfaceDeclaration(data) => data.type_parameters.as_ref(),
            NodeData::TypeAliasDeclaration(_) => {
                return Err(unavailable(
                    DeclaredTypeUnavailable::InvalidClassDeclaration(declaration),
                ));
            }
            _ => continue,
        };
        for parameter in
            explicit_type_parameter_symbols(store, host, declaration, parameters, &mut checked)?
        {
            push_unique(&mut type_parameters, parameter);
        }
    }
    if !saw_class {
        return Err(unavailable(
            DeclaredTypeUnavailable::InvalidClassDeclaration(value_declaration),
        ));
    }
    Ok(ClassPlan {
        symbol,
        type_parameters,
        outer_type_parameter_count,
    })
}

fn is_entity_name_expression(
    store: &SemanticStore<TypeRecord, TypeMapper>,
    host: &DeclaredTypeHost<'_>,
    declaration: NodeRef,
    expression: NodeRef,
    visited: &mut HashSet<NodeRef>,
) -> Result<bool, DeclaredTypeError> {
    if !visited.insert(expression) {
        return Err(unavailable(
            DeclaredTypeUnavailable::InvalidInterfaceDeclaration(declaration),
        ));
    }
    let expression_node = preflight_node(store, host, expression)?;
    match &expression_node.data {
        NodeData::Identifier(_) => Ok(true),
        NodeData::PropertyAccessExpression(access) => {
            let left = NodeRef::new(expression.arena, expression.file, access.expression);
            let name = NodeRef::new(expression.arena, expression.file, access.name);
            let left_node = preflight_node(store, host, left)?;
            let name_node = preflight_node(store, host, name)?;
            if left_node.parent != Some(expression.node)
                || name_node.parent != Some(expression.node)
            {
                return Err(unavailable(
                    DeclaredTypeUnavailable::InvalidInterfaceDeclaration(declaration),
                ));
            }
            if !matches!(name_node.data, NodeData::Identifier(_)) {
                return Ok(false);
            }
            is_entity_name_expression(store, host, declaration, left, visited)
        }
        _ => Ok(false),
    }
}

fn interface_requires_this_type(
    store: &SemanticStore<TypeRecord, TypeMapper>,
    host: &DeclaredTypeHost<'_>,
    declarations: &[NodeRef],
) -> Result<bool, DeclaredTypeError> {
    for declaration in declarations {
        let declaration_node = preflight_node(store, host, *declaration)?;
        let NodeData::InterfaceDeclaration(interface) = &declaration_node.data else {
            return Err(unavailable(
                DeclaredTypeUnavailable::InvalidInterfaceDeclaration(*declaration),
            ));
        };
        let contains_this = host
            .bound_file(*declaration)
            .and_then(|bound| bound.contains_this(*declaration))
            .ok_or_else(|| {
                unavailable(DeclaredTypeUnavailable::MissingOrForeignFacts(*declaration))
            })?;
        if contains_this {
            return Ok(true);
        }
        let Some(heritage_clauses) = interface.heritage_clauses.as_ref() else {
            continue;
        };
        for clause in &heritage_clauses.nodes {
            let clause = NodeRef::new(declaration.arena, declaration.file, *clause);
            let clause_node = preflight_node(store, host, clause)?;
            let NodeData::HeritageClause(clause_data) = &clause_node.data else {
                return Err(unavailable(
                    DeclaredTypeUnavailable::InvalidInterfaceDeclaration(*declaration),
                ));
            };
            if clause_node.parent != Some(declaration.node) {
                return Err(unavailable(
                    DeclaredTypeUnavailable::InvalidInterfaceDeclaration(*declaration),
                ));
            }
            if clause_data.token != SyntaxKind::ExtendsKeyword {
                continue;
            }
            for heritage in &clause_data.types.nodes {
                let heritage = NodeRef::new(declaration.arena, declaration.file, *heritage);
                let heritage_node = preflight_node(store, host, heritage)?;
                let NodeData::ExpressionWithTypeArguments(heritage_data) = &heritage_node.data
                else {
                    return Err(unavailable(
                        DeclaredTypeUnavailable::InvalidInterfaceDeclaration(*declaration),
                    ));
                };
                if heritage_node.parent != Some(clause.node) {
                    return Err(unavailable(
                        DeclaredTypeUnavailable::InvalidInterfaceDeclaration(*declaration),
                    ));
                }
                let expression = NodeRef::new(
                    declaration.arena,
                    declaration.file,
                    heritage_data.expression,
                );
                let expression_node = preflight_node(store, host, expression)?;
                if expression_node.parent != Some(heritage.node) {
                    return Err(unavailable(
                        DeclaredTypeUnavailable::InvalidInterfaceDeclaration(*declaration),
                    ));
                }
                if is_entity_name_expression(
                    store,
                    host,
                    *declaration,
                    expression,
                    &mut HashSet::new(),
                )? {
                    return Err(unavailable(
                        DeclaredTypeUnavailable::UnsupportedInterfaceHeritageResolution(expression),
                    ));
                }
            }
            // `GetHeritageClause` returns the first matching clause. Invalid
            // duplicate `extends` clauses after it are outside this query.
            break;
        }
    }
    Ok(false)
}

fn preflight_interface_plan(
    store: &SemanticStore<TypeRecord, TypeMapper>,
    host: &DeclaredTypeHost<'_>,
    symbol: SemanticSymbolId,
) -> Result<InterfacePlan, DeclaredTypeError> {
    let record = store
        .symbol(symbol)
        .ok_or_else(|| unavailable(DeclaredTypeUnavailable::SymbolNotOwned(symbol)))?;
    let declarations = record
        .declarations()
        .filter(|declarations| !declarations.is_empty())
        .ok_or_else(|| unavailable(DeclaredTypeUnavailable::MissingDeclarations(symbol)))?
        .to_vec();

    let mut interface_declarations = Vec::new();
    for declaration in declarations {
        let node = preflight_node(store, host, declaration)?;
        if !host.symbol_matches(declaration, symbol) {
            return Err(unavailable(
                DeclaredTypeUnavailable::DeclarationSymbolMismatch(declaration),
            ));
        }
        match node.data {
            NodeData::InterfaceDeclaration(_) => interface_declarations.push(declaration),
            NodeData::ClassDeclaration(_)
            | NodeData::ClassExpression(_)
            | NodeData::TypeAliasDeclaration(_) => {
                return Err(unavailable(
                    DeclaredTypeUnavailable::InvalidInterfaceDeclaration(declaration),
                ));
            }
            _ => {}
        }
    }
    let first_declaration = interface_declarations.first().copied().ok_or_else(|| {
        unavailable(DeclaredTypeUnavailable::InvalidInterfaceDeclaration(
            record.declarations().expect("nonempty declarations")[0],
        ))
    })?;

    let mut checked = HashSet::new();
    let mut type_parameters =
        collect_outer_type_parameters(store, host, first_declaration, &mut checked)?;
    let outer_type_parameter_count = type_parameters.len();
    for declaration in &interface_declarations {
        let node = preflight_node(store, host, *declaration)?;
        let NodeData::InterfaceDeclaration(interface) = &node.data else {
            unreachable!("interface declarations were collected by payload kind")
        };
        for parameter in explicit_type_parameter_symbols(
            store,
            host,
            *declaration,
            interface.type_parameters.as_ref(),
            &mut checked,
        )? {
            push_unique(&mut type_parameters, parameter);
        }
    }

    let has_this_type = if type_parameters.is_empty() {
        interface_requires_this_type(store, host, &interface_declarations)?
    } else {
        true
    };
    Ok(InterfacePlan {
        symbol,
        type_parameters,
        outer_type_parameter_count,
        has_this_type,
    })
}

fn publish_declared_type(
    store: &mut SemanticStore<TypeRecord, TypeMapper>,
    symbol: SemanticSymbolId,
    declared_type: TypeId,
) {
    let mut links = store
        .declared_type_links(symbol)
        .cloned()
        .unwrap_or_default();
    links.declared_type = Some(declared_type);
    assert!(store.set_declared_type_links(symbol, links));
}

fn execute_type_parameter(
    store: &mut SemanticStore<TypeRecord, TypeMapper>,
    symbol: SemanticSymbolId,
) -> TypeId {
    if let Some(declared_type) = store
        .declared_type_links(symbol)
        .and_then(|links| links.declared_type)
    {
        return declared_type;
    }
    let declared_type = store
        .alloc_type_parameter(Some(symbol))
        .expect("preflighted type-parameter symbol belongs to this store");
    publish_declared_type(store, symbol, declared_type);
    declared_type
}

fn type_list_key(types: &[TypeId]) -> CacheHashKey {
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

fn execute_class_plan(
    store: &mut SemanticStore<TypeRecord, TypeMapper>,
    plan: ClassPlan,
) -> TypeId {
    if let Some(declared_type) = store
        .declared_type_links(plan.symbol)
        .and_then(|links| links.declared_type)
    {
        return declared_type;
    }

    assert!(store.begin_declared_type_initialization(plan.symbol));
    let declared_type = store
        .alloc_interface_type(ObjectFlags::CLASS, Some(plan.symbol))
        .expect("preflighted class symbol belongs to this store");

    // Upstream publishes the recursive class shell before asking for any
    // outer or local declared type-parameter identity.
    publish_declared_type(store, plan.symbol, declared_type);

    initialize_published_origin(
        store,
        declared_type,
        plan.symbol,
        plan.type_parameters,
        plan.outer_type_parameter_count,
    );
    assert!(store.finish_declared_type_initialization(plan.symbol));
    declared_type
}

fn execute_interface_plan(
    store: &mut SemanticStore<TypeRecord, TypeMapper>,
    plan: InterfacePlan,
) -> TypeId {
    if let Some(declared_type) = store
        .declared_type_links(plan.symbol)
        .and_then(|links| links.declared_type)
    {
        return declared_type;
    }

    assert!(store.begin_declared_type_initialization(plan.symbol));
    let declared_type = store
        .alloc_interface_type(ObjectFlags::INTERFACE, Some(plan.symbol))
        .expect("preflighted interface symbol belongs to this store");
    publish_declared_type(store, plan.symbol, declared_type);

    if plan.has_this_type {
        initialize_published_origin(
            store,
            declared_type,
            plan.symbol,
            plan.type_parameters,
            plan.outer_type_parameter_count,
        );
    }
    assert!(store.finish_declared_type_initialization(plan.symbol));
    declared_type
}

fn initialize_published_origin(
    store: &mut SemanticStore<TypeRecord, TypeMapper>,
    declared_type: TypeId,
    symbol: SemanticSymbolId,
    type_parameters: Vec<SemanticSymbolId>,
    outer_type_parameter_count: usize,
) {
    let mut resolved_type_arguments = type_parameters
        .into_iter()
        .map(|symbol| execute_type_parameter(store, symbol))
        .collect::<Vec<_>>();
    let this_type = store
        .alloc_type_parameter(Some(symbol))
        .expect("preflighted class or interface symbol owns its this type");
    let self_instantiation_key = type_list_key(&resolved_type_arguments);
    resolved_type_arguments.push(this_type);
    assert!(store.initialize_interface_type_parameters(
        declared_type,
        resolved_type_arguments,
        outer_type_parameter_count,
        this_type,
        self_instantiation_key,
    ));
}

impl SemanticStore<TypeRecord, TypeMapper> {
    /// Returns the exact declared identity for the installed class/interface/
    /// type-parameter cut.
    ///
    /// Dispatch happens before consulting family-specific caches. An
    /// combined class/interface symbol therefore always takes the class path.
    ///
    /// # Errors
    ///
    /// Returns [`DeclaredTypeError::Unavailable`] before mutation when the
    /// symbol, syntax provenance, or dependency closure cannot produce an
    /// exact identity in this cut.
    ///
    /// # Panics
    ///
    /// Panics on semantic identity-space exhaustion or if a fully preflighted
    /// store invariant changes during the synchronous initialization sequence.
    pub fn get_declared_type_of_symbol(
        &mut self,
        host: &DeclaredTypeHost<'_>,
        symbol: SemanticSymbolId,
    ) -> Result<TypeId, DeclaredTypeError> {
        let flags = self
            .symbol(symbol)
            .ok_or_else(|| unavailable(DeclaredTypeUnavailable::SymbolNotOwned(symbol)))?
            .flags();
        let error_type = self
            .intrinsic_bootstrap()
            .ok_or_else(|| unavailable(DeclaredTypeUnavailable::IntrinsicBootstrapNotInitialized))?
            .error_type;

        if malformed_alias_merge(flags) {
            return Err(unavailable(
                DeclaredTypeUnavailable::AliasMergedWithDeclaredSymbol(symbol),
            ));
        }

        // This is the pinned dispatcher order. Class wins for
        // `Class | Interface`.
        if flags.contains(SymbolFlags::CLASS) {
            if let Some(declared_type) = cached_class_type(self, symbol)? {
                return Ok(declared_type);
            }
            let plan = preflight_class_plan(self, host, symbol)?;
            return Ok(execute_class_plan(self, plan));
        }
        if flags.contains(SymbolFlags::INTERFACE) {
            if let Some(declared_type) = cached_interface_type(self, symbol)? {
                return Ok(declared_type);
            }
            let plan = preflight_interface_plan(self, host, symbol)?;
            return Ok(execute_interface_plan(self, plan));
        }
        if flags.contains(SymbolFlags::TYPE_PARAMETER) {
            if let Some(declared_type) = cached_type_parameter(self, symbol)? {
                return Ok(declared_type);
            }
            preflight_type_parameter_symbol(self, host, symbol, &mut HashSet::new())?;
            return Ok(execute_type_parameter(self, symbol));
        }
        if flags.contains(SymbolFlags::TYPE_ALIAS) {
            return Err(unavailable(
                DeclaredTypeUnavailable::UnsupportedDeclaredType(
                    UnsupportedDeclaredTypeKind::TypeAlias,
                ),
            ));
        }
        if flags.intersects(SymbolFlags::ENUM) {
            return Err(unavailable(
                DeclaredTypeUnavailable::UnsupportedDeclaredType(UnsupportedDeclaredTypeKind::Enum),
            ));
        }
        if flags.contains(SymbolFlags::ENUM_MEMBER) {
            return Err(unavailable(
                DeclaredTypeUnavailable::UnsupportedDeclaredType(
                    UnsupportedDeclaredTypeKind::EnumMember,
                ),
            ));
        }
        if flags.contains(SymbolFlags::ALIAS) {
            return Err(unavailable(
                DeclaredTypeUnavailable::UnsupportedDeclaredType(
                    UnsupportedDeclaredTypeKind::Alias,
                ),
            ));
        }
        Ok(error_type)
    }
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;

    use ts_ast::{NodeArena, NodeData, NodeId};
    use ts_binder::{
        BoundFile, CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts,
        CanonicalSourceLanguage, CheckFlags, EscapedName, SymbolData,
    };
    use ts_parser::{ParseResult, parse_source_file};
    use xxhash_rust::xxh3::xxh3_128;

    use super::*;
    use crate::semantic::links::DeclaredTypeLinks;
    use crate::semantic::{IntrinsicBootstrapOptions, type_records::TypeParameterData};

    type TestStore = SemanticStore<TypeRecord, TypeMapper>;

    struct Fixture {
        parsed: ParseResult,
        file: FileId,
        files: BTreeMap<FileId, BoundFile>,
        store: TestStore,
    }

    fn fixture(source: &str) -> Fixture {
        fixture_with_module_state(source, CanonicalModuleState::Script)
    }

    fn fixture_with_module_state(source: &str, module_state: CanonicalModuleState) -> Fixture {
        let parsed = parse_source_file(source);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(17);
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source("\"/declared.ts\""),
                    CanonicalSourceLanguage::TypeScript,
                    false,
                    module_state,
                ),
            )
            .unwrap();
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
        let (symbols, files) = binder.finish().try_into_parts().unwrap();
        let mut store = TestStore::from_symbol_store(symbols);
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

    fn host<'a>(arena: &'a NodeArena, bound: &'a BoundFile) -> DeclaredTypeHost<'a> {
        DeclaredTypeHost::new([(arena, bound)]).unwrap()
    }

    fn identifier_text(arena: &NodeArena, identifier: NodeId) -> Option<&str> {
        let NodeData::Identifier(identifier) = &arena.get(identifier)?.data else {
            return None;
        };
        Some(&identifier.text)
    }

    fn declaration_name<'a>(arena: &'a NodeArena, node: &Node) -> Option<&'a str> {
        let name = match &node.data {
            NodeData::ClassDeclaration(data) => data.name?,
            NodeData::ClassExpression(data) => data.name?,
            NodeData::FunctionDeclaration(data) => data.name?,
            NodeData::InterfaceDeclaration(data) => data.name,
            NodeData::TypeAliasDeclaration(data) => data.name,
            NodeData::EnumDeclaration(data) => data.name,
            NodeData::EnumMember(data) => data.name,
            NodeData::VariableDeclaration(data) => data.name,
            NodeData::ImportSpecifier(data) => data.name,
            NodeData::TypeParameterDeclaration(data) => data.name,
            _ => return None,
        };
        identifier_text(arena, name)
    }

    fn named_node(fixture: &Fixture, kind: SyntaxKind, name: &str) -> NodeRef {
        let node = fixture
            .parsed
            .arena
            .iter()
            .find_map(|(id, node)| {
                (node.kind == kind && declaration_name(&fixture.parsed.arena, node) == Some(name))
                    .then_some(id)
            })
            .unwrap_or_else(|| panic!("missing {kind:?} named {name}"));
        NodeRef::new(fixture.parsed.arena.id(), fixture.file, node)
    }

    fn node_symbol(fixture: &Fixture, node: NodeRef) -> SemanticSymbolId {
        fixture
            .files
            .get(&fixture.file)
            .unwrap()
            .symbol(node)
            .unwrap()
    }

    fn named_symbol(fixture: &Fixture, kind: SyntaxKind, name: &str) -> SemanticSymbolId {
        node_symbol(fixture, named_node(fixture, kind, name))
    }

    fn interface_data(store: &TestStore, declared_type: TypeId) -> &InterfaceTypeData {
        let TypeData::Interface(data) = store.type_payload(declared_type).unwrap().data() else {
            panic!("expected interface payload")
        };
        data
    }

    fn type_parameter_data(store: &TestStore, type_parameter: TypeId) -> &TypeParameterData {
        let TypeData::TypeParameter(data) = store.type_payload(type_parameter).unwrap().data()
        else {
            panic!("expected type-parameter payload")
        };
        data
    }

    fn type_parameter_names(store: &TestStore, parameters: &[TypeId]) -> Vec<String> {
        parameters
            .iter()
            .map(|parameter| {
                let symbol = store.type_payload(*parameter).unwrap().symbol().unwrap();
                store
                    .symbol(symbol)
                    .unwrap()
                    .name()
                    .as_utf8()
                    .unwrap()
                    .to_owned()
            })
            .collect()
    }

    fn assert_invalid_cached_declared_type_is_atomic(
        store: &mut TestStore,
        symbol: SemanticSymbolId,
        declared_type: TypeId,
    ) {
        let type_count = store.type_len();
        let mapper_count = store.mapper_len();
        let type_alias_count = store.type_alias_len();
        let link_counts = store.checker_link_allocated_lengths();
        let declared_links = store.declared_type_links(symbol).cloned();
        let empty_host =
            DeclaredTypeHost::new(std::iter::empty::<(&NodeArena, &BoundFile)>()).unwrap();

        assert_eq!(
            store.get_declared_type_of_symbol(&empty_host, symbol),
            Err(unavailable(
                DeclaredTypeUnavailable::InvalidCachedDeclaredType {
                    symbol,
                    declared_type,
                }
            ))
        );
        assert_eq!(store.type_len(), type_count);
        assert_eq!(store.mapper_len(), mapper_count);
        assert_eq!(store.type_alias_len(), type_alias_count);
        assert_eq!(store.checker_link_allocated_lengths(), link_counts);
        assert_eq!(store.declared_type_links(symbol), declared_links.as_ref());
    }

    #[test]
    fn zero_generic_class_gets_exact_recursive_this_identity() {
        let mut fixture = fixture("class Plain {}");
        let class_symbol = named_symbol(&fixture, SyntaxKind::ClassDeclaration, "Plain");
        let bound = fixture.files.get(&fixture.file).unwrap();
        let host = host(&fixture.parsed.arena, bound);
        let type_count = fixture.store.type_len();

        let declared_type = fixture
            .store
            .get_declared_type_of_symbol(&host, class_symbol)
            .unwrap();
        assert_eq!(fixture.store.type_len(), type_count + 2);
        let record = fixture.store.type_payload(declared_type).unwrap();
        assert_eq!(record.flags(), TypeFlags::OBJECT);
        assert_eq!(
            record.object_flags(),
            ObjectFlags::CLASS | ObjectFlags::REFERENCE
        );
        assert_eq!(record.symbol(), Some(class_symbol));

        let data = interface_data(&fixture.store, declared_type);
        let all_type_parameters = data.all_type_parameters.as_deref().unwrap();
        assert_eq!(all_type_parameters.len(), 1);
        let this_type = all_type_parameters[0];
        assert_eq!(data.this_type, Some(this_type));
        assert_eq!(data.outer_type_parameter_count, 0);
        assert_eq!(data.reference.object.target, Some(declared_type));
        assert_eq!(data.reference.resolved_type_arguments, Some(Vec::new()));
        let TypeCacheState::Allocated(instantiations) = &data.reference.object.instantiations
        else {
            panic!("class instantiation cache must be allocated")
        };
        assert_eq!(instantiations.len(), 1);
        assert_eq!(
            instantiations.get(&type_list_key(&[])),
            Some(&declared_type)
        );

        let this_data = type_parameter_data(&fixture.store, this_type);
        assert!(this_data.is_this_type);
        assert_eq!(this_data.constraint, Some(declared_type));
        assert_eq!(
            fixture.store.type_payload(this_type).unwrap().symbol(),
            Some(class_symbol)
        );

        let link_counts = fixture.store.checker_link_allocated_lengths();
        let repeat_type_count = fixture.store.type_len();
        assert_eq!(
            fixture
                .store
                .get_declared_type_of_symbol(&host, class_symbol),
            Ok(declared_type)
        );
        assert_eq!(fixture.store.type_len(), repeat_type_count);
        assert_eq!(fixture.store.checker_link_allocated_lengths(), link_counts);
    }

    #[test]
    fn cached_class_accepts_exact_lazy_type_parameter_flags_and_rejects_extra_flags() {
        let mut fixture = fixture("class Cached<T> {}");
        let class = named_symbol(&fixture, SyntaxKind::ClassDeclaration, "Cached");
        let bound = fixture.files.get(&fixture.file).unwrap();
        let host = host(&fixture.parsed.arena, bound);
        let declared_type = fixture
            .store
            .get_declared_type_of_symbol(&host, class)
            .unwrap();
        let data = interface_data(&fixture.store, declared_type);
        let argument = data.reference.resolved_type_arguments.as_ref().unwrap()[0];
        let this_type = data.this_type.unwrap();
        let lazy_flags = ObjectFlags::COULD_CONTAIN_TYPE_VARIABLES_COMPUTED
            | ObjectFlags::COULD_CONTAIN_TYPE_VARIABLES;
        assert!(fixture.store.add_type_object_flags(argument, lazy_flags));
        assert!(fixture.store.add_type_object_flags(this_type, lazy_flags));
        let type_count = fixture.store.type_len();
        let link_counts = fixture.store.checker_link_allocated_lengths();

        assert_eq!(
            fixture.store.get_declared_type_of_symbol(&host, class),
            Ok(declared_type)
        );
        assert_eq!(fixture.store.type_len(), type_count);
        assert_eq!(fixture.store.checker_link_allocated_lengths(), link_counts);

        assert!(
            fixture
                .store
                .add_type_object_flags(argument, ObjectFlags::NON_INFERRABLE_TYPE)
        );
        assert_invalid_cached_declared_type_is_atomic(&mut fixture.store, class, declared_type);
    }

    #[test]
    fn exported_class_uses_export_identity_and_ignores_local_placeholder() {
        let mut fixture = fixture_with_module_state(
            "export class Exported<T> {}",
            CanonicalModuleState::External,
        );
        let class_declaration = named_node(&fixture, SyntaxKind::ClassDeclaration, "Exported");
        let parameter = named_symbol(&fixture, SyntaxKind::TypeParameter, "T");
        let bound = fixture.files.get(&fixture.file).unwrap();
        let export = bound.symbol(class_declaration).unwrap();
        let local = bound.local_symbol(class_declaration).unwrap();

        assert_ne!(local, export);
        let local_record = fixture.store.symbol(local).unwrap();
        assert_eq!(local_record.flags(), SymbolFlags::EXPORT_VALUE);
        assert_eq!(local_record.export_symbol(), Some(export));
        assert_eq!(
            fixture.store.symbol(export).unwrap().flags(),
            SymbolFlags::CLASS
        );
        assert!(fixture.store.declared_type_links(export).is_none());
        assert!(fixture.store.declared_type_links(local).is_none());

        let host = host(&fixture.parsed.arena, bound);
        let declared_type = fixture
            .store
            .get_declared_type_of_symbol(&host, export)
            .unwrap();
        let arguments = interface_data(&fixture.store, declared_type)
            .reference
            .resolved_type_arguments
            .as_deref()
            .unwrap();
        assert_eq!(arguments.len(), 1);
        assert_eq!(
            fixture.store.type_payload(declared_type).unwrap().symbol(),
            Some(export)
        );
        assert_eq!(
            fixture.store.type_payload(arguments[0]).unwrap().symbol(),
            Some(parameter)
        );
        assert_eq!(
            fixture
                .store
                .declared_type_links(export)
                .and_then(|links| links.declared_type),
            Some(declared_type)
        );
        assert_eq!(
            fixture
                .store
                .declared_type_links(parameter)
                .and_then(|links| links.declared_type),
            Some(arguments[0])
        );
        assert!(fixture.store.declared_type_links(local).is_none());
        let error_type = fixture.store.intrinsic_bootstrap().unwrap().error_type;
        assert_eq!(
            fixture.store.get_declared_type_of_symbol(&host, local),
            Ok(error_type)
        );
        assert!(fixture.store.declared_type_links(local).is_none());
    }

    #[test]
    fn nested_generic_class_orders_outermost_to_inner_then_local_and_this() {
        let mut fixture =
            fixture("function outer<A>() { class Mid<B> { method<C>() { class Inner<D> {} } } }");
        let inner = named_symbol(&fixture, SyntaxKind::ClassDeclaration, "Inner");
        let bound = fixture.files.get(&fixture.file).unwrap();
        let host = host(&fixture.parsed.arena, bound);

        let declared_type = fixture
            .store
            .get_declared_type_of_symbol(&host, inner)
            .unwrap();
        let data = interface_data(&fixture.store, declared_type);
        let arguments = data.reference.resolved_type_arguments.as_deref().unwrap();
        assert_eq!(
            type_parameter_names(&fixture.store, arguments),
            ["A", "B", "C", "D"]
        );
        assert_eq!(data.outer_type_parameter_count, 3);
        let all = data.all_type_parameters.as_deref().unwrap();
        assert_eq!(&all[..4], arguments);
        assert_eq!(all.last().copied(), data.this_type);
        assert_eq!(data.reference.object.target, Some(declared_type));

        let mut encoded = u64::try_from(arguments.len())
            .unwrap()
            .to_le_bytes()
            .to_vec();
        for argument in arguments {
            encoded.extend_from_slice(&argument.get().to_le_bytes());
        }
        assert_eq!(
            type_list_key(arguments),
            CacheHashKey::new(xxh3_128(&encoded))
        );
        let TypeCacheState::Allocated(instantiations) = &data.reference.object.instantiations
        else {
            panic!("class instantiation cache must be allocated")
        };
        assert_eq!(
            instantiations.get(&type_list_key(arguments)),
            Some(&declared_type)
        );
    }

    #[test]
    fn class_interface_merge_dispatches_as_class_and_preserves_identity_dedupe() {
        let mut fixture = fixture("class M<T> {} interface M<T, U> {}");
        let class_node = named_node(&fixture, SyntaxKind::ClassDeclaration, "M");
        let interface_node = named_node(&fixture, SyntaxKind::InterfaceDeclaration, "M");
        let symbol = node_symbol(&fixture, class_node);
        assert_eq!(node_symbol(&fixture, interface_node), symbol);
        let flags = fixture.store.symbol(symbol).unwrap().flags();
        assert!(flags.contains(SymbolFlags::CLASS));
        assert!(flags.contains(SymbolFlags::INTERFACE));
        let bound = fixture.files.get(&fixture.file).unwrap();
        let host = host(&fixture.parsed.arena, bound);

        let declared_type = fixture
            .store
            .get_declared_type_of_symbol(&host, symbol)
            .unwrap();
        let arguments = interface_data(&fixture.store, declared_type)
            .reference
            .resolved_type_arguments
            .as_deref()
            .unwrap();
        assert_eq!(arguments.len(), 2);
        assert_ne!(arguments[0], arguments[1]);
        assert_eq!(type_parameter_names(&fixture.store, arguments), ["T", "U"]);

        let parameter_symbols = arguments
            .iter()
            .map(|parameter| {
                fixture
                    .store
                    .type_payload(*parameter)
                    .unwrap()
                    .symbol()
                    .unwrap()
            })
            .collect::<Vec<_>>();
        let mut deduped = Vec::new();
        push_unique(&mut deduped, parameter_symbols[0]);
        push_unique(&mut deduped, parameter_symbols[0]);
        push_unique(&mut deduped, parameter_symbols[1]);
        assert_eq!(deduped, parameter_symbols);
    }

    #[test]
    fn type_parameter_is_allocated_and_cached_exactly_once() {
        let mut fixture = fixture("class Box<T> {}");
        let parameter = named_symbol(&fixture, SyntaxKind::TypeParameter, "T");
        let class = named_symbol(&fixture, SyntaxKind::ClassDeclaration, "Box");
        let bound = fixture.files.get(&fixture.file).unwrap();
        let host = host(&fixture.parsed.arena, bound);
        let before = fixture.store.type_len();

        let parameter_type = fixture
            .store
            .get_declared_type_of_symbol(&host, parameter)
            .unwrap();
        assert_eq!(fixture.store.type_len(), before + 1);
        let links = fixture.store.checker_link_allocated_lengths();
        assert_eq!(
            fixture.store.get_declared_type_of_symbol(&host, parameter),
            Ok(parameter_type)
        );
        assert_eq!(fixture.store.type_len(), before + 1);
        assert_eq!(fixture.store.checker_link_allocated_lengths(), links);

        let class_type = fixture
            .store
            .get_declared_type_of_symbol(&host, class)
            .unwrap();
        assert_eq!(fixture.store.type_len(), before + 3);
        assert_eq!(
            interface_data(&fixture.store, class_type)
                .reference
                .resolved_type_arguments,
            Some(vec![parameter_type])
        );
    }

    #[test]
    fn class_expression_value_declaration_contributes_local_parameters() {
        let mut fixture = fixture("const value = class Expression<T> {};");
        let class = named_symbol(&fixture, SyntaxKind::ClassExpression, "Expression");
        let bound = fixture.files.get(&fixture.file).unwrap();
        let host = host(&fixture.parsed.arena, bound);

        let declared_type = fixture
            .store
            .get_declared_type_of_symbol(&host, class)
            .unwrap();
        let data = interface_data(&fixture.store, declared_type);
        let arguments = data.reference.resolved_type_arguments.as_deref().unwrap();
        assert_eq!(type_parameter_names(&fixture.store, arguments), ["T"]);
        let this_type = data.this_type.unwrap();
        assert_eq!(
            fixture.store.type_payload(this_type).unwrap().symbol(),
            Some(class)
        );
    }

    #[test]
    fn thisless_interface_stays_a_plain_interface_identity() {
        let mut fixture = fixture("interface Plain { value: string }");
        let interface = named_symbol(&fixture, SyntaxKind::InterfaceDeclaration, "Plain");
        let bound = fixture.files.get(&fixture.file).unwrap();
        let declaration = named_node(&fixture, SyntaxKind::InterfaceDeclaration, "Plain");
        assert_eq!(bound.contains_this(declaration), Some(false));
        let host = host(&fixture.parsed.arena, bound);
        let type_count = fixture.store.type_len();

        let declared_type = fixture
            .store
            .get_declared_type_of_symbol(&host, interface)
            .unwrap();
        assert_eq!(fixture.store.type_len(), type_count + 1);
        let record = fixture.store.type_payload(declared_type).unwrap();
        assert_eq!(record.flags(), TypeFlags::OBJECT);
        assert_eq!(record.object_flags(), ObjectFlags::INTERFACE);
        assert_eq!(record.symbol(), Some(interface));
        let data = interface_data(&fixture.store, declared_type);
        assert!(data.all_type_parameters.is_none());
        assert_eq!(data.outer_type_parameter_count, 0);
        assert!(data.this_type.is_none());
        assert!(data.reference.object.target.is_none());
        assert_eq!(
            data.reference.object.instantiations,
            TypeCacheState::Unallocated
        );
        assert!(data.reference.resolved_type_arguments.is_none());

        let empty_host =
            DeclaredTypeHost::new(std::iter::empty::<(&NodeArena, &BoundFile)>()).unwrap();
        let repeat_type_count = fixture.store.type_len();
        let link_counts = fixture.store.checker_link_allocated_lengths();
        assert_eq!(
            fixture
                .store
                .get_declared_type_of_symbol(&empty_host, interface),
            Ok(declared_type)
        );
        assert_eq!(fixture.store.type_len(), repeat_type_count);
        assert_eq!(fixture.store.checker_link_allocated_lengths(), link_counts);
    }

    #[test]
    fn direct_and_signature_this_make_nongeneric_interfaces_references() {
        for (source, name) in [
            ("interface Direct { value: this }", "Direct"),
            ("interface Signature { (): this }", "Signature"),
        ] {
            let mut fixture = fixture(source);
            let declaration = named_node(&fixture, SyntaxKind::InterfaceDeclaration, name);
            let interface = node_symbol(&fixture, declaration);
            let bound = fixture.files.get(&fixture.file).unwrap();
            assert_eq!(bound.contains_this(declaration), Some(true));
            let host = host(&fixture.parsed.arena, bound);
            let type_count = fixture.store.type_len();

            let declared_type = fixture
                .store
                .get_declared_type_of_symbol(&host, interface)
                .unwrap();
            assert_eq!(fixture.store.type_len(), type_count + 2);
            let record = fixture.store.type_payload(declared_type).unwrap();
            assert_eq!(
                record.object_flags(),
                ObjectFlags::INTERFACE | ObjectFlags::REFERENCE
            );
            let data = interface_data(&fixture.store, declared_type);
            assert_eq!(data.reference.resolved_type_arguments, Some(Vec::new()));
            assert_eq!(data.reference.object.target, Some(declared_type));
            let this_type = data.this_type.unwrap();
            assert_eq!(data.all_type_parameters, Some(vec![this_type]));
            let this_record = fixture.store.type_payload(this_type).unwrap();
            assert_eq!(this_record.symbol(), Some(interface));
            let this_data = type_parameter_data(&fixture.store, this_type);
            assert!(this_data.is_this_type);
            assert_eq!(this_data.constraint, Some(declared_type));
            let TypeCacheState::Allocated(instantiations) = &data.reference.object.instantiations
            else {
                panic!("interface instantiation cache must be allocated")
            };
            assert_eq!(instantiations.len(), 1);
            assert_eq!(
                instantiations.get(&type_list_key(&[])),
                Some(&declared_type)
            );
        }
    }

    #[test]
    fn merged_generic_interface_orders_outer_then_identity_unique_locals() {
        let mut fixture = fixture("function outer<A>() { interface M<B> {} interface M<B, C> {} }");
        let interface = named_symbol(&fixture, SyntaxKind::InterfaceDeclaration, "M");
        let bound = fixture.files.get(&fixture.file).unwrap();
        let host = host(&fixture.parsed.arena, bound);

        let declared_type = fixture
            .store
            .get_declared_type_of_symbol(&host, interface)
            .unwrap();
        let data = interface_data(&fixture.store, declared_type);
        let arguments = data.reference.resolved_type_arguments.as_deref().unwrap();
        assert_eq!(
            type_parameter_names(&fixture.store, arguments),
            ["A", "B", "C"]
        );
        assert_eq!(data.outer_type_parameter_count, 1);
        assert_eq!(data.all_type_parameters.as_ref().unwrap().len(), 4);
        assert_eq!(data.reference.object.target, Some(declared_type));

        let local_b_symbols = fixture
            .parsed
            .arena
            .iter()
            .filter(|(_, node)| {
                node.kind == SyntaxKind::TypeParameter
                    && declaration_name(&fixture.parsed.arena, node) == Some("B")
            })
            .map(|(id, _)| {
                node_symbol(
                    &fixture,
                    NodeRef::new(fixture.parsed.arena.id(), fixture.file, id),
                )
            })
            .collect::<Vec<_>>();
        assert_eq!(local_b_symbols.len(), 2);
        assert_eq!(local_b_symbols[0], local_b_symbols[1]);
    }

    #[test]
    fn generic_interface_short_circuits_entity_heritage_resolution() {
        let mut fixture = fixture("interface Base {} interface Generic<T> extends Base {}");
        let interface = named_symbol(&fixture, SyntaxKind::InterfaceDeclaration, "Generic");
        let declaration = named_node(&fixture, SyntaxKind::InterfaceDeclaration, "Generic");
        let bound = fixture.files.get(&fixture.file).unwrap();
        assert_eq!(bound.contains_this(declaration), Some(false));
        let host = host(&fixture.parsed.arena, bound);

        let declared_type = fixture
            .store
            .get_declared_type_of_symbol(&host, interface)
            .unwrap();
        let data = interface_data(&fixture.store, declared_type);
        assert_eq!(
            type_parameter_names(
                &fixture.store,
                data.reference.resolved_type_arguments.as_deref().unwrap()
            ),
            ["T"]
        );
        assert!(data.this_type.is_some());
    }

    #[test]
    fn entity_name_heritage_is_unavailable_before_checker_writes() {
        let mut fixture = fixture("interface Base {} interface Derived extends Base {}");
        let derived = named_symbol(&fixture, SyntaxKind::InterfaceDeclaration, "Derived");
        let type_count = fixture.store.type_len();
        let mapper_count = fixture.store.mapper_len();
        let link_counts = fixture.store.checker_link_allocated_lengths();
        let bound = fixture.files.get(&fixture.file).unwrap();
        let host = host(&fixture.parsed.arena, bound);

        assert!(matches!(
            fixture.store.get_declared_type_of_symbol(&host, derived),
            Err(DeclaredTypeError::Unavailable(
                DeclaredTypeUnavailable::UnsupportedInterfaceHeritageResolution(_)
            ))
        ));
        assert_eq!(fixture.store.type_len(), type_count);
        assert_eq!(fixture.store.mapper_len(), mapper_count);
        assert_eq!(fixture.store.checker_link_allocated_lengths(), link_counts);
        assert!(fixture.store.declared_type_links(derived).is_none());
    }

    #[test]
    fn thisless_scan_preserves_declaration_order_around_heritage() {
        let mut blocked = fixture(
            "interface Base {} interface Ordered extends Base {} interface Ordered { value: this }",
        );
        let ordered = named_symbol(&blocked, SyntaxKind::InterfaceDeclaration, "Ordered");
        let bound = blocked.files.get(&blocked.file).unwrap();
        let blocked_host = host(&blocked.parsed.arena, bound);
        assert!(matches!(
            blocked
                .store
                .get_declared_type_of_symbol(&blocked_host, ordered),
            Err(DeclaredTypeError::Unavailable(
                DeclaredTypeUnavailable::UnsupportedInterfaceHeritageResolution(_)
            ))
        ));

        let mut short_circuited = fixture(
            "interface Base {} interface Ordered { value: this } interface Ordered extends Base {}",
        );
        let ordered = named_symbol(
            &short_circuited,
            SyntaxKind::InterfaceDeclaration,
            "Ordered",
        );
        let bound = short_circuited.files.get(&short_circuited.file).unwrap();
        let host = host(&short_circuited.parsed.arena, bound);
        let declared_type = short_circuited
            .store
            .get_declared_type_of_symbol(&host, ordered)
            .unwrap();
        assert!(
            short_circuited
                .store
                .type_payload(declared_type)
                .unwrap()
                .object_flags()
                .contains(ObjectFlags::REFERENCE)
        );
    }

    #[test]
    fn non_entity_interface_heritage_is_ignored_by_thisless_analysis() {
        let mut fixture =
            fixture("declare function make(): object; interface Invalid extends make() {}");
        let interface = named_symbol(&fixture, SyntaxKind::InterfaceDeclaration, "Invalid");
        let bound = fixture.files.get(&fixture.file).unwrap();
        let host = host(&fixture.parsed.arena, bound);

        let declared_type = fixture
            .store
            .get_declared_type_of_symbol(&host, interface)
            .unwrap();
        assert_eq!(
            fixture
                .store
                .type_payload(declared_type)
                .unwrap()
                .object_flags(),
            ObjectFlags::INTERFACE
        );
    }

    #[test]
    fn exported_interface_uses_the_canonical_export_owner() {
        let mut fixture = fixture_with_module_state(
            "export interface Exported<T> { current: this }",
            CanonicalModuleState::External,
        );
        let declaration = named_node(&fixture, SyntaxKind::InterfaceDeclaration, "Exported");
        let parameter = named_symbol(&fixture, SyntaxKind::TypeParameter, "T");
        let bound = fixture.files.get(&fixture.file).unwrap();
        let export = bound.symbol(declaration).unwrap();
        let local = bound.local_symbol(declaration).unwrap();
        assert_ne!(export, local);
        let local_record = fixture.store.symbol(local).unwrap();
        assert_eq!(local_record.flags(), SymbolFlags::NONE);
        assert!(!local_record.flags().intersects(SymbolFlags::TYPE));
        assert_eq!(local_record.export_symbol(), Some(export));
        assert!(
            fixture
                .store
                .symbol(export)
                .unwrap()
                .flags()
                .contains(SymbolFlags::INTERFACE)
        );
        let host = host(&fixture.parsed.arena, bound);

        let declared_type = fixture
            .store
            .get_declared_type_of_symbol(&host, export)
            .unwrap();
        let data = interface_data(&fixture.store, declared_type);
        let arguments = data.reference.resolved_type_arguments.as_deref().unwrap();
        assert_eq!(arguments.len(), 1);
        assert_eq!(
            fixture.store.type_payload(declared_type).unwrap().symbol(),
            Some(export)
        );
        assert_eq!(
            fixture.store.type_payload(arguments[0]).unwrap().symbol(),
            Some(parameter)
        );
        assert_eq!(
            fixture
                .store
                .type_payload(data.this_type.unwrap())
                .unwrap()
                .symbol(),
            Some(export)
        );
        assert_eq!(
            fixture
                .store
                .declared_type_links(export)
                .and_then(|links| links.declared_type),
            Some(declared_type)
        );
        assert!(fixture.store.declared_type_links(local).is_none());
        let error_type = fixture.store.intrinsic_bootstrap().unwrap().error_type;
        assert_eq!(
            fixture.store.get_declared_type_of_symbol(&host, local),
            Ok(error_type)
        );
        assert!(fixture.store.declared_type_links(local).is_none());
    }

    #[test]
    fn cached_interface_rejects_the_wrong_origin_atomically() {
        let mut fixture = fixture("interface Wrong {}");
        let interface = named_symbol(&fixture, SyntaxKind::InterfaceDeclaration, "Wrong");
        let wrong_origin = fixture
            .store
            .alloc_interface_type(ObjectFlags::CLASS, Some(interface))
            .unwrap();
        publish_declared_type(&mut fixture.store, interface, wrong_origin);

        assert_invalid_cached_declared_type_is_atomic(&mut fixture.store, interface, wrong_origin);
    }

    #[test]
    fn dispatcher_keeps_unsupported_families_unavailable_and_values_on_error_type() {
        let mut fixture = fixture_with_module_state(
            "import { remote as local } from 'm'; type A = string; enum E { M } const value = 1;",
            CanonicalModuleState::External,
        );
        let alias = named_symbol(&fixture, SyntaxKind::TypeAliasDeclaration, "A");
        let enum_symbol = named_symbol(&fixture, SyntaxKind::EnumDeclaration, "E");
        let member = named_symbol(&fixture, SyntaxKind::EnumMember, "M");
        let import = named_symbol(&fixture, SyntaxKind::ImportSpecifier, "local");
        let value = named_symbol(&fixture, SyntaxKind::VariableDeclaration, "value");
        let error_type = fixture.store.intrinsic_bootstrap().unwrap().error_type;
        let bound = fixture.files.get(&fixture.file).unwrap();
        let host = host(&fixture.parsed.arena, bound);
        let type_count = fixture.store.type_len();
        let link_counts = fixture.store.checker_link_allocated_lengths();

        for (symbol, kind) in [
            (alias, UnsupportedDeclaredTypeKind::TypeAlias),
            (enum_symbol, UnsupportedDeclaredTypeKind::Enum),
            (member, UnsupportedDeclaredTypeKind::EnumMember),
            (import, UnsupportedDeclaredTypeKind::Alias),
        ] {
            assert_eq!(
                fixture.store.get_declared_type_of_symbol(&host, symbol),
                Err(unavailable(
                    DeclaredTypeUnavailable::UnsupportedDeclaredType(kind)
                ))
            );
        }
        assert_eq!(
            fixture.store.get_declared_type_of_symbol(&host, value),
            Ok(error_type)
        );
        assert_eq!(fixture.store.type_len(), type_count);
        assert_eq!(fixture.store.checker_link_allocated_lengths(), link_counts);
    }

    #[test]
    fn cross_store_missing_host_and_alias_merge_fail_atomically() {
        let mut local = fixture("class Local<T> {}");
        let foreign = fixture("class Foreign<U> {}");
        let local_symbol = named_symbol(&local, SyntaxKind::ClassDeclaration, "Local");
        let foreign_symbol = named_symbol(&foreign, SyntaxKind::ClassDeclaration, "Foreign");
        let foreign_bound = foreign.files.get(&foreign.file).unwrap();
        let foreign_host = host(&foreign.parsed.arena, foreign_bound);
        let type_count = local.store.type_len();
        let link_counts = local.store.checker_link_allocated_lengths();

        assert_eq!(
            local
                .store
                .get_declared_type_of_symbol(&foreign_host, foreign_symbol),
            Err(unavailable(DeclaredTypeUnavailable::SymbolNotOwned(
                foreign_symbol
            )))
        );
        assert!(matches!(
            local
                .store
                .get_declared_type_of_symbol(&foreign_host, local_symbol),
            Err(DeclaredTypeError::Unavailable(
                DeclaredTypeUnavailable::MissingOrForeignFacts(_)
            ))
        ));
        let empty_host =
            DeclaredTypeHost::new(std::iter::empty::<(&NodeArena, &BoundFile)>()).unwrap();
        assert!(matches!(
            local
                .store
                .get_declared_type_of_symbol(&empty_host, local_symbol),
            Err(DeclaredTypeError::Unavailable(
                DeclaredTypeUnavailable::MissingOrForeignFacts(_)
            ))
        ));

        let malformed = local
            .store
            .alloc_symbol(SymbolData::new(
                SymbolFlags::CLASS | SymbolFlags::ALIAS,
                EscapedName::source("Malformed"),
            ))
            .unwrap();
        assert_eq!(
            local
                .store
                .get_declared_type_of_symbol(&empty_host, malformed),
            Err(unavailable(
                DeclaredTypeUnavailable::AliasMergedWithDeclaredSymbol(malformed)
            ))
        );
        assert_eq!(local.store.type_len(), type_count);
        assert_eq!(local.store.checker_link_allocated_lengths(), link_counts);
    }

    #[test]
    fn dynamic_outer_parameter_sources_fail_before_any_checker_write() {
        for (source, context) in [
            (
                "const make = <T>() => { class C<U> {} };",
                UnsupportedOuterTypeParameterContext::ArrowFunction,
            ),
            (
                "const make = function<T>() { class C<U> {} };",
                UnsupportedOuterTypeParameterContext::FunctionExpression,
            ),
            (
                "const object = { method<T>() { class C<U> {} } };",
                UnsupportedOuterTypeParameterContext::ObjectLiteralMethod,
            ),
        ] {
            let mut fixture = fixture(source);
            let class = named_symbol(&fixture, SyntaxKind::ClassDeclaration, "C");
            let bound = fixture.files.get(&fixture.file).unwrap();
            let host = host(&fixture.parsed.arena, bound);
            let type_count = fixture.store.type_len();
            let link_counts = fixture.store.checker_link_allocated_lengths();
            assert!(matches!(
                fixture.store.get_declared_type_of_symbol(&host, class),
                Err(DeclaredTypeError::Unavailable(
                    DeclaredTypeUnavailable::UnsupportedOuterTypeParameterContext {
                        context: actual,
                        ..
                    }
                )) if actual == context
            ));
            assert_eq!(fixture.store.type_len(), type_count);
            assert_eq!(fixture.store.checker_link_allocated_lengths(), link_counts);
        }
    }

    #[test]
    fn non_class_value_declaration_is_rejected_before_any_checker_write() {
        let mut fixture = fixture("function Wrong<T>() {}");
        let function = named_symbol(&fixture, SyntaxKind::FunctionDeclaration, "Wrong");
        let function_declaration = named_node(&fixture, SyntaxKind::FunctionDeclaration, "Wrong");
        assert!(
            fixture
                .store
                .set_symbol_flags(function, SymbolFlags::CLASS, CheckFlags::NONE,)
        );
        let bound = fixture.files.get(&fixture.file).unwrap();
        let host = host(&fixture.parsed.arena, bound);
        let type_count = fixture.store.type_len();
        let link_counts = fixture.store.checker_link_allocated_lengths();

        assert_eq!(
            fixture.store.get_declared_type_of_symbol(&host, function),
            Err(unavailable(
                DeclaredTypeUnavailable::InvalidClassDeclaration(function_declaration)
            ))
        );
        assert_eq!(fixture.store.type_len(), type_count);
        assert_eq!(fixture.store.checker_link_allocated_lengths(), link_counts);
    }

    #[test]
    fn mapped_conditional_and_infer_outer_sources_are_explicitly_unavailable() {
        let cases = [
            (
                "type M<K> = { [P in K]: P };",
                SyntaxKind::TypeParameter,
                Some("P"),
                UnsupportedOuterTypeParameterContext::MappedType,
            ),
            (
                "type C<T> = T extends infer U ? U : never;",
                SyntaxKind::TypeParameter,
                Some("U"),
                UnsupportedOuterTypeParameterContext::InferType,
            ),
            (
                "type C<T> = T extends string ? T : never;",
                SyntaxKind::ConditionalType,
                None,
                UnsupportedOuterTypeParameterContext::ConditionalType,
            ),
        ];
        for (source, start_kind, start_name, expected) in cases {
            let fixture = fixture(source);
            let start = if let Some(name) = start_name {
                named_node(&fixture, start_kind, name)
            } else {
                let conditional = fixture
                    .parsed
                    .arena
                    .iter()
                    .find_map(|(id, node)| (node.kind == start_kind).then_some(id))
                    .unwrap();
                let NodeData::ConditionalTypeNode(conditional) =
                    &fixture.parsed.arena.get(conditional).unwrap().data
                else {
                    panic!("expected conditional type")
                };
                NodeRef::new(
                    fixture.parsed.arena.id(),
                    fixture.file,
                    conditional.true_type,
                )
            };
            let bound = fixture.files.get(&fixture.file).unwrap();
            let host = host(&fixture.parsed.arena, bound);
            let type_count = fixture.store.type_len();
            let link_counts = fixture.store.checker_link_allocated_lengths();
            assert!(matches!(
                collect_outer_type_parameters(
                    &fixture.store,
                    &host,
                    start,
                    &mut HashSet::new(),
                ),
                Err(DeclaredTypeError::Unavailable(
                    DeclaredTypeUnavailable::UnsupportedOuterTypeParameterContext {
                        context: actual,
                        ..
                    }
                )) if actual == expected
            ));
            assert_eq!(fixture.store.type_len(), type_count);
            assert_eq!(fixture.store.checker_link_allocated_lengths(), link_counts);
        }
    }

    #[test]
    fn cached_class_rejects_argument_owned_by_class_symbol_atomically() {
        let mut fixture = fixture("class Corrupt<T> {}");
        let class = named_symbol(&fixture, SyntaxKind::ClassDeclaration, "Corrupt");
        let origin = fixture
            .store
            .alloc_interface_type(ObjectFlags::CLASS, Some(class))
            .unwrap();
        let malformed_argument = fixture.store.alloc_type_parameter(Some(class)).unwrap();
        let this_type = fixture.store.alloc_type_parameter(Some(class)).unwrap();
        assert!(fixture.store.initialize_interface_type_parameters(
            origin,
            vec![malformed_argument, this_type],
            0,
            this_type,
            type_list_key(&[malformed_argument]),
        ));
        assert!(fixture.store.set_declared_type_links(
            class,
            DeclaredTypeLinks {
                declared_type: Some(origin),
                ..DeclaredTypeLinks::default()
            },
        ));

        assert_invalid_cached_declared_type_is_atomic(&mut fixture.store, class, origin);
    }

    #[test]
    fn cached_class_rejects_duplicate_ordinary_type_parameter_prefix() {
        let mut fixture = fixture("class Duplicate<A, B> {}");
        let class = named_symbol(&fixture, SyntaxKind::ClassDeclaration, "Duplicate");
        let parameter = named_symbol(&fixture, SyntaxKind::TypeParameter, "A");
        let argument = fixture.store.alloc_type_parameter(Some(parameter)).unwrap();
        assert!(fixture.store.set_declared_type_links(
            parameter,
            DeclaredTypeLinks {
                declared_type: Some(argument),
                ..DeclaredTypeLinks::default()
            },
        ));
        let origin = fixture
            .store
            .alloc_interface_type(ObjectFlags::CLASS, Some(class))
            .unwrap();
        let this_type = fixture.store.alloc_type_parameter(Some(class)).unwrap();
        assert!(fixture.store.initialize_interface_type_parameters(
            origin,
            vec![argument, argument, this_type],
            0,
            this_type,
            type_list_key(&[argument, argument]),
        ));
        assert!(fixture.store.set_declared_type_links(
            class,
            DeclaredTypeLinks {
                declared_type: Some(origin),
                ..DeclaredTypeLinks::default()
            },
        ));

        assert_invalid_cached_declared_type_is_atomic(&mut fixture.store, class, origin);
    }

    #[test]
    fn cached_ordinary_type_parameter_rejects_published_clone() {
        let mut fixture = fixture("class Cloned<T> {}");
        let class = named_symbol(&fixture, SyntaxKind::ClassDeclaration, "Cloned");
        let parameter = named_symbol(&fixture, SyntaxKind::TypeParameter, "T");
        let target = fixture.store.alloc_type_parameter(Some(parameter)).unwrap();
        let clone = fixture.store.alloc_type_parameter(Some(parameter)).unwrap();
        let mapper = fixture
            .store
            .new_simple_type_mapper(target, target)
            .unwrap();
        assert!(fixture.store.set_type_parameter_resolution(
            clone,
            None,
            Some(target),
            Some(mapper),
            None,
        ));
        assert!(fixture.store.set_declared_type_links(
            parameter,
            DeclaredTypeLinks {
                declared_type: Some(clone),
                ..DeclaredTypeLinks::default()
            },
        ));
        let origin = fixture
            .store
            .alloc_interface_type(ObjectFlags::CLASS, Some(class))
            .unwrap();
        let this_type = fixture.store.alloc_type_parameter(Some(class)).unwrap();
        assert!(fixture.store.initialize_interface_type_parameters(
            origin,
            vec![clone, this_type],
            0,
            this_type,
            type_list_key(&[clone]),
        ));
        assert!(fixture.store.set_declared_type_links(
            class,
            DeclaredTypeLinks {
                declared_type: Some(origin),
                ..DeclaredTypeLinks::default()
            },
        ));

        assert_invalid_cached_declared_type_is_atomic(&mut fixture.store, parameter, clone);
        assert_invalid_cached_declared_type_is_atomic(&mut fixture.store, class, origin);
    }

    #[test]
    fn cached_class_rejects_instantiated_synthetic_this_type() {
        let mut fixture = fixture("class ThisClone<T> {}");
        let class = named_symbol(&fixture, SyntaxKind::ClassDeclaration, "ThisClone");
        let parameter = named_symbol(&fixture, SyntaxKind::TypeParameter, "T");
        let argument = fixture.store.alloc_type_parameter(Some(parameter)).unwrap();
        assert!(fixture.store.set_declared_type_links(
            parameter,
            DeclaredTypeLinks {
                declared_type: Some(argument),
                ..DeclaredTypeLinks::default()
            },
        ));
        let origin = fixture
            .store
            .alloc_interface_type(ObjectFlags::CLASS, Some(class))
            .unwrap();
        let this_type = fixture.store.alloc_type_parameter(Some(class)).unwrap();
        assert!(fixture.store.initialize_interface_type_parameters(
            origin,
            vec![argument, this_type],
            0,
            this_type,
            type_list_key(&[argument]),
        ));
        let mapper = fixture
            .store
            .new_simple_type_mapper(argument, argument)
            .unwrap();
        assert!(fixture.store.set_type_parameter_resolution(
            this_type,
            Some(origin),
            None,
            Some(mapper),
            None,
        ));
        assert!(fixture.store.set_declared_type_links(
            class,
            DeclaredTypeLinks {
                declared_type: Some(origin),
                ..DeclaredTypeLinks::default()
            },
        ));

        assert_invalid_cached_declared_type_is_atomic(&mut fixture.store, class, origin);
    }

    #[test]
    fn cached_declared_type_rejects_alias_on_ordinary_or_this_parameter() {
        let mut fixture = fixture("class Aliased<T> {}");
        let class = named_symbol(&fixture, SyntaxKind::ClassDeclaration, "Aliased");
        let parameter = named_symbol(&fixture, SyntaxKind::TypeParameter, "T");
        let bound = fixture.files.get(&fixture.file).unwrap();
        let host = host(&fixture.parsed.arena, bound);
        let declared_type = fixture
            .store
            .get_declared_type_of_symbol(&host, class)
            .unwrap();
        let data = interface_data(&fixture.store, declared_type);
        let argument = data.reference.resolved_type_arguments.as_ref().unwrap()[0];
        let this_type = data.this_type.unwrap();
        let alias = fixture.store.alloc_type_alias(Some(class)).unwrap();

        assert!(fixture.store.set_type_alias(argument, Some(alias)));
        assert_invalid_cached_declared_type_is_atomic(&mut fixture.store, parameter, argument);
        assert_invalid_cached_declared_type_is_atomic(&mut fixture.store, class, declared_type);

        assert!(fixture.store.set_type_alias(argument, None));
        assert_eq!(
            fixture.store.get_declared_type_of_symbol(&host, class),
            Ok(declared_type)
        );
        assert!(fixture.store.set_type_alias(this_type, Some(alias)));
        assert_invalid_cached_declared_type_is_atomic(&mut fixture.store, class, declared_type);
    }

    #[test]
    fn external_uninitialized_class_shell_is_not_a_valid_cached_identity() {
        let mut fixture = fixture("class External<T> {}");
        let class = named_symbol(&fixture, SyntaxKind::ClassDeclaration, "External");
        let shell = fixture
            .store
            .alloc_interface_type(ObjectFlags::CLASS, Some(class))
            .unwrap();
        publish_declared_type(&mut fixture.store, class, shell);
        let type_count = fixture.store.type_len();
        let link_counts = fixture.store.checker_link_allocated_lengths();
        let empty_host =
            DeclaredTypeHost::new(std::iter::empty::<(&NodeArena, &BoundFile)>()).unwrap();

        assert_eq!(
            fixture
                .store
                .get_declared_type_of_symbol(&empty_host, class),
            Err(unavailable(
                DeclaredTypeUnavailable::InvalidCachedDeclaredType {
                    symbol: class,
                    declared_type: shell,
                }
            ))
        );
        assert_eq!(fixture.store.type_len(), type_count);
        assert_eq!(fixture.store.checker_link_allocated_lengths(), link_counts);
        assert!(
            !fixture
                .store
                .declared_type_initialization_in_progress(class)
        );
    }

    #[test]
    fn ordinary_type_parameter_cache_rejects_a_this_type() {
        let mut fixture = fixture("class Holder<T> {}");
        let class = named_symbol(&fixture, SyntaxKind::ClassDeclaration, "Holder");
        let parameter = named_symbol(&fixture, SyntaxKind::TypeParameter, "T");
        let origin = fixture
            .store
            .alloc_interface_type(ObjectFlags::CLASS, Some(class))
            .unwrap();
        let candidate = fixture.store.alloc_type_parameter(Some(parameter)).unwrap();
        assert!(fixture.store.initialize_interface_type_parameters(
            origin,
            vec![candidate],
            0,
            candidate,
            type_list_key(&[]),
        ));
        publish_declared_type(&mut fixture.store, parameter, candidate);
        let type_count = fixture.store.type_len();
        let link_counts = fixture.store.checker_link_allocated_lengths();
        let empty_host =
            DeclaredTypeHost::new(std::iter::empty::<(&NodeArena, &BoundFile)>()).unwrap();

        assert_eq!(
            fixture
                .store
                .get_declared_type_of_symbol(&empty_host, parameter),
            Err(unavailable(
                DeclaredTypeUnavailable::InvalidCachedDeclaredType {
                    symbol: parameter,
                    declared_type: candidate,
                }
            ))
        );
        assert_eq!(fixture.store.type_len(), type_count);
        assert_eq!(fixture.store.checker_link_allocated_lengths(), link_counts);
    }

    #[test]
    fn published_class_shell_is_reentrant_before_parameter_allocation() {
        let mut fixture = fixture("class Reentrant<T> {}");
        let class = named_symbol(&fixture, SyntaxKind::ClassDeclaration, "Reentrant");
        let parameter = named_symbol(&fixture, SyntaxKind::TypeParameter, "T");
        let bound = fixture.files.get(&fixture.file).unwrap();
        let host = host(&fixture.parsed.arena, bound);
        let plan = preflight_class_plan(&fixture.store, &host, class).unwrap();
        assert!(fixture.store.begin_declared_type_initialization(class));
        let shell = fixture
            .store
            .alloc_interface_type(ObjectFlags::CLASS, Some(class))
            .unwrap();
        publish_declared_type(&mut fixture.store, class, shell);
        assert!(fixture.store.declared_type_links(parameter).is_none());
        let type_count = fixture.store.type_len();
        let link_counts = fixture.store.checker_link_allocated_lengths();

        let empty_host =
            DeclaredTypeHost::new(std::iter::empty::<(&NodeArena, &BoundFile)>()).unwrap();
        assert_eq!(
            fixture
                .store
                .get_declared_type_of_symbol(&empty_host, class),
            Ok(shell)
        );
        assert_eq!(fixture.store.type_len(), type_count);
        assert_eq!(fixture.store.checker_link_allocated_lengths(), link_counts);

        initialize_published_origin(
            &mut fixture.store,
            shell,
            plan.symbol,
            plan.type_parameters,
            plan.outer_type_parameter_count,
        );
        assert!(fixture.store.finish_declared_type_initialization(class));
        assert!(
            !fixture
                .store
                .declared_type_initialization_in_progress(class)
        );
        let arguments = interface_data(&fixture.store, shell)
            .reference
            .resolved_type_arguments
            .as_deref()
            .unwrap();
        assert_eq!(arguments.len(), 1);
        assert_eq!(
            fixture.store.type_payload(arguments[0]).unwrap().symbol(),
            Some(parameter)
        );
        assert_eq!(
            fixture
                .store
                .declared_type_links(parameter)
                .and_then(|links| links.declared_type),
            Some(arguments[0])
        );
    }

    #[test]
    fn published_interface_shell_is_reentrant_before_parameter_allocation() {
        let mut fixture = fixture("interface Reentrant<T> {}");
        let interface = named_symbol(&fixture, SyntaxKind::InterfaceDeclaration, "Reentrant");
        let parameter = named_symbol(&fixture, SyntaxKind::TypeParameter, "T");
        let bound = fixture.files.get(&fixture.file).unwrap();
        let host = host(&fixture.parsed.arena, bound);
        let plan = preflight_interface_plan(&fixture.store, &host, interface).unwrap();
        assert!(plan.has_this_type);
        assert!(fixture.store.begin_declared_type_initialization(interface));
        let shell = fixture
            .store
            .alloc_interface_type(ObjectFlags::INTERFACE, Some(interface))
            .unwrap();
        publish_declared_type(&mut fixture.store, interface, shell);
        assert!(fixture.store.declared_type_links(parameter).is_none());
        let type_count = fixture.store.type_len();
        let link_counts = fixture.store.checker_link_allocated_lengths();

        let empty_host =
            DeclaredTypeHost::new(std::iter::empty::<(&NodeArena, &BoundFile)>()).unwrap();
        assert_eq!(
            fixture
                .store
                .get_declared_type_of_symbol(&empty_host, interface),
            Ok(shell)
        );
        assert_eq!(fixture.store.type_len(), type_count);
        assert_eq!(fixture.store.checker_link_allocated_lengths(), link_counts);

        initialize_published_origin(
            &mut fixture.store,
            shell,
            plan.symbol,
            plan.type_parameters,
            plan.outer_type_parameter_count,
        );
        assert!(fixture.store.finish_declared_type_initialization(interface));
        let data = interface_data(&fixture.store, shell);
        let arguments = data.reference.resolved_type_arguments.as_deref().unwrap();
        assert_eq!(arguments.len(), 1);
        assert_eq!(
            fixture.store.type_payload(arguments[0]).unwrap().symbol(),
            Some(parameter)
        );
        assert_eq!(
            fixture
                .store
                .type_payload(data.this_type.unwrap())
                .unwrap()
                .symbol(),
            Some(interface)
        );
    }

    #[test]
    fn cached_interface_rejects_parameter_alias_target_and_mapper_inconsistencies() {
        let mut fixture = fixture("interface Cached<T> {}");
        let interface = named_symbol(&fixture, SyntaxKind::InterfaceDeclaration, "Cached");
        let parameter = named_symbol(&fixture, SyntaxKind::TypeParameter, "T");
        let bound = fixture.files.get(&fixture.file).unwrap();
        let host = host(&fixture.parsed.arena, bound);
        let declared_type = fixture
            .store
            .get_declared_type_of_symbol(&host, interface)
            .unwrap();
        let data = interface_data(&fixture.store, declared_type);
        let argument = data.reference.resolved_type_arguments.as_ref().unwrap()[0];
        let this_type = data.this_type.unwrap();
        let mapper = fixture
            .store
            .new_simple_type_mapper(argument, argument)
            .unwrap();

        assert!(fixture.store.set_type_parameter_resolution(
            this_type,
            Some(declared_type),
            Some(argument),
            Some(mapper),
            None,
        ));
        assert_invalid_cached_declared_type_is_atomic(&mut fixture.store, interface, declared_type);
        assert!(fixture.store.set_type_parameter_resolution(
            this_type,
            Some(declared_type),
            None,
            None,
            None,
        ));

        let alias = fixture.store.alloc_type_alias(Some(interface)).unwrap();
        assert!(fixture.store.set_type_alias(this_type, Some(alias)));
        assert_invalid_cached_declared_type_is_atomic(&mut fixture.store, interface, declared_type);
        assert!(fixture.store.set_type_alias(this_type, None));

        assert!(fixture.store.set_type_parameter_resolution(
            argument,
            None,
            Some(argument),
            Some(mapper),
            None,
        ));
        assert_invalid_cached_declared_type_is_atomic(&mut fixture.store, parameter, argument);
        assert_invalid_cached_declared_type_is_atomic(&mut fixture.store, interface, declared_type);
    }
}
