//! Read-only symbol planning for the dependency-closed top-level variable slice.
//!
//! The source checker owns expression execution and type publication. This module
//! proves the binder/resolver route for one ordinary top-level variable or one
//! read of an already-planned variable without mutating checker state.

use std::collections::HashSet;

use ts_ast::{Node, NodeArena, NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    BoundFile, CanonicalNameResolutionError, CanonicalNameResolver, CanonicalResolutionLocation,
    CheckFlags, SemanticSymbolId, SymbolFlags,
};

use super::{
    CanonicalTypeMapperStore, DeclaredTypeError, DeclaredTypeHost, TypeId, store::SourceNodeParent,
};

/// The declaration-list kind that determines a variable symbol's exact binder flags.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum VariableBindingKind {
    Var,
    Let,
    Const,
}

impl VariableBindingKind {
    pub(super) const fn is_const(self) -> bool {
        matches!(self, Self::Const)
    }

    const fn symbol_flags(self) -> SymbolFlags {
        match self {
            Self::Var => SymbolFlags::FUNCTION_SCOPED_VARIABLE,
            Self::Let | Self::Const => SymbolFlags::BLOCK_SCOPED_VARIABLE,
        }
    }
}

/// Exact resolver identities retained for one identifier expression.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct PlannedIdentifierRead {
    /// The symbol cached by upstream's `getResolvedSymbol` before export routing.
    pub(super) resolved_symbol: SemanticSymbolId,
    /// The value/export symbol whose `resolvedType` owns the expression type.
    pub(super) value_symbol: SemanticSymbolId,
}

/// One computed object binding whose symbol belongs to the binding element.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct PlannedComputedBindingElement {
    pub(super) declaration: NodeRef,
    pub(super) pattern: NodeRef,
    pub(super) element: NodeRef,
    pub(super) computed_name: NodeRef,
    pub(super) key: NodeRef,
    pub(super) name: NodeRef,
    pub(super) symbol: SemanticSymbolId,
}

/// Valid TypeScript symbol routes intentionally outside this source slice.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum VariableUnsupported {
    BindingPattern(NodeRef),
    UnresolvedIdentifier(NodeRef),
    ResolverDeferred {
        node: NodeRef,
        error: CanonicalNameResolutionError,
    },
    AliasSymbol {
        node: NodeRef,
        symbol: SemanticSymbolId,
    },
    NonVariableSymbol {
        node: NodeRef,
        symbol: SemanticSymbolId,
        flags: SymbolFlags,
    },
    MergedSymbol {
        node: NodeRef,
        source: SemanticSymbolId,
        target: SemanticSymbolId,
    },
    NonUniqueDeclaration {
        node: NodeRef,
        symbol: SemanticSymbolId,
        declaration_count: usize,
    },
    CrossFileDeclaration {
        node: NodeRef,
        declaration: NodeRef,
    },
    IdentifierNotPrior {
        node: NodeRef,
        symbol: SemanticSymbolId,
        declaration: NodeRef,
    },
    /// The caller has not proved an exact current type for this prior declaration.
    /// Source checking admits the symbol only after its complete statement tree
    /// has passed the bounded straight-line preflight.
    IdentifierRequiresFlowType {
        node: NodeRef,
        symbol: SemanticSymbolId,
        declaration: NodeRef,
    },
    /// `noImplicitAny` changes the type of a direct non-exported `=[]` initializer,
    /// but that option is not yet represented by `CanonicalCheckerOptions`.
    InferredEmptyArrayOption(NodeRef),
    /// `noImplicitAny` switches a direct/parenthesized non-exported mutable
    /// nullish initializer to control-flow `autoType`.
    InferredMutableNullishOption(NodeRef),
}

/// Malformed binder, resolver, or sparse-link provenance.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum VariableInvariant {
    InvalidBindingPattern(NodeRef),
    InvalidSymbol(SemanticSymbolId),
    MissingDeclarationSymbol(NodeRef),
    InvalidMergedSymbol(SemanticSymbolId),
    InvalidSymbolShape(SemanticSymbolId),
    MissingDeclarations(SemanticSymbolId),
    ValueDeclarationMismatch {
        symbol: SemanticSymbolId,
        declaration: NodeRef,
        value_declaration: Option<NodeRef>,
    },
    DeclarationSymbolMismatch {
        declaration: NodeRef,
        expected: SemanticSymbolId,
        actual: SemanticSymbolId,
    },
    IdentifierNameMismatch {
        node: NodeRef,
        declaration: NodeRef,
    },
    MissingExportSymbol(SemanticSymbolId),
    InvalidExportSymbol {
        value_symbol: SemanticSymbolId,
        export_symbol: SemanticSymbolId,
    },
    InvalidExportLocalShape(SemanticSymbolId),
    MissingExportLocal(NodeRef),
    LocalExportSymbolMismatch {
        declaration: NodeRef,
        expected: Option<SemanticSymbolId>,
        actual: Option<SemanticSymbolId>,
    },
    MissingSourceSymbol(NodeRef),
    InvalidTargetParent {
        symbol: SemanticSymbolId,
        expected: Option<SemanticSymbolId>,
        actual: Option<SemanticSymbolId>,
    },
    InvalidValueLinks(SemanticSymbolId),
    MissingStagedValueType(SemanticSymbolId),
    MissingCurrentFlowType(SemanticSymbolId),
    DuplicateStagedValueType(SemanticSymbolId),
    DuplicateCurrentFlowType(SemanticSymbolId),
    UnexpectedStagedValueType(SemanticSymbolId),
    InvalidStagedValueType {
        symbol: SemanticSymbolId,
        type_: TypeId,
    },
    AssignmentDeclaredTypeMismatch {
        symbol: SemanticSymbolId,
        staged: TypeId,
        resolved: TypeId,
    },
    DuplicateIdentifierRead(NodeRef),
    CachedValueTypeMismatch {
        symbol: SemanticSymbolId,
        cached: TypeId,
        expected: TypeId,
    },
    ValueTypePublication(SemanticSymbolId),
    SymbolNodePublication(NodeRef),
    InvalidSymbolNodeCache {
        node: NodeRef,
        cached: Option<SemanticSymbolId>,
        expected: SemanticSymbolId,
    },
    NameResolution(CanonicalNameResolutionError),
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum VariablePlanError {
    Unsupported(VariableUnsupported),
    Invariant(VariableInvariant),
    DeclaredType(DeclaredTypeError),
}

impl From<VariableInvariant> for VariablePlanError {
    fn from(error: VariableInvariant) -> Self {
        Self::Invariant(error)
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct RoutedValueSymbol {
    resolved: SemanticSymbolId,
    target: SemanticSymbolId,
    export_local: Option<SemanticSymbolId>,
}

/// Proves one source declaration's exact value-symbol owner and warm link shape.
#[allow(clippy::too_many_arguments)]
pub(super) fn plan_top_level_variable(
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    declaration: NodeRef,
    name: NodeRef,
    name_text: &str,
    binding: VariableBindingKind,
    exported: bool,
) -> Result<SemanticSymbolId, VariablePlanError> {
    let raw = bound
        .symbol(declaration)
        .ok_or(VariableInvariant::MissingDeclarationSymbol(declaration))?;
    let merged = store
        .get_merged_symbol(raw)
        .ok_or(VariableInvariant::InvalidMergedSymbol(raw))?;
    if merged != raw {
        return Err(VariablePlanError::Unsupported(
            VariableUnsupported::MergedSymbol {
                node: declaration,
                source: raw,
                target: merged,
            },
        ));
    }
    validate_variable_target(
        store,
        declaration,
        name,
        name_text,
        merged,
        binding.symbol_flags(),
    )?;

    let local = bound.local_symbol(declaration);
    let expected_local = if exported {
        let local = local.ok_or(VariableInvariant::MissingExportLocal(declaration))?;
        validate_export_local(store, local, declaration, merged, name_text)?;
        Some(local)
    } else {
        None
    };
    if local != expected_local {
        return Err(VariableInvariant::LocalExportSymbolMismatch {
            declaration,
            expected: expected_local,
            actual: local,
        }
        .into());
    }
    validate_target_parent(bound, store, merged, exported)?;
    validate_value_links(store, merged)?;
    Ok(merged)
}

/// Proves one top-level `{ [key]: name }` binding without publishing its type.
pub(super) fn plan_top_level_computed_binding_element(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    declaration: NodeRef,
    binding: VariableBindingKind,
    exported: bool,
) -> Result<PlannedComputedBindingElement, VariablePlanError> {
    if bound.node_arena_id() != arena.id()
        || bound.node_arena_revision() != arena.revision()
        || !declaration.is_for(arena.id(), bound.file_id())
    {
        return Err(VariableInvariant::InvalidBindingPattern(declaration).into());
    }
    let declaration_record = arena
        .get(declaration.node)
        .ok_or(VariableInvariant::InvalidBindingPattern(declaration))?;
    let NodeData::VariableDeclaration(variable) = &declaration_record.data else {
        return Err(VariablePlanError::Unsupported(
            VariableUnsupported::BindingPattern(declaration),
        ));
    };
    let list = declaration_record
        .parent
        .map(|node| NodeRef::new(declaration.arena, declaration.file, node))
        .ok_or(VariableInvariant::InvalidBindingPattern(declaration))?;
    let list_record = arena
        .get(list.node)
        .ok_or(VariableInvariant::InvalidBindingPattern(list))?;
    let statement = list_record
        .parent
        .map(|node| NodeRef::new(list.arena, list.file, node))
        .ok_or(VariableInvariant::InvalidBindingPattern(list))?;
    let source = bound.source_file();
    let statement_record = binding_child_node(arena, store, statement, source)?;
    let NodeData::VariableStatement(statement_data) = &statement_record.data else {
        return Err(VariableInvariant::InvalidBindingPattern(statement).into());
    };
    if statement_record.kind != SyntaxKind::VariableStatement
        || statement_data.declaration_list != list.node
    {
        return Err(VariableInvariant::InvalidBindingPattern(statement).into());
    }
    let list_record = binding_child_node(arena, store, list, statement)?;
    let NodeData::VariableDeclarationList(list_data) = &list_record.data else {
        return Err(VariableInvariant::InvalidBindingPattern(list).into());
    };
    let expected_flags = match binding {
        VariableBindingKind::Var => 0,
        VariableBindingKind::Let => 1,
        VariableBindingKind::Const => 1 << 1,
    };
    if list_record.kind != SyntaxKind::VariableDeclarationList
        || list_record.flags.0 != expected_flags
        || list_data
            .declarations
            .nodes
            .iter()
            .filter(|node| **node == declaration.node)
            .count()
            != 1
    {
        return Err(VariableInvariant::InvalidBindingPattern(list).into());
    }
    let declaration_record = binding_child_node(arena, store, declaration, list)?;
    if declaration_record.kind != SyntaxKind::VariableDeclaration
        || declaration_record.flags.0 != 0
        || variable.exclamation_token.is_some()
        || variable.local_symbol.is_some()
        || variable.symbol.is_some()
        || variable.facts != 0
        || bound.symbol(declaration).is_some()
        || bound.local_symbol(declaration).is_some()
    {
        return Err(VariableInvariant::InvalidBindingPattern(declaration).into());
    }

    let pattern = NodeRef::new(declaration.arena, declaration.file, variable.name);
    let pattern_record = binding_child_node(arena, store, pattern, declaration)?;
    let NodeData::BindingPattern(pattern_data) = &pattern_record.data else {
        return Err(VariablePlanError::Unsupported(
            VariableUnsupported::BindingPattern(pattern),
        ));
    };
    let [element] = pattern_data.elements.nodes.as_slice() else {
        return Err(VariablePlanError::Unsupported(
            VariableUnsupported::BindingPattern(pattern),
        ));
    };
    if pattern_record.kind != SyntaxKind::ObjectBindingPattern
        || pattern_record.flags.0 != 0
        || pattern_data.elements.has_trailing_comma
        || pattern_data.elements.range != pattern_record.range
        || pattern_data.facts != 0
    {
        return Err(VariablePlanError::Unsupported(
            VariableUnsupported::BindingPattern(pattern),
        ));
    }

    let element = NodeRef::new(pattern.arena, pattern.file, *element);
    let element_record = binding_child_node(arena, store, element, pattern)?;
    let NodeData::BindingElement(element_data) = &element_record.data else {
        return Err(VariableInvariant::InvalidBindingPattern(element).into());
    };
    if element_record.kind != SyntaxKind::BindingElement
        || element_record.flags.0 != 0
        || element_data.dot_dot_dot_token.is_some()
        || element_data.flow_node.is_some()
        || element_data.initializer.is_some()
        || element_data.local_symbol.is_some()
        || element_data.symbol.is_some()
        || element_data.facts != 0
    {
        return Err(VariablePlanError::Unsupported(
            VariableUnsupported::BindingPattern(element),
        ));
    }

    let computed_name = element_data
        .property_name
        .map(|node| NodeRef::new(element.arena, element.file, node))
        .ok_or(VariablePlanError::Unsupported(
            VariableUnsupported::BindingPattern(element),
        ))?;
    let computed_record = binding_child_node(arena, store, computed_name, element)?;
    let NodeData::ComputedPropertyName(computed) = &computed_record.data else {
        return Err(VariablePlanError::Unsupported(
            VariableUnsupported::BindingPattern(computed_name),
        ));
    };
    if computed_record.kind != SyntaxKind::ComputedPropertyName
        || computed_record.flags.0 != 0
        || computed.facts != 0
    {
        return Err(VariablePlanError::Unsupported(
            VariableUnsupported::BindingPattern(computed_name),
        ));
    }
    let key = NodeRef::new(computed_name.arena, computed_name.file, computed.expression);
    binding_child_node(arena, store, key, computed_name)?;

    let name = element_data
        .name
        .map(|node| NodeRef::new(element.arena, element.file, node))
        .ok_or(VariableInvariant::InvalidBindingPattern(element))?;
    let name_record = binding_child_node(arena, store, name, element)?;
    let NodeData::Identifier(identifier) = &name_record.data else {
        return Err(VariablePlanError::Unsupported(
            VariableUnsupported::BindingPattern(name),
        ));
    };
    if name_record.kind != SyntaxKind::Identifier
        || name_record.flags.0 != 0
        || identifier.flow_node.is_some()
        || identifier.text.is_empty()
        || computed_record.range.end > name_record.range.start
    {
        return Err(VariableInvariant::InvalidBindingPattern(name).into());
    }

    let symbol = plan_top_level_variable(
        bound,
        store,
        element,
        name,
        &identifier.text,
        binding,
        exported,
    )?;
    let local = bound.local_symbol(element).unwrap_or(symbol);
    if bound.container(element) != Some(source)
        || bound.block_scope_container(element) != Some(source)
        || bound
            .locals(source)
            .and_then(|locals| store.symbol_table(locals))
            .and_then(|locals| locals.get_source(&identifier.text))
            != Some(local)
    {
        return Err(VariableInvariant::InvalidBindingPattern(element).into());
    }

    Ok(PlannedComputedBindingElement {
        declaration,
        pattern,
        element,
        computed_name,
        key,
        name,
        symbol,
    })
}

fn binding_child_node<'a>(
    arena: &'a NodeArena,
    store: &CanonicalTypeMapperStore,
    node: NodeRef,
    parent: NodeRef,
) -> Result<&'a Node, VariablePlanError> {
    let record = arena
        .get(node.node)
        .ok_or(VariableInvariant::InvalidBindingPattern(node))?;
    let parent_record = arena
        .get(parent.node)
        .ok_or(VariableInvariant::InvalidBindingPattern(parent))?;
    if !node.is_for(parent.arena, parent.file)
        || record.parent != Some(parent.node)
        || store.source_node_kind(node) != Some(record.kind)
        || store.source_node_parent(node) != Some(SourceNodeParent::Parent(parent))
        || record.range.start < parent_record.range.start
        || record.range.end > parent_record.range.end
        || record.range.start > record.range.end
    {
        return Err(VariableInvariant::InvalidBindingPattern(node).into());
    }
    Ok(record)
}

/// Resolves one identifier and proves that it reads an already-planned source variable.
#[allow(clippy::too_many_arguments)]
pub(super) fn plan_identifier_read(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    prior_variables: &HashSet<SemanticSymbolId>,
    readable_variables: &HashSet<SemanticSymbolId>,
    node: NodeRef,
    name: &str,
) -> Result<PlannedIdentifierRead, VariablePlanError> {
    let mut callback_host = host
        .name_resolver_host(store)
        .map_err(VariablePlanError::DeclaredType)?;
    let mut resolver =
        CanonicalNameResolver::new(arena, bound, store.symbol_store(), &mut callback_host)
            .map_err(|error| name_resolution_error(node, error))?;
    let raw_symbol = match resolver.resolve(
        Some(CanonicalResolutionLocation::Bound(node)),
        name,
        SymbolFlags::VALUE | SymbolFlags::EXPORT_VALUE,
        None,
        false,
        false,
    ) {
        Ok(Some(symbol)) => symbol,
        Ok(None) => {
            return Err(VariablePlanError::Unsupported(
                VariableUnsupported::UnresolvedIdentifier(node),
            ));
        }
        Err(CanonicalNameResolutionError::AliasResolutionUnavailable(symbol)) => {
            return Err(VariablePlanError::Unsupported(
                VariableUnsupported::AliasSymbol { node, symbol },
            ));
        }
        Err(error) => return Err(name_resolution_error(node, error)),
    };
    let routed = route_value_symbol(store, node, raw_symbol)?;
    let record = store
        .symbol(routed.target)
        .ok_or(VariableInvariant::InvalidSymbol(routed.target))?;
    let flags = record.flags();
    if flags.intersects(SymbolFlags::ALIAS) {
        return Err(VariablePlanError::Unsupported(
            VariableUnsupported::AliasSymbol {
                node,
                symbol: routed.target,
            },
        ));
    }
    if variable_binding_flags(flags).is_none() {
        return Err(VariablePlanError::Unsupported(
            VariableUnsupported::NonVariableSymbol {
                node,
                symbol: routed.target,
                flags,
            },
        ));
    }
    let declarations = record
        .declarations()
        .ok_or(VariableInvariant::MissingDeclarations(routed.target))?;
    let declaration =
        single_variable_declaration(store, node, routed.target, flags, declarations, true)?;
    if declaration.file != node.file || declaration.arena != node.arena {
        return Err(VariablePlanError::Unsupported(
            VariableUnsupported::CrossFileDeclaration { node, declaration },
        ));
    }
    if record.value_declaration() != Some(declaration) {
        return Err(VariableInvariant::ValueDeclarationMismatch {
            symbol: routed.target,
            declaration,
            value_declaration: record.value_declaration(),
        }
        .into());
    }
    if record.name().as_bytes() != name.as_bytes() {
        return Err(VariableInvariant::IdentifierNameMismatch { node, declaration }.into());
    }
    let declaration_symbol = bound
        .symbol(declaration)
        .ok_or(VariableInvariant::MissingDeclarationSymbol(declaration))?;
    let declaration_symbol = store
        .get_merged_symbol(declaration_symbol)
        .ok_or(VariableInvariant::InvalidMergedSymbol(declaration_symbol))?;
    if declaration_symbol != routed.target {
        return Err(VariableInvariant::DeclarationSymbolMismatch {
            declaration,
            expected: routed.target,
            actual: declaration_symbol,
        }
        .into());
    }
    if let Some(local) = routed.export_local {
        validate_export_local(store, local, declaration, routed.target, name)?;
    }
    if bound.local_symbol(declaration) != routed.export_local {
        return Err(VariableInvariant::LocalExportSymbolMismatch {
            declaration,
            expected: routed.export_local,
            actual: bound.local_symbol(declaration),
        }
        .into());
    }
    validate_target_parent(bound, store, routed.target, routed.export_local.is_some())?;
    if !prior_variables.contains(&routed.target) {
        return Err(VariablePlanError::Unsupported(
            VariableUnsupported::IdentifierNotPrior {
                node,
                symbol: routed.target,
                declaration,
            },
        ));
    }
    if !readable_variables.contains(&routed.target) {
        return Err(VariablePlanError::Unsupported(
            VariableUnsupported::IdentifierRequiresFlowType {
                node,
                symbol: routed.target,
                declaration,
            },
        ));
    }
    if store.symbol_node_links(node).is_some_and(|links| {
        links
            .resolved_symbol
            .is_some_and(|cached| cached != routed.resolved)
    }) {
        return Err(VariableInvariant::InvalidSymbolNodeCache {
            node,
            cached: store
                .symbol_node_links(node)
                .and_then(|links| links.resolved_symbol),
            expected: routed.resolved,
        }
        .into());
    }
    Ok(PlannedIdentifierRead {
        resolved_symbol: routed.resolved,
        value_symbol: routed.target,
    })
}

/// Resolves one already-planned class or enum value without treating it as a variable.
#[allow(clippy::too_many_arguments)]
pub(super) fn plan_declared_value_identifier_read(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    node: NodeRef,
    name: &str,
    expected: SemanticSymbolId,
) -> Result<PlannedIdentifierRead, VariablePlanError> {
    let mut callback_host = host
        .name_resolver_host(store)
        .map_err(VariablePlanError::DeclaredType)?;
    let mut name_lookup =
        CanonicalNameResolver::new(arena, bound, store.symbol_store(), &mut callback_host)
            .map_err(|error| name_resolution_error(node, error))?;
    let resolved_symbol = name_lookup
        .resolve(
            Some(CanonicalResolutionLocation::Bound(node)),
            name,
            SymbolFlags::VALUE | SymbolFlags::EXPORT_VALUE,
            None,
            false,
            false,
        )
        .map_err(|error| name_resolution_error(node, error))?
        .ok_or(VariablePlanError::Unsupported(
            VariableUnsupported::UnresolvedIdentifier(node),
        ))?;
    let routed = route_value_symbol(store, node, resolved_symbol)?;
    if routed.target != expected {
        return Err(VariableInvariant::InvalidSymbolShape(expected).into());
    }
    let record = store
        .symbol(routed.target)
        .ok_or(VariableInvariant::InvalidSymbol(routed.target))?;
    if !record
        .flags()
        .intersects(SymbolFlags::CLASS | SymbolFlags::ENUM)
    {
        return Err(VariablePlanError::Unsupported(
            VariableUnsupported::NonVariableSymbol {
                node,
                symbol: routed.target,
                flags: record.flags(),
            },
        ));
    }
    let Some([declaration]) = record.declarations() else {
        return Err(VariablePlanError::Unsupported(
            VariableUnsupported::NonUniqueDeclaration {
                node,
                symbol: routed.target,
                declaration_count: record.declarations().map_or(0, <[NodeRef]>::len),
            },
        ));
    };
    let declaration = *declaration;
    if declaration.file != node.file || declaration.arena != node.arena {
        return Err(VariablePlanError::Unsupported(
            VariableUnsupported::CrossFileDeclaration { node, declaration },
        ));
    }
    if !matches!(
        store.source_node_kind(declaration),
        Some(SyntaxKind::ClassDeclaration | SyntaxKind::EnumDeclaration)
    ) || record.value_declaration() != Some(declaration)
        || record.name().as_bytes() != name.as_bytes()
    {
        return Err(VariableInvariant::InvalidSymbolShape(routed.target).into());
    }
    let declaration_symbol = bound
        .symbol(declaration)
        .ok_or(VariableInvariant::MissingDeclarationSymbol(declaration))?;
    if store.get_merged_symbol(declaration_symbol) != Some(routed.target) {
        return Err(VariableInvariant::DeclarationSymbolMismatch {
            declaration,
            expected: routed.target,
            actual: declaration_symbol,
        }
        .into());
    }
    if let Some(local) = routed.export_local {
        validate_export_local(store, local, declaration, routed.target, name)?;
    }
    if bound.local_symbol(declaration) != routed.export_local {
        return Err(VariableInvariant::LocalExportSymbolMismatch {
            declaration,
            expected: routed.export_local,
            actual: bound.local_symbol(declaration),
        }
        .into());
    }
    validate_target_parent(bound, store, routed.target, routed.export_local.is_some())?;
    if store.symbol_node_links(node).is_some_and(|links| {
        links
            .resolved_symbol
            .is_some_and(|cached| cached != routed.resolved)
    }) {
        return Err(VariableInvariant::InvalidSymbolNodeCache {
            node,
            cached: store
                .symbol_node_links(node)
                .and_then(|links| links.resolved_symbol),
            expected: routed.resolved,
        }
        .into());
    }
    Ok(PlannedIdentifierRead {
        resolved_symbol: routed.resolved,
        value_symbol: routed.target,
    })
}

fn route_value_symbol(
    store: &CanonicalTypeMapperStore,
    node: NodeRef,
    resolved: SemanticSymbolId,
) -> Result<RoutedValueSymbol, VariablePlanError> {
    let record = store
        .symbol(resolved)
        .ok_or(VariableInvariant::InvalidSymbol(resolved))?;
    let export_local = record.flags().intersects(SymbolFlags::EXPORT_VALUE);
    let routed = if export_local {
        if record.flags() != SymbolFlags::EXPORT_VALUE
            || record.check_flags() != CheckFlags::NONE
            || !matches!(record.declarations(), Some([_]))
            || record.value_declaration().is_some()
            || record.members().is_some()
            || record.exports().is_some()
            || record.parent().is_some()
        {
            return Err(VariableInvariant::InvalidExportLocalShape(resolved).into());
        }
        let export_symbol = record
            .export_symbol()
            .ok_or(VariableInvariant::MissingExportSymbol(resolved))?;
        if store.symbol(export_symbol).is_none() {
            return Err(VariableInvariant::InvalidExportSymbol {
                value_symbol: resolved,
                export_symbol,
            }
            .into());
        }
        export_symbol
    } else {
        resolved
    };
    let merged = store
        .get_merged_symbol(routed)
        .ok_or(VariableInvariant::InvalidMergedSymbol(routed))?;
    if merged != routed {
        return Err(VariablePlanError::Unsupported(
            VariableUnsupported::MergedSymbol {
                node,
                source: routed,
                target: merged,
            },
        ));
    }
    Ok(RoutedValueSymbol {
        resolved,
        target: merged,
        export_local: export_local.then_some(resolved),
    })
}

fn validate_variable_target(
    store: &CanonicalTypeMapperStore,
    declaration: NodeRef,
    name: NodeRef,
    name_text: &str,
    symbol: SemanticSymbolId,
    expected_flags: SymbolFlags,
) -> Result<(), VariablePlanError> {
    let record = store
        .symbol(symbol)
        .ok_or(VariableInvariant::InvalidSymbol(symbol))?;
    if variable_binding_flags(record.flags()) != Some(expected_flags) {
        return Err(VariablePlanError::Unsupported(
            VariableUnsupported::NonVariableSymbol {
                node: declaration,
                symbol,
                flags: record.flags(),
            },
        ));
    }
    if record.check_flags() != CheckFlags::NONE
        || record.members().is_some() && !record.flags().contains(SymbolFlags::INTERFACE)
        || record.exports().is_some() && !record.flags().contains(SymbolFlags::NAMESPACE_MODULE)
        || record.export_symbol().is_some()
    {
        return Err(VariableInvariant::InvalidSymbolShape(symbol).into());
    }
    let declarations = record
        .declarations()
        .ok_or(VariableInvariant::MissingDeclarations(symbol))?;
    let actual = single_variable_declaration(
        store,
        declaration,
        symbol,
        record.flags(),
        declarations,
        false,
    )?;
    if actual != declaration {
        return Err(VariableInvariant::InvalidSymbolShape(symbol).into());
    }
    if record.value_declaration() != Some(declaration) {
        return Err(VariableInvariant::ValueDeclarationMismatch {
            symbol,
            declaration,
            value_declaration: record.value_declaration(),
        }
        .into());
    }
    if record.name().as_bytes() != name_text.as_bytes() {
        return Err(VariableInvariant::IdentifierNameMismatch {
            node: name,
            declaration,
        }
        .into());
    }
    Ok(())
}

fn variable_binding_flags(flags: SymbolFlags) -> Option<SymbolFlags> {
    let binding = flags & SymbolFlags::VARIABLE;
    if binding != SymbolFlags::FUNCTION_SCOPED_VARIABLE
        && binding != SymbolFlags::BLOCK_SCOPED_VARIABLE
    {
        return None;
    }
    let allowed = binding | SymbolFlags::INTERFACE | SymbolFlags::NAMESPACE_MODULE;
    (flags.without(allowed) == SymbolFlags::NONE).then_some(binding)
}

fn single_variable_declaration(
    store: &CanonicalTypeMapperStore,
    node: NodeRef,
    symbol: SemanticSymbolId,
    flags: SymbolFlags,
    declarations: &[NodeRef],
    allow_parameter: bool,
) -> Result<NodeRef, VariablePlanError> {
    let mut variable = None;
    for declaration in declarations.iter().copied() {
        match store.source_node_kind(declaration) {
            Some(SyntaxKind::VariableDeclaration | SyntaxKind::BindingElement)
                if variable.is_none() =>
            {
                variable = Some(declaration);
            }
            Some(SyntaxKind::Parameter)
                if allow_parameter
                    && variable.is_none()
                    && declarations.len() == 1
                    && flags == SymbolFlags::FUNCTION_SCOPED_VARIABLE =>
            {
                variable = Some(declaration);
            }
            Some(SyntaxKind::InterfaceDeclaration) if flags.contains(SymbolFlags::INTERFACE) => {}
            Some(SyntaxKind::ModuleDeclaration)
                if flags.contains(SymbolFlags::NAMESPACE_MODULE) => {}
            _ => {
                return Err(VariablePlanError::Unsupported(
                    VariableUnsupported::NonUniqueDeclaration {
                        node,
                        symbol,
                        declaration_count: declarations.len(),
                    },
                ));
            }
        }
    }
    variable.ok_or_else(|| VariableInvariant::InvalidSymbolShape(symbol).into())
}

fn validate_export_local(
    store: &CanonicalTypeMapperStore,
    local: SemanticSymbolId,
    declaration: NodeRef,
    target: SemanticSymbolId,
    name: &str,
) -> Result<(), VariablePlanError> {
    let record = store
        .symbol(local)
        .ok_or(VariableInvariant::InvalidSymbol(local))?;
    if record.flags() != SymbolFlags::EXPORT_VALUE
        || record.check_flags() != CheckFlags::NONE
        || record.name().as_bytes() != name.as_bytes()
        || record.declarations() != Some(&[declaration])
        || record.value_declaration().is_some()
        || record.members().is_some()
        || record.exports().is_some()
        || record.parent().is_some()
        || record.export_symbol() != Some(target)
        || store.get_merged_symbol(local) != Some(local)
    {
        return Err(VariableInvariant::InvalidExportLocalShape(local).into());
    }
    Ok(())
}

fn validate_target_parent(
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    target: SemanticSymbolId,
    exported: bool,
) -> Result<(), VariablePlanError> {
    let expected = if exported {
        let source = bound.source_file();
        let raw = bound
            .symbol(source)
            .ok_or(VariableInvariant::MissingSourceSymbol(source))?;
        let merged = store
            .get_merged_symbol(raw)
            .ok_or(VariableInvariant::InvalidMergedSymbol(raw))?;
        if merged != raw {
            return Err(VariablePlanError::Unsupported(
                VariableUnsupported::MergedSymbol {
                    node: source,
                    source: raw,
                    target: merged,
                },
            ));
        }
        Some(merged)
    } else {
        None
    };
    let actual = store
        .symbol(target)
        .ok_or(VariableInvariant::InvalidSymbol(target))?
        .parent();
    if actual != expected {
        return Err(VariableInvariant::InvalidTargetParent {
            symbol: target,
            expected,
            actual,
        }
        .into());
    }
    Ok(())
}

fn validate_value_links(
    store: &CanonicalTypeMapperStore,
    symbol: SemanticSymbolId,
) -> Result<(), VariablePlanError> {
    let Some(links) = store.value_symbol_links(symbol) else {
        return Ok(());
    };
    if links.write_type.is_some()
        || links.target.is_some()
        || links.mapper.is_some()
        || links.name_type.is_some()
        || links.containing_type.is_some()
        || links.function_or_constructor_checked
    {
        return Err(VariableInvariant::InvalidValueLinks(symbol).into());
    }
    Ok(())
}

fn name_resolution_error(node: NodeRef, error: CanonicalNameResolutionError) -> VariablePlanError {
    match error {
        error @ (CanonicalNameResolutionError::JavaScriptDeferred(_)
        | CanonicalNameResolutionError::CommonJsDeferred(_)
        | CanonicalNameResolutionError::JsDocDeferred(_)) => {
            VariablePlanError::Unsupported(VariableUnsupported::ResolverDeferred { node, error })
        }
        error => VariablePlanError::Invariant(VariableInvariant::NameResolution(error)),
    }
}

#[cfg(test)]
mod tests {
    use ts_ast::{FileId, NodeData};
    use ts_binder::{
        CanonicalBinder, CanonicalModuleState, CanonicalNameResolverOptions,
        CanonicalSourceFileFacts, CanonicalSourceLanguage, EscapedName,
    };
    use ts_parser::{ParseResult, parse_source_file};

    use super::*;
    use crate::semantic::{
        IntrinsicBootstrapOptions, ValueSymbolLinks, production::GlobalMergeCompletion,
    };

    struct BindingFixture {
        parsed: ParseResult,
        file: ts_ast::FileId,
        bound: BoundFile,
        store: CanonicalTypeMapperStore,
    }

    fn binding_fixture(source: &str, file: u32) -> BindingFixture {
        let parsed = parse_source_file(source);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(file);
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source("\"/binding-elements.ts\""),
                    CanonicalSourceLanguage::TypeScript,
                    false,
                    CanonicalModuleState::Script,
                ),
            )
            .unwrap();
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
        let (symbols, mut files) = binder.finish().try_into_parts().unwrap();
        let bound = files.remove(&file).unwrap();
        let mut store = CanonicalTypeMapperStore::from_symbol_store(symbols);
        assert!(
            store
                .register_source_file(&parsed.arena, parsed.source_file, file)
                .is_some()
        );
        store
            .initialize_intrinsic_bootstrap(IntrinsicBootstrapOptions::default())
            .unwrap();
        BindingFixture {
            parsed,
            file,
            bound,
            store,
        }
    }

    fn binding_declaration(fixture: &BindingFixture) -> NodeRef {
        fixture
            .parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                let NodeData::VariableDeclaration(declaration) = &record.data else {
                    return None;
                };
                matches!(
                    fixture.parsed.arena.get(declaration.name)?.data,
                    NodeData::BindingPattern(_)
                )
                .then_some(NodeRef::new(
                    fixture.parsed.arena.id(),
                    fixture.file,
                    node,
                ))
            })
            .expect("fixture contains a binding-pattern declaration")
    }

    #[test]
    fn computed_binding_element_preserves_symbol_identity_reads_and_warm_links() {
        let mut fixture = binding_fixture(
            "let key = () => 'name'; let { [key()]: value } = {}; let observed = value;",
            918,
        );
        let declaration = binding_declaration(&fixture);
        let plan = plan_top_level_computed_binding_element(
            &fixture.parsed.arena,
            &fixture.bound,
            &fixture.store,
            declaration,
            VariableBindingKind::Let,
            false,
        )
        .unwrap();

        assert!(fixture.bound.symbol(declaration).is_none());
        assert_eq!(fixture.bound.symbol(plan.element), Some(plan.symbol));
        assert_eq!(
            fixture.store.symbol(plan.symbol).unwrap().declarations(),
            Some(&[plan.element][..])
        );
        assert_eq!(
            fixture.store.source_node_parent(plan.key),
            Some(SourceNodeParent::Parent(plan.computed_name))
        );
        assert!(fixture.store.value_symbol_links(plan.symbol).is_none());
        assert_eq!(
            plan_top_level_variable(
                &fixture.bound,
                &fixture.store,
                plan.element,
                plan.name,
                "value",
                VariableBindingKind::Let,
                false,
            ),
            Ok(plan.symbol)
        );

        let read = fixture
            .parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                let NodeData::Identifier(identifier) = &record.data else {
                    return None;
                };
                (identifier.text == "value" && node != plan.name.node).then_some(NodeRef::new(
                    fixture.parsed.arena.id(),
                    fixture.file,
                    node,
                ))
            })
            .unwrap();
        let globals = fixture.store.intrinsic_bootstrap().unwrap().globals;
        assert_eq!(
            fixture.store.merge_global_symbol(globals, plan.symbol),
            Ok(plan.symbol)
        );
        let host = DeclaredTypeHost::new_after_global_merge(
            [(&fixture.parsed.arena, &fixture.bound)],
            GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
        )
        .unwrap();
        assert_eq!(
            plan_identifier_read(
                &fixture.parsed.arena,
                &fixture.bound,
                &fixture.store,
                &host,
                &HashSet::from([plan.symbol]),
                &HashSet::from([plan.symbol]),
                read,
                "value",
            ),
            Ok(PlannedIdentifierRead {
                resolved_symbol: plan.symbol,
                value_symbol: plan.symbol,
            })
        );

        let error = fixture.store.intrinsic_bootstrap().unwrap().error_type;
        let links = ValueSymbolLinks {
            resolved_type: Some(error),
            ..ValueSymbolLinks::default()
        };
        assert!(
            fixture
                .store
                .set_value_symbol_links(plan.symbol, links.clone())
        );
        let warm = (
            fixture.store.type_len(),
            fixture.store.checker_link_allocated_lengths(),
        );
        assert_eq!(
            plan_top_level_computed_binding_element(
                &fixture.parsed.arena,
                &fixture.bound,
                &fixture.store,
                declaration,
                VariableBindingKind::Let,
                false,
            ),
            Ok(plan)
        );
        assert_eq!(fixture.store.value_symbol_links(plan.symbol), Some(&links));
        assert_eq!(
            (
                fixture.store.type_len(),
                fixture.store.checker_link_allocated_lengths(),
            ),
            warm
        );
    }

    #[test]
    fn unsupported_binding_shapes_and_poisoned_links_stay_fail_closed() {
        for (index, source) in [
            "let { name: value } = {};",
            "let { [key()]: first, [key()]: second } = {};",
            "let { [key()]: value = 1 } = {};",
            "let { [key()]: value, } = {};",
            "let [value] = [];",
        ]
        .into_iter()
        .enumerate()
        {
            let fixture = binding_fixture(source, 920 + u32::try_from(index).unwrap());
            let declaration = binding_declaration(&fixture);
            assert!(matches!(
                plan_top_level_computed_binding_element(
                    &fixture.parsed.arena,
                    &fixture.bound,
                    &fixture.store,
                    declaration,
                    VariableBindingKind::Let,
                    false,
                ),
                Err(VariablePlanError::Unsupported(
                    VariableUnsupported::BindingPattern(_)
                ))
            ));
        }

        let mut fixture = binding_fixture("let { [key()]: value } = {};", 926);
        let declaration = binding_declaration(&fixture);
        let plan = plan_top_level_computed_binding_element(
            &fixture.parsed.arena,
            &fixture.bound,
            &fixture.store,
            declaration,
            VariableBindingKind::Let,
            false,
        )
        .unwrap();
        let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
        let links = ValueSymbolLinks {
            resolved_type: Some(bootstrap.error_type),
            write_type: Some(bootstrap.number_type),
            ..ValueSymbolLinks::default()
        };
        assert!(fixture.store.set_value_symbol_links(plan.symbol, links));
        let poisoned = fixture.store.checker_link_allocated_lengths();
        assert_eq!(
            plan_top_level_computed_binding_element(
                &fixture.parsed.arena,
                &fixture.bound,
                &fixture.store,
                declaration,
                VariableBindingKind::Let,
                false,
            ),
            Err(VariablePlanError::Invariant(
                VariableInvariant::InvalidValueLinks(plan.symbol)
            ))
        );
        assert_eq!(fixture.store.checker_link_allocated_lengths(), poisoned);
    }

    #[test]
    fn merged_interface_and_type_only_namespace_preserve_variable_reads() {
        for (source, merged_flag) in [
            (
                "interface Shared {} declare var Shared: string; const observed = Shared;",
                SymbolFlags::INTERFACE,
            ),
            (
                "declare var Shared: string; declare namespace Shared {} const observed = Shared;",
                SymbolFlags::NAMESPACE_MODULE,
            ),
        ] {
            let parsed = parse_source_file(source);
            assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
            let file = FileId::new(917);
            let mut binder = CanonicalBinder::new();
            binder
                .bind_source_file_with_facts(
                    &parsed.arena,
                    parsed.source_file,
                    file,
                    CanonicalSourceFileFacts::new(
                        EscapedName::source("\"/variables.ts\""),
                        CanonicalSourceLanguage::TypeScript,
                        false,
                        CanonicalModuleState::Script,
                    ),
                )
                .unwrap();
            binder
                .bind_typescript_declaration_slice(&parsed.arena, file)
                .unwrap();
            let (symbols, mut files) = binder.finish().try_into_parts().unwrap();
            let bound = files.remove(&file).unwrap();
            let mut store = CanonicalTypeMapperStore::from_symbol_store(symbols);
            assert!(
                store
                    .register_source_file(&parsed.arena, parsed.source_file, file)
                    .is_some()
            );
            store
                .initialize_intrinsic_bootstrap(IntrinsicBootstrapOptions::default())
                .unwrap();

            let find_declaration = |text: &str| {
                parsed.arena.iter().find_map(|(node, record)| {
                    let NodeData::VariableDeclaration(variable) = &record.data else {
                        return None;
                    };
                    let NodeData::Identifier(identifier) = &parsed.arena.get(variable.name)?.data
                    else {
                        return None;
                    };
                    (identifier.text == text).then_some((
                        NodeRef::new(parsed.arena.id(), file, node),
                        NodeRef::new(parsed.arena.id(), file, variable.name),
                        variable
                            .initializer
                            .map(|initializer| NodeRef::new(parsed.arena.id(), file, initializer)),
                    ))
                })
            };
            let (declaration, name, _) = find_declaration("Shared").unwrap();
            let (_, _, read) = find_declaration("observed").unwrap();
            let read = read.unwrap();
            let raw_symbol = bound.symbol(declaration).unwrap();
            let globals = store.intrinsic_bootstrap().unwrap().globals;
            assert_eq!(
                store.merge_global_symbol(globals, raw_symbol).unwrap(),
                raw_symbol
            );

            let symbol = plan_top_level_variable(
                &bound,
                &store,
                declaration,
                name,
                "Shared",
                VariableBindingKind::Var,
                false,
            )
            .unwrap();
            assert!(store.symbol(symbol).unwrap().flags().contains(merged_flag));
            let host = DeclaredTypeHost::new_after_global_merge(
                [(&parsed.arena, &bound)],
                GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
            )
            .unwrap();
            let planned = plan_identifier_read(
                &parsed.arena,
                &bound,
                &store,
                &host,
                &HashSet::from([symbol]),
                &HashSet::from([symbol]),
                read,
                "Shared",
            )
            .unwrap();
            assert_eq!(planned.value_symbol, symbol);
        }
    }

    #[test]
    fn non_variable_value_merges_are_not_variable_bindings() {
        for additional in [
            SymbolFlags::CLASS,
            SymbolFlags::FUNCTION,
            SymbolFlags::REGULAR_ENUM,
            SymbolFlags::CONST_ENUM,
            SymbolFlags::VALUE_MODULE,
        ] {
            assert_eq!(
                variable_binding_flags(SymbolFlags::FUNCTION_SCOPED_VARIABLE | additional),
                None,
            );
        }
    }
}
