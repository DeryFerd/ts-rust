//! Read-only symbol planning for the dependency-closed top-level variable slice.
//!
//! The source checker owns expression execution and type publication. This module
//! proves the binder/resolver route for ordinary top-level variables, object and
//! array binding elements, already-planned local reads, and authenticated ambient
//! globals from other script declaration files without mutating checker state.

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
    Using,
    AwaitUsing,
}

impl VariableBindingKind {
    pub(super) const fn is_const(self) -> bool {
        matches!(self, Self::Const | Self::Using | Self::AwaitUsing)
    }

    pub(super) const fn is_using(self) -> bool {
        matches!(self, Self::Using | Self::AwaitUsing)
    }

    const fn declaration_flags(self) -> u32 {
        match self {
            Self::Var => 0,
            Self::Let => 1,
            Self::Const => 1 << 1,
            Self::Using => 1 << 2,
            Self::AwaitUsing => (1 << 1) | (1 << 2),
        }
    }

    const fn symbol_flags(self) -> SymbolFlags {
        match self {
            Self::Var => SymbolFlags::FUNCTION_SCOPED_VARIABLE,
            Self::Let | Self::Const | Self::Using | Self::AwaitUsing => {
                SymbolFlags::BLOCK_SCOPED_VARIABLE
            }
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

/// One authenticated global read backed by another script declaration file.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct PlannedCrossFileGlobalRead {
    pub(super) type_node: NodeRef,
    pub(super) read: PlannedIdentifierRead,
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

/// One named property traversed before reaching a nested object binding.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct PlannedObjectBindingProperty {
    pub(super) property: NodeRef,
    pub(super) property_name: String,
}

/// One ordinary object binding whose declaration symbol belongs to its element.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct PlannedObjectBindingElement {
    pub(super) element: NodeRef,
    pub(super) property: NodeRef,
    pub(super) property_name: String,
    pub(super) computed_key: Option<NodeRef>,
    pub(super) parent_properties: Vec<PlannedObjectBindingProperty>,
    pub(super) initializer: Option<NodeRef>,
    pub(super) rest: bool,
    pub(super) excluded_properties: Vec<String>,
    pub(super) name: NodeRef,
    pub(super) symbol: SemanticSymbolId,
}

/// One positional array binding whose symbol belongs to its binding element.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct PlannedArrayBindingElement {
    pub(super) declaration: NodeRef,
    pub(super) pattern: NodeRef,
    pub(super) element: NodeRef,
    pub(super) index: usize,
    pub(super) initializer: Option<NodeRef>,
    pub(super) rest: bool,
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
    /// An evolving empty-array initializer appears in a flow scope that does
    /// not yet support indexed mutations.
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
    plan_variable_declaration(
        bound,
        store,
        declaration,
        name,
        name_text,
        binding,
        exported,
        false,
    )
}

/// Proves a same-file, function-scoped variable with compatible redeclarations.
pub(super) fn plan_redeclared_top_level_variable(
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    declaration: NodeRef,
    name: NodeRef,
    name_text: &str,
) -> Result<SemanticSymbolId, VariablePlanError> {
    plan_variable_declaration(
        bound,
        store,
        declaration,
        name,
        name_text,
        VariableBindingKind::Var,
        false,
        true,
    )
}

/// Proves one recovered anonymous-module `var`, including its shared binder symbol.
pub(super) fn plan_recovered_anonymous_module_variable(
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    declaration: NodeRef,
    name: NodeRef,
    name_text: &str,
) -> Result<SemanticSymbolId, VariablePlanError> {
    plan_variable_declaration(
        bound,
        store,
        declaration,
        name,
        name_text,
        VariableBindingKind::Var,
        false,
        true,
    )
}

#[allow(clippy::too_many_arguments)]
fn plan_variable_declaration(
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    declaration: NodeRef,
    name: NodeRef,
    name_text: &str,
    binding: VariableBindingKind,
    exported: bool,
    allow_recovered_redeclarations: bool,
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
        bound,
        store,
        declaration,
        name,
        name_text,
        merged,
        binding.symbol_flags(),
        allow_recovered_redeclarations,
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
    let expected_flags = binding.declaration_flags();
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

/// Authenticates top-level object bindings and their nested property paths.
pub(super) fn plan_top_level_object_binding_elements(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    declaration: NodeRef,
    binding: VariableBindingKind,
    exported: bool,
) -> Result<Vec<PlannedObjectBindingElement>, VariablePlanError> {
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
    let expected_flags = binding.declaration_flags();
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
    if pattern_record.kind != SyntaxKind::ObjectBindingPattern
        || pattern_record.flags.0 != 0
        || pattern_data.elements.range != pattern_record.range
        || pattern_data.facts != 0
    {
        return Err(VariablePlanError::Unsupported(
            VariableUnsupported::BindingPattern(pattern),
        ));
    }

    let mut planned = Vec::with_capacity(pattern_data.elements.nodes.len());
    let mut names = HashSet::with_capacity(pattern_data.elements.nodes.len());
    plan_object_binding_pattern(
        arena,
        bound,
        store,
        pattern,
        binding,
        exported,
        &[],
        &mut names,
        &mut planned,
    )?;
    Ok(planned)
}

#[allow(clippy::too_many_arguments)]
fn plan_object_binding_pattern(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    pattern: NodeRef,
    binding: VariableBindingKind,
    exported: bool,
    parent_properties: &[PlannedObjectBindingProperty],
    names: &mut HashSet<SemanticSymbolId>,
    planned: &mut Vec<PlannedObjectBindingElement>,
) -> Result<(), VariablePlanError> {
    let pattern_record = arena
        .get(pattern.node)
        .ok_or(VariableInvariant::InvalidBindingPattern(pattern))?;
    let NodeData::BindingPattern(pattern_data) = &pattern_record.data else {
        return Err(VariablePlanError::Unsupported(
            VariableUnsupported::BindingPattern(pattern),
        ));
    };
    if pattern_record.kind != SyntaxKind::ObjectBindingPattern
        || pattern_record.flags.0 != 0
        || pattern_data.elements.range != pattern_record.range
        || pattern_data.facts != 0
        || !parent_properties.is_empty() && pattern_data.elements.nodes.is_empty()
    {
        return Err(VariablePlanError::Unsupported(
            VariableUnsupported::BindingPattern(pattern),
        ));
    }

    let source = bound.source_file();
    let mut excluded_properties = Vec::with_capacity(pattern_data.elements.nodes.len());
    let mut has_dynamic_computed_property = false;
    for (index, element) in pattern_data.elements.nodes.iter().enumerate() {
        let element = NodeRef::new(pattern.arena, pattern.file, *element);
        let element_record = binding_child_node(arena, store, element, pattern)?;
        let NodeData::BindingElement(data) = &element_record.data else {
            return Err(VariableInvariant::InvalidBindingPattern(element).into());
        };
        if element_record.kind != SyntaxKind::BindingElement
            || element_record.flags.0 != 0
            || data.flow_node.is_some()
            || data.local_symbol.is_some()
            || data.symbol.is_some()
            || data.facts != 0
        {
            return Err(VariablePlanError::Unsupported(
                VariableUnsupported::BindingPattern(element),
            ));
        }
        let name = data
            .name
            .map(|node| NodeRef::new(element.arena, element.file, node))
            .ok_or(VariableInvariant::InvalidBindingPattern(element))?;
        let name_record = binding_child_node(arena, store, name, element)?;
        let property = data
            .property_name
            .map_or(name, |node| NodeRef::new(element.arena, element.file, node));
        let property_record = if property == name {
            name_record
        } else {
            binding_child_node(arena, store, property, element)?
        };
        let mut computed_key = None;
        let property_name = match &property_record.data {
            NodeData::Identifier(property)
                if property_record.kind == SyntaxKind::Identifier
                    && property.flow_node.is_none() =>
            {
                property.text.clone()
            }
            NodeData::StringLiteral(property)
                if property_record.kind == SyntaxKind::StringLiteral
                    && property.token_flags.0 == 0 =>
            {
                property.text.clone()
            }
            NodeData::NumericLiteral(property)
                if property_record.kind == SyntaxKind::NumericLiteral
                    && property.token_flags.0 == 0 =>
            {
                property.text.clone()
            }
            NodeData::ComputedPropertyName(computed)
                if property_record.kind == SyntaxKind::ComputedPropertyName
                    && computed.facts == 0 =>
            {
                let key = NodeRef::new(property.arena, property.file, computed.expression);
                let key_record = binding_child_node(arena, store, key, property)?;
                if key_record.flags.0 != 0
                    || key_record.range.start < property_record.range.start
                    || key_record.range.end > property_record.range.end
                {
                    return Err(VariableInvariant::InvalidBindingPattern(key).into());
                }
                computed_key = Some(key);
                match &key_record.data {
                    NodeData::Identifier(key)
                        if key_record.kind == SyntaxKind::Identifier && key.flow_node.is_none() =>
                    {
                        key.text.clone()
                    }
                    NodeData::StringLiteral(key)
                        if key_record.kind == SyntaxKind::StringLiteral
                            && key.token_flags.0 == 0 =>
                    {
                        key.text.clone()
                    }
                    NodeData::NumericLiteral(key)
                        if key_record.kind == SyntaxKind::NumericLiteral
                            && key.token_flags.0 == 0 =>
                    {
                        key.text.clone()
                    }
                    NodeData::NoSubstitutionTemplateLiteral(key)
                        if key_record.kind == SyntaxKind::NoSubstitutionTemplateLiteral
                            && key.token_flags.0 == 0
                            && key.template_flags.0 == 0 =>
                    {
                        key.text.clone()
                    }
                    NodeData::CallExpression(call)
                        if key_record.kind == SyntaxKind::CallExpression
                            && call.question_dot_token.is_none()
                            && call.symbol.is_none()
                            && call.facts == 0
                            && call.type_arguments.is_none()
                            && call.arguments.nodes.is_empty()
                            && !call.arguments.has_trailing_comma =>
                    {
                        let callee = NodeRef::new(key.arena, key.file, call.expression);
                        let callee_record = binding_child_node(arena, store, callee, key)?;
                        let NodeData::Identifier(callee) = &callee_record.data else {
                            return Err(VariablePlanError::Unsupported(
                                VariableUnsupported::BindingPattern(key),
                            ));
                        };
                        if callee_record.kind != SyntaxKind::Identifier
                            || callee_record.flags.0 != 0
                            || callee.flow_node.is_some()
                        {
                            return Err(VariableInvariant::InvalidBindingPattern(key).into());
                        }
                        callee.text.clone()
                    }
                    _ => {
                        return Err(VariablePlanError::Unsupported(
                            VariableUnsupported::BindingPattern(key),
                        ));
                    }
                }
            }
            _ => {
                return Err(VariablePlanError::Unsupported(
                    VariableUnsupported::BindingPattern(property),
                ));
            }
        };
        if property_record.flags.0 != 0
            || property_name.is_empty()
            || property != name && property_record.range.end > name_record.range.start
        {
            return Err(VariableInvariant::InvalidBindingPattern(property).into());
        }

        let initializer = data
            .initializer
            .map(|node| NodeRef::new(element.arena, element.file, node));
        if let Some(initializer) = initializer {
            let initializer_record = binding_child_node(arena, store, initializer, element)?;
            if name_record.range.end > initializer_record.range.start
                || initializer_record.range.end != element_record.range.end
            {
                return Err(VariableInvariant::InvalidBindingPattern(initializer).into());
            }
        }

        let rest = data.dot_dot_dot_token.is_some();
        if let Some(spread) = data.dot_dot_dot_token {
            let spread = NodeRef::new(element.arena, element.file, spread);
            let spread_record = binding_child_node(arena, store, spread, element)?;
            if spread_record.kind != SyntaxKind::DotDotDotToken
                || spread_record.flags.0 != 0
                || !matches!(spread_record.data, NodeData::Token(_))
                || spread_record.range.start != element_record.range.start
                || spread_record.range.end > name_record.range.start
                || index + 1 != pattern_data.elements.nodes.len()
                || pattern_data.elements.has_trailing_comma
                || data.property_name.is_some()
                || initializer.is_some()
                || has_dynamic_computed_property
            {
                return Err(VariablePlanError::Unsupported(
                    VariableUnsupported::BindingPattern(element),
                ));
            }
        }

        if name_record.kind == SyntaxKind::ObjectBindingPattern {
            if rest
                || initializer.is_some()
                || data.property_name.is_none()
                || computed_key.is_some()
            {
                return Err(VariablePlanError::Unsupported(
                    VariableUnsupported::BindingPattern(element),
                ));
            }
            if bound.symbol(element).is_some() || bound.local_symbol(element).is_some() {
                return Err(VariableInvariant::InvalidBindingPattern(element).into());
            }
            excluded_properties.push(property_name.clone());
            let mut nested_properties = parent_properties.to_vec();
            nested_properties.push(PlannedObjectBindingProperty {
                property,
                property_name,
            });
            plan_object_binding_pattern(
                arena,
                bound,
                store,
                name,
                binding,
                exported,
                &nested_properties,
                names,
                planned,
            )?;
            continue;
        }

        let NodeData::Identifier(identifier) = &name_record.data else {
            return Err(VariablePlanError::Unsupported(
                VariableUnsupported::BindingPattern(name),
            ));
        };
        if name_record.kind != SyntaxKind::Identifier
            || name_record.flags.0 != 0
            || identifier.flow_node.is_some()
            || identifier.text.is_empty()
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
        if !names.insert(symbol)
            || bound.container(element) != Some(source)
            || bound.block_scope_container(element) != Some(source)
            || bound
                .locals(source)
                .and_then(|locals| store.symbol_table(locals))
                .and_then(|locals| locals.get_source(&identifier.text))
                != Some(local)
        {
            return Err(VariableInvariant::InvalidBindingPattern(element).into());
        }
        if !rest {
            has_dynamic_computed_property |= computed_key.is_some_and(|key| {
                matches!(
                    store.source_node_kind(key),
                    Some(SyntaxKind::Identifier | SyntaxKind::CallExpression)
                )
            });
            excluded_properties.push(property_name.clone());
        }
        planned.push(PlannedObjectBindingElement {
            element,
            property,
            property_name,
            computed_key,
            parent_properties: parent_properties.to_vec(),
            initializer,
            rest,
            excluded_properties: if rest {
                excluded_properties.clone()
            } else {
                Vec::new()
            },
            name,
            symbol,
        });
    }
    Ok(())
}

/// Authenticates empty array patterns, positional bindings, omissions, defaults, and rest.
pub(super) fn plan_top_level_array_binding_elements(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    declaration: NodeRef,
    binding: VariableBindingKind,
    exported: bool,
) -> Result<Vec<PlannedArrayBindingElement>, VariablePlanError> {
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
    let expected_flags = binding.declaration_flags();
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
    if pattern_record.kind != SyntaxKind::ArrayBindingPattern
        || pattern_record.flags.0 != 0
        || pattern_data.elements.range != pattern_record.range
        || pattern_data.facts != 0
    {
        return Err(VariablePlanError::Unsupported(
            VariableUnsupported::BindingPattern(pattern),
        ));
    }

    let mut planned = Vec::with_capacity(pattern_data.elements.nodes.len());
    let mut names = HashSet::with_capacity(pattern_data.elements.nodes.len());
    for (index, element) in pattern_data.elements.nodes.iter().enumerate() {
        let element = NodeRef::new(pattern.arena, pattern.file, *element);
        let element_record = binding_child_node(arena, store, element, pattern)?;
        if element_record.kind == SyntaxKind::OmittedExpression {
            if !matches!(element_record.data, NodeData::OmittedExpression(_))
                || element_record.flags.0 != 0
                || element_record.range.start != element_record.range.end
                || !bound.contains(element)
                || bound.symbol(element).is_some()
                || bound.local_symbol(element).is_some()
            {
                return Err(VariableInvariant::InvalidBindingPattern(element).into());
            }
            continue;
        }

        let NodeData::BindingElement(element_data) = &element_record.data else {
            return Err(VariablePlanError::Unsupported(
                VariableUnsupported::BindingPattern(element),
            ));
        };
        if element_record.kind != SyntaxKind::BindingElement
            || element_record.flags.0 != 0
            || element_data.flow_node.is_some()
            || element_data.local_symbol.is_some()
            || element_data.property_name.is_some()
            || element_data.symbol.is_some()
            || element_data.facts != 0
        {
            return Err(VariablePlanError::Unsupported(
                VariableUnsupported::BindingPattern(element),
            ));
        }

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
        {
            return Err(VariableInvariant::InvalidBindingPattern(name).into());
        }

        let initializer = element_data
            .initializer
            .map(|node| NodeRef::new(element.arena, element.file, node));
        if let Some(initializer) = initializer {
            let initializer_record = binding_child_node(arena, store, initializer, element)?;
            if name_record.range.end > initializer_record.range.start
                || initializer_record.range.end != element_record.range.end
            {
                return Err(VariableInvariant::InvalidBindingPattern(initializer).into());
            }
        }

        let rest = element_data.dot_dot_dot_token.is_some();
        if let Some(spread) = element_data.dot_dot_dot_token {
            let spread = NodeRef::new(element.arena, element.file, spread);
            let spread_record = binding_child_node(arena, store, spread, element)?;
            if spread_record.kind != SyntaxKind::DotDotDotToken
                || spread_record.flags.0 != 0
                || !matches!(spread_record.data, NodeData::Token(_))
                || spread_record.range.start != element_record.range.start
                || spread_record.range.end > name_record.range.start
                || index + 1 != pattern_data.elements.nodes.len()
                || pattern_data.elements.has_trailing_comma
                || initializer.is_some()
            {
                return Err(VariablePlanError::Unsupported(
                    VariableUnsupported::BindingPattern(element),
                ));
            }
        } else if initializer.is_none() && name_record.range != element_record.range {
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
        if !names.insert(symbol)
            || bound.container(element) != Some(source)
            || bound.block_scope_container(element) != Some(source)
            || bound
                .locals(source)
                .and_then(|locals| store.symbol_table(locals))
                .and_then(|locals| locals.get_source(&identifier.text))
                != Some(local)
        {
            return Err(VariableInvariant::InvalidBindingPattern(element).into());
        }

        planned.push(PlannedArrayBindingElement {
            declaration,
            pattern,
            element,
            index,
            initializer,
            rest,
            name,
            symbol,
        });
    }

    Ok(planned)
}

/// Retains the original exact one-element array-binding proof.
#[cfg(test)]
pub(super) fn plan_top_level_array_binding_element(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    declaration: NodeRef,
    binding: VariableBindingKind,
    exported: bool,
) -> Result<PlannedArrayBindingElement, VariablePlanError> {
    let planned =
        plan_top_level_array_binding_elements(arena, bound, store, declaration, binding, exported)?;
    match planned.as_slice() {
        [element]
            if element.index == 0
                && element.initializer.is_none()
                && !element.rest
                && arena.get(element.pattern.node).is_some_and(|record| {
                    matches!(
                        &record.data,
                        NodeData::BindingPattern(pattern) if !pattern.elements.has_trailing_comma
                    )
                }) =>
        {
            Ok(*element)
        }
        _ => Err(VariablePlanError::Unsupported(
            VariableUnsupported::BindingPattern(declaration),
        )),
    }
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
    plan_identifier_read_worker(
        arena,
        bound,
        store,
        host,
        prior_variables,
        readable_variables,
        node,
        name,
        false,
    )
}

/// Authenticates an explicitly annotated ambient declaration in the global scope.
pub(super) fn plan_cross_file_global_identifier_read(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    node: NodeRef,
    name: &str,
    declaration: NodeRef,
) -> Result<PlannedCrossFileGlobalRead, VariablePlanError> {
    let unsupported = || {
        VariablePlanError::Unsupported(VariableUnsupported::CrossFileDeclaration {
            node,
            declaration,
        })
    };
    if declaration.is_for(node.arena, node.file) {
        return Err(unsupported());
    }
    let (declaration_arena, declaration_bound) =
        host.source(declaration).ok_or_else(unsupported)?;
    let facts = declaration_bound.source_facts().ok_or_else(unsupported)?;
    if !facts.is_declaration_file()
        || facts.is_javascript_file()
        || facts.is_external_or_common_js_module()
    {
        return Err(unsupported());
    }

    let routed = resolve_cross_file_global_value_symbol(arena, bound, store, host, node, name)?
        .ok_or_else(unsupported)?;

    let record = store
        .symbol(routed.target)
        .ok_or(VariableInvariant::InvalidSymbol(routed.target))?;
    let binding = variable_binding_flags(record.flags()).ok_or_else(unsupported)?;
    if !host.symbol_matches(store, declaration, routed.target) {
        return Err(VariableInvariant::InvalidSymbolShape(routed.target).into());
    }
    let (name_node, type_node) = authenticated_cross_file_global_declaration(
        store,
        declaration_arena,
        declaration_bound,
        declaration,
        routed.target,
        name,
    )?
    .ok_or_else(unsupported)?;
    validate_variable_target(
        declaration_bound,
        store,
        declaration,
        name_node,
        name,
        routed.target,
        binding,
        false,
    )?;
    validate_target_parent(declaration_bound, store, routed.target, false)?;
    validate_value_links(store, routed.target)?;
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

    Ok(PlannedCrossFileGlobalRead {
        type_node,
        read: PlannedIdentifierRead {
            resolved_symbol: routed.resolved,
            value_symbol: routed.target,
        },
    })
}

fn resolve_cross_file_global_value_symbol(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    node: NodeRef,
    name: &str,
) -> Result<Option<RoutedValueSymbol>, VariablePlanError> {
    let mut callback_host = host
        .name_resolver_host(store)
        .map_err(VariablePlanError::DeclaredType)?;
    let mut name_lookup =
        CanonicalNameResolver::new(arena, bound, store.symbol_store(), &mut callback_host)
            .map_err(|error| name_resolution_error(node, error))?;
    let Some(resolved) = name_lookup
        .resolve(
            Some(CanonicalResolutionLocation::Bound(node)),
            name,
            SymbolFlags::VALUE | SymbolFlags::EXPORT_VALUE,
            None,
            false,
            false,
        )
        .map_err(|error| name_resolution_error(node, error))?
    else {
        return Ok(None);
    };
    let routed = route_value_symbol(store, node, resolved)?;
    let global = store
        .intrinsic_bootstrap()
        .and_then(|bootstrap| store.symbol_table(bootstrap.globals))
        .and_then(|globals| globals.get_source(name))
        .and_then(|symbol| store.get_merged_symbol(symbol));
    Ok((routed.export_local.is_none() && global == Some(routed.target)).then_some(routed))
}

fn authenticated_cross_file_global_declaration(
    store: &CanonicalTypeMapperStore,
    arena: &NodeArena,
    bound: &BoundFile,
    declaration: NodeRef,
    symbol: SemanticSymbolId,
    name: &str,
) -> Result<Option<(NodeRef, NodeRef)>, VariableInvariant> {
    let invalid = || VariableInvariant::InvalidSymbolShape(symbol);
    let declaration_record = arena.get(declaration.node).ok_or_else(invalid)?;
    let NodeData::VariableDeclaration(variable) = &declaration_record.data else {
        return Ok(None);
    };
    let name_node = NodeRef::new(declaration.arena, declaration.file, variable.name);
    let name_record = arena.get(name_node.node).ok_or_else(invalid)?;
    let NodeData::Identifier(identifier) = &name_record.data else {
        return Ok(None);
    };
    let Some(type_node) = variable
        .type_
        .map(|type_| NodeRef::new(declaration.arena, declaration.file, type_))
    else {
        return Ok(None);
    };
    let annotation = arena.get(type_node.node).ok_or_else(invalid)?;
    let Some(SourceNodeParent::Parent(list)) = store.source_node_parent(declaration) else {
        return Err(invalid());
    };
    let Some(SourceNodeParent::Parent(statement)) = store.source_node_parent(list) else {
        return Err(invalid());
    };
    let Some(SourceNodeParent::Parent(source)) = store.source_node_parent(statement) else {
        return Err(invalid());
    };
    let list_record = arena.get(list.node).ok_or_else(invalid)?;
    let NodeData::VariableDeclarationList(list_data) = &list_record.data else {
        return Err(invalid());
    };
    let statement_record = arena.get(statement.node).ok_or_else(invalid)?;
    let NodeData::VariableStatement(statement_data) = &statement_record.data else {
        return Err(invalid());
    };
    if declaration_record.kind != SyntaxKind::VariableDeclaration
        || declaration_record.flags.0 != 0
        || variable.initializer.is_some()
        || variable.exclamation_token.is_some()
        || variable.local_symbol.is_some()
        || variable.symbol.is_some()
        || variable.facts != 0
        || name_record.kind != SyntaxKind::Identifier
        || name_record.flags.0 != 0
        || name_record.parent != Some(declaration.node)
        || identifier.flow_node.is_some()
        || identifier.text != name
        || annotation.parent != Some(declaration.node)
        || store.source_node_parent(type_node) != Some(SourceNodeParent::Parent(declaration))
        || list_record.kind != SyntaxKind::VariableDeclarationList
        || list_data.facts != 0
        || !list_data.declarations.nodes.contains(&declaration.node)
        || statement_record.kind != SyntaxKind::VariableStatement
        || statement_data.declaration_list != list.node
        || statement_data.flow_node.is_some()
        || statement_data.facts != 0
        || source != bound.source_file()
        || bound.container(declaration) != Some(source)
        || bound.local_symbol(declaration).is_some()
        || bound
            .symbol(declaration)
            .and_then(|candidate| store.get_merged_symbol(candidate))
            != Some(symbol)
        || bound
            .locals(source)
            .and_then(|locals| store.symbol_table(locals))
            .and_then(|locals| locals.get_source(name))
            .and_then(|candidate| store.get_merged_symbol(candidate))
            != Some(symbol)
    {
        return Err(invalid());
    }
    Ok(Some((name_node, type_node)))
}

/// Resolves an authenticated recovered anonymous-module `var` redeclaration.
#[allow(clippy::too_many_arguments)]
pub(super) fn plan_recovered_anonymous_module_identifier_read(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    prior_variables: &HashSet<SemanticSymbolId>,
    readable_variables: &HashSet<SemanticSymbolId>,
    node: NodeRef,
    name: &str,
) -> Result<PlannedIdentifierRead, VariablePlanError> {
    plan_identifier_read_worker(
        arena,
        bound,
        store,
        host,
        prior_variables,
        readable_variables,
        node,
        name,
        true,
    )
}

#[allow(clippy::too_many_arguments)]
fn plan_identifier_read_worker(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    prior_variables: &HashSet<SemanticSymbolId>,
    readable_variables: &HashSet<SemanticSymbolId>,
    node: NodeRef,
    name: &str,
    allow_recovered_redeclarations: bool,
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
    let declaration = single_variable_declaration(
        bound,
        store,
        node,
        routed.target,
        flags,
        declarations,
        true,
        allow_recovered_redeclarations,
    )?;
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

#[allow(clippy::too_many_arguments)]
fn validate_variable_target(
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    declaration: NodeRef,
    name: NodeRef,
    name_text: &str,
    symbol: SemanticSymbolId,
    expected_flags: SymbolFlags,
    allow_recovered_redeclarations: bool,
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
        bound,
        store,
        declaration,
        symbol,
        record.flags(),
        declarations,
        false,
        allow_recovered_redeclarations,
    )?;
    if actual != declaration
        && (!allow_recovered_redeclarations
            || expected_flags != SymbolFlags::FUNCTION_SCOPED_VARIABLE
            || !declarations.contains(&declaration))
    {
        return Err(VariableInvariant::InvalidSymbolShape(symbol).into());
    }
    if record.value_declaration() != Some(actual) {
        return Err(VariableInvariant::ValueDeclarationMismatch {
            symbol,
            declaration: actual,
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
    let merged = flags.intersects(SymbolFlags::INTERFACE | SymbolFlags::NAMESPACE_MODULE);
    let allowed = binding
        | SymbolFlags::INTERFACE
        | SymbolFlags::NAMESPACE_MODULE
        | if merged {
            SymbolFlags::TRANSIENT
        } else {
            SymbolFlags::NONE
        };
    (flags.without(allowed) == SymbolFlags::NONE).then_some(binding)
}

fn is_nonambient_variable_declaration(
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    declaration: NodeRef,
) -> bool {
    if bound
        .source_facts()
        .is_some_and(ts_binder::CanonicalSourceFileFacts::is_declaration_file)
    {
        return false;
    }
    let Some(SourceNodeParent::Parent(list)) = store.source_node_parent(declaration) else {
        return false;
    };
    let Some(SourceNodeParent::Parent(statement)) = store.source_node_parent(list) else {
        return false;
    };
    if store.source_node_kind(list) != Some(SyntaxKind::VariableDeclarationList)
        || store.source_node_kind(statement) != Some(SyntaxKind::VariableStatement)
    {
        return false;
    }
    !bound.traversal_order().any(|node| {
        store.source_node_kind(node) == Some(SyntaxKind::DeclareKeyword)
            && store.source_node_parent(node) == Some(SourceNodeParent::Parent(statement))
    })
}

#[allow(clippy::too_many_arguments)]
fn single_variable_declaration(
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    node: NodeRef,
    symbol: SemanticSymbolId,
    flags: SymbolFlags,
    declarations: &[NodeRef],
    allow_parameter: bool,
    allow_recovered_redeclarations: bool,
) -> Result<NodeRef, VariablePlanError> {
    let mut variable = None;
    for declaration in declarations.iter().copied() {
        match store.source_node_kind(declaration) {
            Some(SyntaxKind::VariableDeclaration | SyntaxKind::BindingElement)
                if variable.is_none() =>
            {
                variable = Some(declaration);
            }
            Some(SyntaxKind::VariableDeclaration)
                if allow_recovered_redeclarations
                    && flags == SymbolFlags::FUNCTION_SCOPED_VARIABLE
                    && variable.is_some_and(|first| {
                        declaration.file == first.file
                            && declaration.arena == first.arena
                            && is_nonambient_variable_declaration(bound, store, first)
                            && is_nonambient_variable_declaration(bound, store, declaration)
                            && bound.symbol(declaration) == Some(symbol)
                            && bound.local_symbol(declaration).is_none()
                            && bound.container(declaration) == bound.container(first)
                            && bound.container(declaration) == Some(bound.source_file())
                    }) => {}
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
    fn using_bindings_preserve_immutable_block_scoped_symbol_identity() {
        for (index, (source, binding, expected_flags)) in [
            ("using resource = null;", VariableBindingKind::Using, 1 << 2),
            (
                "await using resource = null;",
                VariableBindingKind::AwaitUsing,
                (1 << 1) | (1 << 2),
            ),
        ]
        .into_iter()
        .enumerate()
        {
            let fixture = binding_fixture(source, 9_410 + u32::try_from(index).unwrap());
            let declaration = fixture
                .parsed
                .arena
                .iter()
                .find_map(|(node, record)| {
                    (record.kind == SyntaxKind::VariableDeclaration).then_some(NodeRef::new(
                        fixture.parsed.arena.id(),
                        fixture.file,
                        node,
                    ))
                })
                .expect("the resource declaration retains its variable node");
            let NodeData::VariableDeclaration(variable) =
                &fixture.parsed.arena.get(declaration.node).unwrap().data
            else {
                panic!("expected an identifier-named resource declaration")
            };
            let name = NodeRef::new(fixture.parsed.arena.id(), fixture.file, variable.name);
            let list = fixture
                .parsed
                .arena
                .get(declaration.node)
                .and_then(|record| record.parent)
                .and_then(|parent| fixture.parsed.arena.get(parent))
                .unwrap();
            let symbol = fixture.bound.symbol(declaration).unwrap();

            assert_eq!(list.flags.0, expected_flags);
            assert!(binding.is_const());
            assert!(binding.is_using());
            assert_eq!(
                fixture.store.symbol(symbol).unwrap().flags(),
                SymbolFlags::BLOCK_SCOPED_VARIABLE,
            );
            assert_eq!(
                plan_top_level_variable(
                    &fixture.bound,
                    &fixture.store,
                    declaration,
                    name,
                    "resource",
                    binding,
                    false,
                ),
                Ok(symbol),
            );
            assert!(fixture.store.value_symbol_links(symbol).is_none());
        }
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
    fn object_binding_elements_preserve_shorthand_renames_and_trailing_commas() {
        let fixture = binding_fixture(
            "const { first, second: renamed, 'third-key': third, } = input;",
            9_370,
        );
        let declaration = binding_declaration(&fixture);
        let planned = plan_top_level_object_binding_elements(
            &fixture.parsed.arena,
            &fixture.bound,
            &fixture.store,
            declaration,
            VariableBindingKind::Const,
            false,
        )
        .unwrap();

        assert_eq!(
            planned
                .iter()
                .map(|element| element.property_name.as_str())
                .collect::<Vec<_>>(),
            ["first", "second", "third-key"],
        );
        for element in &planned {
            assert_eq!(fixture.bound.symbol(element.element), Some(element.symbol));
            assert_eq!(
                fixture.store.symbol(element.symbol).unwrap().declarations(),
                Some(&[element.element][..]),
            );
            assert!(fixture.store.value_symbol_links(element.symbol).is_none());
        }
        let warm = (
            fixture.store.type_len(),
            fixture.store.checker_link_allocated_lengths(),
        );
        assert_eq!(
            plan_top_level_object_binding_elements(
                &fixture.parsed.arena,
                &fixture.bound,
                &fixture.store,
                declaration,
                VariableBindingKind::Const,
                false,
            ),
            Ok(planned),
        );
        assert_eq!(
            (
                fixture.store.type_len(),
                fixture.store.checker_link_allocated_lengths(),
            ),
            warm,
        );
    }

    #[test]
    fn mixed_computed_object_bindings_preserve_keys_and_binder_owned_symbols() {
        let fixture = binding_fixture(
            concat!(
                "let key = 'dynamic'; let getKey = () => 'called'; ",
                "const { fixed, ['literal']: literal, [key]: dynamic, ",
                "[getKey()]: called } = input;",
            ),
            10_320,
        );
        let declaration = binding_declaration(&fixture);
        let before = (
            fixture.store.type_len(),
            fixture.store.symbol_len(),
            fixture.store.checker_link_allocated_lengths(),
        );

        let planned = plan_top_level_object_binding_elements(
            &fixture.parsed.arena,
            &fixture.bound,
            &fixture.store,
            declaration,
            VariableBindingKind::Const,
            false,
        )
        .unwrap();

        assert_eq!(planned.len(), 4);
        assert!(planned[0].computed_key.is_none());
        for (element, kind) in planned[1..].iter().zip([
            SyntaxKind::StringLiteral,
            SyntaxKind::Identifier,
            SyntaxKind::CallExpression,
        ]) {
            let key = element.computed_key.unwrap();
            assert_eq!(fixture.store.source_node_kind(key), Some(kind));
            assert_eq!(
                fixture.store.source_node_parent(key),
                Some(SourceNodeParent::Parent(element.property)),
            );
            assert_eq!(fixture.bound.symbol(element.element), Some(element.symbol));
            assert!(fixture.store.value_symbol_links(element.symbol).is_none());
        }
        assert_eq!(
            (
                fixture.store.type_len(),
                fixture.store.symbol_len(),
                fixture.store.checker_link_allocated_lengths(),
            ),
            before,
        );
    }

    #[test]
    fn literal_computed_binding_defaults_preserve_object_rest_exclusions() {
        let fixture = binding_fixture(
            "const { ['optional']: selected = 'fallback', ...remaining } = input;",
            10_322,
        );
        let declaration = binding_declaration(&fixture);
        let before = (
            fixture.store.type_len(),
            fixture.store.symbol_len(),
            fixture.store.checker_link_allocated_lengths(),
        );

        let planned = plan_top_level_object_binding_elements(
            &fixture.parsed.arena,
            &fixture.bound,
            &fixture.store,
            declaration,
            VariableBindingKind::Const,
            false,
        )
        .unwrap();

        let [selected, rest] = planned.as_slice() else {
            panic!("expected one defaulted computed binding and one object rest binding")
        };
        assert_eq!(selected.property_name, "optional");
        assert!(selected.computed_key.is_some());
        assert!(selected.initializer.is_some());
        assert!(rest.rest);
        assert_eq!(rest.excluded_properties, vec!["optional".to_owned()]);
        assert_eq!(
            (
                fixture.store.type_len(),
                fixture.store.symbol_len(),
                fixture.store.checker_link_allocated_lengths(),
            ),
            before,
        );
    }

    #[test]
    fn dynamic_computed_object_keys_do_not_forge_rest_exclusions() {
        let fixture = binding_fixture("const { [key]: selected, ...remaining } = input;", 10_321);
        let declaration = binding_declaration(&fixture);
        let before = (
            fixture.store.type_len(),
            fixture.store.symbol_len(),
            fixture.store.checker_link_allocated_lengths(),
        );

        assert!(matches!(
            plan_top_level_object_binding_elements(
                &fixture.parsed.arena,
                &fixture.bound,
                &fixture.store,
                declaration,
                VariableBindingKind::Const,
                false,
            ),
            Err(VariablePlanError::Unsupported(
                VariableUnsupported::BindingPattern(_)
            ))
        ));
        assert_eq!(
            (
                fixture.store.type_len(),
                fixture.store.symbol_len(),
                fixture.store.checker_link_allocated_lengths(),
            ),
            before,
        );
    }

    #[test]
    fn object_binding_elements_preserve_defaults_nested_paths_and_rest_exclusions() {
        let fixture = binding_fixture(
            "const { first = 1, nested: { second: renamed = 2 }, ...remaining } = input;",
            9_391,
        );
        let declaration = binding_declaration(&fixture);
        let planned = plan_top_level_object_binding_elements(
            &fixture.parsed.arena,
            &fixture.bound,
            &fixture.store,
            declaration,
            VariableBindingKind::Const,
            false,
        )
        .unwrap();

        let [first, nested, remaining] = planned.as_slice() else {
            panic!("expected one default, one nested binding, and one rest binding")
        };
        assert_eq!(first.property_name, "first");
        assert!(first.initializer.is_some());
        assert!(first.parent_properties.is_empty());
        assert_eq!(nested.property_name, "second");
        assert_eq!(nested.parent_properties.len(), 1);
        assert_eq!(nested.parent_properties[0].property_name, "nested");
        assert!(nested.initializer.is_some());
        assert!(remaining.rest);
        assert_eq!(
            remaining.excluded_properties,
            vec!["first".to_owned(), "nested".to_owned()],
        );
        for element in &planned {
            assert_eq!(fixture.bound.symbol(element.element), Some(element.symbol));
            assert!(fixture.store.value_symbol_links(element.symbol).is_none());
        }

        let warm = (
            fixture.store.type_len(),
            fixture.store.checker_link_allocated_lengths(),
        );
        assert_eq!(
            plan_top_level_object_binding_elements(
                &fixture.parsed.arena,
                &fixture.bound,
                &fixture.store,
                declaration,
                VariableBindingKind::Const,
                false,
            ),
            Ok(planned),
        );
        assert_eq!(
            (
                fixture.store.type_len(),
                fixture.store.checker_link_allocated_lengths(),
            ),
            warm,
        );

        let empty = binding_fixture("const {} = input;", 9_392);
        let declaration = binding_declaration(&empty);
        assert_eq!(
            plan_top_level_object_binding_elements(
                &empty.parsed.arena,
                &empty.bound,
                &empty.store,
                declaration,
                VariableBindingKind::Const,
                false,
            ),
            Ok(Vec::new()),
        );
    }

    #[test]
    fn object_binding_elements_reject_unsupported_nested_shapes_and_poisoned_links() {
        for (index, source) in [
            "const { nested: {} } = input;",
            "const { nested: { value } = {} } = input;",
            "const { nested: [value] } = input;",
        ]
        .into_iter()
        .enumerate()
        {
            let fixture = binding_fixture(source, 9_380 + u32::try_from(index).unwrap());
            let declaration = binding_declaration(&fixture);
            assert!(matches!(
                plan_top_level_object_binding_elements(
                    &fixture.parsed.arena,
                    &fixture.bound,
                    &fixture.store,
                    declaration,
                    VariableBindingKind::Const,
                    false,
                ),
                Err(VariablePlanError::Unsupported(
                    VariableUnsupported::BindingPattern(_)
                )),
            ));
        }

        let mut fixture = binding_fixture("const { value } = input;", 9_390);
        let declaration = binding_declaration(&fixture);
        let planned = plan_top_level_object_binding_elements(
            &fixture.parsed.arena,
            &fixture.bound,
            &fixture.store,
            declaration,
            VariableBindingKind::Const,
            false,
        )
        .unwrap();
        let symbol = planned[0].symbol;
        let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
        let links = ValueSymbolLinks {
            resolved_type: Some(bootstrap.error_type),
            write_type: Some(bootstrap.number_type),
            ..ValueSymbolLinks::default()
        };
        assert!(fixture.store.set_value_symbol_links(symbol, links));
        let poisoned = fixture.store.checker_link_allocated_lengths();
        assert_eq!(
            plan_top_level_object_binding_elements(
                &fixture.parsed.arena,
                &fixture.bound,
                &fixture.store,
                declaration,
                VariableBindingKind::Const,
                false,
            ),
            Err(VariablePlanError::Invariant(
                VariableInvariant::InvalidValueLinks(symbol)
            )),
        );
        assert_eq!(fixture.store.checker_link_allocated_lengths(), poisoned);
    }

    #[test]
    fn array_binding_elements_preserve_symbol_identity_reads_and_warm_links() {
        for (index, (source, binding, expected_flags)) in [
            (
                "declare var source: string[]; var [value] = source; var observed = value;",
                VariableBindingKind::Var,
                SymbolFlags::FUNCTION_SCOPED_VARIABLE,
            ),
            (
                "declare var source: string[]; let [value] = source; var observed = value;",
                VariableBindingKind::Let,
                SymbolFlags::BLOCK_SCOPED_VARIABLE,
            ),
            (
                "declare var source: string[]; const [value] = source; var observed = value;",
                VariableBindingKind::Const,
                SymbolFlags::BLOCK_SCOPED_VARIABLE,
            ),
        ]
        .into_iter()
        .enumerate()
        {
            let mut fixture = binding_fixture(source, 9_340 + u32::try_from(index).unwrap());
            let declaration = binding_declaration(&fixture);
            let plans = plan_top_level_array_binding_elements(
                &fixture.parsed.arena,
                &fixture.bound,
                &fixture.store,
                declaration,
                binding,
                false,
            )
            .unwrap();
            let [plan] = plans.as_slice() else {
                panic!("expected exactly one array binding")
            };
            let plan = *plan;

            assert!(fixture.bound.symbol(declaration).is_none());
            assert_eq!(fixture.bound.symbol(plan.element), Some(plan.symbol));
            assert_eq!(
                fixture.store.symbol(plan.symbol).unwrap().flags(),
                expected_flags
            );
            assert_eq!(
                fixture.store.symbol(plan.symbol).unwrap().declarations(),
                Some(&[plan.element][..])
            );
            assert_eq!(
                fixture.store.source_node_parent(plan.name),
                Some(SourceNodeParent::Parent(plan.element))
            );
            assert!(fixture.store.value_symbol_links(plan.symbol).is_none());
            assert_eq!(
                plan_top_level_variable(
                    &fixture.bound,
                    &fixture.store,
                    plan.element,
                    plan.name,
                    "value",
                    binding,
                    false,
                ),
                Ok(plan.symbol)
            );

            let read =
                fixture
                    .parsed
                    .arena
                    .iter()
                    .find_map(|(node, record)| {
                        let NodeData::Identifier(identifier) = &record.data else {
                            return None;
                        };
                        (identifier.text == "value" && node != plan.name.node)
                            .then_some(NodeRef::new(fixture.parsed.arena.id(), fixture.file, node))
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

            let links = ValueSymbolLinks {
                resolved_type: Some(fixture.store.intrinsic_bootstrap().unwrap().error_type),
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
                plan_top_level_array_binding_elements(
                    &fixture.parsed.arena,
                    &fixture.bound,
                    &fixture.store,
                    declaration,
                    binding,
                    false,
                ),
                Ok(vec![plan])
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
    }

    #[test]
    fn array_binding_elements_preserve_positions_defaults_rest_and_warm_links() {
        let fixture = binding_fixture("var [, first, , second = 2, ...remaining] = source;", 9_361);
        let declaration = binding_declaration(&fixture);
        let planned = plan_top_level_array_binding_elements(
            &fixture.parsed.arena,
            &fixture.bound,
            &fixture.store,
            declaration,
            VariableBindingKind::Var,
            false,
        )
        .unwrap();

        let [first, second, remaining] = planned.as_slice() else {
            panic!("expected two positional bindings and one rest binding")
        };
        assert_eq!(first.index, 1);
        assert!(first.initializer.is_none());
        assert_eq!(second.index, 3);
        assert!(second.initializer.is_some());
        assert_eq!(remaining.index, 4);
        assert!(remaining.rest);
        for element in &planned {
            assert_eq!(fixture.bound.symbol(element.element), Some(element.symbol));
            assert!(fixture.store.value_symbol_links(element.symbol).is_none());
        }

        let warm = (
            fixture.store.type_len(),
            fixture.store.checker_link_allocated_lengths(),
        );
        assert_eq!(
            plan_top_level_array_binding_elements(
                &fixture.parsed.arena,
                &fixture.bound,
                &fixture.store,
                declaration,
                VariableBindingKind::Var,
                false,
            ),
            Ok(planned),
        );
        assert_eq!(
            (
                fixture.store.type_len(),
                fixture.store.checker_link_allocated_lengths(),
            ),
            warm,
        );

        let trailing = binding_fixture("var [, value,] = source;", 9_362);
        let declaration = binding_declaration(&trailing);
        let planned = plan_top_level_array_binding_elements(
            &trailing.parsed.arena,
            &trailing.bound,
            &trailing.store,
            declaration,
            VariableBindingKind::Var,
            false,
        )
        .unwrap();
        assert_eq!(planned.len(), 1);
        assert_eq!(planned[0].index, 1);
    }

    #[test]
    fn array_binding_elements_preserve_omitted_positions_and_trailing_commas() {
        for (index, (source, binding, names, positions)) in [
            (
                "declare var source: string[]; var [, second, , fourth] = source;",
                VariableBindingKind::Var,
                ["second", "fourth"].as_slice(),
                [1_usize, 3].as_slice(),
            ),
            (
                "declare var source: string[]; let [, second, , fourth, ,] = source;",
                VariableBindingKind::Let,
                ["second", "fourth"].as_slice(),
                [1_usize, 3].as_slice(),
            ),
            (
                "declare var source: string[]; const [value,] = source;",
                VariableBindingKind::Const,
                ["value"].as_slice(),
                [0_usize].as_slice(),
            ),
        ]
        .into_iter()
        .enumerate()
        {
            let fixture = binding_fixture(source, 9_370 + u32::try_from(index).unwrap());
            let declaration = binding_declaration(&fixture);
            let before = (
                fixture.store.type_len(),
                fixture.store.checker_link_allocated_lengths(),
            );

            let planned = plan_top_level_array_binding_elements(
                &fixture.parsed.arena,
                &fixture.bound,
                &fixture.store,
                declaration,
                binding,
                false,
            )
            .unwrap_or_else(|error| panic!("{source}: {error:?}"));

            assert_eq!(planned.len(), names.len(), "{source}");
            for ((element, name), position) in planned.iter().zip(names).zip(positions) {
                let record = fixture.parsed.arena.get(element.name.node).unwrap();
                let NodeData::Identifier(identifier) = &record.data else {
                    panic!("expected an authenticated identifier binding")
                };
                assert_eq!(identifier.text, *name);
                assert_eq!(fixture.bound.symbol(element.element), Some(element.symbol));
                let NodeData::BindingPattern(pattern) =
                    &fixture.parsed.arena.get(element.pattern.node).unwrap().data
                else {
                    panic!("expected the owning array pattern")
                };
                assert_eq!(pattern.elements.nodes[*position], element.element.node);
            }
            assert_eq!(
                (
                    fixture.store.type_len(),
                    fixture.store.checker_link_allocated_lengths(),
                ),
                before,
                "{source}",
            );
        }
    }

    #[test]
    fn empty_and_omission_only_array_bindings_retain_authenticated_patterns() {
        for (index, (source, binding)) in [
            ("var [] = source;", VariableBindingKind::Var),
            ("let [,] = source;", VariableBindingKind::Let),
            ("const [,,] = source;", VariableBindingKind::Const),
        ]
        .into_iter()
        .enumerate()
        {
            let fixture = binding_fixture(source, 9_395 + u32::try_from(index).unwrap());
            let declaration = binding_declaration(&fixture);
            let before = (
                fixture.store.type_len(),
                fixture.store.checker_link_allocated_lengths(),
            );

            assert_eq!(
                plan_top_level_array_binding_elements(
                    &fixture.parsed.arena,
                    &fixture.bound,
                    &fixture.store,
                    declaration,
                    binding,
                    false,
                ),
                Ok(Vec::new()),
                "{source}",
            );
            assert_eq!(
                (
                    fixture.store.type_len(),
                    fixture.store.checker_link_allocated_lengths(),
                ),
                before,
                "{source}",
            );
        }
    }

    #[test]
    fn array_binding_elements_reject_unsupported_shapes_and_poisoned_links() {
        for (index, source) in ["var [[value]] = source;", "var { value } = source;"]
            .into_iter()
            .enumerate()
        {
            let fixture = binding_fixture(source, 9_350 + u32::try_from(index).unwrap());
            let declaration = binding_declaration(&fixture);
            assert!(
                matches!(
                    plan_top_level_array_binding_elements(
                        &fixture.parsed.arena,
                        &fixture.bound,
                        &fixture.store,
                        declaration,
                        VariableBindingKind::Var,
                        false,
                    ),
                    Err(VariablePlanError::Unsupported(
                        VariableUnsupported::BindingPattern(_)
                    ))
                ),
                "{source}"
            );
        }

        for (index, source) in [
            "var [first, second] = source;",
            "var [value,] = source;",
            "var [value = 0] = source;",
            "var [...value] = source;",
        ]
        .into_iter()
        .enumerate()
        {
            let fixture = binding_fixture(source, 9_380 + u32::try_from(index).unwrap());
            let declaration = binding_declaration(&fixture);
            assert!(
                matches!(
                    plan_top_level_array_binding_element(
                        &fixture.parsed.arena,
                        &fixture.bound,
                        &fixture.store,
                        declaration,
                        VariableBindingKind::Var,
                        false,
                    ),
                    Err(VariablePlanError::Unsupported(
                        VariableUnsupported::BindingPattern(_)
                    ))
                ),
                "{source}"
            );
        }

        let mut fixture = binding_fixture("var [value] = source;", 9_360);
        let declaration = binding_declaration(&fixture);
        let plans = plan_top_level_array_binding_elements(
            &fixture.parsed.arena,
            &fixture.bound,
            &fixture.store,
            declaration,
            VariableBindingKind::Var,
            false,
        )
        .unwrap();
        let [plan] = plans.as_slice() else {
            panic!("expected exactly one array binding")
        };
        let plan = *plan;
        let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
        let links = ValueSymbolLinks {
            resolved_type: Some(bootstrap.error_type),
            write_type: Some(bootstrap.number_type),
            ..ValueSymbolLinks::default()
        };
        assert!(fixture.store.set_value_symbol_links(plan.symbol, links));
        let poisoned = fixture.store.checker_link_allocated_lengths();
        assert_eq!(
            plan_top_level_array_binding_elements(
                &fixture.parsed.arena,
                &fixture.bound,
                &fixture.store,
                declaration,
                VariableBindingKind::Var,
                false,
            ),
            Err(VariablePlanError::Invariant(
                VariableInvariant::InvalidValueLinks(plan.symbol)
            ))
        );
        assert_eq!(fixture.store.checker_link_allocated_lengths(), poisoned);
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
    fn transient_variable_symbols_require_an_authenticated_merge_facet() {
        assert_eq!(
            variable_binding_flags(
                SymbolFlags::FUNCTION_SCOPED_VARIABLE
                    | SymbolFlags::INTERFACE
                    | SymbolFlags::TRANSIENT,
            ),
            Some(SymbolFlags::FUNCTION_SCOPED_VARIABLE),
        );
        assert_eq!(
            variable_binding_flags(
                SymbolFlags::FUNCTION_SCOPED_VARIABLE
                    | SymbolFlags::NAMESPACE_MODULE
                    | SymbolFlags::TRANSIENT,
            ),
            Some(SymbolFlags::FUNCTION_SCOPED_VARIABLE),
        );
        assert_eq!(
            variable_binding_flags(SymbolFlags::FUNCTION_SCOPED_VARIABLE | SymbolFlags::TRANSIENT),
            None,
        );
        assert_eq!(
            variable_binding_flags(
                SymbolFlags::FUNCTION_SCOPED_VARIABLE
                    | SymbolFlags::INTERFACE
                    | SymbolFlags::FUNCTION
                    | SymbolFlags::TRANSIENT,
            ),
            None,
        );
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
    fn repeated_function_scoped_variables_share_one_symbol_and_value_declaration() {
        let mut fixture = binding_fixture(
            "var shared = 1; { var shared = 2; } var observed = shared;",
            930,
        );
        let declarations = fixture
            .parsed
            .arena
            .iter()
            .filter_map(|(node, record)| {
                let NodeData::VariableDeclaration(declaration) = &record.data else {
                    return None;
                };
                let NodeData::Identifier(identifier) =
                    &fixture.parsed.arena.get(declaration.name)?.data
                else {
                    return None;
                };
                (identifier.text == "shared").then_some((
                    NodeRef::new(fixture.parsed.arena.id(), fixture.file, node),
                    NodeRef::new(fixture.parsed.arena.id(), fixture.file, declaration.name),
                ))
            })
            .collect::<Vec<_>>();
        let [(first, _), (second, _)] = declarations.as_slice() else {
            panic!("expected two declarations of the same function-scoped variable")
        };
        let symbol = fixture.bound.symbol(*first).unwrap();

        assert_eq!(fixture.bound.symbol(*second), Some(symbol));
        assert_eq!(
            fixture.store.symbol(symbol).unwrap().value_declaration(),
            Some(*first),
        );
        for &(declaration, name) in &declarations {
            assert_eq!(
                plan_recovered_anonymous_module_variable(
                    &fixture.bound,
                    &fixture.store,
                    declaration,
                    name,
                    "shared",
                ),
                Ok(symbol),
            );
            assert_eq!(
                plan_redeclared_top_level_variable(
                    &fixture.bound,
                    &fixture.store,
                    declaration,
                    name,
                    "shared",
                ),
                Ok(symbol),
            );
        }

        let read = fixture
            .parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                let NodeData::Identifier(identifier) = &record.data else {
                    return None;
                };
                (identifier.text == "shared"
                    && !declarations.iter().any(|(_, name)| name.node == node))
                .then_some(NodeRef::new(fixture.parsed.arena.id(), fixture.file, node))
            })
            .unwrap();
        let globals = fixture.store.intrinsic_bootstrap().unwrap().globals;
        assert_eq!(
            fixture.store.merge_global_symbol(globals, symbol),
            Ok(symbol)
        );
        let host = DeclaredTypeHost::new_after_global_merge(
            [(&fixture.parsed.arena, &fixture.bound)],
            GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
        )
        .unwrap();

        assert_eq!(
            plan_recovered_anonymous_module_identifier_read(
                &fixture.parsed.arena,
                &fixture.bound,
                &fixture.store,
                &host,
                &HashSet::from([symbol]),
                &HashSet::from([symbol]),
                read,
                "shared",
            ),
            Ok(PlannedIdentifierRead {
                resolved_symbol: symbol,
                value_symbol: symbol,
            }),
        );

        assert!(matches!(
            plan_top_level_variable(
                &fixture.bound,
                &fixture.store,
                *first,
                declarations[0].1,
                "shared",
                VariableBindingKind::Var,
                false,
            ),
            Err(VariablePlanError::Unsupported(
                VariableUnsupported::NonUniqueDeclaration { .. }
            )),
        ));
        assert!(matches!(
            plan_identifier_read(
                &fixture.parsed.arena,
                &fixture.bound,
                &fixture.store,
                &host,
                &HashSet::from([symbol]),
                &HashSet::from([symbol]),
                read,
                "shared",
            ),
            Err(VariablePlanError::Unsupported(
                VariableUnsupported::NonUniqueDeclaration { .. }
            )),
        ));
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
