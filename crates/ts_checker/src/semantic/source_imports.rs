//! Exact source planning for direct named TypeScript ESM value imports.
//!
//! This first slice accepts only leading, top-level imports of the form
//! `import { exported as local } from "./target"`. The import and every
//! specifier must be value-bearing, identifier-named, modifier-free, and
//! attribute-free. Alias discovery is delegated to the production alias host;
//! a successful alias must point directly at one unique, initialized,
//! annotated, explicitly exported `const` declaration in another retained
//! TypeScript ESM source.
//!
//! Source integration separates declaration checking from value use. Every
//! binding is resolved through [`resolve_source_import_binding`], including
//! unused imports, while [`prepare_source_import_value`] queries the target's
//! annotation only for a proven later value read. Preparation returns eventual
//! target/alias value-link payloads without publishing them. After the whole
//! source has checked, [`preflight_prepared_source_import_publications`]
//! validates and exposes those payloads for the source checker's one combined
//! atomic publication batch. Importer-first Program order never recursively
//! checks the target source: `CanonicalTypeQuery` reads its annotation lazily.
//!
//! The split follows the pinned TypeScript-Go paths in
//! `internal/checker/checker.go`: `checkImportDeclaration` proves import
//! bindings, `resolveAlias` selects the direct export, `getTypeOfAlias` owns
//! the alias value cache, and `getTypeOfVariableOrParameterOrProperty` obtains
//! the annotated target value type.

use std::collections::{HashMap, HashSet};

use ts_ast::{Node, NodeArena, NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    BoundFile, CanonicalNameResolutionError, CanonicalNameResolver, CanonicalResolutionLocation,
    CheckFlags, SemanticSymbolId, SymbolFlags,
};

use super::{
    AliasTargetState, CanonicalCheckerDiagnostics, CanonicalCheckerOptions, CanonicalGlobalTypes,
    CanonicalTypeMapperStore, DeclaredTypeError, DeclaredTypeHost, ProductionAliasTargetHost,
    TypeId, TypeNodeLinks, ValueSymbolLinks,
    alias::{
        CanonicalAliasResolutionError, CanonicalAliasResolutionEvent, CanonicalAliasResolver,
        CanonicalAliasTargetHost, CanonicalImmediateAliasTarget,
    },
    type_nodes::{CanonicalTypeQuery, CanonicalTypeReferenceAliasTarget},
    variables::{VariableBindingKind, VariablePlanError, plan_top_level_variable},
};

const NODE_FLAG_CONST: u32 = 1 << 1;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[cfg_attr(not(test), allow(dead_code))]
enum SourceImportPhase {
    Value,
    Type,
}

/// One exact local binding introduced by a supported named import.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct SourceImportBindingPlan {
    pub(super) declaration: NodeRef,
    pub(super) imported_name: NodeRef,
    pub(super) local_name: NodeRef,
    pub(super) imported_text: String,
    pub(super) local_text: String,
    pub(super) alias_symbol: SemanticSymbolId,
}

/// Read-only plan for one complete top-level named import statement.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct SourceImportPlan {
    pub(super) declaration: NodeRef,
    pub(super) module_specifier: NodeRef,
    pub(super) bindings: Vec<SourceImportBindingPlan>,
}

/// A later identifier expression proven to read one planned import binding.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct PlannedSourceImportRead {
    pub(super) node: NodeRef,
    pub(super) resolved_symbol: SemanticSymbolId,
    pub(super) value_symbol: SemanticSymbolId,
}

/// A binding whose direct alias target has been resolved without querying its
/// value type. Every import declaration uses this state, including imports
/// that have no value read in the checked source.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct ResolvedSourceImportBinding {
    pub(super) binding: SourceImportBindingPlan,
    pub(super) target_symbol: SemanticSymbolId,
}

/// One independently resolved type-only binding whose direct target is a
/// simple exported type declaration in another retained ESM source.
#[derive(Clone, Debug, Eq, PartialEq)]
#[cfg_attr(not(test), allow(dead_code))]
pub(super) struct ResolvedSourceTypeImportBinding {
    pub(super) binding: SourceImportBindingPlan,
    pub(super) target_symbol: SemanticSymbolId,
    pub(super) target_declaration: NodeRef,
}

/// Deferred exact value-link publications for one resolved import binding.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct PreparedSourceImportValue {
    pub(super) binding: SourceImportBindingPlan,
    pub(super) target_symbol: SemanticSymbolId,
    pub(super) target_declaration: NodeRef,
    pub(super) target_type_node: NodeRef,
    pub(super) type_: TypeId,
    target_type_links: Option<TypeNodeLinks>,
    target_links: ValueSymbolLinks,
    alias_links: ValueSymbolLinks,
}

/// One fully preflighted value-link payload for the source checker's combined
/// final publication batch.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct PreparedSourceImportPublication {
    pub(super) symbol: SemanticSymbolId,
    pub(super) links: ValueSymbolLinks,
}

/// Valid TypeScript import forms outside this dependency-closed slice.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum SourceImportUnsupported {
    Declaration {
        node: NodeRef,
        kind: SyntaxKind,
    },
    JavaScriptSource(NodeRef),
    CommonJsSource(NodeRef),
    ScriptSource(NodeRef),
    DeclarationFile(NodeRef),
    ImportShape(NodeRef),
    ImportClause(NodeRef),
    NamedBindings(NodeRef),
    EmptyNamedBindings(NodeRef),
    Binding(NodeRef),
    TypeOnly(NodeRef),
    DefaultImport(NodeRef),
    ImportAttributes(NodeRef),
    NonIdentifierImportName(NodeRef),
    NonIdentifierLocalName(NodeRef),
    MergedAlias(NodeRef),
    TargetNotDirect {
        alias: SemanticSymbolId,
        immediate: Option<SemanticSymbolId>,
        resolved: SemanticSymbolId,
    },
    TargetSymbol {
        alias: SemanticSymbolId,
        target: SemanticSymbolId,
        flags: SymbolFlags,
    },
    SameSourceTarget {
        binding: NodeRef,
        target: NodeRef,
    },
    TargetDeclaration(NodeRef),
    TargetNotExportedConst(NodeRef),
    MissingTargetAnnotation(NodeRef),
    MissingTargetInitializer(NodeRef),
    TypeOnlyAlias(SemanticSymbolId),
    ValueAlias(SemanticSymbolId),
    #[cfg_attr(not(test), allow(dead_code))]
    TargetTypeDeclaration(NodeRef),
    #[cfg_attr(not(test), allow(dead_code))]
    TargetTypeNotExported(NodeRef),
    #[cfg_attr(not(test), allow(dead_code))]
    TargetTypeShape(NodeRef),
    #[cfg_attr(not(test), allow(dead_code))]
    TypeReference(NodeRef),
    #[cfg_attr(not(test), allow(dead_code))]
    ValueUseOfTypeOnlyImport(NodeRef),
}

/// Malformed AST/binder provenance or poisoned checker state.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum SourceImportInvariant {
    InvalidSource(NodeRef),
    MissingSourceFacts(NodeRef),
    InvalidTopLevelDeclaration(NodeRef),
    InvalidNode(NodeRef),
    InvalidAliasSymbol(SemanticSymbolId),
    MissingAliasSymbol(NodeRef),
    DuplicateAlias(SemanticSymbolId),
    DuplicateLocalName(NodeRef),
    AliasDeclarationMismatch {
        alias: SemanticSymbolId,
        declaration: NodeRef,
    },
    AliasNameMismatch {
        alias: SemanticSymbolId,
        name: NodeRef,
    },
    InvalidAliasLinks(SemanticSymbolId),
    InvalidIdentifierCache(NodeRef),
    ReadBindingMismatch(NodeRef),
    InvalidTargetSymbol(SemanticSymbolId),
    TargetNameMismatch {
        target: SemanticSymbolId,
        name: NodeRef,
    },
    InvalidTargetLinks(SemanticSymbolId),
    InvalidAliasValueLinks(SemanticSymbolId),
    CachedTypeMismatch {
        symbol: SemanticSymbolId,
        cached: TypeId,
        expected: TypeId,
    },
    DuplicatePreparedSymbol(SemanticSymbolId),
    PreparedStateChanged(SemanticSymbolId),
}

/// Exact failure domain for the direct named-value import leaf.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) enum SourceImportError {
    Unsupported(SourceImportUnsupported),
    Invariant(SourceImportInvariant),
    Alias(CanonicalAliasResolutionError),
    DeclaredType(DeclaredTypeError),
    Variable(VariablePlanError),
    CircularAlias {
        alias: SemanticSymbolId,
        events: Vec<CanonicalAliasResolutionEvent>,
    },
}

impl SourceImportError {
    /// Best source node for integration into the source checker's error layer.
    pub(super) const fn node(&self) -> Option<NodeRef> {
        match self {
            Self::Unsupported(reason) => match *reason {
                SourceImportUnsupported::Declaration { node, .. }
                | SourceImportUnsupported::JavaScriptSource(node)
                | SourceImportUnsupported::CommonJsSource(node)
                | SourceImportUnsupported::ScriptSource(node)
                | SourceImportUnsupported::DeclarationFile(node)
                | SourceImportUnsupported::ImportShape(node)
                | SourceImportUnsupported::ImportClause(node)
                | SourceImportUnsupported::NamedBindings(node)
                | SourceImportUnsupported::EmptyNamedBindings(node)
                | SourceImportUnsupported::Binding(node)
                | SourceImportUnsupported::TypeOnly(node)
                | SourceImportUnsupported::DefaultImport(node)
                | SourceImportUnsupported::ImportAttributes(node)
                | SourceImportUnsupported::NonIdentifierImportName(node)
                | SourceImportUnsupported::NonIdentifierLocalName(node)
                | SourceImportUnsupported::MergedAlias(node)
                | SourceImportUnsupported::TargetDeclaration(node)
                | SourceImportUnsupported::TargetNotExportedConst(node)
                | SourceImportUnsupported::MissingTargetAnnotation(node)
                | SourceImportUnsupported::MissingTargetInitializer(node)
                | SourceImportUnsupported::TargetTypeDeclaration(node)
                | SourceImportUnsupported::TargetTypeNotExported(node)
                | SourceImportUnsupported::TargetTypeShape(node)
                | SourceImportUnsupported::TypeReference(node)
                | SourceImportUnsupported::ValueUseOfTypeOnlyImport(node) => Some(node),
                SourceImportUnsupported::SameSourceTarget { binding, .. } => Some(binding),
                SourceImportUnsupported::TargetNotDirect { .. }
                | SourceImportUnsupported::TargetSymbol { .. }
                | SourceImportUnsupported::TypeOnlyAlias(_)
                | SourceImportUnsupported::ValueAlias(_) => None,
            },
            Self::Invariant(reason) => match *reason {
                SourceImportInvariant::InvalidSource(node)
                | SourceImportInvariant::MissingSourceFacts(node)
                | SourceImportInvariant::InvalidTopLevelDeclaration(node)
                | SourceImportInvariant::InvalidNode(node)
                | SourceImportInvariant::MissingAliasSymbol(node)
                | SourceImportInvariant::DuplicateLocalName(node)
                | SourceImportInvariant::AliasNameMismatch { name: node, .. }
                | SourceImportInvariant::TargetNameMismatch { name: node, .. }
                | SourceImportInvariant::InvalidIdentifierCache(node)
                | SourceImportInvariant::ReadBindingMismatch(node) => Some(node),
                SourceImportInvariant::AliasDeclarationMismatch { declaration, .. } => {
                    Some(declaration)
                }
                SourceImportInvariant::InvalidAliasSymbol(_)
                | SourceImportInvariant::DuplicateAlias(_)
                | SourceImportInvariant::InvalidAliasLinks(_)
                | SourceImportInvariant::InvalidTargetSymbol(_)
                | SourceImportInvariant::InvalidTargetLinks(_)
                | SourceImportInvariant::InvalidAliasValueLinks(_)
                | SourceImportInvariant::CachedTypeMismatch { .. }
                | SourceImportInvariant::DuplicatePreparedSymbol(_)
                | SourceImportInvariant::PreparedStateChanged(_) => None,
            },
            Self::Alias(_)
            | Self::DeclaredType(_)
            | Self::Variable(_)
            | Self::CircularAlias { .. } => None,
        }
    }
}

impl std::fmt::Display for SourceImportError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Unsupported(reason) => {
                write!(formatter, "source import is unsupported: {reason:?}")
            }
            Self::Invariant(reason) => {
                write!(formatter, "source import invariant failed: {reason:?}")
            }
            Self::Alias(error) => error.fmt(formatter),
            Self::DeclaredType(error) => error.fmt(formatter),
            Self::Variable(error) => {
                write!(formatter, "target variable planning failed: {error:?}")
            }
            Self::CircularAlias { alias, .. } => {
                write!(formatter, "source import alias is circular: {alias:?}")
            }
        }
    }
}

impl std::error::Error for SourceImportError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Alias(error) => Some(error),
            Self::DeclaredType(error) => Some(error),
            Self::Unsupported(_)
            | Self::Invariant(_)
            | Self::Variable(_)
            | Self::CircularAlias { .. } => None,
        }
    }
}

impl From<CanonicalAliasResolutionError> for SourceImportError {
    fn from(error: CanonicalAliasResolutionError) -> Self {
        Self::Alias(error)
    }
}

impl From<DeclaredTypeError> for SourceImportError {
    fn from(error: DeclaredTypeError) -> Self {
        Self::DeclaredType(error)
    }
}

impl From<VariablePlanError> for SourceImportError {
    fn from(error: VariablePlanError) -> Self {
        Self::Variable(error)
    }
}

fn unsupported(reason: SourceImportUnsupported) -> SourceImportError {
    SourceImportError::Unsupported(reason)
}

fn invariant(reason: SourceImportInvariant) -> SourceImportError {
    SourceImportError::Invariant(reason)
}

/// Proves one complete top-level named-value import without checker writes.
///
/// Statement-order ownership stays with the source planner: it must call this
/// only while traversing the leading import prefix.
pub(super) fn plan_top_level_named_value_import(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    declaration: NodeRef,
) -> Result<SourceImportPlan, SourceImportError> {
    plan_top_level_named_import(arena, bound, store, declaration, SourceImportPhase::Value)
}

/// Proves one complete leading `import type { T as Local }` declaration.
///
/// The clause-level `type` marker is required. Mixed imports and the
/// specifier-level `import { type T }` spelling remain outside this leaf so a
/// plan always has one unambiguous namespace.
#[cfg_attr(not(test), allow(dead_code))]
pub(super) fn plan_top_level_named_type_import(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    declaration: NodeRef,
) -> Result<SourceImportPlan, SourceImportError> {
    plan_top_level_named_import(arena, bound, store, declaration, SourceImportPhase::Type)
}

fn plan_top_level_named_import(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    declaration: NodeRef,
    phase: SourceImportPhase,
) -> Result<SourceImportPlan, SourceImportError> {
    let source = bound.source_file();
    validate_source_identity(arena, bound, store, source)?;
    let facts = bound
        .source_facts()
        .ok_or_else(|| invariant(SourceImportInvariant::MissingSourceFacts(source)))?;
    if facts.is_javascript_file() {
        return Err(unsupported(SourceImportUnsupported::JavaScriptSource(
            source,
        )));
    }
    if facts.is_common_js_module() {
        return Err(unsupported(SourceImportUnsupported::CommonJsSource(source)));
    }
    if !facts.is_external_module() {
        return Err(unsupported(SourceImportUnsupported::ScriptSource(source)));
    }
    if facts.is_declaration_file() {
        return Err(unsupported(SourceImportUnsupported::DeclarationFile(
            source,
        )));
    }

    let source_record = checked_node(arena, bound, store, source)?;
    let NodeData::SourceFile(source_data) = &source_record.data else {
        return Err(invariant(SourceImportInvariant::InvalidSource(source)));
    };
    let record = checked_node(arena, bound, store, declaration)?;
    let NodeData::ImportDeclaration(import) = &record.data else {
        return Err(unsupported(SourceImportUnsupported::Declaration {
            node: declaration,
            kind: record.kind,
        }));
    };
    if record.kind != SyntaxKind::ImportDeclaration {
        return Err(unsupported(SourceImportUnsupported::Declaration {
            node: declaration,
            kind: record.kind,
        }));
    }
    if record.parent != Some(source.node)
        || !range_contains(source_record, record)
        || source_data
            .statements
            .nodes
            .iter()
            .filter(|node| **node == declaration.node)
            .count()
            != 1
    {
        return Err(invariant(
            SourceImportInvariant::InvalidTopLevelDeclaration(declaration),
        ));
    }
    if record.flags.0 != 0
        || import.flow_node.is_some()
        || import.symbol.is_some()
        || import.facts != 0
        || import.modifiers.is_some()
    {
        return Err(unsupported(SourceImportUnsupported::ImportShape(
            declaration,
        )));
    }
    if import.attributes.is_some() {
        return Err(unsupported(SourceImportUnsupported::ImportAttributes(
            declaration,
        )));
    }

    let module_specifier =
        NodeRef::new(declaration.arena, declaration.file, import.module_specifier);
    let specifier_record = checked_node(arena, bound, store, module_specifier)?;
    if specifier_record.kind != SyntaxKind::StringLiteral
        || specifier_record.parent != Some(declaration.node)
        || specifier_record.flags.0 != 0
        || !range_contains(record, specifier_record)
        || !matches!(
            &specifier_record.data,
            NodeData::StringLiteral(literal) if literal.token_flags.0 == 0 && !literal.text.is_empty()
        )
    {
        return Err(unsupported(SourceImportUnsupported::ImportShape(
            module_specifier,
        )));
    }

    let clause = import
        .import_clause
        .map(|node| NodeRef::new(declaration.arena, declaration.file, node))
        .ok_or_else(|| unsupported(SourceImportUnsupported::ImportClause(declaration)))?;
    let clause_record = checked_node(arena, bound, store, clause)?;
    let NodeData::ImportClause(clause_data) = &clause_record.data else {
        return Err(unsupported(SourceImportUnsupported::ImportClause(clause)));
    };
    if clause_record.kind != SyntaxKind::ImportClause
        || clause_record.parent != Some(declaration.node)
        || clause_record.flags.0 != 0
        || !range_contains(record, clause_record)
        || clause_data.local_symbol.is_some()
        || clause_data.symbol.is_some()
        || clause_data.facts != 0
    {
        return Err(unsupported(SourceImportUnsupported::ImportClause(clause)));
    }
    if clause_data.phase_modifier
        != match phase {
            SourceImportPhase::Value => None,
            SourceImportPhase::Type => Some(SyntaxKind::TypeKeyword),
        }
    {
        if clause_data.phase_modifier == Some(SyntaxKind::TypeKeyword) {
            return Err(unsupported(SourceImportUnsupported::TypeOnly(clause)));
        }
        return Err(unsupported(SourceImportUnsupported::ImportClause(clause)));
    }
    if clause_data.name.is_some() {
        return Err(unsupported(SourceImportUnsupported::DefaultImport(clause)));
    }
    let named = clause_data
        .named_bindings
        .map(|node| NodeRef::new(declaration.arena, declaration.file, node))
        .ok_or_else(|| unsupported(SourceImportUnsupported::NamedBindings(clause)))?;
    let named_record = checked_node(arena, bound, store, named)?;
    let NodeData::NamedImports(named_data) = &named_record.data else {
        return Err(unsupported(SourceImportUnsupported::NamedBindings(named)));
    };
    if named_record.kind != SyntaxKind::NamedImports
        || named_record.parent != Some(clause.node)
        || named_record.flags.0 != 0
        || !range_contains(clause_record, named_record)
        || named_data.facts != 0
        || named_data.elements.range != named_record.range
        || named_data.elements.has_trailing_comma
    {
        return Err(unsupported(SourceImportUnsupported::NamedBindings(named)));
    }
    if named_data.elements.nodes.is_empty() {
        return Err(unsupported(SourceImportUnsupported::EmptyNamedBindings(
            named,
        )));
    }

    let mut aliases = HashSet::with_capacity(named_data.elements.nodes.len());
    let mut local_names = HashSet::with_capacity(named_data.elements.nodes.len());
    let mut bindings = Vec::with_capacity(named_data.elements.nodes.len());
    for &binding in &named_data.elements.nodes {
        let binding = NodeRef::new(declaration.arena, declaration.file, binding);
        let binding_record = checked_node(arena, bound, store, binding)?;
        let NodeData::ImportSpecifier(specifier) = &binding_record.data else {
            return Err(unsupported(SourceImportUnsupported::Binding(binding)));
        };
        if binding_record.kind != SyntaxKind::ImportSpecifier
            || binding_record.parent != Some(named.node)
            || binding_record.flags.0 != 0
            || !range_contains(named_record, binding_record)
            || specifier.local_symbol.is_some()
            || specifier.symbol.is_some()
            || specifier.facts != 0
        {
            return Err(unsupported(SourceImportUnsupported::Binding(binding)));
        }
        if specifier.is_type_only {
            return Err(unsupported(SourceImportUnsupported::TypeOnly(binding)));
        }

        let imported_name = NodeRef::new(
            declaration.arena,
            declaration.file,
            specifier.property_name.unwrap_or(specifier.name),
        );
        let local_name = NodeRef::new(declaration.arena, declaration.file, specifier.name);
        let imported_text = exact_identifier(
            arena,
            bound,
            store,
            imported_name,
            binding,
            SourceImportUnsupported::NonIdentifierImportName(imported_name),
        )?;
        let local_text = exact_identifier(
            arena,
            bound,
            store,
            local_name,
            binding,
            SourceImportUnsupported::NonIdentifierLocalName(local_name),
        )?;
        if imported_text == "default" {
            return Err(unsupported(SourceImportUnsupported::DefaultImport(
                imported_name,
            )));
        }

        let alias_symbol = bound
            .symbol(binding)
            .ok_or_else(|| invariant(SourceImportInvariant::MissingAliasSymbol(binding)))?;
        validate_alias_symbol(store, alias_symbol, binding, local_name, &local_text)?;
        if !aliases.insert(alias_symbol) {
            return Err(invariant(SourceImportInvariant::DuplicateAlias(
                alias_symbol,
            )));
        }
        if !local_names.insert(local_text.clone()) {
            return Err(invariant(SourceImportInvariant::DuplicateLocalName(
                local_name,
            )));
        }
        match phase {
            SourceImportPhase::Value => preflight_alias_value_links(store, alias_symbol)?,
            SourceImportPhase::Type => preflight_type_import_value_links(store, alias_symbol)?,
        }
        bindings.push(SourceImportBindingPlan {
            declaration: binding,
            imported_name,
            local_name,
            imported_text,
            local_text,
            alias_symbol,
        });
    }

    Ok(SourceImportPlan {
        declaration,
        module_specifier,
        bindings,
    })
}

/// Proves that an identifier expression reads the supplied import binding.
pub(super) fn plan_source_import_identifier_read(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    binding: &SourceImportBindingPlan,
    node: NodeRef,
    name: &str,
    resolved_alias: SemanticSymbolId,
) -> Result<PlannedSourceImportRead, SourceImportError> {
    let record = checked_node(arena, bound, store, node)?;
    if record.kind != SyntaxKind::Identifier
        || record.flags.0 != 0
        || !matches!(
            &record.data,
            NodeData::Identifier(identifier)
                if identifier.flow_node.is_none() && identifier.text == name
        )
        || name != binding.local_text
        || resolved_alias != binding.alias_symbol
    {
        return Err(invariant(SourceImportInvariant::ReadBindingMismatch(node)));
    }
    validate_alias_symbol(
        store,
        binding.alias_symbol,
        binding.declaration,
        binding.local_name,
        &binding.local_text,
    )?;
    if store.symbol_node_links(node).is_some_and(|links| {
        links
            .resolved_symbol
            .is_some_and(|cached| cached != binding.alias_symbol)
    }) {
        return Err(invariant(SourceImportInvariant::InvalidIdentifierCache(
            node,
        )));
    }
    preflight_alias_value_links(store, binding.alias_symbol)?;
    Ok(PlannedSourceImportRead {
        node,
        resolved_symbol: binding.alias_symbol,
        value_symbol: binding.alias_symbol,
    })
}

/// Resolves one import declaration binding without querying its value type.
///
/// The production host is called directly before any sparse alias cache is
/// trusted. This independently re-derives the immediate target from the exact
/// declaration, module-resolution manifest entry, and target export table.
pub(super) fn resolve_source_import_binding(
    store: &mut CanonicalTypeMapperStore,
    alias_host: &mut ProductionAliasTargetHost<'_, '_, '_>,
    binding: &SourceImportBindingPlan,
) -> Result<ResolvedSourceImportBinding, SourceImportError> {
    resolve_source_import_binding_phase(store, alias_host, binding, SourceImportPhase::Value)
}

/// Resolves one type-only import through the exact module manifest and proves
/// that its direct target is one explicitly exported, non-generic type alias
/// or interface. The target's declared type remains lazy.
#[cfg_attr(not(test), allow(dead_code))]
pub(super) fn resolve_source_type_import_binding(
    store: &mut CanonicalTypeMapperStore,
    alias_host: &mut ProductionAliasTargetHost<'_, '_, '_>,
    declared_host: &DeclaredTypeHost<'_>,
    binding: &SourceImportBindingPlan,
) -> Result<ResolvedSourceTypeImportBinding, SourceImportError> {
    let resolved =
        resolve_source_import_binding_phase(store, alias_host, binding, SourceImportPhase::Type)?;
    let target_declaration = plan_direct_exported_type_target(
        store,
        declared_host,
        binding.alias_symbol,
        resolved.target_symbol,
        &binding.imported_text,
    )?;
    if target_declaration.file == binding.declaration.file {
        return Err(unsupported(SourceImportUnsupported::SameSourceTarget {
            binding: binding.declaration,
            target: target_declaration,
        }));
    }
    Ok(ResolvedSourceTypeImportBinding {
        binding: binding.clone(),
        target_symbol: resolved.target_symbol,
        target_declaration,
    })
}

fn resolve_source_import_binding_phase(
    store: &mut CanonicalTypeMapperStore,
    alias_host: &mut ProductionAliasTargetHost<'_, '_, '_>,
    binding: &SourceImportBindingPlan,
    phase: SourceImportPhase,
) -> Result<ResolvedSourceImportBinding, SourceImportError> {
    validate_alias_symbol(
        store,
        binding.alias_symbol,
        binding.declaration,
        binding.local_name,
        &binding.local_text,
    )?;
    if !store.ensure_alias_symbol_links(binding.alias_symbol) {
        return Err(invariant(SourceImportInvariant::InvalidAliasLinks(
            binding.alias_symbol,
        )));
    }

    let independently_derived = alias_host
        .get_target_of_alias_declaration(store, binding.alias_symbol)
        .map_err(|reason| {
            SourceImportError::Alias(CanonicalAliasResolutionError::TargetUnavailable {
                alias: binding.alias_symbol,
                reason,
            })
        })?;
    let CanonicalImmediateAliasTarget::Resolved(direct_target) = independently_derived else {
        return Err(invariant(SourceImportInvariant::InvalidAliasLinks(
            binding.alias_symbol,
        )));
    };
    let direct_flags = store
        .symbol(direct_target)
        .ok_or_else(|| invariant(SourceImportInvariant::InvalidTargetSymbol(direct_target)))?
        .flags();
    if direct_flags.intersects(SymbolFlags::ALIAS) && direct_flags != SymbolFlags::ALIAS {
        return Err(invariant(SourceImportInvariant::InvalidTargetSymbol(
            direct_target,
        )));
    }

    if let Some(links) = store.alias_symbol_links(binding.alias_symbol) {
        match (phase, links.type_only_declaration) {
            (SourceImportPhase::Value, Some(_)) => {
                return Err(unsupported(SourceImportUnsupported::TypeOnlyAlias(
                    binding.alias_symbol,
                )));
            }
            (SourceImportPhase::Type, Some(marker)) if marker == binding.declaration => {}
            (SourceImportPhase::Type, _) => {
                return Err(unsupported(SourceImportUnsupported::ValueAlias(
                    binding.alias_symbol,
                )));
            }
            (SourceImportPhase::Value, None) => {}
        }
        if links
            .immediate_target
            .is_some_and(|cached| cached != direct_target)
            || (direct_flags != SymbolFlags::ALIAS
                && match links.alias_target {
                    AliasTargetState::Unresolved => false,
                    AliasTargetState::Resolved(cached) => cached != direct_target,
                    AliasTargetState::Unknown => true,
                })
        {
            return Err(invariant(SourceImportInvariant::InvalidAliasLinks(
                binding.alias_symbol,
            )));
        }
    }

    let immediate = CanonicalAliasResolver::new(store, alias_host)
        .get_immediate_aliased_symbol(binding.alias_symbol)?;
    if immediate != Some(direct_target) {
        return Err(invariant(SourceImportInvariant::InvalidAliasLinks(
            binding.alias_symbol,
        )));
    }

    let resolution =
        CanonicalAliasResolver::new(store, alias_host).resolve_alias(binding.alias_symbol)?;
    let resolved_target = match resolution.target {
        AliasTargetState::Unknown if direct_flags == SymbolFlags::ALIAS => {
            return Err(SourceImportError::CircularAlias {
                alias: binding.alias_symbol,
                events: resolution.events,
            });
        }
        AliasTargetState::Unknown | AliasTargetState::Unresolved => {
            return Err(invariant(SourceImportInvariant::InvalidAliasLinks(
                binding.alias_symbol,
            )));
        }
        AliasTargetState::Resolved(target) if !resolution.events.is_empty() => {
            return Err(SourceImportError::CircularAlias {
                alias: binding.alias_symbol,
                events: resolution.events,
            });
        }
        AliasTargetState::Resolved(target) => target,
    };

    if direct_flags == SymbolFlags::ALIAS {
        return Err(unsupported(SourceImportUnsupported::TargetNotDirect {
            alias: binding.alias_symbol,
            immediate: Some(direct_target),
            resolved: resolved_target,
        }));
    }
    if resolved_target != direct_target {
        return Err(invariant(SourceImportInvariant::InvalidAliasLinks(
            binding.alias_symbol,
        )));
    }

    let alias_links = store
        .alias_symbol_links(binding.alias_symbol)
        .ok_or_else(|| {
            invariant(SourceImportInvariant::InvalidAliasLinks(
                binding.alias_symbol,
            ))
        })?;
    if alias_links.immediate_target != Some(direct_target)
        || alias_links.alias_target != AliasTargetState::Resolved(direct_target)
        || match phase {
            SourceImportPhase::Value => alias_links.type_only_declaration.is_some(),
            SourceImportPhase::Type => {
                alias_links.type_only_declaration != Some(binding.declaration)
            }
        }
    {
        return Err(invariant(SourceImportInvariant::InvalidAliasLinks(
            binding.alias_symbol,
        )));
    }

    Ok(ResolvedSourceImportBinding {
        binding: binding.clone(),
        target_symbol: direct_target,
    })
}

/// Proves that one exact importer annotation references a resolved type-only
/// binding and returns the immutable capability consumed by
/// [`CanonicalTypeQuery`]. No node or type links are published here.
#[cfg_attr(not(test), allow(dead_code))]
pub(super) fn plan_source_type_import_reference(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    resolved: &ResolvedSourceTypeImportBinding,
    reference: NodeRef,
) -> Result<CanonicalTypeReferenceAliasTarget, SourceImportError> {
    let binding = &resolved.binding;
    validate_resolved_type_import(store, host, resolved)?;
    let (arena, bound) = host
        .source(reference)
        .ok_or_else(|| invariant(SourceImportInvariant::InvalidNode(reference)))?;
    let record = checked_node(arena, bound, store, reference)?;
    let NodeData::TypeReferenceNode(reference_data) = &record.data else {
        return Err(unsupported(SourceImportUnsupported::TypeReference(
            reference,
        )));
    };
    if record.kind != SyntaxKind::TypeReference
        || record.flags.0 != 0
        || reference_data.type_arguments.is_some()
    {
        return Err(unsupported(SourceImportUnsupported::TypeReference(
            reference,
        )));
    }
    let name = NodeRef::new(reference.arena, reference.file, reference_data.type_name);
    let name_record = checked_node(arena, bound, store, name)?;
    if name_record.parent != Some(reference.node)
        || !matches!(
            &name_record.data,
            NodeData::Identifier(identifier)
                if name_record.kind == SyntaxKind::Identifier
                    && name_record.flags.0 == 0
                    && identifier.flow_node.is_none()
                    && identifier.text == binding.local_text
        )
    {
        return Err(unsupported(SourceImportUnsupported::TypeReference(
            reference,
        )));
    }

    let mut callback_host = host.name_resolver_host(store)?;
    let result = CanonicalNameResolver::new(arena, bound, store.symbol_store(), &mut callback_host)
        .map_err(DeclaredTypeError::from)?
        .resolve(
            Some(CanonicalResolutionLocation::Bound(name)),
            &binding.local_text,
            SymbolFlags::TYPE,
            None,
            true,
            false,
        );
    if !matches!(
        result,
        Err(CanonicalNameResolutionError::AliasResolutionUnavailable(alias))
            if alias == binding.alias_symbol
    ) {
        return Err(invariant(SourceImportInvariant::ReadBindingMismatch(
            reference,
        )));
    }
    if store.symbol_node_links(reference).is_some_and(|links| {
        links
            .resolved_symbol
            .is_some_and(|cached| cached != resolved.target_symbol)
    }) {
        return Err(invariant(SourceImportInvariant::InvalidIdentifierCache(
            reference,
        )));
    }

    Ok(CanonicalTypeReferenceAliasTarget::new(
        reference,
        binding.alias_symbol,
        resolved.target_symbol,
    ))
}

/// Classifies an expression read of a proven type-only binding without
/// fabricating a value type. Source integration may translate this boundary
/// into TS1361 while retaining the exact read node.
#[cfg_attr(not(test), allow(dead_code))]
pub(super) fn reject_source_type_import_value_use(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    resolved: &ResolvedSourceTypeImportBinding,
    node: NodeRef,
    name: &str,
    resolved_alias: SemanticSymbolId,
) -> Result<(), SourceImportError> {
    let binding = &resolved.binding;
    let record = checked_node(arena, bound, store, node)?;
    if record.kind != SyntaxKind::Identifier
        || record.flags.0 != 0
        || !matches!(
            &record.data,
            NodeData::Identifier(identifier)
                if identifier.flow_node.is_none() && identifier.text == name
        )
        || name != binding.local_text
        || resolved_alias != binding.alias_symbol
    {
        return Err(invariant(SourceImportInvariant::ReadBindingMismatch(node)));
    }
    validate_alias_symbol(
        store,
        binding.alias_symbol,
        binding.declaration,
        binding.local_name,
        &binding.local_text,
    )?;
    let links = store
        .alias_symbol_links(binding.alias_symbol)
        .ok_or_else(|| {
            invariant(SourceImportInvariant::InvalidAliasLinks(
                binding.alias_symbol,
            ))
        })?;
    if links.immediate_target != Some(resolved.target_symbol)
        || links.alias_target != AliasTargetState::Resolved(resolved.target_symbol)
        || links.type_only_declaration != Some(binding.declaration)
    {
        return Err(invariant(SourceImportInvariant::InvalidAliasLinks(
            binding.alias_symbol,
        )));
    }
    Err(unsupported(
        SourceImportUnsupported::ValueUseOfTypeOnlyImport(node),
    ))
}

/// Lazily types one resolved binding for one proven value read while
/// deferring all target/alias value-link writes.
#[allow(clippy::too_many_arguments)]
pub(super) fn prepare_source_import_value(
    store: &mut CanonicalTypeMapperStore,
    declared_host: &DeclaredTypeHost<'_>,
    global_types: &CanonicalGlobalTypes,
    options: CanonicalCheckerOptions,
    diagnostics: &mut CanonicalCheckerDiagnostics,
    resolved: &ResolvedSourceImportBinding,
    read: &PlannedSourceImportRead,
) -> Result<PreparedSourceImportValue, SourceImportError> {
    validate_planned_import_read(store, declared_host, resolved, read)?;
    let binding = &resolved.binding;
    let target = resolved.target_symbol;
    let alias_links = store
        .alias_symbol_links(binding.alias_symbol)
        .ok_or_else(|| {
            invariant(SourceImportInvariant::InvalidAliasLinks(
                binding.alias_symbol,
            ))
        })?;
    if alias_links.immediate_target != Some(target)
        || alias_links.alias_target != AliasTargetState::Resolved(target)
        || alias_links.type_only_declaration.is_some()
    {
        return Err(invariant(SourceImportInvariant::InvalidAliasLinks(
            binding.alias_symbol,
        )));
    }

    let (target_declaration, target_type_node) = plan_direct_annotated_const_target(
        store,
        declared_host,
        binding.alias_symbol,
        target,
        &binding.imported_text,
    )?;
    if target_declaration.file == binding.declaration.file {
        return Err(unsupported(SourceImportUnsupported::SameSourceTarget {
            binding: binding.declaration,
            target: target_declaration,
        }));
    }
    let type_ = CanonicalTypeQuery::new_with_global_types(
        store,
        declared_host,
        global_types,
        options,
        diagnostics,
    )?
    .get_type_from_type_node(target_type_node)?;
    let target_type_links = store.type_node_links(target_type_node).cloned();
    let target_links = prepare_value_links(store, target, type_, false)?;
    let alias_value_links = prepare_value_links(store, binding.alias_symbol, type_, true)?;

    Ok(PreparedSourceImportValue {
        binding: binding.clone(),
        target_symbol: target,
        target_declaration,
        target_type_node,
        type_,
        target_type_links,
        target_links,
        alias_links: alias_value_links,
    })
}

/// Read-only final preflight for payloads that the source checker can append
/// to its combined atomic publication batch.
pub(super) fn preflight_prepared_source_import_publications(
    store: &CanonicalTypeMapperStore,
    prepared: &[PreparedSourceImportValue],
) -> Result<Vec<PreparedSourceImportPublication>, SourceImportError> {
    let mut publications = Vec::<PreparedSourceImportPublication>::new();
    let mut publication_indices = HashMap::<SemanticSymbolId, usize>::new();
    for value in prepared {
        validate_prepared_import_value(store, value)?;
        for (symbol, links) in [
            (value.target_symbol, &value.target_links),
            (value.binding.alias_symbol, &value.alias_links),
        ] {
            if let Some(&index) = publication_indices.get(&symbol) {
                if publications[index].links != *links {
                    return Err(invariant(SourceImportInvariant::DuplicatePreparedSymbol(
                        symbol,
                    )));
                }
                continue;
            }
            publication_indices.insert(symbol, publications.len());
            publications.push(PreparedSourceImportPublication {
                symbol,
                links: links.clone(),
            });
        }
    }

    for publication in &publications {
        let type_ = publication.links.resolved_type.ok_or(invariant(
            SourceImportInvariant::PreparedStateChanged(publication.symbol),
        ))?;
        let current = prepare_value_links(
            store,
            publication.symbol,
            type_,
            store
                .symbol(publication.symbol)
                .is_some_and(|record| record.flags() == SymbolFlags::ALIAS),
        )?;
        if current != publication.links {
            return Err(invariant(SourceImportInvariant::PreparedStateChanged(
                publication.symbol,
            )));
        }
    }

    Ok(publications)
}

fn validate_source_identity(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    source: NodeRef,
) -> Result<(), SourceImportError> {
    if source != bound.source_file()
        || !source.is_for(arena.id(), bound.file_id())
        || bound.node_arena_revision() != arena.revision()
        || !bound.declarations_complete()
        || !bound.contains(source)
        || !store.contains_node_ref(source)
    {
        return Err(invariant(SourceImportInvariant::InvalidSource(source)));
    }
    Ok(())
}

fn checked_node<'arena>(
    arena: &'arena NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    node: NodeRef,
) -> Result<&'arena Node, SourceImportError> {
    if !node.is_for(arena.id(), bound.file_id())
        || !bound.contains(node)
        || !store.contains_node_ref(node)
    {
        return Err(invariant(SourceImportInvariant::InvalidNode(node)));
    }
    arena
        .get(node.node)
        .filter(|record| record.data.matches_syntax_kind(record.kind))
        .ok_or_else(|| invariant(SourceImportInvariant::InvalidNode(node)))
}

fn range_contains(parent: &Node, child: &Node) -> bool {
    parent.range.start.get() <= child.range.start.get()
        && child.range.start.get() <= child.range.end.get()
        && child.range.end.get() <= parent.range.end.get()
}

fn exact_identifier(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    name: NodeRef,
    parent: NodeRef,
    unsupported_reason: SourceImportUnsupported,
) -> Result<String, SourceImportError> {
    let record = checked_node(arena, bound, store, name)?;
    let NodeData::Identifier(identifier) = &record.data else {
        return Err(unsupported(unsupported_reason));
    };
    if record.kind != SyntaxKind::Identifier
        || record.parent != Some(parent.node)
        || record.flags.0 != 0
        || identifier.flow_node.is_some()
        || identifier.text.is_empty()
    {
        return Err(unsupported(unsupported_reason));
    }
    Ok(identifier.text.clone())
}

fn validate_alias_symbol(
    store: &CanonicalTypeMapperStore,
    alias: SemanticSymbolId,
    declaration: NodeRef,
    name: NodeRef,
    name_text: &str,
) -> Result<(), SourceImportError> {
    let record = store
        .symbol(alias)
        .ok_or_else(|| invariant(SourceImportInvariant::InvalidAliasSymbol(alias)))?;
    let merged = store.get_merged_symbol(alias);
    if merged.is_some_and(|target| target != alias)
        || (record.flags().intersects(SymbolFlags::ALIAS)
            && record.flags() != SymbolFlags::ALIAS
            && record
                .declarations()
                .is_some_and(|declarations| declarations.contains(&declaration)))
    {
        return Err(unsupported(SourceImportUnsupported::MergedAlias(
            declaration,
        )));
    }
    if record.flags() != SymbolFlags::ALIAS
        || record.check_flags() != CheckFlags::NONE
        || record.value_declaration().is_some()
        || record.members().is_some()
        || record.exports().is_some()
        || record.parent().is_some()
        || record.export_symbol().is_some()
        || merged != Some(alias)
    {
        return Err(invariant(SourceImportInvariant::InvalidAliasSymbol(alias)));
    }
    if record.declarations() != Some(&[declaration]) {
        return Err(invariant(SourceImportInvariant::AliasDeclarationMismatch {
            alias,
            declaration,
        }));
    }
    if record.name().as_bytes() != name_text.as_bytes() {
        return Err(invariant(SourceImportInvariant::AliasNameMismatch {
            alias,
            name,
        }));
    }
    if let Some(links) = store.alias_symbol_links(alias)
        && (links
            .immediate_target
            .is_some_and(|target| store.symbol(target).is_none())
            || links
                .alias_target
                .symbol()
                .is_some_and(|target| store.symbol(target).is_none())
            || links
                .type_only_declaration
                .is_some_and(|node| !store.contains_node_ref(node)))
    {
        return Err(invariant(SourceImportInvariant::InvalidAliasLinks(alias)));
    }
    Ok(())
}

fn preflight_alias_value_links(
    store: &CanonicalTypeMapperStore,
    alias: SemanticSymbolId,
) -> Result<(), SourceImportError> {
    let Some(links) = store.value_symbol_links(alias) else {
        return Ok(());
    };
    if links.write_type.is_some()
        || links.target.is_some()
        || links.mapper.is_some()
        || links.name_type.is_some()
        || links.containing_type.is_some()
        || links.function_or_constructor_checked
        || links
            .resolved_type
            .is_some_and(|type_| store.type_payload(type_).is_none())
    {
        return Err(invariant(SourceImportInvariant::InvalidAliasValueLinks(
            alias,
        )));
    }
    Ok(())
}

fn preflight_type_import_value_links(
    store: &CanonicalTypeMapperStore,
    alias: SemanticSymbolId,
) -> Result<(), SourceImportError> {
    preflight_alias_value_links(store, alias)?;
    if store
        .value_symbol_links(alias)
        .is_some_and(|links| links.resolved_type.is_some())
    {
        return Err(invariant(SourceImportInvariant::InvalidAliasValueLinks(
            alias,
        )));
    }
    Ok(())
}

#[cfg_attr(not(test), allow(dead_code))]
fn validate_resolved_type_import(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    resolved: &ResolvedSourceTypeImportBinding,
) -> Result<(), SourceImportError> {
    let binding = &resolved.binding;
    validate_alias_symbol(
        store,
        binding.alias_symbol,
        binding.declaration,
        binding.local_name,
        &binding.local_text,
    )?;
    let links = store
        .alias_symbol_links(binding.alias_symbol)
        .ok_or_else(|| {
            invariant(SourceImportInvariant::InvalidAliasLinks(
                binding.alias_symbol,
            ))
        })?;
    if links.immediate_target != Some(resolved.target_symbol)
        || links.alias_target != AliasTargetState::Resolved(resolved.target_symbol)
        || links.type_only_declaration != Some(binding.declaration)
        || plan_direct_exported_type_target(
            store,
            host,
            binding.alias_symbol,
            resolved.target_symbol,
            &binding.imported_text,
        )? != resolved.target_declaration
    {
        return Err(invariant(SourceImportInvariant::InvalidAliasLinks(
            binding.alias_symbol,
        )));
    }
    Ok(())
}

fn validate_planned_import_read(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    resolved: &ResolvedSourceImportBinding,
    read: &PlannedSourceImportRead,
) -> Result<(), SourceImportError> {
    let binding = &resolved.binding;
    if read.resolved_symbol != binding.alias_symbol
        || read.value_symbol != binding.alias_symbol
        || !store.contains_node_ref(read.node)
    {
        return Err(invariant(SourceImportInvariant::ReadBindingMismatch(
            read.node,
        )));
    }
    let (arena, bound) = host
        .source(read.node)
        .ok_or_else(|| invariant(SourceImportInvariant::InvalidNode(read.node)))?;
    let record = checked_node(arena, bound, store, read.node)?;
    if record.kind != SyntaxKind::Identifier
        || record.flags.0 != 0
        || !matches!(
            &record.data,
            NodeData::Identifier(identifier)
                if identifier.flow_node.is_none() && identifier.text == binding.local_text
        )
    {
        return Err(invariant(SourceImportInvariant::ReadBindingMismatch(
            read.node,
        )));
    }
    if store.symbol_node_links(read.node).is_some_and(|links| {
        links
            .resolved_symbol
            .is_some_and(|cached| cached != binding.alias_symbol)
    }) {
        return Err(invariant(SourceImportInvariant::InvalidIdentifierCache(
            read.node,
        )));
    }
    Ok(())
}

#[cfg_attr(not(test), allow(dead_code))]
fn plan_direct_exported_type_target(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    alias: SemanticSymbolId,
    target: SemanticSymbolId,
    expected_name: &str,
) -> Result<NodeRef, SourceImportError> {
    let target_record = store
        .symbol(target)
        .ok_or_else(|| invariant(SourceImportInvariant::InvalidTargetSymbol(target)))?;
    if target_record.flags() != SymbolFlags::TYPE_ALIAS
        && target_record.flags() != SymbolFlags::INTERFACE
    {
        return Err(unsupported(SourceImportUnsupported::TargetSymbol {
            alias,
            target,
            flags: target_record.flags(),
        }));
    }
    let Some([declaration]) = target_record.declarations() else {
        return Err(unsupported(SourceImportUnsupported::TargetSymbol {
            alias,
            target,
            flags: target_record.flags(),
        }));
    };
    let declaration = *declaration;
    if target_record.value_declaration().is_some() {
        return Err(invariant(SourceImportInvariant::InvalidTargetSymbol(
            target,
        )));
    }
    let (arena, bound) = host
        .source(declaration)
        .ok_or_else(|| unsupported(SourceImportUnsupported::TargetTypeDeclaration(declaration)))?;
    let facts = bound.source_facts().ok_or_else(|| {
        invariant(SourceImportInvariant::MissingSourceFacts(
            bound.source_file(),
        ))
    })?;
    if facts.is_javascript_file()
        || facts.is_common_js_module()
        || !facts.is_external_module()
        || facts.is_declaration_file()
        || !host.symbol_matches(store, declaration, target)
    {
        return Err(unsupported(SourceImportUnsupported::TargetTypeDeclaration(
            declaration,
        )));
    }
    let source_record = checked_node(arena, bound, store, bound.source_file())?;
    let NodeData::SourceFile(source) = &source_record.data else {
        return Err(invariant(SourceImportInvariant::InvalidSource(
            bound.source_file(),
        )));
    };
    if source
        .statements
        .nodes
        .iter()
        .filter(|node| **node == declaration.node)
        .count()
        != 1
    {
        return Err(unsupported(SourceImportUnsupported::TargetTypeDeclaration(
            declaration,
        )));
    }

    let record = checked_node(arena, bound, store, declaration)?;
    if record.parent != Some(bound.source_file().node) || record.flags.0 != 0 {
        return Err(unsupported(SourceImportUnsupported::TargetTypeDeclaration(
            declaration,
        )));
    }
    let (name_node, modifiers) = match &record.data {
        NodeData::TypeAliasDeclaration(type_alias)
            if record.kind == SyntaxKind::TypeAliasDeclaration
                && target_record.flags() == SymbolFlags::TYPE_ALIAS
                && type_alias.flow_node.is_none()
                && type_alias.local_symbol.is_none()
                && type_alias.symbol.is_none()
                && type_alias.type_parameters.is_none() =>
        {
            let type_node = NodeRef::new(declaration.arena, declaration.file, type_alias.type_);
            if checked_node(arena, bound, store, type_node)?.parent != Some(declaration.node) {
                return Err(unsupported(SourceImportUnsupported::TargetTypeShape(
                    declaration,
                )));
            }
            (type_alias.name, type_alias.modifiers.as_ref())
        }
        NodeData::InterfaceDeclaration(interface)
            if record.kind == SyntaxKind::InterfaceDeclaration
                && target_record.flags() == SymbolFlags::INTERFACE
                && interface.flow_node.is_none()
                && interface.local_symbol.is_none()
                && interface.symbol.is_none()
                && interface.type_parameters.is_none()
                && interface.heritage_clauses.is_none() =>
        {
            (interface.name, interface.modifiers.as_ref())
        }
        _ => {
            return Err(unsupported(SourceImportUnsupported::TargetTypeShape(
                declaration,
            )));
        }
    };
    let name = NodeRef::new(declaration.arena, declaration.file, name_node);
    let name_record = checked_node(arena, bound, store, name)?;
    if name_record.parent != Some(declaration.node)
        || !matches!(
            &name_record.data,
            NodeData::Identifier(identifier)
                if name_record.kind == SyntaxKind::Identifier
                    && name_record.flags.0 == 0
                    && identifier.flow_node.is_none()
                    && identifier.text == expected_name
        )
    {
        return Err(invariant(SourceImportInvariant::TargetNameMismatch {
            target,
            name,
        }));
    }
    if !has_exact_export_modifier(arena, bound, store, declaration, modifiers)? {
        return Err(unsupported(SourceImportUnsupported::TargetTypeNotExported(
            declaration,
        )));
    }
    Ok(declaration)
}

fn plan_direct_annotated_const_target(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    alias: SemanticSymbolId,
    target: SemanticSymbolId,
    expected_name: &str,
) -> Result<(NodeRef, NodeRef), SourceImportError> {
    let target_record = store
        .symbol(target)
        .ok_or_else(|| invariant(SourceImportInvariant::InvalidTargetSymbol(target)))?;
    if target_record.flags() != SymbolFlags::BLOCK_SCOPED_VARIABLE {
        return Err(unsupported(SourceImportUnsupported::TargetSymbol {
            alias,
            target,
            flags: target_record.flags(),
        }));
    }
    let Some([declaration]) = target_record.declarations() else {
        return Err(unsupported(SourceImportUnsupported::TargetSymbol {
            alias,
            target,
            flags: target_record.flags(),
        }));
    };
    let declaration = *declaration;
    if target_record.value_declaration() != Some(declaration) {
        return Err(invariant(SourceImportInvariant::InvalidTargetSymbol(
            target,
        )));
    }
    let (arena, bound) = host
        .source(declaration)
        .ok_or_else(|| unsupported(SourceImportUnsupported::TargetDeclaration(declaration)))?;
    let facts = bound.source_facts().ok_or_else(|| {
        invariant(SourceImportInvariant::MissingSourceFacts(
            bound.source_file(),
        ))
    })?;
    if facts.is_javascript_file()
        || facts.is_common_js_module()
        || !facts.is_external_module()
        || facts.is_declaration_file()
    {
        return Err(unsupported(SourceImportUnsupported::TargetDeclaration(
            declaration,
        )));
    }
    let record = checked_node(arena, bound, store, declaration)?;
    let NodeData::VariableDeclaration(variable) = &record.data else {
        return Err(unsupported(SourceImportUnsupported::TargetDeclaration(
            declaration,
        )));
    };
    if record.kind != SyntaxKind::VariableDeclaration
        || record.flags.0 != 0
        || variable.exclamation_token.is_some()
        || variable.local_symbol.is_some()
        || variable.symbol.is_some()
        || variable.facts != 0
    {
        return Err(unsupported(SourceImportUnsupported::TargetDeclaration(
            declaration,
        )));
    }

    let name = NodeRef::new(declaration.arena, declaration.file, variable.name);
    let name_record = checked_node(arena, bound, store, name)?;
    let NodeData::Identifier(identifier) = &name_record.data else {
        return Err(unsupported(SourceImportUnsupported::TargetDeclaration(
            name,
        )));
    };
    if name_record.kind != SyntaxKind::Identifier
        || name_record.parent != Some(declaration.node)
        || name_record.flags.0 != 0
        || identifier.flow_node.is_some()
        || identifier.text.is_empty()
    {
        return Err(unsupported(SourceImportUnsupported::TargetDeclaration(
            name,
        )));
    }
    if identifier.text != expected_name {
        return Err(invariant(SourceImportInvariant::TargetNameMismatch {
            target,
            name,
        }));
    }

    let list = record
        .parent
        .map(|node| NodeRef::new(declaration.arena, declaration.file, node))
        .ok_or_else(|| unsupported(SourceImportUnsupported::TargetNotExportedConst(declaration)))?;
    let list_record = checked_node(arena, bound, store, list)?;
    let NodeData::VariableDeclarationList(list_data) = &list_record.data else {
        return Err(unsupported(
            SourceImportUnsupported::TargetNotExportedConst(declaration),
        ));
    };
    if list_record.kind != SyntaxKind::VariableDeclarationList
        || list_record.flags.0 != NODE_FLAG_CONST
        || list_data.facts != 0
        || !list_data.declarations.nodes.contains(&declaration.node)
    {
        return Err(unsupported(
            SourceImportUnsupported::TargetNotExportedConst(declaration),
        ));
    }
    let statement = list_record
        .parent
        .map(|node| NodeRef::new(declaration.arena, declaration.file, node))
        .ok_or_else(|| unsupported(SourceImportUnsupported::TargetNotExportedConst(declaration)))?;
    let statement_record = checked_node(arena, bound, store, statement)?;
    let NodeData::VariableStatement(statement_data) = &statement_record.data else {
        return Err(unsupported(
            SourceImportUnsupported::TargetNotExportedConst(declaration),
        ));
    };
    if statement_record.kind != SyntaxKind::VariableStatement
        || statement_record.parent != Some(bound.source_file().node)
        || statement_record.flags.0 != 0
        || statement_data.declaration_list != list.node
        || statement_data.flow_node.is_some()
        || statement_data.facts != 0
        || !has_exact_export_modifier(
            arena,
            bound,
            store,
            statement,
            statement_data.modifiers.as_ref(),
        )?
    {
        return Err(unsupported(
            SourceImportUnsupported::TargetNotExportedConst(declaration),
        ));
    }
    let source_record = checked_node(arena, bound, store, bound.source_file())?;
    let NodeData::SourceFile(source_data) = &source_record.data else {
        return Err(invariant(SourceImportInvariant::InvalidSource(
            bound.source_file(),
        )));
    };
    if source_data
        .statements
        .nodes
        .iter()
        .filter(|node| **node == statement.node)
        .count()
        != 1
    {
        return Err(unsupported(
            SourceImportUnsupported::TargetNotExportedConst(declaration),
        ));
    }

    plan_top_level_variable(
        bound,
        store,
        declaration,
        name,
        &identifier.text,
        VariableBindingKind::Const,
        true,
    )?;
    let type_node = variable
        .type_
        .map(|node| NodeRef::new(declaration.arena, declaration.file, node))
        .ok_or_else(|| {
            unsupported(SourceImportUnsupported::MissingTargetAnnotation(
                declaration,
            ))
        })?;
    if checked_node(arena, bound, store, type_node)?.parent != Some(declaration.node) {
        return Err(unsupported(SourceImportUnsupported::TargetDeclaration(
            type_node,
        )));
    }
    let initializer = variable
        .initializer
        .map(|node| NodeRef::new(declaration.arena, declaration.file, node))
        .ok_or_else(|| {
            unsupported(SourceImportUnsupported::MissingTargetInitializer(
                declaration,
            ))
        })?;
    if checked_node(arena, bound, store, initializer)?.parent != Some(declaration.node) {
        return Err(unsupported(SourceImportUnsupported::TargetDeclaration(
            initializer,
        )));
    }
    Ok((declaration, type_node))
}

fn has_exact_export_modifier(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    statement: NodeRef,
    modifiers: Option<&ts_ast::ModifierList>,
) -> Result<bool, SourceImportError> {
    let Some(modifiers) = modifiers else {
        return Ok(false);
    };
    let [modifier] = modifiers.list.nodes.as_slice() else {
        return Ok(false);
    };
    let modifier = NodeRef::new(statement.arena, statement.file, *modifier);
    let record = checked_node(arena, bound, store, modifier)?;
    Ok(modifiers.flags.0 == 0
        && !modifiers.list.has_trailing_comma
        && record.kind == SyntaxKind::ExportKeyword
        && matches!(&record.data, NodeData::Token(_))
        && record.flags.0 == 0
        && record.parent == Some(statement.node))
}

fn prepare_value_links(
    store: &CanonicalTypeMapperStore,
    symbol: SemanticSymbolId,
    type_: TypeId,
    alias: bool,
) -> Result<ValueSymbolLinks, SourceImportError> {
    let record = store.symbol(symbol).ok_or_else(|| {
        invariant(if alias {
            SourceImportInvariant::InvalidAliasSymbol(symbol)
        } else {
            SourceImportInvariant::InvalidTargetSymbol(symbol)
        })
    })?;
    if (alias && record.flags() != SymbolFlags::ALIAS)
        || (!alias && record.flags() != SymbolFlags::BLOCK_SCOPED_VARIABLE)
        || store.type_payload(type_).is_none()
    {
        return Err(invariant(if alias {
            SourceImportInvariant::InvalidAliasValueLinks(symbol)
        } else {
            SourceImportInvariant::InvalidTargetLinks(symbol)
        }));
    }
    let mut links = store
        .value_symbol_links(symbol)
        .cloned()
        .unwrap_or_default();
    if links.write_type.is_some()
        || links.target.is_some()
        || links.mapper.is_some()
        || links.name_type.is_some()
        || links.containing_type.is_some()
        || links.function_or_constructor_checked
    {
        return Err(invariant(if alias {
            SourceImportInvariant::InvalidAliasValueLinks(symbol)
        } else {
            SourceImportInvariant::InvalidTargetLinks(symbol)
        }));
    }
    if let Some(cached) = links.resolved_type
        && cached != type_
    {
        return Err(invariant(SourceImportInvariant::CachedTypeMismatch {
            symbol,
            cached,
            expected: type_,
        }));
    }
    links.resolved_type = Some(type_);
    Ok(links)
}

fn validate_prepared_import_value(
    store: &CanonicalTypeMapperStore,
    prepared: &PreparedSourceImportValue,
) -> Result<(), SourceImportError> {
    validate_alias_symbol(
        store,
        prepared.binding.alias_symbol,
        prepared.binding.declaration,
        prepared.binding.local_name,
        &prepared.binding.local_text,
    )?;
    let alias_links = store
        .alias_symbol_links(prepared.binding.alias_symbol)
        .ok_or_else(|| {
            invariant(SourceImportInvariant::InvalidAliasLinks(
                prepared.binding.alias_symbol,
            ))
        })?;
    if alias_links.immediate_target != Some(prepared.target_symbol)
        || alias_links.alias_target != AliasTargetState::Resolved(prepared.target_symbol)
        || alias_links.type_only_declaration.is_some()
        || store.symbol(prepared.target_symbol).is_none_or(|target| {
            target.flags() != SymbolFlags::BLOCK_SCOPED_VARIABLE
                || target.value_declaration() != Some(prepared.target_declaration)
        })
        || store.type_node_links(prepared.target_type_node) != prepared.target_type_links.as_ref()
    {
        return Err(invariant(SourceImportInvariant::PreparedStateChanged(
            prepared.binding.alias_symbol,
        )));
    }
    if prepare_value_links(store, prepared.target_symbol, prepared.type_, false)?
        != prepared.target_links
        || prepare_value_links(store, prepared.binding.alias_symbol, prepared.type_, true)?
            != prepared.alias_links
    {
        return Err(invariant(SourceImportInvariant::PreparedStateChanged(
            prepared.binding.alias_symbol,
        )));
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;

    use ts_ast::{FileId, NodeId};
    use ts_binder::{
        CanonicalBinder, CanonicalModuleState, CanonicalNameResolverOptions,
        CanonicalSourceFileFacts, CanonicalSourceLanguage, EscapedName,
    };
    use ts_parser::{ParseResult, parse_source_file};

    use super::*;
    use crate::semantic::{
        AliasSymbolLinks, IntrinsicBootstrapOptions, SymbolNodeLinks,
        global_types::initialize_global_library_types,
        module_resolution::{
            CanonicalModuleResolutionEntry, CanonicalModuleResolutionManifest,
            CanonicalModuleResolutionManifestInput, CanonicalModuleResolutionMode,
            CanonicalResolvedModuleInput, validate_module_resolution_manifest,
        },
        production::GlobalMergeCompletion,
    };

    #[derive(Clone, Copy)]
    struct Route {
        source: usize,
        specifier: usize,
        target: Option<usize>,
    }

    struct FixtureFile {
        file: FileId,
        parsed: ParseResult,
    }

    struct Fixture {
        files: Vec<FixtureFile>,
        bound: BTreeMap<FileId, BoundFile>,
        manifest: CanonicalModuleResolutionManifest,
        global_types: CanonicalGlobalTypes,
        store: CanonicalTypeMapperStore,
    }

    impl Fixture {
        fn plan_import(&self, source: usize, import: usize) -> SourceImportPlan {
            let file = &self.files[source];
            let bound = self.bound.get(&file.file).unwrap();
            let declaration = file
                .parsed
                .arena
                .iter()
                .filter_map(|(node, record)| {
                    (record.kind == SyntaxKind::ImportDeclaration).then_some(node)
                })
                .nth(import)
                .expect("fixture contains requested import");
            plan_top_level_named_value_import(
                &file.parsed.arena,
                bound,
                &self.store,
                NodeRef::new(file.parsed.arena.id(), file.file, declaration),
            )
            .unwrap()
        }

        fn plan_type_import(&self, source: usize, import: usize) -> SourceImportPlan {
            let file = &self.files[source];
            let bound = self.bound.get(&file.file).unwrap();
            let declaration = file
                .parsed
                .arena
                .iter()
                .filter_map(|(node, record)| {
                    (record.kind == SyntaxKind::ImportDeclaration).then_some(node)
                })
                .nth(import)
                .expect("fixture contains requested import");
            plan_top_level_named_type_import(
                &file.parsed.arena,
                bound,
                &self.store,
                NodeRef::new(file.parsed.arena.id(), file.file, declaration),
            )
            .unwrap()
        }
    }

    fn parsed(source: &str) -> ParseResult {
        let parsed = parse_source_file(source);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        parsed
    }

    fn facts(file: FileId) -> CanonicalSourceFileFacts {
        CanonicalSourceFileFacts::new(
            EscapedName::source(format!("\"/project/{}.ts\"", file.index())),
            CanonicalSourceLanguage::TypeScript,
            false,
            CanonicalModuleState::External,
        )
    }

    fn module_specifiers(parsed: &ParseResult) -> Vec<NodeId> {
        let mut specifiers = parsed
            .arena
            .iter()
            .filter_map(|(_, record)| match &record.data {
                NodeData::ImportDeclaration(import) => Some(import.module_specifier),
                NodeData::ExportDeclaration(export) => export.module_specifier,
                _ => None,
            })
            .collect::<Vec<_>>();
        specifiers.sort_unstable_by_key(|node| parsed.arena.get(*node).unwrap().range.start);
        specifiers
    }

    fn fixture(sources: &[&str], routes: &[Route]) -> Fixture {
        let files = sources
            .iter()
            .enumerate()
            .map(|(index, source)| {
                let index = u32::try_from(index).expect("fixture file count fits u32");
                FixtureFile {
                    file: FileId::new(700 + index),
                    parsed: parsed(source),
                }
            })
            .collect::<Vec<_>>();
        let mut binder = CanonicalBinder::new();
        for file in &files {
            binder
                .bind_source_file_with_facts(
                    &file.parsed.arena,
                    file.parsed.source_file,
                    file.file,
                    facts(file.file),
                )
                .unwrap();
        }
        for file in &files {
            binder
                .bind_typescript_declaration_slice(&file.parsed.arena, file.file)
                .unwrap();
        }
        let (symbols, bound) = binder.finish().try_into_parts().unwrap();
        let entries = routes.iter().map(|route| {
            let source = &files[route.source];
            let specifier = module_specifiers(&source.parsed)[route.specifier];
            let reference = NodeRef::new(source.parsed.arena.id(), source.file, specifier);
            match route.target {
                Some(target) => CanonicalModuleResolutionEntry::resolved(
                    reference,
                    CanonicalResolvedModuleInput::new(
                        files[target].file,
                        CanonicalModuleResolutionMode::Esm,
                        CanonicalModuleResolutionMode::Esm,
                    ),
                ),
                None => CanonicalModuleResolutionEntry::unresolved(reference),
            }
        });
        let manifest = validate_module_resolution_manifest(
            CanonicalModuleResolutionManifestInput::new(entries),
            &symbols,
            files.iter().map(|file| {
                (
                    file.file,
                    &file.parsed.arena,
                    bound.get(&file.file).unwrap(),
                )
            }),
        )
        .unwrap();
        let mut store = CanonicalTypeMapperStore::from_symbol_store(symbols);
        for file in &files {
            assert!(
                store
                    .register_source_file(&file.parsed.arena, file.parsed.source_file, file.file)
                    .is_some()
            );
        }
        store
            .initialize_intrinsic_bootstrap(IntrinsicBootstrapOptions::default())
            .unwrap();
        let sources = || {
            files.iter().map(|file| {
                (
                    &file.parsed.arena,
                    bound.get(&file.file).expect("fixture bound every file"),
                )
            })
        };
        let declared_host = DeclaredTypeHost::new_after_global_merge(
            sources(),
            GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
        )
        .unwrap();
        let globals = store.intrinsic_bootstrap().unwrap().globals;
        let global_types =
            initialize_global_library_types(&mut store, &declared_host, globals, false).unwrap();
        Fixture {
            files,
            bound,
            manifest,
            global_types,
            store,
        }
    }

    fn resolve_all(
        fixture: &mut Fixture,
        bindings: &[SourceImportBindingPlan],
    ) -> Result<Vec<ResolvedSourceImportBinding>, SourceImportError> {
        let Fixture {
            files,
            bound,
            manifest,
            store,
            ..
        } = fixture;
        let sources = || {
            files.iter().map(|file| {
                (
                    &file.parsed.arena,
                    bound.get(&file.file).expect("fixture bound every file"),
                )
            })
        };
        let mut alias_host = ProductionAliasTargetHost::new(store, sources(), manifest).unwrap();
        bindings
            .iter()
            .map(|binding| resolve_source_import_binding(store, &mut alias_host, binding))
            .collect()
    }

    fn resolve_all_types(
        fixture: &mut Fixture,
        bindings: &[SourceImportBindingPlan],
    ) -> Result<Vec<ResolvedSourceTypeImportBinding>, SourceImportError> {
        let Fixture {
            files,
            bound,
            manifest,
            store,
            ..
        } = fixture;
        let sources = || {
            files.iter().map(|file| {
                (
                    &file.parsed.arena,
                    bound.get(&file.file).expect("fixture bound every file"),
                )
            })
        };
        let declared_host = DeclaredTypeHost::new_after_global_merge(
            sources(),
            GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
        )
        .unwrap();
        let mut alias_host = ProductionAliasTargetHost::new(store, sources(), manifest).unwrap();
        bindings
            .iter()
            .map(|binding| {
                resolve_source_type_import_binding(store, &mut alias_host, &declared_host, binding)
            })
            .collect()
    }

    fn type_reference(fixture: &Fixture, source: usize, name: &str) -> NodeRef {
        let file = &fixture.files[source];
        file.parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                let NodeData::TypeReferenceNode(reference) = &record.data else {
                    return None;
                };
                let name_node = file.parsed.arena.get(reference.type_name)?;
                matches!(
                    &name_node.data,
                    NodeData::Identifier(identifier) if identifier.text == name
                )
                .then_some(NodeRef::new(file.parsed.arena.id(), file.file, node))
            })
            .unwrap_or_else(|| panic!("fixture contains type reference {name}"))
    }

    fn plan_type_reference_capability(
        fixture: &Fixture,
        resolved: &ResolvedSourceTypeImportBinding,
        reference: NodeRef,
    ) -> CanonicalTypeReferenceAliasTarget {
        let sources = || {
            fixture.files.iter().map(|file| {
                (
                    &file.parsed.arena,
                    fixture
                        .bound
                        .get(&file.file)
                        .expect("fixture bound every file"),
                )
            })
        };
        let declared_host = DeclaredTypeHost::new_after_global_merge(
            sources(),
            GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
        )
        .unwrap();
        plan_source_type_import_reference(&fixture.store, &declared_host, resolved, reference)
            .unwrap()
    }

    fn query_imported_type(
        fixture: &mut Fixture,
        reference: NodeRef,
        capability: CanonicalTypeReferenceAliasTarget,
    ) -> Result<TypeId, DeclaredTypeError> {
        let Fixture {
            files,
            bound,
            global_types,
            store,
            ..
        } = fixture;
        let sources = || {
            files.iter().map(|file| {
                (
                    &file.parsed.arena,
                    bound.get(&file.file).expect("fixture bound every file"),
                )
            })
        };
        let declared_host = DeclaredTypeHost::new_after_global_merge(
            sources(),
            GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
        )
        .unwrap();
        CanonicalTypeQuery::new_with_global_types(
            store,
            &declared_host,
            global_types,
            CanonicalCheckerOptions::default(),
            &mut CanonicalCheckerDiagnostics::default(),
        )?
        .with_type_reference_alias_targets([capability])?
        .get_type_from_type_node(reference)
    }

    fn query_declared_type(
        fixture: &mut Fixture,
        symbol: SemanticSymbolId,
    ) -> Result<TypeId, DeclaredTypeError> {
        let Fixture {
            files,
            bound,
            global_types,
            store,
            ..
        } = fixture;
        let sources = || {
            files.iter().map(|file| {
                (
                    &file.parsed.arena,
                    bound.get(&file.file).expect("fixture bound every file"),
                )
            })
        };
        let declared_host = DeclaredTypeHost::new_after_global_merge(
            sources(),
            GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
        )
        .unwrap();
        CanonicalTypeQuery::new_with_global_types(
            store,
            &declared_host,
            global_types,
            CanonicalCheckerOptions::default(),
            &mut CanonicalCheckerDiagnostics::default(),
        )?
        .get_declared_type_of_symbol(symbol)
    }

    fn prepare_one(
        fixture: &mut Fixture,
        resolved: &ResolvedSourceImportBinding,
        read: &PlannedSourceImportRead,
    ) -> Result<PreparedSourceImportValue, SourceImportError> {
        let Fixture {
            files,
            bound,
            global_types,
            store,
            ..
        } = fixture;
        let sources = || {
            files.iter().map(|file| {
                (
                    &file.parsed.arena,
                    bound.get(&file.file).expect("fixture bound every file"),
                )
            })
        };
        let declared_host = DeclaredTypeHost::new_after_global_merge(
            sources(),
            GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
        )
        .unwrap();
        prepare_source_import_value(
            store,
            &declared_host,
            global_types,
            CanonicalCheckerOptions::default(),
            &mut CanonicalCheckerDiagnostics::default(),
            resolved,
            read,
        )
    }

    fn publish_for_test(
        store: &mut CanonicalTypeMapperStore,
        prepared: &[PreparedSourceImportValue],
    ) {
        let publications = preflight_prepared_source_import_publications(store, prepared).unwrap();
        for publication in publications {
            assert!(store.set_value_symbol_links(publication.symbol, publication.links));
        }
    }

    fn identifier_initializer(fixture: &Fixture, source: usize, name: &str) -> NodeRef {
        let file = &fixture.files[source];
        file.parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                let NodeData::Identifier(identifier) = &record.data else {
                    return None;
                };
                if identifier.text != name {
                    return None;
                }
                let parent = record
                    .parent
                    .and_then(|parent| file.parsed.arena.get(parent))?;
                matches!(
                    &parent.data,
                    NodeData::VariableDeclaration(variable) if variable.initializer == Some(node)
                )
                .then_some(NodeRef::new(file.parsed.arena.id(), file.file, node))
            })
            .expect("fixture contains requested identifier initializer")
    }

    fn binding_symbol(plan: &SourceImportPlan, local: &str) -> SemanticSymbolId {
        plan.bindings
            .iter()
            .find(|binding| binding.local_text == local)
            .unwrap_or_else(|| panic!("missing import binding {local}"))
            .alias_symbol
    }

    fn direct_export(fixture: &Fixture, source: usize, name: &str) -> SemanticSymbolId {
        let bound = fixture.bound.get(&fixture.files[source].file).unwrap();
        let module = bound.symbol(bound.source_file()).unwrap();
        let exports = fixture.store.symbol(module).unwrap().exports().unwrap();
        fixture
            .store
            .symbol_table(exports)
            .unwrap()
            .get_source(name)
            .unwrap()
    }

    #[test]
    fn type_only_alias_import_is_exact_in_importer_first_cold_and_warm_orders() {
        let mut fixture = fixture(
            &[
                r#"
                    import type { User as LocalUser } from "./target";
                    const user: LocalUser = { id: 1 };
                "#,
                r"export type User = { id: number };",
            ],
            &[Route {
                source: 0,
                specifier: 0,
                target: Some(1),
            }],
        );
        let plan = fixture.plan_type_import(0, 0);
        assert_eq!(plan.bindings.len(), 1);
        assert_eq!(plan.bindings[0].imported_text, "User");
        assert_eq!(plan.bindings[0].local_text, "LocalUser");
        let reference = type_reference(&fixture, 0, "LocalUser");
        let resolved = resolve_all_types(&mut fixture, &plan.bindings).unwrap();
        let capability = plan_type_reference_capability(&fixture, &resolved[0], reference);
        let imported = query_imported_type(&mut fixture, reference, capability).unwrap();
        let target = direct_export(&fixture, 1, "User");
        assert_eq!(
            fixture
                .store
                .type_alias_links(target)
                .and_then(|links| links.declared_type),
            Some(imported)
        );
        assert_eq!(
            fixture
                .store
                .symbol_node_links(reference)
                .and_then(|links| links.resolved_symbol),
            Some(target)
        );
        assert_eq!(
            fixture
                .store
                .value_symbol_links(plan.bindings[0].alias_symbol),
            None
        );

        let warm_resolved = resolve_all_types(&mut fixture, &plan.bindings).unwrap();
        assert_eq!(warm_resolved, resolved);
        let warm_capability =
            plan_type_reference_capability(&fixture, &warm_resolved[0], reference);
        assert_eq!(
            query_imported_type(&mut fixture, reference, warm_capability).unwrap(),
            imported
        );
    }

    #[test]
    fn type_only_interface_import_is_exact_after_target_first_query() {
        let mut fixture = fixture(
            &[
                r#"
                    import type { User } from "./target";
                    const user: User = { id: 1 };
                "#,
                r"export interface User { id: number }",
            ],
            &[Route {
                source: 0,
                specifier: 0,
                target: Some(1),
            }],
        );
        let target = direct_export(&fixture, 1, "User");
        let target_first = query_declared_type(&mut fixture, target).unwrap();
        let plan = fixture.plan_type_import(0, 0);
        let reference = type_reference(&fixture, 0, "User");
        let resolved = resolve_all_types(&mut fixture, &plan.bindings).unwrap();
        let capability = plan_type_reference_capability(&fixture, &resolved[0], reference);
        assert_eq!(
            query_imported_type(&mut fixture, reference, capability).unwrap(),
            target_first
        );
        let warm_resolved = resolve_all_types(&mut fixture, &plan.bindings).unwrap();
        let warm_capability =
            plan_type_reference_capability(&fixture, &warm_resolved[0], reference);
        assert_eq!(
            query_imported_type(&mut fixture, reference, warm_capability).unwrap(),
            target_first
        );
    }

    #[test]
    fn exact_type_import_capability_rejects_poisoned_warm_reference_links() {
        let mut fixture = fixture(
            &[
                r#"
                    import type { User } from "./target";
                    const user: User = { id: 1 };
                "#,
                r"export type User = { id: number };",
            ],
            &[Route {
                source: 0,
                specifier: 0,
                target: Some(1),
            }],
        );
        let plan = fixture.plan_type_import(0, 0);
        let reference = type_reference(&fixture, 0, "User");
        let resolved = resolve_all_types(&mut fixture, &plan.bindings).unwrap();
        let capability = plan_type_reference_capability(&fixture, &resolved[0], reference);
        assert!(fixture.store.set_symbol_node_links(
            reference,
            SymbolNodeLinks {
                resolved_symbol: Some(plan.bindings[0].alias_symbol),
            },
        ));
        assert!(matches!(
            query_imported_type(&mut fixture, reference, capability),
            Err(DeclaredTypeError::TypeNodeUnavailable(
                super::super::type_nodes::TypeNodeUnavailable::InvalidCachedSymbol {
                    node,
                    symbol,
                }
            )) if node == reference && symbol == plan.bindings[0].alias_symbol
        ));
    }

    #[test]
    fn unused_type_import_stays_lazy_and_value_use_is_a_typed_boundary() {
        let mut fixture = fixture(
            &[
                r#"
                    import type { User } from "./target";
                    const runtime = User;
                "#,
                r"export type User = { id: number };",
            ],
            &[Route {
                source: 0,
                specifier: 0,
                target: Some(1),
            }],
        );
        let plan = fixture.plan_type_import(0, 0);
        let resolved = resolve_all_types(&mut fixture, &plan.bindings).unwrap();
        let target = resolved[0].target_symbol;
        assert_eq!(
            fixture
                .store
                .type_alias_links(target)
                .and_then(|links| links.declared_type),
            None,
            "declaration resolution does not eagerly type an unused import"
        );
        assert_eq!(
            fixture
                .store
                .value_symbol_links(plan.bindings[0].alias_symbol),
            None
        );
        let read = identifier_initializer(&fixture, 0, "User");
        let file = &fixture.files[0];
        let bound = fixture.bound.get(&file.file).unwrap();
        assert_eq!(
            reject_source_type_import_value_use(
                &file.parsed.arena,
                bound,
                &fixture.store,
                &resolved[0],
                read,
                "User",
                plan.bindings[0].alias_symbol,
            ),
            Err(SourceImportError::Unsupported(
                SourceImportUnsupported::ValueUseOfTypeOnlyImport(read)
            ))
        );
        assert_eq!(
            fixture
                .store
                .value_symbol_links(plan.bindings[0].alias_symbol),
            None
        );
    }

    #[test]
    fn cold_and_warm_direct_and_renamed_imports_type_only_used_bindings() {
        let mut fixture = fixture(
            &[
                r#"
                    import { numberValue, textValue as localText } from "./target";
                    const result: string = localText;
                "#,
                r#"
                    export const numberValue: number = 1;
                    export const textValue: string = "ok";
                "#,
            ],
            &[Route {
                source: 0,
                specifier: 0,
                target: Some(1),
            }],
        );
        let plan = fixture.plan_import(0, 0);
        assert_eq!(plan.bindings.len(), 2);
        assert_eq!(plan.bindings[1].imported_text, "textValue");
        assert_eq!(plan.bindings[1].local_text, "localText");

        let read = identifier_initializer(&fixture, 0, "localText");
        let bound = fixture.bound.get(&fixture.files[0].file).unwrap();
        let planned_read = plan_source_import_identifier_read(
            &fixture.files[0].parsed.arena,
            bound,
            &fixture.store,
            &plan.bindings[1],
            read,
            "localText",
            plan.bindings[1].alias_symbol,
        )
        .unwrap();
        assert_eq!(planned_read.resolved_symbol, plan.bindings[1].alias_symbol);
        assert_eq!(planned_read.value_symbol, plan.bindings[1].alias_symbol);

        let resolved = resolve_all(&mut fixture, &plan.bindings).unwrap();
        assert_eq!(resolved.len(), 2);
        let prepared = vec![prepare_one(&mut fixture, &resolved[1], &planned_read).unwrap()];
        let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
        assert_eq!(prepared[0].type_, bootstrap.string_type);
        assert_eq!(
            fixture
                .store
                .value_symbol_links(resolved[0].binding.alias_symbol),
            None,
            "an unused binding resolves but is never value-typed"
        );
        assert_eq!(
            fixture.store.value_symbol_links(resolved[0].target_symbol),
            None
        );
        for value in &prepared {
            assert_eq!(fixture.store.value_symbol_links(value.target_symbol), None);
            assert_eq!(
                fixture.store.value_symbol_links(value.binding.alias_symbol),
                None
            );
        }
        let publications =
            preflight_prepared_source_import_publications(&fixture.store, &prepared).unwrap();
        assert_eq!(publications.len(), 2);
        assert_eq!(
            fixture
                .store
                .value_symbol_links(resolved[0].binding.alias_symbol),
            None,
            "preflight itself performs no writes"
        );
        publish_for_test(&mut fixture.store, &prepared);
        for value in &prepared {
            assert_eq!(
                fixture
                    .store
                    .value_symbol_links(value.target_symbol)
                    .and_then(|links| links.resolved_type),
                Some(value.type_)
            );
            assert_eq!(
                fixture
                    .store
                    .value_symbol_links(value.binding.alias_symbol)
                    .and_then(|links| links.resolved_type),
                Some(value.type_)
            );
        }

        assert_eq!(
            fixture
                .store
                .value_symbol_links(resolved[0].binding.alias_symbol),
            None
        );
        assert_eq!(
            fixture.store.value_symbol_links(resolved[0].target_symbol),
            None
        );

        let warm_resolved = resolve_all(&mut fixture, &plan.bindings).unwrap();
        assert_eq!(warm_resolved, resolved);
        let warm = vec![prepare_one(&mut fixture, &warm_resolved[1], &planned_read).unwrap()];
        assert_eq!(warm, prepared);
        publish_for_test(&mut fixture.store, &warm);
    }

    #[test]
    fn poisoned_late_binding_blocks_every_prepared_publication() {
        let mut fixture = fixture(
            &[
                r#"
                    import { first, second } from "./target";
                    const one: number = first;
                    const two: string = second;
                "#,
                r#"
                    export const first: number = 1;
                    export const second: string = "two";
                "#,
            ],
            &[Route {
                source: 0,
                specifier: 0,
                target: Some(1),
            }],
        );
        let plan = fixture.plan_import(0, 0);
        let first_read_node = identifier_initializer(&fixture, 0, "first");
        let second_read_node = identifier_initializer(&fixture, 0, "second");
        let bound = fixture.bound.get(&fixture.files[0].file).unwrap();
        let first_read = plan_source_import_identifier_read(
            &fixture.files[0].parsed.arena,
            bound,
            &fixture.store,
            &plan.bindings[0],
            first_read_node,
            "first",
            plan.bindings[0].alias_symbol,
        )
        .unwrap();
        let second_read = plan_source_import_identifier_read(
            &fixture.files[0].parsed.arena,
            bound,
            &fixture.store,
            &plan.bindings[1],
            second_read_node,
            "second",
            plan.bindings[1].alias_symbol,
        )
        .unwrap();
        let resolved = resolve_all(&mut fixture, &plan.bindings).unwrap();
        let prepared = vec![
            prepare_one(&mut fixture, &resolved[0], &first_read).unwrap(),
            prepare_one(&mut fixture, &resolved[1], &second_read).unwrap(),
        ];
        let first_alias = binding_symbol(&plan, "first");
        let second_alias = binding_symbol(&plan, "second");
        assert!(fixture.store.set_value_symbol_links(
            second_alias,
            ValueSymbolLinks {
                function_or_constructor_checked: true,
                ..ValueSymbolLinks::default()
            },
        ));

        assert_eq!(
            preflight_prepared_source_import_publications(&fixture.store, &prepared),
            Err(SourceImportError::Invariant(
                SourceImportInvariant::InvalidAliasValueLinks(second_alias)
            ))
        );
        assert_eq!(fixture.store.value_symbol_links(first_alias), None);
        assert_eq!(
            fixture.store.value_symbol_links(prepared[0].target_symbol),
            None
        );
    }

    #[test]
    fn unresolved_module_resolution_is_retryable_and_publishes_no_value_links() {
        let mut fixture = fixture(
            &[
                r#"import { value } from "./target";"#,
                r"export const value: number = 1;",
            ],
            &[Route {
                source: 0,
                specifier: 0,
                target: None,
            }],
        );
        let plan = fixture.plan_import(0, 0);
        let alias = plan.bindings[0].alias_symbol;
        let error = resolve_all(&mut fixture, &plan.bindings).unwrap_err();
        assert!(matches!(
            error,
            SourceImportError::Alias(CanonicalAliasResolutionError::TargetUnavailable {
                alias: failed,
                reason: super::super::alias::CanonicalAliasTargetUnavailable::ModuleResolutionUnresolved(_),
            }) if failed == alias
        ));
        assert_eq!(fixture.store.value_symbol_links(alias), None);
    }

    #[test]
    fn direct_import_alias_cycle_fails_closed_before_target_typing() {
        let mut fixture = fixture(
            &[
                r#"
                    import { value } from "./b";
                    export { value as loop } from "./b";
                "#,
                r#"export { loop as value } from "./a";"#,
            ],
            &[
                Route {
                    source: 0,
                    specifier: 0,
                    target: Some(1),
                },
                Route {
                    source: 0,
                    specifier: 1,
                    target: Some(1),
                },
                Route {
                    source: 1,
                    specifier: 0,
                    target: Some(0),
                },
            ],
        );
        let plan = fixture.plan_import(0, 0);
        let alias = plan.bindings[0].alias_symbol;
        let first = resolve_all(&mut fixture, &plan.bindings).unwrap_err();
        let SourceImportError::CircularAlias {
            alias: failed,
            events,
        } = first
        else {
            panic!("expected circular alias boundary, got {first:?}");
        };
        assert_eq!(failed, alias);
        assert!(
            !events.is_empty(),
            "cold resolution owns the diagnostic event"
        );

        let warm = resolve_all(&mut fixture, &plan.bindings).unwrap_err();
        let SourceImportError::CircularAlias {
            alias: failed,
            events,
        } = warm
        else {
            panic!("expected cached circular alias boundary, got {warm:?}");
        };
        assert_eq!(failed, alias);
        assert!(
            events.is_empty(),
            "warm resolution does not reissue the event"
        );
        assert_eq!(fixture.store.value_symbol_links(alias), None);
    }

    #[test]
    fn consistent_warm_alias_cache_cannot_redirect_manifest_target() {
        let mut fixture = fixture(
            &[
                r#"import { value } from "./selected";"#,
                r"export const value: number = 1;",
                r#"export const value: string = "wrong";"#,
            ],
            &[Route {
                source: 0,
                specifier: 0,
                target: Some(1),
            }],
        );
        let plan = fixture.plan_import(0, 0);
        let alias = plan.bindings[0].alias_symbol;
        let selected = direct_export(&fixture, 1, "value");
        let wrong = direct_export(&fixture, 2, "value");
        assert_ne!(selected, wrong);
        assert!(fixture.store.set_alias_symbol_links(
            alias,
            AliasSymbolLinks {
                immediate_target: Some(wrong),
                alias_target: AliasTargetState::Resolved(wrong),
                ..AliasSymbolLinks::default()
            },
        ));

        assert_eq!(
            resolve_all(&mut fixture, &plan.bindings),
            Err(SourceImportError::Invariant(
                SourceImportInvariant::InvalidAliasLinks(alias)
            )),
            "the production host and manifest, not self-consistent sparse links, own directness"
        );
        assert_eq!(fixture.store.value_symbol_links(alias), None);
        assert_eq!(fixture.store.value_symbol_links(selected), None);
        assert_eq!(fixture.store.value_symbol_links(wrong), None);
    }

    #[test]
    fn unannotated_target_and_non_value_import_syntax_remain_explicit_boundaries() {
        let mut unannotated = fixture(
            &[
                r#"
                    import { value } from "./target";
                    const result = value;
                "#,
                r"export const value = 1;",
            ],
            &[Route {
                source: 0,
                specifier: 0,
                target: Some(1),
            }],
        );
        let plan = unannotated.plan_import(0, 0);
        let read_node = identifier_initializer(&unannotated, 0, "value");
        let bound = unannotated.bound.get(&unannotated.files[0].file).unwrap();
        let read = plan_source_import_identifier_read(
            &unannotated.files[0].parsed.arena,
            bound,
            &unannotated.store,
            &plan.bindings[0],
            read_node,
            "value",
            plan.bindings[0].alias_symbol,
        )
        .unwrap();
        let resolved = resolve_all(&mut unannotated, &plan.bindings).unwrap();
        assert!(matches!(
            prepare_one(&mut unannotated, &resolved[0], &read),
            Err(SourceImportError::Unsupported(
                SourceImportUnsupported::MissingTargetAnnotation(_)
            ))
        ));

        for source in [
            r#"import type { value } from "./target";"#,
            r#"import DefaultValue from "./target";"#,
            r#"import { type value } from "./target";"#,
        ] {
            let fixture = fixture(&[source, r"export const value: number = 1;"], &[]);
            let file = &fixture.files[0];
            let bound = fixture.bound.get(&file.file).unwrap();
            let declaration = file
                .parsed
                .arena
                .iter()
                .find_map(|(node, record)| {
                    (record.kind == SyntaxKind::ImportDeclaration).then_some(node)
                })
                .unwrap();
            assert!(matches!(
                plan_top_level_named_value_import(
                    &file.parsed.arena,
                    bound,
                    &fixture.store,
                    NodeRef::new(file.parsed.arena.id(), file.file, declaration),
                ),
                Err(SourceImportError::Unsupported(_))
            ));
        }
    }
}
