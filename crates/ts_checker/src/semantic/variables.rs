//! Read-only symbol planning for the dependency-closed top-level variable slice.
//!
//! The source checker owns expression execution and type publication. This module
//! proves the binder/resolver route for one ordinary top-level variable or one
//! read of an already-planned variable without mutating checker state.

use std::collections::HashSet;

use ts_ast::{NodeArena, NodeRef};
use ts_binder::{
    BoundFile, CanonicalNameResolutionError, CanonicalNameResolver, CanonicalResolutionLocation,
    CheckFlags, SemanticSymbolId, SymbolFlags,
};

use super::{CanonicalTypeMapperStore, DeclaredTypeError, DeclaredTypeHost, TypeId};

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

/// Valid TypeScript symbol routes intentionally outside this source slice.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum VariableUnsupported {
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
    /// Reading this prior declaration requires upstream control-flow/current-type
    /// state. The installed slice only proves unannotated inferred `const` reads.
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
    DuplicateStagedValueType(SemanticSymbolId),
    UnexpectedStagedValueType(SemanticSymbolId),
    InvalidStagedValueType {
        symbol: SemanticSymbolId,
        type_: TypeId,
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
    if flags != SymbolFlags::FUNCTION_SCOPED_VARIABLE && flags != SymbolFlags::BLOCK_SCOPED_VARIABLE
    {
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
    let [declaration] = declarations else {
        return Err(VariablePlanError::Unsupported(
            VariableUnsupported::NonUniqueDeclaration {
                node,
                symbol: routed.target,
                declaration_count: declarations.len(),
            },
        ));
    };
    let declaration = *declaration;
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
    if record.flags() != expected_flags {
        return Err(VariablePlanError::Unsupported(
            VariableUnsupported::NonVariableSymbol {
                node: declaration,
                symbol,
                flags: record.flags(),
            },
        ));
    }
    if record.check_flags() != CheckFlags::NONE
        || record.members().is_some()
        || record.exports().is_some()
        || record.export_symbol().is_some()
    {
        return Err(VariableInvariant::InvalidSymbolShape(symbol).into());
    }
    let declarations = record
        .declarations()
        .ok_or(VariableInvariant::MissingDeclarations(symbol))?;
    let [actual] = declarations else {
        return Err(VariablePlanError::Unsupported(
            VariableUnsupported::NonUniqueDeclaration {
                node: declaration,
                symbol,
                declaration_count: declarations.len(),
            },
        ));
    };
    if *actual != declaration {
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
