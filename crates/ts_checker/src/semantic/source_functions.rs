//! Read-only binder and resolver proof for source function declarations.
//!
//! Callable construction belongs to `source_callables`; source checking owns
//! statement order and body execution. This module only proves the exact
//! top-level function value symbol (including direct-export routing) and the
//! hoisted identifier route used by source expressions.

use std::collections::HashSet;

use ts_ast::NodeRef;
use ts_binder::{
    BoundFile, CanonicalNameResolutionError, CanonicalNameResolver, CanonicalResolutionLocation,
    CheckFlags, SemanticSymbolId, SymbolFlags,
};

use super::{CanonicalTypeMapperStore, DeclaredTypeError, DeclaredTypeHost, TypeId};

/// Binder identities retained for one exact top-level function declaration.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct PlannedTopLevelFunction {
    pub(super) declaration: NodeRef,
    pub(super) owner_symbol: SemanticSymbolId,
}

/// Exact resolver identities retained for one hoisted function read.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct PlannedFunctionRead {
    /// The symbol cached by upstream before direct-export routing.
    pub(super) resolved_symbol: SemanticSymbolId,
    /// The `FUNCTION` symbol whose value links own the callable `TypeId`.
    pub(super) value_symbol: SemanticSymbolId,
}

/// Valid TypeScript function forms outside the first source-function slice.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum SourceFunctionUnsupported {
    UnresolvedIdentifier(NodeRef),
    ResolverDeferred {
        node: NodeRef,
        error: CanonicalNameResolutionError,
    },
    AliasSymbol {
        node: NodeRef,
        symbol: SemanticSymbolId,
    },
    MergedSymbol {
        node: NodeRef,
        source: SemanticSymbolId,
        target: SemanticSymbolId,
    },
    NonFunctionSymbol {
        node: NodeRef,
        symbol: SemanticSymbolId,
        flags: SymbolFlags,
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
    ExpandoFunction {
        node: NodeRef,
        symbol: SemanticSymbolId,
    },
    IdentifierNotHoisted {
        node: NodeRef,
        symbol: SemanticSymbolId,
        declaration: NodeRef,
    },
    Callable(NodeRef),
    FunctionBody(NodeRef),
}

/// Malformed binder, resolver, or sparse-link provenance for source functions.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum SourceFunctionInvariant {
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
    InvalidSymbolNodeCache {
        node: NodeRef,
        cached: Option<SemanticSymbolId>,
        expected: SemanticSymbolId,
    },
    DuplicateDeclaration(NodeRef),
    MissingDeclaration(NodeRef),
    InvalidStatementIndex(usize),
    Callable(NodeRef),
    MissingCallableType(SemanticSymbolId),
    CallableTypeMismatch {
        symbol: SemanticSymbolId,
        expected: TypeId,
        actual: TypeId,
    },
    NameResolution(CanonicalNameResolutionError),
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum SourceFunctionPlanError {
    Unsupported(SourceFunctionUnsupported),
    Invariant(SourceFunctionInvariant),
    DeclaredType(DeclaredTypeError),
}

impl From<SourceFunctionInvariant> for SourceFunctionPlanError {
    fn from(error: SourceFunctionInvariant) -> Self {
        Self::Invariant(error)
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct RoutedValueSymbol {
    resolved: SemanticSymbolId,
    target: SemanticSymbolId,
    export_local: Option<SemanticSymbolId>,
}

/// Proves the exact value-symbol owner for one named top-level function.
pub(super) fn plan_top_level_function(
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    declaration: NodeRef,
    name: NodeRef,
    name_text: &str,
    exported: bool,
) -> Result<PlannedTopLevelFunction, SourceFunctionPlanError> {
    let raw =
        bound
            .symbol(declaration)
            .ok_or(SourceFunctionInvariant::MissingDeclarationSymbol(
                declaration,
            ))?;
    let merged = store
        .get_merged_symbol(raw)
        .ok_or(SourceFunctionInvariant::InvalidMergedSymbol(raw))?;
    if merged != raw {
        return Err(SourceFunctionPlanError::Unsupported(
            SourceFunctionUnsupported::MergedSymbol {
                node: declaration,
                source: raw,
                target: merged,
            },
        ));
    }
    validate_function_target(store, declaration, name, name_text, merged)?;

    let local = bound.local_symbol(declaration);
    let expected_local = if exported {
        let local = local.ok_or(SourceFunctionInvariant::MissingExportLocal(declaration))?;
        validate_export_local(store, local, declaration, merged, name_text)?;
        Some(local)
    } else {
        None
    };
    if local != expected_local {
        return Err(SourceFunctionInvariant::LocalExportSymbolMismatch {
            declaration,
            expected: expected_local,
            actual: local,
        }
        .into());
    }
    validate_target_parent(bound, store, merged, exported)?;
    Ok(PlannedTopLevelFunction {
        declaration,
        owner_symbol: merged,
    })
}

/// Resolves one identifier as a precollected, hoisted source function.
///
/// The caller invokes this only after the independent variable planner has
/// resolved the same identifier and rejected its routed target specifically as
/// a `FUNCTION`. Repeating resolution here therefore cannot swallow or
/// reclassify unresolved-name, alias, or callback-host failures from the
/// established variable path. Every function-specific invariant is fail-closed.
#[allow(clippy::too_many_arguments)]
pub(super) fn plan_function_identifier_read(
    arena: &ts_ast::NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    hoisted_functions: &HashSet<SemanticSymbolId>,
    node: NodeRef,
    name: &str,
) -> Result<PlannedFunctionRead, SourceFunctionPlanError> {
    let mut callback_host = host
        .name_resolver_host(store)
        .map_err(SourceFunctionPlanError::DeclaredType)?;
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
            return Err(SourceFunctionPlanError::Unsupported(
                SourceFunctionUnsupported::UnresolvedIdentifier(node),
            ));
        }
        Err(CanonicalNameResolutionError::AliasResolutionUnavailable(symbol)) => {
            return Err(SourceFunctionPlanError::Unsupported(
                SourceFunctionUnsupported::AliasSymbol { node, symbol },
            ));
        }
        Err(error) => return Err(name_resolution_error(node, error)),
    };
    let routed = route_value_symbol(store, node, raw_symbol)?;
    let record = store
        .symbol(routed.target)
        .ok_or(SourceFunctionInvariant::InvalidSymbol(routed.target))?;
    if record.flags().intersects(SymbolFlags::ALIAS) {
        return Err(SourceFunctionPlanError::Unsupported(
            SourceFunctionUnsupported::AliasSymbol {
                node,
                symbol: routed.target,
            },
        ));
    }
    if record.flags() != SymbolFlags::FUNCTION {
        return Err(SourceFunctionPlanError::Unsupported(
            SourceFunctionUnsupported::NonFunctionSymbol {
                node,
                symbol: routed.target,
                flags: record.flags(),
            },
        ));
    }
    let declarations = record
        .declarations()
        .ok_or(SourceFunctionInvariant::MissingDeclarations(routed.target))?;
    let [declaration] = declarations else {
        return Err(SourceFunctionPlanError::Unsupported(
            SourceFunctionUnsupported::NonUniqueDeclaration {
                node,
                symbol: routed.target,
                declaration_count: declarations.len(),
            },
        ));
    };
    let declaration = *declaration;
    if declaration.file != node.file || declaration.arena != node.arena {
        return Err(SourceFunctionPlanError::Unsupported(
            SourceFunctionUnsupported::CrossFileDeclaration { node, declaration },
        ));
    }
    validate_function_target(store, declaration, node, name, routed.target)?;
    let declaration_symbol =
        bound
            .symbol(declaration)
            .ok_or(SourceFunctionInvariant::MissingDeclarationSymbol(
                declaration,
            ))?;
    let declaration_symbol = store.get_merged_symbol(declaration_symbol).ok_or(
        SourceFunctionInvariant::InvalidMergedSymbol(declaration_symbol),
    )?;
    if declaration_symbol != routed.target {
        return Err(SourceFunctionInvariant::DeclarationSymbolMismatch {
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
        return Err(SourceFunctionInvariant::LocalExportSymbolMismatch {
            declaration,
            expected: routed.export_local,
            actual: bound.local_symbol(declaration),
        }
        .into());
    }
    validate_target_parent(bound, store, routed.target, routed.export_local.is_some())?;
    if !hoisted_functions.contains(&routed.target) {
        return Err(SourceFunctionPlanError::Unsupported(
            SourceFunctionUnsupported::IdentifierNotHoisted {
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
        return Err(SourceFunctionInvariant::InvalidSymbolNodeCache {
            node,
            cached: store
                .symbol_node_links(node)
                .and_then(|links| links.resolved_symbol),
            expected: routed.resolved,
        }
        .into());
    }
    Ok(PlannedFunctionRead {
        resolved_symbol: routed.resolved,
        value_symbol: routed.target,
    })
}

fn route_value_symbol(
    store: &CanonicalTypeMapperStore,
    node: NodeRef,
    resolved: SemanticSymbolId,
) -> Result<RoutedValueSymbol, SourceFunctionPlanError> {
    let record = store
        .symbol(resolved)
        .ok_or(SourceFunctionInvariant::InvalidSymbol(resolved))?;
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
            return Err(SourceFunctionInvariant::InvalidExportLocalShape(resolved).into());
        }
        let export_symbol = record
            .export_symbol()
            .ok_or(SourceFunctionInvariant::MissingExportSymbol(resolved))?;
        if store.symbol(export_symbol).is_none() {
            return Err(SourceFunctionInvariant::InvalidExportSymbol {
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
        .ok_or(SourceFunctionInvariant::InvalidMergedSymbol(routed))?;
    if merged != routed {
        return Err(SourceFunctionPlanError::Unsupported(
            SourceFunctionUnsupported::MergedSymbol {
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

fn validate_function_target(
    store: &CanonicalTypeMapperStore,
    declaration: NodeRef,
    name: NodeRef,
    name_text: &str,
    symbol: SemanticSymbolId,
) -> Result<(), SourceFunctionPlanError> {
    let record = store
        .symbol(symbol)
        .ok_or(SourceFunctionInvariant::InvalidSymbol(symbol))?;
    if record.flags() != SymbolFlags::FUNCTION {
        return Err(SourceFunctionPlanError::Unsupported(
            SourceFunctionUnsupported::NonFunctionSymbol {
                node: declaration,
                symbol,
                flags: record.flags(),
            },
        ));
    }
    if record.exports().is_some() {
        return Err(SourceFunctionPlanError::Unsupported(
            SourceFunctionUnsupported::ExpandoFunction {
                node: declaration,
                symbol,
            },
        ));
    }
    if record.check_flags() != CheckFlags::NONE
        || record.members().is_some()
        || record.export_symbol().is_some()
    {
        return Err(SourceFunctionInvariant::InvalidSymbolShape(symbol).into());
    }
    let declarations = record
        .declarations()
        .ok_or(SourceFunctionInvariant::MissingDeclarations(symbol))?;
    let [actual] = declarations else {
        return Err(SourceFunctionPlanError::Unsupported(
            SourceFunctionUnsupported::NonUniqueDeclaration {
                node: declaration,
                symbol,
                declaration_count: declarations.len(),
            },
        ));
    };
    if *actual != declaration {
        return Err(SourceFunctionInvariant::InvalidSymbolShape(symbol).into());
    }
    if record.value_declaration() != Some(declaration) {
        return Err(SourceFunctionInvariant::ValueDeclarationMismatch {
            symbol,
            declaration,
            value_declaration: record.value_declaration(),
        }
        .into());
    }
    if record.name().as_bytes() != name_text.as_bytes() {
        return Err(SourceFunctionInvariant::IdentifierNameMismatch {
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
) -> Result<(), SourceFunctionPlanError> {
    let record = store
        .symbol(local)
        .ok_or(SourceFunctionInvariant::InvalidSymbol(local))?;
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
        return Err(SourceFunctionInvariant::InvalidExportLocalShape(local).into());
    }
    Ok(())
}

fn validate_target_parent(
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    target: SemanticSymbolId,
    exported: bool,
) -> Result<(), SourceFunctionPlanError> {
    let expected = if exported {
        let source = bound.source_file();
        let raw = bound
            .symbol(source)
            .ok_or(SourceFunctionInvariant::MissingSourceSymbol(source))?;
        let merged = store
            .get_merged_symbol(raw)
            .ok_or(SourceFunctionInvariant::InvalidMergedSymbol(raw))?;
        if merged != raw {
            return Err(SourceFunctionPlanError::Unsupported(
                SourceFunctionUnsupported::MergedSymbol {
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
        .ok_or(SourceFunctionInvariant::InvalidSymbol(target))?
        .parent();
    if actual != expected {
        return Err(SourceFunctionInvariant::InvalidTargetParent {
            symbol: target,
            expected,
            actual,
        }
        .into());
    }
    Ok(())
}

fn name_resolution_error(
    node: NodeRef,
    error: CanonicalNameResolutionError,
) -> SourceFunctionPlanError {
    match error {
        error @ (CanonicalNameResolutionError::JavaScriptDeferred(_)
        | CanonicalNameResolutionError::CommonJsDeferred(_)
        | CanonicalNameResolutionError::JsDocDeferred(_)) => {
            SourceFunctionPlanError::Unsupported(SourceFunctionUnsupported::ResolverDeferred {
                node,
                error,
            })
        }
        error => SourceFunctionPlanError::Invariant(SourceFunctionInvariant::NameResolution(error)),
    }
}
