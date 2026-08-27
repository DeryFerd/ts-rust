//! Read-only binder and resolver proof for source function declarations.
//!
//! Callable construction belongs to `source_callables`; source checking owns
//! statement order and body execution. This module only proves the exact
//! top-level or nested function value symbol (including direct-export routing)
//! and the hoisted identifier route used by source expressions.

use std::collections::HashSet;

use ts_ast::NodeRef;
use ts_binder::{
    BoundFile, CanonicalNameResolutionError, CanonicalNameResolver, CanonicalResolutionLocation,
    CheckFlags, SemanticSymbolId, SymbolFlags,
};

use super::{
    CanonicalTypeMapperStore, DeclaredTypeError, DeclaredTypeHost, TypeId,
    source_callables::{named_default_function_export_is_exact, valid_source_function_owner_shape},
    store::SourceNodeParent,
};

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
    MissingEnclosingLocals(NodeRef),
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
    InvalidDeclarationContainer {
        declaration: NodeRef,
        expected: NodeRef,
        actual: Option<NodeRef>,
    },
    EnclosingLocalSymbolMismatch {
        declaration: NodeRef,
        enclosing_function: NodeRef,
        expected: SemanticSymbolId,
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
    validate_function_target(bound, store, declaration, name, name_text, merged)?;

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

/// Proves one named function declared directly in an enclosing function body.
pub(super) fn plan_nested_function(
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    declaration: NodeRef,
    name: NodeRef,
    name_text: &str,
    enclosing_function: NodeRef,
) -> Result<PlannedTopLevelFunction, SourceFunctionPlanError> {
    let actual_container = bound.container(declaration);
    if actual_container != Some(enclosing_function) {
        return Err(SourceFunctionInvariant::InvalidDeclarationContainer {
            declaration,
            expected: enclosing_function,
            actual: actual_container,
        }
        .into());
    }

    let function = plan_top_level_function(bound, store, declaration, name, name_text, false)?;
    let locals =
        bound
            .locals(enclosing_function)
            .ok_or(SourceFunctionInvariant::MissingEnclosingLocals(
                enclosing_function,
            ))?;
    let actual = store
        .symbol_table(locals)
        .and_then(|table| table.get_source(name_text));
    if actual != Some(function.owner_symbol) {
        return Err(SourceFunctionInvariant::EnclosingLocalSymbolMismatch {
            declaration,
            enclosing_function,
            expected: function.owner_symbol,
            actual,
        }
        .into());
    }

    Ok(function)
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
    let merged_declaration = (record.flags() != SymbolFlags::FUNCTION)
        .then(|| record.value_declaration())
        .flatten()
        .filter(|declaration| {
            valid_source_function_declaration_owner_shape(store, routed.target, *declaration)
        });
    if record.flags() != SymbolFlags::FUNCTION && merged_declaration.is_none() {
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
    if !hoisted_functions.contains(&routed.target) {
        let declaration = declarations.first().copied().unwrap_or(node);
        return Err(SourceFunctionPlanError::Unsupported(
            SourceFunctionUnsupported::IdentifierNotHoisted {
                node,
                symbol: routed.target,
                declaration,
            },
        ));
    }
    let unique_declaration = match declarations {
        [declaration] => Some(*declaration),
        _ => merged_declaration,
    };
    if let Some(declaration) = unique_declaration {
        if declaration.file != node.file || declaration.arena != node.arena {
            return Err(SourceFunctionPlanError::Unsupported(
                SourceFunctionUnsupported::CrossFileDeclaration { node, declaration },
            ));
        }
        validate_function_target(bound, store, declaration, node, name, routed.target)?;
        validate_function_read_declaration_symbol(bound, store, declaration, routed.target)?;
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
    } else if declarations.len() >= 2 && routed.export_local.is_none() {
        validate_function_overload_read_target(store, node, name, routed.target, declarations)?;
        for declaration in declarations {
            if declaration.file != node.file || declaration.arena != node.arena {
                return Err(SourceFunctionPlanError::Unsupported(
                    SourceFunctionUnsupported::CrossFileDeclaration {
                        node,
                        declaration: *declaration,
                    },
                ));
            }
            validate_function_read_declaration_symbol(bound, store, *declaration, routed.target)?;
            if bound.local_symbol(*declaration).is_some() {
                return Err(SourceFunctionInvariant::LocalExportSymbolMismatch {
                    declaration: *declaration,
                    expected: None,
                    actual: bound.local_symbol(*declaration),
                }
                .into());
            }
        }
        validate_target_parent(bound, store, routed.target, false)?;
    } else {
        return Err(SourceFunctionPlanError::Unsupported(
            SourceFunctionUnsupported::NonUniqueDeclaration {
                node,
                symbol: routed.target,
                declaration_count: declarations.len(),
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

fn validate_function_read_declaration_symbol(
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    declaration: NodeRef,
    expected: SemanticSymbolId,
) -> Result<(), SourceFunctionPlanError> {
    let declaration_symbol =
        bound
            .symbol(declaration)
            .ok_or(SourceFunctionInvariant::MissingDeclarationSymbol(
                declaration,
            ))?;
    let declaration_symbol = store.get_merged_symbol(declaration_symbol).ok_or(
        SourceFunctionInvariant::InvalidMergedSymbol(declaration_symbol),
    )?;
    if declaration_symbol != expected {
        return Err(SourceFunctionInvariant::DeclarationSymbolMismatch {
            declaration,
            expected,
            actual: declaration_symbol,
        }
        .into());
    }
    Ok(())
}

fn validate_function_overload_read_target(
    store: &CanonicalTypeMapperStore,
    node: NodeRef,
    name: &str,
    symbol: SemanticSymbolId,
    declarations: &[NodeRef],
) -> Result<(), SourceFunctionPlanError> {
    let record = store
        .symbol(symbol)
        .ok_or(SourceFunctionInvariant::InvalidSymbol(symbol))?;
    if record.flags() != SymbolFlags::FUNCTION
        || record.check_flags() != CheckFlags::NONE
        || record.name().as_bytes() != name.as_bytes()
        || record.declarations() != Some(declarations)
        || record.value_declaration() != declarations.first().copied()
        || record.members().is_some()
        || record.exports().is_some()
        || record.parent().is_some()
        || record.export_symbol().is_some()
        || declarations.len() < 2
        || declarations.iter().any(|declaration| {
            !declaration.is_for(node.arena, node.file)
                || store.source_node_kind(*declaration)
                    != Some(ts_ast::SyntaxKind::FunctionDeclaration)
        })
    {
        return Err(SourceFunctionPlanError::Unsupported(
            SourceFunctionUnsupported::NonUniqueDeclaration {
                node,
                symbol,
                declaration_count: declarations.len(),
            },
        ));
    }
    Ok(())
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
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    declaration: NodeRef,
    name: NodeRef,
    name_text: &str,
    symbol: SemanticSymbolId,
) -> Result<(), SourceFunctionPlanError> {
    let record = store
        .symbol(symbol)
        .ok_or(SourceFunctionInvariant::InvalidSymbol(symbol))?;
    let valid_owner = valid_source_function_declaration_owner_shape(store, symbol, declaration)
        || valid_source_javascript_duplicate_function_owner_shape(
            bound,
            store,
            symbol,
            declaration,
            name_text,
        );
    if record.flags() != SymbolFlags::FUNCTION && !valid_owner {
        return Err(SourceFunctionPlanError::Unsupported(
            SourceFunctionUnsupported::NonFunctionSymbol {
                node: declaration,
                symbol,
                flags: record.flags(),
            },
        ));
    }
    if record.exports().is_some() && !valid_owner {
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
    if let [actual] = declarations {
        if *actual != declaration {
            return Err(SourceFunctionInvariant::InvalidSymbolShape(symbol).into());
        }
    } else if !valid_owner {
        return Err(SourceFunctionPlanError::Unsupported(
            SourceFunctionUnsupported::NonUniqueDeclaration {
                node: declaration,
                symbol,
                declaration_count: declarations.len(),
            },
        ));
    }
    if record.value_declaration() != Some(declaration) {
        return Err(SourceFunctionInvariant::ValueDeclarationMismatch {
            symbol,
            declaration,
            value_declaration: record.value_declaration(),
        }
        .into());
    }
    let name_matches = if store.source_default_function_name(declaration).is_some() {
        bound.local_symbol(declaration).is_some_and(|local| {
            named_default_function_export_is_exact(store, declaration, symbol, local)
                && store
                    .symbol(local)
                    .is_some_and(|local| local.name().as_bytes() == name_text.as_bytes())
        })
    } else {
        record.name().as_bytes() == name_text.as_bytes()
    };
    if !name_matches {
        return Err(SourceFunctionInvariant::IdentifierNameMismatch {
            node: name,
            declaration,
        }
        .into());
    }
    Ok(())
}

/// Authenticates the first implementation of a JavaScript function group.
pub(super) fn valid_source_javascript_duplicate_function_owner_shape(
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    owner_symbol: SemanticSymbolId,
    declaration: NodeRef,
    name: &str,
) -> bool {
    if bound
        .source_facts()
        .is_none_or(|facts| !facts.is_javascript_file() || facts.is_declaration_file())
    {
        return false;
    }
    let Some(owner) = store.symbol(owner_symbol) else {
        return false;
    };
    let source = bound.source_file();
    if owner.flags() != SymbolFlags::FUNCTION
        || owner.check_flags() != CheckFlags::NONE
        || owner.name().as_bytes() != name.as_bytes()
        || owner.value_declaration() != Some(declaration)
        || owner.members().is_some()
        || owner.exports().is_some()
        || owner.parent().is_some()
        || owner.export_symbol().is_some()
        || store.get_merged_symbol(owner_symbol) != Some(owner_symbol)
        || bound
            .locals(source)
            .and_then(|locals| store.symbol_table(locals))
            .and_then(|locals| locals.get_source(name))
            != Some(owner_symbol)
    {
        return false;
    }
    let Some(declarations) = owner.declarations() else {
        return false;
    };
    declarations.len() >= 2
        && declarations.first().copied() == Some(declaration)
        && declarations
            .iter()
            .enumerate()
            .all(|(index, implementation)| {
                if declarations[..index].contains(implementation)
                    || !implementation.is_for(source.arena, source.file)
                    || store.source_node_kind(*implementation)
                        != Some(ts_ast::SyntaxKind::FunctionDeclaration)
                    || store.source_node_parent(*implementation)
                        != Some(SourceNodeParent::Parent(source))
                    || bound.container(*implementation) != Some(source)
                    || bound.symbol(*implementation) != Some(owner_symbol)
                    || bound.local_symbol(*implementation).is_some()
                {
                    return false;
                }
                let mut bodies = bound.traversal_order().filter(|candidate| {
                    store.source_node_kind(*candidate) == Some(ts_ast::SyntaxKind::Block)
                        && store.source_node_parent(*candidate)
                            == Some(SourceNodeParent::Parent(*implementation))
                        && bound.container(*candidate) == Some(*implementation)
                });
                bodies.next().is_some() && bodies.next().is_none()
            })
}

fn valid_source_function_declaration_owner_shape(
    store: &CanonicalTypeMapperStore,
    owner_symbol: SemanticSymbolId,
    declaration: NodeRef,
) -> bool {
    valid_source_function_owner_shape(store, owner_symbol, declaration)
        || valid_source_function_value_namespace_owner_shape(store, owner_symbol, declaration)
}

fn valid_source_function_value_namespace_owner_shape(
    store: &CanonicalTypeMapperStore,
    owner_symbol: SemanticSymbolId,
    declaration: NodeRef,
) -> bool {
    let Some(owner) = store.symbol(owner_symbol) else {
        return false;
    };
    if owner.flags() != (SymbolFlags::FUNCTION | SymbolFlags::VALUE_MODULE)
        || owner.check_flags() != CheckFlags::NONE
        || owner.value_declaration() != Some(declaration)
        || owner.members().is_some()
        || owner.export_symbol().is_some()
        || store.get_merged_symbol(owner_symbol) != Some(owner_symbol)
    {
        return false;
    }

    let Some(declarations) = owner.declarations() else {
        return false;
    };
    if declarations.len() < 2
        || declarations
            .iter()
            .filter(|candidate| **candidate == declaration)
            .count()
            != 1
        || declarations.iter().any(|candidate| {
            *candidate != declaration
                && (!candidate.is_for(declaration.arena, declaration.file)
                    || store.source_node_kind(*candidate)
                        != Some(ts_ast::SyntaxKind::ModuleDeclaration)
                    || store.source_node_parent(*candidate)
                        != store.source_node_parent(declaration))
        })
    {
        return false;
    }

    let Some(exports) = owner
        .exports()
        .and_then(|exports| store.symbol_table(exports))
    else {
        return false;
    };
    let mut has_value_export = false;
    for (name, member) in exports.iter() {
        let Some(record) = store.symbol(member) else {
            return false;
        };
        if record.name() != name
            || !record.flags().intersects(
                SymbolFlags::TYPE
                    | SymbolFlags::VALUE
                    | SymbolFlags::NAMESPACE
                    | SymbolFlags::ALIAS,
            )
            || store.get_merged_symbol(member) != Some(member)
            || store.get_parent_of_symbol(member) != Some(owner_symbol)
            || record.declarations().is_none_or(|member_declarations| {
                member_declarations.is_empty()
                    || member_declarations.iter().any(|member_declaration| {
                        !member_declaration.is_for(declaration.arena, declaration.file)
                            || !function_namespace_contains_declaration(
                                store,
                                declarations,
                                *member_declaration,
                            )
                    })
            })
        {
            return false;
        }
        has_value_export |= record.flags().intersects(SymbolFlags::VALUE);
    }

    has_value_export
}

fn function_namespace_contains_declaration(
    store: &CanonicalTypeMapperStore,
    owner_declarations: &[NodeRef],
    mut declaration: NodeRef,
) -> bool {
    while let Some(SourceNodeParent::Parent(parent)) = store.source_node_parent(declaration) {
        if owner_declarations.contains(&parent)
            && store.source_node_kind(parent) == Some(ts_ast::SyntaxKind::ModuleDeclaration)
        {
            return true;
        }
        declaration = parent;
    }
    false
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

#[cfg(test)]
mod tests {
    use ts_ast::{FileId, NodeData};
    use ts_binder::{
        CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
        EscapedName,
    };
    use ts_parser::{parse_javascript_source_file, parse_source_file};

    use super::*;

    fn value_namespace_function_fixture(
        source: &str,
        file: FileId,
        declaration_file: bool,
    ) -> (
        ts_parser::ParseResult,
        BoundFile,
        CanonicalTypeMapperStore,
        NodeRef,
        NodeRef,
    ) {
        let parsed = parse_source_file(source);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source(format!("\"/project/function-{}.ts\"", file.index())),
                    CanonicalSourceLanguage::TypeScript,
                    declaration_file,
                    CanonicalModuleState::External,
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
        let (declaration, name) = parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                let NodeData::FunctionDeclaration(function) = &record.data else {
                    return None;
                };
                Some((
                    NodeRef::new(parsed.arena.id(), file, node),
                    NodeRef::new(parsed.arena.id(), file, function.name?),
                ))
            })
            .unwrap();

        (parsed, bound, store, declaration, name)
    }

    fn javascript_duplicate_function_fixture(
        file: FileId,
    ) -> (
        ts_parser::ParseResult,
        BoundFile,
        CanonicalTypeMapperStore,
        Vec<(NodeRef, NodeRef)>,
    ) {
        let parsed =
            parse_javascript_source_file("function repeated() {} function repeated(value) {}");
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source(format!("\"/project/repeated-{}.js\"", file.index())),
                    CanonicalSourceLanguage::JavaScript,
                    false,
                    CanonicalModuleState::Script,
                ),
            )
            .unwrap();
        binder
            .bind_javascript_declaration_slice(&parsed.arena, file)
            .unwrap();
        let (symbols, mut files) = binder.finish().try_into_parts().unwrap();
        let bound = files.remove(&file).unwrap();
        let mut store = CanonicalTypeMapperStore::from_symbol_store(symbols);
        assert!(
            store
                .register_source_file(&parsed.arena, parsed.source_file, file)
                .is_some()
        );
        let source = parsed.arena.get(parsed.source_file).unwrap();
        let NodeData::SourceFile(source) = &source.data else {
            panic!("the JavaScript fixture must retain its source-file root")
        };
        let declarations = source
            .statements
            .nodes
            .iter()
            .filter_map(|node| {
                let record = parsed.arena.get(*node)?;
                let NodeData::FunctionDeclaration(function) = &record.data else {
                    return None;
                };
                Some((
                    NodeRef::new(parsed.arena.id(), file, *node),
                    NodeRef::new(parsed.arena.id(), file, function.name?),
                ))
            })
            .collect();

        (parsed, bound, store, declarations)
    }

    #[test]
    fn javascript_duplicate_functions_keep_the_first_implementation_on_replay() {
        let (_, bound, store, declarations) =
            javascript_duplicate_function_fixture(FileId::new(8_930));
        let [(first, first_name), (second, second_name)] = declarations.as_slice() else {
            panic!("the JavaScript fixture must retain both implementations")
        };
        let owner = bound.symbol(*first).unwrap();
        assert_eq!(bound.symbol(*second), Some(owner));
        assert_eq!(
            store.symbol(owner).unwrap().value_declaration(),
            Some(*first)
        );
        let before = (
            store.type_len(),
            store.symbol_len(),
            store.symbol_store().symbol_table_len(),
            store.checker_link_allocated_lengths(),
        );

        for _ in 0..2 {
            assert!(valid_source_javascript_duplicate_function_owner_shape(
                &bound, &store, owner, *first, "repeated",
            ));
            assert_eq!(
                plan_top_level_function(&bound, &store, *first, *first_name, "repeated", false),
                Ok(PlannedTopLevelFunction {
                    declaration: *first,
                    owner_symbol: owner,
                }),
            );
            assert_eq!(
                (
                    store.type_len(),
                    store.symbol_len(),
                    store.symbol_store().symbol_table_len(),
                    store.checker_link_allocated_lengths(),
                ),
                before,
            );
        }
        assert!(!valid_source_javascript_duplicate_function_owner_shape(
            &bound, &store, owner, *second, "repeated",
        ));
        assert_eq!(
            plan_top_level_function(&bound, &store, *second, *second_name, "repeated", false),
            Err(SourceFunctionPlanError::Unsupported(
                SourceFunctionUnsupported::NonUniqueDeclaration {
                    node: *second,
                    symbol: owner,
                    declaration_count: 2,
                },
            )),
        );
    }

    #[test]
    fn javascript_duplicate_functions_reject_forged_declaration_order_and_relationships() {
        let (_, bound, mut store, declarations) =
            javascript_duplicate_function_fixture(FileId::new(8_931));
        let [(first, first_name), (second, _)] = declarations.as_slice() else {
            panic!("the JavaScript fixture must retain both implementations")
        };
        let owner = bound.symbol(*first).unwrap();
        assert!(store.set_symbol_declarations(owner, Some(vec![*second, *first]), Some(*first)));
        assert!(!valid_source_javascript_duplicate_function_owner_shape(
            &bound, &store, owner, *first, "repeated",
        ));
        assert_eq!(
            plan_top_level_function(&bound, &store, *first, *first_name, "repeated", false),
            Err(SourceFunctionPlanError::Unsupported(
                SourceFunctionUnsupported::NonUniqueDeclaration {
                    node: *first,
                    symbol: owner,
                    declaration_count: 2,
                },
            )),
        );

        assert!(store.set_symbol_declarations(owner, Some(vec![*first, *second]), Some(*first)));
        let record = store.symbol(owner).unwrap();
        let (members, parent, export_symbol) =
            (record.members(), record.parent(), record.export_symbol());
        let exports = store.alloc_symbol_table();
        assert!(store.set_symbol_relationships(
            owner,
            members,
            Some(exports),
            parent,
            export_symbol
        ));
        assert!(!valid_source_javascript_duplicate_function_owner_shape(
            &bound, &store, owner, *first, "repeated",
        ));
        assert_eq!(
            plan_top_level_function(&bound, &store, *first, *first_name, "repeated", false),
            Err(SourceFunctionPlanError::Unsupported(
                SourceFunctionUnsupported::ExpandoFunction {
                    node: *first,
                    symbol: owner,
                },
            )),
        );
    }

    #[test]
    fn value_namespace_function_owners_preserve_declaration_identity_on_replay() {
        for (index, (source, declaration_file)) in [
            (
                "declare function callable(): void; \
                 declare namespace callable { export const value: string; } \
                 export = callable;",
                true,
            ),
            (
                "function callable() {} \
                 namespace callable { export var value = 1; } \
                 export = callable;",
                false,
            ),
        ]
        .into_iter()
        .enumerate()
        {
            let (_, bound, store, declaration, name) = value_namespace_function_fixture(
                source,
                FileId::new(8_927 + u32::try_from(index).unwrap()),
                declaration_file,
            );
            let owner = bound.symbol(declaration).unwrap();
            assert_eq!(
                store.symbol(owner).unwrap().flags(),
                SymbolFlags::FUNCTION | SymbolFlags::VALUE_MODULE,
            );
            let before = (
                store.type_len(),
                store.symbol_len(),
                store.symbol_store().symbol_table_len(),
                store.checker_link_allocated_lengths(),
            );

            for _ in 0..2 {
                assert_eq!(
                    plan_top_level_function(&bound, &store, declaration, name, "callable", false),
                    Ok(PlannedTopLevelFunction {
                        declaration,
                        owner_symbol: owner,
                    }),
                );
                assert_eq!(
                    (
                        store.type_len(),
                        store.symbol_len(),
                        store.symbol_store().symbol_table_len(),
                        store.checker_link_allocated_lengths(),
                    ),
                    before,
                );
            }
        }
    }

    #[test]
    fn value_namespace_function_owners_reject_unowned_exports() {
        let (_, bound, mut store, declaration, name) = value_namespace_function_fixture(
            "declare function callable(): void; \
             declare namespace callable { export const value: string; } \
             export = callable;",
            FileId::new(8_929),
            true,
        );
        let owner = bound.symbol(declaration).unwrap();
        let member = store
            .symbol(owner)
            .and_then(ts_binder::semantic::Symbol::exports)
            .and_then(|exports| store.symbol_table(exports))
            .and_then(|exports| exports.get_source("value"))
            .unwrap();
        let record = store.symbol(member).unwrap();
        let (members, exports, export_symbol) =
            (record.members(), record.exports(), record.export_symbol());
        assert!(store.set_symbol_relationships(member, members, exports, None, export_symbol));

        assert_eq!(
            plan_top_level_function(&bound, &store, declaration, name, "callable", false),
            Err(SourceFunctionPlanError::Unsupported(
                SourceFunctionUnsupported::NonFunctionSymbol {
                    node: declaration,
                    symbol: owner,
                    flags: SymbolFlags::FUNCTION | SymbolFlags::VALUE_MODULE,
                },
            )),
        );
    }

    #[test]
    fn nested_function_uses_enclosing_locals_and_preserves_variable_shadowing() {
        let parsed = parse_source_file(concat!(
            "function outer() { const x = 0; ",
            "function inner() { var x = 'inner'; } }",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(8_926);
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source("\"/project/nested-functions.ts\""),
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

        let function = |expected_name: &str| {
            parsed
                .arena
                .iter()
                .find_map(|(node, record)| {
                    let NodeData::FunctionDeclaration(function) = &record.data else {
                        return None;
                    };
                    let name = function.name?;
                    let NodeData::Identifier(identifier) = &parsed.arena.get(name)?.data else {
                        return None;
                    };
                    (identifier.text == expected_name).then_some((
                        NodeRef::new(parsed.arena.id(), file, node),
                        NodeRef::new(parsed.arena.id(), file, name),
                    ))
                })
                .unwrap()
        };
        let (outer, _) = function("outer");
        let (inner, name) = function("inner");

        let planned = plan_nested_function(&bound, &store, inner, name, "inner", outer).unwrap();
        assert_eq!(planned.owner_symbol, bound.symbol(inner).unwrap());
        assert_eq!(
            plan_nested_function(&bound, &store, inner, name, "inner", outer),
            Ok(planned)
        );

        let shadowed_variables: Vec<_> = parsed
            .arena
            .iter()
            .filter_map(|(node, record)| {
                let NodeData::VariableDeclaration(_) = &record.data else {
                    return None;
                };
                bound.symbol(NodeRef::new(parsed.arena.id(), file, node))
            })
            .collect();
        assert_eq!(shadowed_variables.len(), 2);
        assert_ne!(shadowed_variables[0], shadowed_variables[1]);

        assert_eq!(
            plan_nested_function(&bound, &store, inner, name, "inner", bound.source_file(),),
            Err(SourceFunctionPlanError::Invariant(
                SourceFunctionInvariant::InvalidDeclarationContainer {
                    declaration: inner,
                    expected: bound.source_file(),
                    actual: Some(outer),
                },
            ))
        );
    }
}
