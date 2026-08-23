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
    source_callables::valid_source_function_owner_shape,
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
            valid_source_function_owner_shape(store, routed.target, *declaration)
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
        validate_function_target(store, declaration, node, name, routed.target)?;
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
    store: &CanonicalTypeMapperStore,
    declaration: NodeRef,
    name: NodeRef,
    name_text: &str,
    symbol: SemanticSymbolId,
) -> Result<(), SourceFunctionPlanError> {
    let record = store
        .symbol(symbol)
        .ok_or(SourceFunctionInvariant::InvalidSymbol(symbol))?;
    let valid_owner = valid_source_function_owner_shape(store, symbol, declaration);
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

#[cfg(test)]
mod tests {
    use ts_ast::{FileId, NodeData};
    use ts_binder::{
        CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
        EscapedName,
    };
    use ts_parser::parse_source_file;

    use super::*;

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
