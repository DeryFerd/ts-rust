//! Exact symbol-merge substrate used by pinned checker initialization.
//!
//! This ports the graph operations from `checker.go` without owning Program
//! orchestration, alias resolution, or diagnostic emission. Unsupported
//! branches fail with typed errors instead of guessing a merge result.

use std::collections::HashSet;

use ts_ast::{NodeRef, SyntaxKind};
use ts_binder::{
    CheckFlags, SemanticSymbolId, SymbolFlags, SymbolTableId, should_replace_value_declaration,
};

use super::store::{MergedSymbolRecordError, SemanticStore};

/// Checker behavior required by an incompatible merge but not yet owned by
/// the canonical construction prefix.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum SymbolMergeDiagnosticKind {
    IncompatibleDeclarations,
    CannotAugmentNonModule,
}

/// A symbol graph that cannot be merged exactly by the installed substrate.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum SymbolMergeError {
    InvalidSymbol(SemanticSymbolId),
    InvalidTable(SymbolTableId),
    InvalidMergedParent(SemanticSymbolId),
    AliasResolutionRequired(SemanticSymbolId),
    DiagnosticRequired {
        kind: SymbolMergeDiagnosticKind,
        target: SemanticSymbolId,
        source: SemanticSymbolId,
    },
    MissingValueDeclarationKind(NodeRef),
    RecursiveMerge {
        target: SemanticSymbolId,
        source: SemanticSymbolId,
    },
    RedirectInvariant {
        target: SemanticSymbolId,
        source: SemanticSymbolId,
    },
    StoreInvariant(&'static str),
}

impl std::fmt::Display for SymbolMergeError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::InvalidSymbol(symbol) => {
                write!(
                    formatter,
                    "symbol {symbol:?} is not owned by the checker store"
                )
            }
            Self::InvalidTable(table) => {
                write!(
                    formatter,
                    "symbol table {table:?} is not owned by the checker store"
                )
            }
            Self::InvalidMergedParent(parent) => write!(
                formatter,
                "merged export parent {parent:?} is not owned by the checker store"
            ),
            Self::AliasResolutionRequired(symbol) => write!(
                formatter,
                "non-local alias {symbol:?} requires the unported alias resolver"
            ),
            Self::DiagnosticRequired {
                kind,
                target,
                source,
            } => write!(
                formatter,
                "merge of {source:?} into {target:?} requires checker diagnostic {kind:?}"
            ),
            Self::MissingValueDeclarationKind(node) => write!(
                formatter,
                "value declaration {node:?} has no checker-registered source kind"
            ),
            Self::RecursiveMerge { target, source } => write!(
                formatter,
                "recursive merge of {source:?} into {target:?} is unsupported"
            ),
            Self::RedirectInvariant { target, source } => write!(
                formatter,
                "merge redirect from {source:?} to {target:?} violates store invariants"
            ),
            Self::StoreInvariant(message) => formatter.write_str(message),
        }
    }
}

impl std::error::Error for SymbolMergeError {}

/// Computes the exact dynamic exclusion mask from pinned `checker.go`.
#[must_use]
pub fn get_excluded_symbol_flags(flags: SymbolFlags) -> SymbolFlags {
    let mut result = SymbolFlags::NONE;
    for (flag, excludes) in [
        (
            SymbolFlags::BLOCK_SCOPED_VARIABLE,
            SymbolFlags::BLOCK_SCOPED_VARIABLE_EXCLUDES,
        ),
        (
            SymbolFlags::FUNCTION_SCOPED_VARIABLE,
            SymbolFlags::FUNCTION_SCOPED_VARIABLE_EXCLUDES,
        ),
        (SymbolFlags::PROPERTY, SymbolFlags::PROPERTY_EXCLUDES),
        (SymbolFlags::ENUM_MEMBER, SymbolFlags::ENUM_MEMBER_EXCLUDES),
        (SymbolFlags::FUNCTION, SymbolFlags::FUNCTION_EXCLUDES),
        (SymbolFlags::CLASS, SymbolFlags::CLASS_EXCLUDES),
        (SymbolFlags::INTERFACE, SymbolFlags::INTERFACE_EXCLUDES),
        (
            SymbolFlags::REGULAR_ENUM,
            SymbolFlags::REGULAR_ENUM_EXCLUDES,
        ),
        (SymbolFlags::CONST_ENUM, SymbolFlags::CONST_ENUM_EXCLUDES),
        (
            SymbolFlags::VALUE_MODULE,
            SymbolFlags::VALUE_MODULE_EXCLUDES,
        ),
        (SymbolFlags::METHOD, SymbolFlags::METHOD_EXCLUDES),
        (
            SymbolFlags::GET_ACCESSOR,
            SymbolFlags::GET_ACCESSOR_EXCLUDES,
        ),
        (
            SymbolFlags::SET_ACCESSOR,
            SymbolFlags::SET_ACCESSOR_EXCLUDES,
        ),
        (
            SymbolFlags::TYPE_PARAMETER,
            SymbolFlags::TYPE_PARAMETER_EXCLUDES,
        ),
        (SymbolFlags::TYPE_ALIAS, SymbolFlags::TYPE_ALIAS_EXCLUDES),
        (SymbolFlags::ALIAS, SymbolFlags::ALIAS_EXCLUDES),
    ] {
        if flags.intersects(flag) {
            result |= excludes;
        }
    }
    if flags.intersects(SymbolFlags::REPLACEABLE_BY_METHOD) {
        result = result.without(SymbolFlags::METHOD);
    }
    result
}

#[allow(dead_code)] // Wired by the production-construction slice that consumes this substrate.
impl<TypePayload, MapperPayload> SemanticStore<TypePayload, MapperPayload> {
    /// Makes the exact shallow transient clone used before mutating a bound
    /// target symbol.
    pub(super) fn clone_symbol(
        &mut self,
        symbol: SemanticSymbolId,
    ) -> Result<SemanticSymbolId, SymbolMergeError> {
        MergeSession::new(self).clone_symbol(symbol)
    }

    /// Merges one source symbol into one target symbol.
    pub(super) fn merge_symbol(
        &mut self,
        target: SemanticSymbolId,
        source: SemanticSymbolId,
        unidirectional: bool,
    ) -> Result<SemanticSymbolId, SymbolMergeError> {
        MergeSession::new(self).merge_symbol(target, source, unidirectional)
    }

    /// Merges a complete source table into a target table in escaped-byte
    /// order, preserving pinned collision and export-parent semantics.
    pub(super) fn merge_symbol_table(
        &mut self,
        target: SymbolTableId,
        source: SymbolTableId,
        unidirectional: bool,
        merged_parent: Option<SemanticSymbolId>,
    ) -> Result<(), SymbolMergeError> {
        MergeSession::new(self).merge_symbol_table(target, source, unidirectional, merged_parent)
    }

    /// Merges one symbol into the checker globals table by its exact escaped
    /// name and returns the table's resulting symbol.
    pub(super) fn merge_global_symbol(
        &mut self,
        globals: SymbolTableId,
        symbol: SemanticSymbolId,
    ) -> Result<SemanticSymbolId, SymbolMergeError> {
        MergeSession::new(self).merge_global_symbol(globals, symbol)
    }
}

#[allow(dead_code)] // Constructed through the sibling-visible entry points above.
struct MergeSession<'store, TypePayload, MapperPayload> {
    store: &'store mut SemanticStore<TypePayload, MapperPayload>,
    active: HashSet<(SemanticSymbolId, SemanticSymbolId)>,
}

#[allow(dead_code)] // Constructed through the sibling-visible entry points above.
impl<'store, TypePayload, MapperPayload> MergeSession<'store, TypePayload, MapperPayload> {
    fn new(store: &'store mut SemanticStore<TypePayload, MapperPayload>) -> Self {
        Self {
            store,
            active: HashSet::new(),
        }
    }

    fn merge_global_symbol(
        &mut self,
        globals: SymbolTableId,
        symbol: SemanticSymbolId,
    ) -> Result<SemanticSymbolId, SymbolMergeError> {
        let name = self.symbol(symbol)?.name().to_owned();
        let target = self.table(globals)?.get(name.as_ref());
        let merged = if let Some(target) = target {
            self.merge_symbol(target, symbol, false)?
        } else {
            self.store
                .get_merged_symbol(symbol)
                .ok_or(SymbolMergeError::InvalidSymbol(symbol))?
        };
        self.store
            .insert_symbol(globals, name, merged)
            .ok_or(SymbolMergeError::InvalidTable(globals))?;
        Ok(merged)
    }

    fn merge_symbol_table(
        &mut self,
        target: SymbolTableId,
        source: SymbolTableId,
        unidirectional: bool,
        merged_parent: Option<SemanticSymbolId>,
    ) -> Result<(), SymbolMergeError> {
        self.table(target)?;
        let mut source_entries = self
            .table(source)?
            .iter()
            .map(|(name, symbol)| (name.to_owned(), symbol))
            .collect::<Vec<_>>();
        source_entries.sort_by(|(left, _), (right, _)| left.as_bytes().cmp(right.as_bytes()));
        if let Some(parent) = merged_parent
            && self.store.symbol(parent).is_none()
        {
            return Err(SymbolMergeError::InvalidMergedParent(parent));
        }

        for (name, source_symbol) in source_entries {
            let target_symbol = self.table(target)?.get(name.as_ref());
            let merged = if let Some(target_symbol) = target_symbol {
                self.merge_symbol(target_symbol, source_symbol, unidirectional)?
            } else {
                self.store
                    .get_merged_symbol(source_symbol)
                    .ok_or(SymbolMergeError::InvalidSymbol(source_symbol))?
            };
            if let (Some(parent), Some(_)) = (merged_parent, target_symbol)
                && self
                    .symbol(merged)?
                    .flags()
                    .intersects(SymbolFlags::TRANSIENT)
            {
                self.set_parent(merged, Some(parent))?;
            }
            self.store
                .insert_symbol(target, name, merged)
                .ok_or(SymbolMergeError::InvalidTable(target))?;
        }
        Ok(())
    }

    fn merge_symbol(
        &mut self,
        target: SemanticSymbolId,
        source: SemanticSymbolId,
        unidirectional: bool,
    ) -> Result<SemanticSymbolId, SymbolMergeError> {
        self.symbol(target)?;
        self.symbol(source)?;
        if !self.active.insert((target, source)) {
            return Err(SymbolMergeError::RecursiveMerge { target, source });
        }
        let result = self.merge_symbol_inner(target, source, unidirectional);
        self.active.remove(&(target, source));
        result
    }

    #[allow(clippy::too_many_lines)] // Mirrors the branch order in pinned `mergeSymbol`.
    fn merge_symbol_inner(
        &mut self,
        mut target: SemanticSymbolId,
        source: SemanticSymbolId,
        unidirectional: bool,
    ) -> Result<SemanticSymbolId, SymbolMergeError> {
        let source_flags = self.symbol(source)?.flags();
        let target_flags = self.symbol(target)?.flags();
        if compatible(target_flags, source_flags) {
            if source == target {
                return Ok(target);
            }
            if !target_flags.intersects(SymbolFlags::TRANSIENT) {
                let resolved_target = self.resolve_symbol_for_merge(target)?;
                if self
                    .store
                    .intrinsic_bootstrap
                    .as_ref()
                    .is_some_and(|bootstrap| bootstrap.unknown_symbol == resolved_target)
                {
                    return Ok(source);
                }
                let resolved_flags = self.symbol(resolved_target)?.flags();
                if compatible(resolved_flags, source_flags) {
                    target = self.clone_symbol(resolved_target)?;
                } else {
                    return Err(SymbolMergeError::DiagnosticRequired {
                        kind: SymbolMergeDiagnosticKind::IncompatibleDeclarations,
                        target,
                        source,
                    });
                }
            }

            let target_snapshot = self.symbol(target)?.clone();
            let source_snapshot = self.symbol(source)?.clone();
            let mut flags = target_snapshot.flags();
            if source_flags.intersects(SymbolFlags::VALUE_MODULE)
                && flags.intersects(SymbolFlags::VALUE_MODULE)
                && flags.intersects(SymbolFlags::CONST_ENUM_ONLY_MODULE)
                && !source_flags.intersects(SymbolFlags::CONST_ENUM_ONLY_MODULE)
            {
                flags = flags.without(SymbolFlags::CONST_ENUM_ONLY_MODULE);
            }
            flags |= source_flags;

            let value_declaration = self.merged_value_declaration(
                target_snapshot.value_declaration(),
                source_snapshot.value_declaration(),
            )?;
            let declarations = append_declarations(
                target_snapshot.declarations(),
                source_snapshot.declarations(),
            );
            if !self
                .store
                .set_symbol_flags(target, flags, target_snapshot.check_flags())
            {
                return Err(SymbolMergeError::StoreInvariant(
                    "merged target flags failed canonical validation",
                ));
            }
            if !self
                .store
                .set_symbol_declarations(target, declarations, value_declaration)
            {
                return Err(SymbolMergeError::StoreInvariant(
                    "merged target declarations failed canonical validation",
                ));
            }

            if let Some(source_members) = source_snapshot.members() {
                let target_members = self.ensure_relationship_table(target, false)?;
                self.merge_symbol_table(target_members, source_members, unidirectional, None)?;
            }
            if let Some(source_exports) = source_snapshot.exports() {
                let target_exports = self.ensure_relationship_table(target, true)?;
                self.merge_symbol_table(
                    target_exports,
                    source_exports,
                    unidirectional,
                    Some(target),
                )?;
            }
            if !unidirectional {
                self.record_merged_symbol(target, source)?;
            }
        } else if target_flags.intersects(SymbolFlags::NAMESPACE_MODULE) {
            let is_global_this = self
                .store
                .intrinsic_bootstrap
                .as_ref()
                .is_some_and(|bootstrap| bootstrap.global_this_symbol == target);
            if !is_global_this {
                return Err(SymbolMergeError::DiagnosticRequired {
                    kind: SymbolMergeDiagnosticKind::CannotAugmentNonModule,
                    target,
                    source,
                });
            }
        } else {
            return Err(SymbolMergeError::DiagnosticRequired {
                kind: SymbolMergeDiagnosticKind::IncompatibleDeclarations,
                target,
                source,
            });
        }
        Ok(target)
    }

    fn clone_symbol(
        &mut self,
        symbol: SemanticSymbolId,
    ) -> Result<SemanticSymbolId, SymbolMergeError> {
        let snapshot = self.symbol(symbol)?.clone();
        let result = self.store.alloc_transient_symbol(
            snapshot.flags(),
            snapshot.name().to_owned(),
            CheckFlags::NONE,
        );
        let members = snapshot
            .members()
            .map(|table| {
                self.store
                    .clone_symbol_table(table)
                    .ok_or(SymbolMergeError::InvalidTable(table))
            })
            .transpose()?;
        let exports = snapshot
            .exports()
            .map(|table| {
                self.store
                    .clone_symbol_table(table)
                    .ok_or(SymbolMergeError::InvalidTable(table))
            })
            .transpose()?;
        if !self.store.set_symbol_declarations(
            result,
            snapshot.declarations().map(<[NodeRef]>::to_vec),
            snapshot.value_declaration(),
        ) || !self.store.set_symbol_relationships(
            result,
            members,
            exports,
            snapshot.parent(),
            None,
        ) {
            return Err(SymbolMergeError::StoreInvariant(
                "cloned symbol failed canonical relationship validation",
            ));
        }
        self.record_merged_symbol(result, symbol)?;
        Ok(result)
    }

    fn resolve_symbol_for_merge(
        &self,
        symbol: SemanticSymbolId,
    ) -> Result<SemanticSymbolId, SymbolMergeError> {
        let flags = self.symbol(symbol)?.flags();
        let alias_excludes = SymbolFlags::VALUE | SymbolFlags::TYPE | SymbolFlags::NAMESPACE;
        let non_local_alias = flags & (SymbolFlags::ALIAS | alias_excludes) == SymbolFlags::ALIAS
            || flags.intersects(SymbolFlags::ALIAS) && flags.intersects(SymbolFlags::ASSIGNMENT);
        if non_local_alias {
            Err(SymbolMergeError::AliasResolutionRequired(symbol))
        } else {
            Ok(symbol)
        }
    }

    fn merged_value_declaration(
        &self,
        current: Option<NodeRef>,
        incoming: Option<NodeRef>,
    ) -> Result<Option<NodeRef>, SymbolMergeError> {
        let Some(incoming) = incoming else {
            return Ok(current);
        };
        let Some(current) = current else {
            return Ok(Some(incoming));
        };
        let current_kind = self.node_kind(current)?;
        let incoming_kind = self.node_kind(incoming)?;
        Ok(Some(
            if should_replace_value_declaration(current_kind, incoming_kind) {
                incoming
            } else {
                current
            },
        ))
    }

    fn ensure_relationship_table(
        &mut self,
        symbol: SemanticSymbolId,
        exports: bool,
    ) -> Result<SymbolTableId, SymbolMergeError> {
        let snapshot = self.symbol(symbol)?.clone();
        let existing = if exports {
            snapshot.exports()
        } else {
            snapshot.members()
        };
        if let Some(existing) = existing {
            return Ok(existing);
        }
        let table = self.store.alloc_symbol_table();
        let (members, exports_table) = if exports {
            (snapshot.members(), Some(table))
        } else {
            (Some(table), snapshot.exports())
        };
        if !self.store.set_symbol_relationships(
            symbol,
            members,
            exports_table,
            snapshot.parent(),
            snapshot.export_symbol(),
        ) {
            return Err(SymbolMergeError::StoreInvariant(
                "merged target table failed canonical relationship validation",
            ));
        }
        Ok(table)
    }

    fn set_parent(
        &mut self,
        symbol: SemanticSymbolId,
        parent: Option<SemanticSymbolId>,
    ) -> Result<(), SymbolMergeError> {
        let snapshot = self.symbol(symbol)?.clone();
        if !self.store.set_symbol_relationships(
            symbol,
            snapshot.members(),
            snapshot.exports(),
            parent,
            snapshot.export_symbol(),
        ) {
            return Err(SymbolMergeError::StoreInvariant(
                "merged export parent failed canonical relationship validation",
            ));
        }
        Ok(())
    }

    fn record_merged_symbol(
        &mut self,
        target: SemanticSymbolId,
        source: SemanticSymbolId,
    ) -> Result<(), SymbolMergeError> {
        self.store
            .record_merged_symbol(target, source)
            .map(drop)
            .map_err(|error| match error {
                MergedSymbolRecordError::InvalidTarget(target) => {
                    SymbolMergeError::InvalidSymbol(target)
                }
                MergedSymbolRecordError::InvalidSource(source) => {
                    SymbolMergeError::InvalidSymbol(source)
                }
                MergedSymbolRecordError::SelfRedirect(_)
                | MergedSymbolRecordError::RedirectCycle { .. } => {
                    SymbolMergeError::RedirectInvariant { target, source }
                }
            })
    }

    fn node_kind(&self, node: NodeRef) -> Result<SyntaxKind, SymbolMergeError> {
        self.store
            .source_node_kind(node)
            .ok_or(SymbolMergeError::MissingValueDeclarationKind(node))
    }

    fn symbol(
        &self,
        symbol: SemanticSymbolId,
    ) -> Result<&ts_binder::semantic::Symbol, SymbolMergeError> {
        self.store
            .symbol(symbol)
            .ok_or(SymbolMergeError::InvalidSymbol(symbol))
    }

    fn table(
        &self,
        table: SymbolTableId,
    ) -> Result<&ts_binder::semantic::SymbolTable, SymbolMergeError> {
        self.store
            .symbol_table(table)
            .ok_or(SymbolMergeError::InvalidTable(table))
    }
}

#[allow(dead_code)] // Reached through the sibling-visible merge entry points.
fn compatible(target: SymbolFlags, source: SymbolFlags) -> bool {
    !target.intersects(get_excluded_symbol_flags(source))
        || (source | target).intersects(SymbolFlags::ASSIGNMENT)
}

#[allow(dead_code)] // Reached through the sibling-visible merge entry points.
fn append_declarations(
    target: Option<&[NodeRef]>,
    source: Option<&[NodeRef]>,
) -> Option<Vec<NodeRef>> {
    match target {
        Some(target) => {
            let mut declarations = target.to_vec();
            declarations.extend(source.unwrap_or_default());
            Some(declarations)
        }
        None => source
            .filter(|source| !source.is_empty())
            .map(<[NodeRef]>::to_vec),
    }
}

#[cfg(test)]
mod tests;
