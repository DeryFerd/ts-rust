//! Exact symbol-merge substrate used by pinned checker initialization.
//!
//! This ports the graph operations from `checker.go` without owning Program
//! orchestration. Host callbacks place alias resolution and nonfatal reporting
//! inside the exact merge branches; callers that install no capabilities fail
//! with typed errors instead of guessing a merge result.

use std::collections::HashSet;

use ts_ast::{NodeRef, SyntaxKind};
use ts_binder::{
    CheckFlags, SemanticSymbolId, SymbolFlags, SymbolTableId, should_replace_value_declaration,
};
use ts_diagnostics::{Diagnostic, message_by_code};

use super::{
    diagnostics::{CanonicalCheckerDiagnostics, CanonicalCheckerRelatedInformation},
    store::{MergedSymbolRecordError, SemanticStore},
};

/// The checker report selected by one incompatible merge branch.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum SymbolMergeDiagnosticKind {
    IncompatibleDeclarations,
    CannotAugmentNonModule,
}

/// One nonfatal diagnostic requested from inside the exact merge control flow.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct SymbolMergeDiagnostic {
    pub kind: SymbolMergeDiagnosticKind,
    pub target: SemanticSymbolId,
    pub source: SemanticSymbolId,
}

/// Checker capabilities consulted by one recursive symbol-merge session.
///
/// Alias resolution receives the mutable store because the eventual exact
/// resolver owns cache and cycle-state writes. Diagnostic reporting receives
/// an immutable store snapshot and must report synchronously; returning `Ok`
/// tells the merge kernel to take the pinned nonfatal continuation in place.
/// The default methods preserve the previous fail-closed boundary.
pub trait SymbolMergeHost<TypePayload, MapperPayload> {
    /// Resolves a non-local alias reached by a compatible bound target.
    ///
    /// # Errors
    ///
    /// Returns a typed capability or semantic failure when the alias cannot be
    /// resolved exactly. The merge session stops at the callback location.
    fn resolve_alias_for_merge(
        &mut self,
        _store: &mut SemanticStore<TypePayload, MapperPayload>,
        symbol: SemanticSymbolId,
    ) -> Result<SemanticSymbolId, SymbolMergeError> {
        Err(SymbolMergeError::AliasResolutionRequired(symbol))
    }

    /// Reports one collision before the merge takes its pinned continuation.
    ///
    /// # Errors
    ///
    /// Returns a typed capability or reporting failure. `Ok(())` means the
    /// diagnostic is nonfatal and permits the in-place continuation.
    fn report_merge_diagnostic(
        &mut self,
        _store: &SemanticStore<TypePayload, MapperPayload>,
        diagnostic: SymbolMergeDiagnostic,
    ) -> Result<(), SymbolMergeError> {
        Err(SymbolMergeError::DiagnosticRequired {
            kind: diagnostic.kind,
            target: diagnostic.target,
            source: diagnostic.source,
        })
    }
}

/// Host used by the compatibility entry points until their caller owns
/// diagnostics and alias resolution.
///
/// A fail-closed error is terminal for that merge attempt. Recursive merging
/// can mutate an outer target before reaching a missing nested capability, and
/// the merge kernel does not roll those writes back. Callers must not catch the
/// error and retry the same operation after installing another host.
#[derive(Clone, Copy, Debug, Default)]
pub struct FailClosedSymbolMergeHost;

impl<TypePayload, MapperPayload> SymbolMergeHost<TypePayload, MapperPayload>
    for FailClosedSymbolMergeHost
{
}

/// Dependency-closed merge host that owns TypeScript diagnostic continuations
/// while leaving alias resolution fail-closed.
///
/// It uses retained raw declaration identities as locations and binder escaped
/// names as spelling. Plain-JavaScript suppression, declaration-name location
/// adjustment, and checker `symbolToString` spelling require the later
/// Program/AST diagnostic host and can implement [`SymbolMergeHost`] directly.
pub struct CheckerDiagnosticMergeHost<'diagnostics> {
    diagnostics: &'diagnostics mut CanonicalCheckerDiagnostics,
}

impl<'diagnostics> CheckerDiagnosticMergeHost<'diagnostics> {
    #[must_use]
    pub const fn new(diagnostics: &'diagnostics mut CanonicalCheckerDiagnostics) -> Self {
        Self { diagnostics }
    }

    fn report_incompatible<TypePayload, MapperPayload>(
        &mut self,
        store: &SemanticStore<TypePayload, MapperPayload>,
        target: SemanticSymbolId,
        source: SemanticSymbolId,
    ) -> Result<(), SymbolMergeError> {
        let target_record = store
            .symbol(target)
            .ok_or(SymbolMergeError::InvalidSymbol(target))?;
        let source_record = store
            .symbol(source)
            .ok_or(SymbolMergeError::InvalidSymbol(source))?;
        let target_declarations = target_record.declarations().unwrap_or_default().to_vec();
        let source_declarations = source_record.declarations().unwrap_or_default().to_vec();
        let symbol_name = display_symbol_name(source_record);
        let code = if (target_record.flags() | source_record.flags()).intersects(SymbolFlags::ENUM)
        {
            2567
        } else if (target_record.flags() | source_record.flags())
            .intersects(SymbolFlags::BLOCK_SCOPED_VARIABLE)
        {
            2451
        } else {
            2300
        };

        self.report_duplicate_side(
            &source_declarations,
            &target_declarations,
            code,
            &symbol_name,
        );
        self.report_duplicate_side(
            &target_declarations,
            &source_declarations,
            code,
            &symbol_name,
        );
        Ok(())
    }

    fn report_duplicate_side(
        &mut self,
        declarations: &[NodeRef],
        related_declarations: &[NodeRef],
        code: u32,
        symbol_name: &str,
    ) {
        for &node in declarations {
            let message = message_by_code(code).expect("pinned merge diagnostic is in the catalog");
            let diagnostic = if code == 2567 {
                Diagnostic::new(message)
            } else {
                Diagnostic::with_arguments(message, [symbol_name])
            };
            let diagnostic = self.diagnostics.lookup_or_issue(Some(node), diagnostic);
            for &related_node in related_declarations {
                let leading = CanonicalCheckerRelatedInformation {
                    node: Some(related_node),
                    diagnostic: Diagnostic::with_arguments(
                        message_by_code(6203)
                            .expect("pinned leading related diagnostic is in the catalog"),
                        [symbol_name],
                    ),
                };
                let follow_on = CanonicalCheckerRelatedInformation {
                    node: Some(related_node),
                    diagnostic: Diagnostic::new(
                        message_by_code(6204)
                            .expect("pinned follow-on related diagnostic is in the catalog"),
                    ),
                };
                if related_node == node
                    || diagnostic.related_information.len() >= 5
                    || diagnostic.related_information.contains(&leading)
                    || diagnostic.related_information.contains(&follow_on)
                {
                    continue;
                }
                let related = if diagnostic.related_information.is_empty() {
                    leading
                } else {
                    follow_on
                };
                diagnostic.append_related(related);
            }
        }
    }

    fn report_cannot_augment<TypePayload, MapperPayload>(
        &mut self,
        store: &SemanticStore<TypePayload, MapperPayload>,
        target: SemanticSymbolId,
        source: SemanticSymbolId,
    ) -> Result<(), SymbolMergeError> {
        let target_record = store
            .symbol(target)
            .ok_or(SymbolMergeError::InvalidSymbol(target))?;
        let source_record = store
            .symbol(source)
            .ok_or(SymbolMergeError::InvalidSymbol(source))?;
        let node = source_record
            .declarations()
            .and_then(|declarations| declarations.first())
            .copied();
        self.diagnostics.add(
            node,
            Diagnostic::with_arguments(
                message_by_code(2649).expect("pinned augmentation diagnostic is in the catalog"),
                [display_symbol_name(target_record)],
            ),
        );
        Ok(())
    }
}

impl<TypePayload, MapperPayload> SymbolMergeHost<TypePayload, MapperPayload>
    for CheckerDiagnosticMergeHost<'_>
{
    fn report_merge_diagnostic(
        &mut self,
        store: &SemanticStore<TypePayload, MapperPayload>,
        diagnostic: SymbolMergeDiagnostic,
    ) -> Result<(), SymbolMergeError> {
        match diagnostic.kind {
            SymbolMergeDiagnosticKind::IncompatibleDeclarations => {
                self.report_incompatible(store, diagnostic.target, diagnostic.source)
            }
            SymbolMergeDiagnosticKind::CannotAugmentNonModule => {
                self.report_cannot_augment(store, diagnostic.target, diagnostic.source)
            }
        }
    }
}

fn display_symbol_name(symbol: &ts_binder::semantic::Symbol) -> String {
    symbol.name().as_utf8().map_or_else(
        || symbol.name().escaped_display().to_string(),
        str::to_owned,
    )
}

/// A symbol graph that cannot be merged exactly by the installed substrate.
///
/// Errors terminate the current recursive session but do not imply rollback.
/// A nested error may be observed after earlier target mutations, so retrying
/// the same merge is not a supported recovery strategy.
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
        let mut host = FailClosedSymbolMergeHost;
        MergeSession::new(self, &mut host).clone_symbol(symbol)
    }

    /// Merges one source symbol into one target symbol.
    pub(super) fn merge_symbol(
        &mut self,
        target: SemanticSymbolId,
        source: SemanticSymbolId,
        unidirectional: bool,
    ) -> Result<SemanticSymbolId, SymbolMergeError> {
        let mut host = FailClosedSymbolMergeHost;
        self.merge_symbol_with_host(&mut host, target, source, unidirectional)
    }

    /// Merges one source symbol through one host-owned recursive session.
    pub(super) fn merge_symbol_with_host<Host>(
        &mut self,
        host: &mut Host,
        target: SemanticSymbolId,
        source: SemanticSymbolId,
        unidirectional: bool,
    ) -> Result<SemanticSymbolId, SymbolMergeError>
    where
        Host: SymbolMergeHost<TypePayload, MapperPayload>,
    {
        MergeSession::new(self, host).merge_symbol(target, source, unidirectional)
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
        let mut host = FailClosedSymbolMergeHost;
        self.merge_symbol_table_with_host(&mut host, target, source, unidirectional, merged_parent)
    }

    /// Merges a source table through one host-owned recursive session.
    pub(super) fn merge_symbol_table_with_host<Host>(
        &mut self,
        host: &mut Host,
        target: SymbolTableId,
        source: SymbolTableId,
        unidirectional: bool,
        merged_parent: Option<SemanticSymbolId>,
    ) -> Result<(), SymbolMergeError>
    where
        Host: SymbolMergeHost<TypePayload, MapperPayload>,
    {
        MergeSession::new(self, host).merge_symbol_table(
            target,
            source,
            unidirectional,
            merged_parent,
        )
    }

    /// Merges one symbol into the checker globals table by its exact escaped
    /// name and returns the table's resulting symbol.
    pub(super) fn merge_global_symbol(
        &mut self,
        globals: SymbolTableId,
        symbol: SemanticSymbolId,
    ) -> Result<SemanticSymbolId, SymbolMergeError> {
        let mut host = FailClosedSymbolMergeHost;
        self.merge_global_symbol_with_host(&mut host, globals, symbol)
    }

    /// Merges one global through one host-owned recursive session.
    pub(super) fn merge_global_symbol_with_host<Host>(
        &mut self,
        host: &mut Host,
        globals: SymbolTableId,
        symbol: SemanticSymbolId,
    ) -> Result<SemanticSymbolId, SymbolMergeError>
    where
        Host: SymbolMergeHost<TypePayload, MapperPayload>,
    {
        MergeSession::new(self, host).merge_global_symbol(globals, symbol)
    }
}

#[allow(dead_code)] // Constructed through the sibling-visible entry points above.
struct MergeSession<'store, 'host, TypePayload, MapperPayload, Host> {
    store: &'store mut SemanticStore<TypePayload, MapperPayload>,
    host: &'host mut Host,
    active: HashSet<(SemanticSymbolId, SemanticSymbolId)>,
}

#[allow(dead_code)] // Constructed through the sibling-visible entry points above.
impl<'store, 'host, TypePayload, MapperPayload, Host>
    MergeSession<'store, 'host, TypePayload, MapperPayload, Host>
where
    Host: SymbolMergeHost<TypePayload, MapperPayload>,
{
    fn new(
        store: &'store mut SemanticStore<TypePayload, MapperPayload>,
        host: &'host mut Host,
    ) -> Self {
        Self {
            store,
            host,
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
                    self.report_diagnostic(SymbolMergeDiagnostic {
                        kind: SymbolMergeDiagnosticKind::IncompatibleDeclarations,
                        target,
                        source,
                    })?;
                    return Ok(source);
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
                self.report_diagnostic(SymbolMergeDiagnostic {
                    kind: SymbolMergeDiagnosticKind::CannotAugmentNonModule,
                    target,
                    source,
                })?;
            }
        } else {
            self.report_diagnostic(SymbolMergeDiagnostic {
                kind: SymbolMergeDiagnosticKind::IncompatibleDeclarations,
                target,
                source,
            })?;
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
        &mut self,
        symbol: SemanticSymbolId,
    ) -> Result<SemanticSymbolId, SymbolMergeError> {
        let flags = self.symbol(symbol)?.flags();
        let alias_excludes = SymbolFlags::VALUE | SymbolFlags::TYPE | SymbolFlags::NAMESPACE;
        let non_local_alias = flags & (SymbolFlags::ALIAS | alias_excludes) == SymbolFlags::ALIAS
            || flags.intersects(SymbolFlags::ALIAS) && flags.intersects(SymbolFlags::ASSIGNMENT);
        if non_local_alias {
            let resolved = self.host.resolve_alias_for_merge(self.store, symbol)?;
            self.symbol(resolved)?;
            Ok(resolved)
        } else {
            Ok(symbol)
        }
    }

    fn report_diagnostic(
        &mut self,
        diagnostic: SymbolMergeDiagnostic,
    ) -> Result<(), SymbolMergeError> {
        self.host.report_merge_diagnostic(self.store, diagnostic)
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
