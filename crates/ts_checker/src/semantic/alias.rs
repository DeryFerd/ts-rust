//! Canonical alias-target caching and cycle resolution.
//!
//! This is the declaration-provider-independent kernel of the pinned
//! `getImmediateAliasedSymbol`, `resolveAlias`, `resolveIndirectionAlias`, and
//! `tryResolveAlias` paths. Syntax-specific target discovery remains a host
//! capability: an unsupported declaration family fails explicitly and never
//! becomes a cached missing target.

use ts_ast::{FileId, NodeRef};
use ts_binder::{SemanticStoreId, SemanticSymbolId, SymbolFlags};

use super::{
    AliasSymbolLinks, AliasTargetState, CanonicalSemanticStore, TypeResolutionTarget,
    TypeResolutionTargetError, TypeSystemPropertyName, links::TypeResolutionCheckpoint,
};

const CIRCULAR_DEFINITION_OF_IMPORT_ALIAS: u32 = 2_303;

/// One immediate result from the syntax-specific alias target provider.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CanonicalImmediateAliasTarget {
    /// The declaration resolved normally but has no target.
    Missing,
    /// The declaration resolved to this store-owned symbol.
    Resolved(SemanticSymbolId),
}

/// Why a host cannot supply the exact target of an alias declaration.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CanonicalAliasTargetUnavailable {
    /// The declaration belongs to a syntax/provider family outside this port.
    UnsupportedDeclarationFamily,
    /// The declaration family is known, but one of its semantic providers is
    /// not installed yet.
    TargetProviderUnavailable,
    /// The Program did not install module-resolution capability for this
    /// exact module-specifier node.
    ModuleResolutionCapabilityUnavailable(NodeRef),
    /// Module-resolution capability is installed, but has no entry for this
    /// exact module-specifier node.
    ModuleResolutionEntryAbsent(NodeRef),
    /// The Program attempted and failed resolution for this exact module-
    /// specifier node.
    ModuleResolutionUnresolved(NodeRef),
    /// The selected alias declaration is outside the production provider's
    /// dependency-closed syntax slice.
    UnsupportedAliasDeclaration(NodeRef),
    /// Default imports and re-exports require the default/export-equals
    /// interoperability path, which is not part of the plain-ESM slice.
    UnsupportedDefaultAlias(NodeRef),
    /// A named export without a module specifier needs lexical name
    /// resolution instead of module-resolution facts.
    UnsupportedLocalExport(NodeRef),
    /// The requested member is not a direct export and the module contains
    /// export-star declarations whose resolved export table is unavailable.
    ExportStarResolutionUnsupported {
        declaration: NodeRef,
        module: SemanticSymbolId,
    },
    /// The target module contains an `export =` entry and needs CommonJS/ESM
    /// interoperability semantics.
    ExportEqualsResolutionUnsupported {
        declaration: NodeRef,
        module: SemanticSymbolId,
    },
    /// The declaration or target uses `CommonJS` resolution semantics.
    CommonJsModuleUnsupported { declaration: NodeRef, file: FileId },
    /// JavaScript declaration semantics are not installed in this provider.
    JavaScriptModuleUnsupported { declaration: NodeRef, file: FileId },
    /// The resolved module needs a synthetic ESM namespace/interoperability
    /// wrapper rather than a direct source-file module symbol.
    SyntheticModuleResolutionUnsupported {
        declaration: NodeRef,
        module: SemanticSymbolId,
    },
    /// A retained declaration no longer has the exact shape that was bound.
    MalformedDeclaration(NodeRef),
    /// A retained AST arena changed after declaration binding completed.
    StaleSourceFile(FileId),
    /// The callback was invoked with a semantic store other than the one used
    /// to construct the production provider.
    ForeignStore {
        expected: SemanticStoreId,
        actual: SemanticStoreId,
    },
    /// A declaration or resolved target belongs to an unretained/foreign AST
    /// source.
    ForeignDeclaration(NodeRef),
    /// A resolved module names a Program file that was not retained by this
    /// production host.
    ForeignModuleTarget { declaration: NodeRef, file: FileId },
    /// Binder declaration ownership does not agree with the alias selected by
    /// the canonical symbol's reverse declaration search.
    AliasDeclarationOwnerMismatch {
        alias: SemanticSymbolId,
        declaration: NodeRef,
    },
    /// The retained module source symbol or its direct export table is
    /// malformed for this Program.
    MalformedModuleSymbol {
        declaration: NodeRef,
        module: SemanticSymbolId,
    },
    /// A direct, byte-exact export with the requested module-export name is
    /// absent. Diagnostics, rather than a cached missing alias, own this case.
    MissingExport {
        declaration: NodeRef,
        module: SemanticSymbolId,
    },
    /// The alias checker-links record needed for a syntactic type-only marker
    /// was not available or rejected the exact declaration node.
    InvalidAliasLinks(SemanticSymbolId),
}

/// Syntax-specific callback required by the dependency-closed alias kernel.
///
/// Implementations may publish checker links such as `type_only_declaration`
/// while resolving a target, matching `getTargetOfAliasDeclaration` upstream.
/// Returning [`CanonicalAliasTargetUnavailable`] is fail-closed: the kernel
/// restores its resolution stack and leaves the transitive target unresolved.
pub trait CanonicalAliasTargetHost<MapperPayload> {
    /// Returns the immediate target selected by the alias declaration.
    ///
    /// # Errors
    ///
    /// Returns a typed unavailable boundary when the declaration family or a
    /// semantic provider needed by that family is not installed.
    fn get_target_of_alias_declaration(
        &mut self,
        store: &mut CanonicalSemanticStore<MapperPayload>,
        alias: SemanticSymbolId,
    ) -> Result<CanonicalImmediateAliasTarget, CanonicalAliasTargetUnavailable>;
}

/// Checker event emitted while first resolving an alias target.
///
/// Diagnostic ownership remains outside this kernel. The later owner can use
/// the alias symbol to recover its pinned declaration and display name.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CanonicalAliasResolutionEvent {
    /// Pinned TS2303, emitted once for each active alias invalidated while a
    /// circular chain unwinds.
    CircularDefinitionOfImportAlias { alias: SemanticSymbolId },
}

impl CanonicalAliasResolutionEvent {
    /// The pinned diagnostic code owned by the later checker-diagnostics
    /// layer.
    #[must_use]
    pub const fn diagnostic_code(self) -> u32 {
        match self {
            Self::CircularDefinitionOfImportAlias { .. } => CIRCULAR_DEFINITION_OF_IMPORT_ALIAS,
        }
    }
}

/// Result of one transitive alias query.
///
/// `events` contains only events produced by this query. A cached subsequent
/// lookup returns the same target with an empty event list, matching upstream's
/// one-time diagnostic side effect.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CanonicalAliasResolution {
    pub target: AliasTargetState,
    pub events: Vec<CanonicalAliasResolutionEvent>,
}

/// An invariant or unavailable dependency encountered by alias resolution.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CanonicalAliasResolutionError {
    InvalidSymbol(SemanticSymbolId),
    SymbolIsNotAlias(SemanticSymbolId),
    InvalidTarget {
        alias: SemanticSymbolId,
        target: SemanticSymbolId,
    },
    TargetUnavailable {
        alias: SemanticSymbolId,
        reason: CanonicalAliasTargetUnavailable,
    },
    InvalidAliasLinks(SemanticSymbolId),
    TypeResolutionTarget(TypeResolutionTargetError),
    ResolutionStackInvariant(SemanticSymbolId),
}

impl std::fmt::Display for CanonicalAliasResolutionError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::InvalidSymbol(symbol) => {
                write!(
                    formatter,
                    "alias resolution received invalid symbol {symbol:?}"
                )
            }
            Self::SymbolIsNotAlias(symbol) => {
                write!(formatter, "symbol {symbol:?} has no alias meaning")
            }
            Self::InvalidTarget { alias, target } => write!(
                formatter,
                "alias {alias:?} resolved to invalid target {target:?}"
            ),
            Self::TargetUnavailable { alias, reason } => write!(
                formatter,
                "alias target provider is unavailable for {alias:?}: {reason:?}"
            ),
            Self::InvalidAliasLinks(symbol) => {
                write!(formatter, "alias links rejected state for {symbol:?}")
            }
            Self::TypeResolutionTarget(error) => write!(formatter, "{error}"),
            Self::ResolutionStackInvariant(symbol) => write!(
                formatter,
                "alias resolution stack could not unwind {symbol:?}"
            ),
        }
    }
}

impl std::error::Error for CanonicalAliasResolutionError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::TypeResolutionTarget(error) => Some(error),
            _ => None,
        }
    }
}

impl From<TypeResolutionTargetError> for CanonicalAliasResolutionError {
    fn from(error: TypeResolutionTargetError) -> Self {
        Self::TypeResolutionTarget(error)
    }
}

/// Stateful view over one checker store and its declaration-specific provider.
pub struct CanonicalAliasResolver<'store, 'host, MapperPayload, Host> {
    store: &'store mut CanonicalSemanticStore<MapperPayload>,
    host: &'host mut Host,
}

impl<'store, 'host, MapperPayload, Host> CanonicalAliasResolver<'store, 'host, MapperPayload, Host>
where
    Host: CanonicalAliasTargetHost<MapperPayload>,
{
    #[must_use]
    pub fn new(
        store: &'store mut CanonicalSemanticStore<MapperPayload>,
        host: &'host mut Host,
    ) -> Self {
        Self { store, host }
    }

    /// Returns and positively caches the immediate declaration target.
    ///
    /// A missing target remains uncached because the pinned immediate-target
    /// link uses `nil` for both unresolved and missing states.
    ///
    /// # Errors
    ///
    /// Returns an error for a foreign/non-alias symbol, an invalid provider
    /// target, an unavailable target provider, or rejected link state.
    pub fn get_immediate_aliased_symbol(
        &mut self,
        alias: SemanticSymbolId,
    ) -> Result<Option<SemanticSymbolId>, CanonicalAliasResolutionError> {
        self.prepare_alias(alias)?;
        if let Some(target) = self
            .store
            .alias_symbol_links(alias)
            .and_then(|links| links.immediate_target)
        {
            return Ok(Some(target));
        }

        let immediate = self.target_from_host(alias)?;
        let CanonicalImmediateAliasTarget::Resolved(target) = immediate else {
            return Ok(None);
        };
        self.validate_target(alias, target)?;
        let mut links = self.alias_links(alias)?;
        links.immediate_target = Some(target);
        self.publish_alias_links(alias, links)?;
        Ok(Some(target))
    }

    /// Resolves a pure alias chain to its first target with another meaning.
    ///
    /// # Errors
    ///
    /// Returns an error when the symbol graph is invalid, target discovery is
    /// unavailable, or the typed resolution/link stores reject an invariant.
    pub fn resolve_alias(
        &mut self,
        alias: SemanticSymbolId,
    ) -> Result<CanonicalAliasResolution, CanonicalAliasResolutionError> {
        let mut events = Vec::new();
        let target = self.resolve_alias_worker(alias, &mut events)?;
        Ok(CanonicalAliasResolution { target, events })
    }

    /// Resolves unless the uncached alias is already active in the current
    /// alias-target resolution chain.
    ///
    /// # Errors
    ///
    /// Returns the same typed symbol, provider, resolution-stack, and link
    /// errors as [`Self::resolve_alias`].
    pub fn try_resolve_alias(
        &mut self,
        alias: SemanticSymbolId,
    ) -> Result<Option<CanonicalAliasResolution>, CanonicalAliasResolutionError> {
        self.prepare_alias(alias)?;
        let state = self.alias_links(alias)?.alias_target;
        if !state.has_property()
            && self
                .store
                .find_type_resolution_cycle_start(
                    TypeResolutionTarget::Symbol(alias),
                    TypeSystemPropertyName::AliasTarget,
                )?
                .is_some()
        {
            return Ok(None);
        }
        self.resolve_alias(alias).map(Some)
    }

    fn resolve_alias_worker(
        &mut self,
        alias: SemanticSymbolId,
        events: &mut Vec<CanonicalAliasResolutionEvent>,
    ) -> Result<AliasTargetState, CanonicalAliasResolutionError> {
        self.prepare_alias(alias)?;
        let cached = self.alias_links(alias)?.alias_target;
        if cached.has_property() {
            return Ok(cached);
        }
        let initial_target = cached;

        let checkpoint = self.store.checkpoint_type_resolution();
        let pushed = match self.store.push_type_resolution(
            TypeResolutionTarget::Symbol(alias),
            TypeSystemPropertyName::AliasTarget,
        ) {
            Ok(pushed) => pushed,
            Err(error) => {
                self.commit_checkpoint(alias, checkpoint)?;
                return Err(error.into());
            }
        };
        if !pushed {
            self.commit_checkpoint(alias, checkpoint)?;
            return Ok(AliasTargetState::Unknown);
        }

        let target = match self.resolve_uncached_alias(alias, events) {
            Ok(target) => target,
            Err(error) => return Err(self.rollback_error(alias, checkpoint, error)),
        };
        let target = match self.publish_alias_target(alias, target) {
            Ok(target) => target,
            Err(error) => {
                return Err(self.rollback_published_error(
                    alias,
                    initial_target,
                    checkpoint,
                    error,
                ));
            }
        };
        let Some(cycle_free) = self.store.pop_type_resolution() else {
            let error = CanonicalAliasResolutionError::ResolutionStackInvariant(alias);
            return Err(self.rollback_published_error(alias, initial_target, checkpoint, error));
        };
        if cycle_free {
            self.commit_published_checkpoint(alias, initial_target, checkpoint)?;
            return Ok(target);
        }

        let target = match self.publish_alias_target(alias, AliasTargetState::Unknown) {
            Ok(target) => target,
            Err(error) => {
                return Err(self.rollback_published_error(
                    alias,
                    initial_target,
                    checkpoint,
                    error,
                ));
            }
        };
        self.commit_published_checkpoint(alias, initial_target, checkpoint)?;
        events.push(CanonicalAliasResolutionEvent::CircularDefinitionOfImportAlias { alias });
        Ok(target)
    }

    fn resolve_uncached_alias(
        &mut self,
        alias: SemanticSymbolId,
        events: &mut Vec<CanonicalAliasResolutionEvent>,
    ) -> Result<AliasTargetState, CanonicalAliasResolutionError> {
        let immediate = self.target_from_host(alias)?;
        let CanonicalImmediateAliasTarget::Resolved(target) = immediate else {
            return Ok(AliasTargetState::Unknown);
        };
        let flags = self.validate_target(alias, target)?;
        if !is_non_local_alias(flags) {
            return Ok(AliasTargetState::Resolved(target));
        }

        let resolved = self.resolve_alias_worker(target, events)?;
        self.propagate_type_only_declaration(alias, target)?;
        match resolved {
            AliasTargetState::Unknown => Ok(AliasTargetState::Unknown),
            AliasTargetState::Resolved(resolved) => self
                .store
                .get_merged_symbol(resolved)
                .map(AliasTargetState::Resolved)
                .ok_or(CanonicalAliasResolutionError::InvalidTarget {
                    alias,
                    target: resolved,
                }),
            AliasTargetState::Unresolved => unreachable!("recursive alias query always resolves"),
        }
    }

    fn prepare_alias(
        &mut self,
        alias: SemanticSymbolId,
    ) -> Result<(), CanonicalAliasResolutionError> {
        let flags = self
            .store
            .symbol(alias)
            .ok_or(CanonicalAliasResolutionError::InvalidSymbol(alias))?
            .flags();
        if !flags.intersects(SymbolFlags::ALIAS) {
            return Err(CanonicalAliasResolutionError::SymbolIsNotAlias(alias));
        }
        if !self.store.ensure_alias_symbol_links(alias) {
            return Err(CanonicalAliasResolutionError::InvalidAliasLinks(alias));
        }
        Ok(())
    }

    fn validate_target(
        &self,
        alias: SemanticSymbolId,
        target: SemanticSymbolId,
    ) -> Result<SymbolFlags, CanonicalAliasResolutionError> {
        self.store
            .symbol(target)
            .map(ts_binder::semantic::Symbol::flags)
            .ok_or(CanonicalAliasResolutionError::InvalidTarget { alias, target })
    }

    fn target_from_host(
        &mut self,
        alias: SemanticSymbolId,
    ) -> Result<CanonicalImmediateAliasTarget, CanonicalAliasResolutionError> {
        self.host
            .get_target_of_alias_declaration(self.store, alias)
            .map_err(|reason| CanonicalAliasResolutionError::TargetUnavailable { alias, reason })
    }

    fn alias_links(
        &self,
        alias: SemanticSymbolId,
    ) -> Result<AliasSymbolLinks, CanonicalAliasResolutionError> {
        self.store
            .alias_symbol_links(alias)
            .cloned()
            .ok_or(CanonicalAliasResolutionError::InvalidAliasLinks(alias))
    }

    fn publish_alias_links(
        &mut self,
        alias: SemanticSymbolId,
        links: AliasSymbolLinks,
    ) -> Result<(), CanonicalAliasResolutionError> {
        if self.store.set_alias_symbol_links(alias, links) {
            Ok(())
        } else {
            Err(CanonicalAliasResolutionError::InvalidAliasLinks(alias))
        }
    }

    fn publish_alias_target(
        &mut self,
        alias: SemanticSymbolId,
        target: AliasTargetState,
    ) -> Result<AliasTargetState, CanonicalAliasResolutionError> {
        let mut links = self.alias_links(alias)?;
        links.alias_target = target;
        self.publish_alias_links(alias, links)?;
        Ok(self.alias_links(alias)?.alias_target)
    }

    fn propagate_type_only_declaration(
        &mut self,
        source: SemanticSymbolId,
        target: SemanticSymbolId,
    ) -> Result<(), CanonicalAliasResolutionError> {
        let target_marker = self.alias_links(target)?.type_only_declaration;
        let Some(target_marker) = target_marker else {
            return Ok(());
        };
        let mut source_links = self.alias_links(source)?;
        if source_links.type_only_declaration.is_none() {
            source_links.type_only_declaration = Some(target_marker);
            self.publish_alias_links(source, source_links)?;
        }
        Ok(())
    }

    fn commit_checkpoint(
        &mut self,
        alias: SemanticSymbolId,
        checkpoint: TypeResolutionCheckpoint,
    ) -> Result<(), CanonicalAliasResolutionError> {
        match self.store.commit_type_resolution_checkpoint(checkpoint) {
            Ok(()) => Ok(()),
            Err(checkpoint) => {
                let _ = self.store.rollback_type_resolution_checkpoint(checkpoint);
                Err(CanonicalAliasResolutionError::ResolutionStackInvariant(
                    alias,
                ))
            }
        }
    }

    fn rollback_error(
        &mut self,
        alias: SemanticSymbolId,
        checkpoint: TypeResolutionCheckpoint,
        error: CanonicalAliasResolutionError,
    ) -> CanonicalAliasResolutionError {
        if self
            .store
            .rollback_type_resolution_checkpoint(checkpoint)
            .is_ok()
        {
            error
        } else {
            CanonicalAliasResolutionError::ResolutionStackInvariant(alias)
        }
    }

    fn commit_published_checkpoint(
        &mut self,
        alias: SemanticSymbolId,
        initial_target: AliasTargetState,
        checkpoint: TypeResolutionCheckpoint,
    ) -> Result<(), CanonicalAliasResolutionError> {
        match self.store.commit_type_resolution_checkpoint(checkpoint) {
            Ok(()) => Ok(()),
            Err(checkpoint) => Err(self.rollback_published_error(
                alias,
                initial_target,
                checkpoint,
                CanonicalAliasResolutionError::ResolutionStackInvariant(alias),
            )),
        }
    }

    fn rollback_published_error(
        &mut self,
        alias: SemanticSymbolId,
        initial_target: AliasTargetState,
        checkpoint: TypeResolutionCheckpoint,
        error: CanonicalAliasResolutionError,
    ) -> CanonicalAliasResolutionError {
        let stack_restored = self
            .store
            .rollback_type_resolution_checkpoint(checkpoint)
            .is_ok();
        let target_restored = self.restore_alias_target(alias, initial_target).is_ok();
        if stack_restored && target_restored {
            error
        } else {
            CanonicalAliasResolutionError::ResolutionStackInvariant(alias)
        }
    }

    fn restore_alias_target(
        &mut self,
        alias: SemanticSymbolId,
        target: AliasTargetState,
    ) -> Result<(), CanonicalAliasResolutionError> {
        let mut links = self.alias_links(alias)?;
        links.alias_target = target;
        self.publish_alias_links(alias, links)?;
        if self.alias_links(alias)?.alias_target == target {
            Ok(())
        } else {
            Err(CanonicalAliasResolutionError::InvalidAliasLinks(alias))
        }
    }
}

fn is_non_local_alias(flags: SymbolFlags) -> bool {
    let excludes = SymbolFlags::VALUE | SymbolFlags::TYPE | SymbolFlags::NAMESPACE;
    flags & (SymbolFlags::ALIAS | excludes) == SymbolFlags::ALIAS
        || flags.intersects(SymbolFlags::ALIAS) && flags.intersects(SymbolFlags::ASSIGNMENT)
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use ts_ast::{FileId, NodeRef};
    use ts_binder::{EscapedName, SymbolData};
    use ts_parser::parse_source_file;

    use super::*;

    type TestStore = CanonicalSemanticStore<()>;

    #[derive(Clone, Copy)]
    enum SyntheticTarget {
        Available(CanonicalImmediateAliasTarget),
        Unavailable(CanonicalAliasTargetUnavailable),
        ResolveThenUnavailable {
            active_alias: SemanticSymbolId,
            reason: CanonicalAliasTargetUnavailable,
        },
    }

    #[derive(Default)]
    struct SyntheticHost {
        targets: HashMap<SemanticSymbolId, SyntheticTarget>,
        calls: HashMap<SemanticSymbolId, usize>,
    }

    impl SyntheticHost {
        fn insert(&mut self, alias: SemanticSymbolId, target: CanonicalImmediateAliasTarget) {
            self.targets
                .insert(alias, SyntheticTarget::Available(target));
        }

        fn unavailable(
            &mut self,
            alias: SemanticSymbolId,
            reason: CanonicalAliasTargetUnavailable,
        ) {
            self.targets
                .insert(alias, SyntheticTarget::Unavailable(reason));
        }

        fn resolve_then_unavailable(
            &mut self,
            alias: SemanticSymbolId,
            active_alias: SemanticSymbolId,
            reason: CanonicalAliasTargetUnavailable,
        ) {
            self.targets.insert(
                alias,
                SyntheticTarget::ResolveThenUnavailable {
                    active_alias,
                    reason,
                },
            );
        }

        fn calls(&self, alias: SemanticSymbolId) -> usize {
            self.calls.get(&alias).copied().unwrap_or(0)
        }
    }

    impl<MapperPayload> CanonicalAliasTargetHost<MapperPayload> for SyntheticHost {
        fn get_target_of_alias_declaration(
            &mut self,
            store: &mut CanonicalSemanticStore<MapperPayload>,
            alias: SemanticSymbolId,
        ) -> Result<CanonicalImmediateAliasTarget, CanonicalAliasTargetUnavailable> {
            *self.calls.entry(alias).or_default() += 1;
            match self
                .targets
                .get(&alias)
                .copied()
                .unwrap_or(SyntheticTarget::Unavailable(
                    CanonicalAliasTargetUnavailable::TargetProviderUnavailable,
                )) {
                SyntheticTarget::Available(target) => Ok(target),
                SyntheticTarget::Unavailable(reason) => Err(reason),
                SyntheticTarget::ResolveThenUnavailable {
                    active_alias,
                    reason,
                } => {
                    let mut nested_host = Self::default();
                    let nested = CanonicalAliasResolver::new(store, &mut nested_host)
                        .resolve_alias(active_alias)
                        .expect("active synthetic alias query is dependency-closed");
                    assert_eq!(nested.target, AliasTargetState::Unknown);
                    Err(reason)
                }
            }
        }
    }

    fn symbol(store: &mut TestStore, name: &str, flags: SymbolFlags) -> SemanticSymbolId {
        store
            .alloc_symbol(SymbolData::new(flags, EscapedName::source(name)))
            .unwrap()
    }

    fn alias(store: &mut TestStore, name: &str) -> SemanticSymbolId {
        symbol(store, name, SymbolFlags::ALIAS)
    }

    fn alias_target(store: &TestStore, alias: SemanticSymbolId) -> AliasTargetState {
        store.alias_symbol_links(alias).unwrap().alias_target
    }

    #[test]
    fn immediate_target_positive_cache_is_distinct_from_transitive_cache() {
        let mut store = TestStore::default();
        let resolved_alias = alias(&mut store, "resolved");
        let missing_alias = alias(&mut store, "missing");
        let target = symbol(&mut store, "target", SymbolFlags::PROPERTY);
        let mut host = SyntheticHost::default();
        host.insert(
            resolved_alias,
            CanonicalImmediateAliasTarget::Resolved(target),
        );
        host.insert(missing_alias, CanonicalImmediateAliasTarget::Missing);

        {
            let mut resolver = CanonicalAliasResolver::new(&mut store, &mut host);
            assert_eq!(
                resolver.get_immediate_aliased_symbol(resolved_alias),
                Ok(Some(target))
            );
            assert_eq!(
                resolver.get_immediate_aliased_symbol(resolved_alias),
                Ok(Some(target))
            );
            assert_eq!(
                resolver.get_immediate_aliased_symbol(missing_alias),
                Ok(None)
            );
            assert_eq!(
                resolver.get_immediate_aliased_symbol(missing_alias),
                Ok(None)
            );
        }

        assert_eq!(host.calls(resolved_alias), 1);
        assert_eq!(host.calls(missing_alias), 2);
        let resolved_links = store.alias_symbol_links(resolved_alias).unwrap();
        assert_eq!(resolved_links.immediate_target, Some(target));
        assert_eq!(resolved_links.alias_target, AliasTargetState::Unresolved);
        let missing_links = store.alias_symbol_links(missing_alias).unwrap();
        assert_eq!(missing_links.immediate_target, None);
        assert_eq!(missing_links.alias_target, AliasTargetState::Unresolved);

        let transitive = CanonicalAliasResolver::new(&mut store, &mut host)
            .resolve_alias(resolved_alias)
            .unwrap();
        assert_eq!(transitive.target, AliasTargetState::Resolved(target));
        assert_eq!(host.calls(resolved_alias), 2);
        assert_eq!(
            CanonicalAliasResolver::new(&mut store, &mut host)
                .get_immediate_aliased_symbol(resolved_alias),
            Ok(Some(target))
        );
        assert_eq!(host.calls(resolved_alias), 2);
    }

    #[test]
    fn transitive_resolution_caches_each_level_and_merges_only_indirection_result() {
        let parsed = parse_source_file("export {};");
        let file = FileId::new(1);
        let marker = NodeRef::new(parsed.arena.id(), file, parsed.source_file);
        let mut store = TestStore::default();
        store
            .register_source_file(&parsed.arena, parsed.source_file, file)
            .unwrap();
        let outer = alias(&mut store, "outer");
        let inner = alias(&mut store, "inner");
        let raw_target = symbol(&mut store, "raw", SymbolFlags::PROPERTY);
        let merged_target = symbol(&mut store, "merged", SymbolFlags::PROPERTY);
        store
            .record_merged_symbol(merged_target, raw_target)
            .unwrap();
        assert!(store.set_alias_symbol_links(
            inner,
            AliasSymbolLinks {
                type_only_declaration: Some(marker),
                ..AliasSymbolLinks::default()
            }
        ));
        let mut host = SyntheticHost::default();
        host.insert(outer, CanonicalImmediateAliasTarget::Resolved(inner));
        host.insert(inner, CanonicalImmediateAliasTarget::Resolved(raw_target));

        let first = CanonicalAliasResolver::new(&mut store, &mut host)
            .resolve_alias(outer)
            .unwrap();
        assert_eq!(first.target, AliasTargetState::Resolved(merged_target));
        assert!(first.events.is_empty());
        let second = CanonicalAliasResolver::new(&mut store, &mut host)
            .resolve_alias(outer)
            .unwrap();
        assert_eq!(second.target, first.target);
        assert!(second.events.is_empty());

        assert_eq!(
            alias_target(&store, inner),
            AliasTargetState::Resolved(raw_target)
        );
        assert_eq!(
            alias_target(&store, outer),
            AliasTargetState::Resolved(merged_target)
        );
        assert_eq!(
            store
                .alias_symbol_links(outer)
                .unwrap()
                .type_only_declaration,
            Some(marker)
        );
        assert_eq!(
            store.alias_symbol_links(outer).unwrap().immediate_target,
            None,
            "resolveAlias does not populate getImmediateAliasedSymbol's cache"
        );
        assert_eq!(host.calls(outer), 1);
        assert_eq!(host.calls(inner), 1);
    }

    #[test]
    fn missing_transitive_target_is_cached_as_unknown_without_cycle_event() {
        let mut store = TestStore::default();
        let missing = alias(&mut store, "missing");
        let mut host = SyntheticHost::default();
        host.insert(missing, CanonicalImmediateAliasTarget::Missing);

        let first = CanonicalAliasResolver::new(&mut store, &mut host)
            .resolve_alias(missing)
            .unwrap();
        assert_eq!(first.target, AliasTargetState::Unknown);
        assert!(first.events.is_empty());
        assert_eq!(alias_target(&store, missing), AliasTargetState::Unknown);
        assert!(store.type_resolution_is_empty());

        let cached = CanonicalAliasResolver::new(&mut store, &mut host)
            .resolve_alias(missing)
            .unwrap();
        assert_eq!(cached.target, AliasTargetState::Unknown);
        assert!(cached.events.is_empty());
        assert_eq!(host.calls(missing), 1);
    }

    #[test]
    fn type_only_propagation_preserves_existing_marker_and_crosses_unknown() {
        let parsed = parse_source_file("interface Marker {}");
        let file = FileId::new(2);
        let source_marker = NodeRef::new(parsed.arena.id(), file, parsed.source_file);
        let target_marker_node = parsed
            .arena
            .iter()
            .find_map(|(node, _)| (node != parsed.source_file).then_some(node))
            .unwrap();
        let target_marker = NodeRef::new(parsed.arena.id(), file, target_marker_node);
        let mut store = TestStore::default();
        store
            .register_source_file(&parsed.arena, parsed.source_file, file)
            .unwrap();
        let protected = alias(&mut store, "protected");
        let propagated = alias(&mut store, "propagated");
        let target = alias(&mut store, "target");
        assert!(store.set_alias_symbol_links(
            protected,
            AliasSymbolLinks {
                type_only_declaration: Some(source_marker),
                ..AliasSymbolLinks::default()
            }
        ));
        assert!(store.set_alias_symbol_links(
            target,
            AliasSymbolLinks {
                type_only_declaration: Some(target_marker),
                ..AliasSymbolLinks::default()
            }
        ));
        let mut host = SyntheticHost::default();
        host.insert(protected, CanonicalImmediateAliasTarget::Resolved(target));
        host.insert(propagated, CanonicalImmediateAliasTarget::Resolved(target));
        host.insert(target, CanonicalImmediateAliasTarget::Missing);

        let protected_result = CanonicalAliasResolver::new(&mut store, &mut host)
            .resolve_alias(protected)
            .unwrap();
        assert_eq!(protected_result.target, AliasTargetState::Unknown);
        assert_eq!(
            store
                .alias_symbol_links(protected)
                .unwrap()
                .type_only_declaration,
            Some(source_marker)
        );

        let propagated_result = CanonicalAliasResolver::new(&mut store, &mut host)
            .resolve_alias(propagated)
            .unwrap();
        assert_eq!(propagated_result.target, AliasTargetState::Unknown);
        assert_eq!(
            store
                .alias_symbol_links(propagated)
                .unwrap()
                .type_only_declaration,
            Some(target_marker)
        );
        assert_eq!(host.calls(target), 1);
    }

    #[test]
    fn circular_chain_caches_unknown_and_emits_ts2303_events_while_unwinding() {
        let mut store = TestStore::default();
        let first = alias(&mut store, "first");
        let second = alias(&mut store, "second");
        let mut host = SyntheticHost::default();
        host.insert(first, CanonicalImmediateAliasTarget::Resolved(second));
        host.insert(second, CanonicalImmediateAliasTarget::Resolved(first));

        let resolution = CanonicalAliasResolver::new(&mut store, &mut host)
            .resolve_alias(first)
            .unwrap();
        assert_eq!(resolution.target, AliasTargetState::Unknown);
        assert_eq!(
            resolution.events,
            [
                CanonicalAliasResolutionEvent::CircularDefinitionOfImportAlias { alias: second },
                CanonicalAliasResolutionEvent::CircularDefinitionOfImportAlias { alias: first },
            ]
        );
        assert!(
            resolution
                .events
                .iter()
                .all(|event| event.diagnostic_code() == 2303)
        );
        assert_eq!(alias_target(&store, first), AliasTargetState::Unknown);
        assert_eq!(alias_target(&store, second), AliasTargetState::Unknown);
        assert!(store.type_resolution_is_empty());

        let cached = CanonicalAliasResolver::new(&mut store, &mut host)
            .resolve_alias(first)
            .unwrap();
        assert_eq!(cached.target, AliasTargetState::Unknown);
        assert!(cached.events.is_empty());
        assert_eq!(host.calls(first), 1);
        assert_eq!(host.calls(second), 1);
    }

    #[test]
    fn self_cycle_marks_only_its_suffix_and_preserves_active_outer_result() {
        let mut store = TestStore::default();
        let outer = alias(&mut store, "outer");
        let recursive = alias(&mut store, "recursive");
        assert_eq!(
            store.push_type_resolution(
                TypeResolutionTarget::Symbol(outer),
                TypeSystemPropertyName::AliasTarget,
            ),
            Ok(true)
        );
        let mut host = SyntheticHost::default();
        host.insert(
            recursive,
            CanonicalImmediateAliasTarget::Resolved(recursive),
        );

        let result = CanonicalAliasResolver::new(&mut store, &mut host)
            .resolve_alias(recursive)
            .unwrap();
        assert_eq!(result.target, AliasTargetState::Unknown);
        assert_eq!(
            result.events,
            [CanonicalAliasResolutionEvent::CircularDefinitionOfImportAlias { alias: recursive },]
        );
        assert_eq!(store.type_resolution_len(), 1);
        assert_eq!(store.pop_type_resolution(), Some(true));
    }

    #[test]
    fn callback_error_restores_outer_cycle_result_and_truncates_alias_suffix() {
        let mut store = TestStore::default();
        let outer = alias(&mut store, "outer");
        let failing = alias(&mut store, "failing");
        assert_eq!(
            store.push_type_resolution(
                TypeResolutionTarget::Symbol(outer),
                TypeSystemPropertyName::AliasTarget,
            ),
            Ok(true)
        );
        let mut host = SyntheticHost::default();
        host.resolve_then_unavailable(
            failing,
            outer,
            CanonicalAliasTargetUnavailable::UnsupportedDeclarationFamily,
        );

        let error = CanonicalAliasResolver::new(&mut store, &mut host)
            .resolve_alias(failing)
            .unwrap_err();
        assert_eq!(
            error,
            CanonicalAliasResolutionError::TargetUnavailable {
                alias: failing,
                reason: CanonicalAliasTargetUnavailable::UnsupportedDeclarationFamily,
            }
        );
        assert_eq!(alias_target(&store, failing), AliasTargetState::Unresolved);
        assert_eq!(store.type_resolution_len(), 1);
        assert_eq!(store.pop_type_resolution(), Some(true));
    }

    struct LeaveBoundaryOnceHost {
        target: SemanticSymbolId,
        marker: NodeRef,
        calls: usize,
        boundary: Option<crate::semantic::TypeResolutionBoundary>,
    }

    impl<MapperPayload> CanonicalAliasTargetHost<MapperPayload> for LeaveBoundaryOnceHost {
        fn get_target_of_alias_declaration(
            &mut self,
            store: &mut CanonicalSemanticStore<MapperPayload>,
            alias: SemanticSymbolId,
        ) -> Result<CanonicalImmediateAliasTarget, CanonicalAliasTargetUnavailable> {
            self.calls += 1;
            let mut links = store
                .alias_symbol_links(alias)
                .cloned()
                .expect("resolver prepares alias links before invoking the host");
            links.immediate_target = Some(self.target);
            links.referenced = true;
            links.type_only_declaration = Some(self.marker);
            assert!(store.set_alias_symbol_links(alias, links));
            if self.calls == 1 {
                self.boundary = Some(store.reset_type_resolution_start());
            }
            Ok(CanonicalImmediateAliasTarget::Resolved(self.target))
        }
    }

    #[test]
    fn post_publication_stack_invariant_restores_only_alias_target_and_allows_retry() {
        let parsed = parse_source_file("interface Marker {}");
        let file = FileId::new(3);
        let marker = NodeRef::new(parsed.arena.id(), file, parsed.source_file);
        let mut store = TestStore::default();
        store
            .register_source_file(&parsed.arena, parsed.source_file, file)
            .unwrap();
        let failing = alias(&mut store, "failing");
        let target = symbol(&mut store, "target", SymbolFlags::PROPERTY);
        let mut host = LeaveBoundaryOnceHost {
            target,
            marker,
            calls: 0,
            boundary: None,
        };

        let error = CanonicalAliasResolver::new(&mut store, &mut host)
            .resolve_alias(failing)
            .unwrap_err();
        assert_eq!(
            error,
            CanonicalAliasResolutionError::ResolutionStackInvariant(failing)
        );
        assert_eq!(
            store.alias_symbol_links(failing),
            Some(&AliasSymbolLinks {
                immediate_target: Some(target),
                alias_target: AliasTargetState::Unresolved,
                referenced: true,
                type_only_declaration: Some(marker),
            })
        );
        assert!(store.type_resolution_is_empty());

        let stale_boundary = host
            .boundary
            .take()
            .expect("first callback leaves one boundary token");
        let replacement = store.reset_type_resolution_start();
        let _stale_boundary = store
            .restore_type_resolution_start(stale_boundary)
            .expect_err("rolled-back boundary identity must not be reused");
        assert!(store.restore_type_resolution_start(replacement).is_ok());

        let retry = CanonicalAliasResolver::new(&mut store, &mut host)
            .resolve_alias(failing)
            .unwrap();
        assert_eq!(retry.target, AliasTargetState::Resolved(target));
        assert!(retry.events.is_empty());
        assert_eq!(host.calls, 2);
        assert_eq!(
            alias_target(&store, failing),
            AliasTargetState::Resolved(target)
        );
    }

    struct CycleThenLeaveBoundaryOnceHost {
        target: SemanticSymbolId,
        calls: usize,
        boundary: Option<crate::semantic::TypeResolutionBoundary>,
    }

    impl<MapperPayload> CanonicalAliasTargetHost<MapperPayload> for CycleThenLeaveBoundaryOnceHost {
        fn get_target_of_alias_declaration(
            &mut self,
            store: &mut CanonicalSemanticStore<MapperPayload>,
            alias: SemanticSymbolId,
        ) -> Result<CanonicalImmediateAliasTarget, CanonicalAliasTargetUnavailable> {
            self.calls += 1;
            if self.calls == 1 {
                assert_eq!(store.pop_type_resolution(), Some(true));
                self.boundary = Some(store.reset_type_resolution_start());
                assert_eq!(
                    store.push_type_resolution(
                        TypeResolutionTarget::Symbol(alias),
                        TypeSystemPropertyName::AliasTarget,
                    ),
                    Ok(true)
                );
                assert_eq!(
                    store.push_type_resolution(
                        TypeResolutionTarget::Symbol(alias),
                        TypeSystemPropertyName::AliasTarget,
                    ),
                    Ok(false)
                );
            }
            Ok(CanonicalImmediateAliasTarget::Resolved(self.target))
        }
    }

    #[test]
    fn cycle_unknown_commit_invariant_restores_alias_target_before_retry() {
        let mut store = TestStore::default();
        let failing = alias(&mut store, "failing");
        let target = symbol(&mut store, "target", SymbolFlags::PROPERTY);
        let mut host = CycleThenLeaveBoundaryOnceHost {
            target,
            calls: 0,
            boundary: None,
        };

        let error = CanonicalAliasResolver::new(&mut store, &mut host)
            .resolve_alias(failing)
            .unwrap_err();
        assert_eq!(
            error,
            CanonicalAliasResolutionError::ResolutionStackInvariant(failing)
        );
        assert_eq!(alias_target(&store, failing), AliasTargetState::Unresolved);
        assert!(store.type_resolution_is_empty());
        let stale_boundary = host
            .boundary
            .take()
            .expect("first callback leaves one cycle boundary token");
        let _stale_boundary = store
            .restore_type_resolution_start(stale_boundary)
            .expect_err("failed cycle commit must roll back its callback boundary");

        let retry = CanonicalAliasResolver::new(&mut store, &mut host)
            .resolve_alias(failing)
            .unwrap();
        assert_eq!(retry.target, AliasTargetState::Resolved(target));
        assert!(retry.events.is_empty());
        assert_eq!(host.calls, 2);
    }

    struct RemovePreexistingBoundaryHost {
        boundary: Option<crate::semantic::TypeResolutionBoundary>,
    }

    impl<MapperPayload> CanonicalAliasTargetHost<MapperPayload> for RemovePreexistingBoundaryHost {
        fn get_target_of_alias_declaration(
            &mut self,
            store: &mut CanonicalSemanticStore<MapperPayload>,
            _alias: SemanticSymbolId,
        ) -> Result<CanonicalImmediateAliasTarget, CanonicalAliasTargetUnavailable> {
            assert_eq!(store.pop_type_resolution(), Some(true));
            let boundary = self
                .boundary
                .take()
                .expect("synthetic callback owns one pre-existing boundary token");
            assert!(store.restore_type_resolution_start(boundary).is_ok());
            Err(CanonicalAliasTargetUnavailable::TargetProviderUnavailable)
        }
    }

    #[test]
    fn removed_preexisting_boundary_surfaces_resolution_stack_invariant() {
        let mut store = TestStore::default();
        let failing = alias(&mut store, "failing");
        let boundary = store.reset_type_resolution_start();
        let mut host = RemovePreexistingBoundaryHost {
            boundary: Some(boundary),
        };

        let error = CanonicalAliasResolver::new(&mut store, &mut host)
            .resolve_alias(failing)
            .unwrap_err();
        assert_eq!(
            error,
            CanonicalAliasResolutionError::ResolutionStackInvariant(failing)
        );
        assert_eq!(alias_target(&store, failing), AliasTargetState::Unresolved);
        assert!(store.type_resolution_is_empty());
    }

    #[test]
    fn local_meaning_stops_indirection_but_assignment_aliases_continue() {
        let mut store = TestStore::default();
        let local_source = alias(&mut store, "localSource");
        let local_target = symbol(
            &mut store,
            "localTarget",
            SymbolFlags::ALIAS | SymbolFlags::TYPE,
        );
        let assignment_source = alias(&mut store, "assignmentSource");
        let assignment_target = symbol(
            &mut store,
            "assignmentTarget",
            SymbolFlags::ALIAS | SymbolFlags::TYPE | SymbolFlags::ASSIGNMENT,
        );
        let value = symbol(&mut store, "value", SymbolFlags::PROPERTY);
        let mut host = SyntheticHost::default();
        host.insert(
            local_source,
            CanonicalImmediateAliasTarget::Resolved(local_target),
        );
        host.unavailable(
            local_target,
            CanonicalAliasTargetUnavailable::TargetProviderUnavailable,
        );
        host.insert(
            assignment_source,
            CanonicalImmediateAliasTarget::Resolved(assignment_target),
        );
        host.insert(
            assignment_target,
            CanonicalImmediateAliasTarget::Resolved(value),
        );

        let local = CanonicalAliasResolver::new(&mut store, &mut host)
            .resolve_alias(local_source)
            .unwrap();
        assert_eq!(local.target, AliasTargetState::Resolved(local_target));
        assert_eq!(host.calls(local_target), 0);

        let assignment = CanonicalAliasResolver::new(&mut store, &mut host)
            .resolve_alias(assignment_source)
            .unwrap();
        assert_eq!(assignment.target, AliasTargetState::Resolved(value));
        assert_eq!(host.calls(assignment_target), 1);
    }

    #[test]
    fn unavailable_or_foreign_targets_fail_closed_and_restore_the_stack() {
        let mut store = TestStore::default();
        let unavailable = alias(&mut store, "unavailable");
        let foreign_alias = alias(&mut store, "foreign");
        let mut foreign_store = TestStore::default();
        let foreign_target = symbol(&mut foreign_store, "target", SymbolFlags::PROPERTY);
        let mut host = SyntheticHost::default();
        host.unavailable(
            unavailable,
            CanonicalAliasTargetUnavailable::UnsupportedDeclarationFamily,
        );
        host.insert(
            foreign_alias,
            CanonicalImmediateAliasTarget::Resolved(foreign_target),
        );

        let unavailable_error = CanonicalAliasResolutionError::TargetUnavailable {
            alias: unavailable,
            reason: CanonicalAliasTargetUnavailable::UnsupportedDeclarationFamily,
        };
        assert_eq!(
            CanonicalAliasResolver::new(&mut store, &mut host)
                .get_immediate_aliased_symbol(unavailable),
            Err(unavailable_error)
        );
        assert_eq!(
            alias_target(&store, unavailable),
            AliasTargetState::Unresolved
        );
        assert_eq!(
            store
                .alias_symbol_links(unavailable)
                .unwrap()
                .immediate_target,
            None
        );
        assert!(store.type_resolution_is_empty());
        assert_eq!(
            CanonicalAliasResolver::new(&mut store, &mut host).try_resolve_alias(unavailable),
            Err(unavailable_error)
        );
        assert_eq!(
            alias_target(&store, unavailable),
            AliasTargetState::Unresolved
        );
        assert!(store.type_resolution_is_empty());

        assert_eq!(
            CanonicalAliasResolver::new(&mut store, &mut host).resolve_alias(unavailable),
            Err(unavailable_error)
        );
        assert_eq!(
            alias_target(&store, unavailable),
            AliasTargetState::Unresolved
        );
        assert!(store.type_resolution_is_empty());

        let foreign_error = CanonicalAliasResolutionError::InvalidTarget {
            alias: foreign_alias,
            target: foreign_target,
        };
        assert_eq!(
            CanonicalAliasResolver::new(&mut store, &mut host)
                .get_immediate_aliased_symbol(foreign_alias),
            Err(foreign_error)
        );
        assert_eq!(
            alias_target(&store, foreign_alias),
            AliasTargetState::Unresolved
        );
        assert_eq!(
            store
                .alias_symbol_links(foreign_alias)
                .unwrap()
                .immediate_target,
            None
        );
        assert!(store.type_resolution_is_empty());
        assert_eq!(
            CanonicalAliasResolver::new(&mut store, &mut host).try_resolve_alias(foreign_alias),
            Err(foreign_error)
        );
        assert_eq!(
            alias_target(&store, foreign_alias),
            AliasTargetState::Unresolved
        );
        assert!(store.type_resolution_is_empty());
        assert_eq!(
            CanonicalAliasResolver::new(&mut store, &mut host).resolve_alias(foreign_alias),
            Err(foreign_error)
        );
        assert_eq!(
            alias_target(&store, foreign_alias),
            AliasTargetState::Unresolved
        );
        assert!(store.type_resolution_is_empty());
    }

    #[test]
    fn try_resolve_alias_does_not_reenter_an_active_uncached_alias() {
        let mut store = TestStore::default();
        let active = alias(&mut store, "active");
        assert_eq!(
            store.push_type_resolution(
                TypeResolutionTarget::Symbol(active),
                TypeSystemPropertyName::AliasTarget,
            ),
            Ok(true)
        );
        let mut host = SyntheticHost::default();
        host.insert(active, CanonicalImmediateAliasTarget::Missing);

        let result = CanonicalAliasResolver::new(&mut store, &mut host)
            .try_resolve_alias(active)
            .unwrap();
        assert_eq!(result, None);
        assert_eq!(host.calls(active), 0);
        assert_eq!(alias_target(&store, active), AliasTargetState::Unresolved);
        assert_eq!(store.type_resolution_len(), 1);
        assert_eq!(store.pop_type_resolution(), Some(true));
    }

    #[test]
    fn non_alias_symbols_are_rejected_before_provider_or_cache_mutation() {
        let mut store = TestStore::default();
        let value = symbol(&mut store, "value", SymbolFlags::PROPERTY);
        let mut host = SyntheticHost::default();
        let error = CanonicalAliasResolver::new(&mut store, &mut host)
            .resolve_alias(value)
            .unwrap_err();
        assert_eq!(
            error,
            CanonicalAliasResolutionError::SymbolIsNotAlias(value)
        );
        assert!(store.alias_symbol_links(value).is_none());
        assert_eq!(host.calls(value), 0);
        assert!(store.type_resolution_is_empty());
    }
}
