//! Combined symbol meanings across canonical alias targets.
//!
//! This is the dependency-closed kernel of the pinned `getSymbolFlags` and
//! `getSymbolFlagsEx` paths. Alias target discovery remains owned by
//! [`CanonicalAliasTargetHost`].

use std::collections::HashSet;

use ts_binder::{SemanticSymbolId, SymbolFlags};

use super::{
    AliasTargetState, CanonicalSemanticStore,
    alias::{
        CanonicalAliasResolutionError, CanonicalAliasResolutionEvent, CanonicalAliasResolver,
        CanonicalAliasTargetHost,
    },
};

/// The flags and one-time alias-resolution events produced by one query.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CanonicalSymbolFlagsResolution {
    pub flags: SymbolFlags,
    pub events: Vec<CanonicalAliasResolutionEvent>,
}

/// Invalid canonical state or an unavailable alias dependency.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CanonicalSymbolFlagsError {
    InvalidSymbol(SemanticSymbolId),
    AliasResolution(CanonicalAliasResolutionError),
    InvalidAliasLinks(SemanticSymbolId),
    UnresolvedAliasTarget(SemanticSymbolId),
    InvalidExportSymbol {
        value_symbol: SemanticSymbolId,
        export_symbol: SemanticSymbolId,
    },
    InvalidMergedSymbol(SemanticSymbolId),
}

impl std::fmt::Display for CanonicalSymbolFlagsError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::InvalidSymbol(symbol) => {
                write!(formatter, "symbol flags received invalid symbol {symbol:?}")
            }
            Self::AliasResolution(error) => error.fmt(formatter),
            Self::InvalidAliasLinks(symbol) => {
                write!(formatter, "alias links are unavailable for {symbol:?}")
            }
            Self::UnresolvedAliasTarget(symbol) => {
                write!(
                    formatter,
                    "alias {symbol:?} remained unresolved after resolution"
                )
            }
            Self::InvalidExportSymbol {
                value_symbol,
                export_symbol,
            } => write!(
                formatter,
                "export value {value_symbol:?} has invalid export symbol {export_symbol:?}"
            ),
            Self::InvalidMergedSymbol(symbol) => {
                write!(formatter, "merged-symbol routing rejected {symbol:?}")
            }
        }
    }
}

impl std::error::Error for CanonicalSymbolFlagsError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::AliasResolution(error) => Some(error),
            _ => None,
        }
    }
}

impl From<CanonicalAliasResolutionError> for CanonicalSymbolFlagsError {
    fn from(error: CanonicalAliasResolutionError) -> Self {
        Self::AliasResolution(error)
    }
}

/// Stateful view over one checker store and its alias target provider.
pub struct CanonicalSymbolFlagsResolver<'store, 'host, MapperPayload, Host> {
    store: &'store mut CanonicalSemanticStore<MapperPayload>,
    host: &'host mut Host,
}

impl<'store, 'host, MapperPayload, Host>
    CanonicalSymbolFlagsResolver<'store, 'host, MapperPayload, Host>
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

    /// Gets the local meanings and all meanings reached through alias targets.
    ///
    /// # Errors
    ///
    /// Returns a typed error for foreign symbols, malformed export routing, or
    /// any alias-resolution provider/invariant failure.
    pub fn get_symbol_flags(
        &mut self,
        symbol: SemanticSymbolId,
    ) -> Result<CanonicalSymbolFlagsResolution, CanonicalSymbolFlagsError> {
        self.get_symbol_flags_ex(symbol, false, false)
    }

    /// Gets combined meanings with the pinned local/type-only exclusions.
    ///
    /// A target resolving to the canonical unknown state returns
    /// [`SymbolFlags::ALL`] to suppress cascading errors.
    ///
    /// # Errors
    ///
    /// Returns a typed error for foreign symbols, malformed export routing, or
    /// any alias-resolution provider/invariant failure.
    pub fn get_symbol_flags_ex(
        &mut self,
        mut symbol: SemanticSymbolId,
        exclude_type_only_meanings: bool,
        exclude_local_meanings: bool,
    ) -> Result<CanonicalSymbolFlagsResolution, CanonicalSymbolFlagsError> {
        let initial_flags = self.symbol_flags(symbol)?;
        let mut flags = if exclude_local_meanings {
            SymbolFlags::NONE
        } else {
            initial_flags
        };
        let mut events = Vec::new();
        let mut seen_symbols = None::<HashSet<SemanticSymbolId>>;
        let mut symbol_flags = initial_flags;

        while symbol_flags.intersects(SymbolFlags::ALIAS) {
            if exclude_type_only_meanings
                && self
                    .get_type_only_alias_declaration(symbol, &mut events)?
                    .is_some()
            {
                break;
            }

            let resolution =
                CanonicalAliasResolver::new(self.store, self.host).resolve_alias(symbol)?;
            events.extend(resolution.events);
            let target = match resolution.target {
                AliasTargetState::Resolved(target) => target,
                AliasTargetState::Unknown => {
                    return Ok(CanonicalSymbolFlagsResolution {
                        flags: SymbolFlags::ALL,
                        events,
                    });
                }
                AliasTargetState::Unresolved => {
                    return Err(CanonicalSymbolFlagsError::UnresolvedAliasTarget(symbol));
                }
            };
            let target = self.get_export_symbol_of_value_symbol_if_exported(target)?;
            let target_flags = self.symbol_flags(target)?;

            if target_flags.intersects(SymbolFlags::ALIAS) {
                if target == symbol
                    || seen_symbols
                        .as_ref()
                        .is_some_and(|seen| seen.contains(&target))
                {
                    break;
                }
                if let Some(seen) = &mut seen_symbols {
                    seen.insert(target);
                } else {
                    seen_symbols = Some(HashSet::from([symbol, target]));
                }
            }

            flags |= target_flags;
            symbol = target;
            symbol_flags = target_flags;
        }

        Ok(CanonicalSymbolFlagsResolution { flags, events })
    }

    fn get_type_only_alias_declaration(
        &mut self,
        symbol: SemanticSymbolId,
        events: &mut Vec<CanonicalAliasResolutionEvent>,
    ) -> Result<Option<ts_ast::NodeRef>, CanonicalSymbolFlagsError> {
        let resolution =
            CanonicalAliasResolver::new(self.store, self.host).resolve_alias(symbol)?;
        events.extend(resolution.events);
        self.store
            .alias_symbol_links(symbol)
            .map(|links| links.type_only_declaration)
            .ok_or(CanonicalSymbolFlagsError::InvalidAliasLinks(symbol))
    }

    fn get_export_symbol_of_value_symbol_if_exported(
        &self,
        symbol: SemanticSymbolId,
    ) -> Result<SemanticSymbolId, CanonicalSymbolFlagsError> {
        let record = self
            .store
            .symbol(symbol)
            .ok_or(CanonicalSymbolFlagsError::InvalidSymbol(symbol))?;
        let routed = if record.flags().intersects(SymbolFlags::EXPORT_VALUE) {
            if let Some(export_symbol) = record.export_symbol() {
                if self.store.symbol(export_symbol).is_none() {
                    return Err(CanonicalSymbolFlagsError::InvalidExportSymbol {
                        value_symbol: symbol,
                        export_symbol,
                    });
                }
                export_symbol
            } else {
                symbol
            }
        } else {
            symbol
        };
        self.store
            .get_merged_symbol(routed)
            .ok_or(CanonicalSymbolFlagsError::InvalidMergedSymbol(routed))
    }

    fn symbol_flags(
        &self,
        symbol: SemanticSymbolId,
    ) -> Result<SymbolFlags, CanonicalSymbolFlagsError> {
        self.store
            .symbol(symbol)
            .map(ts_binder::semantic::Symbol::flags)
            .ok_or(CanonicalSymbolFlagsError::InvalidSymbol(symbol))
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use ts_ast::{FileId, NodeRef};
    use ts_binder::{EscapedName, SymbolData};
    use ts_parser::parse_source_file;

    use super::*;
    use crate::semantic::{
        AliasSymbolLinks,
        alias::{CanonicalAliasTargetUnavailable, CanonicalImmediateAliasTarget},
    };

    type TestStore = CanonicalSemanticStore<()>;

    #[derive(Clone, Copy)]
    enum SyntheticTarget {
        Available(CanonicalImmediateAliasTarget),
        Unavailable(CanonicalAliasTargetUnavailable),
    }

    #[derive(Default)]
    struct SyntheticHost {
        targets: HashMap<SemanticSymbolId, SyntheticTarget>,
        markers: HashMap<SemanticSymbolId, NodeRef>,
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

        fn publish_marker(&mut self, alias: SemanticSymbolId, marker: NodeRef) {
            self.markers.insert(alias, marker);
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
            if let Some(marker) = self.markers.get(&alias).copied() {
                let mut links = store
                    .alias_symbol_links(alias)
                    .cloned()
                    .expect("resolver prepares alias links before target discovery");
                links.type_only_declaration = Some(marker);
                assert!(store.set_alias_symbol_links(alias, links));
            }
            match self
                .targets
                .get(&alias)
                .copied()
                .unwrap_or(SyntheticTarget::Unavailable(
                    CanonicalAliasTargetUnavailable::TargetProviderUnavailable,
                )) {
                SyntheticTarget::Available(target) => Ok(target),
                SyntheticTarget::Unavailable(reason) => Err(reason),
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

    fn marker(store: &mut TestStore, file: u32) -> NodeRef {
        let parsed = parse_source_file("export {};");
        let file = FileId::new(file);
        assert!(
            store
                .register_source_file(&parsed.arena, parsed.source_file, file)
                .is_some()
        );
        NodeRef::new(parsed.arena.id(), file, parsed.source_file)
    }

    fn set_type_only_marker(store: &mut TestStore, alias: SemanticSymbolId, marker: NodeRef) {
        assert!(store.ensure_alias_symbol_links(alias));
        assert!(store.set_alias_symbol_links(
            alias,
            AliasSymbolLinks {
                type_only_declaration: Some(marker),
                ..AliasSymbolLinks::default()
            }
        ));
    }

    fn set_export_symbol(store: &mut TestStore, value: SemanticSymbolId, export: SemanticSymbolId) {
        let record = store.symbol(value).unwrap();
        let (members, exports, parent) = (record.members(), record.exports(), record.parent());
        assert!(store.set_symbol_relationships(value, members, exports, parent, Some(export)));
    }

    #[test]
    fn local_meanings_are_returned_or_excluded_without_alias_work() {
        let mut store = TestStore::default();
        let local = symbol(
            &mut store,
            "local",
            SymbolFlags::CLASS | SymbolFlags::VALUE_MODULE,
        );
        let mut host = SyntheticHost::default();

        let included = CanonicalSymbolFlagsResolver::new(&mut store, &mut host)
            .get_symbol_flags(local)
            .unwrap();
        assert_eq!(
            included,
            CanonicalSymbolFlagsResolution {
                flags: SymbolFlags::CLASS | SymbolFlags::VALUE_MODULE,
                events: Vec::new(),
            }
        );

        let excluded = CanonicalSymbolFlagsResolver::new(&mut store, &mut host)
            .get_symbol_flags_ex(local, true, true)
            .unwrap();
        assert_eq!(excluded.flags, SymbolFlags::NONE);
        assert!(excluded.events.is_empty());
        assert!(host.calls.is_empty());
    }

    #[test]
    fn pure_alias_chain_resolves_transitively_and_reuses_cache() {
        let mut store = TestStore::default();
        let outer = alias(&mut store, "outer");
        let inner = alias(&mut store, "inner");
        let target = symbol(
            &mut store,
            "target",
            SymbolFlags::CLASS | SymbolFlags::FUNCTION,
        );
        let mut host = SyntheticHost::default();
        host.insert(outer, CanonicalImmediateAliasTarget::Resolved(inner));
        host.insert(inner, CanonicalImmediateAliasTarget::Resolved(target));

        let first = CanonicalSymbolFlagsResolver::new(&mut store, &mut host)
            .get_symbol_flags(outer)
            .unwrap();
        assert_eq!(
            first.flags,
            SymbolFlags::ALIAS | SymbolFlags::CLASS | SymbolFlags::FUNCTION
        );
        assert!(first.events.is_empty());

        let second = CanonicalSymbolFlagsResolver::new(&mut store, &mut host)
            .get_symbol_flags(outer)
            .unwrap();
        assert_eq!(second, first);
        assert_eq!(host.calls(outer), 1);
        assert_eq!(host.calls(inner), 1);
    }

    #[test]
    fn alias_merged_with_type_meaning_continues_to_later_value_target() {
        let mut store = TestStore::default();
        let outer = alias(&mut store, "outer");
        let merged_alias = symbol(
            &mut store,
            "merged",
            SymbolFlags::ALIAS | SymbolFlags::TYPE_ALIAS,
        );
        let value = symbol(&mut store, "value", SymbolFlags::PROPERTY);
        let mut host = SyntheticHost::default();
        host.insert(outer, CanonicalImmediateAliasTarget::Resolved(merged_alias));
        host.insert(merged_alias, CanonicalImmediateAliasTarget::Resolved(value));

        let resolution = CanonicalSymbolFlagsResolver::new(&mut store, &mut host)
            .get_symbol_flags(outer)
            .unwrap();
        assert_eq!(
            resolution.flags,
            SymbolFlags::ALIAS | SymbolFlags::TYPE_ALIAS | SymbolFlags::PROPERTY
        );
        assert_eq!(host.calls(outer), 1);
        assert_eq!(host.calls(merged_alias), 1);
    }

    #[test]
    fn exported_value_routes_to_export_symbol_then_one_merged_redirect() {
        let mut store = TestStore::default();
        let outer = alias(&mut store, "outer");
        let raw_value = symbol(
            &mut store,
            "raw",
            SymbolFlags::PROPERTY | SymbolFlags::EXPORT_VALUE,
        );
        let export = symbol(&mut store, "export", SymbolFlags::CLASS);
        let merged = symbol(&mut store, "merged", SymbolFlags::INTERFACE);
        let second_redirect = symbol(&mut store, "second", SymbolFlags::TYPE_ALIAS);
        set_export_symbol(&mut store, raw_value, export);
        assert_eq!(store.record_merged_symbol(merged, export), Ok(None));
        assert_eq!(
            store.record_merged_symbol(second_redirect, merged),
            Ok(None)
        );
        let mut host = SyntheticHost::default();
        host.insert(outer, CanonicalImmediateAliasTarget::Resolved(raw_value));

        let resolution = CanonicalSymbolFlagsResolver::new(&mut store, &mut host)
            .get_symbol_flags(outer)
            .unwrap();
        assert_eq!(
            resolution.flags,
            SymbolFlags::ALIAS | SymbolFlags::INTERFACE
        );
        assert!(!resolution.flags.intersects(SymbolFlags::PROPERTY));
        assert!(!resolution.flags.intersects(SymbolFlags::CLASS));
        assert!(!resolution.flags.intersects(SymbolFlags::TYPE_ALIAS));
    }

    #[test]
    fn export_value_without_export_symbol_merges_the_original_symbol() {
        let mut store = TestStore::default();
        let outer = alias(&mut store, "outer");
        let raw_value = symbol(
            &mut store,
            "raw",
            SymbolFlags::PROPERTY | SymbolFlags::EXPORT_VALUE,
        );
        let merged = symbol(&mut store, "merged", SymbolFlags::INTERFACE);
        assert_eq!(store.record_merged_symbol(merged, raw_value), Ok(None));
        let mut host = SyntheticHost::default();
        host.insert(outer, CanonicalImmediateAliasTarget::Resolved(raw_value));

        let resolution = CanonicalSymbolFlagsResolver::new(&mut store, &mut host)
            .get_symbol_flags(outer)
            .unwrap();
        assert_eq!(
            resolution.flags,
            SymbolFlags::ALIAS | SymbolFlags::INTERFACE
        );
    }

    #[test]
    fn unknown_target_returns_all_meanings() {
        let mut store = TestStore::default();
        let missing = alias(&mut store, "missing");
        let mut host = SyntheticHost::default();
        host.insert(missing, CanonicalImmediateAliasTarget::Missing);

        let first = CanonicalSymbolFlagsResolver::new(&mut store, &mut host)
            .get_symbol_flags_ex(missing, false, true)
            .unwrap();
        assert_eq!(first.flags, SymbolFlags::ALL);
        assert!(first.events.is_empty());

        let cached = CanonicalSymbolFlagsResolver::new(&mut store, &mut host)
            .get_symbol_flags(missing)
            .unwrap();
        assert_eq!(cached.flags, SymbolFlags::ALL);
        assert!(cached.events.is_empty());
        assert_eq!(host.calls(missing), 1);
    }

    #[test]
    fn direct_type_only_marker_is_checked_after_resolution() {
        let mut store = TestStore::default();
        let type_only = alias(&mut store, "typeOnly");
        let value = symbol(&mut store, "value", SymbolFlags::PROPERTY);
        let marker = marker(&mut store, 1);
        set_type_only_marker(&mut store, type_only, marker);
        let mut host = SyntheticHost::default();
        host.insert(type_only, CanonicalImmediateAliasTarget::Resolved(value));

        let excluded = CanonicalSymbolFlagsResolver::new(&mut store, &mut host)
            .get_symbol_flags_ex(type_only, true, false)
            .unwrap();
        assert_eq!(excluded.flags, SymbolFlags::ALIAS);
        assert_eq!(host.calls(type_only), 1, "marker lookup resolves first");
        assert_eq!(
            store.alias_symbol_links(type_only).unwrap().alias_target,
            AliasTargetState::Resolved(value)
        );

        let included = CanonicalSymbolFlagsResolver::new(&mut store, &mut host)
            .get_symbol_flags(type_only)
            .unwrap();
        assert_eq!(included.flags, SymbolFlags::ALIAS | SymbolFlags::PROPERTY);
        assert_eq!(host.calls(type_only), 1);
    }

    #[test]
    fn transitive_type_only_marker_is_propagated_before_exclusion() {
        let mut store = TestStore::default();
        let outer = alias(&mut store, "outer");
        let inner = alias(&mut store, "inner");
        let value = symbol(&mut store, "value", SymbolFlags::PROPERTY);
        let marker = marker(&mut store, 2);
        set_type_only_marker(&mut store, inner, marker);
        let mut host = SyntheticHost::default();
        host.insert(outer, CanonicalImmediateAliasTarget::Resolved(inner));
        host.insert(inner, CanonicalImmediateAliasTarget::Resolved(value));

        let excluded = CanonicalSymbolFlagsResolver::new(&mut store, &mut host)
            .get_symbol_flags_ex(outer, true, false)
            .unwrap();
        assert_eq!(excluded.flags, SymbolFlags::ALIAS);
        assert_eq!(
            store
                .alias_symbol_links(outer)
                .unwrap()
                .type_only_declaration,
            Some(marker)
        );
        assert_eq!(host.calls(outer), 1);
        assert_eq!(host.calls(inner), 1);
    }

    #[test]
    fn provider_published_type_only_marker_is_observed_in_same_query() {
        let mut store = TestStore::default();
        let type_only = alias(&mut store, "typeOnly");
        let value = symbol(&mut store, "value", SymbolFlags::PROPERTY);
        let marker = marker(&mut store, 3);
        let mut host = SyntheticHost::default();
        host.insert(type_only, CanonicalImmediateAliasTarget::Resolved(value));
        host.publish_marker(type_only, marker);

        let excluded = CanonicalSymbolFlagsResolver::new(&mut store, &mut host)
            .get_symbol_flags_ex(type_only, true, true)
            .unwrap();
        assert_eq!(excluded.flags, SymbolFlags::NONE);
        assert_eq!(
            store
                .alias_symbol_links(type_only)
                .unwrap()
                .type_only_declaration,
            Some(marker)
        );
        assert_eq!(host.calls(type_only), 1);
    }

    #[test]
    fn type_only_merged_alias_keeps_its_local_meaning_then_stops() {
        let mut store = TestStore::default();
        let outer = alias(&mut store, "outer");
        let merged_alias = symbol(
            &mut store,
            "merged",
            SymbolFlags::ALIAS | SymbolFlags::TYPE_ALIAS,
        );
        let value = symbol(&mut store, "value", SymbolFlags::PROPERTY);
        let marker = marker(&mut store, 4);
        set_type_only_marker(&mut store, merged_alias, marker);
        let mut host = SyntheticHost::default();
        host.insert(outer, CanonicalImmediateAliasTarget::Resolved(merged_alias));
        host.insert(merged_alias, CanonicalImmediateAliasTarget::Resolved(value));

        let excluded = CanonicalSymbolFlagsResolver::new(&mut store, &mut host)
            .get_symbol_flags_ex(outer, true, false)
            .unwrap();
        assert_eq!(excluded.flags, SymbolFlags::ALIAS | SymbolFlags::TYPE_ALIAS);
        assert!(!excluded.flags.intersects(SymbolFlags::PROPERTY));
        assert_eq!(host.calls(outer), 1);
        assert_eq!(host.calls(merged_alias), 1);
    }

    #[test]
    fn self_alias_loop_breaks_before_adding_target_flags() {
        let mut store = TestStore::default();
        let recursive = symbol(
            &mut store,
            "recursive",
            SymbolFlags::ALIAS | SymbolFlags::TYPE_ALIAS,
        );
        let mut host = SyntheticHost::default();
        host.insert(
            recursive,
            CanonicalImmediateAliasTarget::Resolved(recursive),
        );

        let excluded = CanonicalSymbolFlagsResolver::new(&mut store, &mut host)
            .get_symbol_flags_ex(recursive, false, true)
            .unwrap();
        assert_eq!(excluded.flags, SymbolFlags::NONE);

        let included = CanonicalSymbolFlagsResolver::new(&mut store, &mut host)
            .get_symbol_flags(recursive)
            .unwrap();
        assert_eq!(included.flags, SymbolFlags::ALIAS | SymbolFlags::TYPE_ALIAS);
        assert_eq!(host.calls(recursive), 1);
    }

    #[test]
    fn mutual_local_alias_loop_uses_exact_seen_ordering() {
        let mut store = TestStore::default();
        let first = symbol(
            &mut store,
            "first",
            SymbolFlags::ALIAS | SymbolFlags::TYPE_ALIAS,
        );
        let second = symbol(
            &mut store,
            "second",
            SymbolFlags::ALIAS | SymbolFlags::VALUE_MODULE,
        );
        let mut host = SyntheticHost::default();
        host.insert(first, CanonicalImmediateAliasTarget::Resolved(second));
        host.insert(second, CanonicalImmediateAliasTarget::Resolved(first));

        let excluded = CanonicalSymbolFlagsResolver::new(&mut store, &mut host)
            .get_symbol_flags_ex(first, false, true)
            .unwrap();
        assert_eq!(
            excluded.flags,
            SymbolFlags::ALIAS | SymbolFlags::VALUE_MODULE,
            "the seen root breaks before its flags are re-added"
        );

        let included = CanonicalSymbolFlagsResolver::new(&mut store, &mut host)
            .get_symbol_flags(first)
            .unwrap();
        assert_eq!(
            included.flags,
            SymbolFlags::ALIAS | SymbolFlags::TYPE_ALIAS | SymbolFlags::VALUE_MODULE
        );
        assert_eq!(host.calls(first), 1);
        assert_eq!(host.calls(second), 1);
    }

    #[test]
    fn longer_seen_loop_breaks_before_repeated_target_accumulation() {
        let mut store = TestStore::default();
        let first = symbol(
            &mut store,
            "first",
            SymbolFlags::ALIAS | SymbolFlags::TYPE_ALIAS,
        );
        let second = symbol(
            &mut store,
            "second",
            SymbolFlags::ALIAS | SymbolFlags::VALUE_MODULE,
        );
        let third = symbol(
            &mut store,
            "third",
            SymbolFlags::ALIAS | SymbolFlags::INTERFACE,
        );
        let mut host = SyntheticHost::default();
        host.insert(first, CanonicalImmediateAliasTarget::Resolved(second));
        host.insert(second, CanonicalImmediateAliasTarget::Resolved(third));
        host.insert(third, CanonicalImmediateAliasTarget::Resolved(second));

        let resolution = CanonicalSymbolFlagsResolver::new(&mut store, &mut host)
            .get_symbol_flags_ex(first, false, true)
            .unwrap();
        assert_eq!(
            resolution.flags,
            SymbolFlags::ALIAS | SymbolFlags::VALUE_MODULE | SymbolFlags::INTERFACE
        );
        assert_eq!(host.calls(first), 1);
        assert_eq!(host.calls(second), 1);
        assert_eq!(host.calls(third), 1);
    }

    #[test]
    fn pure_cycle_returns_all_and_only_first_query_reports_events() {
        let mut store = TestStore::default();
        let first = alias(&mut store, "first");
        let second = alias(&mut store, "second");
        let mut host = SyntheticHost::default();
        host.insert(first, CanonicalImmediateAliasTarget::Resolved(second));
        host.insert(second, CanonicalImmediateAliasTarget::Resolved(first));

        let initial = CanonicalSymbolFlagsResolver::new(&mut store, &mut host)
            .get_symbol_flags_ex(first, true, false)
            .unwrap();
        assert_eq!(initial.flags, SymbolFlags::ALL);
        assert_eq!(
            initial.events,
            [
                CanonicalAliasResolutionEvent::CircularDefinitionOfImportAlias { alias: second },
                CanonicalAliasResolutionEvent::CircularDefinitionOfImportAlias { alias: first },
            ]
        );

        let cached = CanonicalSymbolFlagsResolver::new(&mut store, &mut host)
            .get_symbol_flags_ex(first, true, true)
            .unwrap();
        assert_eq!(cached.flags, SymbolFlags::ALL);
        assert!(cached.events.is_empty());
        assert_eq!(host.calls(first), 1);
        assert_eq!(host.calls(second), 1);
    }

    #[test]
    fn provider_failure_is_typed_and_leaves_target_and_stack_retryable() {
        let mut store = TestStore::default();
        let failing = alias(&mut store, "failing");
        assert!(store.ensure_alias_symbol_links(failing));
        let before = store.alias_symbol_links(failing).unwrap().clone();
        let mut host = SyntheticHost::default();
        host.unavailable(
            failing,
            CanonicalAliasTargetUnavailable::TargetProviderUnavailable,
        );

        let expected = CanonicalSymbolFlagsError::AliasResolution(
            CanonicalAliasResolutionError::TargetUnavailable {
                alias: failing,
                reason: CanonicalAliasTargetUnavailable::TargetProviderUnavailable,
            },
        );
        assert_eq!(
            CanonicalSymbolFlagsResolver::new(&mut store, &mut host).get_symbol_flags(failing),
            Err(expected)
        );
        assert_eq!(store.alias_symbol_links(failing), Some(&before));
        assert!(store.type_resolution_is_empty());

        assert_eq!(
            CanonicalSymbolFlagsResolver::new(&mut store, &mut host).get_symbol_flags(failing),
            Err(expected)
        );
        assert_eq!(host.calls(failing), 2);
    }

    #[test]
    fn foreign_symbols_and_targets_fail_without_publishing_local_state() {
        let mut store = TestStore::default();
        let local_alias = alias(&mut store, "local");
        assert!(store.ensure_alias_symbol_links(local_alias));
        let before_links = store.alias_symbol_links(local_alias).unwrap().clone();
        let before_counts = store.checker_link_allocated_lengths();

        let mut foreign_store = TestStore::default();
        let foreign_alias = alias(&mut foreign_store, "foreignAlias");
        let foreign_target = symbol(&mut foreign_store, "foreignTarget", SymbolFlags::CLASS);
        let mut host = SyntheticHost::default();
        host.insert(
            local_alias,
            CanonicalImmediateAliasTarget::Resolved(foreign_target),
        );

        assert_eq!(
            CanonicalSymbolFlagsResolver::new(&mut store, &mut host)
                .get_symbol_flags(foreign_alias),
            Err(CanonicalSymbolFlagsError::InvalidSymbol(foreign_alias))
        );
        assert_eq!(host.calls(local_alias), 0);
        assert_eq!(store.checker_link_allocated_lengths(), before_counts);

        assert_eq!(
            CanonicalSymbolFlagsResolver::new(&mut store, &mut host).get_symbol_flags(local_alias),
            Err(CanonicalSymbolFlagsError::AliasResolution(
                CanonicalAliasResolutionError::InvalidTarget {
                    alias: local_alias,
                    target: foreign_target,
                }
            ))
        );
        assert_eq!(store.alias_symbol_links(local_alias), Some(&before_links));
        assert!(store.type_resolution_is_empty());
        assert_eq!(host.calls(local_alias), 1);
    }

    #[test]
    fn symbol_store_rejects_foreign_export_relationship_atomically() {
        let mut store = TestStore::default();
        let outer = alias(&mut store, "outer");
        let raw_value = symbol(
            &mut store,
            "raw",
            SymbolFlags::PROPERTY | SymbolFlags::EXPORT_VALUE,
        );
        let valid_export = symbol(&mut store, "validExport", SymbolFlags::CLASS);
        set_export_symbol(&mut store, raw_value, valid_export);

        let mut foreign_store = TestStore::default();
        let foreign_export = symbol(&mut foreign_store, "foreign", SymbolFlags::INTERFACE);
        let record = store.symbol(raw_value).unwrap();
        assert!(!store.set_symbol_relationships(
            raw_value,
            record.members(),
            record.exports(),
            record.parent(),
            Some(foreign_export),
        ));
        assert_eq!(
            store.symbol(raw_value).unwrap().export_symbol(),
            Some(valid_export)
        );

        let mut host = SyntheticHost::default();
        host.insert(outer, CanonicalImmediateAliasTarget::Resolved(raw_value));
        let resolution = CanonicalSymbolFlagsResolver::new(&mut store, &mut host)
            .get_symbol_flags(outer)
            .unwrap();
        assert_eq!(resolution.flags, SymbolFlags::ALIAS | SymbolFlags::CLASS);
    }
}
