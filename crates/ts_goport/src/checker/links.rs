//! Port of `checker/links.go` (tsgo#4329).
//!
//! PORT: Go adds `core.PagedLinkStore` (pages of 256 values, a page list for
//! low page indexes and a map for high ones) and the two stores below on top
//! of it. `core::LinkStore` is paged the same way for every store: node keys
//! use per-file page tables of 64-key pages, arena keys (symbols) use one
//! page table, and a page holds the values. So both Go stores map onto
//! `core::LinkStore`; a store of large values holds `Box<V>`, like Go
//! `symbolArenaLinkStore`. `has` and `try_get` keep the exact "a record
//! exists" answer. Go
//! `nodeLinkStore.TryGet` also answers a zero record for a key in an
//! allocated page; its one reader (`tryGetResolvedSymbolFromTypeNode`) then
//! reads a nil `resolvedSymbol`, which is the same result as no record.

use crate::prelude::*;

// Go: checker/links.go:10 nodeLinkStore
/// A links store keyed by node references (Go stores the values in the pages).
pub type NodeLinkStore<V> = LinkStore<Node, V>;

// Go: checker/links.go:28 symbolArenaLinkStore
/// A links store keyed by symbol references (Go stores the values in an arena;
/// here they sit in the pages, as most keys of a page have a record).
/// Read it with `SymbolArenaLinks`, which gives the symbol its id as Go does.
pub type SymbolArenaLinkStore<V> = LinkStore<SymbolId, V>;

/// The reads of a `SymbolArenaLinkStore`. Go keys the store by
/// `ast.GetSymbolId`, so each `Get`, `TryGet` and `Has` gives the symbol its
/// id first. The ids count up in that order (`ast::get_symbol_id`), and a
/// late-bound name holds the id of its unique symbol (`__@k@<id>`, Go
/// `getESSymbolLikeTypeForNode`). The node builder counts the length of that
/// name toward truncation, so the ids must count as Go's do.
// PORT: the store is still keyed by the arena index; only the id order is Go's.
pub trait SymbolArenaLinks<V> {
    /// Go `symbolArenaLinkStore.Get`.
    fn get_by_id(&mut self, symbols: &SymbolArena, symbol: SymbolId) -> &mut V;
    /// Go `symbolArenaLinkStore.Get` followed by writes to the new record
    /// (`LinkStore::insert_new`).
    fn insert_new_by_id(&mut self, symbols: &SymbolArena, symbol: SymbolId, value: V) -> &mut V;
    /// Go `symbolArenaLinkStore.TryGet`.
    fn try_get_by_id(&self, symbols: &SymbolArena, symbol: SymbolId) -> Option<&V>;
    /// Go `symbolArenaLinkStore.Has`.
    fn has_by_id(&self, symbols: &SymbolArena, symbol: SymbolId) -> bool;
}

impl<V: Default> SymbolArenaLinks<V> for SymbolArenaLinkStore<V> {
    #[inline]
    fn get_by_id(&mut self, symbols: &SymbolArena, symbol: SymbolId) -> &mut V {
        get_symbol_id(symbols, symbol);
        self.get(symbol)
    }

    #[inline]
    fn insert_new_by_id(&mut self, symbols: &SymbolArena, symbol: SymbolId, value: V) -> &mut V {
        get_symbol_id(symbols, symbol);
        self.insert_new(symbol, value)
    }

    #[inline]
    fn try_get_by_id(&self, symbols: &SymbolArena, symbol: SymbolId) -> Option<&V> {
        get_symbol_id(symbols, symbol);
        self.try_get(symbol)
    }

    #[inline]
    fn has_by_id(&self, symbols: &SymbolArena, symbol: SymbolId) -> bool {
        get_symbol_id(symbols, symbol);
        self.has(symbol)
    }
}
