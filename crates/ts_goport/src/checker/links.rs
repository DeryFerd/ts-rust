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
pub type SymbolArenaLinkStore<V> = LinkStore<SymbolId, V>;
