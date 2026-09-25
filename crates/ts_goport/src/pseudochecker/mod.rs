//! Port of Go `internal/pseudochecker` (checker.go here, type.go in
//! `types.rs`, lookup.go in `lookup.rs`).
//!
//! pseudochecker is a limited "checker" that returns pseudo-"types" of
//! expressions - mostly those which trivially have type nodes.
//!
//! Callers use it the way Go code uses the package:
//! `pseudochecker::new_pseudo_type_union(...)`,
//! `pc.get_type_of_declaration(&self.symbols, node)`.

use crate::prelude::*;

mod lookup;
mod types;

pub use lookup::*;
pub use types::*;

// TODO: Late binding/symbol merging?
// In strada, `expressionToTypeNode` used many `resolver` methods whose net effect was just
// calling `Checker.GetMergedSymbol` on a symbol when dealing with accessors. Right now those
// just use Node.Symbol, which will fail to pair up late-bound symbols. In theory, this is actually
// fine, since ID can't possibly know if `set [q1()](a){}` and `get [q2()](): T {}` are connected
// without performing real type checking, regardless, so it shouldn't matter. If anything, it might be
// OK to add a "dumb" late binder that can merge multiple `[a.b.c]: T` together, but not anything else.
// This is an area of active ~~feature-creep~~ development in ID output, prerequisite refactoring would include
// extracting the `mergeSymbol` core checker logic into a reusable component.

/// Go `pseudochecker.PseudoChecker`.
// PORT: Go reads `node.Symbol.Declarations` through shared symbol pointers.
// Here symbols live in an arena, so each method that can reach a symbol read
// takes `symbols: &SymbolArena` (the checker's arena) as its first
// parameter. The struct holds only the two Go flags, so it is `Copy`.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct PseudoChecker {
    pub strict_null_checks: bool,
    pub exact_optional_property_types: bool,
}

// Go: pseudochecker/checker.go:19 NewPseudoChecker
pub fn new_pseudo_checker(strict_null_checks: bool, exact_optional_property_types: bool) -> PseudoChecker {
    PseudoChecker { strict_null_checks, exact_optional_property_types }
}
