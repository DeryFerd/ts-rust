// Go: internal/typeparser/could_be_strict_effect.go

use crate::effect::typeparser::*;
use crate::prelude::*;
use std::sync::LazyLock;

/// strictEffectTypeNames are the type symbol names that StrictEffectType can
/// match. couldBeNamed takes a set so future prefilters for other wrapper
/// types (Stream, Layer, ...) can reuse the same conservative walk.
pub static STRICT_EFFECT_TYPE_NAMES: LazyLock<FxHashMap<&'static str, bool>> =
    LazyLock::new(|| FxHashMap::from_iter([("Effect", true)]));

impl TypeParser<'_> {
    /// NodeCouldBeStrictEffect reports whether node's flow type could possibly be
    /// a strict Effect type (a type whose symbol is named "Effect", see
    /// StrictEffectType). For reference nodes (identifiers and property accesses)
    /// it inspects the referenced symbol's declared type, which is cheap compared
    /// to the flow analysis performed by GetTypeAtLocation. Flow narrowing can
    /// only refine the declared type — select union constituents, narrow
    /// any/unknown, or intersect it — so a declared type that conclusively
    /// contains no possibly-Effect constituent can never produce a strict-Effect
    /// flow type.
    ///
    /// It returns true ("cannot rule out") for every other node kind and whenever
    /// the answer is not conclusively negative, so whole-file walker rules may use
    /// a false result to skip expensive GetTypeAtLocation queries without ever
    /// missing a strict Effect type.
    pub fn node_could_be_strict_effect(&mut self, node: Node) -> bool {
        if node.is_nil() {
            return true;
        }
        if node.kind() == SyntaxKind::CallExpression {
            return self.call_could_return_strict_effect(node);
        }
        if node.kind() != SyntaxKind::Identifier
            && node.kind() != SyntaxKind::PropertyAccessExpression
        {
            return true;
        }
        let sym = self.reference_symbol_at_node(node);
        if sym.is_nil() {
            return true;
        }
        self.symbol_could_be_strict_effect(sym)
    }

    /// callCouldReturnStrictEffect reports whether a call expression's type could
    /// possibly be a strict Effect type, based on the return type of its resolved
    /// signature. The signature and its return type are cached from the main check
    /// phase, so consulting them is cheap compared to re-checking the call via
    /// GetTypeAtLocation. A call expression's type is its resolved signature's
    /// return type (union-widened with undefined for optional chains, which the
    /// conservative union walk handles), so a conclusively non-Effect declared
    /// return type rules the node out.
    pub fn call_could_return_strict_effect(&mut self, node: Node) -> bool {
        let checker = &mut *self.checker;
        // Go: defer func() { if r := recover(); r != nil { result = true } }()
        let result = go_recover(|| {
            let signature = checker.get_resolved_signature_exported(node);
            if signature.is_nil() {
                return true;
            }
            let return_type = checker.get_return_type_of_signature_exported(signature);
            could_be_named(checker, return_type, &STRICT_EFFECT_TYPE_NAMES, 0)
        });
        result.unwrap_or(true)
    }

    /// SymbolCouldBeStrictEffect reports whether a reference to sym could possibly
    /// have a strict-Effect flow type, based on the symbol's declared type only.
    pub fn symbol_could_be_strict_effect(&mut self, sym: SymbolId) -> bool {
        if sym.is_nil() {
            return true;
        }
        let declared = self.get_type_of_symbol_safe(sym);
        self.could_be_strict_effect(declared)
    }

    /// getTypeOfSymbolSafe wraps Checker.GetTypeOfSymbol with a panic guard,
    /// returning nil (treated as inconclusive by callers) on any checker panic.
    pub fn get_type_of_symbol_safe(&mut self, sym: SymbolId) -> TypeId {
        let checker = &mut *self.checker;
        // Go: defer func() { if r := recover(); r != nil { result = nil } }()
        go_recover(|| checker.get_type_of_symbol_exported(sym)).unwrap_or(TypeId::NIL)
    }

    /// CouldBeStrictEffect reports whether flow narrowing starting from declared
    /// type t could ever produce a strict Effect type. It is deliberately
    /// conservative: it only returns false when t is conclusively non-Effect (a
    /// primitive/never type, or a plain object type with a non-nil symbol whose
    /// name is not "Effect"). Any/unknown, type variables, unions, intersections
    /// and symbol-less types all return true.
    pub fn could_be_strict_effect(&mut self, t: TypeId) -> bool {
        could_be_named(self.checker, t, &STRICT_EFFECT_TYPE_NAMES, 0)
    }
}

/// couldBeNamed reports whether flow narrowing starting from declared type t
/// could ever produce a type whose symbol name is in names. False only on a
/// conclusive negative.
pub fn could_be_named(c: &Checker, t: TypeId, names: &FxHashMap<&str, bool>, depth: i32) -> bool {
    if t.is_nil() {
        return true;
    }
    let flags = c.ty(t).flags();
    if flags.intersects(TypeFlags::ANY_OR_UNKNOWN) {
        return true;
    }
    if flags.intersects(TypeFlags::UNION_OR_INTERSECTION) {
        if depth > 4 {
            return true;
        }
        for &member in c.ty(t).types() {
            if could_be_named(c, member, names, depth + 1) {
                return true;
            }
        }
        return false;
    }
    // Type parameters, indexed accesses, conditionals, substitutions, etc.
    // can instantiate to anything.
    if flags.intersects(TypeFlags::INSTANTIABLE) {
        return true;
    }
    // Primitives and never can never narrow to an object type.
    if flags.intersects(TypeFlags::PRIMITIVE | TypeFlags::NEVER) {
        return false;
    }
    // Anything that is not a plain object type at this point is unexpected;
    // stay conservative.
    if !flags.intersects(TypeFlags::OBJECT) {
        return true;
    }
    let sym = c.ty(t).symbol;
    if sym.is_nil() {
        return true;
    }
    names
        .get(c.sym(sym).name.as_str())
        .copied()
        .unwrap_or(false)
}
