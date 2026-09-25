//! Port of Go `nodebuilder/types.go`: the node builder flags and the
//! `SymbolTracker` interface. Also holds the Go `collections.CopyOnWriteMap`
//! and `CopyOnWriteSet` types that `NodeBuilderContext` uses.

use crate::prelude::*;
use crate::flags_macros::go_flags;

// Go: nodebuilder/types.go:9 SymbolTracker
// TODO: previously all symboltracker methods were optional, but now they're required.
// PORT: Go passes the interface by value. Here a tracker is shared as
// `Rc<dyn SymbolTracker>`, so the methods take `&self` and an implementation
// that keeps state uses interior mutability. Every method also takes the
// checker, because Go trackers reach the checker through their own pointers
// and here the caller already holds it. Callers must not hold a borrow of
// the node builder or its context while they call a tracker, because
// `SymbolTrackerImpl` writes to that context.
pub trait SymbolTracker {
    fn track_symbol(&self, c: &mut Checker, symbol: SymbolId, enclosing_declaration: Node, meaning: SymbolFlags) -> bool;
    fn report_inaccessible_this_error(&self, c: &mut Checker);
    fn report_private_in_base_of_class_expression(&self, c: &mut Checker, property_name: &str);
    fn report_inaccessible_unique_symbol_error(&self, c: &mut Checker);
    fn report_cyclic_structure_error(&self, c: &mut Checker);
    fn report_likely_unsafe_import_required_error(&self, c: &mut Checker, specifier: &str, symbol_name: &str);
    fn report_truncation_error(&self, c: &mut Checker);
    fn report_nonlocal_augmentation(&self, c: &mut Checker, containing_file: Node, parent_symbol: SymbolId, augmenting_symbol: SymbolId);
    fn report_non_serializable_property(&self, c: &mut Checker, property_name: &str);

    fn report_inference_fallback(&self, c: &mut Checker, node: Node);
    fn push_error_fallback_node(&self, c: &mut Checker, node: Node);
    fn pop_error_fallback_node(&self, c: &mut Checker);

    /// Go type assertion `tracker.(*SymbolTrackerImpl)`.
    // PORT: Rust has no downcast on this trait object, so the one Go type
    // assertion is a method. Only `SymbolTrackerImpl` overrides it.
    fn as_symbol_tracker_impl(&self) -> Option<&SymbolTrackerImpl> {
        None
    }
}

// Go: nodebuilder/types.go:26 Flags
// NOTE: If modifying this enum, must modify `TypeFormatFlags` too!
go_flags!(NodeBuilderFlags, u32 {
    NONE = 0;
    // Options
    NO_TRUNCATION = 1 << 0;
    WRITE_ARRAY_AS_GENERIC_TYPE = 1 << 1;
    GENERATE_NAMES_FOR_SHADOWED_TYPE_PARAMS = 1 << 2;
    USE_STRUCTURAL_FALLBACK = 1 << 3;
    FORBID_INDEXED_ACCESS_SYMBOL_REFERENCES = 1 << 4;
    WRITE_TYPE_ARGUMENTS_OF_SIGNATURE = 1 << 5;
    USE_FULLY_QUALIFIED_TYPE = 1 << 6;
    USE_ONLY_EXTERNAL_ALIASING = 1 << 7;
    SUPPRESS_ANY_RETURN_TYPE = 1 << 8;
    WRITE_TYPE_PARAMETERS_IN_QUALIFIED_NAME = 1 << 9;
    MULTILINE_OBJECT_LITERALS = 1 << 10;
    WRITE_CLASS_EXPRESSION_AS_TYPE_LITERAL = 1 << 11;
    USE_TYPE_OF_FUNCTION = 1 << 12;
    OMIT_PARAMETER_MODIFIERS = 1 << 13;
    USE_ALIAS_DEFINED_OUTSIDE_CURRENT_SCOPE = 1 << 14;
    USE_SINGLE_QUOTES_FOR_STRING_LITERAL_TYPE = 1 << 28;
    NO_TYPE_REDUCTION = 1 << 29;
    USE_INSTANTIATION_EXPRESSIONS = 1 << 30;
    OMIT_THIS_PARAMETER = 1 << 25;
    WRITE_CALL_STYLE_SIGNATURE = 1 << 27;
    // Error handling
    ALLOW_THIS_IN_OBJECT_LITERAL = 1 << 15;
    ALLOW_QUALIFIED_NAME_IN_PLACE_OF_IDENTIFIER = 1 << 16;
    ALLOW_ANONYMOUS_IDENTIFIER = 1 << 17;
    ALLOW_EMPTY_UNION_OR_INTERSECTION = 1 << 18;
    ALLOW_EMPTY_TUPLE = 1 << 19;
    ALLOW_UNIQUE_ES_SYMBOL_TYPE = 1 << 20;
    ALLOW_EMPTY_INDEX_INFO_TYPE = 1 << 21;
    // Errors (cont.)
    ALLOW_NODE_MODULES_RELATIVE_PATHS = 1 << 26;
    IGNORE_ERRORS = (1 << 15) | (1 << 16) | (1 << 17) | (1 << 18) | (1 << 19) | (1 << 21) | (1 << 26);
    // State
    IN_OBJECT_TYPE_LITERAL = 1 << 22;
    IN_TYPE_ALIAS = 1 << 23;
    IN_INITIAL_ENTITY_NAME = 1 << 24;
});

// Go: nodebuilder/types.go:70 InternalFlags
go_flags!(InternalNodeBuilderFlags, i32 {
    NONE = 0;
    WRITE_COMPUTED_PROPS = 1 << 0;
    NO_SYNTACTIC_PRINTER = 1 << 1;
    DO_NOT_INCLUDE_SYMBOL_CHAIN = 1 << 2;
    ALLOW_UNRESOLVED_NAMES = 1 << 3;
});

/// Go `collections.CopyOnWriteMap[K, V]`: a map that shares its backing
/// storage with the parent scope until the first write.
// PORT: Go keeps an `owned` flag and clones with `maps.Clone`. Here the
// storage is an `Rc` and `Rc::make_mut` clones it when a saved scope still
// shares it. The observable behavior is the same.
#[derive(Clone, Debug)]
pub struct CopyOnWriteMap<K: std::hash::Hash + Eq + Clone, V: Clone> {
    m: Rc<FxHashMap<K, V>>,
}

impl<K: std::hash::Hash + Eq + Clone, V: Clone> Default for CopyOnWriteMap<K, V> {
    fn default() -> Self {
        Self { m: Rc::new(FxHashMap::default()) }
    }
}

impl<K: std::hash::Hash + Eq + Clone, V: Clone> CopyOnWriteMap<K, V> {
    // Go: collections/cow.go:16 CopyOnWriteMap.Get
    pub fn get(&self, k: &K) -> Option<&V> {
        self.m.get(k)
    }

    // Go: collections/cow.go:22 CopyOnWriteMap.Has
    pub fn has(&self, k: &K) -> bool {
        self.m.contains_key(k)
    }

    // Go: collections/cow.go:28 CopyOnWriteMap.Set
    pub fn set(&mut self, k: K, v: V) {
        Rc::make_mut(&mut self.m).insert(k, v);
    }

    // Go: collections/cow.go:49 CopyOnWriteMap.EnterScope
    // PORT: Go returns a restore closure over the map pointer. The map lives
    // inside a `RefCell` context here, so this returns the saved state and the
    // caller restores it with `restore_scope`.
    #[must_use]
    pub fn enter_scope(&self) -> Self {
        self.clone()
    }

    /// Restores the state that `enter_scope` returned.
    pub fn restore_scope(&mut self, saved: Self) {
        *self = saved;
    }
}

/// Go `collections.CopyOnWriteSet[K]`.
#[derive(Clone, Debug)]
pub struct CopyOnWriteSet<K: std::hash::Hash + Eq + Clone> {
    m: CopyOnWriteMap<K, ()>,
}

impl<K: std::hash::Hash + Eq + Clone> Default for CopyOnWriteSet<K> {
    fn default() -> Self {
        Self { m: CopyOnWriteMap::default() }
    }
}

impl<K: std::hash::Hash + Eq + Clone> CopyOnWriteSet<K> {
    // Go: collections/cow.go:60 CopyOnWriteSet.Has
    pub fn has(&self, k: &K) -> bool {
        self.m.get(k).is_some()
    }

    // Go: collections/cow.go:66 CopyOnWriteSet.Add
    pub fn add(&mut self, k: K) {
        self.m.set(k, ());
    }

    // Go: collections/cow.go:74 CopyOnWriteSet.EnterScope
    // PORT: see `CopyOnWriteMap::enter_scope`.
    #[must_use]
    pub fn enter_scope(&self) -> Self {
        self.clone()
    }

    /// Restores the state that `enter_scope` returned.
    pub fn restore_scope(&mut self, saved: Self) {
        *self = saved;
    }
}
