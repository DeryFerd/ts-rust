//! The binder reference resolver as a `TransformReferenceResolver`.
//!
//! PORT: Go `getScriptTransformers` builds
//! `binder.NewReferenceResolver(options, binder.ReferenceResolverHooks{})`
//! for isolated modules. With no hooks, Go reads only the binder's
//! `ast.Symbol` values, which every goroutine shares. Here the resolver reads
//! the program's binder symbols (`BinderSymbols`), so it needs no checker and
//! runs on any thread: on the file's checker thread, or on the program's emit
//! pool (`emitter::program_emit`).

use crate::prelude::*;

use super::transformer::TransformReferenceResolver;
use crate::binder::reference_resolver::{
    ReferenceResolver, ReferenceResolverHooks, new_reference_resolver,
};

/// The program's binder symbols as a `NameResolverHost` (Go reads binder
/// symbols through their pointers). The name resolver only reads them,
/// except for the transient `arguments` symbol it makes (Go makes a
/// free-standing symbol). The first such write makes a copy-on-write copy of
/// the arena, which costs one `Arc` clone per chunk; reads before the copy
/// read the program arena, which the copy equals.
///
/// It has no checker: `hook_checker` panics. The resolver that uses it has
/// no hooks, so it never asks.
pub struct BinderSymbols {
    bound: &'static SymbolArena,
    copy: Option<SymbolArena>,
}

impl BinderSymbols {
    /// The binder symbols of the current program, which must be bound.
    #[must_use]
    pub fn of_program() -> Self {
        BinderSymbols {
            bound: prog().bound_symbols.get().expect("program is not bound"),
            copy: None,
        }
    }
}

impl NameResolverHost for BinderSymbols {
    fn symbol_arena(&self) -> &SymbolArena {
        self.copy.as_ref().unwrap_or(self.bound)
    }

    fn symbol_arena_mut(&mut self) -> &mut SymbolArena {
        let bound = self.bound;
        // `for_checker`: the symbols the copy adds get ids of their own
        // (`ast::get_symbol_id`), as a checker's do.
        self.copy.get_or_insert_with(|| bound.for_checker())
    }

    fn hook_checker(&mut self) -> &mut Checker {
        panic!("the binder reference resolver has no checker");
    }
}

/// Go `binder.NewReferenceResolver(options, hooks)` as a transform resolver.
pub struct BinderReferenceResolver {
    resolver: RefCell<ReferenceResolver>,
    /// The symbols the resolver reads, for one file's transforms.
    symbols: RefCell<BinderSymbols>,
}

// Go: binder/referenceresolver.go:37 NewReferenceResolver
// PORT: Go `getScriptTransformers` passes empty hooks, so this takes none.
// A hook would need the checker, which `BinderSymbols` does not have.
#[must_use]
pub fn new_binder_reference_resolver(options: &'static CompilerOptions) -> BinderReferenceResolver {
    BinderReferenceResolver {
        resolver: RefCell::new(new_reference_resolver(
            options,
            ReferenceResolverHooks::default(),
        )),
        symbols: RefCell::new(BinderSymbols::of_program()),
    }
}

impl TransformReferenceResolver for BinderReferenceResolver {
    fn get_referenced_export_container(&self, node: Node, prefix_locals: bool) -> Node {
        self.resolver.borrow_mut().get_referenced_export_container(
            &mut *self.symbols.borrow_mut(),
            node,
            prefix_locals,
        )
    }

    fn get_referenced_import_declaration(&self, node: Node) -> Node {
        self.resolver
            .borrow_mut()
            .get_referenced_import_declaration(&mut *self.symbols.borrow_mut(), node)
    }

    fn get_referenced_value_declaration(&self, node: Node) -> Node {
        self.resolver
            .borrow_mut()
            .get_referenced_value_declaration(&mut *self.symbols.borrow_mut(), node)
    }

    fn get_referenced_value_declarations(&self, node: Node) -> Vec<Node> {
        self.resolver
            .borrow_mut()
            .get_referenced_value_declarations(&mut *self.symbols.borrow_mut(), node)
    }

    fn get_element_access_expression_name(&self, expression: Node) -> String {
        self.resolver
            .borrow()
            .get_element_access_expression_name(&mut *self.symbols.borrow_mut(), expression)
    }

    fn get_referenced_member_value_declaration(&self, node: Node) -> Node {
        self.resolver
            .borrow()
            .get_referenced_member_value_declaration(&mut *self.symbols.borrow_mut(), node)
    }
}
