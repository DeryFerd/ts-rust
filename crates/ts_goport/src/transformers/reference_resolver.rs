//! The binder reference resolver as a `TransformReferenceResolver`.
//!
//! PORT: Go `getScriptTransformers` builds
//! `binder.NewReferenceResolver(options, binder.ReferenceResolverHooks{})`
//! for isolated modules. The Rust binder resolver reads symbols through a
//! checker on each call, so this wrapper lends it the checker of the file
//! being emitted (emit runs on that checker's thread).

use crate::prelude::*;

use super::transformer::TransformReferenceResolver;
use crate::binder::reference_resolver::{
    ReferenceResolver, ReferenceResolverHooks, new_reference_resolver,
};

/// Go `binder.NewReferenceResolver(options, hooks)` as a transform resolver.
pub struct BinderReferenceResolver {
    resolver: RefCell<ReferenceResolver>,
    /// Pool index of the checker whose symbol arena the resolver reads.
    checker_index: usize,
}

// Go: binder/referenceresolver.go:37 NewReferenceResolver
#[must_use]
pub fn new_binder_reference_resolver(
    options: &'static CompilerOptions,
    hooks: ReferenceResolverHooks,
    checker_index: usize,
) -> BinderReferenceResolver {
    BinderReferenceResolver {
        resolver: RefCell::new(new_reference_resolver(options, hooks)),
        checker_index,
    }
}

impl TransformReferenceResolver for BinderReferenceResolver {
    fn get_referenced_export_container(&self, node: Node, prefix_locals: bool) -> Node {
        with_checker_at(self.checker_index, |c| {
            self.resolver
                .borrow_mut()
                .get_referenced_export_container(c, node, prefix_locals)
        })
    }

    fn get_referenced_import_declaration(&self, node: Node) -> Node {
        with_checker_at(self.checker_index, |c| {
            self.resolver
                .borrow_mut()
                .get_referenced_import_declaration(c, node)
        })
    }

    fn get_referenced_value_declaration(&self, node: Node) -> Node {
        with_checker_at(self.checker_index, |c| {
            self.resolver
                .borrow_mut()
                .get_referenced_value_declaration(c, node)
        })
    }

    fn get_referenced_value_declarations(&self, node: Node) -> Vec<Node> {
        with_checker_at(self.checker_index, |c| {
            self.resolver
                .borrow_mut()
                .get_referenced_value_declarations(c, node)
        })
    }

    fn get_element_access_expression_name(&self, expression: Node) -> String {
        with_checker_at(self.checker_index, |c| {
            self.resolver
                .borrow()
                .get_element_access_expression_name(c, expression)
        })
    }

    fn get_referenced_member_value_declaration(&self, node: Node) -> Node {
        with_checker_at(self.checker_index, |c| {
            self.resolver
                .borrow()
                .get_referenced_member_value_declaration(c, node)
        })
    }
}
