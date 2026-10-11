// Go: internal/typeparser/module_export_reference.go

use crate::effect::typeparser::*;
use crate::prelude::*;
use std::sync::atomic::{AtomicU32, Ordering};

/// Go `func(*TypeParser, *checker.Checker, *ast.SourceFile) bool`. The
/// checker is `tp.checker`.
pub type MatchesSourceFileFn = fn(&mut TypeParser<'_>, Node) -> bool;

pub struct PackageSourceFileDescriptor {
    pub package_name: String,
    pub matches_source_file: Option<MatchesSourceFileFn>,
    pub cache_key: Option<PackageSourceFileDescriptorCacheKey>,
}

/// Go `packageSourceFileDescriptorCacheKey`. Go uses the address of a
/// fresh `new(packageSourceFileDescriptorCacheKey)` as the identity of a
/// descriptor; the port gives each descriptor a fresh number.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct PackageSourceFileDescriptorCacheKey(pub u32);

/// The next `PackageSourceFileDescriptorCacheKey` (Go `new`).
static NEXT_PACKAGE_SOURCE_FILE_DESCRIPTOR_CACHE_KEY: AtomicU32 = AtomicU32::new(1);

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct ModuleExportReferenceCacheKey {
    pub symbol: SymbolId,
    pub descriptor: PackageSourceFileDescriptorCacheKey,
    pub member_name: String,
}

// Go: newPackageSourceFileDescriptor
/// Descriptors are package-level values (`LazyLock` statics in the port).
pub fn new_package_source_file_descriptor(
    package_name: &str,
    matches_source_file: Option<MatchesSourceFileFn>,
) -> PackageSourceFileDescriptor {
    PackageSourceFileDescriptor {
        package_name: package_name.to_string(),
        matches_source_file,
        cache_key: Some(PackageSourceFileDescriptorCacheKey(
            NEXT_PACKAGE_SOURCE_FILE_DESCRIPTOR_CACHE_KEY.fetch_add(1, Ordering::Relaxed),
        )),
    }
}

/// A `reference_symbol` cache entry.
// PORT: Go caches only `reference`. The port also keeps `at_location`, so the
// stability rules need no second `GetSymbolAtLocation` call.
#[derive(Clone, Copy, Debug)]
pub struct ReferenceSymbols {
    /// The first `get_symbol_at_location(node)` result. For an Identifier it
    /// is the checker's `GetSymbolAtLocation(node)`.
    pub at_location: SymbolId,
    /// Go `ReferenceSymbolAtNode(node)`.
    pub reference: SymbolId,
}

impl TypeParser<'_> {
    pub fn reference_symbol_at_node(&mut self, node: Node) -> SymbolId {
        self.reference_symbols_at_node(node).reference
    }

    /// `reference_symbol_at_node(node)`, with the symbol at `node` that it
    /// starts from.
    // PORT: not in Go. Go `runStabilityApiUsage` calls `GetSymbolAtLocation`
    // and then `ReferenceSymbolAtNode`, which calls it again on a cache miss.
    // The checker gives an Identifier the same symbol on every call, so the
    // port keeps the first result and saves one call per identifier per rule.
    pub fn reference_symbols_at_node(&mut self, node: Node) -> ReferenceSymbols {
        if node.is_nil() {
            return ReferenceSymbols {
                at_location: SymbolId::NIL,
                reference: SymbolId::NIL,
            };
        }

        cached!(self, reference_symbol, node, {
            let at_location = self.get_symbol_at_location(node);
            let mut sym = at_location;
            if sym.is_nil() && node.kind() == SyntaxKind::PropertyAccessExpression {
                let prop = node;
                if prop.name().is_some() {
                    sym = self.get_symbol_at_location(prop.name());
                }
            }

            sym = self.resolve_aliased_symbol(sym);
            let reference = if node.kind() == SyntaxKind::Identifier && !is_declaration_name(node) {
                self.resolve_constant_alias_symbol(sym)
            } else {
                sym
            };
            ReferenceSymbols {
                at_location,
                reference,
            }
        })
    }

    pub fn resolve_constant_alias_symbol(&mut self, sym: SymbolId) -> SymbolId {
        let mut sym = sym;
        let mut seen: FxHashSet<SymbolId> = FxHashSet::default();
        while sym.is_some() {
            if seen.contains(&sym) {
                return sym;
            }
            seen.insert(sym);

            let declaration_node = self.checker.sym(sym).value_declaration;
            if declaration_node.is_nil()
                || declaration_node.kind() != SyntaxKind::VariableDeclaration
                || declaration_node.parent().is_nil()
                || declaration_node.parent().kind() != SyntaxKind::VariableDeclarationList
                || !declaration_node
                    .parent()
                    .flags()
                    .intersects(NodeFlags::CONST)
            {
                return sym;
            }
            let declaration = declaration_node;
            if declaration.initializer().is_nil() {
                return sym;
            }

            let next = self.get_symbol_at_location(skip_parentheses(declaration.initializer()));
            if next.is_nil() {
                return sym;
            }
            sym = self.resolve_aliased_symbol(next);
        }
        SymbolId::NIL
    }

    pub fn is_source_file_in_package(&mut self, sf: Node, package_name: &str) -> bool {
        if sf.is_nil() {
            return false;
        }
        let Some(pkg) = self.package_json_for_source_file(sf) else {
            return false;
        };
        let (name, ok) = pkg.fields.name.get_value();
        ok && crate::frontend::vfs::vfsmatch::equal_fold(name.as_bytes(), package_name.as_bytes())
    }

    pub fn is_node_reference_to_module_export(
        &mut self,
        node: Node,
        desc: &PackageSourceFileDescriptor,
        member_name: &str,
    ) -> bool {
        let sym = self.reference_symbol_at_node(node);
        if sym.is_nil() {
            return false;
        }
        // Exported descriptors built as struct literals have no stable matcher identity.
        let Some(cache_key) = desc.cache_key else {
            return self.is_symbol_reference_to_module_export(sym, desc, member_name);
        };

        let key = ModuleExportReferenceCacheKey {
            symbol: sym,
            descriptor: cache_key,
            member_name: member_name.to_string(),
        };
        cached!(self, module_export_reference, key, {
            self.is_symbol_reference_to_module_export(sym, desc, member_name)
        })
    }

    pub fn is_symbol_reference_to_module_export(
        &mut self,
        sym: SymbolId,
        desc: &PackageSourceFileDescriptor,
        member_name: &str,
    ) -> bool {
        let declarations = self.checker.sym(sym).declarations.to_vec();
        for decl in declarations {
            if decl.is_nil() {
                continue;
            }
            let sf = get_source_file_of_node(decl);
            if sf.is_nil() || !self.is_source_file_in_package(sf, &desc.package_name) {
                continue;
            }
            if let Some(matches_source_file) = desc.matches_source_file
                && !matches_source_file(self, sf)
            {
                continue;
            }
            let module_sym = self.checker.get_symbol_of_declaration(sf);
            if module_sym.is_nil() {
                continue;
            }
            let mut export_sym = self
                .checker
                .try_get_member_in_module_exports_and_properties(member_name, module_sym);
            export_sym = self.resolve_aliased_symbol(export_sym);
            if self
                .checker
                .get_symbol_if_same_reference(export_sym, sym)
                .is_some()
            {
                return true;
            }
        }

        false
    }

    pub fn is_node_reference_to_module(
        &mut self,
        node: Node,
        desc: &PackageSourceFileDescriptor,
    ) -> bool {
        let sym = self.reference_symbol_at_node(node);
        if sym.is_nil() {
            return false;
        }

        let declarations = self.checker.sym(sym).declarations.to_vec();
        for decl in declarations {
            if decl.is_nil() {
                continue;
            }
            let sf = get_source_file_of_node(decl);
            if sf.is_nil() || !self.is_source_file_in_package(sf, &desc.package_name) {
                continue;
            }
            match desc.matches_source_file {
                None => return true,
                Some(matches_source_file) => {
                    if matches_source_file(self, sf) {
                        return true;
                    }
                }
            }
        }

        false
    }
}
