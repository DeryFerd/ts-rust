// Go: internal/typeparser/module_export_reference.go

use crate::effect::typeparser::*;
use crate::prelude::*;
use std::sync::atomic::{AtomicU32, Ordering};
use std::sync::{LazyLock, Mutex};

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

/// Go `moduleExportReferenceCacheKey`.
/// PORT: Go keys by the member name. Here `member` is the descriptor id
/// (low 8 bits) and the `ExportMember::id` of the member name (high 24
/// bits), so an entry with its value is 12 bytes and no key holds a string.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct ModuleExportReferenceCacheKey {
    pub symbol: SymbolId,
    pub member: u32,
}

/// A member name that a rule asks about (the `memberName` argument of Go
/// `IsNodeReferenceToModuleExport`). Make one per call site with
/// `member!("name")`, or keep them in a static table.
// PERF: the static keeps the id of its name, so a module-export check reads
// one number for its cache key and does not hash the name (effperf3 item 2).
#[derive(Debug)]
pub struct ExportMember {
    pub name: &'static str,
    /// `id()`, or 0 before the first call.
    id: AtomicU32,
}

impl ExportMember {
    #[must_use]
    pub const fn new(name: &'static str) -> Self {
        Self {
            name,
            id: AtomicU32::new(0),
        }
    }

    /// The id of the name, the same for every `ExportMember` with that name
    /// in this process. Ids count from 1.
    #[inline]
    pub fn id(&self) -> u32 {
        match self.id.load(Ordering::Relaxed) {
            0 => self.first_id(),
            id => id,
        }
    }

    #[cold]
    #[inline(never)]
    fn first_id(&self) -> u32 {
        static IDS: LazyLock<Mutex<FxHashMap<&'static str, u32>>> = LazyLock::new(Mutex::default);
        let mut ids = IDS
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        let next = u32::try_from(ids.len() + 1).unwrap_or(u32::MAX);
        let id = *ids.entry(self.name).or_insert(next);
        self.id.store(id, Ordering::Relaxed);
        id
    }
}

/// Go's zero value of a member name, "".
impl Default for &'static ExportMember {
    fn default() -> Self {
        member!("")
    }
}

/// `&'static ExportMember` of a string literal: `member!("succeed")`.
#[macro_export]
#[doc(hidden)]
macro_rules! effect_export_member {
    ($name:literal) => {{
        static MEMBER: $crate::effect::typeparser::ExportMember =
            $crate::effect::typeparser::ExportMember::new($name);
        &MEMBER
    }};
}
pub use crate::effect_export_member as member;

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
    /// is the checker's `GetSymbolAtLocation(node)`. A later call can give a
    /// new transient symbol (a for-of binding element's property name does)
    /// with the same declarations and flags; the stability walk reads only
    /// those, so the first result gives the same answers.
    pub at_location: SymbolId,
    /// Go `ReferenceSymbolAtNode(node)`.
    pub reference: SymbolId,
}

/// A `reference_symbol` slot in a node link page: the `ReferenceSymbols`
/// of a node, with `at_location` kept like `CachedId`, so that
/// `Option<CachedReferenceSymbols>` is 8 bytes (a page of 64 nodes 512
/// bytes). The default is nil.
// PERF: the cache stays on node link pages (effcache1) and keeps both
// symbols (effperf1).
#[derive(Clone, Copy, Default)]
pub struct CachedReferenceSymbols {
    at_location: CachedId,
    reference: SymbolId,
}

const _: () = assert!(size_of::<Option<CachedReferenceSymbols>>() == 8);

impl TypeParser<'_> {
    pub fn reference_symbol_at_node(&mut self, node: Node) -> SymbolId {
        self.reference_symbols_at_node(node).reference
    }

    /// `reference_symbol_at_node(node)`, with the symbol at `node` that it
    /// starts from.
    // PORT: not in Go. Go `runStabilityApiUsage` calls `GetSymbolAtLocation`
    // and then `ReferenceSymbolAtNode`, which calls it again on a cache miss.
    // A later call on an Identifier gives a symbol with the same declarations
    // and flags (sometimes a new transient one), and the walk reads only those,
    // so the port keeps the first result and saves one call per identifier per
    // rule.
    pub fn reference_symbols_at_node(&mut self, node: Node) -> ReferenceSymbols {
        if node.is_nil() {
            return ReferenceSymbols {
                at_location: SymbolId::NIL,
                reference: SymbolId::NIL,
            };
        }

        // Go `Cached(&tp.links.ReferenceSymbol, node, ..)`.
        if let Some(cached) = self.links().reference_symbol.try_get(node) {
            return ReferenceSymbols {
                at_location: SymbolId(cached.at_location.get()),
                reference: cached.reference,
            };
        }
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
        *self.links().reference_symbol.get(node) = CachedReferenceSymbols {
            at_location: CachedId::new(at_location.0),
            reference,
        };
        ReferenceSymbols {
            at_location,
            reference,
        }
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
        member: &ExportMember,
    ) -> bool {
        let sym = self.reference_symbol_at_node(node);
        if sym.is_nil() {
            return false;
        }
        // Exported descriptors built as struct literals have no stable matcher identity.
        let Some(cache_key) = desc.cache_key else {
            return self.is_symbol_reference_to_module_export(sym, desc, member.name);
        };

        let Some(member_key) = module_export_member_key(cache_key, member) else {
            return self.is_symbol_reference_to_module_export(sym, desc, member.name);
        };
        let key = ModuleExportReferenceCacheKey {
            symbol: sym,
            member: member_key,
        };
        cached!(self, module_export_reference, key, {
            self.is_symbol_reference_to_module_export(sym, desc, member.name)
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

/// The `member` of a `ModuleExportReferenceCacheKey`, or `None` when the
/// descriptor id or the member id does not fit (then the caller does not
/// cache, as for a descriptor with no cache key).
fn module_export_member_key(
    descriptor: PackageSourceFileDescriptorCacheKey,
    member: &ExportMember,
) -> Option<u32> {
    let descriptor = u8::try_from(descriptor.0).ok()?;
    let id = member.id();
    (id < 1 << 24).then_some((id << 8) | u32::from(descriptor))
}
