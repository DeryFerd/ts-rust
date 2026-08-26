//! Location-aware symbol chains from the pinned symbol accessibility query.
//!
//! Display names are local to one enclosing node. They never replace names,
//! symbols, or types in the semantic store.

use std::{
    cmp::Ordering,
    collections::{BTreeMap, HashMap, HashSet},
};

use ts_ast::{FileId, NodeData, NodeRef, SyntaxKind};
use ts_binder::{InternalSymbolName, SemanticSymbolId, SymbolFlags, SymbolTableId};

use super::{
    AliasTargetState, CanonicalTypeMapperStore, DeclaredTypeHost, DeclaredTypeHostError,
    ProductionAliasTargetHost, ProductionAliasTargetHostError,
    alias::{CanonicalAliasResolutionError, CanonicalAliasResolver, CanonicalImmediateAliasTarget},
    module_resolution::{CanonicalModuleResolutionLookup, CanonicalModuleResolutionManifest},
};

/// A location-aware name could not be proved from the retained source graph.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum SymbolDisplayError {
    SourceHost(DeclaredTypeHostError),
    AliasHost(ProductionAliasTargetHostError),
    InvalidLocation(NodeRef),
    InvalidModuleSpecifier(NodeRef),
    InvalidSymbol(SemanticSymbolId),
    InvalidTable(SymbolTableId),
    InvalidAliasCache(SemanticSymbolId),
    Alias(CanonicalAliasResolutionError),
    CyclicAlias(SemanticSymbolId),
    CyclicContainer(SemanticSymbolId),
    MissingModuleSpecifier(SemanticSymbolId),
}

impl std::fmt::Display for SymbolDisplayError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::SourceHost(error) => error.fmt(formatter),
            Self::AliasHost(error) => error.fmt(formatter),
            Self::InvalidLocation(node) => {
                write!(formatter, "symbol display has an invalid location {node:?}")
            }
            Self::InvalidModuleSpecifier(node) => write!(
                formatter,
                "symbol display has an invalid module specifier for {node:?}"
            ),
            Self::InvalidSymbol(symbol) => {
                write!(formatter, "symbol display has an invalid symbol {symbol:?}")
            }
            Self::InvalidTable(table) => {
                write!(formatter, "symbol display has an invalid table {table:?}")
            }
            Self::InvalidAliasCache(symbol) => write!(
                formatter,
                "symbol display has an invalid alias cache for {symbol:?}"
            ),
            Self::Alias(error) => error.fmt(formatter),
            Self::CyclicAlias(symbol) => {
                write!(formatter, "symbol display has a cyclic alias {symbol:?}")
            }
            Self::CyclicContainer(symbol) => write!(
                formatter,
                "symbol display has a cyclic container {symbol:?}"
            ),
            Self::MissingModuleSpecifier(symbol) => write!(
                formatter,
                "symbol display has no module specifier for {symbol:?}"
            ),
        }
    }
}

impl std::error::Error for SymbolDisplayError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::SourceHost(error) => Some(error),
            Self::AliasHost(error) => Some(error),
            Self::Alias(error) => Some(error),
            _ => None,
        }
    }
}

#[derive(Clone, Copy, Debug)]
struct ScopeTable {
    id: SymbolTableId,
    types_only: bool,
    local: bool,
}

/// One query's scope and independently checked alias targets.
#[derive(Debug)]
pub(super) struct SymbolDisplayContext {
    enclosing: NodeRef,
    scopes: Vec<ScopeTable>,
    aliases: HashMap<SemanticSymbolId, Result<SemanticSymbolId, SymbolDisplayError>>,
    module_specifiers: HashMap<SemanticSymbolId, String>,
    file_order: Vec<FileId>,
}

impl SymbolDisplayContext {
    pub(super) fn new(
        store: &mut CanonicalTypeMapperStore,
        host: &DeclaredTypeHost<'_>,
        alias_host: &mut ProductionAliasTargetHost<'_, '_, '_>,
        manifest: &CanonicalModuleResolutionManifest,
        globals: SymbolTableId,
        file_order: &[FileId],
        enclosing: NodeRef,
    ) -> Result<Self, SymbolDisplayError> {
        let scopes = scope_tables(store, host, globals, enclosing)?;
        let mut context = Self {
            enclosing,
            scopes,
            aliases: HashMap::new(),
            module_specifiers: HashMap::new(),
            file_order: file_order.to_vec(),
        };
        let mut tables = context
            .scopes
            .iter()
            .map(|scope| scope.id)
            .collect::<Vec<_>>();
        let (arena, bound) = host
            .source(enclosing)
            .ok_or(SymbolDisplayError::InvalidLocation(enclosing))?;
        for (id, record) in arena.iter() {
            let NodeData::StringLiteral(literal) = &record.data else {
                continue;
            };
            let node = NodeRef::new(arena.id(), bound.file_id(), id);
            let CanonicalModuleResolutionLookup::Resolved(module) = manifest.lookup(node) else {
                continue;
            };
            let symbol = store
                .get_merged_symbol(module.target_symbol())
                .ok_or(SymbolDisplayError::InvalidSymbol(module.target_symbol()))?;
            context
                .module_specifiers
                .entry(symbol)
                .or_insert_with(|| literal.text.clone());
            if let Some(table) = exports(store, symbol)? {
                tables.push(table);
            }
        }
        let mut visited = HashSet::new();
        while let Some(table) = tables.pop() {
            if !visited.insert(table) {
                continue;
            }
            let aliases = store
                .symbol_table(table)
                .ok_or(SymbolDisplayError::InvalidTable(table))?
                .iter()
                .filter_map(|(_, symbol)| {
                    store
                        .symbol(symbol)
                        .is_some_and(|record| record.flags().intersects(SymbolFlags::ALIAS))
                        .then_some(symbol)
                })
                .collect::<Vec<_>>();
            for alias in aliases {
                let result = checked_alias_target(store, alias_host, alias, &mut HashSet::new());
                if let Ok(target) = result
                    && let Some(table) = exports(store, target)?
                {
                    tables.push(table);
                }
                context.aliases.insert(alias, result);
            }
        }
        Ok(context)
    }

    pub(super) fn symbol_chain(
        &self,
        store: &CanonicalTypeMapperStore,
        host: &DeclaredTypeHost<'_>,
        symbol: SemanticSymbolId,
        meaning: SymbolFlags,
        yield_module: bool,
    ) -> Result<Vec<SemanticSymbolId>, SymbolDisplayError> {
        validate_symbol(store, host, symbol)?;
        if store
            .symbol(symbol)
            .is_some_and(|record| record.flags().intersects(SymbolFlags::TYPE_PARAMETER))
        {
            return Ok(vec![symbol]);
        }
        self.symbol_chain_worker(
            store,
            host,
            symbol,
            meaning,
            yield_module,
            true,
            &mut HashSet::new(),
        )
    }

    #[allow(clippy::too_many_arguments)]
    fn symbol_chain_worker(
        &self,
        store: &CanonicalTypeMapperStore,
        host: &DeclaredTypeHost<'_>,
        symbol: SemanticSymbolId,
        meaning: SymbolFlags,
        yield_module: bool,
        end_of_chain: bool,
        parents: &mut HashSet<SemanticSymbolId>,
    ) -> Result<Vec<SemanticSymbolId>, SymbolDisplayError> {
        if !parents.insert(symbol) {
            return Err(SymbolDisplayError::CyclicContainer(symbol));
        }
        let result = (|| {
            let mut chain =
                self.accessible_chain(store, host, symbol, meaning, &mut HashSet::new())?;
            let qualifier_meaning = if chain.len() > 1 {
                left_meaning(meaning)
            } else {
                meaning
            };
            if chain.is_empty()
                || self.needs_qualification(
                    store,
                    host,
                    *chain.first().unwrap_or(&symbol),
                    qualifier_meaning,
                )?
            {
                let root = *chain.first().unwrap_or(&symbol);
                if let Some(parent) = validated_parent(store, host, root)? {
                    let mut parent_chain = self.symbol_chain_worker(
                        store,
                        host,
                        parent,
                        left_meaning(meaning),
                        yield_module,
                        false,
                        parents,
                    )?;
                    if !parent_chain.is_empty() {
                        if chain.is_empty() {
                            chain.push(symbol);
                        }
                        parent_chain.extend(chain);
                        chain = parent_chain;
                    }
                }
            }
            if !chain.is_empty() {
                return Ok(chain);
            }
            let record = store
                .symbol(symbol)
                .ok_or(SymbolDisplayError::InvalidSymbol(symbol))?;
            if !end_of_chain
                && (record
                    .flags()
                    .intersects(SymbolFlags::TYPE_LITERAL | SymbolFlags::OBJECT_LITERAL)
                    || !yield_module && is_external_module(store, host, symbol)?)
            {
                return Ok(Vec::new());
            }
            Ok(vec![symbol])
        })();
        parents.remove(&symbol);
        result
    }

    fn accessible_chain(
        &self,
        store: &CanonicalTypeMapperStore,
        host: &DeclaredTypeHost<'_>,
        symbol: SemanticSymbolId,
        meaning: SymbolFlags,
        visited: &mut HashSet<(SemanticSymbolId, SymbolTableId)>,
    ) -> Result<Vec<SemanticSymbolId>, SymbolDisplayError> {
        if is_property_or_method_declaration(store, host, symbol)? {
            return Ok(Vec::new());
        }
        for scope in &self.scopes {
            let chain =
                self.chain_in_table(store, host, symbol, meaning, *scope, false, visited)?;
            if !chain.is_empty() {
                return Ok(chain);
            }
        }
        Ok(Vec::new())
    }

    #[allow(clippy::too_many_arguments)]
    fn chain_in_table(
        &self,
        store: &CanonicalTypeMapperStore,
        host: &DeclaredTypeHost<'_>,
        symbol: SemanticSymbolId,
        meaning: SymbolFlags,
        scope: ScopeTable,
        ignore_qualification: bool,
        visited: &mut HashSet<(SemanticSymbolId, SymbolTableId)>,
    ) -> Result<Vec<SemanticSymbolId>, SymbolDisplayError> {
        if !visited.insert((symbol, scope.id)) {
            return Ok(Vec::new());
        }
        let result = (|| {
            let target = store
                .symbol(symbol)
                .ok_or(SymbolDisplayError::InvalidSymbol(symbol))?;
            let table = store
                .symbol_table(scope.id)
                .ok_or(SymbolDisplayError::InvalidTable(scope.id))?;
            if let Some(direct) = table
                .get(target.name())
                .filter(|direct| in_scope(store, scope, *direct))
                && (same_reference(store, direct, symbol)?
                    || store
                        .symbol(direct)
                        .and_then(|record| record.export_symbol())
                        .is_some_and(|export| {
                            same_reference(store, export, symbol).unwrap_or(false)
                        }))
                && !is_external_module(store, host, direct)?
                && (ignore_qualification
                    || self.can_qualify(store, host, direct, meaning, visited)?)
            {
                return Ok(vec![symbol]);
            }
            let mut candidates = Vec::new();
            for (_, alias) in table.iter() {
                let record = store
                    .symbol(alias)
                    .ok_or(SymbolDisplayError::InvalidSymbol(alias))?;
                if scope.types_only
                    || !record.flags().intersects(SymbolFlags::ALIAS)
                    || record.name() == InternalSymbolName::ExportEquals.as_ref()
                    || record.name() == InternalSymbolName::Default.as_ref()
                    || !ignore_qualification
                        && has_declaration_kind(store, host, alias, SyntaxKind::ExportSpecifier)?
                    || scope.local
                        && has_declaration_kind(store, host, alias, SyntaxKind::NamespaceExport)?
                    || has_declaration_kind(
                        store,
                        host,
                        alias,
                        SyntaxKind::NamespaceExportDeclaration,
                    )? && host
                        .bound_file(self.enclosing)
                        .and_then(|bound| bound.source_facts())
                        .is_some_and(
                            ts_binder::CanonicalSourceFileFacts::is_external_or_common_js_module,
                        )
                {
                    continue;
                }
                let imported = self.alias_target(alias)?;
                if same_reference(store, alias, symbol)? || same_reference(store, imported, symbol)?
                {
                    if ignore_qualification
                        || self.can_qualify(store, host, alias, meaning, visited)?
                    {
                        candidates.push(vec![alias]);
                    }
                    continue;
                }
                if let Some(exports) = exports(store, imported)? {
                    let mut child = self.chain_in_table(
                        store,
                        host,
                        symbol,
                        meaning,
                        ScopeTable {
                            id: exports,
                            types_only: false,
                            local: false,
                        },
                        true,
                        visited,
                    )?;
                    if !child.is_empty()
                        && self.can_qualify(store, host, alias, left_meaning(meaning), visited)?
                    {
                        child.insert(0, alias);
                        candidates.push(child);
                    }
                }
            }
            candidates.sort_by(|left, right| self.compare_chains(store, host, left, right));
            Ok(candidates.into_iter().next().unwrap_or_default())
        })();
        visited.remove(&(symbol, scope.id));
        result
    }

    fn needs_qualification(
        &self,
        store: &CanonicalTypeMapperStore,
        host: &DeclaredTypeHost<'_>,
        symbol: SemanticSymbolId,
        meaning: SymbolFlags,
    ) -> Result<bool, SymbolDisplayError> {
        let record = store
            .symbol(symbol)
            .ok_or(SymbolDisplayError::InvalidSymbol(symbol))?;
        for scope in &self.scopes {
            let table = store
                .symbol_table(scope.id)
                .ok_or(SymbolDisplayError::InvalidTable(scope.id))?;
            let Some(raw) = table
                .get(record.name())
                .filter(|candidate| in_scope(store, *scope, *candidate))
            else {
                continue;
            };
            let candidate = store
                .get_merged_symbol(raw)
                .ok_or(SymbolDisplayError::InvalidSymbol(raw))?;
            if same_reference(store, candidate, symbol)? {
                return Ok(false);
            }
            let candidate_record = store
                .symbol(candidate)
                .ok_or(SymbolDisplayError::InvalidSymbol(candidate))?;
            let candidate = if candidate_record.flags().intersects(SymbolFlags::ALIAS)
                && !has_declaration_kind(store, host, candidate, SyntaxKind::ExportSpecifier)?
            {
                self.alias_target(candidate)?
            } else {
                candidate
            };
            if store
                .symbol(candidate)
                .ok_or(SymbolDisplayError::InvalidSymbol(candidate))?
                .flags()
                .intersects(meaning)
            {
                return Ok(true);
            }
        }
        Ok(false)
    }

    fn can_qualify(
        &self,
        store: &CanonicalTypeMapperStore,
        host: &DeclaredTypeHost<'_>,
        symbol: SemanticSymbolId,
        meaning: SymbolFlags,
        visited: &mut HashSet<(SemanticSymbolId, SymbolTableId)>,
    ) -> Result<bool, SymbolDisplayError> {
        if !self.needs_qualification(store, host, symbol, meaning)? {
            return Ok(true);
        }
        let Some(parent) = validated_parent(store, host, symbol)? else {
            return Ok(false);
        };
        self.accessible_chain(store, host, parent, left_meaning(meaning), visited)
            .map(|chain| !chain.is_empty())
    }

    fn alias_target(
        &self,
        alias: SemanticSymbolId,
    ) -> Result<SemanticSymbolId, SymbolDisplayError> {
        self.aliases
            .get(&alias)
            .copied()
            .unwrap_or(Err(SymbolDisplayError::InvalidAliasCache(alias)))
    }

    fn compare_chains(
        &self,
        store: &CanonicalTypeMapperStore,
        host: &DeclaredTypeHost<'_>,
        left: &[SemanticSymbolId],
        right: &[SemanticSymbolId],
    ) -> Ordering {
        left.len().cmp(&right.len()).then_with(|| {
            left.iter()
                .zip(right)
                .map(|(left, right)| self.compare_symbols(store, host, *left, *right))
                .find(|order| *order != Ordering::Equal)
                .unwrap_or(Ordering::Equal)
        })
    }

    fn compare_symbols(
        &self,
        store: &CanonicalTypeMapperStore,
        host: &DeclaredTypeHost<'_>,
        left: SemanticSymbolId,
        right: SemanticSymbolId,
    ) -> Ordering {
        let (Some(left_record), Some(right_record)) = (store.symbol(left), store.symbol(right))
        else {
            return left.cmp(&right);
        };
        let left_declaration = left_record
            .declarations()
            .and_then(|declarations| declarations.first());
        let right_declaration = right_record
            .declarations()
            .and_then(|declarations| declarations.first());
        let order = match (left_declaration, right_declaration) {
            (Some(left), Some(right)) => self
                .file_order
                .iter()
                .position(|file| *file == left.file)
                .cmp(&self.file_order.iter().position(|file| *file == right.file))
                .then_with(|| {
                    host.node(*left)
                        .map(|node| node.range.start)
                        .cmp(&host.node(*right).map(|node| node.range.start))
                }),
            (Some(_), None) => Ordering::Less,
            (None, Some(_)) => Ordering::Greater,
            (None, None) => Ordering::Equal,
        };
        order
            .then_with(|| {
                left_record
                    .name()
                    .as_bytes()
                    .cmp(right_record.name().as_bytes())
            })
            .then_with(|| left.cmp(&right))
    }

    pub(super) fn module_specifier(
        &self,
        symbol: SemanticSymbolId,
    ) -> Result<&str, SymbolDisplayError> {
        self.module_specifiers
            .get(&symbol)
            .map(String::as_str)
            .ok_or(SymbolDisplayError::MissingModuleSpecifier(symbol))
    }

    pub(super) fn add_module_specifiers(
        &mut self,
        specifiers: &BTreeMap<SemanticSymbolId, String>,
    ) {
        for (symbol, specifier) in specifiers {
            self.module_specifiers
                .entry(*symbol)
                .or_insert_with(|| specifier.clone());
        }
    }
}

fn in_scope(store: &CanonicalTypeMapperStore, scope: ScopeTable, symbol: SemanticSymbolId) -> bool {
    !scope.types_only
        || store.symbol(symbol).is_some_and(|record| {
            record.flags().intersects(SymbolFlags::TYPE)
                && !record.flags().intersects(SymbolFlags::ASSIGNMENT)
        })
}

fn scope_tables(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    globals: SymbolTableId,
    enclosing: NodeRef,
) -> Result<Vec<ScopeTable>, SymbolDisplayError> {
    let mut tables = Vec::new();
    let mut current = Some(enclosing);
    let mut visited = HashSet::new();
    while let Some(node) = current {
        if !visited.insert(node) {
            return Err(SymbolDisplayError::InvalidLocation(node));
        }
        let record = host
            .node(node)
            .ok_or(SymbolDisplayError::InvalidLocation(node))?;
        let (arena, bound) = host
            .source(node)
            .ok_or(SymbolDisplayError::InvalidLocation(node))?;
        if arena.revision() != bound.node_arena_revision() {
            return Err(SymbolDisplayError::InvalidLocation(node));
        }
        if !store.contains_node_ref(node) {
            return Err(SymbolDisplayError::InvalidLocation(node));
        }
        let external = bound
            .source_facts()
            .is_some_and(ts_binder::CanonicalSourceFileFacts::is_external_or_common_js_module);
        if (record.kind != SyntaxKind::SourceFile || external)
            && let Some(id) = bound.locals(node)
        {
            tables.push(ScopeTable {
                id,
                types_only: false,
                local: true,
            });
        }
        let owner = bound
            .symbol(node)
            .and_then(|symbol| store.get_merged_symbol(symbol));
        match record.kind {
            SyntaxKind::ModuleDeclaration | SyntaxKind::SourceFile
                if record.kind != SyntaxKind::SourceFile || external =>
            {
                let owner = owner.ok_or(SymbolDisplayError::InvalidLocation(node))?;
                if let Some(id) = store.symbol(owner).and_then(|record| record.exports()) {
                    tables.push(ScopeTable {
                        id,
                        types_only: false,
                        local: true,
                    });
                }
            }
            SyntaxKind::ClassDeclaration
            | SyntaxKind::ClassExpression
            | SyntaxKind::InterfaceDeclaration => {
                let owner = owner.ok_or(SymbolDisplayError::InvalidLocation(node))?;
                if let Some(id) = store.symbol(owner).and_then(|record| record.members()) {
                    tables.push(ScopeTable {
                        id,
                        types_only: true,
                        local: false,
                    });
                }
            }
            _ => {}
        }
        current = record
            .parent
            .map(|parent| NodeRef::new(node.arena, node.file, parent));
    }
    tables.push(ScopeTable {
        id: globals,
        types_only: false,
        local: true,
    });
    for scope in &tables {
        if store.symbol_table(scope.id).is_none() {
            return Err(SymbolDisplayError::InvalidTable(scope.id));
        }
    }
    Ok(tables)
}

fn checked_alias_target(
    store: &mut CanonicalTypeMapperStore,
    host: &mut ProductionAliasTargetHost<'_, '_, '_>,
    alias: SemanticSymbolId,
    visiting: &mut HashSet<SemanticSymbolId>,
) -> Result<SemanticSymbolId, SymbolDisplayError> {
    if !visiting.insert(alias) {
        return Err(SymbolDisplayError::CyclicAlias(alias));
    }
    if !store.ensure_alias_symbol_links(alias) {
        return Err(SymbolDisplayError::InvalidAliasCache(alias));
    }
    let original = store.alias_symbol_links(alias).cloned();
    let result = (|| {
        let (immediate, type_only) = host
            .get_target_and_type_only_of_alias_declaration(store, alias)
            .map_err(|reason| {
                SymbolDisplayError::Alias(CanonicalAliasResolutionError::TargetUnavailable {
                    alias,
                    reason,
                })
            })?;
        let CanonicalImmediateAliasTarget::Resolved(immediate) = immediate else {
            return Err(SymbolDisplayError::InvalidAliasCache(alias));
        };
        let target = store
            .symbol(immediate)
            .ok_or(SymbolDisplayError::InvalidSymbol(immediate))?;
        let target_flags = target.flags();
        let non_local_alias = target_flags
            & (SymbolFlags::ALIAS
                | SymbolFlags::VALUE
                | SymbolFlags::TYPE
                | SymbolFlags::NAMESPACE)
            == SymbolFlags::ALIAS
            || target_flags == SymbolFlags::ALIAS | SymbolFlags::NAMESPACE_MODULE
            || target_flags.intersects(SymbolFlags::ALIAS)
                && target_flags.intersects(SymbolFlags::ASSIGNMENT);
        let target = if non_local_alias {
            let target = checked_alias_target(store, host, immediate, visiting)?;
            store
                .get_merged_symbol(target)
                .ok_or(SymbolDisplayError::InvalidSymbol(target))?
        } else {
            immediate
        };
        let inherited_type_only = store
            .alias_symbol_links(immediate)
            .and_then(|links| links.type_only_declaration);
        if let Some(original) = original
            && (original
                .immediate_target
                .is_some_and(|cached| cached != immediate)
                || original.alias_target != AliasTargetState::Unresolved
                    && original.alias_target != AliasTargetState::Resolved(target)
                || original
                    .type_only_declaration
                    .is_some_and(|cached| Some(cached) != type_only.or(inherited_type_only))
                || original.alias_target != AliasTargetState::Unresolved
                    && original.type_only_declaration != type_only.or(inherited_type_only))
        {
            return Err(SymbolDisplayError::InvalidAliasCache(alias));
        }
        let resolved = CanonicalAliasResolver::new(store, host)
            .resolve_alias(alias)
            .map_err(SymbolDisplayError::Alias)?;
        if resolved.target != AliasTargetState::Resolved(target) {
            return Err(SymbolDisplayError::InvalidAliasCache(alias));
        }
        Ok(target)
    })();
    visiting.remove(&alias);
    result
}

fn same_reference(
    store: &CanonicalTypeMapperStore,
    left: SemanticSymbolId,
    right: SemanticSymbolId,
) -> Result<bool, SymbolDisplayError> {
    let left = store
        .get_merged_symbol(left)
        .ok_or(SymbolDisplayError::InvalidSymbol(left))?;
    let right = store
        .get_merged_symbol(right)
        .ok_or(SymbolDisplayError::InvalidSymbol(right))?;
    Ok(left == right)
}

fn exports(
    store: &CanonicalTypeMapperStore,
    symbol: SemanticSymbolId,
) -> Result<Option<SymbolTableId>, SymbolDisplayError> {
    let record = store
        .symbol(symbol)
        .ok_or(SymbolDisplayError::InvalidSymbol(symbol))?;
    let exports = store
        .module_symbol_links(symbol)
        .and_then(|links| links.resolved_exports)
        .or_else(|| record.exports());
    if let Some(exports) = exports
        && store.symbol_table(exports).is_none()
    {
        return Err(SymbolDisplayError::InvalidTable(exports));
    }
    Ok(exports)
}

fn has_declaration_kind(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    symbol: SemanticSymbolId,
    kind: SyntaxKind,
) -> Result<bool, SymbolDisplayError> {
    let record = store
        .symbol(symbol)
        .ok_or(SymbolDisplayError::InvalidSymbol(symbol))?;
    Ok(record
        .declarations()
        .unwrap_or_default()
        .iter()
        .any(|declaration| {
            host.node(*declaration)
                .is_some_and(|node| node.kind == kind)
        }))
}

fn is_property_or_method_declaration(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    symbol: SemanticSymbolId,
) -> Result<bool, SymbolDisplayError> {
    let record = store
        .symbol(symbol)
        .ok_or(SymbolDisplayError::InvalidSymbol(symbol))?;
    let declarations = record.declarations().unwrap_or_default();
    Ok(!declarations.is_empty()
        && declarations.iter().all(|declaration| {
            host.node(*declaration).is_some_and(|node| {
                matches!(
                    node.kind,
                    SyntaxKind::PropertyDeclaration
                        | SyntaxKind::MethodDeclaration
                        | SyntaxKind::GetAccessor
                        | SyntaxKind::SetAccessor
                )
            })
        }))
}

pub(super) fn is_external_module(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    symbol: SemanticSymbolId,
) -> Result<bool, SymbolDisplayError> {
    let record = store
        .symbol(symbol)
        .ok_or(SymbolDisplayError::InvalidSymbol(symbol))?;
    Ok(record
        .declarations()
        .unwrap_or_default()
        .iter()
        .any(
            |declaration| match host.node(*declaration).map(|node| &node.data) {
                Some(NodeData::SourceFile(_)) => host
                    .bound_file(*declaration)
                    .and_then(|bound| bound.source_facts())
                    .is_some_and(
                        ts_binder::CanonicalSourceFileFacts::is_external_or_common_js_module,
                    ),
                Some(NodeData::ModuleDeclaration(module)) => host
                    .node(NodeRef::new(
                        declaration.arena,
                        declaration.file,
                        module.name,
                    ))
                    .is_some_and(|name| name.kind == SyntaxKind::StringLiteral),
                _ => false,
            },
        ))
}

fn validate_symbol(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    symbol: SemanticSymbolId,
) -> Result<(), SymbolDisplayError> {
    let record = store
        .symbol(symbol)
        .ok_or(SymbolDisplayError::InvalidSymbol(symbol))?;
    let canonical = store
        .get_merged_symbol(symbol)
        .ok_or(SymbolDisplayError::InvalidSymbol(symbol))?;
    for declaration in record.declarations().unwrap_or_default() {
        if host.node(*declaration).is_none() || !host.symbol_matches(store, *declaration, canonical)
        {
            return Err(SymbolDisplayError::InvalidSymbol(symbol));
        }
    }
    Ok(())
}

fn validated_parent(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    symbol: SemanticSymbolId,
) -> Result<Option<SemanticSymbolId>, SymbolDisplayError> {
    let record = store
        .symbol(symbol)
        .ok_or(SymbolDisplayError::InvalidSymbol(symbol))?;
    let Some(parent) = store.get_parent_of_symbol(symbol) else {
        return Ok(None);
    };
    validate_symbol(store, host, parent)?;
    let owner = store
        .symbol(parent)
        .ok_or(SymbolDisplayError::InvalidSymbol(parent))?;
    let member = [owner.members(), owner.exports()]
        .into_iter()
        .flatten()
        .any(|table| {
            store
                .symbol_table(table)
                .and_then(|table| table.get(record.name()))
                .is_some_and(|candidate| same_reference(store, candidate, symbol).unwrap_or(false))
        });
    if !member {
        return Err(SymbolDisplayError::InvalidSymbol(symbol));
    }
    Ok(Some(parent))
}

const fn left_meaning(meaning: SymbolFlags) -> SymbolFlags {
    if meaning.bits() == SymbolFlags::VALUE.bits() {
        SymbolFlags::VALUE
    } else {
        SymbolFlags::NAMESPACE
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::semantic::{
        CanonicalCheckerContext, CanonicalCheckerOptions, CanonicalModuleResolutionEntry,
        CanonicalModuleResolutionManifestInput, CanonicalModuleResolutionMode,
        CanonicalResolvedModuleInput, TypeDisplayUnavailable,
    };
    use ts_binder::{
        CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
        EscapedName,
    };
    use ts_parser::{ParseResult, parse_source_file};

    fn facts(path: &str, module: CanonicalModuleState) -> CanonicalSourceFileFacts {
        CanonicalSourceFileFacts::new(
            EscapedName::source(format!("\"{path}\"")),
            CanonicalSourceLanguage::TypeScript,
            true,
            module,
        )
    }

    fn declaration(parsed: &ParseResult, file: FileId, name: &str) -> NodeRef {
        parsed.arena.iter().find_map(|(id, record)| {
            let name_id = match &record.data {
                NodeData::InterfaceDeclaration(declaration) => declaration.name,
                NodeData::FunctionDeclaration(declaration) => declaration.name?,
                NodeData::ModuleDeclaration(declaration) => declaration.name,
                _ => return None,
            };
            matches!(&parsed.arena.get(name_id)?.data, NodeData::Identifier(identifier) if identifier.text == name)
                .then_some(NodeRef::new(parsed.arena.id(), file, id))
        }).unwrap()
    }

    fn symbol(context: &CanonicalCheckerContext<'_>, node: NodeRef) -> SemanticSymbolId {
        let symbol = context.file(node.file).unwrap().1.symbol(node).unwrap();
        context.store().get_merged_symbol(symbol).unwrap()
    }

    fn bind(
        binder: &mut CanonicalBinder,
        parsed: &ParseResult,
        file: FileId,
        path: &str,
        module: CanonicalModuleState,
    ) {
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                facts(path, module),
            )
            .unwrap();
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
    }

    #[test]
    fn location_display_shortens_namespace_names_only_inside_the_namespace() {
        let parsed = parse_source_file(
            "declare namespace Foo { export function bar(): number; export interface Shape { value: number; } } declare const outside: Foo.Shape;",
        );
        let file = FileId::new(41_001);
        let mut binder = CanonicalBinder::new();
        bind(
            &mut binder,
            &parsed,
            file,
            "/input.d.ts",
            CanonicalModuleState::Script,
        );
        let mut context = CanonicalCheckerContext::new(
            binder.finish(),
            vec![(file, &parsed.arena)],
            CanonicalCheckerOptions::default(),
        )
        .unwrap();
        let bar = declaration(&parsed, file, "bar");
        let shape = declaration(&parsed, file, "Shape");
        let source = NodeRef::new(parsed.arena.id(), file, parsed.source_file);
        let bar_symbol = symbol(&context, bar);
        let shape_symbol = symbol(&context, shape);
        let shape_type = context.get_declared_type_of_symbol(shape_symbol).unwrap();
        for _ in 0..2 {
            assert_eq!(
                context
                    .symbol_to_string_at_location(bar_symbol, bar)
                    .unwrap(),
                "bar"
            );
            assert_eq!(
                context
                    .symbol_to_string_at_location(bar_symbol, source)
                    .unwrap(),
                "Foo.bar"
            );
            assert_eq!(
                context
                    .type_to_string_at_location(shape_type, shape)
                    .unwrap(),
                "Shape"
            );
            assert_eq!(
                context
                    .type_to_string_at_location(shape_type, source)
                    .unwrap(),
                "Foo.Shape"
            );
        }
        assert_eq!(context.symbol_to_string(bar_symbol).unwrap(), "bar");
        assert_eq!(context.type_to_string(shape_type).unwrap(), "Shape");
        assert_eq!(
            context
                .store()
                .symbol(shape_symbol)
                .unwrap()
                .name()
                .as_utf8(),
            Some("Shape")
        );
    }

    #[test]
    fn location_display_qualifies_interface_members_through_the_namespace() {
        let parsed = parse_source_file(
            "declare namespace JSX { interface IntrinsicElements { div: { id?: string }; } } declare const outside: number;",
        );
        let file = FileId::new(41_002);
        let mut binder = CanonicalBinder::new();
        bind(
            &mut binder,
            &parsed,
            file,
            "/input.d.ts",
            CanonicalModuleState::Script,
        );
        let mut context = CanonicalCheckerContext::new(
            binder.finish(),
            vec![(file, &parsed.arena)],
            CanonicalCheckerOptions::default(),
        )
        .unwrap();
        let property = parsed.arena.iter().find_map(|(id, record)| {
            let NodeData::PropertyDeclaration(property) = &record.data else { return None };
            matches!(&parsed.arena.get(property.name)?.data, NodeData::Identifier(identifier) if identifier.text == "div")
                .then_some(NodeRef::new(parsed.arena.id(), file, id))
        }).unwrap();
        let property_symbol = symbol(&context, property);
        let source = NodeRef::new(parsed.arena.id(), file, parsed.source_file);
        assert_eq!(
            context
                .symbol_to_string_at_location(property_symbol, source)
                .unwrap(),
            "JSX.IntrinsicElements.div"
        );
        assert_eq!(
            context
                .symbol_to_string_at_location(property_symbol, property)
                .unwrap(),
            "IntrinsicElements.div"
        );
    }

    fn import_context<'a>(
        target: &'a ParseResult,
        left: &'a ParseResult,
        right: &'a ParseResult,
    ) -> CanonicalCheckerContext<'a> {
        let mut binder = CanonicalBinder::new();
        let files = [
            (FileId::new(41_010), target, "/model.d.ts"),
            (FileId::new(41_011), left, "/left.d.ts"),
            (FileId::new(41_012), right, "/right.d.ts"),
        ];
        let mut entries = Vec::new();
        for (file, parsed, path) in files {
            bind(
                &mut binder,
                parsed,
                file,
                path,
                CanonicalModuleState::External,
            );
            for (_, record) in parsed.arena.iter() {
                if let NodeData::ImportDeclaration(import) = &record.data {
                    entries.push(CanonicalModuleResolutionEntry::resolved(
                        NodeRef::new(parsed.arena.id(), file, import.module_specifier),
                        CanonicalResolvedModuleInput::new(
                            FileId::new(41_010),
                            CanonicalModuleResolutionMode::Esm,
                            CanonicalModuleResolutionMode::Esm,
                        ),
                    ));
                }
            }
        }
        CanonicalCheckerContext::new_with_module_resolutions(
            binder.finish(),
            files
                .into_iter()
                .map(|(file, parsed, _)| (file, &parsed.arena))
                .collect(),
            CanonicalCheckerOptions::default(),
            CanonicalModuleResolutionManifestInput::new(entries),
        )
        .unwrap()
    }

    #[test]
    fn location_display_uses_each_files_alias_without_renaming_the_shared_target() {
        let target = parse_source_file(
            "export interface Shape { value: number; } export interface Other { text: string; }",
        );
        let left = parse_source_file(
            "import type { Shape as Left } from './model'; declare const value: Left;",
        );
        let right = parse_source_file(
            "import type { Shape as Right } from './model'; declare const value: Right;",
        );
        let mut context = import_context(&target, &left, &right);
        let target_symbol = symbol(&context, declaration(&target, FileId::new(41_010), "Shape"));
        let type_ = context.get_declared_type_of_symbol(target_symbol).unwrap();
        let left_location = NodeRef::new(left.arena.id(), FileId::new(41_011), left.source_file);
        let right_location = NodeRef::new(right.arena.id(), FileId::new(41_012), right.source_file);
        for _ in 0..2 {
            assert_eq!(
                context
                    .type_to_string_at_location(type_, left_location)
                    .unwrap(),
                "Left"
            );
            assert_eq!(
                context
                    .type_to_string_at_location(type_, right_location)
                    .unwrap(),
                "Right"
            );
            assert_eq!(
                context
                    .symbol_to_string_at_location(target_symbol, left_location)
                    .unwrap(),
                "Left"
            );
            assert_eq!(
                context
                    .symbol_to_string_at_location(target_symbol, right_location)
                    .unwrap(),
                "Right"
            );
        }
        assert_eq!(
            context.store().type_payload(type_).unwrap().symbol(),
            Some(target_symbol)
        );
        assert_eq!(context.type_to_string(type_).unwrap(), "Shape");
        assert_eq!(
            context
                .store()
                .symbol(target_symbol)
                .unwrap()
                .name()
                .as_utf8(),
            Some("Shape")
        );
    }

    #[test]
    fn module_display_specifiers_require_the_exact_source_module() {
        let target = parse_source_file("export interface Shape { value: number; }");
        let left = parse_source_file("export {};");
        let right = parse_source_file("export {};");
        let mut context = import_context(&target, &left, &right);
        let declaration = declaration(&target, FileId::new(41_010), "Shape");
        let target_symbol = symbol(&context, declaration);
        let type_ = context.get_declared_type_of_symbol(target_symbol).unwrap();
        let target_source = NodeRef::new(target.arena.id(), declaration.file, target.source_file);
        let location = NodeRef::new(right.arena.id(), FileId::new(41_012), right.source_file);
        let target_module = symbol(&context, target_source);
        assert_eq!(
            context.type_to_string_at_location_with_flags(
                type_,
                location,
                crate::semantic::CanonicalTypeFormatFlags::NO_TRUNCATION
            ),
            Err(TypeDisplayUnavailable::SymbolDisplay(
                SymbolDisplayError::MissingModuleSpecifier(target_module)
            ))
        );
        assert_eq!(
            context.set_module_display_specifier(declaration, "item-api".to_owned()),
            Err(SymbolDisplayError::InvalidLocation(declaration))
        );
        assert_eq!(
            context.set_module_display_specifier(target_source, String::new()),
            Err(SymbolDisplayError::InvalidModuleSpecifier(target_source))
        );
        let foreign = parse_source_file("export {};");
        let foreign_source =
            NodeRef::new(foreign.arena.id(), declaration.file, foreign.source_file);
        assert_eq!(
            context.set_module_display_specifier(foreign_source, "item-api".to_owned()),
            Err(SymbolDisplayError::InvalidLocation(foreign_source))
        );
        context
            .set_module_display_specifier(target_source, "item-api".to_owned())
            .unwrap();
        for _ in 0..2 {
            assert_eq!(
                context
                    .type_to_string_at_location_with_flags(
                        type_,
                        location,
                        crate::semantic::CanonicalTypeFormatFlags::NO_TRUNCATION
                    )
                    .unwrap(),
                "import(\"item-api\").Shape"
            );
        }
        assert_eq!(context.type_to_string(type_).unwrap(), "Shape");
        assert_eq!(
            context.store().type_payload(type_).unwrap().symbol(),
            Some(target_symbol)
        );
    }

    #[test]
    fn location_display_follows_namespace_imports_and_rejects_redirected_alias_caches() {
        let target = parse_source_file(
            "export interface Shape { value: number; } export interface Other { text: string; }",
        );
        let left = parse_source_file(
            "import type { Shape as Left } from './model'; declare const value: Left;",
        );
        let right = parse_source_file(
            "import * as Items from './model'; declare const value: Items.Shape;",
        );
        let mut context = import_context(&target, &left, &right);
        let target_symbol = symbol(&context, declaration(&target, FileId::new(41_010), "Shape"));
        let other = symbol(&context, declaration(&target, FileId::new(41_010), "Other"));
        let type_ = context.get_declared_type_of_symbol(target_symbol).unwrap();
        let left_location = NodeRef::new(left.arena.id(), FileId::new(41_011), left.source_file);
        let right_location = NodeRef::new(right.arena.id(), FileId::new(41_012), right.source_file);
        assert_eq!(
            context
                .type_to_string_at_location(type_, right_location)
                .unwrap(),
            "Items.Shape"
        );
        assert_eq!(
            context
                .type_to_string_at_location(type_, left_location)
                .unwrap(),
            "Left"
        );
        let alias = left
            .arena
            .iter()
            .find_map(|(id, node)| {
                matches!(node.data, NodeData::ImportSpecifier(_)).then_some(NodeRef::new(
                    left.arena.id(),
                    left_location.file,
                    id,
                ))
            })
            .unwrap();
        let alias = symbol(&context, alias);
        let mut links = context.store().alias_symbol_links(alias).unwrap().clone();
        links.alias_target = AliasTargetState::Resolved(other);
        links.immediate_target = Some(other);
        assert!(
            context
                .store_mut_for_test()
                .set_alias_symbol_links(alias, links.clone())
        );
        assert_eq!(
            context.type_to_string_at_location(type_, left_location),
            Err(TypeDisplayUnavailable::SymbolDisplay(
                SymbolDisplayError::InvalidAliasCache(alias)
            ))
        );
        assert_eq!(context.store().alias_symbol_links(alias), Some(&links));
        assert_eq!(
            context
                .type_to_string_at_location(type_, right_location)
                .unwrap(),
            "Items.Shape"
        );
        let foreign = parse_source_file("declare const outside: number;");
        let foreign_location =
            NodeRef::new(foreign.arena.id(), left_location.file, foreign.source_file);
        assert_eq!(
            context.type_to_string_at_location(type_, foreign_location),
            Err(TypeDisplayUnavailable::SymbolDisplay(
                SymbolDisplayError::InvalidLocation(foreign_location)
            ))
        );
    }
}
