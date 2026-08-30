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
    alias::{CanonicalAliasResolutionError, CanonicalAliasResolver},
    alias_provider::DisplayAliasTarget,
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
    UnnameableSymbol(SemanticSymbolId),
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
            Self::UnnameableSymbol(symbol) => write!(
                formatter,
                "symbol display cannot prove an accessible export name for {symbol:?}"
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
    entries: ScopeEntries,
    types_only: bool,
    local: bool,
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
enum ScopeEntries {
    Table(SymbolTableId),
    ClassExpressionName(SemanticSymbolId),
}

type VisitedTables = HashSet<(SemanticSymbolId, ScopeEntries, bool)>;

/// One query's scope and independently checked alias targets.
#[derive(Debug)]
pub(super) struct SymbolDisplayContext {
    enclosing: NodeRef,
    scopes: Vec<ScopeTable>,
    aliases: HashMap<SemanticSymbolId, Result<DisplayAliasTarget, SymbolDisplayError>>,
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
            .filter_map(|scope| match scope.entries {
                ScopeEntries::Table(id) => Some(id),
                ScopeEntries::ClassExpressionName(_) => None,
            })
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
                let checkpoint = store.checkpoint_alias_symbol_links();
                let result = checked_alias_target(store, alias_host, alias, &mut HashSet::new());
                if result.is_err() || matches!(result, Ok(DisplayAliasTarget::Namespace(_))) {
                    assert!(
                        store.restore_alias_symbol_links(checkpoint),
                        "alias lookup owns its checkpoint"
                    );
                }
                if let Ok(target) = result
                    && let Some(table) = display_alias_exports(store, host, alias, target)?
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
                let container = if let Some(parent) = validated_parent(store, host, root)? {
                    Some((parent, Some(root)))
                } else {
                    self.declaration_export_container(store, host, root)?
                };
                if let Some((parent, exported)) = container {
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
                            chain.extend(exported);
                        } else if let Some(exported) = exported {
                            chain[0] = exported;
                        } else {
                            chain.remove(0);
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
            if record.parent().is_none()
                && !record.name().is_internal()
                && record.flags().intersects(SymbolFlags::TYPE)
                && record
                    .declarations()
                    .is_some_and(|declarations| !declarations.is_empty())
                && !is_external_module(store, host, symbol)?
                && class_expression_name(store, host, symbol)?.is_none()
            {
                return Err(SymbolDisplayError::UnnameableSymbol(symbol));
            }
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

    fn declaration_export_container(
        &self,
        store: &CanonicalTypeMapperStore,
        host: &DeclaredTypeHost<'_>,
        symbol: SemanticSymbolId,
    ) -> Result<Option<(SemanticSymbolId, Option<SemanticSymbolId>)>, SymbolDisplayError> {
        let record = store
            .symbol(symbol)
            .ok_or(SymbolDisplayError::InvalidSymbol(symbol))?;
        for declaration in record.declarations().unwrap_or_default() {
            let node = host
                .node(*declaration)
                .ok_or(SymbolDisplayError::InvalidLocation(*declaration))?;
            let Some(parent) = node.parent else { continue };
            let mut container = NodeRef::new(declaration.arena, declaration.file, parent);
            let parent_node = host
                .node(container)
                .ok_or(SymbolDisplayError::InvalidLocation(container))?;
            if parent_node.kind == SyntaxKind::ModuleBlock {
                let Some(parent) = parent_node.parent else {
                    continue;
                };
                container.node = parent;
            }
            let kind = host
                .node(container)
                .ok_or(SymbolDisplayError::InvalidLocation(container))?
                .kind;
            if !matches!(kind, SyntaxKind::SourceFile | SyntaxKind::ModuleDeclaration) {
                continue;
            }
            let Some(module) = host
                .bound_file(container)
                .and_then(|bound| bound.symbol(container))
                .and_then(|module| store.get_merged_symbol(module))
            else {
                continue;
            };
            validate_symbol(store, host, module)?;
            let Some(table) = exports(store, module)? else {
                continue;
            };
            let table = store
                .symbol_table(table)
                .ok_or(SymbolDisplayError::InvalidTable(table))?;
            if let Some(exported) = table.get(InternalSymbolName::ExportEquals.as_ref())
                && self.export_matches(store, exported, symbol)?
            {
                return Ok(Some((module, None)));
            }
            if let Some(exported) = table.get(record.name())
                && self.export_matches(store, exported, symbol)?
            {
                return Ok(Some((module, Some(exported))));
            }
            let mut candidates = Vec::new();
            for (_, exported) in table.iter() {
                let export = store
                    .symbol(exported)
                    .ok_or(SymbolDisplayError::InvalidSymbol(exported))?;
                if self.export_matches(store, exported, symbol)? {
                    if export.name() == InternalSymbolName::ExportEquals.as_ref() {
                        return Ok(Some((module, None)));
                    }
                    candidates.push(exported);
                }
            }
            candidates.sort_by(|left, right| self.compare_symbols(store, host, *left, *right));
            if let Some(exported) = candidates.first() {
                return Ok(Some((module, Some(*exported))));
            }
        }
        Ok(None)
    }

    fn export_matches(
        &self,
        store: &CanonicalTypeMapperStore,
        exported: SemanticSymbolId,
        requested: SemanticSymbolId,
    ) -> Result<bool, SymbolDisplayError> {
        if store
            .symbol(exported)
            .ok_or(SymbolDisplayError::InvalidSymbol(exported))?
            .flags()
            .intersects(SymbolFlags::ALIAS)
        {
            let target = self
                .aliases
                .get(&exported)
                .copied()
                .ok_or(SymbolDisplayError::UnnameableSymbol(requested))??;
            target
                .reference()
                .map(|target| same_reference(store, target, requested))
                .transpose()
                .map(|matched| matched.unwrap_or(false))
        } else {
            same_reference(store, exported, requested)
        }
    }

    pub(super) fn enclosing(&self) -> NodeRef {
        self.enclosing
    }

    fn accessible_chain(
        &self,
        store: &CanonicalTypeMapperStore,
        host: &DeclaredTypeHost<'_>,
        symbol: SemanticSymbolId,
        meaning: SymbolFlags,
        visited: &mut VisitedTables,
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
        let globals = *self.scopes.last().expect("scope lookup includes globals");
        let ScopeEntries::Table(globals_id) = globals.entries else {
            return Err(SymbolDisplayError::InvalidLocation(self.enclosing));
        };
        let global_this = store
            .intrinsic_bootstrap()
            .ok_or(SymbolDisplayError::InvalidTable(globals_id))?
            .global_this_symbol;
        if store.symbol(global_this).is_none_or(|record| {
            record.name().as_utf8() != Some("globalThis") || record.exports() != Some(globals_id)
        }) {
            return Err(SymbolDisplayError::InvalidSymbol(global_this));
        }
        if symbol != global_this {
            // globalThis exports the global table. A qualified visit must not
            // collide with the same table's lexical visit when a name is hidden.
            let mut chain =
                self.chain_in_table(store, host, symbol, meaning, globals, true, visited)?;
            if !chain.is_empty()
                && self.can_qualify(store, host, global_this, left_meaning(meaning), visited)?
            {
                chain.insert(0, global_this);
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
        visited: &mut VisitedTables,
    ) -> Result<Vec<SemanticSymbolId>, SymbolDisplayError> {
        if !visited.insert((symbol, scope.entries, ignore_qualification)) {
            return Ok(Vec::new());
        }
        let result = (|| {
            let target = store
                .symbol(symbol)
                .ok_or(SymbolDisplayError::InvalidSymbol(symbol))?;
            let table = match scope.entries {
                ScopeEntries::Table(id) => Some(
                    store
                        .symbol_table(id)
                        .ok_or(SymbolDisplayError::InvalidTable(id))?,
                ),
                ScopeEntries::ClassExpressionName(_) => None,
            };
            let direct = match scope.entries {
                ScopeEntries::Table(_) => table.and_then(|table| table.get(target.name())),
                ScopeEntries::ClassExpressionName(owner) => {
                    let name = class_expression_name(store, host, owner)?
                        .ok_or(SymbolDisplayError::InvalidSymbol(owner))?;
                    (target.name().as_utf8() == Some(name)).then_some(owner)
                }
            };
            if let Some(direct) = direct.filter(|direct| in_scope(store, scope, *direct))
                && (same_reference(store, direct, symbol)?
                    || store
                        .symbol(direct)
                        .and_then(ts_binder::semantic::Symbol::export_symbol)
                        .is_some_and(|export| {
                            same_reference(store, export, symbol).unwrap_or(false)
                        }))
                && !is_external_module(store, host, direct)?
                && (ignore_qualification
                    || self.can_qualify(store, host, direct, meaning, visited)?)
            {
                return Ok(vec![symbol]);
            }
            let Some(table) = table else {
                return Ok(Vec::new());
            };
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
                if same_reference(store, alias, symbol)?
                    || imported
                        .reference()
                        .map(|target| same_reference(store, target, symbol))
                        .transpose()?
                        .unwrap_or(false)
                {
                    if ignore_qualification
                        || self.can_qualify(store, host, alias, meaning, visited)?
                    {
                        candidates.push(vec![alias]);
                    }
                    continue;
                }
                if let Some(exports) = display_alias_exports(store, host, alias, imported)? {
                    let mut child = self.chain_in_table(
                        store,
                        host,
                        symbol,
                        meaning,
                        ScopeTable {
                            entries: ScopeEntries::Table(exports),
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
        visited.remove(&(symbol, scope.entries, ignore_qualification));
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
            let candidate = match scope.entries {
                ScopeEntries::Table(id) => store
                    .symbol_table(id)
                    .ok_or(SymbolDisplayError::InvalidTable(id))?
                    .get(record.name()),
                ScopeEntries::ClassExpressionName(owner) => {
                    let name = class_expression_name(store, host, owner)?
                        .ok_or(SymbolDisplayError::InvalidSymbol(owner))?;
                    (record.name().as_utf8() == Some(name)).then_some(owner)
                }
            };
            let Some(raw) = candidate.filter(|candidate| in_scope(store, *scope, *candidate))
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
                let target = self.alias_target(candidate)?.exports_owner();
                if meaning == SymbolFlags::NAMESPACE {
                    merged_export_assignment_namespace(store, host, candidate, target)?
                        .unwrap_or(target)
                } else {
                    target
                }
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
        visited: &mut VisitedTables,
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
    ) -> Result<DisplayAliasTarget, SymbolDisplayError> {
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
        specifiers: &BTreeMap<(FileId, SemanticSymbolId), String>,
    ) {
        for ((file, symbol), specifier) in specifiers {
            if *file != self.enclosing.file {
                continue;
            }
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
                entries: ScopeEntries::Table(id),
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
                if let Some(id) = store
                    .symbol(owner)
                    .and_then(ts_binder::semantic::Symbol::exports)
                {
                    tables.push(ScopeTable {
                        entries: ScopeEntries::Table(id),
                        types_only: false,
                        local: true,
                    });
                }
            }
            SyntaxKind::ClassDeclaration
            | SyntaxKind::ClassExpression
            | SyntaxKind::InterfaceDeclaration => {
                let owner = owner.ok_or(SymbolDisplayError::InvalidLocation(node))?;
                if let Some(id) = store
                    .symbol(owner)
                    .and_then(ts_binder::semantic::Symbol::members)
                {
                    tables.push(ScopeTable {
                        entries: ScopeEntries::Table(id),
                        types_only: true,
                        local: false,
                    });
                }
                if matches!(&record.data, NodeData::ClassExpression(class) if class.name.is_some())
                {
                    class_expression_name(store, host, owner)?
                        .ok_or(SymbolDisplayError::InvalidSymbol(owner))?;
                    tables.push(ScopeTable {
                        entries: ScopeEntries::ClassExpressionName(owner),
                        types_only: false,
                        local: true,
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
        entries: ScopeEntries::Table(globals),
        types_only: false,
        local: true,
    });
    for scope in &tables {
        if let ScopeEntries::Table(id) = scope.entries
            && store.symbol_table(id).is_none()
        {
            return Err(SymbolDisplayError::InvalidTable(id));
        }
    }
    Ok(tables)
}

fn class_expression_name<'store>(
    store: &'store CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    symbol: SemanticSymbolId,
) -> Result<Option<&'store str>, SymbolDisplayError> {
    let invalid = || SymbolDisplayError::InvalidSymbol(symbol);
    let record = store.symbol(symbol).ok_or_else(invalid)?;
    let Some([declaration]) = record.declarations() else {
        return Ok(None);
    };
    let Some(NodeData::ClassExpression(class)) = host.node(*declaration).map(|node| &node.data)
    else {
        return Ok(None);
    };
    let Some(name) = class.name else {
        return Ok(None);
    };
    let name = NodeRef::new(declaration.arena, declaration.file, name);
    let source = host.node(name).ok_or_else(invalid)?;
    let NodeData::Identifier(identifier) = &source.data else {
        return Err(invalid());
    };
    if record.flags() != SymbolFlags::CLASS
        || record.check_flags() != ts_binder::CheckFlags::NONE
        || record.value_declaration() != Some(*declaration)
        || record.parent().is_some()
        || record.export_symbol().is_some()
        || store.get_merged_symbol(symbol) != Some(symbol)
        || !host.symbol_matches(store, *declaration, symbol)
        || !store.source_declaration_belongs_to_symbol(*declaration, symbol)
        || source.parent != Some(declaration.node)
        || identifier.text.is_empty()
        || record.name().as_utf8() != Some(identifier.text.as_str())
    {
        return Err(invalid());
    }
    Ok(record.name().as_utf8())
}

fn checked_alias_target(
    store: &mut CanonicalTypeMapperStore,
    host: &mut ProductionAliasTargetHost<'_, '_, '_>,
    alias: SemanticSymbolId,
    visiting: &mut HashSet<SemanticSymbolId>,
) -> Result<DisplayAliasTarget, SymbolDisplayError> {
    if !visiting.insert(alias) {
        return Err(SymbolDisplayError::CyclicAlias(alias));
    }
    let original = store.alias_symbol_links(alias).cloned();
    if !store.ensure_alias_symbol_links(alias) {
        return Err(SymbolDisplayError::InvalidAliasCache(alias));
    }
    let result = (|| {
        let (immediate, type_only) = host
            .get_display_target_and_type_only(store, alias)
            .map_err(|reason| {
                SymbolDisplayError::Alias(CanonicalAliasResolutionError::TargetUnavailable {
                    alias,
                    reason,
                })
            })?;
        let immediate = match immediate {
            DisplayAliasTarget::Namespace(namespace) => {
                if original.as_ref().is_some_and(|links| {
                    links.immediate_target.is_some()
                        || links.alias_target != AliasTargetState::Unresolved
                        || links.type_only_declaration != type_only
                }) {
                    return Err(SymbolDisplayError::InvalidAliasCache(alias));
                }
                return Ok(DisplayAliasTarget::Namespace(namespace));
            }
            DisplayAliasTarget::Symbol(symbol) => symbol,
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
            match checked_alias_target(store, host, immediate, visiting)? {
                DisplayAliasTarget::Symbol(target) => DisplayAliasTarget::Symbol(
                    store
                        .get_merged_symbol(target)
                        .ok_or(SymbolDisplayError::InvalidSymbol(target))?,
                ),
                namespace @ DisplayAliasTarget::Namespace(_) => namespace,
            }
        } else {
            DisplayAliasTarget::Symbol(immediate)
        };
        let inherited_type_only = store
            .alias_symbol_links(immediate)
            .and_then(|links| links.type_only_declaration);
        let expected_target = target
            .reference()
            .map_or(AliasTargetState::Unresolved, AliasTargetState::Resolved);
        let expected_type_only = type_only.or(inherited_type_only);
        if let Some(original) = &original
            && (original
                .immediate_target
                .is_some_and(|cached| cached != immediate)
                || original.alias_target != AliasTargetState::Unresolved
                    && original.alias_target != expected_target
                || original
                    .type_only_declaration
                    .is_some_and(|cached| Some(cached) != expected_type_only)
                || original.alias_target != AliasTargetState::Unresolved
                    && original.type_only_declaration != expected_type_only)
        {
            return Err(SymbolDisplayError::InvalidAliasCache(alias));
        }
        if matches!(target, DisplayAliasTarget::Namespace(_)) {
            let mut links = store
                .alias_symbol_links(alias)
                .cloned()
                .ok_or(SymbolDisplayError::InvalidAliasCache(alias))?;
            links.type_only_declaration = expected_type_only;
            if !store.set_alias_symbol_links(alias, links) {
                return Err(SymbolDisplayError::InvalidAliasCache(alias));
            }
            return Ok(target);
        }
        let resolved = CanonicalAliasResolver::new(store, host)
            .resolve_alias(alias)
            .map_err(SymbolDisplayError::Alias)?;
        if resolved.target != expected_target {
            return Err(SymbolDisplayError::InvalidAliasCache(alias));
        }
        Ok(target)
    })();
    visiting.remove(&alias);
    result
}

fn display_alias_exports(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    alias: SemanticSymbolId,
    target: DisplayAliasTarget,
) -> Result<Option<SymbolTableId>, SymbolDisplayError> {
    match target {
        DisplayAliasTarget::Symbol(symbol) => {
            if let Some(table) = exports(store, symbol)? {
                return Ok(Some(table));
            }
            let Some(namespace) = merged_export_assignment_namespace(store, host, alias, symbol)?
            else {
                return Ok(None);
            };
            exports(store, namespace)
        }
        DisplayAliasTarget::Namespace(symbol) => {
            let table = store
                .symbol(symbol)
                .ok_or(SymbolDisplayError::InvalidSymbol(symbol))?
                .exports();
            if let Some(table) = table
                && store.symbol_table(table).is_none()
            {
                return Err(SymbolDisplayError::InvalidTable(table));
            }
            Ok(table)
        }
    }
}

/// Reads the type-export namespace without changing an import's value target.
fn merged_export_assignment_namespace(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    alias: SemanticSymbolId,
    target: SemanticSymbolId,
) -> Result<Option<SemanticSymbolId>, SymbolDisplayError> {
    let invalid = || SymbolDisplayError::InvalidSymbol(alias);
    let target_record = store.symbol(target).ok_or_else(invalid)?;
    if target_record.name() != InternalSymbolName::ExportEquals.as_ref()
        || target_record.flags() != SymbolFlags::PROPERTY
            && target_record.flags() != SymbolFlags::PROPERTY | SymbolFlags::NAMESPACE_MODULE
    {
        return Ok(None);
    }
    let alias_record = store.symbol(alias).ok_or_else(invalid)?;
    let Some([declaration]) = alias_record.declarations() else {
        return Ok(None);
    };
    let Some(NodeData::ImportEqualsDeclaration(import)) =
        host.node(*declaration).map(|record| &record.data)
    else {
        return Ok(None);
    };
    if alias_record.flags() != SymbolFlags::ALIAS
        || store.get_merged_symbol(alias) != Some(alias)
        || !host.symbol_matches(store, *declaration, alias)
    {
        return Err(invalid());
    }
    let reference = NodeRef::new(declaration.arena, declaration.file, import.module_reference);
    if !matches!(
        host.node(reference).map(|record| &record.data),
        Some(NodeData::ExternalModuleReference(_))
    ) {
        return Ok(None);
    }
    let name = NodeRef::new(declaration.arena, declaration.file, import.name);
    let mut resolver = host.name_resolver_host(store).map_err(|_| invalid())?;
    let Some(namespace) = resolver
        .resolve_entity_name(name, SymbolFlags::NAMESPACE)
        .map_err(|_| invalid())?
    else {
        return Ok(None);
    };
    if store.get_parent_of_symbol(target) != Some(namespace) {
        return Ok(None);
    }
    validate_symbol(store, host, namespace)?;
    let Some(table) = exports(store, namespace)? else {
        return Ok(None);
    };
    let members = store
        .symbol_table(table)
        .ok_or(SymbolDisplayError::InvalidTable(table))?;
    if members.get(InternalSymbolName::ExportEquals.as_ref()) != Some(target)
        || members.iter().any(|(name, member)| {
            if name == InternalSymbolName::ExportEquals.as_ref() {
                return member != target;
            }
            store.symbol(member).is_none_or(|record| {
                !record
                    .flags()
                    .intersects(SymbolFlags::TYPE | SymbolFlags::NAMESPACE)
                    || record.flags().intersects(SymbolFlags::ASSIGNMENT)
            })
        })
    {
        return Ok(None);
    }
    Ok(Some(namespace))
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

/// Returns the proved source symbol for declaration and parent matching.
fn validate_symbol(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    symbol: SemanticSymbolId,
) -> Result<SemanticSymbolId, SymbolDisplayError> {
    let record = store
        .symbol(symbol)
        .ok_or(SymbolDisplayError::InvalidSymbol(symbol))?;
    let canonical = store
        .get_merged_symbol(symbol)
        .ok_or(SymbolDisplayError::InvalidSymbol(symbol))?;
    if let Some(wrapper) = store.source_file_namespace_wrapper_for_module(symbol) {
        if canonical != symbol
            || !super::alias_provider::source_file_namespace_wrapper_is_exact(store, wrapper)
        {
            return Err(SymbolDisplayError::InvalidSymbol(symbol));
        }
        // A namespace wrapper shares source declarations but keeps its own aliases.
        validate_symbol(store, host, wrapper.source.module)?;
        validate_symbol(store, host, wrapper.source.alias)?;
        return Ok(symbol);
    }
    // Namespace wrappers reuse exports. They do not own source declarations.
    if store.get_parent_of_symbol(symbol).is_some_and(|parent| {
        store
            .source_file_namespace_wrapper_for_module(parent)
            .is_some()
    }) {
        return Err(SymbolDisplayError::InvalidSymbol(symbol));
    }
    if record.flags().contains(SymbolFlags::CLASS)
        && record.declarations().is_none_or(<[NodeRef]>::is_empty)
    {
        return Err(SymbolDisplayError::InvalidSymbol(symbol));
    }
    if let Some([declaration]) = record.declarations()
        && matches!(host.node(*declaration).map(|node| &node.data),
            Some(NodeData::ClassExpression(class)) if class.name.is_some())
    {
        class_expression_name(store, host, symbol)?
            .ok_or(SymbolDisplayError::InvalidSymbol(symbol))?;
    }
    // Union properties share declarations without being object-literal clones.
    // Prove their cache before the clone validator rejects shared declarations.
    if let Some(source) =
        super::member_resolution::published_union_property_source(store, host, symbol)
            .map_err(|_| SymbolDisplayError::InvalidSymbol(symbol))?
    {
        return Ok(source);
    }
    let source = object_literal_property_source(store, host, symbol)?;
    if canonical != symbol {
        super::member_resolution::published_union_property_source(store, host, canonical)
            .map_err(|_| SymbolDisplayError::InvalidSymbol(canonical))?;
        object_literal_property_source(store, host, canonical)?;
    }
    if let Some(source) = source {
        return Ok(source);
    }
    if record
        .declarations()
        .unwrap_or_default()
        .iter()
        .all(|declaration| {
            host.node(*declaration).is_some() && host.symbol_matches(store, *declaration, canonical)
        })
    {
        Ok(symbol)
    } else {
        Err(SymbolDisplayError::InvalidSymbol(symbol))
    }
}

/// Proves an object-literal clone against the source retained at publication.
fn object_literal_property_source(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    symbol: SemanticSymbolId,
) -> Result<Option<SemanticSymbolId>, SymbolDisplayError> {
    let record = store
        .symbol(symbol)
        .ok_or(SymbolDisplayError::InvalidSymbol(symbol))?;
    let Some(origin) = store.object_literal_property_clone_origin(symbol) else {
        let object_declaration =
            record
                .declarations()
                .unwrap_or_default()
                .iter()
                .find_map(|declaration| {
                    if host.bound_file(*declaration)?.symbol(*declaration)? == symbol {
                        return None;
                    }
                    let owner = NodeRef::new(
                        declaration.arena,
                        declaration.file,
                        host.node(*declaration)?.parent?,
                    );
                    (store.source_node_kind(owner) == Some(SyntaxKind::ObjectLiteralExpression))
                        .then_some(owner)
                });
        return if object_declaration.is_some() {
            Err(SymbolDisplayError::InvalidSymbol(symbol))
        } else {
            Ok(None)
        };
    };
    let source = (|| {
        let plan = super::object_members::plan_object_literal(store, host, origin.owner()).ok()?;
        let state = super::object_members::object_literal_state(store, &plan).ok()??;
        if !state.is_resolved() {
            return None;
        }
        let members = store.type_payload(state.type_id())?.data().structured()?;
        if !members.properties.as_ref()?.contains(&symbol)
            || store.symbol_table(members.members?)?.get(record.name()) != Some(symbol)
        {
            return None;
        }
        let target = store.value_symbol_links(symbol)?.target?;
        (target == origin.source()
            && plan
                .properties
                .iter()
                .any(|property| property.symbol == origin.source()))
        .then_some(origin.source())
    })();
    source
        .map(Some)
        .ok_or(SymbolDisplayError::InvalidSymbol(symbol))
}

fn validated_parent(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    symbol: SemanticSymbolId,
) -> Result<Option<SemanticSymbolId>, SymbolDisplayError> {
    let source = validate_symbol(store, host, symbol)?;
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
                .is_some_and(|candidate| same_reference(store, candidate, source).unwrap_or(false))
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

pub(super) fn written_default_name(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    symbol: SemanticSymbolId,
    enclosing: NodeRef,
    initial: bool,
    use_alias_outside_scope: bool,
) -> Result<Option<String>, SymbolDisplayError> {
    let record = store
        .symbol(symbol)
        .ok_or(SymbolDisplayError::InvalidSymbol(symbol))?;
    if record.name() != InternalSymbolName::Default.as_ref()
        || !record
            .flags()
            .intersects(SymbolFlags::FUNCTION | SymbolFlags::CLASS | SymbolFlags::INTERFACE)
    {
        return Ok(None);
    }
    let declarations = record.declarations().unwrap_or_default();
    if !use_alias_outside_scope
        && (!initial
            || declarations.is_empty()
            || binding_context(host, declarations[0])? != binding_context(host, enclosing)?)
    {
        return Ok(Some("default".to_owned()));
    }
    for declaration in declarations {
        let node = host
            .node(*declaration)
            .ok_or(SymbolDisplayError::InvalidLocation(*declaration))?;
        let name = match &node.data {
            NodeData::FunctionDeclaration(function) => function.name,
            NodeData::ClassDeclaration(class) => class.name,
            NodeData::InterfaceDeclaration(interface) => Some(interface.name),
            _ => None,
        };
        let Some(name) = name else { continue };
        let name = NodeRef::new(declaration.arena, declaration.file, name);
        let name_node = host
            .node(name)
            .ok_or(SymbolDisplayError::InvalidLocation(name))?;
        let NodeData::Identifier(identifier) = &name_node.data else {
            continue;
        };
        let written = host
            .source(name)
            .and_then(|(arena, _)| arena.source_text())
            .and_then(|text| {
                text.get(name_node.range.start.get() as usize..name_node.range.end.get() as usize)
            })
            .unwrap_or(&identifier.text);
        return Ok(Some(written.to_owned()));
    }
    Ok(None)
}

fn binding_context(
    host: &DeclaredTypeHost<'_>,
    mut node: NodeRef,
) -> Result<NodeRef, SymbolDisplayError> {
    let mut visited = HashSet::new();
    loop {
        if !visited.insert(node) {
            return Err(SymbolDisplayError::InvalidLocation(node));
        }
        let record = host
            .node(node)
            .ok_or(SymbolDisplayError::InvalidLocation(node))?;
        let ambient_module = if let NodeData::ModuleDeclaration(module) = &record.data {
            let name = NodeRef::new(node.arena, node.file, module.name);
            module.keyword == SyntaxKind::GlobalKeyword
                || host
                    .node(name)
                    .ok_or(SymbolDisplayError::InvalidLocation(name))?
                    .kind
                    == SyntaxKind::StringLiteral
        } else {
            false
        };
        if record.kind == SyntaxKind::SourceFile || ambient_module {
            return Ok(node);
        }
        node.node = record
            .parent
            .ok_or(SymbolDisplayError::InvalidLocation(node))?;
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::semantic::{
        CanonicalCheckerContext, CanonicalCheckerOptions, CanonicalModuleResolutionEntry,
        CanonicalModuleResolutionManifestInput, CanonicalModuleResolutionMode,
        CanonicalResolvedModuleInput, CanonicalUnionPropertyError, IntrinsicBootstrapOptions,
        RelationStateSnapshot, SymbolNodeLinks, TypeData, TypeDisplayUnavailable, TypeId,
        TypeNodeLinks, ValueSymbolLinks, types::ObjectFlags,
    };
    use ts_binder::{
        CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
        CheckFlags, EscapedName, SymbolData,
        semantic::{Symbol, SymbolTable},
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

    fn alias_declaration(parsed: &ParseResult, file: FileId, name: &str) -> NodeRef {
        parsed.arena.iter().find_map(|(id, record)| {
            let name_id = match &record.data {
                NodeData::ImportSpecifier(specifier) => specifier.name,
                NodeData::ExportSpecifier(specifier) => specifier.name,
                _ => return None,
            };
            matches!(&parsed.arena.get(name_id)?.data, NodeData::Identifier(identifier) if identifier.text == name)
                .then_some(NodeRef::new(parsed.arena.id(), file, id))
        }).unwrap()
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

    fn class_expression_context(parsed: &ParseResult, file: FileId) -> CanonicalCheckerContext<'_> {
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source("\"/class-expression.ts\""),
                    CanonicalSourceLanguage::TypeScript,
                    false,
                    CanonicalModuleState::Script,
                ),
            )
            .unwrap();
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
        CanonicalCheckerContext::new(
            binder.finish(),
            vec![(file, &parsed.arena)],
            CanonicalCheckerOptions::default(),
        )
        .unwrap()
    }

    struct UnionDisplayFixture<'arena> {
        context: CanonicalCheckerContext<'arena>,
        access: NodeRef,
        name: NodeRef,
        union: TypeId,
        property: SemanticSymbolId,
        sources: [SemanticSymbolId; 2],
    }

    fn union_display_fixture(parsed: &ParseResult, file: FileId) -> UnionDisplayFixture<'_> {
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source("\"/union-display.ts\""),
                    CanonicalSourceLanguage::TypeScript,
                    false,
                    CanonicalModuleState::Script,
                ),
            )
            .unwrap();
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
        let mut context = CanonicalCheckerContext::new(
            binder.finish(),
            vec![(file, &parsed.arena)],
            CanonicalCheckerOptions {
                intrinsic: IntrinsicBootstrapOptions {
                    strict_null_checks: true,
                    ..IntrinsicBootstrapOptions::default()
                },
                ..CanonicalCheckerOptions::default()
            },
        )
        .unwrap();
        context.check_source_file(file).unwrap();
        assert!(context.diagnostics().is_empty());
        let (access, name) = parsed
            .arena
            .iter()
            .find_map(|(id, record)| {
                let NodeData::PropertyAccessExpression(access) = &record.data else {
                    return None;
                };
                Some((
                    NodeRef::new(parsed.arena.id(), file, id),
                    NodeRef::new(parsed.arena.id(), file, access.name),
                ))
            })
            .unwrap();
        let property = context.get_symbol_at_location(access).unwrap().unwrap();
        let union = context
            .store()
            .value_symbol_links(property)
            .unwrap()
            .containing_type
            .unwrap();
        let TypeData::Union(data) = context.store().type_payload(union).unwrap().data() else {
            panic!("the property must retain its containing union")
        };
        let sources = data
            .union
            .types
            .iter()
            .map(|type_| {
                let members = context
                    .store()
                    .type_payload(*type_)
                    .unwrap()
                    .data()
                    .structured()
                    .unwrap()
                    .members
                    .unwrap();
                context
                    .store()
                    .symbol_table(members)
                    .unwrap()
                    .get(context.store().symbol(property).unwrap().name())
                    .unwrap()
            })
            .collect::<Vec<_>>();
        UnionDisplayFixture {
            context,
            access,
            name,
            union,
            property,
            sources: sources.try_into().unwrap(),
        }
    }

    #[derive(Debug, Eq, PartialEq)]
    struct UnionDisplayState {
        counts: [usize; 6],
        link_lengths: [usize; 26],
        types: Vec<(TypeId, String)>,
        symbols: Vec<(
            SemanticSymbolId,
            Symbol,
            Option<ValueSymbolLinks>,
            Option<SemanticSymbolId>,
        )>,
        tables: Vec<(SymbolTableId, SymbolTable)>,
        nodes: Vec<(NodeRef, Option<TypeNodeLinks>, Option<SymbolNodeLinks>)>,
        relations: RelationStateSnapshot,
    }

    fn union_display_state(
        context: &CanonicalCheckerContext<'_>,
        parsed: &ParseResult,
        file: FileId,
    ) -> UnionDisplayState {
        let store = context.store();
        let mut tables = vec![store.intrinsic_bootstrap().unwrap().globals];
        for (_, record) in store.types() {
            tables.extend(record.data().structured().and_then(|data| data.members));
            if let TypeData::Union(data) = record.data() {
                tables.extend(data.union.property_cache);
                tables.extend(data.union.property_cache_without_function_property_augment);
            }
        }
        for (_, record) in store.symbol_store().symbols() {
            tables.extend(record.members());
            tables.extend(record.exports());
        }
        tables.sort_unstable();
        tables.dedup();
        UnionDisplayState {
            counts: [
                store.type_len(),
                store.symbol_len(),
                store.symbol_store().symbol_table_len(),
                store.signature_len(),
                store.mapper_len(),
                store.index_info_len(),
            ],
            link_lengths: store.checker_link_allocated_lengths(),
            types: store
                .types()
                .map(|(id, record)| (id, format!("{record:?}")))
                .collect(),
            symbols: store
                .symbol_store()
                .symbols()
                .map(|(id, record)| {
                    (
                        id,
                        record.clone(),
                        store.value_symbol_links(id).cloned(),
                        store.get_merged_symbol(id),
                    )
                })
                .collect(),
            tables: tables
                .into_iter()
                .map(|id| (id, store.symbol_table(id).unwrap().clone()))
                .collect(),
            nodes: parsed
                .arena
                .iter()
                .map(|(id, _)| {
                    let node = NodeRef::new(parsed.arena.id(), file, id);
                    (
                        node,
                        store.type_node_links(node).cloned(),
                        store.symbol_node_links(node).cloned(),
                    )
                })
                .collect(),
            relations: store.relation_state_snapshot(),
        }
    }

    #[test]
    fn location_display_retains_published_union_property_identity_and_declarations() {
        for (name, source) in [
            (
                "msg",
                concat!(
                    "type Left = { msg?: undefined }; type Right = { msg: string }; ",
                    "function read(input: Left | Right): string | undefined { return input.msg; }",
                ),
            ),
            (
                "msg",
                concat!(
                    "interface Left { readonly msg: string } type Right = { msg: number }; ",
                    "function read(input: Left | Right): string | number { return input.msg; }",
                ),
            ),
            (
                "__msg",
                concat!(
                    "type Left = { __msg: string }; type Right = { __msg: number }; ",
                    "function read(input: Left | Right): string | number { return input.__msg; }",
                ),
            ),
        ] {
            let parsed = parse_source_file(source);
            let file = FileId::new(41_023);
            let mut fixture = union_display_fixture(&parsed, file);
            let declarations = fixture.sources.map(|source| {
                assert_ne!(source, fixture.property);
                fixture.context.get_symbol_declarations(source).unwrap()[0]
            });
            assert_ne!(declarations[0], declarations[1]);
            assert_eq!(
                fixture
                    .context
                    .get_symbol_declarations(fixture.property)
                    .unwrap(),
                declarations
            );
            let before = union_display_state(&fixture.context, &parsed, file);
            for _ in 0..2 {
                for location in [fixture.access, fixture.name] {
                    assert_eq!(
                        fixture.context.get_symbol_at_location(location).unwrap(),
                        Some(fixture.property)
                    );
                    assert_eq!(
                        fixture
                            .context
                            .symbol_to_string_at_location(fixture.property, location)
                            .unwrap(),
                        name
                    );
                    assert_eq!(
                        fixture
                            .context
                            .get_symbol_declarations(fixture.property)
                            .unwrap(),
                        declarations
                    );
                }
                assert_eq!(union_display_state(&fixture.context, &parsed, file), before);
            }
        }
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Keep publication, absent-member validation, and replay together.
    fn location_display_retains_raw_partial_union_property_with_transient_absence() {
        let parsed = parse_source_file("");
        let file = FileId::new(41_027);
        let mut context = class_expression_context(&parsed, file);
        let enclosing = NodeRef::new(parsed.arena.id(), file, parsed.source_file);
        let store = context.store_mut_for_test();
        let number = store.intrinsic_bootstrap().unwrap().number_type;
        let value = store
            .alloc_symbol(SymbolData::new(
                SymbolFlags::PROPERTY,
                EscapedName::source("value"),
            ))
            .unwrap();
        let other = store.alloc_transient_symbol(
            SymbolFlags::PROPERTY,
            EscapedName::source("other"),
            CheckFlags::NONE,
        );
        let links = ValueSymbolLinks {
            resolved_type: Some(number),
            ..ValueSymbolLinks::default()
        };
        let mut objects = Vec::new();
        for property in [value, other] {
            assert!(store.set_value_symbol_links(property, links.clone()));
            let object = store
                .alloc_plain_object_type(ObjectFlags::ANONYMOUS, None)
                .unwrap();
            let table = store.alloc_symbol_table();
            let name = store.symbol(property).unwrap().name().to_owned();
            assert_eq!(store.insert_symbol(table, name, property), Some(None));
            assert!(store.set_structured_type_members(
                object,
                Some(table),
                Some(vec![property]),
                None,
                None,
                None
            ));
            objects.push(object);
        }
        objects.sort_unstable();
        let union = store.alloc_union_type(ObjectFlags::NONE, objects).unwrap();
        assert_eq!(context.get_union_property(union, "value"), Ok(None));
        let TypeData::Union(data) = context.store().type_payload(union).unwrap().data() else {
            panic!("the receiver must retain the union")
        };
        let cache = data
            .union
            .property_cache
            .expect("a partial lookup publishes its property cache");
        let property = context
            .store()
            .symbol_table(cache)
            .unwrap()
            .get_source("value")
            .unwrap();
        assert_ne!(property, value);
        assert_ne!(property, other);
        let record = context.store().symbol(property).unwrap();
        assert_eq!(
            record.flags(),
            SymbolFlags::PROPERTY | SymbolFlags::TRANSIENT
        );
        assert_eq!(
            record.check_flags(),
            CheckFlags::SYNTHETIC_PROPERTY | CheckFlags::CONTAINS_PUBLIC | CheckFlags::READ_PARTIAL
        );
        assert!(record.declarations().is_none());
        assert_eq!(
            context.store().value_symbol_links(property),
            Some(&ValueSymbolLinks {
                resolved_type: Some(number),
                containing_type: Some(union),
                ..ValueSymbolLinks::default()
            })
        );
        let published = union_display_state(&context, &parsed, file);

        for _ in 0..2 {
            assert_eq!(
                context
                    .symbol_to_string_at_location(property, enclosing)
                    .unwrap(),
                "value"
            );
            assert!(
                context
                    .get_symbol_declarations(property)
                    .unwrap()
                    .is_empty()
            );
            assert_eq!(union_display_state(&context, &parsed, file), published);
            assert_eq!(context.get_union_property(union, "value"), Ok(None));
            assert_eq!(
                context
                    .store()
                    .symbol_table(cache)
                    .unwrap()
                    .get_source("value"),
                Some(property)
            );
            assert_eq!(union_display_state(&context, &parsed, file), published);
        }
        assert_eq!(
            context.get_union_property(union, "other"),
            Err(CanonicalUnionPropertyError::InvalidProperty(other))
        );
        assert_eq!(union_display_state(&context, &parsed, file), published);

        let mut changed = links.clone();
        changed.target = Some(value);
        assert!(
            context
                .store_mut_for_test()
                .set_value_symbol_links(other, changed)
        );
        let damaged = union_display_state(&context, &parsed, file);
        for _ in 0..2 {
            assert!(matches!(
                context.symbol_to_string_at_location(property, enclosing),
                Err(crate::semantic::artifact_queries::CanonicalArtifactQueryError::SymbolDisplay(
                    SymbolDisplayError::InvalidSymbol(symbol)
                )) if symbol == property
            ));
            assert_eq!(union_display_state(&context, &parsed, file), damaged);
        }
        assert!(
            context
                .store_mut_for_test()
                .set_value_symbol_links(other, links)
        );
        assert_eq!(
            context
                .symbol_to_string_at_location(property, enclosing)
                .unwrap(),
            "value"
        );
        assert_eq!(context.get_union_property(union, "value"), Ok(None));
        assert_eq!(union_display_state(&context, &parsed, file), published);
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Keep each changed field beside its exact restoration.
    fn location_display_rejects_changed_union_properties_without_writes() {
        #[derive(Clone, Copy, Debug)]
        enum Damage {
            Flags,
            CheckFlags,
            DeclarationOrder,
            MissingDeclarations,
            ValueDeclaration,
            Parent,
            MissingContainingType,
            WrongContainingType,
            ResolvedType,
            MissingCache,
            CacheEntry,
            SourceDeclaration,
            SourceParent,
            SourceType,
            SourceMembers,
        }
        let parsed = parse_source_file(concat!(
            "type Left = { msg?: undefined }; type Right = { msg: string }; ",
            "function read(input: Left | Right): string | undefined { return input.msg; }",
        ));
        let file = FileId::new(41_024);
        let mut fixture = union_display_fixture(&parsed, file);
        let property = fixture.property;
        let source = fixture.sources[0];
        let original = fixture.context.store().symbol(property).unwrap().clone();
        let original_links = fixture
            .context
            .store()
            .value_symbol_links(property)
            .unwrap()
            .clone();
        let source_record = fixture.context.store().symbol(source).unwrap().clone();
        let source_links = fixture
            .context
            .store()
            .value_symbol_links(source)
            .unwrap()
            .clone();
        let other = fixture
            .context
            .store()
            .symbol(fixture.sources[1])
            .unwrap()
            .clone();
        let TypeData::Union(union) = fixture
            .context
            .store()
            .type_payload(fixture.union)
            .unwrap()
            .data()
        else {
            panic!("the receiver must remain a union")
        };
        let union = union.clone();
        let cache = union.union.property_cache.unwrap();
        let owner = source_record.parent().unwrap();
        let source_members = fixture
            .context
            .store()
            .symbol(owner)
            .unwrap()
            .members()
            .unwrap();
        let wrong_type = fixture
            .context
            .store()
            .intrinsic_bootstrap()
            .unwrap()
            .number_type;
        let before = union_display_state(&fixture.context, &parsed, file);
        for damage in [
            Damage::Flags,
            Damage::CheckFlags,
            Damage::DeclarationOrder,
            Damage::MissingDeclarations,
            Damage::ValueDeclaration,
            Damage::Parent,
            Damage::MissingContainingType,
            Damage::WrongContainingType,
            Damage::ResolvedType,
            Damage::MissingCache,
            Damage::CacheEntry,
            Damage::SourceDeclaration,
            Damage::SourceParent,
            Damage::SourceType,
            Damage::SourceMembers,
        ] {
            let store = fixture.context.store_mut_for_test();
            match damage {
                Damage::Flags => assert!(store.set_symbol_flags(
                    property,
                    SymbolFlags::PROPERTY,
                    original.check_flags()
                )),
                Damage::CheckFlags => {
                    assert!(store.set_symbol_flags(property, original.flags(), CheckFlags::NONE))
                }
                Damage::DeclarationOrder => {
                    let mut declarations = original.declarations().unwrap().to_vec();
                    declarations.reverse();
                    assert!(store.set_symbol_declarations(property, Some(declarations), None));
                }
                Damage::MissingDeclarations => {
                    assert!(store.set_symbol_declarations(property, None, None))
                }
                Damage::ValueDeclaration => assert!(store.set_symbol_declarations(
                    property,
                    original.declarations().map(<[NodeRef]>::to_vec),
                    source_record.value_declaration()
                )),
                Damage::Parent => {
                    assert!(store.set_symbol_relationships(property, None, None, Some(owner), None))
                }
                Damage::MissingContainingType
                | Damage::WrongContainingType
                | Damage::ResolvedType => {
                    let mut links = original_links.clone();
                    match damage {
                        Damage::MissingContainingType => links.containing_type = None,
                        Damage::WrongContainingType => {
                            links.containing_type = Some(union.union.types[0])
                        }
                        Damage::ResolvedType => links.resolved_type = Some(wrong_type),
                        _ => unreachable!(),
                    }
                    assert!(store.set_value_symbol_links(property, links));
                }
                Damage::MissingCache => {
                    assert!(store.set_union_or_intersection_caches(fixture.union, None, None, None))
                }
                Damage::CacheEntry => assert_eq!(
                    store.insert_symbol(cache, EscapedName::source("msg"), source),
                    Some(Some(property))
                ),
                Damage::SourceDeclaration => assert!(store.set_symbol_declarations(
                    source,
                    other.declarations().map(<[NodeRef]>::to_vec),
                    other.value_declaration()
                )),
                Damage::SourceParent => assert!(store.set_symbol_relationships(
                    source,
                    None,
                    None,
                    other.parent(),
                    None
                )),
                Damage::SourceType => {
                    let mut links = source_links.clone();
                    links.resolved_type = Some(wrong_type);
                    assert!(store.set_value_symbol_links(source, links));
                }
                Damage::SourceMembers => assert_eq!(
                    store.insert_symbol(
                        source_members,
                        EscapedName::source("msg"),
                        fixture.sources[1]
                    ),
                    Some(Some(source))
                ),
            }
            let damaged = union_display_state(&fixture.context, &parsed, file);
            for _ in 0..2 {
                let result = fixture
                    .context
                    .symbol_to_string_at_location(property, fixture.access);
                assert!(
                    matches!(
                        &result,
                        Err(crate::semantic::artifact_queries::CanonicalArtifactQueryError::SymbolDisplay(
                            SymbolDisplayError::InvalidSymbol(symbol)
                        )) if *symbol == property
                    ),
                    "damage {damage:?}: {result:?}"
                );
                assert_eq!(
                    union_display_state(&fixture.context, &parsed, file),
                    damaged,
                    "damage {damage:?}"
                );
            }
            let store = fixture.context.store_mut_for_test();
            assert!(store.set_symbol_flags(property, original.flags(), original.check_flags()));
            assert!(store.set_symbol_declarations(
                property,
                original.declarations().map(<[NodeRef]>::to_vec),
                original.value_declaration()
            ));
            assert!(store.set_symbol_relationships(
                property,
                original.members(),
                original.exports(),
                original.parent(),
                original.export_symbol()
            ));
            assert!(store.set_value_symbol_links(property, original_links.clone()));
            assert!(store.set_symbol_declarations(
                source,
                source_record.declarations().map(<[NodeRef]>::to_vec),
                source_record.value_declaration()
            ));
            assert!(store.set_symbol_relationships(
                source,
                source_record.members(),
                source_record.exports(),
                source_record.parent(),
                source_record.export_symbol()
            ));
            assert!(store.set_value_symbol_links(source, source_links.clone()));
            assert!(store.set_union_or_intersection_caches(
                fixture.union,
                union.union.property_cache,
                union.union.property_cache_without_function_property_augment,
                union.union.resolved_properties.clone()
            ));
            assert!(
                store
                    .insert_symbol(cache, EscapedName::source("msg"), property)
                    .is_some()
            );
            assert!(
                store
                    .insert_symbol(source_members, EscapedName::source("msg"), source)
                    .is_some()
            );
            assert_eq!(
                fixture
                    .context
                    .symbol_to_string_at_location(property, fixture.access)
                    .unwrap(),
                "msg"
            );
            assert_eq!(
                fixture
                    .context
                    .get_symbol_at_location(fixture.access)
                    .unwrap(),
                Some(property)
            );
            assert_eq!(
                fixture.context.get_symbol_declarations(property).unwrap(),
                original.declarations().unwrap()
            );
            assert_eq!(
                union_display_state(&fixture.context, &parsed, file),
                before,
                "restored {damage:?}"
            );
        }
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Keep the forged source and its restored member table together.
    fn location_display_rejects_union_sources_without_binder_ownership() {
        let parsed = parse_source_file(concat!(
            "type Left = { msg: string }; type Right = { msg: number }; ",
            "function read(input: Left | Right): string | number { return input.msg; }",
        ));
        let file = FileId::new(41_025);
        let mut fixture = union_display_fixture(&parsed, file);
        let source = fixture.sources[0];
        let original = fixture.context.store().symbol(source).unwrap().clone();
        let links = fixture
            .context
            .store()
            .value_symbol_links(source)
            .unwrap()
            .clone();
        let TypeData::Union(union) = fixture
            .context
            .store()
            .type_payload(fixture.union)
            .unwrap()
            .data()
        else {
            panic!("the receiver must remain a union")
        };
        let constituent = union.union.types[0];
        let members = fixture
            .context
            .store()
            .type_payload(constituent)
            .unwrap()
            .data()
            .structured()
            .unwrap()
            .clone();
        let table = members.members.unwrap();
        let store = fixture.context.store_mut_for_test();
        let forged = store
            .alloc_symbol(SymbolData::new(
                original.flags(),
                original.name().to_owned(),
            ))
            .unwrap();
        assert!(store.set_symbol_declarations(
            forged,
            original.declarations().map(<[NodeRef]>::to_vec),
            original.value_declaration()
        ));
        assert!(store.set_symbol_relationships(forged, None, None, original.parent(), None));
        assert!(store.set_value_symbol_links(forged, links));
        let before = union_display_state(&fixture.context, &parsed, file);
        let store = fixture.context.store_mut_for_test();
        assert_eq!(
            store.insert_symbol(table, EscapedName::source("msg"), forged),
            Some(Some(source))
        );
        assert!(store.set_structured_type_members(
            constituent,
            Some(table),
            Some(vec![forged]),
            None,
            None,
            None
        ));
        let damaged = union_display_state(&fixture.context, &parsed, file);
        for _ in 0..2 {
            for property in [fixture.property, forged] {
                assert!(matches!(
                    fixture.context.symbol_to_string_at_location(property, fixture.access),
                    Err(crate::semantic::artifact_queries::CanonicalArtifactQueryError::SymbolDisplay(
                        SymbolDisplayError::InvalidSymbol(symbol)
                    )) if symbol == property
                ));
            }
            assert_eq!(
                union_display_state(&fixture.context, &parsed, file),
                damaged
            );
        }
        let store = fixture.context.store_mut_for_test();
        assert_eq!(
            store.insert_symbol(table, EscapedName::source("msg"), source),
            Some(Some(forged))
        );
        assert!(store.set_structured_type_members(
            constituent,
            members.members,
            members.properties,
            None,
            None,
            members.index_infos
        ));
        assert_eq!(
            fixture
                .context
                .symbol_to_string_at_location(fixture.property, fixture.access)
                .unwrap(),
            "msg"
        );
        assert_eq!(
            fixture
                .context
                .get_symbol_at_location(fixture.access)
                .unwrap(),
            Some(fixture.property)
        );
        assert_eq!(union_display_state(&fixture.context, &parsed, file), before);
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Keep the competing producer claims and restoration together.
    fn location_display_rejects_object_literal_clones_claiming_union_publication() {
        let parsed = parse_source_file(concat!(
            "type Left = { msg: string }; type Right = { msg: number }; ",
            "function read(input: Left | Right): string | number { return input.msg; } ",
            "const object = { msg: 'local' };",
        ));
        let file = FileId::new(41_026);
        let mut fixture = union_display_fixture(&parsed, file);
        let object = parsed
            .arena
            .iter()
            .find_map(|(id, node)| {
                (node.kind == SyntaxKind::ObjectLiteralExpression).then_some(NodeRef::new(
                    parsed.arena.id(),
                    file,
                    id,
                ))
            })
            .unwrap();
        let object_type = fixture.context.get_type_at_location(object).unwrap();
        let members = fixture
            .context
            .store()
            .type_payload(object_type)
            .unwrap()
            .data()
            .structured()
            .unwrap()
            .members
            .unwrap();
        let clone = fixture
            .context
            .store()
            .symbol_table(members)
            .unwrap()
            .get_source("msg")
            .unwrap();
        let original = fixture.context.store().symbol(clone).unwrap().clone();
        let original_links = fixture
            .context
            .store()
            .value_symbol_links(clone)
            .unwrap()
            .clone();
        let origin = *fixture
            .context
            .store()
            .object_literal_property_clone_origin(clone)
            .unwrap();
        let union_property = fixture
            .context
            .store()
            .symbol(fixture.property)
            .unwrap()
            .clone();
        let union_links = fixture
            .context
            .store()
            .value_symbol_links(fixture.property)
            .unwrap()
            .clone();
        let TypeData::Union(union) = fixture
            .context
            .store()
            .type_payload(fixture.union)
            .unwrap()
            .data()
        else {
            panic!("the receiver must remain a union")
        };
        let cache = union.union.property_cache.unwrap();
        let before = union_display_state(&fixture.context, &parsed, file);
        let store = fixture.context.store_mut_for_test();
        assert!(store.set_symbol_flags(
            clone,
            union_property.flags(),
            union_property.check_flags()
        ));
        assert!(store.set_symbol_declarations(
            clone,
            union_property.declarations().map(<[NodeRef]>::to_vec),
            union_property.value_declaration()
        ));
        assert!(store.set_symbol_relationships(clone, None, None, None, None));
        assert!(store.set_value_symbol_links(clone, union_links));
        assert_eq!(
            store.insert_symbol(cache, EscapedName::source("msg"), clone),
            Some(Some(fixture.property))
        );
        let damaged = union_display_state(&fixture.context, &parsed, file);
        for _ in 0..2 {
            assert!(matches!(
                fixture.context.symbol_to_string_at_location(clone, fixture.access),
                Err(crate::semantic::artifact_queries::CanonicalArtifactQueryError::SymbolDisplay(
                    SymbolDisplayError::InvalidSymbol(symbol)
                )) if symbol == clone
            ));
            assert_eq!(
                union_display_state(&fixture.context, &parsed, file),
                damaged
            );
        }
        let store = fixture.context.store_mut_for_test();
        assert!(store.set_symbol_flags(clone, original.flags(), original.check_flags()));
        assert!(store.set_symbol_declarations(
            clone,
            original.declarations().map(<[NodeRef]>::to_vec),
            original.value_declaration()
        ));
        assert!(store.set_symbol_relationships(
            clone,
            original.members(),
            original.exports(),
            original.parent(),
            original.export_symbol()
        ));
        assert!(store.set_value_symbol_links(clone, original_links));
        assert_eq!(
            store.insert_symbol(cache, EscapedName::source("msg"), fixture.property),
            Some(Some(clone))
        );
        assert_eq!(
            fixture
                .context
                .symbol_to_string_at_location(clone, object)
                .unwrap(),
            "msg"
        );
        assert_eq!(
            fixture
                .context
                .symbol_to_string_at_location(fixture.property, fixture.access)
                .unwrap(),
            "msg"
        );
        assert_eq!(
            fixture
                .context
                .store()
                .object_literal_property_clone_origin(clone),
            Some(&origin)
        );
        assert_eq!(union_display_state(&fixture.context, &parsed, file), before);
    }

    #[test]
    fn named_class_expression_display_uses_a_read_only_self_binding() {
        let parsed = parse_source_file("class Shared {} const Holder = class Shared {};");
        assert!(parsed.diagnostics.is_empty());
        let file = FileId::new(41_031);
        let mut context = class_expression_context(&parsed, file);
        let outer = parsed
            .arena
            .iter()
            .find_map(|(id, record)| {
                matches!(record.data, NodeData::ClassDeclaration(_)).then_some(NodeRef::new(
                    parsed.arena.id(),
                    file,
                    id,
                ))
            })
            .unwrap();
        let (inner, name) = parsed
            .arena
            .iter()
            .find_map(|(id, record)| {
                let NodeData::ClassExpression(class) = &record.data else {
                    return None;
                };
                Some((
                    NodeRef::new(parsed.arena.id(), file, id),
                    NodeRef::new(parsed.arena.id(), file, class.name.unwrap()),
                ))
            })
            .unwrap();
        let outer_symbol = symbol(&context, outer);
        let inner_symbol = symbol(&context, inner);
        let outside = NodeRef::new(parsed.arena.id(), file, parsed.source_file);
        let bound = context.file(file).unwrap().1.clone();
        let host = DeclaredTypeHost::new([(&parsed.arena, &bound)]).unwrap();
        assert!(!context.module_resolutions().is_available());
        let manifest = CanonicalModuleResolutionManifest::unavailable();
        let globals = context.globals();
        let global_this = context
            .store()
            .intrinsic_bootstrap()
            .unwrap()
            .global_this_symbol;
        let mut aliases =
            ProductionAliasTargetHost::new(context.store(), [(&parsed.arena, &bound)], &manifest)
                .unwrap();
        let location = SymbolDisplayContext::new(
            context.store_mut_for_test(),
            &host,
            &mut aliases,
            &manifest,
            globals,
            &[file],
            name,
        )
        .unwrap();
        let before = (
            context.store().type_len(),
            context.store().symbol_len(),
            context.store().symbol_store().symbol_table_len(),
            context.store().checker_link_allocated_lengths(),
        );
        for _ in 0..2 {
            assert_eq!(
                location
                    .symbol_chain(
                        context.store(),
                        &host,
                        inner_symbol,
                        SymbolFlags::TYPE,
                        true
                    )
                    .unwrap(),
                [inner_symbol]
            );
            assert_eq!(
                location
                    .symbol_chain(
                        context.store(),
                        &host,
                        outer_symbol,
                        SymbolFlags::TYPE,
                        true
                    )
                    .unwrap(),
                [global_this, outer_symbol]
            );
            assert_eq!(
                context
                    .symbol_to_string_at_location(inner_symbol, name)
                    .unwrap(),
                "Shared"
            );
            assert_eq!(
                context
                    .symbol_to_string_at_location(inner_symbol, outside)
                    .unwrap(),
                "Shared"
            );
        }
        assert_eq!(
            (
                context.store().type_len(),
                context.store().symbol_len(),
                context.store().symbol_store().symbol_table_len(),
                context.store().checker_link_allocated_lengths()
            ),
            before
        );
    }

    #[test]
    fn named_class_expression_display_rejects_changed_source_ownership() {
        for poison in 0..5 {
            let parsed = parse_source_file("class Shared {} const Holder = class Shared {};");
            let file = FileId::new(41_032);
            let mut context = class_expression_context(&parsed, file);
            let outer =
                parsed
                    .arena
                    .iter()
                    .find_map(|(id, record)| {
                        matches!(record.data, NodeData::ClassDeclaration(_))
                            .then_some(NodeRef::new(parsed.arena.id(), file, id))
                    })
                    .unwrap();
            let (inner, name) = parsed
                .arena
                .iter()
                .find_map(|(id, record)| {
                    let NodeData::ClassExpression(class) = &record.data else {
                        return None;
                    };
                    Some((
                        NodeRef::new(parsed.arena.id(), file, id),
                        NodeRef::new(parsed.arena.id(), file, class.name.unwrap()),
                    ))
                })
                .unwrap();
            let owner = symbol(&context, inner);
            let outer_owner = symbol(&context, outer);
            assert_eq!(
                context.symbol_to_string_at_location(owner, name).unwrap(),
                "Shared"
            );
            match poison {
                0 => assert!(context.store_mut_for_test().set_symbol_flags(
                    owner,
                    SymbolFlags::INTERFACE,
                    ts_binder::CheckFlags::NONE
                )),
                1 => assert!(context.store_mut_for_test().set_symbol_declarations(
                    owner,
                    Some(vec![inner]),
                    Some(outer)
                )),
                2 => assert!(context.store_mut_for_test().set_symbol_declarations(
                    owner,
                    Some(vec![outer]),
                    Some(outer)
                )),
                3 => {
                    let record = context.store().symbol(owner).unwrap();
                    let (members, exports) = (record.members(), record.exports());
                    assert!(context.store_mut_for_test().set_symbol_relationships(
                        owner,
                        members,
                        exports,
                        Some(outer_owner),
                        None
                    ));
                }
                4 => assert!(context.store_mut_for_test().set_symbol_declarations(
                    owner,
                    Some(Vec::new()),
                    None
                )),
                _ => unreachable!(),
            }
            let before = (
                context.store().type_len(),
                context.store().symbol_len(),
                context.store().symbol_store().symbol_table_len(),
                context.store().checker_link_allocated_lengths(),
            );
            assert!(
                context.symbol_to_string_at_location(owner, name).is_err(),
                "poison {poison}"
            );
            let outside = NodeRef::new(parsed.arena.id(), file, parsed.source_file);
            assert!(
                context
                    .symbol_to_string_at_location(owner, outside)
                    .is_err(),
                "poison {poison}"
            );
            assert_eq!(
                (
                    context.store().type_len(),
                    context.store().symbol_len(),
                    context.store().symbol_store().symbol_table_len(),
                    context.store().checker_link_allocated_lengths()
                ),
                before,
                "poison {poison}"
            );
        }
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
    #[allow(clippy::too_many_lines)] // Keep the clone's valid, changed, and restored states together.
    fn export_assignment_artifact_property_clones_retain_display_ownership() {
        let parsed = parse_source_file("export = { first: 1, second: 2 };");
        let file = FileId::new(41_020);
        for redirect_to_clone in [false, true] {
            let mut binder = CanonicalBinder::new();
            binder
                .bind_source_file_with_facts(
                    &parsed.arena,
                    parsed.source_file,
                    file,
                    CanonicalSourceFileFacts::new(
                        EscapedName::source("\"/export.ts\""),
                        CanonicalSourceLanguage::TypeScript,
                        false,
                        CanonicalModuleState::External,
                    ),
                )
                .unwrap();
            binder
                .bind_typescript_declaration_slice(&parsed.arena, file)
                .unwrap();
            let mut context = CanonicalCheckerContext::new(
                binder.finish(),
                vec![(file, &parsed.arena)],
                CanonicalCheckerOptions::default(),
            )
            .unwrap();
            context.check_source_file(file).unwrap();
            let object =
                parsed
                    .arena
                    .iter()
                    .find_map(|(node, record)| {
                        (record.kind == SyntaxKind::ObjectLiteralExpression)
                            .then_some(NodeRef::new(parsed.arena.id(), file, node))
                    })
                    .unwrap();
            let type_ = context.get_type_at_location(object).unwrap();
            let members = context
                .store()
                .type_payload(type_)
                .unwrap()
                .data()
                .structured()
                .unwrap()
                .members
                .unwrap();
            let [first, second] = ["first", "second"].map(|name| {
                context
                    .store()
                    .symbol_table(members)
                    .unwrap()
                    .get_source(name)
                    .unwrap()
            });
            let original = context.store().value_symbol_links(first).unwrap().clone();
            let source = original.target.unwrap();
            let origin = *context
                .store()
                .object_literal_property_clone_origin(first)
                .unwrap();
            assert_eq!(origin.symbol(), first);
            assert_eq!(origin.source(), source);
            assert_eq!(origin.owner(), object);
            assert_ne!(source, first);
            assert_eq!(
                context.get_symbol_declarations(first).unwrap(),
                context.get_symbol_declarations(source).unwrap(),
            );
            for _ in 0..2 {
                assert_eq!(
                    context.symbol_to_string_at_location(first, object).unwrap(),
                    "first",
                );
            }
            let other_source = context.store().value_symbol_links(second).unwrap().target;
            let mut changed = original.clone();
            changed.target = other_source;
            assert!(
                context
                    .store_mut_for_test()
                    .set_value_symbol_links(first, changed)
            );
            let before = (
                context.store().type_len(),
                context.store().symbol_len(),
                context.store().checker_link_allocated_lengths(),
            );
            for _ in 0..2 {
                assert!(matches!(
                    context.symbol_to_string_at_location(first, object),
                    Err(crate::semantic::artifact_queries::CanonicalArtifactQueryError::SymbolDisplay(
                        SymbolDisplayError::InvalidSymbol(symbol)
                    )) if symbol == first
                ));
            }
            assert_eq!(
                (
                    context.store().type_len(),
                    context.store().symbol_len(),
                    context.store().checker_link_allocated_lengths(),
                ),
                before,
            );
            assert!(
                context
                    .store_mut_for_test()
                    .set_value_symbol_links(first, original)
            );
            assert_eq!(
                context.symbol_to_string_at_location(first, object).unwrap(),
                "first",
            );
            let mut changed = context.store().value_symbol_links(first).unwrap().clone();
            changed.target = other_source;
            assert!(
                context
                    .store_mut_for_test()
                    .set_value_symbol_links(first, changed)
            );
            let (target, redirected) = if redirect_to_clone {
                (first, source)
            } else {
                (source, first)
            };
            assert_eq!(
                context
                    .store_mut_for_test()
                    .record_merged_symbol(target, redirected),
                Ok(None),
            );
            let declaration = context.get_symbol_declarations(first).unwrap()[0];
            for clear_declarations in [false, true] {
                assert!(context.store_mut_for_test().set_symbol_declarations(
                    first,
                    (!clear_declarations).then(|| vec![declaration]),
                    (!clear_declarations).then_some(declaration),
                ));
                for flags in [
                    SymbolFlags::PROPERTY | SymbolFlags::TRANSIENT,
                    SymbolFlags::PROPERTY,
                ] {
                    assert!(context.store_mut_for_test().set_symbol_flags(
                        first,
                        flags,
                        ts_binder::CheckFlags::NONE,
                    ));
                    let poisoned_symbol = context.store().symbol(first).unwrap().clone();
                    let poisoned_links = context.store().value_symbol_links(first).unwrap().clone();
                    for queried in [first, source] {
                        for _ in 0..2 {
                            let result = context.symbol_to_string_at_location(queried, object);
                            if queried == source && !redirect_to_clone {
                                assert_eq!(result.unwrap(), "first");
                            } else {
                                assert!(
                                    matches!(
                                        &result,
                                        Err(crate::semantic::artifact_queries::CanonicalArtifactQueryError::SymbolDisplay(
                                            SymbolDisplayError::InvalidSymbol(symbol)
                                        )) if *symbol == first
                                    ),
                                    "unexpected display result: {result:?}"
                                );
                            }
                        }
                    }
                    assert_eq!(context.store().symbol(first), Some(&poisoned_symbol));
                    assert_eq!(
                        context.store().value_symbol_links(first),
                        Some(&poisoned_links)
                    );
                }
            }
            assert_eq!(
                (
                    context.store().type_len(),
                    context.store().symbol_len(),
                    context.store().checker_link_allocated_lengths(),
                ),
                before,
            );
            assert_eq!(
                context.store().object_literal_property_clone_origin(first),
                Some(&origin)
            );
        }
    }

    #[test]
    fn location_display_accepts_merged_source_and_synthetic_properties() {
        let first = parse_source_file("interface Shape { value: number; }");
        let second = parse_source_file("interface Shape { value: number; }");
        let files = [
            (FileId::new(41_021), &first, "/first.d.ts"),
            (FileId::new(41_022), &second, "/second.d.ts"),
        ];
        let mut binder = CanonicalBinder::new();
        for (file, parsed, path) in files {
            bind(
                &mut binder,
                parsed,
                file,
                path,
                CanonicalModuleState::Script,
            );
        }
        let mut context = CanonicalCheckerContext::new(
            binder.finish(),
            files
                .iter()
                .map(|(file, parsed, _)| (*file, &parsed.arena))
                .collect(),
            CanonicalCheckerOptions::default(),
        )
        .unwrap();
        let properties =
            files.map(|(file, parsed, _)| {
                let property =
                    parsed
                        .arena
                        .iter()
                        .find_map(|(node, record)| {
                            (record.kind == SyntaxKind::PropertyDeclaration)
                                .then_some(NodeRef::new(parsed.arena.id(), file, node))
                        })
                        .unwrap();
                context.file(file).unwrap().1.symbol(property).unwrap()
            });
        let merged = context.store().get_merged_symbol(properties[0]).unwrap();
        assert_eq!(
            context.store().get_merged_symbol(properties[1]),
            Some(merged)
        );
        assert!(
            context
                .store()
                .symbol(merged)
                .unwrap()
                .flags()
                .contains(SymbolFlags::PROPERTY | SymbolFlags::TRANSIENT,)
        );
        let enclosing = NodeRef::new(first.arena.id(), files[0].0, first.source_file);
        for property in [properties[0], properties[1], merged] {
            assert_eq!(
                context
                    .symbol_to_string_at_location(property, enclosing)
                    .unwrap(),
                "Shape.value",
            );
        }
        let synthetic = context.store_mut_for_test().alloc_transient_symbol(
            SymbolFlags::PROPERTY,
            EscapedName::source("synthetic"),
            ts_binder::CheckFlags::NONE,
        );
        assert_eq!(
            context.store().symbol(synthetic).unwrap().declarations(),
            None
        );
        assert!(
            context
                .store()
                .object_literal_property_clone_origin(synthetic)
                .is_none()
        );
        for _ in 0..2 {
            assert_eq!(
                context
                    .symbol_to_string_at_location(synthetic, enclosing)
                    .unwrap(),
                "synthetic",
            );
        }
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

    #[test]
    fn location_display_uses_global_this_when_a_type_name_is_hidden() {
        let parsed = parse_source_file(
            "interface Shape { global: number; } declare namespace Local { interface Shape { local: string; } }",
        );
        let file = FileId::new(41_003);
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
        let target = symbol(&context, declaration(&parsed, file, "Shape"));
        let type_ = context.get_declared_type_of_symbol(target).unwrap();
        let inside = declaration(&parsed, file, "Local");
        let outside = NodeRef::new(parsed.arena.id(), file, parsed.source_file);
        for _ in 0..2 {
            assert_eq!(
                context.type_to_string_at_location(type_, inside).unwrap(),
                "globalThis.Shape"
            );
            assert_eq!(
                context.type_to_string_at_location(type_, outside).unwrap(),
                "Shape"
            );
        }
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
            context.set_module_display_specifier(location, declaration, "item-api".to_owned()),
            Err(SymbolDisplayError::InvalidLocation(declaration))
        );
        assert_eq!(
            context.set_module_display_specifier(location, target_source, String::new()),
            Err(SymbolDisplayError::InvalidModuleSpecifier(target_source))
        );
        let foreign = parse_source_file("export {};");
        let foreign_source =
            NodeRef::new(foreign.arena.id(), declaration.file, foreign.source_file);
        assert_eq!(
            context.set_module_display_specifier(location, foreign_source, "item-api".to_owned()),
            Err(SymbolDisplayError::InvalidLocation(foreign_source))
        );
        context
            .set_module_display_specifier(location, target_source, "item-api".to_owned())
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
        assert_eq!(context.type_to_string_at_location_with_flags(type_, location,
            crate::semantic::CanonicalTypeFormatFlags::NO_TRUNCATION | crate::semantic::CanonicalTypeFormatFlags::USE_SINGLE_QUOTES_FOR_STRING_LITERAL_TYPE).unwrap(), "import('item-api').Shape");
        assert_eq!(context.type_to_string(type_).unwrap(), "Shape");
        let other_location = NodeRef::new(left.arena.id(), FileId::new(41_011), left.source_file);
        assert_eq!(
            context.type_to_string_at_location_with_flags(
                type_,
                other_location,
                crate::semantic::CanonicalTypeFormatFlags::NO_TRUNCATION
            ),
            Err(TypeDisplayUnavailable::SymbolDisplay(
                SymbolDisplayError::MissingModuleSpecifier(target_module)
            ))
        );
        assert_eq!(
            context.set_module_display_specifier(
                foreign_source,
                target_source,
                "item-api".to_owned()
            ),
            Err(SymbolDisplayError::InvalidLocation(foreign_source))
        );
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
        let mut wrong_target = context.store().alias_symbol_links(alias).unwrap().clone();
        let mut wrong_marker = wrong_target.clone();
        wrong_target.alias_target = AliasTargetState::Resolved(other);
        wrong_target.immediate_target = Some(other);
        wrong_marker.type_only_declaration =
            Some(declaration(&target, FileId::new(41_010), "Other"));
        for links in [wrong_target, wrong_marker] {
            assert!(
                context
                    .store_mut_for_test()
                    .set_alias_symbol_links(alias, links.clone())
            );
            for _ in 0..2 {
                assert_eq!(
                    context.type_to_string_at_location(type_, left_location),
                    Err(TypeDisplayUnavailable::SymbolDisplay(
                        SymbolDisplayError::InvalidAliasCache(alias)
                    ))
                );
                assert_eq!(context.store().alias_symbol_links(alias), Some(&links));
            }
        }
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

    #[test]
    fn failed_display_restores_visible_and_nested_aliases_as_one_query() {
        let target = parse_source_file(
            "interface Shape { value: number; } interface Other { text: string; } export { Shape, Other };",
        );
        let left = parse_source_file("import type { Shape as Bad, Other as Good } from './model';");
        let right = parse_source_file("export {};");
        let mut context = import_context(&target, &left, &right);
        let target_file = FileId::new(41_010);
        let left_file = FileId::new(41_011);
        let shape = symbol(&context, declaration(&target, target_file, "Shape"));
        let other = symbol(&context, declaration(&target, target_file, "Other"));
        let bad = symbol(&context, alias_declaration(&left, left_file, "Bad"));
        let good = symbol(&context, alias_declaration(&left, left_file, "Good"));
        let exported_shape = symbol(&context, alias_declaration(&target, target_file, "Shape"));
        let exported_other = symbol(&context, alias_declaration(&target, target_file, "Other"));
        let type_ = context.get_declared_type_of_symbol(shape).unwrap();
        let location = NodeRef::new(left.arena.id(), left_file, left.source_file);
        let poison = crate::semantic::AliasSymbolLinks {
            immediate_target: Some(other),
            alias_target: AliasTargetState::Resolved(other),
            ..crate::semantic::AliasSymbolLinks::default()
        };
        assert!(
            context
                .store_mut_for_test()
                .set_alias_symbol_links(bad, poison.clone())
        );
        let before = context.store().checker_link_allocated_lengths();
        for _ in 0..2 {
            assert_eq!(
                context.type_to_string_at_location(type_, location),
                Err(TypeDisplayUnavailable::SymbolDisplay(
                    SymbolDisplayError::InvalidAliasCache(bad)
                ))
            );
            assert_eq!(
                context.symbol_to_string_at_location(shape, location),
                Err(
                    crate::semantic::artifact_queries::CanonicalArtifactQueryError::SymbolDisplay(
                        SymbolDisplayError::InvalidAliasCache(bad)
                    )
                )
            );
            assert_eq!(context.store().alias_symbol_links(bad), Some(&poison));
            for cold in [good, exported_shape, exported_other] {
                assert_eq!(context.store().alias_symbol_links(cold), None);
            }
            assert_eq!(context.store().checker_link_allocated_lengths(), before);
        }
    }

    #[test]
    fn failed_cold_alias_does_not_leave_a_default_link_entry() {
        let target = parse_source_file(
            "export interface Shape { value: number; } export interface Other { text: string; }",
        );
        let left =
            parse_source_file("import type { Missing as Bad, Other as Good } from './model';");
        let right = parse_source_file("export {};");
        let mut context = import_context(&target, &left, &right);
        let target_file = FileId::new(41_010);
        let left_file = FileId::new(41_011);
        let shape = symbol(&context, declaration(&target, target_file, "Shape"));
        let bad = symbol(&context, alias_declaration(&left, left_file, "Bad"));
        let good = symbol(&context, alias_declaration(&left, left_file, "Good"));
        let type_ = context.get_declared_type_of_symbol(shape).unwrap();
        let location = NodeRef::new(left.arena.id(), left_file, left.source_file);
        let before = context.store().checker_link_allocated_lengths();
        for _ in 0..2 {
            assert!(
                matches!(context.type_to_string_at_location(type_, location), Err(TypeDisplayUnavailable::SymbolDisplay(SymbolDisplayError::Alias(CanonicalAliasResolutionError::TargetUnavailable { alias, .. }))) if alias == bad)
            );
            assert_eq!(context.store().alias_symbol_links(bad), None);
            assert_eq!(context.store().alias_symbol_links(good), None);
            assert_eq!(context.store().checker_link_allocated_lengths(), before);
        }
        let number = context.store().intrinsic_bootstrap().unwrap().number_type;
        assert_eq!(
            context
                .type_to_string_at_location(number, location)
                .unwrap(),
            "number"
        );
        assert_eq!(context.store().alias_symbol_links(bad), None);
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Check rejected, display-only, and canonical namespace queries in order.
    fn display_preflight_does_not_publish_synthetic_namespaces() {
        let foo = parse_source_file(
            "declare function foo(): void; declare namespace foo { export const tag: number; } export = foo;",
        );
        let shapes = parse_source_file(
            "export interface Shape { value: number; } export interface Other { text: string; }",
        );
        let importer = parse_source_file(
            "import * as foo from './foo'; import type { Shape as Bad } from './shapes';",
        );
        let foo_file = FileId::new(41_020);
        let shapes_file = FileId::new(41_021);
        let input_file = FileId::new(41_022);
        let files = [
            (foo_file, &foo, "/foo.d.ts"),
            (shapes_file, &shapes, "/shapes.d.ts"),
            (input_file, &importer, "/input.d.ts"),
        ];
        let mut binder = CanonicalBinder::new();
        for (file, parsed, path) in files {
            bind(
                &mut binder,
                parsed,
                file,
                path,
                CanonicalModuleState::External,
            );
        }
        let entries = importer
            .arena
            .iter()
            .filter_map(|(_, node)| {
                let NodeData::ImportDeclaration(import) = &node.data else {
                    return None;
                };
                let NodeData::StringLiteral(specifier) =
                    &importer.arena.get(import.module_specifier)?.data
                else {
                    return None;
                };
                let target = match specifier.text.as_str() {
                    "./foo" => foo_file,
                    "./shapes" => shapes_file,
                    _ => panic!("unexpected import"),
                };
                Some(CanonicalModuleResolutionEntry::resolved(
                    NodeRef::new(importer.arena.id(), input_file, import.module_specifier),
                    CanonicalResolvedModuleInput::new(
                        target,
                        CanonicalModuleResolutionMode::Esm,
                        CanonicalModuleResolutionMode::Esm,
                    ),
                ))
            })
            .collect::<Vec<_>>();
        let mut context = CanonicalCheckerContext::new_with_module_resolutions(
            binder.finish(),
            files
                .into_iter()
                .map(|(file, parsed, _)| (file, &parsed.arena))
                .collect(),
            CanonicalCheckerOptions::default(),
            CanonicalModuleResolutionManifestInput::new(entries),
        )
        .unwrap();
        let original_foo = symbol(&context, declaration(&foo, foo_file, "foo"));
        let namespace_import = importer
            .arena
            .iter()
            .find_map(|(id, node)| {
                matches!(node.data, NodeData::NamespaceImport(_)).then_some(NodeRef::new(
                    importer.arena.id(),
                    input_file,
                    id,
                ))
            })
            .unwrap();
        let foo_alias = symbol(&context, namespace_import);
        let bad = symbol(&context, alias_declaration(&importer, input_file, "Bad"));
        let shape = symbol(&context, declaration(&shapes, shapes_file, "Shape"));
        let other = symbol(&context, declaration(&shapes, shapes_file, "Other"));
        let type_ = context.get_declared_type_of_symbol(shape).unwrap();
        let location = NodeRef::new(importer.arena.id(), input_file, importer.source_file);
        let poison = crate::semantic::AliasSymbolLinks {
            immediate_target: Some(other),
            alias_target: AliasTargetState::Resolved(other),
            ..crate::semantic::AliasSymbolLinks::default()
        };
        assert!(
            context
                .store_mut_for_test()
                .set_alias_symbol_links(bad, poison.clone())
        );
        let counts = |context: &CanonicalCheckerContext<'_>| {
            (
                context.store().symbol_len(),
                context.store().symbol_store().symbol_table_len(),
                context.store().checker_link_allocated_lengths(),
            )
        };
        let before = counts(&context);
        for _ in 0..3 {
            assert_eq!(
                context.type_to_string_at_location(type_, location),
                Err(TypeDisplayUnavailable::SymbolDisplay(
                    SymbolDisplayError::InvalidAliasCache(bad)
                ))
            );
            assert_eq!(
                context.symbol_to_string_at_location(shape, location),
                Err(
                    crate::semantic::artifact_queries::CanonicalArtifactQueryError::SymbolDisplay(
                        SymbolDisplayError::InvalidAliasCache(bad)
                    )
                )
            );
            assert_eq!(
                counts(&context),
                before,
                "symbols, tables, and every link store must be unchanged"
            );
            assert_eq!(context.store().alias_symbol_links(foo_alias), None);
            assert_eq!(context.store().alias_symbol_links(bad), Some(&poison));
        }
        assert!(
            context
                .store_mut_for_test()
                .set_alias_symbol_links(bad, crate::semantic::AliasSymbolLinks::default())
        );
        context.resolve_alias(bad).unwrap();
        let tag = foo.arena.iter().find_map(|(id, node)| {
            let NodeData::VariableDeclaration(variable) = &node.data else { return None };
            matches!(&foo.arena.get(variable.name)?.data, NodeData::Identifier(name) if name.text == "tag").then_some(NodeRef::new(foo.arena.id(), foo_file, id))
        }).unwrap();
        let tag = symbol(&context, tag);
        assert_eq!(
            context.symbol_to_string_at_location(tag, location).unwrap(),
            "foo.tag"
        );
        assert_eq!(context.store().symbol_len(), before.0);
        assert_eq!(context.store().symbol_store().symbol_table_len(), before.1);
        assert_eq!(context.store().alias_symbol_links(foo_alias), None);
        let AliasTargetState::Resolved(synthetic) =
            context.resolve_alias(foo_alias).unwrap().target
        else {
            panic!("namespace must resolve")
        };
        assert_ne!(synthetic, original_foo);
        assert_eq!(context.store().symbol_len(), before.0 + 2);
        assert_eq!(
            context.store().symbol_store().symbol_table_len(),
            before.1 + 1
        );
        assert_eq!(
            context.store().export_type_links(synthetic).unwrap().target,
            Some(original_foo)
        );
        let warm = counts(&context);
        for _ in 0..2 {
            assert_eq!(
                context.symbol_to_string_at_location(tag, location).unwrap(),
                "foo.tag"
            );
            assert_eq!(counts(&context), warm);
        }
        assert!(
            context
                .store_mut_for_test()
                .set_alias_symbol_links(bad, poison.clone())
        );
        let exports = context
            .store()
            .symbol(synthetic)
            .unwrap()
            .exports()
            .unwrap();
        let exports_before = context.store().symbol_table(exports).unwrap().clone();
        let export_links_before = context
            .store()
            .export_type_links(synthetic)
            .unwrap()
            .clone();
        let alias_links_before = context
            .store()
            .alias_symbol_links(foo_alias)
            .unwrap()
            .clone();
        for _ in 0..2 {
            assert_eq!(
                context.type_to_string_at_location(type_, location),
                Err(TypeDisplayUnavailable::SymbolDisplay(
                    SymbolDisplayError::InvalidAliasCache(bad)
                ))
            );
            assert_eq!(counts(&context), warm);
            assert_eq!(context.store().symbol_table(exports), Some(&exports_before));
            assert_eq!(
                context.store().export_type_links(synthetic),
                Some(&export_links_before)
            );
            assert_eq!(
                context.store().alias_symbol_links(foo_alias),
                Some(&alias_links_before)
            );
            assert_eq!(context.store().alias_symbol_links(bad), Some(&poison));
        }
    }

    #[test]
    fn location_display_brackets_a_string_named_namespace_export() {
        let target =
            parse_source_file("declare function read(): number; export { read as 'read-name' };");
        let left = parse_source_file("export {};");
        let right = parse_source_file("import * as Items from './model';");
        let mut context = import_context(&target, &left, &right);
        let target = symbol(&context, declaration(&target, FileId::new(41_010), "read"));
        let location = NodeRef::new(right.arena.id(), FileId::new(41_012), right.source_file);
        assert_eq!(
            context
                .symbol_to_string_at_location(target, location)
                .unwrap(),
            "Items['read-name']"
        );
    }

    #[test]
    fn location_display_finds_the_public_export_of_a_local_type() {
        let target =
            parse_source_file("interface Item { value: number; } export { Item as PublicItem };");
        let left = parse_source_file("import {} from './model';");
        let right = parse_source_file("import * as Items from './model';");
        let mut context = import_context(&target, &left, &right);
        let item = symbol(&context, declaration(&target, FileId::new(41_010), "Item"));
        assert_eq!(context.store().symbol(item).unwrap().parent(), None);
        let type_ = context.get_declared_type_of_symbol(item).unwrap();
        let own = NodeRef::new(target.arena.id(), FileId::new(41_010), target.source_file);
        let left_location = NodeRef::new(left.arena.id(), FileId::new(41_011), left.source_file);
        let right_location = NodeRef::new(right.arena.id(), FileId::new(41_012), right.source_file);
        for _ in 0..2 {
            assert_eq!(
                context
                    .type_to_string_at_location_with_flags(
                        type_,
                        left_location,
                        crate::semantic::CanonicalTypeFormatFlags::NO_TRUNCATION
                    )
                    .unwrap(),
                "import(\"./model\").PublicItem"
            );
            assert_eq!(
                context
                    .symbol_to_string_at_location(item, right_location)
                    .unwrap(),
                "Items.PublicItem"
            );
            assert_eq!(
                context
                    .type_to_string_at_location_with_flags(
                        type_,
                        own,
                        crate::semantic::CanonicalTypeFormatFlags::NO_TRUNCATION
                    )
                    .unwrap(),
                "Item"
            );
        }
        assert_eq!(
            context.store().symbol(item).unwrap().name().as_utf8(),
            Some("Item")
        );
    }

    #[test]
    fn location_display_does_not_substitute_an_inaccessible_private_name() {
        let target =
            parse_source_file("interface Item { value: number; } export { Item as PublicItem };");
        let left = parse_source_file("export {};");
        let right = parse_source_file("export {};");
        let mut context = import_context(&target, &left, &right);
        let item = symbol(&context, declaration(&target, FileId::new(41_010), "Item"));
        let type_ = context.get_declared_type_of_symbol(item).unwrap();
        let location = NodeRef::new(left.arena.id(), FileId::new(41_011), left.source_file);
        assert_eq!(
            context.type_to_string_at_location_with_flags(
                type_,
                location,
                crate::semantic::CanonicalTypeFormatFlags::NO_TRUNCATION
            ),
            Err(TypeDisplayUnavailable::SymbolDisplay(
                SymbolDisplayError::UnnameableSymbol(item)
            ))
        );
    }

    #[test]
    fn named_defaults_keep_the_written_name_only_in_the_same_binding_context() {
        let target =
            parse_source_file("export default function make(): number; declare namespace Inner {}");
        let left = parse_source_file("import * as Items from './model';");
        let right = parse_source_file("import chosen from './model';");
        let mut context = import_context(&target, &left, &right);
        let make_declaration = declaration(&target, FileId::new(41_010), "make");
        let make = symbol(&context, make_declaration);
        let inner = declaration(&target, FileId::new(41_010), "Inner");
        let own = NodeRef::new(target.arena.id(), FileId::new(41_010), target.source_file);
        let left_location = NodeRef::new(left.arena.id(), FileId::new(41_011), left.source_file);
        let right_location = NodeRef::new(right.arena.id(), FileId::new(41_012), right.source_file);
        for _ in 0..2 {
            assert_eq!(
                context
                    .symbol_to_string_at_location(make, make_declaration)
                    .unwrap(),
                "make"
            );
            assert_eq!(
                context.symbol_to_string_at_location(make, own).unwrap(),
                "make"
            );
            assert_eq!(
                context.symbol_to_string_at_location(make, inner).unwrap(),
                "make"
            );
            assert_eq!(
                context
                    .symbol_to_string_at_location(make, left_location)
                    .unwrap(),
                "Items.default"
            );
            assert_eq!(
                context
                    .symbol_to_string_at_location(make, right_location)
                    .unwrap(),
                "chosen"
            );
        }
        assert_eq!(
            context.store().symbol(make).unwrap().name(),
            InternalSymbolName::Default.as_ref()
        );
    }

    #[test]
    fn default_binding_context_stops_at_ambient_modules_and_global_augmentations() {
        let parsed = parse_source_file(concat!(
            "export {}; ",
            "declare namespace Outer { namespace Inner { interface Plain {} } } ",
            "declare module './ambient' { namespace Inner { interface Ambient {} } } ",
            "declare global { namespace Inner { interface Global {} } }",
        ));
        let file = FileId::new(41_030);
        let mut binder = CanonicalBinder::new();
        bind(
            &mut binder,
            &parsed,
            file,
            "/input.d.ts",
            CanonicalModuleState::External,
        );
        let bindings = binder.finish();
        let host = DeclaredTypeHost::new([(&parsed.arena, bindings.file(file).unwrap())]).unwrap();
        let source = NodeRef::new(parsed.arena.id(), file, parsed.source_file);
        let global = declaration(&parsed, file, "global");
        let ambient = parsed
            .arena
            .iter()
            .find_map(|(id, record)| {
                let NodeData::ModuleDeclaration(module) = &record.data else {
                    return None;
                };
                matches!(
                    parsed.arena.get(module.name)?.data,
                    NodeData::StringLiteral(_)
                )
                .then_some(NodeRef::new(parsed.arena.id(), file, id))
            })
            .unwrap();
        for (name, expected) in [("Plain", source), ("Ambient", ambient), ("Global", global)] {
            assert_eq!(
                binding_context(&host, declaration(&parsed, file, name)).unwrap(),
                expected
            );
        }
        for boundary in [source, ambient, global] {
            assert_eq!(binding_context(&host, boundary).unwrap(), boundary);
        }
    }
}
