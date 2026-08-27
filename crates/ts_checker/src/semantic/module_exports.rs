//! Source-owned module export lookup without alias or value-type resolution.

use std::collections::{BTreeMap, BTreeSet};

use ts_ast::{NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    CheckFlags, EscapedName, InternalSymbolName, SemanticSymbolId, SymbolFlags, SymbolTableId,
};

use super::{
    CanonicalTypeMapperStore, DeclaredTypeHost, DeclaredTypeHostError, ProductionAliasTargetHost,
    ProductionAliasTargetHostError, SourceCheckError,
    alias::CanonicalAliasTargetUnavailable,
    source_namespaces::{has_pure_module_flags, validate_module_export_table},
};

/// A missing provider or invalid source graph is not a missing export.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum CanonicalModuleExportQueryError {
    TargetHost(ProductionAliasTargetHostError),
    DeclaredHost(DeclaredTypeHostError),
    Source(SourceCheckError),
    Target(CanonicalAliasTargetUnavailable),
    InvalidModule(SemanticSymbolId),
    UnsupportedModule(SemanticSymbolId),
    InvalidExportCache(SemanticSymbolId),
    UnsupportedExportCache(SemanticSymbolId),
}

impl std::fmt::Display for CanonicalModuleExportQueryError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::TargetHost(error) => error.fmt(formatter),
            Self::DeclaredHost(error) => error.fmt(formatter),
            Self::Source(error) => error.fmt(formatter),
            Self::Target(error) => write!(
                formatter,
                "module export provider is unavailable: {error:?}"
            ),
            Self::InvalidModule(module) => {
                write!(formatter, "module export owner is invalid: {module:?}")
            }
            Self::UnsupportedModule(module) => {
                write!(formatter, "module export owner is unsupported: {module:?}")
            }
            Self::InvalidExportCache(module) => {
                write!(formatter, "module export cache is invalid: {module:?}")
            }
            Self::UnsupportedExportCache(module) => {
                write!(formatter, "module export cache is unsupported: {module:?}")
            }
        }
    }
}

impl std::error::Error for CanonicalModuleExportQueryError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::TargetHost(error) => Some(error),
            Self::DeclaredHost(error) => Some(error),
            Self::Source(error) => Some(error),
            _ => None,
        }
    }
}

impl From<ProductionAliasTargetHostError> for CanonicalModuleExportQueryError {
    fn from(error: ProductionAliasTargetHostError) -> Self {
        Self::TargetHost(error)
    }
}

impl From<DeclaredTypeHostError> for CanonicalModuleExportQueryError {
    fn from(error: DeclaredTypeHostError) -> Self {
        Self::DeclaredHost(error)
    }
}

impl From<SourceCheckError> for CanonicalModuleExportQueryError {
    fn from(error: SourceCheckError) -> Self {
        Self::Source(error)
    }
}

impl From<CanonicalAliasTargetUnavailable> for CanonicalModuleExportQueryError {
    fn from(error: CanonicalAliasTargetUnavailable) -> Self {
        Self::Target(error)
    }
}

struct ModuleExportSource {
    declaration: NodeRef,
    exports: Option<SymbolTableId>,
}

pub(super) fn get_module_export_by_name(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    aliases: &ProductionAliasTargetHost<'_, '_, '_>,
    module: SemanticSymbolId,
    name: &str,
) -> Result<Option<SemanticSymbolId>, CanonicalModuleExportQueryError> {
    let mut sources = BTreeMap::new();
    let mut pending = vec![module];
    while let Some(owner) = pending.pop() {
        if sources.contains_key(&owner) {
            continue;
        }
        let source = validate_source_module(store, host, owner)?;
        pending.extend(aliases.export_star_targets(store, source.declaration, owner, true)?);
        sources.insert(owner, source);
    }
    validate_resolved_export_caches(store, aliases, &sources)?;
    let source = sources
        .get(&module)
        .ok_or(CanonicalModuleExportQueryError::InvalidModule(module))?;
    lookup_export(store, aliases, source.declaration, module, name)
}

fn validate_source_module(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    module: SemanticSymbolId,
) -> Result<ModuleExportSource, CanonicalModuleExportQueryError> {
    let invalid = || CanonicalModuleExportQueryError::InvalidModule(module);
    let owner = store.symbol(module).ok_or_else(invalid)?;
    let Some([declaration]) = owner.declarations() else {
        return Err(CanonicalModuleExportQueryError::UnsupportedModule(module));
    };
    let (arena, bound) = host.source(*declaration).ok_or_else(invalid)?;
    if arena.revision() != bound.node_arena_revision() {
        return Err(CanonicalAliasTargetUnavailable::StaleSourceFile(declaration.file).into());
    }
    if !has_pure_module_flags(owner.flags())
        || !matches!(
            arena.get(declaration.node).map(|node| &node.data),
            Some(NodeData::SourceFile(_))
        )
        || bound
            .source_facts()
            .is_none_or(|facts| !facts.is_external_module() || facts.is_javascript_file())
    {
        return Err(CanonicalModuleExportQueryError::UnsupportedModule(module));
    }
    if *declaration != bound.source_file()
        || !declaration.is_for(arena.id(), bound.file_id())
        || !store.contains_node_ref(*declaration)
        || store.source_node_kind(*declaration) != Some(SyntaxKind::SourceFile)
        || bound.symbol(*declaration) != Some(module)
        || store.get_merged_symbol(module) != Some(module)
        || !store.source_merged_symbol_declarations_match(module)
        || owner.check_flags() != CheckFlags::NONE
        || owner.members().is_some()
        || owner.parent().is_some()
        || owner.export_symbol().is_some()
        || owner.value_declaration().is_some() != owner.flags().contains(SymbolFlags::VALUE_MODULE)
        || owner
            .value_declaration()
            .is_some_and(|value| value != *declaration)
    {
        return Err(invalid());
    }
    validate_module_export_table(store, host, module, &[*declaration], owner.exports())?;
    if let Some(exports) = owner.exports() {
        let exports = store.symbol_table(exports).ok_or_else(invalid)?;
        if exports
            .get(InternalSymbolName::ExportEquals.as_ref())
            .is_some()
        {
            return Err(
                CanonicalAliasTargetUnavailable::ExportEqualsResolutionUnsupported {
                    declaration: *declaration,
                    module,
                }
                .into(),
            );
        }
        if exports.iter().any(|(_, symbol)| {
            store.get_merged_symbol(symbol) != Some(symbol)
                || !store.source_merged_symbol_declarations_match(symbol)
        }) {
            return Err(invalid());
        }
    }
    Ok(ModuleExportSource {
        declaration: *declaration,
        exports: owner.exports(),
    })
}

fn lookup_export(
    store: &CanonicalTypeMapperStore,
    aliases: &ProductionAliasTargetHost<'_, '_, '_>,
    declaration: NodeRef,
    module: SemanticSymbolId,
    name: &str,
) -> Result<Option<SemanticSymbolId>, CanonicalModuleExportQueryError> {
    match aliases.direct_export(store, declaration, module, name, true) {
        Ok(symbol) => Ok(Some(symbol)),
        Err(CanonicalAliasTargetUnavailable::MissingExport {
            module: missing, ..
        }) if missing == module => Ok(None),
        Err(error) => Err(error.into()),
    }
}

fn validate_resolved_export_caches(
    store: &CanonicalTypeMapperStore,
    aliases: &ProductionAliasTargetHost<'_, '_, '_>,
    sources: &BTreeMap<SemanticSymbolId, ModuleExportSource>,
) -> Result<(), CanonicalModuleExportQueryError> {
    let names = sources
        .values()
        .flat_map(|source| {
            source
                .exports
                .and_then(|exports| store.symbol_table(exports))
                .into_iter()
                .flat_map(ts_binder::semantic::SymbolTable::iter)
                .filter_map(|(name, _)| name.as_utf8().map(str::to_owned))
        })
        .collect::<BTreeSet<_>>();
    for (&module, source) in sources {
        let Some(links) = store.module_symbol_links(module) else {
            continue;
        };
        if links.type_only_export_star_map.is_some() {
            return Err(CanonicalModuleExportQueryError::UnsupportedExportCache(
                module,
            ));
        }
        let Some(cached) = links.resolved_exports else {
            continue;
        };
        let invalid = || CanonicalModuleExportQueryError::InvalidExportCache(module);
        let cached = store.symbol_table(cached).ok_or_else(invalid)?;
        let mut expected = BTreeMap::new();
        for name in &names {
            if let Some(symbol) = lookup_export(store, aliases, source.declaration, module, name)? {
                expected.insert(EscapedName::source(name), symbol);
            }
        }
        if cached
            .get(InternalSymbolName::ExportStar.as_ref())
            .is_some()
        {
            let star = source
                .exports
                .and_then(|exports| store.symbol_table(exports))
                .and_then(|exports| exports.get(InternalSymbolName::ExportStar.as_ref()))
                .ok_or_else(invalid)?;
            expected.insert(EscapedName::internal(InternalSymbolName::ExportStar), star);
        }
        if cached.len() != expected.len()
            || cached
                .iter()
                .any(|(name, symbol)| expected.get(&name.to_owned()) != Some(&symbol))
        {
            return Err(invalid());
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use ts_ast::{FileId, NodeData, NodeRef};
    use ts_binder::{
        CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    };
    use ts_parser::{ParseResult, parse_source_file};

    use super::*;
    use crate::semantic::{
        AliasTargetState, CanonicalCheckerContext, CanonicalCheckerOptions,
        CanonicalModuleResolutionEntry, CanonicalModuleResolutionManifestInput,
        CanonicalModuleResolutionMode, CanonicalResolvedModuleInput, ModuleSymbolLinks,
    };

    const HELPER: &str = "__classPrivateFieldSet";

    fn file(index: usize) -> FileId {
        FileId::new(u32::try_from(index + 1).unwrap())
    }

    fn make_context<'a>(
        sources: &'a [ParseResult],
        resolutions: Option<&[(usize, &str, usize)]>,
    ) -> CanonicalCheckerContext<'a> {
        let mut binder = CanonicalBinder::new();
        for (index, source) in sources.iter().enumerate() {
            assert!(source.diagnostics.is_empty(), "{:?}", source.diagnostics);
            binder
                .bind_source_file_with_facts(
                    &source.arena,
                    source.source_file,
                    file(index),
                    CanonicalSourceFileFacts::new(
                        EscapedName::source(format!("\"/project/{index}.d.ts\"")),
                        CanonicalSourceLanguage::TypeScript,
                        true,
                        CanonicalModuleState::External,
                    ),
                )
                .unwrap();
            binder
                .bind_typescript_declaration_slice(&source.arena, file(index))
                .unwrap();
        }
        let arenas = sources
            .iter()
            .enumerate()
            .map(|(index, source)| (file(index), &source.arena))
            .collect();
        let Some(resolutions) = resolutions else {
            return CanonicalCheckerContext::new(
                binder.finish(),
                arenas,
                CanonicalCheckerOptions::default(),
            )
            .unwrap();
        };
        let entries = resolutions.iter().map(|&(source, name, target)| {
            let parsed = &sources[source];
            let specifier = parsed.arena.iter().find_map(|(_, node)| {
                let NodeData::ExportDeclaration(export) = &node.data else { return None; };
                let specifier = export.module_specifier?;
                matches!(&parsed.arena.get(specifier)?.data, NodeData::StringLiteral(literal) if literal.text == name)
                    .then_some(NodeRef::new(parsed.arena.id(), file(source), specifier))
            }).unwrap();
            CanonicalModuleResolutionEntry::resolved(specifier, CanonicalResolvedModuleInput::new(
                file(target), CanonicalModuleResolutionMode::CommonJs, CanonicalModuleResolutionMode::CommonJs,
            ))
        });
        CanonicalCheckerContext::new_with_module_resolutions(
            binder.finish(),
            arenas,
            CanonicalCheckerOptions::default(),
            CanonicalModuleResolutionManifestInput::new(entries),
        )
        .unwrap()
    }

    fn module(context: &CanonicalCheckerContext<'_>, index: usize) -> SemanticSymbolId {
        let (_, bound) = context.file(file(index)).unwrap();
        bound.symbol(bound.source_file()).unwrap()
    }

    fn direct(context: &CanonicalCheckerContext<'_>, index: usize, name: &str) -> SemanticSymbolId {
        let exports = context
            .store()
            .symbol(module(context, index))
            .unwrap()
            .exports()
            .unwrap();
        context
            .store()
            .symbol_table(exports)
            .unwrap()
            .get_source(name)
            .unwrap()
    }

    fn counts(context: &CanonicalCheckerContext<'_>) -> (usize, usize, usize, usize) {
        let store = context.store();
        (
            store.type_len(),
            store.symbol_len(),
            store.signature_len(),
            store.mapper_len(),
        )
    }

    fn assert_failed_lookup_is_read_only(
        context: &CanonicalCheckerContext<'_>,
        owner: SemanticSymbolId,
    ) {
        let before = (
            counts(context),
            context.store().checker_link_allocated_lengths(),
        );
        let diagnostics = context.diagnostics().clone();
        for _ in 0..2 {
            assert!(context.get_module_export_by_name(owner, HELPER).is_err());
            assert!(context.get_module_export_by_name(owner, "absent").is_err());
        }
        assert_eq!(
            (
                counts(context),
                context.store().checker_link_allocated_lengths()
            ),
            before
        );
        assert_eq!(context.diagnostics(), &diagnostics);
    }

    #[test]
    fn module_export_lookup_keeps_values_and_class_bodies_cold() {
        let sources = [parse_source_file(concat!(
            "export function __classPrivateFieldSet(value: Missing) { try {} finally {} } ",
            "export class Cold { method() { try {} finally {} } } ",
            "export type OnlyType = Missing; export const scalar = 1;",
        ))];
        let context = make_context(&sources, None);
        let owner = module(&context, 0);
        let before = (
            counts(&context),
            context.store().checker_link_allocated_lengths(),
        );
        for _ in 0..2 {
            for name in [HELPER, "Cold", "OnlyType", "scalar"] {
                let symbol = direct(&context, 0, name);
                assert_eq!(
                    context.get_module_export_by_name(owner, name),
                    Ok(Some(symbol))
                );
                assert!(context.store().value_symbol_links(symbol).is_none());
            }
            assert_eq!(context.get_module_export_by_name(owner, "absent"), Ok(None));
        }
        assert_eq!(
            (
                counts(&context),
                context.store().checker_link_allocated_lengths()
            ),
            before
        );
        assert!(context.diagnostics().is_empty());
    }

    #[test]
    fn module_export_lookup_follows_stars_type_only_stars_and_cycles() {
        let sources = [
            parse_source_file("export * from './left'; export type * from './right';"),
            parse_source_file("export * from './root'; export * from './leaf';"),
            parse_source_file("export declare function onlyTypeStar(): Missing;"),
            parse_source_file(
                "export declare function __classPrivateFieldSet(): Missing; export default function hidden(): Missing;",
            ),
        ];
        let context = make_context(
            &sources,
            Some(&[
                (0, "./left", 1),
                (0, "./right", 2),
                (1, "./root", 0),
                (1, "./leaf", 3),
            ]),
        );
        let owner = module(&context, 0);
        let helper = direct(&context, 3, HELPER);
        let type_only = direct(&context, 2, "onlyTypeStar");
        let before = (
            counts(&context),
            context.store().checker_link_allocated_lengths(),
        );
        for _ in 0..2 {
            assert_eq!(
                context.get_module_export_by_name(owner, HELPER),
                Ok(Some(helper))
            );
            assert_eq!(
                context.get_module_export_by_name(owner, "onlyTypeStar"),
                Ok(Some(type_only))
            );
            assert_eq!(
                context.get_module_export_by_name(owner, "default"),
                Ok(None)
            );
            assert_eq!(context.get_module_export_by_name(owner, "absent"), Ok(None));
        }
        assert_eq!(
            (
                counts(&context),
                context.store().checker_link_allocated_lengths()
            ),
            before
        );
        assert!(context.store().value_symbol_links(helper).is_none());
        assert!(context.store().value_symbol_links(type_only).is_none());
    }

    #[test]
    fn module_export_lookup_keeps_type_only_alias_resolution_separate() {
        let sources = [
            parse_source_file("export type { helper as __classPrivateFieldSet } from './target';"),
            parse_source_file("export declare function helper(): Missing;"),
        ];
        let mut context = make_context(&sources, Some(&[(0, "./target", 1)]));
        let owner = module(&context, 0);
        let alias = direct(&context, 0, HELPER);
        let target = direct(&context, 1, "helper");
        assert_eq!(
            context.store().symbol(alias).unwrap().flags(),
            SymbolFlags::ALIAS
        );
        assert!(context.store().alias_symbol_links(alias).is_none());
        assert_eq!(
            context.get_module_export_by_name(owner, HELPER),
            Ok(Some(alias))
        );
        assert!(context.store().alias_symbol_links(alias).is_none());
        let resolution = context.resolve_alias(alias).unwrap();
        assert_eq!(resolution.target, AliasTargetState::Resolved(target));
        assert!(resolution.events.is_empty());
        let links = context.store().alias_symbol_links(alias).unwrap().clone();
        assert!(links.type_only_declaration.is_some());
        let before = (
            counts(&context),
            context.store().checker_link_allocated_lengths(),
        );
        assert_eq!(
            context.get_module_export_by_name(owner, HELPER),
            Ok(Some(alias))
        );
        assert_eq!(context.store().alias_symbol_links(alias), Some(&links));
        assert_eq!(
            (
                counts(&context),
                context.store().checker_link_allocated_lengths()
            ),
            before
        );
    }

    #[test]
    fn module_export_lookup_does_not_consume_alias_cycle_events() {
        let sources = [
            parse_source_file("export { __classPrivateFieldSet } from './right';"),
            parse_source_file("export { __classPrivateFieldSet } from './left';"),
        ];
        let mut context = make_context(&sources, Some(&[(0, "./right", 1), (1, "./left", 0)]));
        let owner = module(&context, 0);
        let alias = direct(&context, 0, HELPER);
        assert_eq!(
            context.get_module_export_by_name(owner, HELPER),
            Ok(Some(alias))
        );
        assert!(context.store().alias_symbol_links(alias).is_none());
        let cold = context.resolve_alias(alias).unwrap();
        assert_eq!(cold.target, AliasTargetState::Unknown);
        assert!(!cold.events.is_empty());
        assert!(
            cold.events
                .iter()
                .all(|event| event.diagnostic_code() == 2303)
        );
        assert_eq!(
            context.get_module_export_by_name(owner, HELPER),
            Ok(Some(alias))
        );
        let warm = context.resolve_alias(alias).unwrap();
        assert_eq!(warm.target, AliasTargetState::Unknown);
        assert!(warm.events.is_empty());
    }

    #[test]
    fn module_export_lookup_rejects_unavailable_stars_without_writes() {
        let sources = [parse_source_file("export * from './missing';")];
        for resolutions in [None, Some([].as_slice())] {
            let context = make_context(&sources, resolutions);
            assert_failed_lookup_is_read_only(&context, module(&context, 0));
        }
    }

    #[test]
    fn module_export_lookup_rejects_missing_leaf_tables_and_recovers() {
        let sources = [
            parse_source_file("export * from './leaf';"),
            parse_source_file("export declare function __classPrivateFieldSet(): Missing;"),
        ];
        let mut context = make_context(&sources, Some(&[(0, "./leaf", 1)]));
        let owner = module(&context, 0);
        let leaf = module(&context, 1);
        let helper = direct(&context, 1, HELPER);
        let exports = context.store().symbol(leaf).unwrap().exports();
        assert_eq!(
            context.get_module_export_by_name(owner, HELPER),
            Ok(Some(helper))
        );
        assert!(
            context
                .store_mut_for_test()
                .set_symbol_relationships(leaf, None, None, None, None)
        );
        assert_failed_lookup_is_read_only(&context, owner);
        assert!(
            context
                .store_mut_for_test()
                .set_symbol_relationships(leaf, None, exports, None, None)
        );
        assert_eq!(
            context.get_module_export_by_name(owner, HELPER),
            Ok(Some(helper))
        );
        assert_eq!(context.get_module_export_by_name(owner, "absent"), Ok(None));
    }

    #[test]
    fn module_export_lookup_rejects_foreign_entries_and_owners() {
        let sources = [
            parse_source_file("export declare function __classPrivateFieldSet(): Missing;"),
            parse_source_file("export declare function __classPrivateFieldSet(): Missing;"),
        ];
        let mut context = make_context(&sources, None);
        let owner = module(&context, 0);
        let helper = direct(&context, 0, HELPER);
        let other = direct(&context, 1, HELPER);
        let exports = context.store().symbol(owner).unwrap().exports().unwrap();
        assert_eq!(
            context
                .store_mut_for_test()
                .insert_symbol(exports, EscapedName::source(HELPER), other),
            Some(Some(helper))
        );
        assert_failed_lookup_is_read_only(&context, owner);
        assert_eq!(
            context.store_mut_for_test().insert_symbol(
                exports,
                EscapedName::source(HELPER),
                helper
            ),
            Some(Some(other))
        );
        assert_eq!(
            context.get_module_export_by_name(owner, HELPER),
            Ok(Some(helper))
        );
        assert!(context.get_module_export_by_name(helper, HELPER).is_err());
        let foreign = make_context(&sources, None);
        assert!(
            context
                .get_module_export_by_name(module(&foreign, 0), HELPER)
                .is_err()
        );
    }

    #[test]
    fn module_export_lookup_validates_resolved_export_caches() {
        let sources = [
            parse_source_file("export * from './leaf';"),
            parse_source_file("export declare function __classPrivateFieldSet(): Missing;"),
        ];
        let mut context = make_context(&sources, Some(&[(0, "./leaf", 1)]));
        let owner = module(&context, 0);
        let leaf = module(&context, 1);
        let helper = direct(&context, 1, HELPER);
        let leaf_exports = context.store().symbol(leaf).unwrap().exports().unwrap();
        let cache = context
            .store_mut_for_test()
            .clone_symbol_table(leaf_exports)
            .unwrap();
        let good = ModuleSymbolLinks {
            resolved_exports: Some(cache),
            ..ModuleSymbolLinks::default()
        };
        assert!(
            context
                .store_mut_for_test()
                .set_module_symbol_links(owner, good.clone())
        );
        assert_eq!(
            context.get_module_export_by_name(owner, HELPER),
            Ok(Some(helper))
        );
        assert_eq!(context.get_module_export_by_name(owner, "absent"), Ok(None));
        let empty = context.store_mut_for_test().alloc_symbol_table();
        assert!(context.store_mut_for_test().set_module_symbol_links(
            owner,
            ModuleSymbolLinks {
                resolved_exports: Some(empty),
                ..ModuleSymbolLinks::default()
            }
        ));
        assert_failed_lookup_is_read_only(&context, owner);
        assert!(
            context
                .store_mut_for_test()
                .set_module_symbol_links(owner, good)
        );
        assert_eq!(
            context.get_module_export_by_name(owner, HELPER),
            Ok(Some(helper))
        );
    }

    #[test]
    fn module_export_lookup_does_not_report_star_conflicts_as_missing() {
        let sources = [
            parse_source_file("export * from './left'; export * from './right';"),
            parse_source_file("export declare function __classPrivateFieldSet(): Missing;"),
            parse_source_file("export declare function __classPrivateFieldSet(): Missing;"),
        ];
        let context = make_context(&sources, Some(&[(0, "./left", 1), (0, "./right", 2)]));
        let owner = module(&context, 0);
        assert!(matches!(
            context.get_module_export_by_name(owner, HELPER),
            Err(CanonicalModuleExportQueryError::Target(
                CanonicalAliasTargetUnavailable::ExportStarResolutionUnsupported { .. }
            ))
        ));
        assert_eq!(context.get_module_export_by_name(owner, "absent"), Ok(None));
    }
}
