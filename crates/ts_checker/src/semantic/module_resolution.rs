//! Checker-owned module-resolution facts supplied by the Program host.
//!
//! The compiler resolves paths, but checker queries consume exact module-
//! specifier nodes. Keeping the manifest keyed by [`NodeRef`] prevents two
//! equal spellings in different declarations, files, or Programs from sharing
//! a resolution accidentally. Construction is intentionally one-shot: every
//! entry is validated against declaration-complete binder state before the
//! canonical checker store is created.

use std::collections::{BTreeMap, BTreeSet};

use ts_ast::{
    FileId, NodeArena, NodeArenaId, NodeArenaRevision, NodeData, NodeId, NodeRef, SyntaxKind,
};
use ts_binder::{BoundFile, SemanticSymbolId, SymbolFlags, SymbolStore};

/// Local equivalent of the resolution modes consumed by checker module
/// interoperability queries.
///
/// This deliberately does not depend on `ts_module` or `ts_options`; the
/// compiler boundary translates its richer modes into these three semantic
/// states when it creates the manifest.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CanonicalModuleResolutionMode {
    None,
    CommonJs,
    Esm,
}

/// A successful compiler-owned resolution before checker validation.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct CanonicalResolvedModuleInput {
    target_file: FileId,
    usage_mode: CanonicalModuleResolutionMode,
    target_mode: CanonicalModuleResolutionMode,
}

impl CanonicalResolvedModuleInput {
    #[must_use]
    pub const fn new(
        target_file: FileId,
        usage_mode: CanonicalModuleResolutionMode,
        target_mode: CanonicalModuleResolutionMode,
    ) -> Self {
        Self {
            target_file,
            usage_mode,
            target_mode,
        }
    }

    #[must_use]
    pub const fn target_file(self) -> FileId {
        self.target_file
    }

    #[must_use]
    pub const fn usage_mode(self) -> CanonicalModuleResolutionMode {
        self.usage_mode
    }

    #[must_use]
    pub const fn target_mode(self) -> CanonicalModuleResolutionMode {
        self.target_mode
    }
}

/// One explicit compiler result for a module-specifier node.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CanonicalModuleResolutionInput {
    Unresolved,
    Resolved(CanonicalResolvedModuleInput),
}

/// One exact module-specifier entry supplied at checker construction.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct CanonicalModuleResolutionEntry {
    specifier: NodeRef,
    resolution: CanonicalModuleResolutionInput,
}

impl CanonicalModuleResolutionEntry {
    #[must_use]
    pub const fn unresolved(specifier: NodeRef) -> Self {
        Self {
            specifier,
            resolution: CanonicalModuleResolutionInput::Unresolved,
        }
    }

    #[must_use]
    pub const fn resolved(specifier: NodeRef, resolution: CanonicalResolvedModuleInput) -> Self {
        Self {
            specifier,
            resolution: CanonicalModuleResolutionInput::Resolved(resolution),
        }
    }

    #[must_use]
    pub const fn specifier(self) -> NodeRef {
        self.specifier
    }

    #[must_use]
    pub const fn resolution(self) -> CanonicalModuleResolutionInput {
        self.resolution
    }
}

/// Explicit input for an available Program module-resolution capability.
///
/// There is deliberately no `Default` implementation. An explicitly empty
/// value means "the provider is available and has no entry"; callers that do
/// not supply this input get an unavailable capability instead.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CanonicalModuleResolutionManifestInput {
    entries: Vec<CanonicalModuleResolutionEntry>,
}

impl CanonicalModuleResolutionManifestInput {
    #[must_use]
    pub fn new(entries: impl IntoIterator<Item = CanonicalModuleResolutionEntry>) -> Self {
        Self {
            entries: entries.into_iter().collect(),
        }
    }

    #[must_use]
    pub fn entries(&self) -> &[CanonicalModuleResolutionEntry] {
        &self.entries
    }
}

/// A resolution whose target has been adopted and validated by the checker.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct CanonicalResolvedModule {
    target_file: FileId,
    target_symbol: SemanticSymbolId,
    usage_mode: CanonicalModuleResolutionMode,
    target_mode: CanonicalModuleResolutionMode,
}

impl CanonicalResolvedModule {
    #[must_use]
    pub const fn target_file(self) -> FileId {
        self.target_file
    }

    /// The canonical external-module source symbol for [`Self::target_file`].
    #[must_use]
    pub const fn target_symbol(self) -> SemanticSymbolId {
        self.target_symbol
    }

    #[must_use]
    pub const fn usage_mode(self) -> CanonicalModuleResolutionMode {
        self.usage_mode
    }

    #[must_use]
    pub const fn target_mode(self) -> CanonicalModuleResolutionMode {
        self.target_mode
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum RetainedModuleResolution {
    Unresolved,
    Resolved(CanonicalResolvedModule),
}

/// Typed result of one exact module-specifier lookup.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CanonicalModuleResolutionLookup {
    /// The Program did not provide module-resolution capability.
    Unavailable,
    /// The capability is available but has no entry for this exact node.
    EntryAbsent,
    /// The provider explicitly attempted and failed this exact resolution.
    Unresolved,
    /// The provider resolved this node to a retained external-module source.
    Resolved(CanonicalResolvedModule),
}

/// Immutable checker-owned module-resolution manifest.
#[derive(Debug, Eq, PartialEq)]
pub struct CanonicalModuleResolutionManifest {
    entries: Option<BTreeMap<NodeRef, RetainedModuleResolution>>,
}

impl CanonicalModuleResolutionManifest {
    pub(super) const fn unavailable() -> Self {
        Self { entries: None }
    }

    fn available(entries: BTreeMap<NodeRef, RetainedModuleResolution>) -> Self {
        Self {
            entries: Some(entries),
        }
    }

    #[must_use]
    pub const fn is_available(&self) -> bool {
        self.entries.is_some()
    }

    #[must_use]
    pub fn len(&self) -> usize {
        self.entries.as_ref().map_or(0, BTreeMap::len)
    }

    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    #[must_use]
    pub fn lookup(&self, specifier: NodeRef) -> CanonicalModuleResolutionLookup {
        let Some(entries) = &self.entries else {
            return CanonicalModuleResolutionLookup::Unavailable;
        };
        match entries.get(&specifier) {
            None => CanonicalModuleResolutionLookup::EntryAbsent,
            Some(RetainedModuleResolution::Unresolved) => {
                CanonicalModuleResolutionLookup::Unresolved
            }
            Some(RetainedModuleResolution::Resolved(resolved)) => {
                CanonicalModuleResolutionLookup::Resolved(*resolved)
            }
        }
    }
}

/// Why an available compiler manifest could not be adopted by the checker.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum CanonicalModuleResolutionManifestError {
    DuplicateSpecifier(NodeRef),
    MissingSpecifierFile(NodeRef),
    SpecifierArenaMismatch {
        specifier: NodeRef,
        expected: NodeArenaId,
    },
    IncompleteSpecifierFile(FileId),
    StaleSpecifierFile {
        file: FileId,
        expected: NodeArenaRevision,
        actual: NodeArenaRevision,
    },
    MissingSpecifierNode(NodeRef),
    UnboundSpecifier(NodeRef),
    UnownedSpecifier(NodeRef),
    MalformedSpecifier(NodeRef),
    UnsupportedSpecifierPosition(NodeRef),
    MissingTargetFile(FileId),
    IncompleteTargetFile(FileId),
    StaleTargetFile {
        file: FileId,
        expected: NodeArenaRevision,
        actual: NodeArenaRevision,
    },
    ScriptTarget(FileId),
    MissingTargetSourceSymbol(FileId),
    InvalidTargetSourceSymbol {
        file: FileId,
        symbol: SemanticSymbolId,
    },
}

impl std::fmt::Display for CanonicalModuleResolutionManifestError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::DuplicateSpecifier(specifier) => {
                write!(
                    formatter,
                    "module specifier {specifier:?} occurs more than once"
                )
            }
            Self::MissingSpecifierFile(specifier) => write!(
                formatter,
                "module specifier {specifier:?} belongs to an unretained file"
            ),
            Self::SpecifierArenaMismatch {
                specifier,
                expected,
            } => write!(
                formatter,
                "module specifier {specifier:?} is not in retained arena {expected:?}"
            ),
            Self::IncompleteSpecifierFile(file) => write!(
                formatter,
                "module specifier file {} is not declaration-complete",
                file.index()
            ),
            Self::StaleSpecifierFile { file, .. } => write!(
                formatter,
                "module specifier file {} changed after binding",
                file.index()
            ),
            Self::MissingSpecifierNode(specifier) => {
                write!(
                    formatter,
                    "module specifier {specifier:?} is absent from its arena"
                )
            }
            Self::UnboundSpecifier(specifier) => write!(
                formatter,
                "module specifier {specifier:?} was not reached by canonical binding"
            ),
            Self::UnownedSpecifier(specifier) => write!(
                formatter,
                "module specifier {specifier:?} is not owned by the canonical symbol store"
            ),
            Self::MalformedSpecifier(specifier) => write!(
                formatter,
                "module specifier {specifier:?} is not a string-literal-like node"
            ),
            Self::UnsupportedSpecifierPosition(specifier) => write!(
                formatter,
                "module specifier {specifier:?} is not in a supported import/export position"
            ),
            Self::MissingTargetFile(file) => write!(
                formatter,
                "resolved module target file {} is not retained",
                file.index()
            ),
            Self::IncompleteTargetFile(file) => write!(
                formatter,
                "resolved module target file {} is not declaration-complete",
                file.index()
            ),
            Self::StaleTargetFile { file, .. } => write!(
                formatter,
                "resolved module target file {} changed after binding",
                file.index()
            ),
            Self::ScriptTarget(file) => write!(
                formatter,
                "resolved module target file {} is not an external module",
                file.index()
            ),
            Self::MissingTargetSourceSymbol(file) => write!(
                formatter,
                "resolved module target file {} has no canonical source symbol",
                file.index()
            ),
            Self::InvalidTargetSourceSymbol { file, symbol } => write!(
                formatter,
                "resolved module target file {} has invalid source symbol {symbol:?}",
                file.index()
            ),
        }
    }
}

impl std::error::Error for CanonicalModuleResolutionManifestError {}

pub(super) fn validate_module_resolution_manifest<'arena, 'bound, I>(
    input: CanonicalModuleResolutionManifestInput,
    symbols: &SymbolStore,
    files: I,
) -> Result<CanonicalModuleResolutionManifest, CanonicalModuleResolutionManifestError>
where
    I: IntoIterator<Item = (FileId, &'arena NodeArena, &'bound BoundFile)>,
{
    let files = files
        .into_iter()
        .map(|(file, arena, bound)| (file, (arena, bound)))
        .collect::<BTreeMap<_, _>>();

    let mut seen = BTreeSet::new();
    for entry in &input.entries {
        if !seen.insert(entry.specifier) {
            return Err(CanonicalModuleResolutionManifestError::DuplicateSpecifier(
                entry.specifier,
            ));
        }
    }

    let mut entries = BTreeMap::new();
    let mut targets = BTreeMap::new();
    for entry in input.entries {
        validate_specifier(entry.specifier, symbols, &files)?;
        let retained = match entry.resolution {
            CanonicalModuleResolutionInput::Unresolved => RetainedModuleResolution::Unresolved,
            CanonicalModuleResolutionInput::Resolved(resolution) => {
                let target_symbol =
                    if let Some(target) = targets.get(&resolution.target_file).copied() {
                        target
                    } else {
                        let target = validate_target(resolution.target_file, symbols, &files)?;
                        targets.insert(resolution.target_file, target);
                        target
                    };
                RetainedModuleResolution::Resolved(CanonicalResolvedModule {
                    target_file: resolution.target_file,
                    target_symbol,
                    usage_mode: resolution.usage_mode,
                    target_mode: resolution.target_mode,
                })
            }
        };
        let previous = entries.insert(entry.specifier, retained);
        debug_assert!(
            previous.is_none(),
            "duplicates were rejected before validation"
        );
    }

    Ok(CanonicalModuleResolutionManifest::available(entries))
}

fn validate_specifier(
    specifier: NodeRef,
    symbols: &SymbolStore,
    files: &BTreeMap<FileId, (&NodeArena, &BoundFile)>,
) -> Result<(), CanonicalModuleResolutionManifestError> {
    let Some(&(arena, bound)) = files.get(&specifier.file) else {
        return Err(CanonicalModuleResolutionManifestError::MissingSpecifierFile(specifier));
    };
    if specifier.arena != arena.id() || bound.node_arena_id() != arena.id() {
        return Err(
            CanonicalModuleResolutionManifestError::SpecifierArenaMismatch {
                specifier,
                expected: arena.id(),
            },
        );
    }
    if !bound.declarations_complete() {
        return Err(
            CanonicalModuleResolutionManifestError::IncompleteSpecifierFile(specifier.file),
        );
    }
    if bound.node_arena_revision() != arena.revision() {
        return Err(CanonicalModuleResolutionManifestError::StaleSpecifierFile {
            file: specifier.file,
            expected: bound.node_arena_revision(),
            actual: arena.revision(),
        });
    }
    let Some(node) = arena.get(specifier.node) else {
        return Err(CanonicalModuleResolutionManifestError::MissingSpecifierNode(specifier));
    };
    if !bound.contains(specifier) {
        return Err(CanonicalModuleResolutionManifestError::UnboundSpecifier(
            specifier,
        ));
    }
    if !symbols.contains_node_ref(specifier) {
        return Err(CanonicalModuleResolutionManifestError::UnownedSpecifier(
            specifier,
        ));
    }
    if !matches!(
        (node.kind, &node.data),
        (SyntaxKind::StringLiteral, NodeData::StringLiteral(_))
            | (
                SyntaxKind::NoSubstitutionTemplateLiteral,
                NodeData::NoSubstitutionTemplateLiteral(_)
            )
    ) {
        return Err(CanonicalModuleResolutionManifestError::MalformedSpecifier(
            specifier,
        ));
    }
    if !is_supported_specifier_position(arena, specifier.node) {
        return Err(
            CanonicalModuleResolutionManifestError::UnsupportedSpecifierPosition(specifier),
        );
    }
    Ok(())
}

fn is_supported_specifier_position(arena: &NodeArena, specifier: NodeId) -> bool {
    let Some(parent_id) = arena.get(specifier).and_then(|node| node.parent) else {
        return false;
    };
    let Some(parent) = arena.get(parent_id) else {
        return false;
    };
    match (parent.kind, &parent.data) {
        (
            SyntaxKind::ImportDeclaration | SyntaxKind::JsImportDeclaration,
            NodeData::ImportDeclaration(import),
        ) => import.module_specifier == specifier,
        (SyntaxKind::ExportDeclaration, NodeData::ExportDeclaration(export)) => {
            export.module_specifier == Some(specifier)
        }
        (SyntaxKind::ExternalModuleReference, NodeData::ExternalModuleReference(reference))
            if reference.expression == specifier =>
        {
            let Some(import_equals_id) = parent.parent else {
                return false;
            };
            matches!(
                arena.get(import_equals_id),
                Some(ts_ast::Node {
                    kind: SyntaxKind::ImportEqualsDeclaration,
                    data: NodeData::ImportEqualsDeclaration(import),
                    ..
                }) if import.module_reference == parent_id
            )
        }
        _ => false,
    }
}

fn validate_target(
    target_file: FileId,
    symbols: &SymbolStore,
    files: &BTreeMap<FileId, (&NodeArena, &BoundFile)>,
) -> Result<SemanticSymbolId, CanonicalModuleResolutionManifestError> {
    let Some(&(arena, bound)) = files.get(&target_file) else {
        return Err(CanonicalModuleResolutionManifestError::MissingTargetFile(
            target_file,
        ));
    };
    if !bound.declarations_complete() {
        return Err(CanonicalModuleResolutionManifestError::IncompleteTargetFile(target_file));
    }
    if bound.node_arena_revision() != arena.revision() {
        return Err(CanonicalModuleResolutionManifestError::StaleTargetFile {
            file: target_file,
            expected: bound.node_arena_revision(),
            actual: arena.revision(),
        });
    }
    let facts =
        bound
            .source_facts()
            .ok_or(CanonicalModuleResolutionManifestError::ScriptTarget(
                target_file,
            ))?;
    if !facts.is_external_or_common_js_module() {
        return Err(CanonicalModuleResolutionManifestError::ScriptTarget(
            target_file,
        ));
    }
    let source = bound.source_file();
    let source_symbol = bound
        .symbol(source)
        .ok_or(CanonicalModuleResolutionManifestError::MissingTargetSourceSymbol(target_file))?;
    let valid = symbols.symbol(source_symbol).is_some_and(|symbol| {
        symbol.flags().intersects(SymbolFlags::MODULE)
            && symbol
                .declarations()
                .is_some_and(|declarations| declarations.contains(&source))
    });
    if !valid {
        return Err(
            CanonicalModuleResolutionManifestError::InvalidTargetSourceSymbol {
                file: target_file,
                symbol: source_symbol,
            },
        );
    }
    Ok(source_symbol)
}

#[cfg(test)]
mod tests {
    use ts_binder::{
        CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
        EscapedName,
    };
    use ts_parser::{ParseResult, parse_source_file};

    use super::*;
    use crate::semantic::{
        CanonicalCheckerContext, CanonicalCheckerContextError, CanonicalCheckerOptions,
    };

    fn parsed(source: &str) -> ParseResult {
        let parsed = parse_source_file(source);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        parsed
    }

    fn facts(file: FileId, module_state: CanonicalModuleState) -> CanonicalSourceFileFacts {
        CanonicalSourceFileFacts::new(
            EscapedName::source(format!("\"/project/{}.ts\"", file.index())),
            CanonicalSourceLanguage::TypeScript,
            false,
            module_state,
        )
    }

    fn completed_bindings(
        files: &[(FileId, &ParseResult, CanonicalModuleState)],
    ) -> ts_binder::CanonicalProgramBindings {
        let mut binder = CanonicalBinder::new();
        for &(file, parsed, module_state) in files {
            binder
                .bind_source_file_with_facts(
                    &parsed.arena,
                    parsed.source_file,
                    file,
                    facts(file, module_state),
                )
                .unwrap();
        }
        for &(file, parsed, _) in files {
            binder
                .bind_typescript_declaration_slice(&parsed.arena, file)
                .unwrap();
        }
        binder.finish()
    }

    fn module_specifiers(parsed: &ParseResult) -> Vec<NodeId> {
        let mut specifiers = parsed
            .arena
            .iter()
            .filter_map(|(node, data)| {
                matches!(
                    (data.kind, &data.data),
                    (SyntaxKind::StringLiteral, NodeData::StringLiteral(_))
                        | (
                            SyntaxKind::NoSubstitutionTemplateLiteral,
                            NodeData::NoSubstitutionTemplateLiteral(_)
                        )
                )
                .then_some(node)
            })
            .filter(|node| is_supported_specifier_position(&parsed.arena, *node))
            .collect::<Vec<_>>();
        specifiers.sort_unstable_by_key(|node| parsed.arena.get(*node).unwrap().range.start);
        specifiers
    }

    fn node_ref(parsed: &ParseResult, file: FileId, node: NodeId) -> NodeRef {
        NodeRef::new(parsed.arena.id(), file, node)
    }

    fn resolved(target: FileId) -> CanonicalResolvedModuleInput {
        CanonicalResolvedModuleInput::new(
            target,
            CanonicalModuleResolutionMode::Esm,
            CanonicalModuleResolutionMode::CommonJs,
        )
    }

    #[test]
    fn distinguishes_all_lookup_states_and_keys_equal_text_by_node_identity() {
        let importer = parsed(
            r#"
                import first from "./target";
                import second from "./target";
                export { Target } from "./target";
            "#,
        );
        let target = parsed("export interface Target { value: string }");
        let importer_file = FileId::new(1);
        let target_file = FileId::new(2);
        let specifiers = module_specifiers(&importer);
        assert_eq!(specifiers.len(), 3);
        let first = node_ref(&importer, importer_file, specifiers[0]);
        let second = node_ref(&importer, importer_file, specifiers[1]);
        let absent = node_ref(&importer, importer_file, specifiers[2]);
        assert_ne!(first, second);

        let unavailable = CanonicalCheckerContext::new(
            completed_bindings(&[
                (importer_file, &importer, CanonicalModuleState::External),
                (target_file, &target, CanonicalModuleState::External),
            ]),
            vec![
                (importer_file, &importer.arena),
                (target_file, &target.arena),
            ],
            CanonicalCheckerOptions::default(),
        )
        .unwrap();
        assert_eq!(
            unavailable.module_resolution(first),
            CanonicalModuleResolutionLookup::Unavailable
        );
        assert!(!unavailable.module_resolutions().is_available());

        let available = CanonicalCheckerContext::new_with_module_resolutions(
            completed_bindings(&[
                (importer_file, &importer, CanonicalModuleState::External),
                (target_file, &target, CanonicalModuleState::External),
            ]),
            vec![
                (importer_file, &importer.arena),
                (target_file, &target.arena),
            ],
            CanonicalCheckerOptions::default(),
            CanonicalModuleResolutionManifestInput::new([
                CanonicalModuleResolutionEntry::resolved(first, resolved(target_file)),
                CanonicalModuleResolutionEntry::unresolved(second),
            ]),
        )
        .unwrap();
        assert!(available.module_resolutions().is_available());
        assert_eq!(available.module_resolutions().len(), 2);
        assert_eq!(
            available.module_resolution(second),
            CanonicalModuleResolutionLookup::Unresolved
        );
        assert_eq!(
            available.module_resolution(absent),
            CanonicalModuleResolutionLookup::EntryAbsent
        );

        let CanonicalModuleResolutionLookup::Resolved(found) = available.module_resolution(first)
        else {
            panic!("first import should retain its cross-file resolution");
        };
        assert_eq!(found.target_file(), target_file);
        let target_source = available.source_file(target_file).unwrap();
        let (_, target_bound) = available.file(target_file).unwrap();
        assert_eq!(
            found.target_symbol(),
            target_bound.symbol(target_source.node_ref()).unwrap()
        );
        assert_eq!(found.usage_mode(), CanonicalModuleResolutionMode::Esm);
        assert_eq!(found.target_mode(), CanonicalModuleResolutionMode::CommonJs);
        assert!(available.store().symbol(found.target_symbol()).is_some());
    }

    #[test]
    fn explicit_empty_manifest_is_available_while_default_is_unavailable() {
        let importer = parsed("import value from './target';");
        let target = parsed("export const value = 1;");
        let importer_file = FileId::new(10);
        let target_file = FileId::new(11);
        let specifier = node_ref(&importer, importer_file, module_specifiers(&importer)[0]);

        let context = CanonicalCheckerContext::new_with_module_resolutions(
            completed_bindings(&[
                (importer_file, &importer, CanonicalModuleState::External),
                (target_file, &target, CanonicalModuleState::External),
            ]),
            vec![
                (importer_file, &importer.arena),
                (target_file, &target.arena),
            ],
            CanonicalCheckerOptions::default(),
            CanonicalModuleResolutionManifestInput::new([]),
        )
        .unwrap();

        assert!(context.module_resolutions().is_available());
        assert!(context.module_resolutions().is_empty());
        assert_eq!(
            context.module_resolution(specifier),
            CanonicalModuleResolutionLookup::EntryAbsent
        );
    }

    #[test]
    fn accepts_export_and_import_equals_module_specifier_positions() {
        let importer = parsed(
            r#"
                export { Target } from "./target";
                import legacy = require("./target");
            "#,
        );
        let target = parsed("export interface Target {}");
        let importer_file = FileId::new(20);
        let target_file = FileId::new(21);
        let specifiers = module_specifiers(&importer);
        assert_eq!(specifiers.len(), 2);
        let specifier_refs = specifiers
            .iter()
            .map(|specifier| node_ref(&importer, importer_file, *specifier))
            .collect::<Vec<_>>();
        let entries = [
            CanonicalModuleResolutionEntry::resolved(
                specifier_refs[0],
                CanonicalResolvedModuleInput::new(
                    target_file,
                    CanonicalModuleResolutionMode::None,
                    CanonicalModuleResolutionMode::None,
                ),
            ),
            CanonicalModuleResolutionEntry::resolved(
                specifier_refs[1],
                CanonicalResolvedModuleInput::new(
                    target_file,
                    CanonicalModuleResolutionMode::CommonJs,
                    CanonicalModuleResolutionMode::Esm,
                ),
            ),
        ];

        let context = CanonicalCheckerContext::new_with_module_resolutions(
            completed_bindings(&[
                (importer_file, &importer, CanonicalModuleState::External),
                (target_file, &target, CanonicalModuleState::External),
            ]),
            vec![
                (importer_file, &importer.arena),
                (target_file, &target.arena),
            ],
            CanonicalCheckerOptions::default(),
            CanonicalModuleResolutionManifestInput::new(entries),
        )
        .unwrap();

        let CanonicalModuleResolutionLookup::Resolved(export) =
            context.module_resolution(specifier_refs[0])
        else {
            panic!("export specifier should resolve");
        };
        assert_eq!(export.usage_mode(), CanonicalModuleResolutionMode::None);
        assert_eq!(export.target_mode(), CanonicalModuleResolutionMode::None);

        let CanonicalModuleResolutionLookup::Resolved(import_equals) =
            context.module_resolution(specifier_refs[1])
        else {
            panic!("import-equals specifier should resolve");
        };
        assert_eq!(
            import_equals.usage_mode(),
            CanonicalModuleResolutionMode::CommonJs
        );
        assert_eq!(
            import_equals.target_mode(),
            CanonicalModuleResolutionMode::Esm
        );
    }

    #[test]
    fn rejects_same_node_duplicates_before_adopting_any_entry() {
        let importer = parsed("import value from './target';");
        let target = parsed("export const value = 1;");
        let importer_file = FileId::new(30);
        let target_file = FileId::new(31);
        let specifier = node_ref(&importer, importer_file, module_specifiers(&importer)[0]);
        let make_bindings = || {
            completed_bindings(&[
                (importer_file, &importer, CanonicalModuleState::External),
                (target_file, &target, CanonicalModuleState::External),
            ])
        };
        let order = || {
            vec![
                (importer_file, &importer.arena),
                (target_file, &target.arena),
            ]
        };

        let error = CanonicalCheckerContext::new_with_module_resolutions(
            make_bindings(),
            order(),
            CanonicalCheckerOptions::default(),
            CanonicalModuleResolutionManifestInput::new([
                CanonicalModuleResolutionEntry::unresolved(specifier),
                CanonicalModuleResolutionEntry::resolved(specifier, resolved(target_file)),
            ]),
        )
        .unwrap_err();
        assert_eq!(
            error,
            CanonicalCheckerContextError::ModuleResolutions(
                CanonicalModuleResolutionManifestError::DuplicateSpecifier(specifier)
            )
        );

        let retry = CanonicalCheckerContext::new_with_module_resolutions(
            make_bindings(),
            order(),
            CanonicalCheckerOptions::default(),
            CanonicalModuleResolutionManifestInput::new([
                CanonicalModuleResolutionEntry::unresolved(specifier),
            ]),
        )
        .unwrap();
        assert_eq!(
            retry.module_resolution(specifier),
            CanonicalModuleResolutionLookup::Unresolved
        );
    }

    #[test]
    fn rejects_foreign_non_module_and_malformed_specifier_nodes() {
        let importer = parsed("import value from './target';");
        let foreign = parsed("import other from './target';");
        let target = parsed("export const value = 1;");
        let importer_file = FileId::new(40);
        let target_file = FileId::new(41);
        let foreign_specifier = node_ref(&foreign, importer_file, module_specifiers(&foreign)[0]);

        let foreign_error = CanonicalCheckerContext::new_with_module_resolutions(
            completed_bindings(&[
                (importer_file, &importer, CanonicalModuleState::External),
                (target_file, &target, CanonicalModuleState::External),
            ]),
            vec![
                (importer_file, &importer.arena),
                (target_file, &target.arena),
            ],
            CanonicalCheckerOptions::default(),
            CanonicalModuleResolutionManifestInput::new([
                CanonicalModuleResolutionEntry::unresolved(foreign_specifier),
            ]),
        )
        .unwrap_err();
        assert!(matches!(
            foreign_error,
            CanonicalCheckerContextError::ModuleResolutions(
                CanonicalModuleResolutionManifestError::SpecifierArenaMismatch { .. }
            )
        ));

        let non_module = parsed("export {}; const text = './target';");
        let literal = non_module
            .arena
            .iter()
            .find_map(|(node, data)| {
                matches!(data.data, NodeData::StringLiteral(_)).then_some(node)
            })
            .unwrap();
        let literal_ref = node_ref(&non_module, importer_file, literal);
        let position_error = CanonicalCheckerContext::new_with_module_resolutions(
            completed_bindings(&[
                (importer_file, &non_module, CanonicalModuleState::External),
                (target_file, &target, CanonicalModuleState::External),
            ]),
            vec![
                (importer_file, &non_module.arena),
                (target_file, &target.arena),
            ],
            CanonicalCheckerOptions::default(),
            CanonicalModuleResolutionManifestInput::new([
                CanonicalModuleResolutionEntry::unresolved(literal_ref),
            ]),
        )
        .unwrap_err();
        assert_eq!(
            position_error,
            CanonicalCheckerContextError::ModuleResolutions(
                CanonicalModuleResolutionManifestError::UnsupportedSpecifierPosition(literal_ref)
            )
        );

        let malformed = parse_source_file("import value from target;");
        let malformed_node = malformed
            .arena
            .iter()
            .find_map(|(_, node)| match &node.data {
                NodeData::ImportDeclaration(import) => Some(import.module_specifier),
                _ => None,
            })
            .unwrap();
        let malformed_ref = node_ref(&malformed, importer_file, malformed_node);
        let malformed_error = CanonicalCheckerContext::new_with_module_resolutions(
            completed_bindings(&[
                (importer_file, &malformed, CanonicalModuleState::External),
                (target_file, &target, CanonicalModuleState::External),
            ]),
            vec![
                (importer_file, &malformed.arena),
                (target_file, &target.arena),
            ],
            CanonicalCheckerOptions::default(),
            CanonicalModuleResolutionManifestInput::new([
                CanonicalModuleResolutionEntry::unresolved(malformed_ref),
            ]),
        )
        .unwrap_err();
        assert_eq!(
            malformed_error,
            CanonicalCheckerContextError::ModuleResolutions(
                CanonicalModuleResolutionManifestError::MalformedSpecifier(malformed_ref)
            )
        );
    }

    #[test]
    fn rejects_missing_and_script_targets() {
        let importer = parsed("import value from './target';");
        let script = parsed("const value = 1;");
        let importer_file = FileId::new(50);
        let script_file = FileId::new(51);
        let missing_file = FileId::new(99);
        let specifier = node_ref(&importer, importer_file, module_specifiers(&importer)[0]);
        let make_bindings = || {
            completed_bindings(&[
                (importer_file, &importer, CanonicalModuleState::External),
                (script_file, &script, CanonicalModuleState::Script),
            ])
        };
        let order = || {
            vec![
                (importer_file, &importer.arena),
                (script_file, &script.arena),
            ]
        };

        let missing_error = CanonicalCheckerContext::new_with_module_resolutions(
            make_bindings(),
            order(),
            CanonicalCheckerOptions::default(),
            CanonicalModuleResolutionManifestInput::new([
                CanonicalModuleResolutionEntry::resolved(specifier, resolved(missing_file)),
            ]),
        )
        .unwrap_err();
        assert_eq!(
            missing_error,
            CanonicalCheckerContextError::ModuleResolutions(
                CanonicalModuleResolutionManifestError::MissingTargetFile(missing_file)
            )
        );

        let script_error = CanonicalCheckerContext::new_with_module_resolutions(
            make_bindings(),
            order(),
            CanonicalCheckerOptions::default(),
            CanonicalModuleResolutionManifestInput::new([
                CanonicalModuleResolutionEntry::resolved(specifier, resolved(script_file)),
            ]),
        )
        .unwrap_err();
        assert_eq!(
            script_error,
            CanonicalCheckerContextError::ModuleResolutions(
                CanonicalModuleResolutionManifestError::ScriptTarget(script_file)
            )
        );
    }

    #[test]
    fn stale_specifier_and_target_arenas_fail_before_checker_construction() {
        let mut importer = parsed("import value from './target';");
        let target = parsed("export const value = 1;");
        let importer_file = FileId::new(60);
        let target_file = FileId::new(61);
        let specifier = node_ref(&importer, importer_file, module_specifiers(&importer)[0]);
        let bindings = completed_bindings(&[
            (importer_file, &importer, CanonicalModuleState::External),
            (target_file, &target, CanonicalModuleState::External),
        ]);
        importer.arena.set_source_text("stale importer");

        let stale_specifier = CanonicalCheckerContext::new_with_module_resolutions(
            bindings,
            vec![
                (importer_file, &importer.arena),
                (target_file, &target.arena),
            ],
            CanonicalCheckerOptions::default(),
            CanonicalModuleResolutionManifestInput::new([
                CanonicalModuleResolutionEntry::resolved(specifier, resolved(target_file)),
            ]),
        )
        .unwrap_err();
        assert!(matches!(
            stale_specifier,
            CanonicalCheckerContextError::ArenaRevisionMismatch {
                file,
                ..
            } if file == importer_file
        ));

        let importer = parsed("import value from './target';");
        let mut target = parsed("export const value = 1;");
        let specifier = node_ref(&importer, importer_file, module_specifiers(&importer)[0]);
        let bindings = completed_bindings(&[
            (importer_file, &importer, CanonicalModuleState::External),
            (target_file, &target, CanonicalModuleState::External),
        ]);
        target.arena.set_source_text("stale target");

        let stale_target = CanonicalCheckerContext::new_with_module_resolutions(
            bindings,
            vec![
                (importer_file, &importer.arena),
                (target_file, &target.arena),
            ],
            CanonicalCheckerOptions::default(),
            CanonicalModuleResolutionManifestInput::new([
                CanonicalModuleResolutionEntry::resolved(specifier, resolved(target_file)),
            ]),
        )
        .unwrap_err();
        assert!(matches!(
            stale_target,
            CanonicalCheckerContextError::ArenaRevisionMismatch {
                file,
                ..
            } if file == target_file
        ));
    }
}
