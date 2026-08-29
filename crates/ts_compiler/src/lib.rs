//! Compiler Program and source-file graph foundations.

mod project_graph;
mod top_level_await;

pub use project_graph::{
    ProgramGraphConfig, ProgramGraphMissingEvidence, ProgramGraphPackageScopeDecision,
    ProgramGraphPackageScopeEvent, ProgramGraphPackageScopeObservation,
    ProgramGraphPackageScopeReadError, ProgramGraphReference, ProgramGraphReferenceKind,
    ProgramGraphReferenceTarget, ProgramGraphResolution, ProgramGraphResolutionKind,
    ProgramGraphResolutionRequest, ProgramGraphRoot, ProgramGraphSnapshot, ProgramGraphSource,
    ProgramGraphTarget,
};

use std::{
    cmp::Ordering,
    collections::{BTreeMap, BTreeSet, HashSet, VecDeque},
    path::Path,
};

use ts_ast::{FileId, Node, NodeData, NodeFlags, NodeId, NodeRef, SyntaxKind};
use ts_binder::{
    BindResult, CanonicalBindError, CanonicalBinder, CanonicalDeclarationError,
    CanonicalModuleAugmentation, CanonicalModuleState, CanonicalNameResolutionError,
    CanonicalSourceFileFacts, CanonicalSourceLanguage, EscapedName, SymbolFlags,
    bind_source_file_in_file, bind_source_file_in_file_with_facts,
};
use ts_checker::semantic::alias::{
    CanonicalAliasResolution, CanonicalAliasResolutionError, CanonicalAliasResolutionEvent,
    CanonicalAliasTargetUnavailable,
};
use ts_checker::semantic::formatter::FunctionTypeDisplayUnavailable;
use ts_checker::semantic::production::{CanonicalJsxRuntime, CanonicalJsxRuntimeEvidence};
use ts_checker::semantic::{
    AliasTargetState, ArrayTypeError, CanonicalAliasQueryError, CanonicalCheckerContext,
    CanonicalCheckerContextError, CanonicalCheckerDiagnosticRange, CanonicalCheckerOptions,
    CanonicalGlobalInitializationError, CanonicalGlobalTypeInitializationError,
    CanonicalHelperSignatureError, CanonicalModuleExportQueryError, CanonicalModuleResolutionEntry,
    CanonicalModuleResolutionManifestInput, CanonicalModuleResolutionMode,
    CanonicalResolvedModuleInput, DeclaredTypeError, DeclaredTypeUnavailable, DerivedTypeError,
    EnumTypeError, IntrinsicBootstrapOptions, RelationUnavailable, SourceCheckError,
    SourceLiteralCacheError, SymbolMergeError, TypeDisplayUnavailable, TypeNodeUnavailable,
};
use ts_checker::{
    CheckDiagnostic, CheckResult, CheckerOptions, EnumConstantValue as CheckerConstantValue,
    ProgramSource, TypeId, TypeKind, check_program_with_paths, empty_check_result,
};
use ts_config::{
    ConfigDiagnostic, ConfigObservationLimits, ConfigResolutionObservation,
    resolve_config_file_with_observation,
};
use ts_core::{TextPos, TextRange};
use ts_diagnostics::{Category, Diagnostic, FormatError, message_by_code};
use ts_glob::{DiscoveryOptions, GlobPattern, discover_files};
use ts_module::{
    ModuleFormat, ResolutionOptions, Resolver, automatic_type_directive_names, parse_package_json,
};
use ts_options::{
    CompilerOptions, ModuleDetectionKind, ModuleKind, ModuleResolutionKind, PrinterSettings,
    ScriptTarget, parse_project_options,
};
use ts_parser::{
    ParseResult, parse_javascript_source_file, parse_jsx_source_file, parse_source_file,
};
use ts_path::{
    CaseSensitivity, FileExtension, canonicalize, change_extension, declaration_emit_extension,
    directory_path, is_absolute, remove_file_extension, resolve_path,
};
use ts_printer::{
    AmdDependency as PrinterAmdDependency, BUNDLE_EXTENDS_HELPER, EmitConstantValue, EmitContext,
    emit_declaration_file_with_semantics_and_options, emit_source_file_with_context,
    runtime_identifier_uses, source_needs_extends_helper,
};
use ts_scanner::Scanner;
use ts_sourcemap::{SourceMap, SourceMapBuilder};
use ts_vfs::FileSystem;

pub use ts_checker::semantic::artifact_queries::CanonicalArtifactQueryError;
pub use ts_checker::semantic::{
    CanonicalModuleResolutionLookup, CanonicalTypeFormatFlags,
    SemanticStoreId as CanonicalSemanticStoreId, SemanticSymbolId as CanonicalSymbolId,
    TypeId as CanonicalTypeId,
};

/// One parsed source file owned by a Program.
#[derive(Debug)]
pub struct SourceFile {
    pub id: FileId,
    pub file_name: String,
    pub source_text: String,
    pub parse: ParseResult,
    pub binding: BindResult,
    pub checking: CheckResult,
    pub is_default_library: bool,
    implied_node_format: ModuleKind,
}

impl SourceFile {
    /// Returns a program-wide identity when `node` belongs to this file's arena.
    #[must_use]
    pub fn node_ref(&self, node: NodeId) -> Option<NodeRef> {
        if self.binding.file_id() != Some(self.id)
            || !self
                .binding
                .is_for_source(&self.parse.arena, self.parse.source_file)
        {
            return None;
        }
        self.parse
            .arena
            .get(node)
            .map(|_| NodeRef::new(self.parse.arena.id(), self.id, node))
    }
}

fn bundle_namespace_path(source: &SourceFile, declaration: NodeId) -> Option<Vec<String>> {
    let mut path = Vec::new();
    let mut current = Some(declaration);
    while let Some(id) = current {
        let node = source.parse.arena.get(id)?;
        if let NodeData::ModuleDeclaration(module) = &node.data {
            let name = match &source.parse.arena.get(module.name)?.data {
                NodeData::Identifier(name) => &name.text,
                NodeData::StringLiteral(name) => &name.text,
                _ => return None,
            };
            path.push(name.clone());
        }
        current = node.parent;
    }
    path.reverse();
    Some(path)
}

fn bundle_namespace_members(sources: &[&SourceFile]) -> BTreeMap<Vec<String>, BTreeSet<String>> {
    let value_flags = SymbolFlags::FUNCTION
        | SymbolFlags::CLASS
        | SymbolFlags::FUNCTION_SCOPED_VARIABLE
        | SymbolFlags::BLOCK_SCOPED_VARIABLE
        | SymbolFlags::REGULAR_ENUM
        | SymbolFlags::CONST_ENUM
        | SymbolFlags::VALUE_MODULE
        | SymbolFlags::NAMESPACE_MODULE;
    let mut result = BTreeMap::<Vec<String>, BTreeSet<String>>::new();
    for source in sources {
        for (id, node) in source.parse.arena.iter() {
            let NodeData::ModuleDeclaration(module) = &node.data else {
                continue;
            };
            let Some(path) = bundle_namespace_path(source, id) else {
                continue;
            };
            let symbol = source
                .binding
                .node_symbols
                .get(&module.name)
                .copied()
                .or_else(|| source.binding.node_symbols.get(&id).copied());
            let Some(symbol) = symbol.and_then(|symbol| source.binding.symbols.get(symbol)) else {
                continue;
            };
            let members = result.entry(path).or_default();
            for (name, member) in symbol.members.iter() {
                if source
                    .binding
                    .symbols
                    .get(member)
                    .is_some_and(|member| member.flags.intersects(value_flags))
                {
                    members.insert(name.to_owned());
                }
            }
        }
    }
    result
}

/// A diagnostic produced while constructing or parsing a Program.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ProgramDiagnostic {
    pub file_name: Option<String>,
    pub range: Option<TextRange>,
    pub code: Option<u32>,
    pub category: Category,
    pub message: String,
    /// Related records owned by this diagnostic in their canonical order.
    ///
    /// These records are deliberately nested instead of entering Program's
    /// top-level diagnostic stream. Canonical conversion validates every
    /// located record against this Program before publishing the primary.
    pub related_information: Vec<ProgramDiagnostic>,
}

/// Pinned `ast.CompareDiagnostics` order adapted to the owned Program record.
///
/// `ProgramDiagnostic::message` is already the rendered ownership boundary, so
/// it supplies the deterministic message-argument/chain tie-break after the
/// exact path, location, and code keys. Related records retain the pinned
/// longer-first ordering and recurse through the same comparator.
fn compare_program_diagnostics(left: &ProgramDiagnostic, right: &ProgramDiagnostic) -> Ordering {
    left.file_name
        .as_deref()
        .unwrap_or("")
        .cmp(right.file_name.as_deref().unwrap_or(""))
        .then_with(|| compare_program_diagnostic_ranges(left.range, right.range))
        .then_with(|| left.code.cmp(&right.code))
        .then_with(|| left.message.cmp(&right.message))
        .then_with(|| {
            right
                .related_information
                .len()
                .cmp(&left.related_information.len())
        })
        .then_with(|| {
            left.related_information
                .iter()
                .zip(&right.related_information)
                .map(|(left, right)| compare_program_diagnostics(left, right))
                .find(|ordering| !ordering.is_eq())
                .unwrap_or(Ordering::Equal)
        })
}

fn compare_program_diagnostic_ranges(
    left: Option<TextRange>,
    right: Option<TextRange>,
) -> Ordering {
    match (left, right) {
        (Some(left), Some(right)) => left
            .start
            .cmp(&right.start)
            .then_with(|| left.end.cmp(&right.end)),
        (None, Some(_)) => Ordering::Less,
        (Some(_), None) => Ordering::Greater,
        (None, None) => Ordering::Equal,
    }
}

/// Why a resolved module was not admitted to the source graph.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CanonicalModuleTargetOmission {
    NoResolve,
    JavaScriptDisabled,
    NodeModuleJavaScriptDepth { depth: u32, limit: i64 },
}

/// A typed failure from the experimental canonical diagnostics pipeline.
///
/// These failures are construction boundaries, not TypeScript diagnostics. A
/// failed attempt never returns a partially checked [`Program`] and never
/// falls back to the legacy checker.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum CanonicalProgramCheckError {
    UnsupportedSourceKind {
        file_name: String,
        script_kind: ts_path::ScriptKind,
    },
    FixedModuleFormatUnsupported {
        file_name: String,
    },
    ImportMetaModuleIndicatorUnsupported {
        file_name: String,
    },
    NodeModuleFactsUnsupported {
        file_name: String,
        module: ModuleKind,
        module_resolution: ModuleResolutionKind,
    },
    PlainEsmModuleResolutionUnsupported {
        file_name: String,
        module: ModuleKind,
        module_resolution: ModuleResolutionKind,
    },
    ModuleSpecifierResolutionModeUnsupported(NodeRef),
    DeclarationFileCheckingUnsupported {
        file_name: String,
    },
    ProjectReferencesUnsupported {
        config_path: String,
    },
    Bind {
        file_name: String,
        error: CanonicalBindError,
    },
    DeclarationBind {
        file_name: String,
        error: CanonicalDeclarationError,
    },
    Context(CanonicalCheckerContextError),
    SourceCheck {
        file_name: String,
        error: SourceCheckError,
    },
    ImportHelper {
        file_name: String,
        node: NodeRef,
        error: Box<CanonicalImportHelperError>,
    },
    MissingBoundFile {
        file_name: String,
        file: FileId,
    },
    InvalidModuleSourceFile(NodeRef),
    InvalidModuleSpecifier(NodeRef),
    ExternalModuleTargetUnsupported {
        specifier: NodeRef,
        target_file_name: String,
    },
    OmittedModuleTargetUnsupported {
        specifier: NodeRef,
        target_file_name: String,
        reason: CanonicalModuleTargetOmission,
    },
    MissingResolvedModuleTarget {
        containing_file: String,
        specifier: NodeRef,
        resolved_file_name: String,
    },
    InvalidDiagnosticNode(NodeRef),
    InvalidDiagnosticRange {
        node: Option<NodeRef>,
        range_override: CanonicalCheckerDiagnosticRange,
    },
    InvalidRelatedDiagnosticNode {
        primary_code: u32,
        index: usize,
        node: NodeRef,
    },
    DiagnosticFormat(FormatError),
}

/// A helper dependency could not provide an exact export, value, or signature.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum CanonicalImportHelperError {
    ModuleSymbolUnavailable {
        file_name: String,
    },
    Export(CanonicalModuleExportQueryError),
    Alias(CanonicalAliasQueryError),
    AliasUnresolved {
        alias: CanonicalSymbolId,
        resolution: CanonicalAliasResolution,
    },
    AliasEvents {
        symbol: CanonicalSymbolId,
        events: Vec<CanonicalAliasResolutionEvent>,
    },
    Signature(CanonicalHelperSignatureError),
}

impl std::fmt::Display for CanonicalImportHelperError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Export(error) => error.fmt(formatter),
            Self::Alias(error) => error.fmt(formatter),
            Self::Signature(error) => error.fmt(formatter),
            error => write!(formatter, "helper dependency is unavailable: {error:?}"),
        }
    }
}

impl std::error::Error for CanonicalImportHelperError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Export(error) => Some(error),
            Self::Alias(error) => Some(error),
            Self::Signature(error) => Some(error),
            _ => None,
        }
    }
}

/// Stable corpus classification for a canonical checker construction failure.
///
/// Capability codes name an intentionally unsupported port-map boundary.
/// Invariant codes name a failure that must stay fatal. Corpus tooling can use
/// this typed envelope without parsing [`CanonicalProgramCheckError`]'s display
/// text or weakening the compiler's fail-closed behavior.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CanonicalProgramCheckFailureClass {
    Unsupported { capability_code: &'static str },
    Fatal { invariant_code: &'static str },
}

impl CanonicalProgramCheckFailureClass {
    #[must_use]
    pub const fn code(self) -> &'static str {
        match self {
            Self::Unsupported { capability_code } => capability_code,
            Self::Fatal { invariant_code } => invariant_code,
        }
    }

    #[must_use]
    pub const fn is_unsupported(self) -> bool {
        matches!(self, Self::Unsupported { .. })
    }
}

impl CanonicalProgramCheckError {
    /// Returns the stable typed corpus classification for this failure.
    #[must_use]
    pub fn failure_class(&self) -> CanonicalProgramCheckFailureClass {
        if let Some(capability_code) = canonical_program_capability_code(self) {
            CanonicalProgramCheckFailureClass::Unsupported { capability_code }
        } else {
            CanonicalProgramCheckFailureClass::Fatal {
                invariant_code: canonical_program_invariant_code(self),
            }
        }
    }

    /// Returns whether this failure is an explicit, not-yet-ported semantic
    /// boundary rather than a violated compiler invariant.
    ///
    /// Corpus drivers may retain these failures as unsupported coverage. A
    /// caller must not use the classification to suppress structural,
    /// provenance, cache, catalog, or diagnostic-conversion failures.
    #[must_use]
    pub fn is_unsupported_boundary(&self) -> bool {
        self.failure_class().is_unsupported()
    }
}

fn canonical_program_capability_code(error: &CanonicalProgramCheckError) -> Option<&'static str> {
    match error {
        CanonicalProgramCheckError::UnsupportedSourceKind { .. } => Some("C00.SOURCE_KIND"),
        CanonicalProgramCheckError::FixedModuleFormatUnsupported { .. } => {
            Some("M00.FIXED_MODULE_FORMAT")
        }
        CanonicalProgramCheckError::ImportMetaModuleIndicatorUnsupported { .. } => {
            Some("M03.IMPORT_META_MODULE_MODE")
        }
        CanonicalProgramCheckError::NodeModuleFactsUnsupported { .. } => {
            Some("M00.NODE_MODULE_FACTS")
        }
        CanonicalProgramCheckError::PlainEsmModuleResolutionUnsupported { .. } => {
            Some("M00.PLAIN_ESM_MODE")
        }
        CanonicalProgramCheckError::ModuleSpecifierResolutionModeUnsupported(_) => {
            Some("M00.SPECIFIER_RESOLUTION_MODE")
        }
        CanonicalProgramCheckError::DeclarationFileCheckingUnsupported { .. } => {
            Some("M00.DECLARATION_FILE")
        }
        CanonicalProgramCheckError::ProjectReferencesUnsupported { .. } => {
            Some("M00.PROJECT_REFERENCES")
        }
        CanonicalProgramCheckError::DeclarationBind { error, .. }
            if canonical_declaration_error_is_unsupported(error) =>
        {
            Some("B02.DECLARATION_FAMILY")
        }
        CanonicalProgramCheckError::Context(error) if context_error_is_unsupported(error) => {
            Some("T04.GLOBAL_CONTEXT")
        }
        CanonicalProgramCheckError::SourceCheck { error, .. } => {
            source_check_capability_code(error)
        }
        CanonicalProgramCheckError::ImportHelper { error, .. } => {
            import_helper_capability_code(error)
        }
        CanonicalProgramCheckError::ExternalModuleTargetUnsupported { .. } => {
            Some("M00.EXTERNAL_MODULE_TARGET")
        }
        CanonicalProgramCheckError::OmittedModuleTargetUnsupported { .. } => {
            Some("M00.OMITTED_MODULE_TARGET")
        }
        CanonicalProgramCheckError::Bind { .. }
        | CanonicalProgramCheckError::DeclarationBind { .. }
        | CanonicalProgramCheckError::Context(_)
        | CanonicalProgramCheckError::MissingBoundFile { .. }
        | CanonicalProgramCheckError::InvalidModuleSourceFile(_)
        | CanonicalProgramCheckError::InvalidModuleSpecifier(_)
        | CanonicalProgramCheckError::MissingResolvedModuleTarget { .. }
        | CanonicalProgramCheckError::InvalidDiagnosticNode(_)
        | CanonicalProgramCheckError::InvalidDiagnosticRange { .. }
        | CanonicalProgramCheckError::InvalidRelatedDiagnosticNode { .. }
        | CanonicalProgramCheckError::DiagnosticFormat(_) => None,
    }
}

fn import_helper_capability_code(error: &CanonicalImportHelperError) -> Option<&'static str> {
    match error {
        CanonicalImportHelperError::ModuleSymbolUnavailable { .. } => {
            Some("M00.IMPORT_HELPER_MODULE")
        }
        CanonicalImportHelperError::Export(
            CanonicalModuleExportQueryError::UnsupportedModule(_)
            | CanonicalModuleExportQueryError::UnsupportedExportCache(_),
        ) => Some("M00.IMPORT_HELPER_EXPORT"),
        CanonicalImportHelperError::Export(CanonicalModuleExportQueryError::Target(reason))
            if alias_target_error_is_unsupported(*reason) =>
        {
            Some("M00.IMPORT_HELPER_EXPORT")
        }
        CanonicalImportHelperError::Export(CanonicalModuleExportQueryError::Source(error)) => {
            source_check_capability_code(error)
        }
        CanonicalImportHelperError::Alias(error) if alias_query_error_is_unsupported(*error) => {
            Some("M00.IMPORT_HELPER_ALIAS")
        }
        CanonicalImportHelperError::AliasUnresolved { resolution, .. }
            if resolution.target == AliasTargetState::Unknown =>
        {
            Some("M00.IMPORT_HELPER_ALIAS")
        }
        CanonicalImportHelperError::AliasEvents { .. } => Some("M00.IMPORT_HELPER_ALIAS"),
        CanonicalImportHelperError::Signature(
            CanonicalHelperSignatureError::ProviderUnavailable { .. }
            | CanonicalHelperSignatureError::ArityUnavailable { .. },
        ) => Some("T06.IMPORT_HELPER_SIGNATURE"),
        CanonicalImportHelperError::Signature(CanonicalHelperSignatureError::DeclaredType(
            error,
        )) if declared_type_error_is_unsupported(error) => Some("T06.IMPORT_HELPER_SIGNATURE"),
        CanonicalImportHelperError::Export(_)
        | CanonicalImportHelperError::Alias(_)
        | CanonicalImportHelperError::AliasUnresolved { .. }
        | CanonicalImportHelperError::Signature(_) => None,
    }
}

fn alias_query_error_is_unsupported(error: CanonicalAliasQueryError) -> bool {
    match error {
        CanonicalAliasQueryError::AliasResolution(
            CanonicalAliasResolutionError::TargetUnavailable { reason, .. },
        )
        | CanonicalAliasQueryError::SymbolFlags(
            ts_checker::semantic::alias_flags::CanonicalSymbolFlagsError::AliasResolution(
                CanonicalAliasResolutionError::TargetUnavailable { reason, .. },
            ),
        ) => alias_target_error_is_unsupported(reason),
        _ => false,
    }
}

fn source_check_capability_code(error: &SourceCheckError) -> Option<&'static str> {
    match error {
        SourceCheckError::Unsupported(_) => Some("E00.SOURCE_SYNTAX"),
        SourceCheckError::DeclaredType(error) if declared_type_error_is_unsupported(error) => {
            Some(match error {
                DeclaredTypeError::Unavailable(_)
                | DeclaredTypeError::Host(_)
                | DeclaredTypeError::NameResolverHost(_)
                | DeclaredTypeError::TypeResolutionTarget(_) => "T05.DECLARED_TYPE",
                DeclaredTypeError::TypeNodeUnavailable(_) => "T06.TYPE_NODE",
                DeclaredTypeError::Enum(_) => "E00.ENUM_TYPE",
                DeclaredTypeError::NameResolution(_) => "B03.NAME_RESOLUTION",
            })
        }
        SourceCheckError::RelationUnavailable(error) if relation_error_is_unsupported(error) => {
            Some("R01.RELATION")
        }
        SourceCheckError::TypeDisplayUnavailable(error) if display_error_is_unsupported(error) => {
            Some("T07.TYPE_DISPLAY")
        }
        SourceCheckError::LiteralCache(error) if literal_cache_error_is_unsupported(error) => {
            Some("T06.LITERAL_UNION")
        }
        SourceCheckError::ArrayType(error) if array_type_error_is_unsupported(error) => {
            Some("T06.ARRAY_TYPE")
        }
        SourceCheckError::DerivedType(error) if derived_type_error_is_unsupported(error) => {
            Some("E00.DERIVED_TYPE")
        }
        SourceCheckError::Provenance(_)
        | SourceCheckError::DeclaredType(_)
        | SourceCheckError::RelationUnavailable(_)
        | SourceCheckError::TypeDisplayUnavailable(_)
        | SourceCheckError::LiteralCache(_)
        | SourceCheckError::ObjectLiteral(_)
        | SourceCheckError::ArrayType(_)
        | SourceCheckError::DerivedType(_)
        | SourceCheckError::Assertion(_)
        | SourceCheckError::Assignment(_)
        | SourceCheckError::Arrow(_)
        | SourceCheckError::Function(_)
        | SourceCheckError::Variable(_)
        | SourceCheckError::Call(_)
        | SourceCheckError::Enum(_)
        | SourceCheckError::Import(_)
        | SourceCheckError::Class(_)
        | SourceCheckError::Property(_)
        | SourceCheckError::Element(_)
        | SourceCheckError::PrimitiveOperator(_)
        | SourceCheckError::LogicalOperator(_)
        | SourceCheckError::Conditional(_)
        | SourceCheckError::MissingDiagnostic(_) => None,
    }
}

fn canonical_program_invariant_code(error: &CanonicalProgramCheckError) -> &'static str {
    match error {
        CanonicalProgramCheckError::Bind { .. } => "INV.PROGRAM.BIND",
        CanonicalProgramCheckError::DeclarationBind { .. } => "INV.PROGRAM.DECLARATION_BIND",
        CanonicalProgramCheckError::Context(_) => "INV.PROGRAM.CHECKER_CONTEXT",
        CanonicalProgramCheckError::SourceCheck { error, .. } => source_check_invariant_code(error),
        CanonicalProgramCheckError::ImportHelper { .. } => "INV.PROGRAM.IMPORT_HELPER",
        CanonicalProgramCheckError::MissingBoundFile { .. } => "INV.PROGRAM.MISSING_BOUND_FILE",
        CanonicalProgramCheckError::InvalidModuleSourceFile(_) => {
            "INV.PROGRAM.INVALID_MODULE_SOURCE"
        }
        CanonicalProgramCheckError::InvalidModuleSpecifier(_) => {
            "INV.PROGRAM.INVALID_MODULE_SPECIFIER"
        }
        CanonicalProgramCheckError::MissingResolvedModuleTarget { .. } => {
            "INV.PROGRAM.MISSING_MODULE_TARGET"
        }
        CanonicalProgramCheckError::InvalidDiagnosticNode(_) => {
            "INV.PROGRAM.INVALID_DIAGNOSTIC_NODE"
        }
        CanonicalProgramCheckError::InvalidDiagnosticRange { .. } => {
            "INV.PROGRAM.INVALID_DIAGNOSTIC_RANGE"
        }
        CanonicalProgramCheckError::InvalidRelatedDiagnosticNode { .. } => {
            "INV.PROGRAM.INVALID_RELATED_DIAGNOSTIC"
        }
        CanonicalProgramCheckError::DiagnosticFormat(_) => "INV.PROGRAM.DIAGNOSTIC_FORMAT",
        CanonicalProgramCheckError::UnsupportedSourceKind { .. }
        | CanonicalProgramCheckError::FixedModuleFormatUnsupported { .. }
        | CanonicalProgramCheckError::ImportMetaModuleIndicatorUnsupported { .. }
        | CanonicalProgramCheckError::NodeModuleFactsUnsupported { .. }
        | CanonicalProgramCheckError::PlainEsmModuleResolutionUnsupported { .. }
        | CanonicalProgramCheckError::ModuleSpecifierResolutionModeUnsupported(_)
        | CanonicalProgramCheckError::DeclarationFileCheckingUnsupported { .. }
        | CanonicalProgramCheckError::ProjectReferencesUnsupported { .. }
        | CanonicalProgramCheckError::ExternalModuleTargetUnsupported { .. }
        | CanonicalProgramCheckError::OmittedModuleTargetUnsupported { .. } => {
            "INV.PROGRAM.FAILURE_CLASSIFICATION"
        }
    }
}

fn source_check_invariant_code(error: &SourceCheckError) -> &'static str {
    match error {
        SourceCheckError::Provenance(_) => "INV.SOURCE.PROVENANCE",
        SourceCheckError::Unsupported(_) => "INV.SOURCE.FAILURE_CLASSIFICATION",
        SourceCheckError::DeclaredType(_) => "INV.SOURCE.DECLARED_TYPE",
        SourceCheckError::RelationUnavailable(_) => "INV.SOURCE.RELATION",
        SourceCheckError::TypeDisplayUnavailable(_) => "INV.SOURCE.TYPE_DISPLAY",
        SourceCheckError::LiteralCache(_) => "INV.SOURCE.LITERAL_CACHE",
        SourceCheckError::ObjectLiteral(_) => "INV.SOURCE.OBJECT_LITERAL",
        SourceCheckError::ArrayType(_) => "INV.SOURCE.ARRAY_TYPE",
        SourceCheckError::DerivedType(_) => "INV.SOURCE.DERIVED_TYPE",
        SourceCheckError::Assertion(_) => "INV.SOURCE.ASSERTION",
        SourceCheckError::Assignment(_) => "INV.SOURCE.ASSIGNMENT",
        SourceCheckError::Arrow(_) => "INV.SOURCE.ARROW",
        SourceCheckError::Function(_) => "INV.SOURCE.FUNCTION",
        SourceCheckError::Variable(_) => "INV.SOURCE.VARIABLE",
        SourceCheckError::Call(_) => "INV.SOURCE.CALL",
        SourceCheckError::Enum(_) => "INV.SOURCE.ENUM",
        SourceCheckError::Import(_) => "INV.SOURCE.IMPORT",
        SourceCheckError::Class(_) => "INV.SOURCE.CLASS",
        SourceCheckError::Property(_) => "INV.SOURCE.PROPERTY",
        SourceCheckError::Element(_) => "INV.SOURCE.ELEMENT",
        SourceCheckError::PrimitiveOperator(_) => "INV.SOURCE.PRIMITIVE_OPERATOR",
        SourceCheckError::LogicalOperator(_) => "INV.SOURCE.LOGICAL_OPERATOR",
        SourceCheckError::Conditional(_) => "INV.SOURCE.CONDITIONAL",
        SourceCheckError::MissingDiagnostic(_) => "INV.SOURCE.MISSING_DIAGNOSTIC",
    }
}

fn context_error_is_unsupported(error: &CanonicalCheckerContextError) -> bool {
    match error {
        CanonicalCheckerContextError::GlobalInitialization(error) => {
            global_initialization_error_is_unsupported(error)
        }
        CanonicalCheckerContextError::Extraction(_)
        | CanonicalCheckerContextError::DuplicateFileInOrder(_)
        | CanonicalCheckerContextError::DuplicateArenaInOrder { .. }
        | CanonicalCheckerContextError::ExtraOrderedFile(_)
        | CanonicalCheckerContextError::MissingOrderedFile(_)
        | CanonicalCheckerContextError::ArenaMismatch { .. }
        | CanonicalCheckerContextError::MissingSourceFileFacts(_)
        | CanonicalCheckerContextError::SourceFileProvenance { .. }
        | CanonicalCheckerContextError::MissingSourceFileRoot(_)
        | CanonicalCheckerContextError::InvalidSourceFileRoot { .. }
        | CanonicalCheckerContextError::SourceFileHasParent { .. }
        | CanonicalCheckerContextError::UnboundSourceFile(_)
        | CanonicalCheckerContextError::BoundNodeNowUnreachable(_)
        | CanonicalCheckerContextError::NewlyReachableUnboundNode(_)
        | CanonicalCheckerContextError::ArenaRevisionMismatch { .. }
        | CanonicalCheckerContextError::UnownedBoundNode(_)
        | CanonicalCheckerContextError::SourceRegistrationFailed(_)
        | CanonicalCheckerContextError::Bootstrap(_)
        | CanonicalCheckerContextError::ModuleResolutions(_)
        | CanonicalCheckerContextError::AliasTargetHost(_)
        | CanonicalCheckerContextError::StrictBuiltinIteratorReturnClaim { .. }
        | CanonicalCheckerContextError::StrictFunctionTypesClaim { .. } => false,
    }
}

fn global_initialization_error_is_unsupported(error: &CanonicalGlobalInitializationError) -> bool {
    match error {
        CanonicalGlobalInitializationError::ScriptGlobalThisDeclaration { .. }
        | CanonicalGlobalInitializationError::UndefinedValueDeclaration(_) => true,
        CanonicalGlobalInitializationError::GlobalTypes(error) => {
            global_type_initialization_error_is_unsupported(error)
        }
        CanonicalGlobalInitializationError::Merge(error) => merge_error_is_unsupported(error),
        CanonicalGlobalInitializationError::ModuleAugmentationTarget(error) => {
            alias_target_error_is_unsupported(*error)
        }
        CanonicalGlobalInitializationError::MissingBootstrap
        | CanonicalGlobalInitializationError::MissingFile(_)
        | CanonicalGlobalInitializationError::MissingSourceFileFacts(_)
        | CanonicalGlobalInitializationError::InvalidTable { .. }
        | CanonicalGlobalInitializationError::InvalidGlobals(_)
        | CanonicalGlobalInitializationError::InvalidSymbol(_)
        | CanonicalGlobalInitializationError::MissingSourceFileSymbol(_)
        | CanonicalGlobalInitializationError::InvalidUmdInsertion { .. }
        | CanonicalGlobalInitializationError::UnexpectedUmdCollision { .. }
        | CanonicalGlobalInitializationError::InvalidAugmentationName(_)
        | CanonicalGlobalInitializationError::MissingAugmentationSymbol(_)
        | CanonicalGlobalInitializationError::MissingAugmentationDeclaration(_)
        | CanonicalGlobalInitializationError::InvalidDeclarationProvenance(_)
        | CanonicalGlobalInitializationError::UnexpectedUndefinedCollision
        | CanonicalGlobalInitializationError::InvalidUndefinedInsertion { .. }
        | CanonicalGlobalInitializationError::DeclaredTypeHost(_) => false,
    }
}

fn global_type_initialization_error_is_unsupported(
    error: &CanonicalGlobalTypeInitializationError,
) -> bool {
    match error {
        CanonicalGlobalTypeInitializationError::NameResolution(error) => {
            name_resolution_error_is_unsupported(error)
        }
        CanonicalGlobalTypeInitializationError::DeclaredType(error) => {
            declared_type_error_is_unsupported(error)
        }
        CanonicalGlobalTypeInitializationError::MissingBootstrap
        | CanonicalGlobalTypeInitializationError::InvalidGlobals(_)
        | CanonicalGlobalTypeInitializationError::InvalidSymbol(_)
        | CanonicalGlobalTypeInitializationError::InvalidType(_)
        | CanonicalGlobalTypeInitializationError::InvalidValueSymbolLinks(_)
        | CanonicalGlobalTypeInitializationError::InvalidAnonymousType
        | CanonicalGlobalTypeInitializationError::InvalidAnonymousTypeMembers(_)
        | CanonicalGlobalTypeInitializationError::InvalidGenericTarget(_)
        | CanonicalGlobalTypeInitializationError::InvalidTypeReference(_)
        | CanonicalGlobalTypeInitializationError::InvalidInstantiationCache(_)
        | CanonicalGlobalTypeInitializationError::InvalidGlobalObjectDeclaration(_)
        | CanonicalGlobalTypeInitializationError::InvalidGlobalObjectBaseResolution(_) => false,
    }
}

fn merge_error_is_unsupported(error: &SymbolMergeError) -> bool {
    match error {
        SymbolMergeError::AliasResolutionRequired(_)
        | SymbolMergeError::DiagnosticRequired { .. }
        | SymbolMergeError::RecursiveMerge { .. } => true,
        SymbolMergeError::InvalidSymbol(_)
        | SymbolMergeError::InvalidTable(_)
        | SymbolMergeError::InvalidMergedParent(_)
        | SymbolMergeError::MissingValueDeclarationKind(_)
        | SymbolMergeError::RedirectInvariant { .. }
        | SymbolMergeError::StoreInvariant(_) => false,
    }
}

fn canonical_declaration_error_is_unsupported(error: &CanonicalDeclarationError) -> bool {
    match error {
        CanonicalDeclarationError::JavaScriptDeclarationsDeferred(_)
        | CanonicalDeclarationError::CommonJsDeclarationsDeferred(_)
        | CanonicalDeclarationError::UnsupportedDeclarationFamily(_) => true,
        CanonicalDeclarationError::UnboundFile(_)
        | CanonicalDeclarationError::WrongArena { .. }
        | CanonicalDeclarationError::ArenaRevisionMismatch { .. }
        | CanonicalDeclarationError::UnboundNode(_)
        | CanonicalDeclarationError::InvalidSymbolTable(_)
        | CanonicalDeclarationError::InvalidParent(_)
        | CanonicalDeclarationError::InvalidLocalSymbol(_)
        | CanonicalDeclarationError::InvalidExportSymbol(_)
        | CanonicalDeclarationError::ExportSymbolMismatch { .. }
        | CanonicalDeclarationError::DynamicNameRequiresComputed(_)
        | CanonicalDeclarationError::JavaScriptFileKindRequired(_)
        | CanonicalDeclarationError::MissingContainingClassSymbol(_)
        | CanonicalDeclarationError::MissingSourceFileFacts(_)
        | CanonicalDeclarationError::DuplicateDeclarationDispatch(_) => false,
    }
}

fn literal_cache_error_is_unsupported(error: &SourceLiteralCacheError) -> bool {
    matches!(
        error,
        SourceLiteralCacheError::UnsupportedUnionConstituent(_)
    )
}

fn array_type_error_is_unsupported(error: &ArrayTypeError) -> bool {
    match error {
        ArrayTypeError::GlobalType(error) => global_type_initialization_error_is_unsupported(error),
        ArrayTypeError::UnsupportedCreationFlags(_)
        | ArrayTypeError::InvalidReference(_)
        | ArrayTypeError::InvalidArrayLiteralCache { .. }
        | ArrayTypeError::Capacity(_) => false,
    }
}

fn derived_type_error_is_unsupported(error: &DerivedTypeError) -> bool {
    match error {
        DerivedTypeError::ArrayType(error) => array_type_error_is_unsupported(error),
        DerivedTypeError::UnsupportedWideningType(_)
        | DerivedTypeError::RecursiveWideningType(_)
        | DerivedTypeError::RecursiveObjectLiteral(_) => true,
        DerivedTypeError::BootstrapUninitialized
        | DerivedTypeError::Type(_)
        | DerivedTypeError::MalformedObjectLiteral(_)
        | DerivedTypeError::InvalidRegularObjectLiteralCache { .. }
        | DerivedTypeError::InvalidWidenedTypeCache { .. }
        | DerivedTypeError::Capacity(_) => false,
    }
}

fn declared_type_error_is_unsupported(error: &DeclaredTypeError) -> bool {
    match error {
        DeclaredTypeError::Unavailable(error) => declared_type_unavailable_is_unsupported(error),
        DeclaredTypeError::TypeNodeUnavailable(error) => type_node_error_is_unsupported(error),
        DeclaredTypeError::Enum(EnumTypeError::Unsupported(_)) => true,
        DeclaredTypeError::NameResolution(error) => name_resolution_error_is_unsupported(error),
        DeclaredTypeError::Enum(EnumTypeError::Invariant(_))
        | DeclaredTypeError::Host(_)
        | DeclaredTypeError::NameResolverHost(_)
        | DeclaredTypeError::TypeResolutionTarget(_) => false,
    }
}

fn declared_type_unavailable_is_unsupported(error: &DeclaredTypeUnavailable) -> bool {
    match error {
        DeclaredTypeUnavailable::UnsupportedDeclaredType(_)
        | DeclaredTypeUnavailable::UnsupportedInterfaceHeritageResolution(_)
        | DeclaredTypeUnavailable::UnsupportedOuterTypeParameterContext { .. } => true,
        DeclaredTypeUnavailable::IntrinsicBootstrapNotInitialized
        | DeclaredTypeUnavailable::SymbolNotOwned(_)
        | DeclaredTypeUnavailable::AliasMergedWithDeclaredSymbol(_)
        | DeclaredTypeUnavailable::MissingDeclarations(_)
        | DeclaredTypeUnavailable::MissingValueDeclaration(_)
        | DeclaredTypeUnavailable::MissingOrForeignFacts(_)
        | DeclaredTypeUnavailable::DeclarationSymbolMismatch(_)
        | DeclaredTypeUnavailable::InvalidClassDeclaration(_)
        | DeclaredTypeUnavailable::InvalidInterfaceDeclaration(_)
        | DeclaredTypeUnavailable::PostGlobalNameResolutionUnavailable
        | DeclaredTypeUnavailable::InvalidTypeParameterSymbol(_)
        | DeclaredTypeUnavailable::InvalidTypeParameterDeclaration(_)
        | DeclaredTypeUnavailable::InvalidCachedDeclaredType { .. } => false,
    }
}

fn type_node_error_is_unsupported(error: &TypeNodeUnavailable) -> bool {
    match error {
        TypeNodeUnavailable::NamespaceAlias { error, .. } => alias_error_is_unsupported(*error),
        TypeNodeUnavailable::UnsupportedSyntax { .. }
        | TypeNodeUnavailable::JsDoc(_)
        | TypeNodeUnavailable::QualifiedTypeReference(_)
        | TypeNodeUnavailable::TypeArgumentsUnsupported(_)
        | TypeNodeUnavailable::MissingTypeReference(_)
        | TypeNodeUnavailable::ImportAliasTypeReference { .. }
        | TypeNodeUnavailable::ImportAliasCapabilityUnsupported(_)
        | TypeNodeUnavailable::JsDocImportTypeCapabilityUnsupported(_)
        | TypeNodeUnavailable::UnsupportedReferenceTarget { .. }
        | TypeNodeUnavailable::GenericReferenceUnsupported { .. }
        | TypeNodeUnavailable::GenericAliasConstraintUnsupported { .. }
        | TypeNodeUnavailable::GenericAliasInstantiationUnsupported { .. }
        | TypeNodeUnavailable::GenericAliasDefaultReferenceUnsupported { .. }
        | TypeNodeUnavailable::CircularGenericAliasDefault { .. }
        | TypeNodeUnavailable::JsDocTypeAlias(_)
        | TypeNodeUnavailable::UnsupportedUnionConstituent(_)
        | TypeNodeUnavailable::UnsupportedUnionConstituentType(_)
        | TypeNodeUnavailable::UnsupportedIntersectionConstituent(_)
        | TypeNodeUnavailable::UnsupportedIntersectionProperty(_)
        | TypeNodeUnavailable::UnsupportedIntersectionConstituentType(_)
        | TypeNodeUnavailable::UnsupportedIntersectionOptionalProperty(_)
        | TypeNodeUnavailable::UnsupportedIntersectionPropertyType(_)
        | TypeNodeUnavailable::UnsupportedTupleElementOrder { .. }
        | TypeNodeUnavailable::RecursiveTupleAliasUnsupported { .. } => true,
        TypeNodeUnavailable::InvalidParenthesizedType(_)
        | TypeNodeUnavailable::NamespaceAliasHost { .. }
        | TypeNodeUnavailable::InvalidTypeReference(_)
        | TypeNodeUnavailable::InvalidImportAliasTarget { .. }
        | TypeNodeUnavailable::InvalidJsDocImportTypeTarget { .. }
        | TypeNodeUnavailable::InvalidTypeAliasSymbol(_)
        | TypeNodeUnavailable::MissingTypeAliasDeclaration(_)
        | TypeNodeUnavailable::InvalidTypeAliasDeclaration(_)
        | TypeNodeUnavailable::InvalidCachedTypeAlias(_)
        | TypeNodeUnavailable::InvalidCachedSymbol { .. }
        | TypeNodeUnavailable::MissingGenericAliasMetadata(_)
        | TypeNodeUnavailable::InvalidGenericAliasInstantiationCache(_)
        | TypeNodeUnavailable::CheckerOptionMismatch { .. }
        | TypeNodeUnavailable::DiagnosticOwnerRequired(_)
        | TypeNodeUnavailable::MissingPlannedTypeAlias(_)
        | TypeNodeUnavailable::MissingPlannedTypeReference(_)
        | TypeNodeUnavailable::InvalidLiteralType(_)
        | TypeNodeUnavailable::MissingPlannedLiteralType(_)
        | TypeNodeUnavailable::InvalidLiteralCacheValue
        | TypeNodeUnavailable::InvalidCachedLiteralType(_)
        | TypeNodeUnavailable::InvalidUnionType(_)
        | TypeNodeUnavailable::MissingPlannedUnionType(_)
        | TypeNodeUnavailable::InvalidCachedUnionType(_)
        | TypeNodeUnavailable::InvalidIntersectionType(_)
        | TypeNodeUnavailable::MissingPlannedIntersectionType(_)
        | TypeNodeUnavailable::InvalidCachedIntersectionType(_)
        | TypeNodeUnavailable::InvalidCachedArrayType(_)
        | TypeNodeUnavailable::InvalidIndexedAccessType(_)
        | TypeNodeUnavailable::MissingPlannedIndexedAccessType(_)
        | TypeNodeUnavailable::InvalidKeyofType(_)
        | TypeNodeUnavailable::MissingPlannedKeyofType(_)
        | TypeNodeUnavailable::InvalidFunctionType(_)
        | TypeNodeUnavailable::InvalidFunctionSignature(_)
        | TypeNodeUnavailable::InvalidUnionAlias(_)
        | TypeNodeUnavailable::InvalidPreparedTypeQuery
        | TypeNodeUnavailable::LiteralTypeCapacity
        | TypeNodeUnavailable::InvalidTupleType(_)
        | TypeNodeUnavailable::MissingPlannedTupleType(_)
        | TypeNodeUnavailable::InvalidCachedTupleType(_)
        | TypeNodeUnavailable::ResolutionStackInvariant(_) => false,
    }
}

fn name_resolution_error_is_unsupported(error: &CanonicalNameResolutionError) -> bool {
    match error {
        CanonicalNameResolutionError::JavaScriptDeferred(_)
        | CanonicalNameResolutionError::CommonJsDeferred(_)
        | CanonicalNameResolutionError::JsDocDeferred(_)
        | CanonicalNameResolutionError::AliasResolutionUnavailable(_) => true,
        CanonicalNameResolutionError::WrongArena { .. }
        | CanonicalNameResolutionError::ArenaRevisionMismatch { .. }
        | CanonicalNameResolutionError::DeclarationsIncomplete(_)
        | CanonicalNameResolutionError::MissingSourceFileFacts(_)
        | CanonicalNameResolutionError::InvalidSymbolStore(_)
        | CanonicalNameResolutionError::UnboundLocation(_)
        | CanonicalNameResolutionError::InvalidHostSymbol(_)
        | CanonicalNameResolutionError::InvalidHostTable(_)
        | CanonicalNameResolutionError::MissingDeclarationSymbol(_)
        | CanonicalNameResolutionError::MissingArgumentsSymbol
        | CanonicalNameResolutionError::ForeignDeclarationAstUnavailable(_)
        | CanonicalNameResolutionError::InvalidSyntheticScope(_)
        | CanonicalNameResolutionError::MissingSyntheticScope(_)
        | CanonicalNameResolutionError::SyntheticScopeCycle(_) => false,
    }
}

fn relation_error_is_unsupported(error: &RelationUnavailable) -> bool {
    match error {
        RelationUnavailable::UnsupportedUnionConstituent(_)
        | RelationUnavailable::EnumRelation { .. }
        | RelationUnavailable::LateBoundMembers(_)
        | RelationUnavailable::RelationKeyTypeReferenceArguments(_)
        | RelationUnavailable::RelationKeyTypeReferenceTarget(_)
        | RelationUnavailable::RelationKeyTypeParameterConstraint(_)
        | RelationUnavailable::RelationKeyCyclicGenericArguments(_)
        | RelationUnavailable::UnresolvedStructuredMembers(_)
        | RelationUnavailable::UnsupportedStructuredType(_)
        | RelationUnavailable::StructuredSignatures(_)
        | RelationUnavailable::StructuredIndexInfos(_)
        | RelationUnavailable::UnsupportedProperty(_)
        | RelationUnavailable::UnresolvedPropertyType(_)
        | RelationUnavailable::StrictOptionalProperty(_)
        | RelationUnavailable::UnresolvedGlobalObject(_)
        | RelationUnavailable::StructuralRelation { .. } => true,
        RelationUnavailable::CanonicalGlobalType(error) => {
            global_type_initialization_error_is_unsupported(error)
        }
        RelationUnavailable::MissingBootstrap
        | RelationUnavailable::Type(_)
        | RelationUnavailable::Symbol(_)
        | RelationUnavailable::MalformedLiteral(_)
        | RelationUnavailable::MalformedUnion(_)
        | RelationUnavailable::MalformedIntersection(_)
        | RelationUnavailable::InvalidUnionAlias(_)
        | RelationUnavailable::InvalidUnionPreparation(_)
        | RelationUnavailable::UnionValidationCapacity(_)
        | RelationUnavailable::MalformedStructuredType(_)
        | RelationUnavailable::MalformedEnumType(_)
        | RelationUnavailable::InvalidSymbolMembers(_)
        | RelationUnavailable::RelationKeyType(_)
        | RelationUnavailable::InvalidUnknownLikeUnionState(_)
        | RelationUnavailable::InvalidStructuredMembers(_)
        | RelationUnavailable::UnavailableCanonicalArrayTarget(_)
        | RelationUnavailable::MalformedCanonicalArrayReference(_)
        | RelationUnavailable::UnresolvedFunctionType(_)
        | RelationUnavailable::UnresolvedSignatureReturn(_)
        | RelationUnavailable::MalformedFunctionType(_)
        | RelationUnavailable::StrictFunctionTypesOptionMismatch { .. } => false,
    }
}

fn display_error_is_unsupported(error: &TypeDisplayUnavailable) -> bool {
    match error {
        TypeDisplayUnavailable::Alias { .. }
        | TypeDisplayUnavailable::UnsupportedType { .. }
        | TypeDisplayUnavailable::UnsupportedUnionConstituent { .. }
        | TypeDisplayUnavailable::CyclicType(_)
        | TypeDisplayUnavailable::UniqueSymbolName(_)
        | TypeDisplayUnavailable::FullyQualifiedName { .. }
        | TypeDisplayUnavailable::Utf8TruncationBoundary { .. } => true,
        TypeDisplayUnavailable::FunctionType { reason, .. } => {
            function_display_error_is_unsupported(*reason)
        }
        TypeDisplayUnavailable::Type(_)
        | TypeDisplayUnavailable::MalformedType(_)
        | TypeDisplayUnavailable::InvalidUnion(_)
        | TypeDisplayUnavailable::InvalidIntersection(_)
        | TypeDisplayUnavailable::InvalidLiteralLinks(_)
        | TypeDisplayUnavailable::MissingBootstrap
        | TypeDisplayUnavailable::EmptyTupleType(_)
        | TypeDisplayUnavailable::SourceHost(_) => false,
        TypeDisplayUnavailable::ArrayType(error) => array_type_error_is_unsupported(error),
        TypeDisplayUnavailable::SymbolDisplay(error) => symbol_display_error_is_unsupported(*error),
    }
}

fn symbol_display_error_is_unsupported(error: ts_checker::semantic::SymbolDisplayError) -> bool {
    use ts_checker::semantic::SymbolDisplayError;
    match error {
        SymbolDisplayError::MissingModuleSpecifier(_)
        | SymbolDisplayError::CyclicAlias(_)
        | SymbolDisplayError::UnnameableSymbol(_) => true,
        SymbolDisplayError::Alias(error) => alias_error_is_unsupported(error),
        SymbolDisplayError::SourceHost(_)
        | SymbolDisplayError::AliasHost(_)
        | SymbolDisplayError::InvalidLocation(_)
        | SymbolDisplayError::InvalidModuleSpecifier(_)
        | SymbolDisplayError::InvalidSymbol(_)
        | SymbolDisplayError::InvalidTable(_)
        | SymbolDisplayError::InvalidAliasCache(_)
        | SymbolDisplayError::CyclicContainer(_) => false,
    }
}

fn alias_error_is_unsupported(error: CanonicalAliasResolutionError) -> bool {
    match error {
        CanonicalAliasResolutionError::TargetUnavailable { reason, .. } => {
            alias_target_error_is_unsupported(reason)
        }
        _ => false,
    }
}

fn alias_target_error_is_unsupported(reason: CanonicalAliasTargetUnavailable) -> bool {
    matches!(
        reason,
        CanonicalAliasTargetUnavailable::UnsupportedDeclarationFamily
            | CanonicalAliasTargetUnavailable::TargetProviderUnavailable
            | CanonicalAliasTargetUnavailable::ModuleResolutionCapabilityUnavailable(_)
            | CanonicalAliasTargetUnavailable::ModuleResolutionEntryAbsent(_)
            | CanonicalAliasTargetUnavailable::ModuleResolutionUnresolved(_)
            | CanonicalAliasTargetUnavailable::UnsupportedAliasDeclaration(_)
            | CanonicalAliasTargetUnavailable::UnsupportedDefaultAlias(_)
            | CanonicalAliasTargetUnavailable::UnsupportedLocalExport(_)
            | CanonicalAliasTargetUnavailable::ExportStarResolutionUnsupported { .. }
            | CanonicalAliasTargetUnavailable::ExportEqualsResolutionUnsupported { .. }
            | CanonicalAliasTargetUnavailable::CommonJsModuleUnsupported { .. }
            | CanonicalAliasTargetUnavailable::JavaScriptModuleUnsupported { .. }
            | CanonicalAliasTargetUnavailable::SyntheticModuleResolutionUnsupported { .. }
    )
}

const fn function_display_error_is_unsupported(reason: FunctionTypeDisplayUnavailable) -> bool {
    match reason {
        FunctionTypeDisplayUnavailable::SourceContext
        | FunctionTypeDisplayUnavailable::GenericAlias
        | FunctionTypeDisplayUnavailable::GenericSignature
        | FunctionTypeDisplayUnavailable::ThisParameter
        | FunctionTypeDisplayUnavailable::RestParameter
        | FunctionTypeDisplayUnavailable::InitializedParameter
        | FunctionTypeDisplayUnavailable::DestructuredParameter
        | FunctionTypeDisplayUnavailable::ParameterModifiers
        | FunctionTypeDisplayUnavailable::MissingParameterType
        | FunctionTypeDisplayUnavailable::MissingReturnType
        | FunctionTypeDisplayUnavailable::TypePredicate
        | FunctionTypeDisplayUnavailable::Overloads
        | FunctionTypeDisplayUnavailable::ConstructSignatures
        | FunctionTypeDisplayUnavailable::IndexSignatures
        | FunctionTypeDisplayUnavailable::CallableProperties
        | FunctionTypeDisplayUnavailable::UnvalidatedCallable => true,
        FunctionTypeDisplayUnavailable::PendingSignature
        | FunctionTypeDisplayUnavailable::UnresolvedReturn => false,
    }
}

impl std::fmt::Display for CanonicalProgramCheckError {
    #[allow(clippy::too_many_lines)] // Exhaustive typed compiler-boundary display.
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::UnsupportedSourceKind {
                file_name,
                script_kind,
            } => write!(
                formatter,
                "canonical checking does not support {script_kind:?} source '{file_name}'"
            ),
            Self::FixedModuleFormatUnsupported { file_name } => write!(
                formatter,
                "canonical checking cannot yet retain fixed module-format facts for '{file_name}'"
            ),
            Self::ImportMetaModuleIndicatorUnsupported { file_name } => write!(
                formatter,
                "canonical checking cannot yet retain the import.meta module indicator for '{file_name}'"
            ),
            Self::NodeModuleFactsUnsupported {
                file_name,
                module,
                module_resolution,
            } => write!(
                formatter,
                "canonical checking cannot yet derive Node module facts for '{file_name}' with module={module:?} and moduleResolution={module_resolution:?}"
            ),
            Self::PlainEsmModuleResolutionUnsupported {
                file_name,
                module,
                module_resolution,
            } => write!(
                formatter,
                "canonical module resolution for '{file_name}' requires a plain TypeScript source with ESM emit and Bundler resolution, got module={module:?} and moduleResolution={module_resolution:?}"
            ),
            Self::ModuleSpecifierResolutionModeUnsupported(specifier) => write!(
                formatter,
                "canonical module resolution cannot prove an ESM mode for module specifier {specifier:?}"
            ),
            Self::DeclarationFileCheckingUnsupported { file_name } => write!(
                formatter,
                "canonical checking of declaration file '{file_name}' requires skipLibCheck"
            ),
            Self::ProjectReferencesUnsupported { config_path } => write!(
                formatter,
                "canonical checking does not support project references in '{config_path}'"
            ),
            Self::Bind { file_name, error } => {
                write!(
                    formatter,
                    "canonical binding failed for '{file_name}': {error}"
                )
            }
            Self::DeclarationBind { file_name, error } => write!(
                formatter,
                "canonical declaration binding failed for '{file_name}': {error}"
            ),
            Self::Context(error) => {
                write!(formatter, "canonical checker construction failed: {error}")
            }
            Self::SourceCheck { file_name, error } => {
                write!(
                    formatter,
                    "canonical checking failed for '{file_name}': {error}"
                )
            }
            Self::ImportHelper {
                file_name,
                node,
                error,
            } => write!(
                formatter,
                "canonical helper query failed for '{file_name}' at {node:?}: {error}"
            ),
            Self::MissingBoundFile { file_name, file } => write!(
                formatter,
                "canonical binding omitted Program file {} ('{file_name}')",
                file.index()
            ),
            Self::InvalidModuleSourceFile(source) => write!(
                formatter,
                "canonical module resolution references malformed Program source {source:?}"
            ),
            Self::InvalidModuleSpecifier(specifier) => write!(
                formatter,
                "canonical module resolution references malformed Program node {specifier:?}"
            ),
            Self::ExternalModuleTargetUnsupported {
                specifier,
                target_file_name,
            } => write!(
                formatter,
                "canonical module specifier {specifier:?} resolved to script source '{target_file_name}', whose external-module diagnostic is not yet ported"
            ),
            Self::OmittedModuleTargetUnsupported {
                specifier,
                target_file_name,
                reason,
            } => write!(
                formatter,
                "canonical module specifier {specifier:?} resolved to '{target_file_name}', excluded by {reason:?}; checking this omitted target is not yet supported"
            ),
            Self::MissingResolvedModuleTarget {
                containing_file,
                specifier,
                resolved_file_name,
            } => write!(
                formatter,
                "canonical module specifier {specifier:?} in '{containing_file}' resolved to unretained Program file '{resolved_file_name}'"
            ),
            Self::InvalidDiagnosticNode(node) => write!(
                formatter,
                "canonical diagnostic references invalid Program node {node:?}"
            ),
            Self::InvalidDiagnosticRange {
                node,
                range_override,
            } => write!(
                formatter,
                "canonical diagnostic node {node:?} references invalid anchored range {range_override:?}"
            ),
            Self::InvalidRelatedDiagnosticNode {
                primary_code,
                index,
                node,
            } => write!(
                formatter,
                "canonical diagnostic TS{primary_code} related record {index} references invalid Program node {node:?}"
            ),
            Self::DiagnosticFormat(error) => std::fmt::Display::fmt(error, formatter),
        }
    }
}

impl std::error::Error for CanonicalProgramCheckError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Bind { error, .. } => Some(error),
            Self::DeclarationBind { error, .. } => Some(error),
            Self::Context(error) => Some(error),
            Self::SourceCheck { error, .. } => Some(error),
            Self::ImportHelper { error, .. } => Some(error.as_ref()),
            Self::DiagnosticFormat(error) => Some(error),
            Self::UnsupportedSourceKind { .. }
            | Self::FixedModuleFormatUnsupported { .. }
            | Self::ImportMetaModuleIndicatorUnsupported { .. }
            | Self::NodeModuleFactsUnsupported { .. }
            | Self::PlainEsmModuleResolutionUnsupported { .. }
            | Self::ModuleSpecifierResolutionModeUnsupported(_)
            | Self::ExternalModuleTargetUnsupported { .. }
            | Self::OmittedModuleTargetUnsupported { .. }
            | Self::DeclarationFileCheckingUnsupported { .. }
            | Self::ProjectReferencesUnsupported { .. }
            | Self::MissingBoundFile { .. }
            | Self::InvalidModuleSourceFile(_)
            | Self::InvalidModuleSpecifier(_)
            | Self::MissingResolvedModuleTarget { .. }
            | Self::InvalidDiagnosticNode(_)
            | Self::InvalidDiagnosticRange { .. }
            | Self::InvalidRelatedDiagnosticNode { .. } => None,
        }
    }
}

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
enum ProgramChecker {
    #[default]
    Legacy,
    Canonical,
}

/// Command-line overrides applied after loading a project configuration.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct ProgramOptionsOverride {
    pub no_check: Option<bool>,
    pub no_emit: Option<bool>,
    pub no_lib: Option<bool>,
}

struct ProgramConfigInputs {
    config_path: String,
    current_directory: String,
    root_names: Vec<String>,
    has_project_references: bool,
    options: CompilerOptions,
    diagnostics: Vec<ProgramDiagnostic>,
    graph_config: ProgramGraphConfig,
    config_resolution_observation: ConfigResolutionObservation,
}

struct ProgramConfigLoadError {
    diagnostics: Vec<ProgramDiagnostic>,
    config_resolution_observation: ConfigResolutionObservation,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct OutputFile {
    pub file_name: String,
    pub text: String,
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct EmitOutput {
    pub files: Vec<OutputFile>,
    pub diagnostics: Vec<ProgramDiagnostic>,
}

fn prepend_emit_bom(files: &mut [OutputFile]) {
    for file in files {
        let lower = file.file_name.to_ascii_lowercase();
        if [".js", ".jsx", ".mjs", ".cjs", ".d.ts", ".d.mts", ".d.cts"]
            .iter()
            .any(|extension| lower.ends_with(extension))
            && !file.text.starts_with('\u{feff}')
        {
            file.text.insert(0, '\u{feff}');
        }
    }
}

fn is_valid_jsx_factory_expression(value: &str, allow_null: bool) -> bool {
    (allow_null && value == "null")
        || value.split('.').all(|part| {
            !part.is_empty()
                && part.chars().next().is_some_and(|character| {
                    character == '_' || character == '$' || character.is_alphabetic()
                })
                && part.chars().skip(1).all(|character| {
                    character == '_' || character == '$' || character.is_alphanumeric()
                })
        })
}

fn source_jsx_pragma_value<'a>(source: &'a str, pragma: &str) -> Option<&'a str> {
    source
        .match_indices(pragma)
        .filter_map(|(start, _)| {
            source[start + pragma.len()..]
                .trim_start_matches([' ', '\t', ':'])
                .split(|character: char| character.is_whitespace() || character == '*')
                .next()
                .filter(|value| !value.is_empty())
        })
        .last()
}

fn source_check_js_directive(source: &str) -> Option<bool> {
    let mut remaining = source.strip_prefix('\u{feff}').unwrap_or(source);
    if remaining.starts_with("#!") {
        remaining = remaining
            .split_once(['\r', '\n', '\u{2028}', '\u{2029}'])
            .map_or("", |(_, source)| source);
    }

    let mut directive = None;
    loop {
        remaining = remaining.trim_start_matches([' ', '\t', '\r', '\n', '\u{2028}', '\u{2029}']);
        if let Some(comment) = remaining.strip_prefix("//") {
            let (line, rest) = comment
                .split_once(['\r', '\n', '\u{2028}', '\u{2029}'])
                .unwrap_or((comment, ""));
            remaining = rest;
            let pragma = line
                .strip_prefix('/')
                .unwrap_or(line)
                .trim_start_matches([' ', '\t']);
            if let Some(pragma) = pragma.strip_prefix('@') {
                let end = pragma
                    .find(|character: char| !character.is_ascii_alphabetic() && character != '-')
                    .unwrap_or(pragma.len());
                let name = &pragma[..end];
                if name.eq_ignore_ascii_case("ts-check") {
                    directive = Some(true);
                } else if name.eq_ignore_ascii_case("ts-nocheck") {
                    directive = Some(false);
                }
            }
            continue;
        }
        if let Some(comment) = remaining.strip_prefix("/*") {
            let Some((_, rest)) = comment.split_once("*/") else {
                break;
            };
            remaining = rest;
            continue;
        }
        break;
    }

    directive
}

#[derive(Clone, Copy, Debug)]
struct SourceCommentDirective {
    range: TextRange,
    expect_error: bool,
    used: bool,
}

fn source_line_starts(source: &str) -> Vec<usize> {
    let mut line_starts = vec![0];
    let bytes = source.as_bytes();
    for (position, character) in source.char_indices() {
        match character {
            '\r' => line_starts.push(
                position
                    + if bytes.get(position + 1) == Some(&b'\n') {
                        2
                    } else {
                        1
                    },
            ),
            '\n' if position == 0 || bytes[position - 1] != b'\r' => {
                line_starts.push(position + 1);
            }
            '\u{2028}' | '\u{2029}' => line_starts.push(position + character.len_utf8()),
            _ => {}
        }
    }
    line_starts
}

fn source_line_of_position(line_starts: &[usize], position: usize) -> usize {
    line_starts
        .partition_point(|start| *start <= position)
        .saturating_sub(1)
}

fn source_comment_directives(
    parse: &ParseResult,
    line_starts: &[usize],
) -> BTreeMap<usize, SourceCommentDirective> {
    parse
        .comment_directives
        .iter()
        .filter_map(|directive| {
            let position = usize::try_from(directive.range.start.get()).ok()?;
            Some((
                source_line_of_position(line_starts, position),
                SourceCommentDirective {
                    range: directive.range,
                    expect_error: directive.expect_error,
                    used: false,
                },
            ))
        })
        .collect()
}

fn source_line_is_comment_or_blank(line: &str) -> bool {
    let line = line.trim_start_matches([' ', '\t']);
    line.is_empty()
        || line.starts_with("//")
        || line
            .chars()
            .next()
            .is_some_and(|character| matches!(character, '\r' | '\n' | '\u{2028}' | '\u{2029}'))
}

fn source_printer_settings(mut settings: PrinterSettings, source: &str) -> PrinterSettings {
    if settings.jsx == ts_options::JsxEmit::React
        && source_jsx_pragma_value(source, "@jsxImportSource").is_some()
    {
        settings.jsx = ts_options::JsxEmit::ReactJsx;
    }
    match source_jsx_pragma_value(source, "@jsxRuntime") {
        Some("classic")
            if matches!(
                settings.jsx,
                ts_options::JsxEmit::ReactJsx | ts_options::JsxEmit::ReactJsxDev
            ) =>
        {
            settings.jsx = ts_options::JsxEmit::React;
        }
        Some("automatic") => {
            if !matches!(
                settings.jsx,
                ts_options::JsxEmit::Preserve
                    | ts_options::JsxEmit::ReactNative
                    | ts_options::JsxEmit::None
                    | ts_options::JsxEmit::ReactJsxDev
            ) {
                settings.jsx = ts_options::JsxEmit::ReactJsx;
            }
        }
        _ => {}
    }
    settings
}

fn source_shebang(source: &SourceFile) -> Option<&str> {
    let text = source
        .source_text
        .strip_prefix('\u{feff}')
        .unwrap_or(&source.source_text);
    text.lines()
        .next()
        .filter(|line| line.starts_with("#!"))
        .map(|line| line.trim_end_matches('\r'))
}

fn source_is_json(source: &SourceFile) -> bool {
    Path::new(&source.file_name)
        .extension()
        .and_then(|extension| extension.to_str())
        .is_some_and(|extension| extension.eq_ignore_ascii_case("json"))
}

fn source_prologue_directives(source: &SourceFile) -> Vec<&str> {
    let Some(NodeData::SourceFile(file)) = source
        .parse
        .arena
        .get(source.parse.source_file)
        .map(|node| &node.data)
    else {
        return Vec::new();
    };
    file.statements
        .nodes
        .iter()
        .map_while(|statement| {
            let NodeData::ExpressionStatement(statement) =
                &source.parse.arena.get(*statement)?.data
            else {
                return None;
            };
            let NodeData::StringLiteral(literal) =
                &source.parse.arena.get(statement.expression)?.data
            else {
                return None;
            };
            Some(literal.text.as_str())
        })
        .collect()
}

fn push_bundle_prologue(code: &mut String, directive: &str) {
    code.push('"');
    for character in directive.chars() {
        match character {
            '"' => code.push_str("\\\""),
            '\\' => code.push_str("\\\\"),
            '\n' => code.push_str("\\n"),
            '\r' => code.push_str("\\r"),
            '\t' => code.push_str("\\t"),
            character => code.push(character),
        }
    }
    code.push_str("\";\n");
}

fn bundle_detached_comment(source: &SourceFile) -> Option<(String, u32)> {
    let Some(NodeData::SourceFile(file)) = source
        .parse
        .arena
        .get(source.parse.source_file)
        .map(|node| &node.data)
    else {
        return None;
    };
    let first_statement = file.statements.nodes.first()?;
    let end = usize::try_from(source.parse.arena.get(*first_statement)?.range.start.get()).ok()?;
    let prefix = source.source_text.get(..end)?;
    let separators = ["\r\n\r\n", "\n\n", "\r\r"];
    let (separator_start, separator_len) = separators
        .iter()
        .filter_map(|separator| prefix.find(separator).map(|start| (start, separator.len())))
        .min_by_key(|(start, _)| *start)?;
    let comment = prefix[..separator_start].trim();
    if !comment.starts_with("//") && !comment.starts_with("/*") {
        return None;
    }
    let excluded_end = u32::try_from(separator_start + separator_len).ok()?;
    Some((format!("{comment}\n"), excluded_end))
}

// Matches the dependency phases in pinned parseTask.load and import resolution.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum SourceDependencyOrder {
    PathReference(TextPos),
    TypeReference(TextPos),
    ImportHelper,
    JsxRuntime,
    StaticImport(TextPos),
    DynamicImport(TextPos),
}

#[derive(Clone, Copy, Debug)]
enum SourceLoadKind {
    Module(Option<SourceDependencyOrder>),
    PathReference(TextPos),
    TypeReference(TextPos),
}

#[derive(Clone, Debug)]
struct SourceLoadDependency {
    file_name: String,
    external_library: bool,
    kind: SourceLoadKind,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct ResolvedModuleKey {
    containing_file: String,
    specifier: String,
    mode: Option<ModuleFormat>,
}

impl ResolvedModuleKey {
    fn new(
        containing_file: String,
        specifier: String,
        mode: CanonicalModuleResolutionMode,
    ) -> Self {
        Self {
            containing_file,
            specifier,
            mode: match mode {
                CanonicalModuleResolutionMode::CommonJs => Some(ModuleFormat::CommonJs),
                CanonicalModuleResolutionMode::Esm => Some(ModuleFormat::Esm),
                CanonicalModuleResolutionMode::None => None,
            },
        }
    }
}

/// A compilation's parsed source-file graph.
#[derive(Debug, Default)]
pub struct Program {
    source_files: Vec<SourceFile>,
    file_index: BTreeMap<String, usize>,
    root_file_names: BTreeSet<String>,
    ordered_root_file_names: Vec<String>,
    source_dependencies: BTreeMap<FileId, Vec<(SourceDependencyOrder, FileId)>>,
    source_node_module_depths: BTreeMap<FileId, u32>,
    source_load_dependencies: BTreeMap<FileId, Vec<SourceLoadDependency>>,
    resolved_modules: BTreeMap<ResolvedModuleKey, String>,
    resolved_module_loads: BTreeMap<ResolvedModuleKey, (FileId, SourceLoadDependency)>,
    graph_resolution_options: Option<ResolutionOptions>,
    graph_resolutions: Vec<ProgramGraphResolution>,
    graph_references: Vec<ProgramGraphReference>,
    graph_config: Option<ProgramGraphConfig>,
    graph_config_resolution_observation: Option<ConfigResolutionObservation>,
    graph_package_scope_recorder: project_graph::PackageScopeObservationRecorder,
    module_resolution_diagnostics: Vec<ProgramDiagnostic>,
    package_export_specifiers: BTreeMap<String, Vec<String>>,
    package_display_specifiers: BTreeMap<(FileId, String), String>,
    diagnostics: Vec<ProgramDiagnostic>,
    current_directory: String,
    config_file_path: Option<String>,
    case_sensitivity: CaseSensitivity,
    options: CompilerOptions,
    checker: ProgramChecker,
}

/// Scoped access to the original canonical checker graph of one Program.
///
/// The checker borrows the Program's AST arenas, so this value can be used
/// only inside Program's canonical query callbacks. Query results must be
/// converted to owned data before the callback returns.
#[derive(Debug)]
pub struct CanonicalProgramQueries<'arena> {
    context: CanonicalCheckerContext<'arena>,
    program: &'arena Program,
    checked_sources: Vec<CanonicalCheckedSource<'arena>>,
    bind_diagnostics: Vec<ProgramDiagnostic>,
    cold_diagnostics: Vec<ProgramDiagnostic>,
    has_diagnostics: bool,
}

impl CanonicalProgramQueries<'_> {
    /// Reports whether diagnostics remain after the last completed check.
    #[must_use]
    pub fn has_diagnostics(&self) -> bool {
        self.has_diagnostics
    }

    /// Returns all cold Program diagnostics in their final output order.
    ///
    /// This includes loader, config, bind, and checker diagnostics with their
    /// related records. Comment directives use the normal Program rules.
    /// The owned snapshot does not change after queries or source replay.
    #[must_use]
    pub fn cold_diagnostic_snapshot(&self) -> Vec<ProgramDiagnostic> {
        self.cold_diagnostics.clone()
    }

    /// Forces the original checked sources through the same checker again.
    ///
    /// Each source bypasses its completion flag and uses its original JSX
    /// runtime facts. Files retain their original order and canonical graph.
    /// The result owns the complete, sorted Program diagnostics after replay.
    ///
    /// # Errors
    ///
    /// Returns the original source-checking or diagnostic conversion failure.
    /// A failed replay does not return a partial diagnostic snapshot.
    pub fn replay_sources(&mut self) -> Result<Vec<ProgramDiagnostic>, CanonicalProgramCheckError> {
        for checked in &self.checked_sources {
            self.context
                .recheck_source_file_with_jsx_runtime(checked.source.id, checked.runtime.evidence())
                .map_err(|error| CanonicalProgramCheckError::SourceCheck {
                    file_name: checked.source.file_name.clone(),
                    error,
                })?;
        }
        let diagnostics = self.program.canonical_checker_diagnostics(
            &mut self.context,
            &self.bind_diagnostics,
            &self.checked_sources,
        )?;
        let snapshot = self.program.canonical_diagnostic_snapshot(&diagnostics);
        self.has_diagnostics = !snapshot.is_empty();
        Ok(snapshot)
    }

    /// Returns the canonical type recorded for an exact Program node.
    ///
    /// # Errors
    ///
    /// Returns the original checker's provenance or unsupported-query error.
    pub fn get_type_at_location(
        &mut self,
        node: NodeRef,
    ) -> Result<CanonicalTypeId, CanonicalArtifactQueryError> {
        self.context.get_type_at_location(node)
    }

    /// Returns the canonical declaration or reference symbol for a Program node.
    ///
    /// # Errors
    ///
    /// Returns the original checker's provenance or unsupported-query error.
    pub fn get_symbol_at_location(
        &mut self,
        node: NodeRef,
    ) -> Result<Option<CanonicalSymbolId>, CanonicalArtifactQueryError> {
        self.context.get_symbol_at_location(node)
    }

    /// Returns declarations owned by the same canonical symbol graph.
    ///
    /// # Errors
    ///
    /// Returns an error when the symbol or any declaration is foreign.
    pub fn get_symbol_declarations(
        &self,
        symbol: CanonicalSymbolId,
    ) -> Result<&[NodeRef], CanonicalArtifactQueryError> {
        self.context.get_symbol_declarations(symbol)
    }

    /// Formats a type from this Program's canonical checker graph.
    ///
    /// # Errors
    ///
    /// Returns an error when the type is foreign or cannot yet be displayed.
    pub fn type_to_string(
        &self,
        type_id: CanonicalTypeId,
    ) -> Result<String, TypeDisplayUnavailable> {
        self.context.type_to_string(type_id)
    }

    /// Returns the validated intrinsic name of an `any` type.
    ///
    /// # Errors
    ///
    /// Returns an error for a foreign type or an invalid intrinsic payload.
    pub fn intrinsic_any_name(
        &self,
        type_id: CanonicalTypeId,
    ) -> Result<Option<&str>, TypeDisplayUnavailable> {
        self.context.intrinsic_any_name(type_id)
    }

    /// Formats a canonical type with explicit TypeScript display flags.
    ///
    /// # Errors
    ///
    /// Returns an error when the type is foreign or cannot yet be displayed.
    pub fn type_to_string_with_flags(
        &self,
        type_id: CanonicalTypeId,
        flags: CanonicalTypeFormatFlags,
    ) -> Result<String, TypeDisplayUnavailable> {
        self.context.type_to_string_with_flags(type_id, flags)
    }

    /// Formats a canonical type using names visible at an exact Program node.
    ///
    /// # Errors
    ///
    /// Returns an error for foreign nodes, invalid caches, or unavailable display.
    pub fn type_to_string_at_location_with_flags(
        &mut self,
        type_id: CanonicalTypeId,
        enclosing: NodeRef,
        flags: CanonicalTypeFormatFlags,
    ) -> Result<String, TypeDisplayUnavailable> {
        self.context
            .type_to_string_at_location_with_flags(type_id, enclosing, flags)
    }

    /// Formats a canonical symbol name using the checker's escaped-name rules.
    ///
    /// # Errors
    ///
    /// Returns an error when the symbol belongs to another checker graph.
    pub fn symbol_to_string(
        &self,
        symbol: CanonicalSymbolId,
    ) -> Result<String, CanonicalArtifactQueryError> {
        self.context.symbol_to_string(symbol)
    }

    /// Formats a canonical symbol using names visible at an exact Program node.
    ///
    /// # Errors
    ///
    /// Returns an error for foreign nodes, invalid caches, or unavailable names.
    pub fn symbol_to_string_at_location(
        &mut self,
        symbol: CanonicalSymbolId,
        enclosing: NodeRef,
    ) -> Result<String, CanonicalArtifactQueryError> {
        self.context.symbol_to_string_at_location(symbol, enclosing)
    }

    /// Returns the identity shared by this Program's canonical types and symbols.
    #[must_use]
    pub fn semantic_store_id(&self) -> CanonicalSemanticStoreId {
        self.context.id()
    }

    /// Returns the exact module resolution attached to a source specifier.
    #[must_use]
    pub fn module_resolution(&self, specifier: NodeRef) -> CanonicalModuleResolutionLookup {
        self.context.module_resolution(specifier)
    }
}

#[derive(Debug)]
struct CanonicalCheckedSource<'arena> {
    source: &'arena SourceFile,
    runtime: CanonicalReplayJsxRuntime,
}

#[derive(Debug)]
enum CanonicalReplayJsxRuntime {
    Preserve,
    Classic {
        factory_namespace: String,
        fragment_factory_namespace: String,
        fragment_factory_required: bool,
        fragment_factory_pragma_required: bool,
    },
    Automatic {
        module_specifier: String,
        resolved_module: Option<CanonicalSymbolId>,
    },
}

impl CanonicalReplayJsxRuntime {
    fn evidence(&self) -> CanonicalJsxRuntimeEvidence<'_> {
        match self {
            Self::Preserve => CanonicalJsxRuntimeEvidence::Preserve,
            Self::Classic {
                factory_namespace,
                fragment_factory_namespace,
                fragment_factory_required,
                fragment_factory_pragma_required,
            } => CanonicalJsxRuntimeEvidence::Classic {
                factory_namespace,
                fragment_factory_namespace,
                fragment_factory_required: *fragment_factory_required,
                fragment_factory_pragma_required: *fragment_factory_pragma_required,
            },
            Self::Automatic {
                module_specifier,
                resolved_module,
            } => CanonicalJsxRuntimeEvidence::Automatic {
                module_specifier,
                resolved_module: *resolved_module,
            },
        }
    }
}

impl From<CanonicalJsxRuntimeEvidence<'_>> for CanonicalReplayJsxRuntime {
    fn from(runtime: CanonicalJsxRuntimeEvidence<'_>) -> Self {
        match runtime {
            CanonicalJsxRuntimeEvidence::Preserve => Self::Preserve,
            CanonicalJsxRuntimeEvidence::Classic {
                factory_namespace,
                fragment_factory_namespace,
                fragment_factory_required,
                fragment_factory_pragma_required,
            } => Self::Classic {
                factory_namespace: factory_namespace.to_owned(),
                fragment_factory_namespace: fragment_factory_namespace.to_owned(),
                fragment_factory_required,
                fragment_factory_pragma_required,
            },
            CanonicalJsxRuntimeEvidence::Automatic {
                module_specifier,
                resolved_module,
            } => Self::Automatic {
                module_specifier: module_specifier.to_owned(),
                resolved_module,
            },
        }
    }
}

impl Program {
    /// Creates a Program from explicit root file names.
    #[must_use]
    pub fn new(
        file_system: &dyn FileSystem,
        current_directory: &str,
        root_names: &[String],
    ) -> Self {
        let mut program = Self::new_unchecked(file_system, current_directory, root_names);
        program.check_program_legacy();
        program
    }

    fn new_unchecked(
        file_system: &dyn FileSystem,
        current_directory: &str,
        root_names: &[String],
    ) -> Self {
        Self::new_unchecked_with_options(
            file_system,
            current_directory,
            root_names,
            CompilerOptions::default(),
        )
    }

    fn new_unchecked_with_options(
        file_system: &dyn FileSystem,
        current_directory: &str,
        root_names: &[String],
        options: CompilerOptions,
    ) -> Self {
        Self::new_unchecked_with_options_and_checker(
            file_system,
            current_directory,
            root_names,
            options,
            ProgramChecker::Legacy,
        )
    }

    fn new_unchecked_with_options_and_checker(
        file_system: &dyn FileSystem,
        current_directory: &str,
        root_names: &[String],
        options: CompilerOptions,
        checker: ProgramChecker,
    ) -> Self {
        let case_sensitivity = if file_system.use_case_sensitive_file_names() {
            CaseSensitivity::Sensitive
        } else {
            CaseSensitivity::Insensitive
        };
        let current_directory = ts_path::normalize_path(current_directory);
        let mut program = Self {
            current_directory: current_directory.clone(),
            ordered_root_file_names: root_names.to_vec(),
            case_sensitivity,
            options,
            checker,
            ..Self::default()
        };
        if checker == ProgramChecker::Canonical
            && program.options.check_js
            && !program.options.allow_js
            && program.options.allow_js_specified
        {
            program
                .diagnostics
                .push(check_js_requires_allow_js_diagnostic());
        }
        for root_name in root_names {
            let file_name = if is_absolute(root_name) {
                ts_path::normalize_path(root_name)
            } else {
                resolve_path(&current_directory, &[root_name])
            };
            program.root_file_names.insert(canonicalize(
                &file_name,
                &program.current_directory,
                program.case_sensitivity,
            ));
            if checker == ProgramChecker::Canonical
                && !(program.options.allow_js
                    || (program.options.check_js && !program.options.allow_js_specified))
                && is_javascript_file_name(&file_name)
            {
                let display_name = relative_path(&program.current_directory, &file_name);
                program
                    .diagnostics
                    .push(javascript_file_not_allowed_diagnostic(&display_name));
                continue;
            }
            program.load_file(file_system, &file_name, true);
        }
        program
    }

    /// Creates a Program and follows import/export module specifiers using the
    /// foundational Node resolver.
    #[must_use]
    pub fn new_with_module_resolution(
        file_system: &dyn FileSystem,
        current_directory: &str,
        root_names: &[String],
        resolution_options: ResolutionOptions,
    ) -> Self {
        let mut program = Self::new_unchecked(file_system, current_directory, root_names);
        program.load_module_graph(file_system, resolution_options);
        program.check_program_legacy();
        program
    }

    #[allow(clippy::too_many_lines)] // Preserve upstream reference and import discovery order.
    fn load_module_graph(
        &mut self,
        file_system: &dyn FileSystem,
        resolution_options: ResolutionOptions,
    ) {
        self.graph_resolution_options = Some(resolution_options.clone());
        let resolver = Resolver::new(file_system, resolution_options);
        let mut ambient_modules = BTreeMap::new();
        let mut pending_module_diagnostics = Vec::new();
        for source_file in &self.source_files {
            self.source_node_module_depths
                .entry(source_file.id)
                .or_insert(0);
            register_ambient_external_modules(
                source_file,
                &self.options,
                &self.current_directory,
                self.case_sensitivity,
                &mut ambient_modules,
            );
        }
        let mut file_index = 0;
        while file_index < self.source_files.len() {
            if self.source_files[file_index].is_default_library {
                file_index += 1;
                continue;
            }
            let source_count_before_references = self.source_files.len();
            self.load_reference_directives_for_file(file_system, &resolver, file_index);
            for source_file in &self.source_files[source_count_before_references..] {
                register_ambient_external_modules(
                    source_file,
                    &self.options,
                    &self.current_directory,
                    self.case_sensitivity,
                    &mut ambient_modules,
                );
            }
            register_ambient_external_modules(
                &self.source_files[file_index],
                &self.options,
                &self.current_directory,
                self.case_sensitivity,
                &mut ambient_modules,
            );
            let containing_file = self.source_files[file_index].file_name.clone();
            let containing_id = self.source_files[file_index].id;
            let implicit_jsx_runtime = {
                let source = &self.source_files[file_index];
                source_contains_jsx(&source.parse).then(|| {
                    self.options.jsx_runtime_module_specifier_for_source(
                        source_jsx_pragma_value(&source.source_text, "@jsxRuntime"),
                        source_jsx_pragma_value(&source.source_text, "@jsxImportSource"),
                    )
                })
            }
            .flatten();
            if let Some(specifier) = implicit_jsx_runtime {
                let result =
                    resolver.resolve_with_mode(&specifier, &containing_file, ModuleFormat::Esm);
                self.record_graph_resolution(
                    ProgramGraphResolutionRequest {
                        kind: ProgramGraphResolutionKind::JsxRuntime,
                        containing_file: containing_file.clone(),
                        range: None,
                        specifier: specifier.clone(),
                        mode: Some(ModuleFormat::Esm),
                    },
                    &result,
                    None,
                );
                if let Some(resolved) = result.resolved {
                    if let Some(package_json) = resolved.package_json.as_deref() {
                        self.register_package_export_specifiers(
                            file_system,
                            &resolver,
                            package_json,
                            &containing_file,
                            CanonicalModuleResolutionMode::Esm,
                        );
                    }
                    let containing = canonicalize(
                        &containing_file,
                        &self.current_directory,
                        self.case_sensitivity,
                    );
                    self.load_resolved_module_target(
                        file_system,
                        containing_id,
                        ResolvedModuleKey::new(
                            containing,
                            specifier,
                            CanonicalModuleResolutionMode::Esm,
                        ),
                        &resolved,
                        Some(SourceDependencyOrder::JsxRuntime),
                    );
                }
            }
            let source_mode = self.canonical_emit_module_mode(&self.source_files[file_index]);
            if self.source_needs_import_helpers(&self.source_files[file_index]) {
                let format = match source_mode {
                    CanonicalModuleResolutionMode::CommonJs => Some(ModuleFormat::CommonJs),
                    CanonicalModuleResolutionMode::Esm => Some(ModuleFormat::Esm),
                    CanonicalModuleResolutionMode::None => None,
                };
                let result = match format {
                    Some(format) => resolver.resolve_with_mode("tslib", &containing_file, format),
                    None => resolver.resolve("tslib", &containing_file),
                };
                self.record_graph_resolution(
                    ProgramGraphResolutionRequest {
                        kind: ProgramGraphResolutionKind::ImportHelpers,
                        containing_file: containing_file.clone(),
                        range: None,
                        specifier: "tslib".to_owned(),
                        mode: format,
                    },
                    &result,
                    None,
                );
                if let Some(resolved) = result.resolved {
                    if let Some(package_json) = resolved.package_json.as_deref() {
                        self.register_package_export_specifiers(
                            file_system,
                            &resolver,
                            package_json,
                            &containing_file,
                            source_mode,
                        );
                    }
                    let containing = canonicalize(
                        &containing_file,
                        &self.current_directory,
                        self.case_sensitivity,
                    );
                    self.load_resolved_module_target(
                        file_system,
                        containing_id,
                        ResolvedModuleKey::new(containing, "tslib".to_owned(), source_mode),
                        &resolved,
                        Some(SourceDependencyOrder::ImportHelper),
                    );
                }
            }
            let usage_modes =
                canonical_static_module_specifiers(&self.source_files[file_index], &self.options)
                    .unwrap_or_default()
                    .into_iter()
                    .filter_map(|(specifier, _, requested_mode)| {
                        self.source_files[file_index]
                            .parse
                            .arena
                            .get(specifier.node)
                            .map(|node| (node.range, requested_mode.unwrap_or(source_mode)))
                    })
                    .collect::<Vec<_>>();
            let specifiers = module_specifiers(&self.source_files[file_index], &self.options);
            for ModuleSpecifier {
                text: specifier,
                range,
                can_resolve_ambient,
                side_effect_only,
                is_augmentation,
                dependency_order,
            } in specifiers
            {
                let mode = usage_modes
                    .iter()
                    .find_map(|(candidate, mode)| (*candidate == range).then_some(*mode))
                    .unwrap_or(source_mode);
                let result = match mode {
                    CanonicalModuleResolutionMode::CommonJs => resolver.resolve_with_mode(
                        &specifier,
                        &containing_file,
                        ModuleFormat::CommonJs,
                    ),
                    CanonicalModuleResolutionMode::Esm => {
                        resolver.resolve_with_mode(&specifier, &containing_file, ModuleFormat::Esm)
                    }
                    CanonicalModuleResolutionMode::None => {
                        resolver.resolve(&specifier, &containing_file)
                    }
                };
                let ambient_target = if result.resolved.is_none()
                    && can_resolve_ambient
                    && !module_name_is_relative(&specifier)
                {
                    ambient_modules.get(&specifier).cloned()
                } else {
                    None
                };
                self.record_graph_resolution(
                    ProgramGraphResolutionRequest {
                        kind: ProgramGraphResolutionKind::Module,
                        containing_file: containing_file.clone(),
                        range: Some(range),
                        specifier: specifier.clone(),
                        mode: match mode {
                            CanonicalModuleResolutionMode::CommonJs => Some(ModuleFormat::CommonJs),
                            CanonicalModuleResolutionMode::Esm => Some(ModuleFormat::Esm),
                            CanonicalModuleResolutionMode::None => None,
                        },
                    },
                    &result,
                    ambient_target.as_deref(),
                );
                if let Some(resolved) = result.resolved {
                    if self.checker == ProgramChecker::Canonical
                        && !self.options.no_check
                        && resolved.resolved_using_ts_extension
                        && !self
                            .options
                            .allows_importing_typescript_extensions_from(&containing_file)
                        && !ts_path::is_declaration_file(&specifier)
                        && module_specifier_is_emittable(
                            &self.source_files[file_index].parse,
                            range,
                        )
                        && let Some(extension) = imported_typescript_extension(&specifier)
                    {
                        self.module_resolution_diagnostics.push(
                            typescript_extension_import_diagnostic(
                                &containing_file,
                                range,
                                extension,
                            ),
                        );
                    }
                    if let Some(package_json) = resolved.package_json.as_deref() {
                        self.register_package_export_specifiers(
                            file_system,
                            &resolver,
                            package_json,
                            &containing_file,
                            mode,
                        );
                    }
                    let containing = canonicalize(
                        &containing_file,
                        &self.current_directory,
                        self.case_sensitivity,
                    );
                    let source_count_before_import = self.source_files.len();
                    self.load_resolved_module_target(
                        file_system,
                        containing_id,
                        ResolvedModuleKey::new(containing, specifier.clone(), mode),
                        &resolved,
                        dependency_order,
                    );
                    for source_file in &self.source_files[source_count_before_import..] {
                        register_ambient_external_modules(
                            source_file,
                            &self.options,
                            &self.current_directory,
                            self.case_sensitivity,
                            &mut ambient_modules,
                        );
                    }
                } else if let Some(target) = ambient_target {
                    let containing = canonicalize(
                        &containing_file,
                        &self.current_directory,
                        self.case_sensitivity,
                    );
                    self.resolved_modules.insert(
                        ResolvedModuleKey::new(containing, specifier.clone(), mode),
                        target,
                    );
                } else if !(self.options.no_check
                    || is_augmentation
                    || side_effect_only && !self.options.no_unchecked_side_effect_imports
                    || self.options.skip_lib_check
                        && ts_path::is_declaration_file(&containing_file))
                {
                    pending_module_diagnostics.push((
                        containing_file.clone(),
                        range,
                        specifier,
                        can_resolve_ambient,
                        side_effect_only,
                    ));
                }
            }
            file_index += 1;
        }
        for dependencies in self.source_dependencies.values_mut() {
            dependencies.sort_by_key(|(order, _)| *order);
        }
        for (containing_file, range, specifier, can_resolve_ambient, side_effect_only) in
            pending_module_diagnostics
        {
            if can_resolve_ambient && ambient_modules.contains_key(&specifier) {
                continue;
            }
            self.diagnostics.push(if side_effect_only {
                side_effect_import_not_found_diagnostic(&containing_file, range, &specifier)
            } else {
                module_not_found_diagnostic(&containing_file, range, &specifier)
            });
        }
        self.resolve_package_display_specifiers(&resolver);
    }

    fn allows_javascript_sources(&self) -> bool {
        self.options.allow_js || self.options.check_js && !self.options.allow_js_specified
    }

    fn source_load_omission(
        &self,
        source: FileId,
        dependency: &SourceLoadDependency,
    ) -> Option<CanonicalModuleTargetOmission> {
        if !matches!(dependency.kind, SourceLoadKind::Module(_)) {
            return None;
        }
        if self.options.no_resolve {
            return Some(CanonicalModuleTargetOmission::NoResolve);
        }
        if is_javascript_file_name(&dependency.file_name) {
            if !self.allows_javascript_sources() {
                return Some(CanonicalModuleTargetOmission::JavaScriptDisabled);
            }
            let depth = self
                .source_node_module_depths
                .get(&source)
                .copied()
                .unwrap_or(0)
                .saturating_add(u32::from(dependency.external_library));
            let limit = self.options.max_node_module_js_depth.unwrap_or(0);
            if dependency.external_library
                && dependency.file_name.contains("/node_modules/")
                && i64::from(depth) > limit
            {
                return Some(CanonicalModuleTargetOmission::NodeModuleJavaScriptDepth {
                    depth,
                    limit,
                });
            }
        }
        None
    }

    fn load_source_at_node_depth(
        &mut self,
        file_system: &dyn FileSystem,
        file_name: &str,
        depth: u32,
        report_missing: bool,
    ) -> Option<(FileId, bool)> {
        let previous = self.source_file(file_name).map(|source| source.id);
        self.load_file(file_system, file_name, report_missing);
        let target = self.source_file(file_name)?.id;
        let old_depth = self
            .source_node_module_depths
            .get(&target)
            .copied()
            .or_else(|| previous.map(|_| 0));
        let lowered = old_depth.is_none_or(|old| depth < old);
        if lowered {
            self.source_node_module_depths.insert(target, depth);
        }
        Some((target, lowered))
    }

    fn load_source_dependency(
        &mut self,
        file_system: &dyn FileSystem,
        source: FileId,
        dependency: SourceLoadDependency,
    ) {
        self.source_load_dependencies
            .entry(source)
            .or_default()
            .push(dependency.clone());
        let mut pending = VecDeque::from([(source, dependency)]);
        while let Some((source, dependency)) = pending.pop_front() {
            if self.source_load_omission(source, &dependency).is_some() {
                continue;
            }
            let depth = self
                .source_node_module_depths
                .get(&source)
                .copied()
                .unwrap_or(0)
                .saturating_add(u32::from(dependency.external_library));
            let (order, report_missing) = match dependency.kind {
                SourceLoadKind::Module(order) => (order, false),
                SourceLoadKind::PathReference(position) => {
                    (Some(SourceDependencyOrder::PathReference(position)), true)
                }
                SourceLoadKind::TypeReference(position) => {
                    (Some(SourceDependencyOrder::TypeReference(position)), false)
                }
            };
            let Some((target, lowered)) = self.load_source_at_node_depth(
                file_system,
                &dependency.file_name,
                depth,
                report_missing,
            ) else {
                continue;
            };
            if let Some(order) = order {
                self.record_source_dependency(source, &dependency.file_name, order);
            }
            // A shallower route can admit previously excluded descendants.
            // Reuse their resolved edges instead of repeating filesystem resolution.
            if lowered && let Some(dependencies) = self.source_load_dependencies.get(&target) {
                pending.extend(
                    dependencies
                        .iter()
                        .cloned()
                        .map(|dependency| (target, dependency)),
                );
            }
        }
    }

    fn load_resolved_module_target(
        &mut self,
        file_system: &dyn FileSystem,
        source: FileId,
        key: ResolvedModuleKey,
        resolved: &ts_module::ResolvedModule,
        order: Option<SourceDependencyOrder>,
    ) {
        let target = canonicalize(
            &resolved.resolved_file_name,
            &self.current_directory,
            self.case_sensitivity,
        );
        let dependency = SourceLoadDependency {
            file_name: resolved.resolved_file_name.clone(),
            external_library: resolved.is_external_library_import,
            kind: SourceLoadKind::Module(order),
        };
        self.resolved_modules.insert(key.clone(), target);
        self.resolved_module_loads
            .insert(key, (source, dependency.clone()));
        self.load_source_dependency(file_system, source, dependency);
    }

    fn record_source_dependency(
        &mut self,
        containing: FileId,
        target: &str,
        order: SourceDependencyOrder,
    ) {
        if self.options.no_resolve {
            return;
        }
        let Some(target) = self.source_file(target).map(|source| source.id) else {
            return;
        };
        self.source_dependencies
            .entry(containing)
            .or_default()
            .push((order, target));
    }

    fn register_package_export_specifiers(
        &mut self,
        file_system: &dyn FileSystem,
        resolver: &Resolver<'_, dyn FileSystem + '_>,
        package_json_path: &str,
        containing_file: &str,
        mode: CanonicalModuleResolutionMode,
    ) {
        let Some(package) = file_system
            .read_file(package_json_path)
            .ok()
            .and_then(|contents| parse_package_json(&contents).ok())
        else {
            return;
        };
        let directory = directory_path(package_json_path);
        let Some(name) = package_display_name(&directory, package.name.as_deref()) else {
            return;
        };
        let Some(exports) = package.exports else {
            return;
        };
        let Some(exports) = exports.as_object() else {
            return;
        };
        for key in exports.keys() {
            let specifier = if key == "." {
                name.clone()
            } else if let Some(subpath) = key.strip_prefix("./") {
                format!("{name}/{subpath}")
            } else {
                continue;
            };
            let lookup = match mode {
                CanonicalModuleResolutionMode::CommonJs => {
                    resolver.resolve_with_mode(&specifier, containing_file, ModuleFormat::CommonJs)
                }
                CanonicalModuleResolutionMode::Esm => {
                    resolver.resolve_with_mode(&specifier, containing_file, ModuleFormat::Esm)
                }
                CanonicalModuleResolutionMode::None => {
                    resolver.resolve(&specifier, containing_file)
                }
            };
            let Some(module) = lookup.resolved else {
                continue;
            };
            let target = canonicalize(
                &module.resolved_file_name,
                &self.current_directory,
                self.case_sensitivity,
            );
            let candidates = self.package_export_specifiers.entry(target).or_default();
            if !candidates.contains(&specifier) {
                candidates.push(specifier);
            }
        }
    }

    fn resolve_package_display_specifiers(&mut self, resolver: &Resolver<'_, dyn FileSystem + '_>) {
        self.package_display_specifiers.clear();
        for source in &self.source_files {
            if source.is_default_library {
                continue;
            }
            let mode = self.canonical_emit_module_mode(source);
            for (target, candidates) in &self.package_export_specifiers {
                if !self.file_index.contains_key(target) {
                    continue;
                }
                for candidate in candidates {
                    let resolution = match mode {
                        CanonicalModuleResolutionMode::CommonJs => resolver.resolve_with_mode(
                            candidate,
                            &source.file_name,
                            ModuleFormat::CommonJs,
                        ),
                        CanonicalModuleResolutionMode::Esm => resolver.resolve_with_mode(
                            candidate,
                            &source.file_name,
                            ModuleFormat::Esm,
                        ),
                        CanonicalModuleResolutionMode::None => {
                            resolver.resolve(candidate, &source.file_name)
                        }
                    };
                    if resolution.resolved.is_some_and(|resolved| {
                        canonicalize(
                            &resolved.resolved_file_name,
                            &self.current_directory,
                            self.case_sensitivity,
                        ) == *target
                    }) {
                        self.package_display_specifiers
                            .insert((source.id, target.clone()), candidate.clone());
                        break;
                    }
                }
            }
        }
    }

    /// Creates a Program using fully normalized compiler options, including
    /// module resolution and bundled default-library selection.
    #[must_use]
    pub fn new_with_options(
        file_system: &dyn FileSystem,
        current_directory: &str,
        root_names: &[String],
        mut options: CompilerOptions,
    ) -> Self {
        options.normalize_strict_flags();
        let mut program =
            Self::new_unchecked_with_options(file_system, current_directory, root_names, options);
        program.load_remaining_program_graph(file_system);
        program.check_program_legacy();
        program
    }

    /// Creates a Program and checks it through the experimental canonical
    /// diagnostics-only semantic core.
    ///
    /// The complete file graph is canonically traversed before declaration
    /// replay starts. One checker context then borrows the Program's arenas for
    /// the duration of checking, and only owned diagnostics are committed after
    /// every eligible source succeeds. The legacy checker is never invoked and
    /// there is no fallback on an unsupported canonical boundary.
    /// Diagnostics and their validated, owned related records are source-sorted
    /// by the pinned Program comparator after canonical checking. Program-level
    /// deduplication remains explicit follow-up work.
    /// Bundled default declarations participate in binding and global-type
    /// initialization but are not source-checked: they are immutable pinned
    /// compiler inputs, while declaration-file source checking is not installed.
    ///
    /// Emit is intentionally unavailable on the returned Program until the
    /// canonical emit-resolver surface is ported.
    ///
    /// # Errors
    ///
    /// Returns [`CanonicalProgramCheckError`] when canonical binding, checker
    /// construction, source checking, or owned diagnostic conversion fails.
    pub fn try_new_with_canonical_checker(
        file_system: &dyn FileSystem,
        current_directory: &str,
        root_names: &[String],
        options: CompilerOptions,
    ) -> Result<Self, CanonicalProgramCheckError> {
        Self::try_new_with_canonical_checker_with_config_path(
            file_system,
            current_directory,
            root_names,
            options,
            None,
        )
    }

    /// Creates a canonically checked Program with explicit project provenance.
    ///
    /// A configuration file only affects provenance when its path is provided
    /// here. An unrelated configuration on the filesystem is not sufficient.
    ///
    /// # Errors
    ///
    /// Returns the same construction failures as
    /// [`Self::try_new_with_canonical_checker`].
    pub fn try_new_with_canonical_checker_with_config_path(
        file_system: &dyn FileSystem,
        current_directory: &str,
        root_names: &[String],
        options: CompilerOptions,
        config_file_path: Option<&str>,
    ) -> Result<Self, CanonicalProgramCheckError> {
        Self::try_new_with_canonical_checker_and_queries_with_config_path(
            file_system,
            current_directory,
            root_names,
            options,
            config_file_path,
            |_, _| (),
        )
        .map(|(program, _)| program)
    }

    /// Checks a Program and runs queries against its original canonical graph.
    ///
    /// The callback runs after every source has checked successfully and
    /// before the checker releases its borrowed Program arenas. Its return
    /// value is owned, so neither checker references nor AST borrows escape.
    /// When `noCheck` skips checker construction, the callback is not called
    /// and the query result is `None`.
    ///
    /// # Errors
    ///
    /// Returns the same atomic construction failures as
    /// [`Self::try_new_with_canonical_checker`].
    pub fn try_new_with_canonical_checker_and_queries<T>(
        file_system: &dyn FileSystem,
        current_directory: &str,
        root_names: &[String],
        options: CompilerOptions,
        queries: impl FnOnce(&Self, &mut CanonicalProgramQueries<'_>) -> T,
    ) -> Result<(Self, Option<T>), CanonicalProgramCheckError> {
        Self::try_new_with_canonical_checker_and_queries_with_config_path(
            file_system,
            current_directory,
            root_names,
            options,
            None,
            queries,
        )
    }

    /// Checks a Program with explicit project provenance and runs graph queries.
    ///
    /// # Errors
    ///
    /// Returns the same construction failures as
    /// [`Self::try_new_with_canonical_checker_and_queries`].
    pub fn try_new_with_canonical_checker_and_queries_with_config_path<T>(
        file_system: &dyn FileSystem,
        current_directory: &str,
        root_names: &[String],
        options: CompilerOptions,
        config_file_path: Option<&str>,
        queries: impl FnOnce(&Self, &mut CanonicalProgramQueries<'_>) -> T,
    ) -> Result<(Self, Option<T>), CanonicalProgramCheckError> {
        let mut program = Self::new_unchecked_with_options_and_checker(
            file_system,
            current_directory,
            root_names,
            options,
            ProgramChecker::Canonical,
        );
        program.config_file_path = config_file_path.map(|path| {
            if is_absolute(path) {
                ts_path::normalize_path(path)
            } else {
                resolve_path(&program.current_directory, &[path])
            }
        });
        program.load_remaining_program_graph(file_system);
        if let Some(diagnostic) = program.common_source_directory_diagnostic(file_system) {
            program.diagnostics.push(diagnostic);
        }
        let settings = program.options.printer_settings();
        if settings.emit_javascript || settings.emit_declarations {
            let diagnostics = program.canonical_output_diagnostics();
            program.diagnostics.extend(diagnostics);
        }
        let mut result = None;
        if !program.options.no_check {
            let (diagnostics, query_result) = program.check_program_canonical(queries)?;
            program.diagnostics.extend(diagnostics);
            result = Some(query_result);
        }
        program.diagnostics.sort_by(compare_program_diagnostics);
        Ok((program, result))
    }

    fn load_remaining_program_graph(&mut self, file_system: &dyn FileSystem) {
        if self.options.incremental
            && self.options.incremental_specified
            && self.options.ts_build_info_file.is_none()
            && self.config_file_path.is_none()
        {
            self.diagnostics
                .push(incremental_requires_config_diagnostic());
        }
        if self.options.emit_declaration_only
            && !self.options.declaration
            && !self.options.composite
        {
            self.diagnostics.push(emit_declaration_only_diagnostic());
        }
        let mut resolution_options = self.options.module_resolution_options();
        // Resolving a JavaScript file does not imply admitting it to the Program.
        resolution_options.allow_javascript = true;
        if !self.options.no_check && !self.root_file_names.is_empty() {
            self.load_default_libraries();
            self.load_automatic_type_directives(file_system, &resolution_options);
        }
        self.load_module_graph(file_system, resolution_options);
    }

    fn common_source_directory(&self) -> String {
        if let Some(root_directory) = self.options.root_dir.as_deref() {
            let root_directory = canonicalize(
                root_directory,
                &self.current_directory,
                CaseSensitivity::Sensitive,
            );
            return ts_path::ensure_trailing_directory_separator(&root_directory);
        }

        if let Some(config_file_path) = self.config_file_path.as_deref() {
            return ts_path::ensure_trailing_directory_separator(&directory_path(config_file_path));
        }

        let source_names = self
            .source_files
            .iter()
            .filter(|source| {
                !source.is_default_library
                    && !ts_path::is_declaration_file(&source.file_name)
                    && self.source_should_emit(source)
            })
            .map(|source| source.file_name.clone())
            .collect::<Vec<_>>();
        ts_outputpaths::common_source_directory(
            &source_names,
            &self.current_directory,
            self.case_sensitivity,
        )
    }

    fn common_source_directory_diagnostic(
        &self,
        file_system: &dyn FileSystem,
    ) -> Option<ProgramDiagnostic> {
        if self.options.no_emit || self.options.composite {
            return None;
        }
        let config_file = self.config_file_path.as_deref()?;
        let config_source = file_system.read_file(config_file).ok()?;
        if self.has_explicit_config_root_directory(config_file, &config_source) {
            return None;
        }
        let (option, fallback) = if self.options.out_file.is_some() {
            ("outFile", None)
        } else if self.options.out_dir.is_some() {
            ("outDir", Some("declarationDir"))
        } else if self.options.declaration && self.options.declaration_dir.is_some() {
            ("declarationDir", None)
        } else {
            return None;
        };
        let emitted_sources = self
            .source_files
            .iter()
            .filter(|source| {
                !source.is_default_library
                    && !ts_path::is_declaration_file(&source.file_name)
                    && self.source_should_emit(source)
            })
            .map(|source| source.file_name.clone())
            .collect::<Vec<_>>();
        if emitted_sources.is_empty() {
            return None;
        }
        let inferred_directory = ts_outputpaths::common_source_directory(
            &emitted_sources,
            &self.current_directory,
            self.case_sensitivity,
        );
        if inferred_directory.is_empty()
            || canonicalize(
                &self.common_source_directory(),
                &self.current_directory,
                self.case_sensitivity,
            ) == canonicalize(
                &inferred_directory,
                &self.current_directory,
                self.case_sensitivity,
            )
        {
            return None;
        }

        let range = compiler_option_key_range(config_file, &config_source, option, fallback)?;
        let relative = ts_path::relative_path_from_directory(
            &directory_path(config_file),
            &inferred_directory,
            self.case_sensitivity,
        );
        let relative = if relative.starts_with('.') || is_absolute(&relative) {
            relative
        } else {
            format!("./{relative}")
        };
        let config_name = config_file.rsplit('/').next().unwrap_or(config_file);
        let message = message_by_code(5011)?;
        let migration = message_by_code(5111)?;
        let message = format!(
            "{}\n  {}",
            message.format(&[config_name.to_owned(), relative]).ok()?,
            migration.text(),
        );
        Some(ProgramDiagnostic {
            file_name: Some(config_file.to_owned()),
            range: Some(range),
            code: Some(5011),
            category: Category::Error,
            message,
            related_information: Vec::new(),
        })
    }

    fn has_explicit_config_root_directory(&self, file_name: &str, source: &str) -> bool {
        let Some(root_directory) = self.options.root_dir.as_deref() else {
            return false;
        };
        let explicitly_configured =
            ts_config::parse_jsonc(file_name, source)
                .value
                .is_some_and(|config| {
                    config
                        .as_object()
                        .and_then(|root| root.get("compilerOptions"))
                        .and_then(ts_config::JsonValue::as_object)
                        .is_some_and(|options| {
                            options
                                .keys()
                                .any(|key| key.eq_ignore_ascii_case("rootDir"))
                        })
                });
        explicitly_configured
            || canonicalize(
                root_directory,
                &self.current_directory,
                self.case_sensitivity,
            ) != canonicalize(
                &directory_path(file_name),
                &self.current_directory,
                self.case_sensitivity,
            )
    }

    fn canonical_output_diagnostics(&self) -> Vec<ProgramDiagnostic> {
        let common_source_directory = self.common_source_directory();
        let bundle_emits_javascript = self.options.out_file.is_none()
            || self.bundle_sources().into_iter().any(|source| {
                matches!(self.options.module, ModuleKind::Amd | ModuleKind::System)
                    || !source_is_external_module(source)
            });
        let mut observed_output_paths = BTreeSet::new();
        let mut reported_input_collisions = BTreeSet::new();
        let mut reported_output_collisions = BTreeSet::new();

        let mut diagnostics = Vec::new();
        for source in self.source_files.iter().filter(|source| {
            !source.is_default_library
                && !ts_path::is_declaration_file(&source.file_name)
                && self.source_should_emit(source)
        }) {
            let paths = if self.options.out_file.is_some() {
                let Some(paths) =
                    ts_outputpaths::bundle_output_paths(&self.options, &self.current_directory)
                else {
                    continue;
                };
                paths
            } else {
                ts_outputpaths::output_paths(
                    &source.file_name,
                    &self.options,
                    &self.current_directory,
                    &common_source_directory,
                    self.case_sensitivity,
                )
            };
            for file_name in [
                paths.javascript.filter(|_| bundle_emits_javascript),
                paths.declaration,
            ]
            .into_iter()
            .flatten()
            {
                let canonical =
                    canonicalize(&file_name, &self.current_directory, self.case_sensitivity);
                let repeated_output = !observed_output_paths.insert(canonical.clone());
                if self.output_overwrites_input(&file_name)
                    && reported_input_collisions.insert(canonical.clone())
                {
                    let mut diagnostic = output_overwrites_input_diagnostic(&file_name);
                    if self.config_file_path.is_none() {
                        let advice =
                            message_by_code(5068).expect("TS5068 must be in the generated catalog");
                        diagnostic.message.push_str("\n  ");
                        diagnostic.message.push_str(advice.text());
                    }
                    diagnostics.push(diagnostic);
                }
                if repeated_output
                    && self.options.out_file.is_none()
                    && reported_output_collisions.insert(canonical)
                {
                    diagnostics.push(output_collision_diagnostic(&file_name));
                }
            }
        }
        diagnostics
    }

    /// Creates a Program from the explicit `files` list in a tsconfig.
    /// Include/exclude glob expansion is added by the file-loader layer.
    #[must_use]
    pub fn from_config(file_system: &dyn FileSystem, config_path: &str) -> Self {
        Self::from_config_with_options(file_system, config_path, ProgramOptionsOverride::default())
    }

    /// Creates a Program from a tsconfig and applies command-line overrides.
    #[must_use]
    pub fn from_config_with_options(
        file_system: &dyn FileSystem,
        config_path: &str,
        overrides: ProgramOptionsOverride,
    ) -> Self {
        Self::from_config_with_overrides(file_system, config_path, overrides, None)
    }

    #[must_use]
    pub fn from_config_with_command_line_options(
        file_system: &dyn FileSystem,
        config_path: &str,
        overrides: ProgramOptionsOverride,
        command_line_options: &CompilerOptions,
        specified_options: &BTreeSet<String>,
    ) -> Self {
        Self::from_config_with_overrides(
            file_system,
            config_path,
            overrides,
            Some((command_line_options, specified_options)),
        )
    }

    /// Loads a tsconfig and checks its file graph with the canonical checker.
    ///
    /// The query callback uses the original canonical graph and can read config
    /// diagnostics. It is not called when the config cannot be loaded or when
    /// `noCheck` disables checking. This method never invokes the legacy checker
    /// or emits files.
    ///
    /// # Errors
    ///
    /// Returns the same construction failures as
    /// [`Self::try_new_with_canonical_checker_and_queries`]. Config diagnostics
    /// remain on the returned Program. Project references return
    /// [`CanonicalProgramCheckError::ProjectReferencesUnsupported`].
    pub fn try_from_config_with_canonical_checker_and_queries<T>(
        file_system: &dyn FileSystem,
        config_path: &str,
        queries: impl FnOnce(&Self, &mut CanonicalProgramQueries<'_>) -> T,
    ) -> Result<(Self, Option<T>), CanonicalProgramCheckError> {
        let ProgramConfigInputs {
            config_path,
            current_directory,
            root_names,
            has_project_references,
            options,
            mut diagnostics,
            graph_config,
            config_resolution_observation,
        } = match Self::load_config_inputs(
            file_system,
            config_path,
            ProgramOptionsOverride::default(),
            None,
        ) {
            Ok(inputs) => inputs,
            Err(ProgramConfigLoadError {
                diagnostics,
                config_resolution_observation,
            }) => {
                return Ok((
                    Self {
                        diagnostics,
                        config_file_path: Some(ts_path::normalize_path(config_path)),
                        graph_config_resolution_observation: Some(config_resolution_observation),
                        checker: ProgramChecker::Canonical,
                        ..Self::default()
                    },
                    None,
                ));
            }
        };
        if has_project_references {
            return Err(CanonicalProgramCheckError::ProjectReferencesUnsupported { config_path });
        }
        let mut program = Self::new_unchecked_with_options_and_checker(
            file_system,
            &current_directory,
            &root_names,
            options,
            ProgramChecker::Canonical,
        );
        program.config_file_path = Some(config_path);
        program.graph_config = Some(graph_config);
        program.graph_config_resolution_observation = Some(config_resolution_observation);
        program.load_remaining_program_graph(file_system);
        if let Some(diagnostic) = program.common_source_directory_diagnostic(file_system) {
            diagnostics.push(diagnostic);
        }
        let settings = program.options.printer_settings();
        if settings.emit_javascript || settings.emit_declarations {
            let output_diagnostics = program.canonical_output_diagnostics();
            program.diagnostics.extend(output_diagnostics);
        }
        program.add_config_diagnostics(diagnostics);
        let mut result = None;
        if !program.options.no_check {
            let (diagnostics, query_result) = program.check_program_canonical(queries)?;
            program.diagnostics.extend(diagnostics);
            result = Some(query_result);
        }
        program.diagnostics.sort_by(compare_program_diagnostics);
        Ok((program, result))
    }

    fn from_config_with_overrides(
        file_system: &dyn FileSystem,
        config_path: &str,
        overrides: ProgramOptionsOverride,
        command_line: Option<(&CompilerOptions, &BTreeSet<String>)>,
    ) -> Self {
        let ProgramConfigInputs {
            config_path,
            current_directory,
            root_names,
            options,
            mut diagnostics,
            graph_config,
            config_resolution_observation,
            ..
        } = match Self::load_config_inputs(file_system, config_path, overrides, command_line) {
            Ok(inputs) => inputs,
            Err(ProgramConfigLoadError {
                diagnostics,
                config_resolution_observation,
            }) => {
                return Self {
                    diagnostics,
                    config_file_path: Some(ts_path::normalize_path(config_path)),
                    graph_config_resolution_observation: Some(config_resolution_observation),
                    ..Self::default()
                };
            }
        };
        let mut program =
            Self::new_with_options(file_system, &current_directory, &root_names, options);
        program.config_file_path = Some(config_path);
        program.graph_config = Some(graph_config);
        program.graph_config_resolution_observation = Some(config_resolution_observation);
        if let Some(diagnostic) = program.common_source_directory_diagnostic(file_system) {
            diagnostics.push(diagnostic);
        }
        program.add_config_diagnostics(diagnostics);
        program
    }

    fn load_config_inputs(
        file_system: &dyn FileSystem,
        config_path: &str,
        overrides: ProgramOptionsOverride,
        command_line: Option<(&CompilerOptions, &BTreeSet<String>)>,
    ) -> Result<ProgramConfigInputs, ProgramConfigLoadError> {
        let observed = resolve_config_file_with_observation(
            file_system,
            config_path,
            ConfigObservationLimits::default(),
        );
        let parsed = observed.result;
        let config_resolution_observation = observed.observation;
        let mut config_diagnostics: Vec<_> =
            parsed.diagnostics.iter().map(config_diagnostic).collect();
        let Some(config) = parsed.value else {
            return Err(ProgramConfigLoadError {
                diagnostics: config_diagnostics,
                config_resolution_observation,
            });
        };
        let config_directory = config
            .path
            .rsplit_once('/')
            .map_or(".", |(directory, _)| directory);
        let mut options_result = parse_project_options(&config);
        let config_source = file_system.read_file(&config.path).ok();
        let graph_config = ProgramGraphConfig {
            source_text: config_source.clone(),
            resolved: config.clone(),
        };
        let empty_files = config
            .raw
            .get("files")
            .and_then(ts_config::JsonValue::as_array)
            .is_some_and(<[ts_config::JsonValue]>::is_empty);
        let no_references = config
            .raw
            .get("references")
            .and_then(ts_config::JsonValue::as_array)
            .is_none_or(<[ts_config::JsonValue]>::is_empty);
        if empty_files && no_references {
            // Resolution removes extends, but it suppresses TS18002 on the leaf config.
            let has_extends = config_source
                .as_deref()
                .and_then(|source| ts_config::parse_config_text(&config.path, source).value)
                .is_some_and(|config| {
                    config
                        .raw
                        .get("extends")
                        .is_some_and(|value| !matches!(value, ts_config::JsonValue::Null))
                });
            if !has_extends {
                config_diagnostics.push(Self::empty_files_config_diagnostic(
                    &config.path,
                    config_source.as_deref(),
                ));
            }
        }
        config_diagnostics.extend(options_result.diagnostics.iter().map(|diagnostic| {
            ProgramDiagnostic {
                file_name: Some(config.path.clone()),
                range: config_source.as_deref().and_then(|source| {
                    compiler_option_diagnostic_range(&config.path, source, diagnostic)
                }),
                code: Some(diagnostic.code()),
                category: diagnostic.category(),
                message: diagnostic
                    .render()
                    .unwrap_or_else(|error| error.to_string()),
                related_information: Vec::new(),
            }
        }));
        if let Some(value) = overrides.no_check {
            options_result.options.no_check = value;
        }
        if let Some(value) = overrides.no_emit {
            options_result.options.no_emit = value;
        }
        if let Some(value) = overrides.no_lib {
            options_result.options.no_lib = value;
            if value {
                options_result.options.lib = None;
            }
        }
        if let Some((command_line_options, specified_options)) = command_line {
            options_result
                .options
                .apply_overrides(command_line_options, specified_options);
        }
        let mut discovery = DiscoveryOptions::new(config_directory);
        let has_files = config.files.is_some();
        discovery.files = config.files.unwrap_or_default();
        discovery.include = config.include.unwrap_or_else(|| {
            if has_files {
                Vec::new()
            } else {
                vec!["**/*".to_owned()]
            }
        });
        discovery.exclude = config.exclude.unwrap_or_default();
        if options_result.options.allow_js {
            discovery.extensions.extend([
                FileExtension::Js,
                FileExtension::Jsx,
                FileExtension::Mjs,
                FileExtension::Cjs,
            ]);
        }
        if options_result.options.resolve_json_module {
            discovery.extensions.push(FileExtension::Json);
        }
        let mut roots = discover_files(file_system, &discovery).unwrap_or_else(|error| {
            config_diagnostics.push(ProgramDiagnostic {
                file_name: Some(config.path.clone()),
                range: None,
                code: None,
                category: Category::Error,
                message: error.to_string(),
                related_information: Vec::new(),
            });
            discovery.files.clone()
        });
        if options_result.options.resolve_json_module {
            let has_json_extension = |path: &str| {
                Path::new(path)
                    .extension()
                    .and_then(|extension| extension.to_str())
                    .is_some_and(|extension| extension.eq_ignore_ascii_case("json"))
            };
            let case_sensitive = file_system.use_case_sensitive_file_names();
            let case_sensitivity = if case_sensitive {
                CaseSensitivity::Sensitive
            } else {
                CaseSensitivity::Insensitive
            };
            let explicit_files = discovery
                .files
                .iter()
                .map(|file| canonicalize(file, config_directory, case_sensitivity))
                .collect::<BTreeSet<_>>();
            let json_patterns = discovery
                .include
                .iter()
                .filter(|include| has_json_extension(include))
                .filter_map(|include| {
                    GlobPattern::compile(include, config_directory, case_sensitive, false)
                })
                .collect::<Vec<_>>();
            roots.retain(|root| {
                !has_json_extension(root)
                    || explicit_files.contains(&canonicalize(
                        root,
                        config_directory,
                        case_sensitivity,
                    ))
                    || json_patterns.iter().any(|pattern| pattern.matches(root))
            });
        }
        options_result.options.normalize_strict_flags();
        Ok(ProgramConfigInputs {
            current_directory: config_directory.to_owned(),
            config_path: config.path,
            root_names: roots,
            has_project_references: !config.references.is_empty(),
            options: options_result.options,
            diagnostics: config_diagnostics,
            graph_config,
            config_resolution_observation,
        })
    }

    fn empty_files_config_diagnostic(config_path: &str, source: Option<&str>) -> ProgramDiagnostic {
        let range = source.and_then(|source| {
            let mut scanner = Scanner::new(source);
            let mut object_depth = 0usize;
            loop {
                let token = scanner.scan();
                match token.kind {
                    SyntaxKind::EndOfFile => return None,
                    SyntaxKind::OpenBraceToken => object_depth = object_depth.checked_add(1)?,
                    SyntaxKind::CloseBraceToken => object_depth = object_depth.checked_sub(1)?,
                    SyntaxKind::StringLiteral
                        if object_depth == 1
                            && token.value.as_ref()?.to_string_lossy() == "files" =>
                    {
                        let checkpoint = scanner.mark();
                        if scanner.scan().kind == SyntaxKind::ColonToken {
                            let open = scanner.scan();
                            let close = scanner.scan();
                            if open.kind == SyntaxKind::OpenBracketToken
                                && close.kind == SyntaxKind::CloseBracketToken
                            {
                                return Some(TextRange::new(open.range.start, close.range.end));
                            }
                        }
                        scanner.rewind(checkpoint);
                    }
                    _ => {}
                }
            }
        });
        let message = message_by_code(18_002).expect("TS18002 must be in the generated catalog");
        ProgramDiagnostic {
            file_name: Some(config_path.to_owned()),
            range,
            code: Some(message.code()),
            category: message.category(),
            message: message
                .format(&[config_path.to_owned()])
                .expect("TS18002 has one formatting argument"),
            related_information: Vec::new(),
        }
    }

    fn add_config_diagnostics(&mut self, mut config_diagnostics: Vec<ProgramDiagnostic>) {
        config_diagnostics.sort_by(compare_program_diagnostics);
        self.diagnostics.retain(|diagnostic| {
            if diagnostic.file_name.is_some() {
                return true;
            }
            diagnostic.code != Some(5074)
                && !config_diagnostics.iter().any(|configured| {
                    configured.code == diagnostic.code && configured.message == diagnostic.message
                })
        });
        config_diagnostics.append(&mut self.diagnostics);
        self.diagnostics = config_diagnostics;
    }

    /// Returns files in storage order, where each index equals its `FileId`.
    /// The canonical checker uses a separate semantic order.
    #[must_use]
    pub fn source_files(&self) -> &[SourceFile] {
        &self.source_files
    }

    #[must_use]
    pub fn diagnostics(&self) -> &[ProgramDiagnostic] {
        &self.diagnostics
    }

    /// Returns the configuration file that originated this Program, if any.
    #[must_use]
    pub fn config_file_path(&self) -> Option<&str> {
        self.config_file_path.as_deref()
    }

    #[must_use]
    pub const fn options(&self) -> &CompilerOptions {
        &self.options
    }

    #[must_use]
    pub fn source_file(&self, file_name: &str) -> Option<&SourceFile> {
        let canonical = canonicalize(file_name, &self.current_directory, self.case_sensitivity);
        self.file_index
            .get(&canonical)
            .and_then(|index| self.source_files.get(*index))
    }

    /// Looks up a source file by its stable program identity.
    #[must_use]
    pub fn source_file_by_id(&self, id: FileId) -> Option<&SourceFile> {
        self.source_files
            .get(id.index())
            .filter(|source| source.id == id)
    }

    /// Looks up a node using its unambiguous program-wide identity.
    #[must_use]
    pub fn node(&self, node: NodeRef) -> Option<&Node> {
        let source = self.source_file_by_id(node.file)?;
        node.is_for(source.parse.arena.id(), source.id)
            .then(|| source.parse.arena.get(node.node))
            .flatten()
    }

    /// Emits modern JavaScript for all implementation source files currently
    /// supported by the printer.
    #[must_use]
    #[allow(clippy::too_many_lines)]
    pub fn emit(&self) -> EmitOutput {
        let mut output = EmitOutput::default();
        if self.checker == ProgramChecker::Canonical {
            output
                .diagnostics
                .push(canonical_emit_unavailable_diagnostic());
            return output;
        }
        if self.options.no_emit_on_error && !self.diagnostics.is_empty() {
            return output;
        }
        let settings = self.options.printer_settings();
        let jsx_factory = self
            .options
            .jsx_factory
            .as_ref()
            .filter(|factory| is_valid_jsx_factory_expression(factory, false))
            .cloned()
            .or_else(|| {
                self.options
                    .react_namespace
                    .as_ref()
                    .map(|namespace| format!("{namespace}.createElement"))
            });
        let jsx_fragment_factory = self
            .options
            .jsx_fragment_factory
            .as_deref()
            .filter(|factory| is_valid_jsx_factory_expression(factory, true));
        if !settings.emit_javascript && !settings.emit_declarations {
            return output;
        }
        if self.options.out_file.is_some() {
            return self.emit_bundle(settings);
        }
        let common_source_directory = self.common_source_directory();
        let mut checked_paths = BTreeSet::new();
        for (source_index, source_file) in self.source_files.iter().enumerate() {
            if source_file.is_default_library
                || ts_path::is_declaration_file(&source_file.file_name)
                || !self.source_should_emit(source_file)
            {
                continue;
            }
            let paths = ts_outputpaths::output_paths(
                &source_file.file_name,
                &self.options,
                &self.current_directory,
                &common_source_directory,
                self.case_sensitivity,
            );
            let enum_member_values = enum_values_for_emit(&source_file.checking.enum_member_values);
            let enum_access_values = enum_values_for_emit(&source_file.checking.enum_access_values);
            let javascript_output_overwrites_input = paths
                .javascript
                .as_deref()
                .is_some_and(|file_name| self.output_overwrites_input(file_name));
            if settings.emit_javascript
                && javascript_output_overwrites_input
                && let Some(file_name) = paths.javascript.as_deref()
                && checked_paths.insert(canonicalize(
                    file_name,
                    &self.current_directory,
                    self.case_sensitivity,
                ))
            {
                output
                    .diagnostics
                    .push(output_overwrites_input_diagnostic(file_name));
            }
            if settings.emit_javascript && !javascript_output_overwrites_input {
                let node_module_kind = matches!(
                    settings.module,
                    ModuleKind::Node16
                        | ModuleKind::Node18
                        | ModuleKind::Node20
                        | ModuleKind::NodeNext
                );
                let mut source_settings =
                    source_printer_settings(settings, &source_file.source_text);
                let lower_file_name = source_file.file_name.to_ascii_lowercase();
                let fixed_es_module = [".mts", ".mjs"]
                    .iter()
                    .any(|extension| lower_file_name.ends_with(extension));
                let fixed_commonjs_module = [".cts", ".cjs"]
                    .iter()
                    .any(|extension| lower_file_name.ends_with(extension));
                if self.options.module_specified
                    && source_settings.module == ModuleKind::None
                    && source_is_external_module(source_file)
                {
                    source_settings.module = ModuleKind::CommonJs;
                } else if matches!(
                    source_settings.module,
                    ModuleKind::Node16
                        | ModuleKind::Node18
                        | ModuleKind::Node20
                        | ModuleKind::NodeNext
                ) {
                    source_settings.module = source_file.implied_node_format;
                } else if source_settings.module == ModuleKind::CommonJs && fixed_es_module {
                    source_settings.module = ModuleKind::EsNext;
                } else if matches!(
                    source_settings.module,
                    ModuleKind::Es2015
                        | ModuleKind::Es2020
                        | ModuleKind::Es2022
                        | ModuleKind::EsNext
                ) && fixed_commonjs_module
                {
                    source_settings.module = ModuleKind::CommonJs;
                }
                let amd_dependencies = source_file
                    .parse
                    .amd_dependencies
                    .iter()
                    .map(|dependency| PrinterAmdDependency {
                        path: &dependency.path,
                        name: dependency.name.as_deref(),
                        comment_start: dependency.range.start.get(),
                        comment_end: dependency.range.end.get(),
                    })
                    .collect::<Vec<_>>();
                let preserve_const_enums = self.options.preserve_const_enums
                    || self.options.isolated_modules
                    || self.options.verbatim_module_syntax;
                let jsx_import_source =
                    source_jsx_pragma_value(&source_file.source_text, "@jsxImportSource")
                        .or(self.options.jsx_import_source.as_deref());
                let mut import_runtime_meanings = import_runtime_meanings_for_emit(
                    source_file,
                    preserve_const_enums,
                    source_settings.module == ModuleKind::Amd,
                    &later_top_level_script_variable_names(
                        self.source_files.iter().skip(source_index + 1),
                    ),
                );
                if matches!(
                    source_settings.jsx,
                    ts_options::JsxEmit::React | ts_options::JsxEmit::Preserve
                ) && source_file.parse.arena.iter().any(|(_, node)| {
                    matches!(
                        node.data,
                        NodeData::JsxElement(_)
                            | NodeData::JsxSelfClosingElement(_)
                            | NodeData::JsxFragment(_)
                    )
                }) {
                    preserve_classic_jsx_factory_import(
                        source_file,
                        &mut import_runtime_meanings,
                        jsx_factory.as_deref().unwrap_or("React.createElement"),
                    );
                }
                let preserve_top_of_file_reference_directive = self
                    .source_has_resolved_path_reference(source_file)
                    || has_preserved_reference_directive(&source_file.source_text);
                let emit_context = EmitContext {
                    bindings: &source_file.binding,
                    bundle_namespace_members: &BTreeMap::new(),
                    amd_module_name: source_file.parse.amd_module_name.as_deref(),
                    amd_bundle: false,
                    preemitted_source_prologues: false,
                    preemitted_shebang: source_shebang(source_file).is_some(),
                    suppress_extends_helper: false,
                    preemitted_comment_end: None,
                    preserve_top_of_file_reference_directive,
                    amd_dependencies: &amd_dependencies,
                    amd_module_specifier_rewrites: &BTreeMap::new(),
                    amd_generated_name_offsets: &BTreeMap::new(),
                    enum_member_values: &enum_member_values,
                    enum_access_values: &enum_access_values,
                    import_runtime_meanings: &import_runtime_meanings,
                    preserve_const_enums,
                    inline_const_enums: !self.options.isolated_modules
                        && !self.options.verbatim_module_syntax,
                    emit_decorator_metadata: self.options.emit_decorator_metadata,
                    es_module_interop: self.options.es_module_interop,
                    preserve_dynamic_import: matches!(
                        settings.module,
                        ModuleKind::Node16
                            | ModuleKind::Node18
                            | ModuleKind::Node20
                            | ModuleKind::NodeNext
                    ),
                    verbatim_module_syntax: self.options.verbatim_module_syntax,
                    isolated_modules: self.options.isolated_modules,
                    strict_null_checks: self.options.strict_null_checks,
                    no_lib: self.options.no_lib,
                    force_use_strict: fixed_es_module && settings.module == ModuleKind::CommonJs,
                    jsx_factory: jsx_factory.as_deref(),
                    jsx_fragment_factory,
                    jsx_import_source,
                    downlevel_iteration: self.options.downlevel_iteration,
                    module_detection: if node_module_kind {
                        ModuleDetectionKind::Force
                    } else {
                        self.options.module_detection
                    },
                };
                match emit_source_file_with_context(
                    &source_file.parse.arena,
                    source_file.parse.source_file,
                    &source_file.file_name,
                    &source_file.source_text,
                    source_settings,
                    &emit_context,
                ) {
                    Ok(mut emitted) => {
                        let Some(file_name) = paths.javascript.clone() else {
                            continue;
                        };
                        let shebang = source_shebang(source_file);
                        if let Some(shebang) = shebang {
                            emitted.code = format!("{shebang}\n{}", emitted.code);
                        }
                        if let Some(mut source_map) = emitted.source_map {
                            if shebang.is_some() {
                                source_map.mappings.insert(0, ';');
                            }
                            if self.options.inline_sources {
                                source_map.sources_content =
                                    Some(vec![source_file.source_text.clone()]);
                            }
                            source_map.file = file_name.rsplit('/').next().map(str::to_owned);
                            let source_map_file = paths
                                .source_map
                                .clone()
                                .unwrap_or_else(|| format!("{file_name}.map"));
                            let source_map_directory = if self.options.source_root.is_some() {
                                common_source_directory.clone()
                            } else {
                                self.logical_source_map_path(&source_map_file).map_or_else(
                                    || directory_path(&file_name),
                                    |path| directory_path(&path),
                                )
                            };
                            make_source_map_sources_relative(
                                &mut source_map,
                                &source_map_directory,
                                self.case_sensitivity,
                            );
                            let serialized = serialize_source_map(
                                &source_map,
                                self.options.source_root.as_deref(),
                            );
                            if settings.inline_source_map {
                                emitted
                                    .code
                                    .push_str("//# sourceMappingURL=data:application/json;base64,");
                                emitted.code.push_str(&base64_encode(serialized.as_bytes()));
                            } else if let Some(map_file_name) = paths.source_map.clone() {
                                emitted.code.push_str("//# sourceMappingURL=");
                                emitted
                                    .code
                                    .push_str(&self.source_map_url(&file_name, &map_file_name));
                                output.files.push(OutputFile {
                                    file_name: map_file_name,
                                    text: serialized,
                                });
                            }
                        }
                        output.files.push(OutputFile {
                            file_name,
                            text: emitted.code,
                        });
                    }
                    Err(error) => output
                        .diagnostics
                        .push(emit_diagnostic(source_file, &error)),
                }
            }
            if settings.emit_declarations && !source_is_json(source_file) {
                let Some(declaration_file_name) = paths.declaration.as_deref() else {
                    continue;
                };
                if self.output_overwrites_input(declaration_file_name) {
                    let canonical = canonicalize(
                        declaration_file_name,
                        &self.current_directory,
                        self.case_sensitivity,
                    );
                    if checked_paths.insert(canonical) {
                        output
                            .diagnostics
                            .push(output_overwrites_input_diagnostic(declaration_file_name));
                    }
                    continue;
                }
                if (self.options.isolated_declarations
                    && (has_isolated_declaration_emit_error(source_file)
                        || self.source_imports_isolated_declaration_augmentation(source_file)))
                    || has_private_export_type_query(source_file)
                    || has_unserializable_exported_anonymous_class(source_file)
                    || has_unserializable_exported_class_property_type(source_file)
                    || source_file.checking.diagnostics.iter().any(|diagnostic| {
                        matches!(
                            diagnostic.diagnostic.code(),
                            2527 | 2883
                                | 4023
                                | 4025
                                | 4032
                                | 4081
                                | 4094
                                | 4118
                                | 5088
                                | 7056
                                | 9010
                        )
                    })
                {
                    continue;
                }
                let declaration_node_types =
                    declaration_node_types_for_emit(source_file, self.options.strict_null_checks);
                let declaration_import_type_references =
                    self.preferred_declaration_import_type_references(source_file);
                match emit_declaration_file_with_semantics_and_options(
                    &source_file.parse.arena,
                    source_file.parse.source_file,
                    &source_file.file_name,
                    &source_file.source_text,
                    self.options.declaration_map,
                    Some(&source_file.checking.declaration_reachability),
                    Some(&source_file.checking.import_runtime_meanings),
                    Some(&enum_member_values),
                    Some(&source_file.checking.types),
                    Some(&declaration_node_types),
                    Some(&declaration_import_type_references),
                    Some(&source_file.checking.named_type_references),
                    settings.remove_comments,
                    self.options.rewrite_relative_import_extensions,
                    self.options.strip_internal,
                ) {
                    Ok(mut emitted) => {
                        let file_name = declaration_file_name.to_owned();
                        emitted.code = remove_unused_named_declaration_imports(&emitted.code);
                        let reference_directives =
                            preserved_reference_directives(source_file, &file_name);
                        if !reference_directives.is_empty() {
                            emitted.code.insert_str(0, &reference_directives);
                        }
                        if let Some(mut source_map) = emitted.source_map {
                            source_map.sources_content = None;
                            source_map.file = file_name.rsplit('/').next().map(str::to_owned);
                            if let Some(map_file_name) = paths.declaration_map.clone() {
                                let source_map_directory = if self.options.source_root.is_some() {
                                    common_source_directory.clone()
                                } else {
                                    self.logical_source_map_path(&map_file_name).map_or_else(
                                        || directory_path(&file_name),
                                        |path| directory_path(&path),
                                    )
                                };
                                make_source_map_sources_relative(
                                    &mut source_map,
                                    &source_map_directory,
                                    self.case_sensitivity,
                                );
                                emitted.code.push_str("//# sourceMappingURL=");
                                emitted.code.push_str(&percent_encode_source_map_url(
                                    map_file_name.rsplit('/').next().unwrap_or(&map_file_name),
                                ));
                                output.files.push(OutputFile {
                                    file_name: map_file_name,
                                    text: serialize_source_map(
                                        &source_map,
                                        self.options.source_root.as_deref(),
                                    ),
                                });
                            }
                        }
                        output.files.push(OutputFile {
                            file_name,
                            text: emitted.code,
                        });
                    }
                    Err(error) => output
                        .diagnostics
                        .push(emit_diagnostic(source_file, &error)),
                }
            }
        }
        suppress_output_path_collisions(
            &mut output,
            &self.current_directory,
            self.case_sensitivity,
        );
        if self.options.emit_bom {
            prepend_emit_bom(&mut output.files);
        }
        if self.options.no_emit_on_error && !output.diagnostics.is_empty() {
            output.files.clear();
        }
        output
    }

    #[allow(clippy::too_many_lines)]
    fn emit_bundle(&self, settings: PrinterSettings) -> EmitOutput {
        let mut output = EmitOutput::default();
        let jsx_factory = self
            .options
            .jsx_factory
            .as_ref()
            .filter(|factory| is_valid_jsx_factory_expression(factory, false))
            .cloned()
            .or_else(|| {
                self.options
                    .react_namespace
                    .as_ref()
                    .map(|namespace| format!("{namespace}.createElement"))
            });
        let jsx_fragment_factory = self
            .options
            .jsx_fragment_factory
            .as_deref()
            .filter(|factory| is_valid_jsx_factory_expression(factory, true));
        let paths = ts_outputpaths::bundle_output_paths(&self.options, &self.current_directory)
            .expect("outFile was checked before bundle emission");
        let sources = self.bundle_sources();
        let javascript_sources = sources
            .iter()
            .copied()
            .filter(|source| {
                matches!(settings.module, ModuleKind::Amd | ModuleKind::System)
                    || !source_is_external_module(source)
            })
            .collect::<Vec<_>>();
        let bundle_namespace_members = bundle_namespace_members(&javascript_sources);
        let declaration_sources = if settings.emit_javascript
            && !matches!(settings.module, ModuleKind::Amd | ModuleKind::System)
        {
            &javascript_sources
        } else {
            &sources
        };
        let bundle_source_names = sources
            .iter()
            .map(|source| source.file_name.clone())
            .collect::<Vec<_>>();
        let bundle_root = ts_outputpaths::common_source_directory(
            &bundle_source_names,
            &self.current_directory,
            self.case_sensitivity,
        );

        let mut checked_paths = BTreeSet::new();
        let javascript_output_overwrites_input = paths
            .javascript
            .as_deref()
            .is_some_and(|file_name| self.output_overwrites_input(file_name));
        if settings.emit_javascript
            && !javascript_sources.is_empty()
            && javascript_output_overwrites_input
            && let Some(file_name) = paths.javascript.as_deref()
            && checked_paths.insert(canonicalize(
                file_name,
                &self.current_directory,
                self.case_sensitivity,
            ))
        {
            output
                .diagnostics
                .push(output_overwrites_input_diagnostic(file_name));
        }
        if settings.emit_javascript
            && !javascript_output_overwrites_input
            && !javascript_sources.is_empty()
        {
            let mut code = String::new();
            let mut map_builder = settings.source_map.then(SourceMapBuilder::new);
            let mut map_sources = Vec::new();
            let mut map_sources_content = Vec::new();
            let mut amd_generated_name_offsets = BTreeMap::new();
            if let Some(shebang) = javascript_sources
                .iter()
                .find_map(|source| source_shebang(source))
            {
                code.push_str(shebang);
                code.push('\n');
            }
            let mut prologues = Vec::new();
            let mut seen_prologues = HashSet::new();
            let has_script_sources = javascript_sources
                .iter()
                .any(|source| !source_is_json(source) && !source_is_external_module(source));
            for source in javascript_sources
                .iter()
                .filter(|source| !source_is_json(source) && !source_is_external_module(source))
            {
                for directive in source_prologue_directives(source) {
                    if seen_prologues.insert(directive.to_owned()) {
                        prologues.push(directive.to_owned());
                    }
                }
            }
            if has_script_sources
                && settings.always_strict
                && seen_prologues.insert("use strict".to_owned())
            {
                prologues.insert(0, "use strict".to_owned());
            }
            for directive in &prologues {
                push_bundle_prologue(&mut code, directive);
            }
            let bundle_needs_extends_helper = settings.target < ts_options::ScriptTarget::Es2015
                && !settings.no_emit_helpers
                && javascript_sources.iter().any(|source| {
                    (!settings.import_helpers || !source_is_external_module(source))
                        && source_needs_extends_helper(&source.parse.arena)
                });
            if bundle_needs_extends_helper {
                code.push_str(BUNDLE_EXTENDS_HELPER);
            }
            for (source_index, source) in javascript_sources.iter().enumerate() {
                let map_source_offset = map_builder.as_ref().map(|_| {
                    let offset = u32::try_from(map_sources.len()).unwrap_or(u32::MAX);
                    map_sources.push(source.file_name.clone());
                    if self.options.inline_sources {
                        map_sources_content.push(source.source_text.clone());
                    }
                    offset
                });
                let source_detached_comment = bundle_detached_comment(source);
                let detached_comment = (settings.module == ModuleKind::Amd
                    && source_is_external_module(source))
                .then(|| source_detached_comment.clone())
                .flatten();
                if let Some((comment, _)) = &source_detached_comment
                    && let (Some(builder), Some(source_offset)) =
                        (&mut map_builder, map_source_offset)
                {
                    let line = u32::try_from(code.bytes().filter(|byte| *byte == b'\n').count())
                        .unwrap_or(u32::MAX);
                    let comment = comment.trim_end_matches(['\n', '\r']);
                    let column = u32::try_from(comment.encode_utf16().count()).unwrap_or(u32::MAX);
                    let _ = builder.add_mapping(line, 0, source_offset, 0, 0);
                    let _ = builder.add_mapping(line, column, source_offset, 0, column);
                }
                if let Some((comment, _)) = &detached_comment {
                    code.push_str(comment);
                }
                let generated_line =
                    u32::try_from(code.bytes().filter(|byte| *byte == b'\n').count())
                        .unwrap_or(u32::MAX);
                if settings.module == ModuleKind::Amd && source_is_json(source) {
                    if let (Some(builder), Some(source_offset)) =
                        (&mut map_builder, map_source_offset)
                    {
                        let _ = builder.add_mapping(generated_line, 0, source_offset, 0, 0);
                    }
                    code.push_str("define(");
                    code.push_str(
                        &serde_json::to_string(&amd_bundle_module_name(source, &bundle_root))
                            .expect("AMD JSON module names are serializable"),
                    );
                    code.push_str(", [], ");
                    code.push_str(source.source_text.trim_end_matches(['\n', '\r']));
                    code.push_str(");\n");
                    continue;
                }
                let mut source_settings = source_printer_settings(settings, &source.source_text);
                source_settings.source_map = settings.source_map;
                source_settings.inline_source_map = false;
                source_settings.always_strict = false;
                let enum_member_values = enum_values_for_emit(&source.checking.enum_member_values);
                let enum_access_values = enum_values_for_emit(&source.checking.enum_access_values);
                let amd_dependencies = source
                    .parse
                    .amd_dependencies
                    .iter()
                    .map(|dependency| PrinterAmdDependency {
                        path: &dependency.path,
                        name: dependency.name.as_deref(),
                        comment_start: dependency.range.start.get(),
                        comment_end: dependency.range.end.get(),
                    })
                    .collect::<Vec<_>>();
                let amd_module_name =
                    (matches!(settings.module, ModuleKind::Amd | ModuleKind::System)
                        && source_is_external_module(source))
                    .then(|| {
                        if settings.module == ModuleKind::Amd {
                            amd_bundle_module_name(source, &bundle_root)
                        } else {
                            bundle_declaration_module_name(source, &bundle_root, settings.module)
                        }
                    });
                let amd_module_specifier_rewrites =
                    self.amd_bundle_specifier_rewrites(source, &bundle_root);
                let preserve_const_enums = self.options.preserve_const_enums
                    || self.options.isolated_modules
                    || self.options.verbatim_module_syntax;
                let jsx_import_source =
                    source_jsx_pragma_value(&source.source_text, "@jsxImportSource")
                        .or(self.options.jsx_import_source.as_deref());
                let mut import_runtime_meanings = import_runtime_meanings_for_emit(
                    source,
                    preserve_const_enums,
                    settings.module == ModuleKind::Amd,
                    &later_top_level_script_variable_names(
                        javascript_sources.iter().skip(source_index + 1).copied(),
                    ),
                );
                if matches!(
                    source_settings.jsx,
                    ts_options::JsxEmit::React | ts_options::JsxEmit::Preserve
                ) && source.parse.arena.iter().any(|(_, node)| {
                    matches!(
                        node.data,
                        NodeData::JsxElement(_)
                            | NodeData::JsxSelfClosingElement(_)
                            | NodeData::JsxFragment(_)
                    )
                }) {
                    preserve_classic_jsx_factory_import(
                        source,
                        &mut import_runtime_meanings,
                        jsx_factory.as_deref().unwrap_or("React.createElement"),
                    );
                }
                let emit_context = EmitContext {
                    bindings: &source.binding,
                    bundle_namespace_members: &bundle_namespace_members,
                    amd_module_name: amd_module_name.as_deref(),
                    amd_bundle: true,
                    preemitted_source_prologues: !source_is_external_module(source),
                    preemitted_shebang: source_shebang(source).is_some(),
                    suppress_extends_helper: bundle_needs_extends_helper,
                    preemitted_comment_end: detached_comment.as_ref().map(|(_, end)| *end),
                    preserve_top_of_file_reference_directive: self
                        .source_has_resolved_path_reference(source)
                        || has_preserved_reference_directive(&source.source_text),
                    amd_dependencies: &amd_dependencies,
                    amd_module_specifier_rewrites: &amd_module_specifier_rewrites,
                    amd_generated_name_offsets: &amd_generated_name_offsets,
                    enum_member_values: &enum_member_values,
                    enum_access_values: &enum_access_values,
                    import_runtime_meanings: &import_runtime_meanings,
                    preserve_const_enums,
                    inline_const_enums: !self.options.isolated_modules
                        && !self.options.verbatim_module_syntax,
                    emit_decorator_metadata: self.options.emit_decorator_metadata,
                    es_module_interop: self.options.es_module_interop,
                    preserve_dynamic_import: matches!(
                        settings.module,
                        ModuleKind::Node16
                            | ModuleKind::Node18
                            | ModuleKind::Node20
                            | ModuleKind::NodeNext
                    ),
                    verbatim_module_syntax: self.options.verbatim_module_syntax,
                    isolated_modules: self.options.isolated_modules,
                    strict_null_checks: self.options.strict_null_checks,
                    no_lib: self.options.no_lib,
                    force_use_strict: false,
                    jsx_factory: jsx_factory.as_deref(),
                    jsx_fragment_factory,
                    jsx_import_source,
                    downlevel_iteration: self.options.downlevel_iteration,
                    module_detection: self.options.module_detection,
                };
                let mut emitted_uses_tslib_dependency = false;
                match emit_source_file_with_context(
                    &source.parse.arena,
                    source.parse.source_file,
                    &source.file_name,
                    &source.source_text,
                    source_settings,
                    &emit_context,
                ) {
                    Ok(emitted) => {
                        emitted_uses_tslib_dependency = emitted.code.contains("\"tslib\"");
                        if !emitted.code.is_empty() {
                            if let Some(builder) = &mut map_builder {
                                let source_offset = map_source_offset.unwrap_or(0);
                                if let Some(source_map) = &emitted.source_map {
                                    let _ = builder.append_mappings(
                                        &source_map.mappings,
                                        generated_line,
                                        source_offset,
                                    );
                                } else {
                                    let _ =
                                        builder.add_mapping(generated_line, 0, source_offset, 0, 0);
                                }
                            }
                            code.push_str(&emitted.code);
                        }
                    }
                    Err(error) => output.diagnostics.push(emit_diagnostic(source, &error)),
                }
                for base in amd_generated_dependency_bases(source) {
                    *amd_generated_name_offsets.entry(base).or_default() += 1;
                }
                if settings.module == ModuleKind::System && source_is_external_module(source) {
                    *amd_generated_name_offsets
                        .entry("exports".to_owned())
                        .or_default() += 1;
                    *amd_generated_name_offsets
                        .entry("context".to_owned())
                        .or_default() += 1;
                }
                if emitted_uses_tslib_dependency {
                    *amd_generated_name_offsets
                        .entry("tslib".to_owned())
                        .or_default() += 1;
                }
            }
            if let Some(mut map) = map_builder.map(|builder| builder.finish(None, map_sources)) {
                let Some(file_name) = paths.javascript.as_ref() else {
                    return output;
                };
                map.file = file_name.rsplit('/').next().map(str::to_owned);
                if self.options.inline_sources {
                    map.sources_content = Some(map_sources_content);
                }
                let serialized = serialize_source_map(&map, self.options.source_root.as_deref());
                if settings.inline_source_map {
                    code.push_str("//# sourceMappingURL=data:application/json;base64,");
                    code.push_str(&base64_encode(serialized.as_bytes()));
                } else if let Some(map_file_name) = paths.source_map.clone() {
                    code.push_str("//# sourceMappingURL=");
                    code.push_str(&self.source_map_url(file_name, &map_file_name));
                    output.files.push(OutputFile {
                        file_name: map_file_name,
                        text: serialized,
                    });
                }
            }
            if let Some(file_name) = paths.javascript.clone() {
                output.files.push(OutputFile {
                    file_name,
                    text: code,
                });
            }
        }

        if settings.emit_declarations {
            if let Some(declaration_file_name) = paths.declaration.as_deref()
                && self.output_overwrites_input(declaration_file_name)
            {
                let canonical = canonicalize(
                    declaration_file_name,
                    &self.current_directory,
                    self.case_sensitivity,
                );
                if checked_paths.insert(canonical) {
                    output
                        .diagnostics
                        .push(output_overwrites_input_diagnostic(declaration_file_name));
                }
                if self.options.no_emit_on_error {
                    output.files.clear();
                }
                return output;
            }
            let mut code = String::new();
            if let Some(declaration_file) = paths.declaration.as_deref() {
                let mut seen_reference_directives = HashSet::new();
                for source in declaration_sources {
                    let lower = source.file_name.to_ascii_lowercase();
                    if lower.ends_with(".d.ts")
                        || lower.ends_with(".d.mts")
                        || lower.ends_with(".d.cts")
                    {
                        continue;
                    }
                    for directive in
                        preserved_reference_directives(source, declaration_file).lines()
                    {
                        if seen_reference_directives.insert(directive.to_owned()) {
                            code.push_str(directive);
                            code.push('\n');
                        }
                    }
                }
            }
            let mut map_builder = self.options.declaration_map.then(SourceMapBuilder::new);
            let mut map_sources = Vec::new();
            for source in declaration_sources {
                let lower = source.file_name.to_ascii_lowercase();
                if lower.ends_with(".d.ts")
                    || lower.ends_with(".d.mts")
                    || lower.ends_with(".d.cts")
                {
                    continue;
                }
                if (self.options.isolated_declarations
                    && (has_isolated_declaration_emit_error(source)
                        || self.source_imports_isolated_declaration_augmentation(source)))
                    || has_private_export_type_query(source)
                    || has_unserializable_exported_anonymous_class(source)
                    || has_unserializable_exported_class_property_type(source)
                    || source.checking.diagnostics.iter().any(|diagnostic| {
                        matches!(
                            diagnostic.diagnostic.code(),
                            2527 | 2883 | 4023 | 4025 | 4032 | 4081 | 4094 | 5088 | 7056 | 9010
                        )
                    })
                {
                    continue;
                }
                let generated_line =
                    u32::try_from(code.bytes().filter(|byte| *byte == b'\n').count())
                        .unwrap_or(u32::MAX);
                let enum_member_values = enum_values_for_emit(&source.checking.enum_member_values);
                let declaration_node_types =
                    declaration_node_types_for_emit(source, self.options.strict_null_checks);
                let declaration_import_type_references =
                    self.preferred_declaration_import_type_references(source);
                match emit_declaration_file_with_semantics_and_options(
                    &source.parse.arena,
                    source.parse.source_file,
                    &source.file_name,
                    &source.source_text,
                    false,
                    Some(&source.checking.declaration_reachability),
                    Some(&source.checking.import_runtime_meanings),
                    Some(&enum_member_values),
                    Some(&source.checking.types),
                    Some(&declaration_node_types),
                    Some(&declaration_import_type_references),
                    Some(&source.checking.named_type_references),
                    settings.remove_comments,
                    self.options.rewrite_relative_import_extensions,
                    self.options.strip_internal,
                ) {
                    Ok(mut emitted) => {
                        if !emitted.code.is_empty() {
                            if let Some(builder) = &mut map_builder {
                                let source_index =
                                    u32::try_from(map_sources.len()).unwrap_or(u32::MAX);
                                let _ = builder.add_mapping(generated_line, 0, source_index, 0, 0);
                            }
                            map_sources.push(source.file_name.clone());
                            if source_is_external_module(source) {
                                emitted.code = self.rewrite_bundle_declaration_specifiers(
                                    source,
                                    &emitted.code,
                                    &bundle_root,
                                    settings.module,
                                );
                                emitted.code = self.prefer_bundle_declaration_imports(
                                    source,
                                    &emitted.code,
                                    &bundle_root,
                                    settings.module,
                                );
                                emitted.code = self.rewrite_late_bundle_export_references(
                                    source,
                                    &emitted.code,
                                    &bundle_root,
                                    settings.module,
                                );
                                emitted.code =
                                    remove_unused_named_declaration_imports(&emitted.code);
                                emitted.code = defer_export_only_bundle_imports(&emitted.code);
                                append_bundle_declaration_module(
                                    &mut code,
                                    source,
                                    &emitted.code,
                                    &bundle_declaration_module_name(
                                        source,
                                        &bundle_root,
                                        settings.module,
                                    ),
                                    settings.module == ModuleKind::Amd,
                                );
                            } else {
                                code.push_str(&emitted.code);
                            }
                        }
                    }
                    Err(error) => output.diagnostics.push(emit_diagnostic(source, &error)),
                }
            }
            if let Some(mut map) = map_builder.map(|builder| builder.finish(None, map_sources)) {
                let Some(file_name) = paths.declaration.as_ref() else {
                    return output;
                };
                map.file = file_name.rsplit('/').next().map(str::to_owned);
                if let Some(map_file_name) = paths.declaration_map.clone() {
                    code.push_str("//# sourceMappingURL=");
                    code.push_str(&percent_encode_source_map_url(
                        map_file_name.rsplit('/').next().unwrap_or(&map_file_name),
                    ));
                    output.files.push(OutputFile {
                        file_name: map_file_name,
                        text: serialize_source_map(&map, self.options.source_root.as_deref()),
                    });
                }
            }
            if let Some(file_name) = paths.declaration.clone() {
                output.files.push(OutputFile {
                    file_name,
                    text: code,
                });
            }
        }

        if self.options.emit_bom {
            prepend_emit_bom(&mut output.files);
        }
        if self.options.no_emit_on_error && !output.diagnostics.is_empty() {
            output.files.clear();
        }
        output
    }

    fn bundle_sources(&self) -> Vec<&SourceFile> {
        fn visit(
            program: &Program,
            index: usize,
            visited: &mut BTreeSet<usize>,
            ordered: &mut Vec<usize>,
        ) {
            if !visited.insert(index) {
                return;
            }
            let source = &program.source_files[index];
            let canonical = canonicalize(
                &source.file_name,
                &program.current_directory,
                program.case_sensitivity,
            );
            for directive in reference_directives(&source.source_text)
                .into_iter()
                .filter(|directive| matches!(directive.kind, ReferenceKind::Path))
            {
                let referenced = resolve_path(
                    &directory_path(&source.file_name),
                    &[directive.value.as_str()],
                );
                let referenced = canonicalize(
                    &referenced,
                    &program.current_directory,
                    program.case_sensitivity,
                );
                if let Some(target) = program.file_index.get(&referenced) {
                    visit(program, *target, visited, ordered);
                }
            }
            for (key, target) in &program.resolved_modules {
                if key.containing_file != canonical {
                    continue;
                }
                if let Some(target) = program.file_index.get(target) {
                    visit(program, *target, visited, ordered);
                }
            }
            if !source.is_default_library
                && !ts_path::is_declaration_file(&source.file_name)
                && program.source_should_emit(source)
                && (!program.options.module_specified
                    || program.options.module != ModuleKind::None
                    || !source_is_external_module(source))
            {
                ordered.push(index);
            }
        }

        let mut visited = BTreeSet::new();
        let mut ordered = Vec::new();
        for index in 0..self.source_files.len() {
            visit(self, index, &mut visited, &mut ordered);
        }
        ordered
            .into_iter()
            .map(|index| &self.source_files[index])
            .collect()
    }

    fn source_should_emit(&self, source: &SourceFile) -> bool {
        let canonical = canonicalize(
            &source.file_name,
            &self.current_directory,
            self.case_sensitivity,
        );
        if self.root_file_names.contains(&canonical) {
            return true;
        }
        if canonical
            .split('/')
            .any(|component| component.eq_ignore_ascii_case("node_modules"))
        {
            return false;
        }
        let extension = Path::new(&source.file_name)
            .extension()
            .and_then(|extension| extension.to_str());
        if extension.is_some_and(|extension| {
            extension.eq_ignore_ascii_case("tsx") || extension.eq_ignore_ascii_case("jsx")
        }) && self.options.jsx == ts_options::JsxEmit::None
        {
            return false;
        }
        if extension.is_some_and(|extension| {
            ["js", "jsx", "mjs", "cjs"]
                .iter()
                .any(|candidate| extension.eq_ignore_ascii_case(candidate))
        }) && !self.options.allow_js
        {
            return false;
        }
        true
    }

    fn preferred_declaration_import_type_references(
        &self,
        source: &SourceFile,
    ) -> BTreeMap<TypeId, ts_checker::ImportTypeReference> {
        let mut references = source.checking.import_type_references.clone();
        for reference in references.values_mut() {
            let qualifier = reference
                .qualifier
                .split_once('.')
                .map_or(reference.qualifier.as_str(), |(root, _)| root);
            let referenced_file = ts_path::base_file_name(ts_path::remove_file_extension(
                &reference.module_specifier,
            ));
            let preferred = self.source_files.iter().find_map(|candidate| {
                if candidate.binding.exports.get(qualifier).is_none()
                    || ts_path::base_file_name(module_file_stem(&candidate.file_name))
                        != referenced_file
                {
                    return None;
                }
                let target = canonicalize(
                    &candidate.file_name,
                    &self.current_directory,
                    self.case_sensitivity,
                );
                self.package_display_specifiers.get(&(source.id, target))
            });
            if let Some(preferred) = preferred {
                reference.module_specifier.clone_from(preferred);
            }
        }
        references
    }

    fn source_has_resolved_path_reference(&self, source: &SourceFile) -> bool {
        reference_directives(&source.source_text)
            .into_iter()
            .filter(|directive| matches!(directive.kind, ReferenceKind::Path))
            .any(|directive| {
                let referenced = resolve_path(
                    &directory_path(&source.file_name),
                    &[directive.value.as_str()],
                );
                let canonical =
                    canonicalize(&referenced, &self.current_directory, self.case_sensitivity);
                self.file_index.contains_key(&canonical)
            })
    }

    fn source_imports_isolated_declaration_augmentation(&self, source: &SourceFile) -> bool {
        let containing = canonicalize(
            &source.file_name,
            &self.current_directory,
            self.case_sensitivity,
        );
        self.resolved_modules
            .iter()
            .filter(|(key, _)| key.containing_file == containing)
            .filter_map(|(_, target)| self.file_index.get(target))
            .filter_map(|index| self.source_files.get(*index))
            .any(source_has_external_module_augmentation)
    }

    fn output_overwrites_input(&self, file_name: &str) -> bool {
        let canonical = canonicalize(file_name, &self.current_directory, self.case_sensitivity);
        self.file_index.contains_key(&canonical)
    }

    fn amd_bundle_specifier_rewrites(
        &self,
        source: &SourceFile,
        bundle_root: &str,
    ) -> BTreeMap<String, String> {
        let containing = canonicalize(
            &source.file_name,
            &self.current_directory,
            self.case_sensitivity,
        );
        self.resolved_modules
            .iter()
            .filter(|(key, _)| key.containing_file == containing)
            .filter_map(|(key, target)| {
                let target = self
                    .file_index
                    .get(target)
                    .and_then(|index| self.source_files.get(*index))?;
                if ts_path::is_declaration_file(&target.file_name) {
                    return None;
                }
                Some((
                    key.specifier.clone(),
                    amd_bundle_module_name(target, bundle_root),
                ))
            })
            .collect()
    }

    fn source_map_url(&self, generated_file: &str, map_file: &str) -> String {
        let Some(logical_map) = self.logical_source_map_path(map_file) else {
            return percent_encode_source_map_url(map_file.rsplit('/').next().unwrap_or(map_file));
        };
        percent_encode_source_map_url(&relative_path(
            &directory_path(generated_file),
            &logical_map,
        ))
    }

    fn logical_source_map_path(&self, map_file: &str) -> Option<String> {
        let map_root = self.options.map_root.as_deref()?;
        let map_root = if is_absolute(map_root) {
            ts_path::normalize_path(map_root)
        } else {
            resolve_path(&self.current_directory, &[map_root])
        };
        let relative_map = self
            .options
            .out_dir
            .as_deref()
            .and_then(|out_dir| strip_directory_prefix(map_file, out_dir))
            .unwrap_or_else(|| map_file.rsplit('/').next().unwrap_or(map_file).to_owned());
        Some(resolve_path(&map_root, &[&relative_map]))
    }

    fn rewrite_bundle_declaration_specifiers(
        &self,
        source: &SourceFile,
        declaration: &str,
        bundle_root: &str,
        module: ModuleKind,
    ) -> String {
        let containing = canonicalize(
            &source.file_name,
            &self.current_directory,
            self.case_sensitivity,
        );
        self.resolved_modules
            .iter()
            .filter(|(key, _)| key.containing_file == containing)
            .filter_map(|(key, target)| {
                let target = self
                    .file_index
                    .get(target)
                    .and_then(|index| self.source_files.get(*index))?;
                if ts_path::is_declaration_file(&target.file_name)
                    || !self.source_should_emit(target)
                {
                    return None;
                }
                Some((
                    &key.specifier,
                    bundle_declaration_module_name(target, bundle_root, module),
                ))
            })
            .fold(
                declaration.to_owned(),
                |declaration, (specifier, target)| {
                    declaration
                        .replace(&format!("\"{specifier}\""), &format!("\"{target}\""))
                        .replace(&format!("'{specifier}'"), &format!("\"{target}\""))
                },
            )
    }

    fn prefer_bundle_declaration_imports(
        &self,
        source: &SourceFile,
        declaration: &str,
        bundle_root: &str,
        module: ModuleKind,
    ) -> String {
        let Some(NodeData::SourceFile(file)) = source
            .parse
            .arena
            .get(source.parse.source_file)
            .map(|node| &node.data)
        else {
            return declaration.to_owned();
        };
        let containing = canonicalize(
            &source.file_name,
            &self.current_directory,
            self.case_sensitivity,
        );
        let mut declaration = declaration.to_owned();
        let mut imports = Vec::new();
        for statement in &file.statements.nodes {
            let Some(NodeData::ImportDeclaration(import)) =
                source.parse.arena.get(*statement).map(|node| &node.data)
            else {
                continue;
            };
            let Some((_, specifier, requested_mode)) =
                source.parse.arena.get(*statement).and_then(|node| {
                    canonical_static_module_specifier(source, node)
                        .ok()
                        .flatten()
                })
            else {
                continue;
            };
            let Some(target) = self
                .resolved_modules
                .get(&ResolvedModuleKey::new(
                    containing.clone(),
                    specifier,
                    requested_mode.unwrap_or_else(|| self.canonical_emit_module_mode(source)),
                ))
                .and_then(|target| self.file_index.get(target))
                .and_then(|index| self.source_files.get(*index))
            else {
                continue;
            };
            let target = bundle_declaration_module_name(target, bundle_root, module);
            let Some(NodeData::ImportClause(clause)) = import
                .import_clause
                .and_then(|clause| source.parse.arena.get(clause))
                .map(|node| &node.data)
            else {
                continue;
            };
            if let Some(local) = clause
                .name
                .and_then(|name| identifier_text(&source.parse.arena, name))
                && replace_import_type_reference(&mut declaration, &target, "default", local)
            {
                imports.push(format!("import {local} from \"{target}\";"));
            }
            let Some(NodeData::NamedImports(named)) = clause
                .named_bindings
                .and_then(|bindings| source.parse.arena.get(bindings))
                .map(|node| &node.data)
            else {
                continue;
            };
            let mut retained = Vec::new();
            for element in &named.elements.nodes {
                let Some(NodeData::ImportSpecifier(import)) =
                    source.parse.arena.get(*element).map(|node| &node.data)
                else {
                    continue;
                };
                let Some(local) = identifier_text(&source.parse.arena, import.name) else {
                    continue;
                };
                let imported = import
                    .property_name
                    .and_then(|name| identifier_text(&source.parse.arena, name))
                    .unwrap_or(local);
                if replace_import_type_reference(&mut declaration, &target, imported, local) {
                    retained.push(if imported == local {
                        local.to_owned()
                    } else {
                        format!("{imported} as {local}")
                    });
                }
            }
            if !retained.is_empty() {
                imports.push(format!(
                    "import {{ {} }} from \"{target}\";",
                    retained.join(", ")
                ));
            }
        }
        if imports.is_empty() {
            declaration
        } else {
            imports.sort();
            imports.dedup();
            format!("{}\n{declaration}", imports.join("\n"))
        }
    }

    fn rewrite_late_bundle_export_references(
        &self,
        source: &SourceFile,
        declaration: &str,
        bundle_root: &str,
        module: ModuleKind,
    ) -> String {
        let source_module = bundle_declaration_module_name(source, bundle_root, module);
        let source_directory = source_module
            .rsplit_once('/')
            .map_or("", |(directory, _)| directory);
        source
            .checking
            .import_type_references
            .values()
            .filter(|reference| module_name_is_relative(&reference.module_specifier))
            .fold(declaration.to_owned(), |declaration, reference| {
                let resolved = resolve_path(
                    "/",
                    &[source_directory, reference.module_specifier.as_str()],
                );
                let resolved = resolved.trim_start_matches('/');
                let Some(target) = self.source_files.iter().find(|candidate| {
                    bundle_declaration_module_name(candidate, bundle_root, module) == resolved
                        && candidate
                            .binding
                            .exports
                            .get(&reference.qualifier)
                            .is_some()
                }) else {
                    return declaration;
                };
                let target_canonical = canonicalize(
                    &target.file_name,
                    &self.current_directory,
                    self.case_sensitivity,
                );
                let target_directory = directory_path(&target.file_name);
                let Some(barrel) = self.source_files.iter().find(|candidate| {
                    directory_path(&candidate.file_name) == target_directory
                        && ts_path::base_file_name(ts_path::remove_file_extension(
                            &candidate.file_name,
                        )) == "index"
                        && self.source_reexports_target(candidate, &target_canonical)
                }) else {
                    return declaration;
                };
                let barrel = bundle_declaration_module_name(barrel, bundle_root, module);
                let preferred = barrel.strip_suffix("/index").unwrap_or(&barrel);
                if preferred.is_empty() {
                    return declaration;
                }
                declaration.replace(
                    &format!(
                        "import(\"{}\").{}",
                        reference.module_specifier, reference.qualifier
                    ),
                    &format!("import(\"{preferred}\").{}", reference.qualifier),
                )
            })
    }

    fn source_reexports_target(&self, source: &SourceFile, target: &str) -> bool {
        let containing = canonicalize(
            &source.file_name,
            &self.current_directory,
            self.case_sensitivity,
        );
        self.resolved_modules.iter().any(|(key, resolved)| {
            key.containing_file == containing
                && resolved == target
                && source.parse.arena.iter().any(|(_, node)| {
                    matches!(
                        &node.data,
                        NodeData::ExportDeclaration(export)
                            if export.export_clause.is_none()
                                && canonical_static_module_specifier(source, node)
                                    .ok()
                                    .flatten()
                                    .is_some_and(|(_, specifier, requested_mode)| {
                                        *key == ResolvedModuleKey::new(
                                            containing.clone(),
                                            specifier,
                                            requested_mode.unwrap_or_else(|| {
                                                self.canonical_emit_module_mode(source)
                                            }),
                                        )
                                    })
                    )
                })
        })
    }

    fn canonical_module_resolution_manifest(
        &self,
    ) -> Result<CanonicalModuleResolutionManifestInput, CanonicalProgramCheckError> {
        let mut entries = Vec::new();
        let mut ambient_modules = BTreeMap::new();
        for source in &self.source_files {
            register_ambient_external_modules(
                source,
                &self.options,
                &self.current_directory,
                self.case_sensitivity,
                &mut ambient_modules,
            );
        }
        for source in &self.source_files {
            let specifiers = canonical_static_module_specifiers(source, &self.options)?;
            if specifiers.is_empty() {
                continue;
            }
            self.require_supported_module_source(source)?;

            let containing = canonicalize(
                &source.file_name,
                &self.current_directory,
                self.case_sensitivity,
            );
            for (specifier, text, requested_mode) in specifiers {
                let usage_mode =
                    requested_mode.unwrap_or_else(|| self.canonical_emit_module_mode(source));
                let key = ResolvedModuleKey::new(containing.clone(), text, usage_mode);
                let ambient_target = ambient_modules.get(&key.specifier);
                let Some(resolved_file_name) =
                    ambient_target.or_else(|| self.resolved_modules.get(&key))
                else {
                    entries.push(CanonicalModuleResolutionEntry::unresolved(specifier));
                    continue;
                };
                let Some(target) = self
                    .file_index
                    .get(resolved_file_name)
                    .and_then(|index| self.source_files.get(*index))
                else {
                    // Roots and other routes can admit a target that this edge omits.
                    // A missing index for a retained source remains an invariant failure.
                    let admitted = self.source_files.iter().any(|target| {
                        canonicalize(
                            &target.file_name,
                            &self.current_directory,
                            self.case_sensitivity,
                        ) == *resolved_file_name
                    });
                    if !admitted
                        && ambient_target.is_none()
                        && let Some((owner, dependency)) = self.resolved_module_loads.get(&key)
                        && *owner == source.id
                        && canonicalize(
                            &dependency.file_name,
                            &self.current_directory,
                            self.case_sensitivity,
                        ) == *resolved_file_name
                        && let Some(reason) = self.source_load_omission(source.id, dependency)
                    {
                        return Err(CanonicalProgramCheckError::OmittedModuleTargetUnsupported {
                            specifier,
                            target_file_name: resolved_file_name.clone(),
                            reason,
                        });
                    }
                    return Err(CanonicalProgramCheckError::MissingResolvedModuleTarget {
                        containing_file: source.file_name.clone(),
                        specifier,
                        resolved_file_name: resolved_file_name.clone(),
                    });
                };
                self.require_supported_module_source(target)?;
                if !canonical_source_file_facts(target, &self.options)?
                    .is_external_or_common_js_module()
                    && ts_checker::semantic::module_resolution::ambient_module_declaration(
                        &target.parse.arena,
                        &key.specifier,
                    )
                    .is_none()
                {
                    return Err(
                        CanonicalProgramCheckError::ExternalModuleTargetUnsupported {
                            specifier,
                            target_file_name: target.file_name.clone(),
                        },
                    );
                }
                entries.push(CanonicalModuleResolutionEntry::resolved(
                    specifier,
                    CanonicalResolvedModuleInput::new(
                        target.id,
                        usage_mode,
                        self.canonical_emit_module_mode(target),
                    ),
                ));
            }
        }
        Ok(CanonicalModuleResolutionManifestInput::new(entries))
    }

    fn require_supported_module_source(
        &self,
        source: &SourceFile,
    ) -> Result<(), CanonicalProgramCheckError> {
        let source_kind = ts_path::script_kind_from_path(&source.file_name);
        let supported_source = (matches!(
            source_kind,
            ts_path::ScriptKind::Ts | ts_path::ScriptKind::Tsx
        ) || (self.allows_javascript_sources()
            && matches!(
                source_kind,
                ts_path::ScriptKind::Js | ts_path::ScriptKind::Jsx
            )))
            && Path::new(&source.file_name)
                .extension()
                .and_then(|extension| extension.to_str())
                .is_some_and(|extension| {
                    ["ts", "tsx", "js", "jsx", "mts", "cts", "mjs", "cjs"]
                        .iter()
                        .any(|candidate| extension.eq_ignore_ascii_case(candidate))
                });
        if supported_source {
            return Ok(());
        }
        Err(
            CanonicalProgramCheckError::PlainEsmModuleResolutionUnsupported {
                file_name: source.file_name.clone(),
                module: self.options.module,
                module_resolution: self.options.module_resolution,
            },
        )
    }

    fn canonical_emit_module_mode(&self, source: &SourceFile) -> CanonicalModuleResolutionMode {
        if is_javascript_file_name(&source.file_name)
            && source_file_has_commonjs_indicator(&source.parse)
        {
            return CanonicalModuleResolutionMode::CommonJs;
        }
        let extension = Path::new(&source.file_name)
            .extension()
            .and_then(|extension| extension.to_str());
        if extension.is_some_and(|extension| {
            extension.eq_ignore_ascii_case("mts") || extension.eq_ignore_ascii_case("mjs")
        }) {
            return CanonicalModuleResolutionMode::Esm;
        }
        if extension.is_some_and(|extension| {
            extension.eq_ignore_ascii_case("cts") || extension.eq_ignore_ascii_case("cjs")
        }) {
            return CanonicalModuleResolutionMode::CommonJs;
        }

        match self.options.module {
            ModuleKind::CommonJs | ModuleKind::Amd | ModuleKind::Umd | ModuleKind::System => {
                CanonicalModuleResolutionMode::CommonJs
            }
            ModuleKind::Node16 | ModuleKind::Node18 | ModuleKind::Node20 | ModuleKind::NodeNext => {
                if source.implied_node_format == ModuleKind::CommonJs {
                    CanonicalModuleResolutionMode::CommonJs
                } else {
                    CanonicalModuleResolutionMode::Esm
                }
            }
            ModuleKind::None if self.options.module_specified => {
                CanonicalModuleResolutionMode::CommonJs
            }
            ModuleKind::None
            | ModuleKind::Es2015
            | ModuleKind::Es2020
            | ModuleKind::Es2022
            | ModuleKind::EsNext
            | ModuleKind::Preserve => CanonicalModuleResolutionMode::Esm,
        }
    }

    fn canonical_semantic_sources(&self) -> Vec<&SourceFile> {
        let mut sources = self
            .source_files
            .iter()
            .filter(|source| source.is_default_library)
            .collect::<Vec<_>>();
        // Sort after graph loading so explicit roots and later reference-lib
        // dependencies share one priority order without changing file identities.
        sources.sort_by_key(|source| {
            ts_bundled::library_priority(ts_path::base_file_name(&source.file_name))
        });

        let mut visited = vec![false; self.source_files.len()];
        for source in &sources {
            visited[source.id.index()] = true;
        }
        // Ordinary storage starts with explicit roots and automatic type roots.
        // Mark before walking dependencies so shared imports and cycles stop.
        let mut pending = Vec::new();
        for root in &self.source_files {
            pending.push((root.id, false));
            while let Some((file, complete)) = pending.pop() {
                if complete {
                    sources.push(&self.source_files[file.index()]);
                    continue;
                }
                if std::mem::replace(&mut visited[file.index()], true) {
                    continue;
                }
                pending.push((file, true));
                if let Some(dependencies) = self.source_dependencies.get(&file) {
                    pending.extend(
                        dependencies
                            .iter()
                            .rev()
                            .map(|(_, target)| (*target, false)),
                    );
                }
            }
        }
        sources
    }

    #[allow(clippy::too_many_lines)]
    fn check_program_canonical<T>(
        &self,
        queries: impl FnOnce(&Self, &mut CanonicalProgramQueries<'_>) -> T,
    ) -> Result<(Vec<ProgramDiagnostic>, T), CanonicalProgramCheckError> {
        let mut binder = CanonicalBinder::new();
        let sources = self.canonical_semantic_sources();
        let source_facts = sources
            .iter()
            .map(|source| canonical_source_file_facts(source, &self.options))
            .collect::<Result<Vec<_>, _>>()?;

        for (source, facts) in sources.iter().zip(source_facts) {
            binder
                .bind_source_file_with_facts(
                    &source.parse.arena,
                    source.parse.source_file,
                    source.id,
                    facts,
                )
                .map_err(|error| CanonicalProgramCheckError::Bind {
                    file_name: source.file_name.clone(),
                    error,
                })?;
        }

        for source in &sources {
            let result = if is_javascript_file_name(&source.file_name) {
                binder.bind_javascript_declaration_slice(&source.parse.arena, source.id)
            } else {
                binder.bind_typescript_declaration_slice(&source.parse.arena, source.id)
            };
            result.map_err(|error| CanonicalProgramCheckError::DeclarationBind {
                file_name: source.file_name.clone(),
                error,
            })?;
        }

        let mut bind_diagnostics = Vec::new();
        for source in &sources {
            // Keep declaration files bound so their symbols remain available
            // to importers, but mirror pinned SkipTypeChecking by suppressing
            // their bind diagnostics together with checker diagnostics.
            if self.options.skip_lib_check && ts_path::is_declaration_file(&source.file_name)
                || source_check_js_directive(&source.source_text) == Some(false)
            {
                continue;
            }
            let bound = binder.file(source.id).ok_or_else(|| {
                CanonicalProgramCheckError::MissingBoundFile {
                    file_name: source.file_name.clone(),
                    file: source.id,
                }
            })?;
            for diagnostic in bound.diagnostics() {
                bind_diagnostics.push(
                    self.canonical_program_diagnostic(
                        Some(diagnostic.node),
                        None,
                        &diagnostic.diagnostic,
                        diagnostic
                            .related_information
                            .iter()
                            .map(|related| (Some(related.node), &related.diagnostic)),
                    )?,
                );
            }
            self.add_top_level_await_identifier_diagnostics(source, bound, &mut bind_diagnostics)?;
            if bound
                .source_facts()
                .is_some_and(CanonicalSourceFileFacts::is_external_or_common_js_module)
            {
                bind_diagnostics.extend(self.canonical_commonjs_object_collisions(source)?);
            }
        }

        let ordered_arenas = sources
            .iter()
            .map(|source| (source.id, &source.parse.arena))
            .collect();
        let check_files = sources
            .iter()
            .filter(|source| !source.is_default_library)
            .map(|source| {
                (
                    source.id,
                    source.file_name.clone(),
                    ts_path::is_declaration_file(&source.file_name),
                    is_javascript_file_name(&source.file_name),
                )
            })
            .collect::<Vec<_>>();
        let options = self.canonical_checker_options();
        let module_resolutions = self.canonical_module_resolution_manifest()?;
        let mut context = CanonicalCheckerContext::new_with_module_resolutions(
            binder.finish(),
            ordered_arenas,
            options,
            module_resolutions,
        )
        .map_err(CanonicalProgramCheckError::Context)?;

        let mut checked_sources = Vec::new();
        for (file, file_name, is_declaration_file, is_javascript_file) in check_files {
            if is_declaration_file && self.options.skip_lib_check {
                continue;
            }
            let source = self.source_file_by_id(file).ok_or_else(|| {
                CanonicalProgramCheckError::MissingBoundFile {
                    file_name: file_name.clone(),
                    file,
                }
            })?;
            let check_directive = source_check_js_directive(&source.source_text);
            if check_directive == Some(false)
                || is_javascript_file && !check_directive.unwrap_or(self.options.check_js)
            {
                continue;
            }
            let runtime_pragma = source_jsx_pragma_value(&source.source_text, "@jsxRuntime");
            let runtime_module = self.options.jsx_runtime_module_specifier_for_source(
                runtime_pragma,
                source_jsx_pragma_value(&source.source_text, "@jsxImportSource"),
            );
            let runtime = if let Some(module_specifier) = runtime_module.as_deref() {
                let containing = canonicalize(
                    &source.file_name,
                    &self.current_directory,
                    self.case_sensitivity,
                );
                let resolved_module = self
                    .resolved_modules
                    .get(&ResolvedModuleKey::new(
                        containing,
                        module_specifier.to_owned(),
                        CanonicalModuleResolutionMode::Esm,
                    ))
                    .and_then(|target| self.file_index.get(target))
                    .and_then(|index| self.source_files.get(*index))
                    .and_then(|target| context.file(target.id))
                    .and_then(|(_, bound)| bound.symbol(bound.source_file()));
                CanonicalJsxRuntimeEvidence::Automatic {
                    module_specifier,
                    resolved_module,
                }
            } else if runtime_pragma == Some("classic")
                || self.options.jsx == ts_options::JsxEmit::React
            {
                let factory_pragma = source_jsx_pragma_value(&source.source_text, "@jsx ");
                let fragment_factory_pragma =
                    source_jsx_pragma_value(&source.source_text, "@jsxFrag")
                        .or_else(|| source_jsx_pragma_value(&source.source_text, "@jsxfrag"));
                CanonicalJsxRuntimeEvidence::Classic {
                    factory_namespace: self.options.jsx_factory_namespace_for_source(
                        factory_pragma,
                        fragment_factory_pragma,
                        false,
                    ),
                    fragment_factory_namespace: self.options.jsx_factory_namespace_for_source(
                        factory_pragma,
                        fragment_factory_pragma,
                        true,
                    ),
                    fragment_factory_required: self.options.jsx_factory.is_some()
                        && self.options.jsx_fragment_factory.is_none()
                        && fragment_factory_pragma.is_none(),
                    fragment_factory_pragma_required: factory_pragma.is_some()
                        && self.options.jsx_fragment_factory.is_none()
                        && fragment_factory_pragma.is_none(),
                }
            } else {
                CanonicalJsxRuntimeEvidence::Preserve
            };
            context
                .check_source_file_with_jsx_runtime(file, runtime)
                .map_err(|error| CanonicalProgramCheckError::SourceCheck { file_name, error })?;
            checked_sources.push(CanonicalCheckedSource {
                source,
                runtime: runtime.into(),
            });
        }

        let diagnostics =
            self.canonical_checker_diagnostics(&mut context, &bind_diagnostics, &checked_sources)?;
        let cold_diagnostics = self.canonical_diagnostic_snapshot(&diagnostics);
        for ((enclosing, target), specifier) in &self.package_display_specifiers {
            if let Some(source) = self
                .source_file(target)
                .filter(|source| source_is_external_module(source))
                && let Some(enclosing) = self.source_file_by_id(*enclosing)
            {
                context
                    .set_module_display_specifier(
                        NodeRef::new(
                            enclosing.parse.arena.id(),
                            enclosing.id,
                            enclosing.parse.source_file,
                        ),
                        NodeRef::new(source.parse.arena.id(), source.id, source.parse.source_file),
                        specifier.clone(),
                    )
                    .map_err(|error| CanonicalProgramCheckError::SourceCheck {
                        file_name: source.file_name.clone(),
                        error: SourceCheckError::TypeDisplayUnavailable(
                            TypeDisplayUnavailable::SymbolDisplay(error),
                        ),
                    })?;
            }
        }
        let mut canonical_queries = CanonicalProgramQueries {
            context,
            program: self,
            checked_sources,
            bind_diagnostics,
            has_diagnostics: !cold_diagnostics.is_empty(),
            cold_diagnostics,
        };
        let result = queries(self, &mut canonical_queries);
        Ok((diagnostics, result))
    }

    fn canonical_checker_options(&self) -> CanonicalCheckerOptions {
        CanonicalCheckerOptions {
            intrinsic: IntrinsicBootstrapOptions {
                strict_null_checks: self.options.strict_null_checks,
                exact_optional_property_types: self.options.exact_optional_property_types,
            },
            strict_bind_call_apply: self.options.strict_bind_call_apply,
            strict_builtin_iterator_return: self.options.strict_builtin_iterator_return,
            strict_function_types: self.options.strict_function_types,
            strict_property_initialization: self.options.strict_property_initialization,
            use_unknown_in_catch_variables: if self.options.use_unknown_in_catch_variables_specified
            {
                self.options.use_unknown_in_catch_variables
            } else {
                self.options.strict
            },
            no_implicit_any: self.options.no_implicit_any,
            no_implicit_this: if self.options.no_implicit_this_specified {
                self.options.no_implicit_this
            } else {
                self.options.strict
            },
            no_unchecked_indexed_access: self.options.no_unchecked_indexed_access,
            no_unused_locals: self.options.no_unused_locals,
            no_unused_parameters: self.options.no_unused_parameters,
            allow_unreachable_code: self.options.allow_unreachable_code,
            preserve_const_enums: self.options.preserve_const_enums,
            isolated_modules: self.options.isolated_modules,
            jsx_runtime: if self.options.jsx_runtime_module_specifier().is_some() {
                CanonicalJsxRuntime::Automatic
            } else if self.options.jsx == ts_options::JsxEmit::React {
                CanonicalJsxRuntime::Classic
            } else {
                CanonicalJsxRuntime::Preserve
            },
            emit_common_js: self.options.module == ModuleKind::CommonJs,
            import_call_mode: match self
                .options
                .module
                .effective_for_target(self.options.target)
            {
                ModuleKind::EsNext | ModuleKind::Preserve => {
                    ts_checker::semantic::CanonicalImportCallMode::Deferred
                }
                ModuleKind::Es2015 => ts_checker::semantic::CanonicalImportCallMode::Unsupported,
                ModuleKind::Node16
                | ModuleKind::Node18
                | ModuleKind::Node20
                | ModuleKind::NodeNext => {
                    ts_checker::semantic::CanonicalImportCallMode::DynamicWithAttributes
                }
                _ => ts_checker::semantic::CanonicalImportCallMode::Dynamic,
            },
            no_emit: self.options.no_emit,
            uses_wildcard_types: self
                .options
                .types
                .as_ref()
                .is_some_and(|types| types.iter().any(|name| name == "*")),
            no_error_truncation: self.options.no_error_truncation,
            check_bigint_target: true,
            name_resolution: (&self.options).into(),
        }
    }

    fn canonical_checker_diagnostics(
        &self,
        context: &mut CanonicalCheckerContext<'_>,
        bind_diagnostics: &[ProgramDiagnostic],
        checked_sources: &[CanonicalCheckedSource<'_>],
    ) -> Result<Vec<ProgramDiagnostic>, CanonicalProgramCheckError> {
        let mut diagnostics = bind_diagnostics.to_vec();
        let checked_files = checked_sources
            .iter()
            .map(|checked| checked.source.id)
            .collect::<Vec<_>>();
        for checked in checked_sources {
            self.add_missing_jsx_option_diagnostics(checked.source, &mut diagnostics);
            self.add_erasable_import_assignment_diagnostics(checked.source, &mut diagnostics);
            self.add_strict_reserved_identifier_diagnostics(checked.source, &mut diagnostics)?;
            self.add_checked_javascript_parameter_decorator_diagnostics(
                checked.source,
                &mut diagnostics,
            )?;
            self.add_regular_expression_quantifier_diagnostics(
                checked.source,
                context,
                &mut diagnostics,
            )?;
            self.add_external_helper_diagnostics(checked.source, context, &mut diagnostics)?;
            self.add_canonical_module_target_diagnostics(
                checked.source,
                context,
                &mut diagnostics,
            )?;
        }

        // Program.GetGlobalDiagnostics skips checker diagnostics without source files.
        if !self.source_files.is_empty() {
            for diagnostic in context.global_types().diagnostics() {
                diagnostics.push(self.canonical_program_diagnostic(
                    diagnostic.node,
                    None,
                    &diagnostic.diagnostic,
                    std::iter::empty(),
                )?);
            }
        }
        for diagnostic in context.diagnostics().as_slice() {
            diagnostics.push(
                self.canonical_program_diagnostic(
                    diagnostic.node,
                    diagnostic.range_override,
                    &diagnostic.diagnostic,
                    diagnostic
                        .related_information
                        .iter()
                        .map(|related| (related.node, &related.diagnostic)),
                )?,
            );
        }
        if self.options.isolated_declarations
            && (self.options.declaration || self.options.composite)
        {
            for source in &self.source_files {
                if checked_files.contains(&source.id) {
                    self.add_isolated_declaration_function_diagnostics(source, &mut diagnostics)?;
                }
            }
        }

        diagnostics.extend(
            self.module_resolution_diagnostics
                .iter()
                .filter(|diagnostic| {
                    diagnostic
                        .file_name
                        .as_deref()
                        .and_then(|file_name| self.source_file(file_name))
                        .is_some_and(|source| checked_files.contains(&source.id))
                })
                .cloned(),
        );
        self.apply_comment_directives(&mut diagnostics, &checked_files);
        Ok(diagnostics)
    }

    fn add_strict_reserved_identifier_diagnostics(
        &self,
        source: &SourceFile,
        diagnostics: &mut Vec<ProgramDiagnostic>,
    ) -> Result<(), CanonicalProgramCheckError> {
        const JSDOC_OR_REPARSED: u32 = (1 << 22) | NodeFlags::REPARSED.0;
        if self.options.no_check
            || !source.parse.diagnostics.is_empty()
            || ts_path::is_declaration_file(&source.file_name)
            || canonical_source_file_facts(source, &self.options)?.is_external_module()
        {
            return Ok(());
        }
        let arena = &source.parse.arena;
        let mut pending = vec![source.parse.source_file];
        while let Some(id) = pending.pop() {
            let Some(node) = arena.get(id) else {
                continue;
            };
            if node.flags.0 & JSDOC_OR_REPARSED != 0
                || matches!(
                    node.data,
                    NodeData::ClassDeclaration(_) | NodeData::ClassExpression(_)
                )
            {
                continue;
            }
            node.for_each_child(|child| pending.push(child));
            let NodeData::Identifier(identifier) = &node.data else {
                continue;
            };
            // The pinned binder checks these names even when alwaysStrict is disabled.
            let keyword = ts_scanner::Scanner::new(&identifier.text).scan().kind as u16;
            if !(SyntaxKind::FIRST_FUTURE_RESERVED_WORD as u16
                ..=SyntaxKind::LAST_FUTURE_RESERVED_WORD as u16)
                .contains(&keyword)
                || strict_reserved_identifier_is_name(arena, id)
                || private_helper_access_is_ambient(arena, id)
            {
                continue;
            }
            let reference = NodeRef::new(arena.id(), source.id, id);
            let spelling = source
                .source_text
                .get(node.range.start.get() as usize..node.range.end.get() as usize)
                .ok_or(CanonicalProgramCheckError::InvalidDiagnosticNode(reference))?;
            let diagnostic = Diagnostic::with_arguments(
                message_by_code(1212).expect("TS1212 must be in the diagnostic catalog"),
                [spelling],
            );
            diagnostics.push(self.canonical_program_diagnostic(
                Some(reference),
                None,
                &diagnostic,
                std::iter::empty(),
            )?);
        }
        Ok(())
    }

    fn add_checked_javascript_parameter_decorator_diagnostics(
        &self,
        source: &SourceFile,
        diagnostics: &mut Vec<ProgramDiagnostic>,
    ) -> Result<(), CanonicalProgramCheckError> {
        const JSDOC_OR_REPARSED: u32 = (1 << 22) | NodeFlags::REPARSED.0;
        if self.options.no_check
            || self.options.experimental_decorators
            || !is_javascript_file_name(&source.file_name)
        {
            return Ok(());
        }
        let arena = &source.parse.arena;
        let mut pending = vec![source.parse.source_file];
        while let Some(node) = pending.pop() {
            let Some(node) = arena.get(node) else {
                continue;
            };
            if node.flags.0 & JSDOC_OR_REPARSED != 0 {
                continue;
            }
            node.for_each_child(|child| pending.push(child));
            let NodeData::ParameterDeclaration(parameter) = &node.data else {
                continue;
            };
            let Some((decorator, record)) = parameter.modifiers.as_ref().and_then(|modifiers| {
                modifiers.list.nodes.iter().find_map(|decorator| {
                    arena
                        .get(*decorator)
                        .filter(|record| {
                            record.kind == SyntaxKind::Decorator
                                && record.flags.0 & JSDOC_OR_REPARSED == 0
                        })
                        .map(|record| (*decorator, record))
                })
            }) else {
                continue;
            };
            let range = TextRange::new(
                record.range.start,
                TextPos::new(record.range.start.get() + 1),
            );
            let decorator = NodeRef::new(arena.id(), source.id, decorator);
            let diagnostic = Diagnostic::new(
                message_by_code(1206).expect("TS1206 must be in the diagnostic catalog"),
            );
            diagnostics.push(self.canonical_program_diagnostic(
                Some(decorator),
                Some(CanonicalCheckerDiagnosticRange::new(decorator, range)),
                &diagnostic,
                std::iter::empty(),
            )?);
        }
        Ok(())
    }

    fn add_canonical_module_target_diagnostics(
        &self,
        source: &SourceFile,
        context: &CanonicalCheckerContext<'_>,
        diagnostics: &mut Vec<ProgramDiagnostic>,
    ) -> Result<(), CanonicalProgramCheckError> {
        let source_ref = NodeRef::new(source.parse.arena.id(), source.id, source.parse.source_file);
        let (_, bound) =
            context
                .file(source.id)
                .ok_or(CanonicalProgramCheckError::InvalidModuleSourceFile(
                    source_ref,
                ))?;
        for (specifier, text, _) in canonical_static_module_specifiers(source, &self.options)? {
            let Some(augmentation) = bound
                .module_augmentations()
                .iter()
                .find(|augmentation| augmentation.name() == specifier)
            else {
                continue;
            };
            if augmentation.in_ambient_context() {
                continue;
            }
            let declaration = self
                .node(specifier)
                .and_then(|node| node.parent)
                .map(|node| NodeRef::new(specifier.arena, specifier.file, node))
                .ok_or(CanonicalProgramCheckError::InvalidModuleSpecifier(
                    specifier,
                ))?;
            let first_declaration = bound
                .symbol(declaration)
                .and_then(|symbol| context.store().symbol(symbol))
                .and_then(|symbol| symbol.declarations())
                .and_then(|declarations| declarations.first())
                .ok_or(CanonicalProgramCheckError::InvalidModuleSpecifier(
                    specifier,
                ))?;
            if *first_declaration != declaration {
                continue;
            }
            let diagnostic = match context.module_resolution(specifier) {
                CanonicalModuleResolutionLookup::Unresolved => Diagnostic::with_arguments(
                    message_by_code(2664).expect("TS2664 must be in the generated catalog"),
                    [text],
                ),
                CanonicalModuleResolutionLookup::Resolved(_) => continue,
                CanonicalModuleResolutionLookup::Unavailable
                | CanonicalModuleResolutionLookup::EntryAbsent => {
                    return Err(CanonicalProgramCheckError::InvalidModuleSpecifier(
                        specifier,
                    ));
                }
            };
            diagnostics.push(self.canonical_program_diagnostic(
                Some(specifier),
                None,
                &diagnostic,
                std::iter::empty(),
            )?);
        }
        Ok(())
    }

    fn canonical_diagnostic_snapshot(
        &self,
        checker_diagnostics: &[ProgramDiagnostic],
    ) -> Vec<ProgramDiagnostic> {
        let mut diagnostics = self
            .diagnostics
            .iter()
            .chain(checker_diagnostics)
            .cloned()
            .collect::<Vec<_>>();
        diagnostics.sort_by(compare_program_diagnostics);
        diagnostics
    }

    fn add_isolated_declaration_function_diagnostics(
        &self,
        source: &SourceFile,
        diagnostics: &mut Vec<ProgramDiagnostic>,
    ) -> Result<(), CanonicalProgramCheckError> {
        if ts_path::is_declaration_file(&source.file_name)
            || is_javascript_file_name(&source.file_name)
        {
            return Ok(());
        }
        let Some(NodeData::SourceFile(file)) = source
            .parse
            .arena
            .get(source.parse.source_file)
            .map(|node| &node.data)
        else {
            return Ok(());
        };
        for statement in &file.statements.nodes {
            let Some(NodeData::FunctionDeclaration(function)) =
                source.parse.arena.get(*statement).map(|node| &node.data)
            else {
                continue;
            };
            if function.type_.is_some()
                || function.body.is_none()
                || !node_has_modifier(
                    &source.parse.arena,
                    function.modifiers.as_ref(),
                    SyntaxKind::ExportKeyword,
                )
            {
                continue;
            }
            let Some(name) = function.name.and_then(|name| source.node_ref(name)) else {
                continue;
            };
            let error = Diagnostic::new(
                message_by_code(9007).expect("TS9007 must be in the generated catalog"),
            );
            let suggestion = Diagnostic::new(
                message_by_code(9031).expect("TS9031 must be in the generated catalog"),
            );
            let diagnostic = self.canonical_program_diagnostic(
                Some(name),
                None,
                &error,
                [(Some(name), &suggestion)],
            )?;
            if !diagnostics.iter().any(|existing| {
                existing.code == diagnostic.code
                    && existing.file_name == diagnostic.file_name
                    && existing.range == diagnostic.range
            }) {
                diagnostics.push(diagnostic);
            }
        }
        Ok(())
    }

    fn canonical_external_helper_requirements(
        &self,
        source: &SourceFile,
    ) -> Vec<(NodeRef, &'static str)> {
        let mut requirements = self.canonical_commonjs_import_helpers(source);
        requirements.extend(self.canonical_private_helper_requirements(source));
        requirements.sort_by_key(|(node, _)| {
            source
                .parse
                .arena
                .get(node.node)
                .map(|node| node.range.start)
        });
        requirements
    }

    fn source_helper_module_state(&self, source: &SourceFile) -> CanonicalModuleState {
        source_file_module_state(
            &source.file_name,
            &source.parse,
            if is_javascript_file_name(&source.file_name) {
                CanonicalSourceLanguage::JavaScript
            } else {
                CanonicalSourceLanguage::TypeScript
            },
            ts_path::is_declaration_file(&source.file_name),
            source.implied_node_format,
            &self.options,
        )
    }

    fn source_needs_import_helpers(&self, source: &SourceFile) -> bool {
        self.options.import_helpers
            && (is_javascript_file_name(&source.file_name)
                || !ts_path::is_declaration_file(&source.file_name)
                    && (self.options.isolated_modules
                        || self.options.verbatim_module_syntax
                        || matches!(
                            self.source_helper_module_state(source),
                            CanonicalModuleState::External
                                | CanonicalModuleState::ExternalAndCommonJs
                        )))
    }

    fn canonical_private_helper_requirements(
        &self,
        source: &SourceFile,
    ) -> Vec<(NodeRef, &'static str)> {
        let effective_external_module = match self.source_helper_module_state(source) {
            CanonicalModuleState::External | CanonicalModuleState::ExternalAndCommonJs => true,
            CanonicalModuleState::CommonJs => matches!(
                self.options.module,
                ModuleKind::CommonJs
                    | ModuleKind::Node16
                    | ModuleKind::Node18
                    | ModuleKind::Node20
                    | ModuleKind::NodeNext
            ),
            CanonicalModuleState::Script => false,
        };
        if self.checker != ProgramChecker::Canonical
            || self.options.no_check
            || !self.options.import_helpers
            || source.is_default_library
            || ts_path::is_declaration_file(&source.file_name)
            || !effective_external_module
        {
            return Vec::new();
        }
        let use_define = self
            .options
            .use_define_for_class_fields
            .unwrap_or(self.options.target >= ScriptTarget::Es2022);
        if self.options.target >= ScriptTarget::EsNext && use_define {
            return Vec::new();
        }

        let arena = &source.parse.arena;
        let mut accesses = arena
            .iter()
            .filter_map(|(id, node)| {
                let NodeData::PropertyAccessExpression(access) = &node.data else {
                    return None;
                };
                (matches!(
                    arena.get(access.name).map(|name| &name.data),
                    Some(NodeData::PrivateIdentifier(_))
                ) && !private_helper_access_is_ambient(arena, id))
                .then_some((id, node.range))
            })
            .collect::<Vec<_>>();
        accesses.sort_by_key(|(_, range)| (range.start, range.end));

        let mut requirements = Vec::new();
        let mut requested = HashSet::new();
        for (access, _) in accesses {
            let Some(node) = source.node_ref(access) else {
                continue;
            };
            let assignment = private_helper_assignment_kind(arena, access);
            for (needed, helper) in [
                (
                    assignment != PrivateHelperAssignmentKind::None,
                    "__classPrivateFieldSet",
                ),
                (
                    assignment != PrivateHelperAssignmentKind::Definite,
                    "__classPrivateFieldGet",
                ),
            ] {
                if needed && requested.insert(helper) {
                    requirements.push((node, helper));
                }
            }
        }
        requirements
    }

    fn canonical_commonjs_import_helpers(
        &self,
        source: &SourceFile,
    ) -> Vec<(NodeRef, &'static str)> {
        if self.checker != ProgramChecker::Canonical
            || self.options.no_check
            || !self.options.import_helpers
            || !self.options.es_module_interop
            || self.options.no_emit
            || self.options.emit_declaration_only
            || self.options.module != ModuleKind::CommonJs
            || source.is_default_library
            || ts_path::is_declaration_file(&source.file_name)
            || !source_is_external_module(source)
        {
            return Vec::new();
        }

        let Some(NodeData::SourceFile(file)) = source
            .parse
            .arena
            .get(source.parse.source_file)
            .map(|node| &node.data)
        else {
            return Vec::new();
        };
        let runtime_uses = runtime_identifier_uses(&source.parse.arena, source.parse.source_file);
        let mut requirements = Vec::new();
        for statement in &file.statements.nodes {
            let Some(NodeData::ImportDeclaration(import)) =
                source.parse.arena.get(*statement).map(|node| &node.data)
            else {
                continue;
            };
            let Some(NodeData::ImportClause(clause)) = import
                .import_clause
                .and_then(|clause| source.parse.arena.get(clause))
                .map(|node| &node.data)
            else {
                continue;
            };
            if clause.phase_modifier == Some(SyntaxKind::TypeKeyword) {
                continue;
            }

            let namespace_used = clause
                .named_bindings
                .and_then(|bindings| source.parse.arena.get(bindings))
                .and_then(|node| match &node.data {
                    NodeData::NamespaceImport(namespace) => source.parse.arena.get(namespace.name),
                    _ => None,
                })
                .is_some_and(|node| {
                    matches!(
                        &node.data,
                        NodeData::Identifier(identifier)
                            if runtime_uses.contains(&identifier.text)
                    )
                });
            let default_used = clause
                .name
                .and_then(|name| source.parse.arena.get(name))
                .is_some_and(|node| {
                    matches!(
                        &node.data,
                        NodeData::Identifier(identifier)
                            if runtime_uses.contains(&identifier.text)
                    )
                });
            let helper = if namespace_used {
                "__importStar"
            } else if default_used {
                "__importDefault"
            } else {
                continue;
            };
            let Some(statement) = source.node_ref(*statement) else {
                continue;
            };
            requirements.push((statement, helper));
        }
        requirements
    }

    fn add_external_helper_diagnostics(
        &self,
        source: &SourceFile,
        context: &mut CanonicalCheckerContext<'_>,
        diagnostics: &mut Vec<ProgramDiagnostic>,
    ) -> Result<(), CanonicalProgramCheckError> {
        let requirements = self.canonical_external_helper_requirements(source);
        if requirements.is_empty() {
            return Ok(());
        }
        let has_private = requirements.iter().any(|(_, helper)| {
            matches!(*helper, "__classPrivateFieldGet" | "__classPrivateFieldSet")
        });
        let mut staged = Vec::new();

        let containing = canonicalize(
            &source.file_name,
            &self.current_directory,
            self.case_sensitivity,
        );
        let Some(target) = self
            .resolved_modules
            .get(&ResolvedModuleKey::new(
                containing,
                "tslib".to_owned(),
                self.canonical_emit_module_mode(source),
            ))
            .and_then(|file_name| self.source_file(file_name))
        else {
            let message = message_by_code(2354).expect("TS2354 must be in the diagnostic catalog");
            // Import-only sources retain their existing per-import diagnostics.
            let limit = if has_private { 1 } else { requirements.len() };
            for (statement, _) in requirements.into_iter().take(limit) {
                staged.push(self.canonical_program_diagnostic(
                    Some(statement),
                    None,
                    &Diagnostic::with_arguments(message, ["tslib"]),
                    std::iter::empty(),
                )?);
            }
            diagnostics.extend(staged);
            return Ok(());
        };
        let Some((_, bound)) = context.file(target.id) else {
            return Err(CanonicalProgramCheckError::MissingBoundFile {
                file_name: target.file_name.clone(),
                file: target.id,
            });
        };
        let Some(module) = bound.symbol(bound.source_file()) else {
            if has_private {
                if bound
                    .source_facts()
                    .is_none_or(CanonicalSourceFileFacts::is_external_or_common_js_module)
                {
                    return Err(CanonicalProgramCheckError::InvalidModuleSourceFile(
                        bound.source_file(),
                    ));
                }
                return Err(CanonicalProgramCheckError::ImportHelper {
                    file_name: source.file_name.clone(),
                    node: requirements[0].0,
                    error: Box::new(CanonicalImportHelperError::ModuleSymbolUnavailable {
                        file_name: target.file_name.clone(),
                    }),
                });
            }
            return Ok(());
        };
        let message = message_by_code(2343).expect("TS2343 must be in the diagnostic catalog");

        for (statement, helper) in requirements {
            let private = match helper {
                "__classPrivateFieldGet" => Some(PrivateImportHelper::Get),
                "__classPrivateFieldSet" => Some(PrivateImportHelper::Set),
                _ => None,
            };
            if let Some(private) = private {
                if let Some(diagnostic) = self
                    .private_import_helper_diagnostic(source, statement, private, module, context)?
                {
                    staged.push(diagnostic);
                }
                continue;
            }
            let available = context
                .store()
                .symbol(module)
                .and_then(ts_binder::semantic::Symbol::exports)
                .and_then(|exports| context.store().symbol_table(exports))
                .and_then(|exports| exports.get_source(helper))
                .and_then(|symbol| context.store().symbol(symbol))
                .is_some_and(|symbol| symbol.flags().intersects(SymbolFlags::VALUE));
            if available {
                continue;
            }
            staged.push(self.canonical_program_diagnostic(
                Some(statement),
                None,
                &Diagnostic::with_arguments(message, ["tslib", helper]),
                std::iter::empty(),
            )?);
        }
        diagnostics.extend(staged);
        Ok(())
    }

    fn private_import_helper_diagnostic(
        &self,
        source: &SourceFile,
        node: NodeRef,
        helper: PrivateImportHelper,
        module: CanonicalSymbolId,
        context: &mut CanonicalCheckerContext<'_>,
    ) -> Result<Option<ProgramDiagnostic>, CanonicalProgramCheckError> {
        let query_error = |error| CanonicalProgramCheckError::ImportHelper {
            file_name: source.file_name.clone(),
            node,
            error: Box::new(error),
        };
        let symbol = context
            .get_module_export_by_name(module, helper.name())
            .map_err(|error| query_error(CanonicalImportHelperError::Export(error)))?;
        let value = if let Some(mut symbol) = symbol {
            if context
                .store()
                .symbol(symbol)
                .is_some_and(|record| record.flags().intersects(SymbolFlags::ALIAS))
            {
                let resolution = context
                    .resolve_alias(symbol)
                    .map_err(|error| query_error(CanonicalImportHelperError::Alias(error)))?;
                let AliasTargetState::Resolved(target) = resolution.target else {
                    return Err(query_error(CanonicalImportHelperError::AliasUnresolved {
                        alias: symbol,
                        resolution,
                    }));
                };
                if !resolution.events.is_empty() {
                    return Err(query_error(CanonicalImportHelperError::AliasEvents {
                        symbol,
                        events: resolution.events,
                    }));
                }
                symbol = target;
            }
            let meanings = context
                .get_symbol_flags(symbol)
                .map_err(|error| query_error(CanonicalImportHelperError::Alias(error)))?;
            if !meanings.events.is_empty() {
                return Err(query_error(CanonicalImportHelperError::AliasEvents {
                    symbol,
                    events: meanings.events,
                }));
            }
            meanings
                .flags
                .intersects(SymbolFlags::VALUE)
                .then_some(symbol)
        } else {
            None
        };
        let diagnostic = if let Some(value) = value {
            if context
                .has_call_signature_with_arity_greater_than(value, helper.required_parameters() - 1)
                .map_err(|error| query_error(CanonicalImportHelperError::Signature(error)))?
            {
                return Ok(None);
            }
            Diagnostic::with_arguments(
                message_by_code(2807).expect("TS2807 must be in the diagnostic catalog"),
                [
                    "tslib".to_owned(),
                    helper.name().to_owned(),
                    helper.required_parameters().to_string(),
                ],
            )
        } else {
            Diagnostic::with_arguments(
                message_by_code(2343).expect("TS2343 must be in the diagnostic catalog"),
                ["tslib", helper.name()],
            )
        };
        self.canonical_program_diagnostic(Some(node), None, &diagnostic, std::iter::empty())
            .map(Some)
    }

    fn add_regular_expression_quantifier_diagnostics(
        &self,
        source: &SourceFile,
        context: &CanonicalCheckerContext<'_>,
        diagnostics: &mut Vec<ProgramDiagnostic>,
    ) -> Result<(), CanonicalProgramCheckError> {
        // Pinned checkGrammarRegularExpressionLiteral skips files with parse diagnostics.
        if !source.parse.diagnostics.is_empty() {
            return Ok(());
        }
        let (_, bound) = context.file(source.id).ok_or_else(|| {
            CanonicalProgramCheckError::MissingBoundFile {
                file_name: source.file_name.clone(),
                file: source.id,
            }
        })?;
        let root = NodeRef::new(source.parse.arena.id(), source.id, source.parse.source_file);
        if bound.source_file() != root {
            return Err(CanonicalProgramCheckError::InvalidDiagnosticNode(root));
        }
        let message = message_by_code(1_506).expect("TS1506 must be in the generated catalog");
        for (id, node) in source.parse.arena.iter() {
            let literal = NodeRef::new(source.parse.arena.id(), source.id, id);
            if node.kind != SyntaxKind::RegularExpressionLiteral || !bound.contains(literal) {
                continue;
            }
            if !source
                .source_text
                .is_char_boundary(node.range.start.get() as usize)
            {
                return Err(CanonicalProgramCheckError::InvalidDiagnosticNode(literal));
            }
            let mut scanner = Scanner::new(&source.source_text);
            scanner.reset_token_state(node.range.start.get() as usize);
            scanner.scan();
            let token = scanner.rescan_slash_token_with_quantifier_checks();
            if token.kind != SyntaxKind::RegularExpressionLiteral || token.range != node.range {
                return Err(CanonicalProgramCheckError::InvalidDiagnosticNode(literal));
            }
            for error in scanner.diagnostics() {
                if error.code != Some(message.code()) {
                    return Err(CanonicalProgramCheckError::InvalidDiagnosticNode(literal));
                }
                diagnostics.push(self.canonical_program_diagnostic(
                    Some(literal),
                    Some(CanonicalCheckerDiagnosticRange::new(literal, error.range)),
                    &Diagnostic::new(message),
                    std::iter::empty(),
                )?);
            }
        }
        Ok(())
    }

    fn add_missing_jsx_option_diagnostics(
        &self,
        source: &SourceFile,
        diagnostics: &mut Vec<ProgramDiagnostic>,
    ) {
        if self.options.jsx != ts_options::JsxEmit::None
            || ts_path::is_declaration_file(&source.file_name)
        {
            return;
        }

        let message = message_by_code(17004).expect("TS17004 must be in the generated catalog");
        diagnostics.extend(
            source
                .parse
                .arena
                .iter()
                .filter(|(_, node)| {
                    matches!(
                        node.data,
                        NodeData::JsxOpeningElement(_)
                            | NodeData::JsxSelfClosingElement(_)
                            | NodeData::JsxOpeningFragment(_)
                    )
                })
                .map(|(_, node)| ProgramDiagnostic {
                    file_name: Some(source.file_name.clone()),
                    range: Some(node.range),
                    code: Some(message.code()),
                    category: message.category(),
                    message: message.text().to_owned(),
                    related_information: Vec::new(),
                }),
        );
    }

    fn add_erasable_import_assignment_diagnostics(
        &self,
        source: &SourceFile,
        diagnostics: &mut Vec<ProgramDiagnostic>,
    ) {
        if !self.options.erasable_syntax_only
            || is_javascript_file_name(&source.file_name)
            || ts_path::is_declaration_file(&source.file_name)
        {
            return;
        }

        let Some(NodeData::SourceFile(file)) = source
            .parse
            .arena
            .get(source.parse.source_file)
            .map(|node| &node.data)
        else {
            return;
        };
        let emits_ecmascript_modules = matches!(
            self.options.module,
            ModuleKind::Es2015 | ModuleKind::Es2020 | ModuleKind::Es2022 | ModuleKind::EsNext
        ) || self.options.module == ModuleKind::None
            && !self.options.module_specified
            && self.options.target >= ScriptTarget::Es2015;

        for statement in &file.statements.nodes {
            let Some(node) = source.parse.arena.get(*statement) else {
                continue;
            };
            let NodeData::ImportEqualsDeclaration(import) = &node.data else {
                continue;
            };
            if import.is_type_only {
                continue;
            }
            let external_module_reference = source
                .parse
                .arena
                .get(import.module_reference)
                .is_some_and(|reference| {
                    matches!(reference.data, NodeData::ExternalModuleReference(_))
                });

            for code in [
                (emits_ecmascript_modules && external_module_reference).then_some(1202),
                Some(1294),
            ]
            .into_iter()
            .flatten()
            {
                let message = message_by_code(code)
                    .expect("import-assignment diagnostics must be in the generated catalog");
                diagnostics.push(ProgramDiagnostic {
                    file_name: Some(source.file_name.clone()),
                    range: Some(node.range),
                    code: Some(message.code()),
                    category: message.category(),
                    message: message.text().to_owned(),
                    related_information: Vec::new(),
                });
            }
        }
    }

    fn apply_comment_directives(
        &self,
        diagnostics: &mut Vec<ProgramDiagnostic>,
        checked_sources: &[FileId],
    ) {
        for file in checked_sources {
            let Some(source) = self.source_file_by_id(*file) else {
                continue;
            };
            let line_starts = source_line_starts(&source.source_text);
            let mut directives = source_comment_directives(&source.parse, &line_starts);
            if directives.is_empty() {
                continue;
            }
            diagnostics.retain(|diagnostic| {
                if diagnostic.file_name.as_deref() != Some(source.file_name.as_str()) {
                    return true;
                }
                let Some(position) = diagnostic
                    .range
                    .and_then(|range| usize::try_from(range.start.get()).ok())
                    .filter(|position| *position <= source.source_text.len())
                else {
                    return true;
                };
                let line = source_line_of_position(&line_starts, position);
                for previous in (0..line).rev() {
                    if let Some(directive) = directives.get_mut(&previous) {
                        directive.used = true;
                        return false;
                    }
                    let start = line_starts[previous];
                    let end = line_starts
                        .get(previous + 1)
                        .copied()
                        .unwrap_or(source.source_text.len());
                    if !source_line_is_comment_or_blank(&source.source_text[start..end]) {
                        break;
                    }
                }
                true
            });
            let Some(message) = message_by_code(2578) else {
                continue;
            };
            for directive in directives
                .into_values()
                .filter(|directive| directive.expect_error && !directive.used)
            {
                diagnostics.push(ProgramDiagnostic {
                    file_name: Some(source.file_name.clone()),
                    range: Some(directive.range),
                    code: Some(message.code()),
                    category: message.category(),
                    message: message.text().to_owned(),
                    related_information: Vec::new(),
                });
            }
        }
    }

    fn canonical_commonjs_object_collisions(
        &self,
        source: &SourceFile,
    ) -> Result<Vec<ProgramDiagnostic>, CanonicalProgramCheckError> {
        if self.options.module != ModuleKind::CommonJs
            || self.options.no_emit
            || ts_path::is_declaration_file(&source.file_name)
        {
            return Ok(Vec::new());
        }

        let Some(NodeData::SourceFile(file)) = source
            .parse
            .arena
            .get(source.parse.source_file)
            .map(|node| &node.data)
        else {
            return Ok(Vec::new());
        };
        let mut diagnostics = Vec::new();
        for statement in &file.statements.nodes {
            let Some(NodeData::VariableStatement(variable)) =
                source.parse.arena.get(*statement).map(|node| &node.data)
            else {
                continue;
            };
            if node_has_modifier(
                &source.parse.arena,
                variable.modifiers.as_ref(),
                SyntaxKind::DeclareKeyword,
            ) {
                continue;
            }
            let Some(NodeData::VariableDeclarationList(list)) = source
                .parse
                .arena
                .get(variable.declaration_list)
                .map(|node| &node.data)
            else {
                continue;
            };
            for declaration in &list.declarations.nodes {
                let Some(NodeData::VariableDeclaration(declaration)) =
                    source.parse.arena.get(*declaration).map(|node| &node.data)
                else {
                    continue;
                };
                let Some(NodeData::Identifier(identifier)) = source
                    .parse
                    .arena
                    .get(declaration.name)
                    .map(|node| &node.data)
                else {
                    continue;
                };
                if identifier.text != "Object" {
                    continue;
                }
                let name = source.node_ref(declaration.name).ok_or_else(|| {
                    CanonicalProgramCheckError::InvalidDiagnosticNode(NodeRef::new(
                        source.parse.arena.id(),
                        source.id,
                        declaration.name,
                    ))
                })?;
                let message =
                    message_by_code(2441).expect("TS2441 must be in the generated catalog");
                let diagnostic = Diagnostic::with_arguments(message, ["Object", "Object"]);
                diagnostics.push(self.canonical_program_diagnostic(
                    Some(name),
                    None,
                    &diagnostic,
                    std::iter::empty(),
                )?);
            }
        }
        Ok(diagnostics)
    }

    fn canonical_program_diagnostic<'diagnostic>(
        &self,
        node: Option<NodeRef>,
        range_override: Option<CanonicalCheckerDiagnosticRange>,
        diagnostic: &Diagnostic,
        related_information: impl IntoIterator<Item = (Option<NodeRef>, &'diagnostic Diagnostic)>,
    ) -> Result<ProgramDiagnostic, CanonicalProgramCheckError> {
        let mut result =
            self.canonical_program_diagnostic_record(node, range_override, diagnostic)?;
        let primary_code = diagnostic.code();
        result.related_information = related_information
            .into_iter()
            .enumerate()
            .map(|(index, (node, diagnostic))| {
                self.canonical_program_diagnostic_record(node, None, diagnostic)
                    .map_err(|error| match error {
                        CanonicalProgramCheckError::InvalidDiagnosticNode(node) => {
                            CanonicalProgramCheckError::InvalidRelatedDiagnosticNode {
                                primary_code,
                                index,
                                node,
                            }
                        }
                        error => error,
                    })
            })
            .collect::<Result<Vec<_>, _>>()?;
        Ok(result)
    }

    fn canonical_program_diagnostic_record(
        &self,
        node: Option<NodeRef>,
        range_override: Option<CanonicalCheckerDiagnosticRange>,
        diagnostic: &Diagnostic,
    ) -> Result<ProgramDiagnostic, CanonicalProgramCheckError> {
        let (file_name, range) = if let Some(node) = node {
            let anchor = self
                .node(node)
                .ok_or(CanonicalProgramCheckError::InvalidDiagnosticNode(node))?;
            let source = self
                .source_file_by_id(node.file)
                .ok_or(CanonicalProgramCheckError::InvalidDiagnosticNode(node))?;
            let source_range = source
                .parse
                .arena
                .get(source.parse.source_file)
                .map(|source| source.range)
                .ok_or(CanonicalProgramCheckError::InvalidDiagnosticNode(node))?;
            let range = match range_override {
                Some(range_override)
                    if range_override.is_valid_for(node, anchor.range, source_range) =>
                {
                    range_override.range()
                }
                Some(range_override) => {
                    return Err(CanonicalProgramCheckError::InvalidDiagnosticRange {
                        node: Some(node),
                        range_override,
                    });
                }
                None => anchor.range,
            };
            (Some(source.file_name.clone()), Some(range))
        } else {
            if let Some(range_override) = range_override {
                return Err(CanonicalProgramCheckError::InvalidDiagnosticRange {
                    node: None,
                    range_override,
                });
            }
            (None, None)
        };
        Ok(ProgramDiagnostic {
            file_name,
            range,
            code: Some(diagnostic.code()),
            category: diagnostic.category(),
            message: diagnostic
                .render()
                .map_err(CanonicalProgramCheckError::DiagnosticFormat)?,
            related_information: Vec::new(),
        })
    }

    #[allow(clippy::too_many_lines)]
    fn check_program_legacy(&mut self) {
        let module_maps = self
            .source_files
            .iter()
            .map(|source_file| {
                let containing = canonicalize(
                    &source_file.file_name,
                    &self.current_directory,
                    self.case_sensitivity,
                );
                self.resolved_modules
                    .iter()
                    .filter_map(|(key, target)| {
                        (key.containing_file == containing).then(|| {
                            self.file_index
                                .get(target)
                                .map(|index| (key.specifier.clone(), *index))
                        })?
                    })
                    .collect::<BTreeMap<_, _>>()
            })
            .collect::<Vec<_>>();
        let checked = {
            let source_paths = self
                .source_files
                .iter()
                .map(|source_file| source_file.file_name.clone())
                .collect::<Vec<_>>();
            let inputs = self
                .source_files
                .iter()
                .zip(&module_maps)
                .map(|(source_file, resolved_modules)| {
                    let check_directive = source_check_js_directive(&source_file.source_text);
                    ProgramSource {
                        arena: &source_file.parse.arena,
                        source_file: source_file.parse.source_file,
                        bindings: &source_file.binding,
                        resolved_modules,
                        is_default_library: source_file.is_default_library,
                        skip_diagnostics: self.options.no_check
                            || check_directive == Some(false)
                            || (is_javascript_file_name(&source_file.file_name)
                                && !check_directive.unwrap_or(self.options.check_js))
                            || (self.options.skip_lib_check
                                && ts_path::is_declaration_file(&source_file.file_name)),
                        checker_options: CheckerOptions {
                            allow_unreachable_code: self.options.allow_unreachable_code,
                            exact_optional_property_types: self
                                .options
                                .exact_optional_property_types,
                            is_declaration_file: ts_path::is_declaration_file(
                                &source_file.file_name,
                            ),
                            is_javascript_file: is_javascript_file_name(&source_file.file_name),
                            no_fallthrough_cases_in_switch: self
                                .options
                                .no_fallthrough_cases_in_switch,
                            strict_null_checks: self.options.strict_null_checks,
                            strict_property_initialization: self
                                .options
                                .strict_property_initialization,
                            no_implicit_any: self.options.no_implicit_any,
                            no_implicit_this: if self.options.no_implicit_this_specified {
                                self.options.no_implicit_this
                            } else {
                                self.options.strict
                            },
                            no_implicit_returns: self.options.no_implicit_returns,
                            no_unused_locals: self.options.no_unused_locals,
                            no_unused_parameters: self.options.no_unused_parameters,
                            use_unknown_in_catch_variables: self
                                .options
                                .use_unknown_in_catch_variables,
                        },
                    }
                })
                .collect::<Vec<_>>();
            check_program_with_paths(&inputs, &source_paths)
        };
        let check_declaration_portability = self.options.declaration && !self.options.no_check;
        let portability_diagnostics = if check_declaration_portability {
            self.declaration_portability_diagnostics()
        } else {
            vec![Vec::new(); self.source_files.len()]
        };
        let checked_files = checked.into_files();
        for (index, (source_file, mut checking)) in
            self.source_files.iter_mut().zip(checked_files).enumerate()
        {
            if check_declaration_portability {
                add_nonportable_inferred_type_diagnostics(source_file, &mut checking);
            }
            checking
                .diagnostics
                .extend(portability_diagnostics[index].iter().cloned());
            if self.options.no_check
                || source_check_js_directive(&source_file.source_text) == Some(false)
            {
                checking.diagnostics.clear();
            }
            for diagnostic in &checking.diagnostics {
                let range = source_file
                    .parse
                    .arena
                    .get(diagnostic.node)
                    .map(|node| node.range);
                self.diagnostics.push(ProgramDiagnostic {
                    file_name: Some(source_file.file_name.clone()),
                    range,
                    code: Some(diagnostic.diagnostic.code()),
                    category: diagnostic.diagnostic.category(),
                    message: diagnostic
                        .diagnostic
                        .render()
                        .unwrap_or_else(|error| error.to_string()),
                    related_information: Vec::new(),
                });
            }
            source_file.checking = checking;
        }
    }

    fn declaration_portability_diagnostics(&self) -> Vec<Vec<CheckDiagnostic>> {
        let mut diagnostics = self.nonportable_nested_package_diagnostics();
        for (target, additional) in diagnostics
            .iter_mut()
            .zip(self.unserializable_mapped_import_diagnostics())
        {
            target.extend(additional);
        }
        diagnostics
    }

    #[allow(clippy::too_many_lines)]
    fn nonportable_nested_package_diagnostics(&self) -> Vec<Vec<CheckDiagnostic>> {
        let mut diagnostics = vec![Vec::new(); self.source_files.len()];
        for (source_index, source) in self.source_files.iter().enumerate() {
            let containing = canonicalize(
                &source.file_name,
                &self.current_directory,
                self.case_sensitivity,
            );
            let imports = source_import_bindings(source);
            let Some(NodeData::SourceFile(file)) = source
                .parse
                .arena
                .get(source.parse.source_file)
                .map(|node| &node.data)
            else {
                continue;
            };
            for statement in &file.statements.nodes {
                if let Some(diagnostic) = self.nonportable_default_export_assignment_diagnostic(
                    source,
                    &containing,
                    &imports,
                    *statement,
                ) {
                    diagnostics[source_index].push(diagnostic);
                    continue;
                }
                let Some(NodeData::VariableStatement(variable)) =
                    source.parse.arena.get(*statement).map(|node| &node.data)
                else {
                    continue;
                };
                if !node_has_modifier(
                    &source.parse.arena,
                    variable.modifiers.as_ref(),
                    ts_ast::SyntaxKind::ExportKeyword,
                ) {
                    continue;
                }
                let Some(NodeData::VariableDeclarationList(list)) = source
                    .parse
                    .arena
                    .get(variable.declaration_list)
                    .map(|node| &node.data)
                else {
                    continue;
                };
                for declaration_id in &list.declarations.nodes {
                    let Some(NodeData::VariableDeclaration(declaration)) = source
                        .parse
                        .arena
                        .get(*declaration_id)
                        .map(|node| &node.data)
                    else {
                        continue;
                    };
                    if declaration.type_.is_some() {
                        continue;
                    }
                    let Some(NodeData::CallExpression(call)) = declaration
                        .initializer
                        .and_then(|initializer| source.parse.arena.get(initializer))
                        .map(|node| &node.data)
                    else {
                        continue;
                    };
                    let Some(callee) = identifier_text(&source.parse.arena, call.expression) else {
                        continue;
                    };
                    let Some((_, imported_name, specifier)) =
                        imports.iter().find(|(local, _, _)| local == callee)
                    else {
                        continue;
                    };
                    let Some(target_name) = self.resolved_modules.get(&ResolvedModuleKey::new(
                        containing.clone(),
                        specifier.clone(),
                        self.canonical_emit_module_mode(source),
                    )) else {
                        continue;
                    };
                    let Some(target) = self
                        .file_index
                        .get(target_name)
                        .and_then(|index| self.source_files.get(*index))
                    else {
                        continue;
                    };
                    let Some((qualifier, module)) =
                        nonportable_return_import(self, target, imported_name)
                    else {
                        continue;
                    };
                    let Some(name) = identifier_text(&source.parse.arena, declaration.name) else {
                        continue;
                    };
                    let message =
                        message_by_code(2883).expect("TS2883 must be in the diagnostic catalog");
                    diagnostics[source_index].push(CheckDiagnostic {
                        node: declaration.name,
                        diagnostic: Diagnostic::with_arguments(
                            message,
                            [name.to_owned(), qualifier, module],
                        ),
                    });
                }
            }
        }
        diagnostics
    }

    fn nonportable_default_export_assignment_diagnostic(
        &self,
        source: &SourceFile,
        containing: &str,
        imports: &[(String, String, String)],
        statement: NodeId,
    ) -> Option<CheckDiagnostic> {
        let NodeData::ExportAssignment(export) = &source.parse.arena.get(statement)?.data else {
            return None;
        };
        if export.is_export_equals || !export_assignment_is_object_assign(source, export.expression)
        {
            return None;
        }
        let (_, _, specifier) = imports
            .iter()
            .find(|(_, imported, _)| imported == "default")?;
        let target_name = self.resolved_modules.get(&ResolvedModuleKey::new(
            containing.to_owned(),
            specifier.clone(),
            self.canonical_emit_module_mode(source),
        ))?;
        let target = self
            .file_index
            .get(target_name)
            .and_then(|index| self.source_files.get(*index))?;
        let (qualifier, module) = nested_namespace_import_reference(self, target)?;
        let message = message_by_code(2883).expect("TS2883 must be in the diagnostic catalog");
        Some(CheckDiagnostic {
            node: statement,
            diagnostic: Diagnostic::with_arguments(message, ["default".into(), qualifier, module]),
        })
    }

    fn unserializable_mapped_import_diagnostics(&self) -> Vec<Vec<CheckDiagnostic>> {
        let mut diagnostics = vec![Vec::new(); self.source_files.len()];
        for (source_index, source) in self.source_files.iter().enumerate() {
            let containing = canonicalize(
                &source.file_name,
                &self.current_directory,
                self.case_sensitivity,
            );
            let imports = source_import_bindings(source);
            let Some(NodeData::SourceFile(file)) = source
                .parse
                .arena
                .get(source.parse.source_file)
                .map(|node| &node.data)
            else {
                continue;
            };
            for statement in &file.statements.nodes {
                let Some(NodeData::VariableStatement(variable)) =
                    source.parse.arena.get(*statement).map(|node| &node.data)
                else {
                    continue;
                };
                if !node_has_modifier(
                    &source.parse.arena,
                    variable.modifiers.as_ref(),
                    ts_ast::SyntaxKind::ExportKeyword,
                ) {
                    continue;
                }
                let Some(NodeData::VariableDeclarationList(list)) = source
                    .parse
                    .arena
                    .get(variable.declaration_list)
                    .map(|node| &node.data)
                else {
                    continue;
                };
                for declaration_id in &list.declarations.nodes {
                    let Some(NodeData::VariableDeclaration(declaration)) = source
                        .parse
                        .arena
                        .get(*declaration_id)
                        .map(|node| &node.data)
                    else {
                        continue;
                    };
                    if declaration.type_.is_some() {
                        continue;
                    }
                    let Some((local, member)) = declaration
                        .initializer
                        .and_then(|initializer| imported_call_target(source, initializer))
                    else {
                        continue;
                    };
                    let Some((_, imported, specifier)) =
                        imports.iter().find(|(candidate, _, _)| candidate == &local)
                    else {
                        continue;
                    };
                    let imported = if imported == "*" {
                        let Some(member) = member.as_deref() else {
                            continue;
                        };
                        member
                    } else {
                        imported
                    };
                    let Some(target_name) = self.resolved_modules.get(&ResolvedModuleKey::new(
                        containing.clone(),
                        specifier.clone(),
                        self.canonical_emit_module_mode(source),
                    )) else {
                        continue;
                    };
                    let Some(target) = self
                        .file_index
                        .get(target_name)
                        .and_then(|index| self.source_files.get(*index))
                    else {
                        continue;
                    };
                    let Some(property) = imported_function_mapped_symbol_property(target, imported)
                    else {
                        continue;
                    };
                    let message =
                        message_by_code(4118).expect("TS4118 must be in the diagnostic catalog");
                    diagnostics[source_index].push(CheckDiagnostic {
                        node: declaration.name,
                        diagnostic: Diagnostic::with_arguments(message, [format!("[{property}]")]),
                    });
                }
            }
        }
        diagnostics
    }

    fn insert_source_file(&mut self, canonical: String, source_file: SourceFile) {
        let index = self.source_files.len();
        let expected_id =
            FileId::new(u32::try_from(index).expect("Program exceeds u32::MAX source files"));
        assert_eq!(
            source_file.id, expected_id,
            "SourceFile identity does not match its Program slot"
        );
        assert_eq!(
            source_file.binding.file_id(),
            Some(source_file.id),
            "binding provenance does not match its owning SourceFile"
        );
        assert!(
            source_file
                .binding
                .is_for_source(&source_file.parse.arena, source_file.parse.source_file),
            "binding arena and source file do not match their owning SourceFile"
        );
        assert!(
            self.file_index.insert(canonical, index).is_none(),
            "canonical source file inserted more than once"
        );
        self.source_files.push(source_file);
    }

    #[allow(clippy::too_many_lines)]
    fn load_file(&mut self, file_system: &dyn FileSystem, file_name: &str, report_missing: bool) {
        let canonical = canonicalize(file_name, &self.current_directory, self.case_sensitivity);
        if self.file_index.contains_key(&canonical) {
            return;
        }
        let Ok(source_text) = file_system.read_file(file_name) else {
            if report_missing {
                self.diagnostics.push(missing_file_diagnostic(file_name));
            }
            return;
        };
        let extension = Path::new(file_name)
            .extension()
            .and_then(|extension| extension.to_str());
        let is_javascript = extension.is_some_and(|extension| {
            ["js", "jsx", "mjs", "cjs"]
                .iter()
                .any(|candidate| extension.eq_ignore_ascii_case(candidate))
        });
        let parse = if is_javascript {
            parse_javascript_source_file(&source_text)
        } else if extension.is_some_and(|extension| extension.eq_ignore_ascii_case("tsx")) {
            parse_jsx_source_file(&source_text)
        } else {
            parse_source_file(&source_text)
        };
        for diagnostic in &parse.diagnostics {
            self.diagnostics.push(ProgramDiagnostic {
                file_name: Some(file_name.to_owned()),
                range: Some(diagnostic.range),
                code: diagnostic.code,
                category: match diagnostic.category {
                    ts_core::DiagnosticCategory::Warning => Category::Warning,
                    ts_core::DiagnosticCategory::Error => Category::Error,
                    ts_core::DiagnosticCategory::Suggestion => Category::Suggestion,
                    ts_core::DiagnosticCategory::Message => Category::Message,
                },
                message: diagnostic.message.clone(),
                related_information: Vec::new(),
            });
        }
        if is_javascript {
            self.diagnostics.extend(javascript_syntax_diagnostics(
                file_name,
                &source_text,
                &parse,
                !source_check_js_directive(&source_text).unwrap_or(self.options.check_js)
                    && !self.options.experimental_decorators,
            ));
        }
        let index = self.source_files.len();
        let file_id =
            FileId::new(u32::try_from(index).expect("Program exceeds u32::MAX source files"));
        let implied_node_format = implied_node_format(
            file_system,
            file_name,
            file_id,
            &mut self.graph_package_scope_recorder,
        );
        // SourceFile retains this compatibility binding for existing Program
        // consumers. Canonical mode never publishes its diagnostics or passes
        // it to the canonical checker.
        let binding = if self.checker == ProgramChecker::Legacy {
            let language = if is_javascript {
                CanonicalSourceLanguage::JavaScript
            } else {
                CanonicalSourceLanguage::TypeScript
            };
            let is_declaration_file = ts_path::is_declaration_file(file_name);
            let facts = CanonicalSourceFileFacts::new(
                EscapedName::source(format!("\"{}\"", remove_file_extension(file_name))),
                language,
                is_declaration_file,
                source_file_module_state(
                    file_name,
                    &parse,
                    language,
                    is_declaration_file,
                    implied_node_format,
                    &self.options,
                ),
            )
            .with_always_strict(self.options.always_strict);
            bind_source_file_in_file_with_facts(&parse.arena, parse.source_file, file_id, facts)
        } else {
            bind_source_file_in_file(&parse.arena, parse.source_file, file_id)
        };
        if self.checker == ProgramChecker::Legacy
            && source_check_js_directive(&source_text) != Some(false)
        {
            for diagnostic in &binding.diagnostics {
                let range = parse.arena.get(diagnostic.node).map(|node| node.range);
                self.diagnostics.push(ProgramDiagnostic {
                    file_name: Some(file_name.to_owned()),
                    range,
                    code: Some(diagnostic.diagnostic.code()),
                    category: diagnostic.diagnostic.category(),
                    message: diagnostic
                        .diagnostic
                        .render()
                        .unwrap_or_else(|error| error.to_string()),
                    related_information: Vec::new(),
                });
            }
        }
        if self.options.target < ScriptTarget::Es2015
            && let Some(message) = message_by_code(18045)
        {
            for (_, node) in parse.arena.iter() {
                let NodeData::PropertyDeclaration(property) = &node.data else {
                    continue;
                };
                let auto_accessor = property.modifiers.as_ref().is_some_and(|modifiers| {
                    modifiers.list.nodes.iter().any(|modifier| {
                        parse
                            .arena
                            .get(*modifier)
                            .is_some_and(|modifier| modifier.kind == SyntaxKind::AccessorKeyword)
                    })
                });
                if auto_accessor {
                    self.diagnostics.push(ProgramDiagnostic {
                        file_name: Some(file_name.to_owned()),
                        range: Some(node.range),
                        code: Some(message.code()),
                        category: message.category(),
                        message: message
                            .format(&[])
                            .unwrap_or_else(|error| error.to_string()),
                        related_information: Vec::new(),
                    });
                }
            }
        }
        let checking = empty_check_result();
        self.insert_source_file(
            canonical,
            SourceFile {
                id: file_id,
                file_name: file_name.to_owned(),
                source_text,
                parse,
                binding,
                checking,
                is_default_library: false,
                implied_node_format,
            },
        );
    }

    fn load_default_libraries(&mut self) {
        if self.options.no_lib {
            return;
        }
        let roots = match &self.options.lib {
            None => vec![ts_bundled::default_library_name(self.options.target).to_owned()],
            Some(libraries) => libraries
                .iter()
                .map(|name| bundled_library_name(name))
                .collect(),
        };
        for root in roots {
            for library_name in ts_bundled::library_closure(&root) {
                self.load_bundled_library(library_name);
            }
        }
    }

    fn load_automatic_type_directives(
        &mut self,
        file_system: &dyn FileSystem,
        resolution_options: &ResolutionOptions,
    ) {
        let names = automatic_type_directive_names(
            file_system,
            resolution_options,
            &self.current_directory,
        );
        if names.is_empty() {
            return;
        }
        let resolver = Resolver::new(file_system, resolution_options.clone());
        let containing_file =
            resolve_path(&self.current_directory, &["__inferred type names__.ts"]);
        for name in names {
            let result = resolver.resolve_type_reference(&name, &containing_file);
            self.record_graph_resolution(
                ProgramGraphResolutionRequest {
                    kind: ProgramGraphResolutionKind::AutomaticTypeDirective,
                    containing_file: containing_file.clone(),
                    range: None,
                    specifier: name.clone(),
                    mode: None,
                },
                &result,
                None,
            );
            if let Some(resolved) = result.resolved {
                self.load_source_at_node_depth(
                    file_system,
                    &resolved.resolved_file_name,
                    u32::from(resolved.is_external_library_import),
                    false,
                );
            } else if resolution_options
                .types
                .as_ref()
                .is_some_and(|types| types.iter().any(|entry| entry == &name))
            {
                self.diagnostics.push(type_definition_not_found(&name));
            }
        }
    }

    #[allow(clippy::too_many_lines)] // Keep reference order, admission, and diagnostics together.
    fn load_reference_directives_for_file(
        &mut self,
        file_system: &dyn FileSystem,
        resolver: &Resolver<'_, dyn FileSystem + '_>,
        file_index: usize,
    ) {
        let containing_file = self.source_files[file_index].file_name.clone();
        let containing_id = self.source_files[file_index].id;
        let directives = reference_directives(&self.source_files[file_index].source_text);
        for directive in directives {
            match directive.kind {
                ReferenceKind::Path if self.options.no_resolve => {
                    self.graph_references.push(ProgramGraphReference {
                        containing_file: containing_file.clone(),
                        range: directive.range,
                        specifier: directive.value,
                        kind: ProgramGraphReferenceKind::Path,
                        skipped: true,
                        targets: Vec::new(),
                    });
                }
                ReferenceKind::Types if self.options.no_resolve => {}
                ReferenceKind::Lib if self.options.no_lib => {}
                ReferenceKind::Path => {
                    let unresolved_file_name = resolve_path(
                        &directory_path(&containing_file),
                        &[directive.value.as_str()],
                    );
                    let file_name = resolve_reference_path(
                        file_system,
                        &unresolved_file_name,
                        self.allows_javascript_sources(),
                    )
                    .unwrap_or(unresolved_file_name);
                    self.graph_references.push(ProgramGraphReference {
                        containing_file: containing_file.clone(),
                        range: directive.range,
                        specifier: directive.value,
                        kind: ProgramGraphReferenceKind::Path,
                        skipped: false,
                        targets: vec![ProgramGraphReferenceTarget {
                            file_name: file_name.clone(),
                            file_id: None,
                        }],
                    });
                    self.load_source_dependency(
                        file_system,
                        containing_id,
                        SourceLoadDependency {
                            file_name,
                            external_library: false,
                            kind: SourceLoadKind::PathReference(directive.range.start),
                        },
                    );
                }
                ReferenceKind::Types => {
                    let result =
                        resolver.resolve_type_reference(&directive.value, &containing_file);
                    self.record_graph_resolution(
                        ProgramGraphResolutionRequest {
                            kind: ProgramGraphResolutionKind::TypeReference,
                            containing_file: containing_file.clone(),
                            range: Some(directive.range),
                            specifier: directive.value.clone(),
                            mode: None,
                        },
                        &result,
                        None,
                    );
                    if let Some(resolved) = result.resolved {
                        self.load_source_dependency(
                            file_system,
                            containing_id,
                            SourceLoadDependency {
                                file_name: resolved.resolved_file_name,
                                external_library: resolved.is_external_library_import,
                                kind: SourceLoadKind::TypeReference(directive.range.start),
                            },
                        );
                    } else if !(self.options.skip_lib_check
                        && ts_path::is_declaration_file(&containing_file)
                        || source_ignores_processing_diagnostic(
                            &self.source_files[file_index],
                            directive.range,
                        ))
                    {
                        let mut diagnostic = type_definition_not_found(&directive.value);
                        diagnostic.file_name = Some(containing_file.clone());
                        diagnostic.range = Some(directive.range);
                        self.diagnostics.push(diagnostic);
                    }
                }
                ReferenceKind::Lib => {
                    let library_name = bundled_library_name(&directive.value);
                    let dependencies = ts_bundled::library_closure(&library_name);
                    self.graph_references.push(ProgramGraphReference {
                        containing_file: containing_file.clone(),
                        range: directive.range,
                        specifier: directive.value,
                        kind: ProgramGraphReferenceKind::Library,
                        skipped: false,
                        targets: dependencies
                            .iter()
                            .map(|dependency| ProgramGraphReferenceTarget {
                                file_name: format!("/__typescript/lib/{dependency}"),
                                file_id: None,
                            })
                            .collect(),
                    });
                    for dependency in dependencies {
                        self.load_bundled_library(dependency);
                    }
                }
            }
        }
    }

    fn load_bundled_library(&mut self, library_name: &str) {
        let file_name = format!("/__typescript/lib/{library_name}");
        let canonical = canonicalize(&file_name, &self.current_directory, self.case_sensitivity);
        if self.file_index.contains_key(&canonical) {
            return;
        }
        let Some(source) = ts_bundled::library(library_name) else {
            return;
        };
        let source_text = source.to_owned();
        let parse = parse_source_file(&source_text);
        let index = self.source_files.len();
        let file_id =
            FileId::new(u32::try_from(index).expect("Program exceeds u32::MAX source files"));
        let binding = bind_source_file_in_file(&parse.arena, parse.source_file, file_id);
        let checking = empty_check_result();
        self.insert_source_file(
            canonical,
            SourceFile {
                id: file_id,
                file_name,
                source_text,
                parse,
                binding,
                checking,
                is_default_library: true,
                implied_node_format: ModuleKind::CommonJs,
            },
        );
    }
}

fn canonical_source_file_facts(
    source: &SourceFile,
    options: &CompilerOptions,
) -> Result<CanonicalSourceFileFacts, CanonicalProgramCheckError> {
    let script_kind = ts_path::script_kind_from_path(&source.file_name);
    let language = match script_kind {
        ts_path::ScriptKind::Ts | ts_path::ScriptKind::Tsx => CanonicalSourceLanguage::TypeScript,
        ts_path::ScriptKind::Js | ts_path::ScriptKind::Jsx => CanonicalSourceLanguage::JavaScript,
        _ => {
            return Err(CanonicalProgramCheckError::UnsupportedSourceKind {
                file_name: source.file_name.clone(),
                script_kind,
            });
        }
    };

    let is_declaration_file = ts_path::is_declaration_file(&source.file_name);
    if source_contains_import_meta(&source.parse) {
        return Err(
            CanonicalProgramCheckError::ImportMetaModuleIndicatorUnsupported {
                file_name: source.file_name.clone(),
            },
        );
    }

    let module_state = source_file_module_state(
        &source.file_name,
        &source.parse,
        language,
        is_declaration_file,
        source.implied_node_format,
        options,
    );
    Ok(CanonicalSourceFileFacts::new_with_default_library(
        EscapedName::source(format!("\"{}\"", remove_file_extension(&source.file_name))),
        language,
        is_declaration_file,
        source.is_default_library,
        module_state,
    )
    .with_always_strict(options.always_strict))
}

fn source_file_module_state(
    file_name: &str,
    parse: &ParseResult,
    language: CanonicalSourceLanguage,
    is_declaration_file: bool,
    implied_node_format: ModuleKind,
    options: &CompilerOptions,
) -> CanonicalModuleState {
    let extension = Path::new(file_name)
        .extension()
        .and_then(|extension| extension.to_str());
    let fixed_module_file = extension.is_some_and(|extension| {
        ["mts", "cts", "mjs", "cjs"]
            .iter()
            .any(|candidate| extension.eq_ignore_ascii_case(candidate))
    });
    let node_esm_file = matches!(
        options.module,
        ModuleKind::Node16 | ModuleKind::Node18 | ModuleKind::Node20 | ModuleKind::NodeNext
    ) && implied_node_format == ModuleKind::EsNext;
    let jsx_module = matches!(
        options.jsx,
        ts_options::JsxEmit::ReactJsx | ts_options::JsxEmit::ReactJsxDev
    ) && parse.arena.iter().any(|(_, node)| {
        matches!(
            node.data,
            NodeData::JsxElement(_) | NodeData::JsxSelfClosingElement(_) | NodeData::JsxFragment(_)
        )
    });
    let is_external_module = source_file_is_external_module(parse)
        || (!is_declaration_file
            && (options.module_detection == ModuleDetectionKind::Force
                || (options.module_detection == ModuleDetectionKind::Auto
                    && (fixed_module_file || node_esm_file || jsx_module))));
    let is_common_js_module = language == CanonicalSourceLanguage::JavaScript
        && source_file_has_commonjs_indicator(parse);
    match (is_external_module, is_common_js_module) {
        (true, true) => CanonicalModuleState::ExternalAndCommonJs,
        (true, false) => CanonicalModuleState::External,
        (false, true) => CanonicalModuleState::CommonJs,
        (false, false) => CanonicalModuleState::Script,
    }
}

fn resolve_reference_path(
    file_system: &dyn FileSystem,
    file_name: &str,
    allow_javascript: bool,
) -> Option<String> {
    if file_system.file_exists(file_name) {
        return Some(file_name.to_owned());
    }
    if Path::new(file_name).extension().is_some() {
        return None;
    }
    let extensions: &[&str] = if allow_javascript {
        &[".ts", ".tsx", ".d.ts", ".js", ".jsx"]
    } else {
        &[".ts", ".tsx", ".d.ts"]
    };
    extensions
        .iter()
        .map(|extension| format!("{file_name}{extension}"))
        .find(|candidate| file_system.file_exists(candidate))
}

fn implied_node_format(
    file_system: &dyn FileSystem,
    file_name: &str,
    file_id: FileId,
    observation: &mut project_graph::PackageScopeObservationRecorder,
) -> ModuleKind {
    let extension = Path::new(file_name)
        .extension()
        .and_then(|value| value.to_str());
    if extension.is_some_and(|extension| {
        extension.eq_ignore_ascii_case("mts") || extension.eq_ignore_ascii_case("mjs")
    }) {
        observation.decision(
            file_id,
            ModuleKind::EsNext,
            ProgramGraphPackageScopeDecision::FixedExtension,
        );
        return ModuleKind::EsNext;
    }
    if extension.is_some_and(|extension| {
        extension.eq_ignore_ascii_case("cts") || extension.eq_ignore_ascii_case("cjs")
    }) {
        observation.decision(
            file_id,
            ModuleKind::CommonJs,
            ProgramGraphPackageScopeDecision::FixedExtension,
        );
        return ModuleKind::CommonJs;
    }
    let mut directory = directory_path(file_name);
    loop {
        let package_json = resolve_path(&directory, &["package.json"]);
        let exists = file_system.file_exists(&package_json);
        observation.file_exists(file_id, &package_json, exists);
        if exists {
            let (format, reason) = match file_system.read_file(&package_json) {
                Ok(contents) => {
                    observation.read_text(file_id, &package_json, &contents);
                    match parse_package_json(&contents) {
                        Ok(package) => (
                            package
                                .package_type
                                .filter(|package_type| package_type == "module")
                                .map_or(ModuleKind::CommonJs, |_| ModuleKind::EsNext),
                            ProgramGraphPackageScopeDecision::PackageJson,
                        ),
                        Err(_) => (
                            ModuleKind::CommonJs,
                            ProgramGraphPackageScopeDecision::InvalidPackageJson,
                        ),
                    }
                }
                Err(error) => {
                    observation.read_error(file_id, &package_json, &error);
                    (
                        ModuleKind::CommonJs,
                        ProgramGraphPackageScopeDecision::ReadFailure,
                    )
                }
            };
            observation.decision(file_id, format, reason);
            return format;
        }
        let parent = directory_path(&directory);
        if parent == directory {
            break;
        }
        directory = parent;
    }
    observation.decision(
        file_id,
        ModuleKind::CommonJs,
        ProgramGraphPackageScopeDecision::NoPackage,
    );
    ModuleKind::CommonJs
}

fn package_display_name(directory: &str, declared_name: Option<&str>) -> Option<String> {
    let installed = directory
        .rsplit_once("/node_modules/")
        .map(|(_, name)| name)
        .or_else(|| directory.strip_prefix("node_modules/"));
    let name = installed.or(declared_name)?;
    if name.is_empty() {
        return None;
    }
    if let Some(types_package) = name.strip_prefix("@types/") {
        return Some(types_package.split_once("__").map_or_else(
            || types_package.to_owned(),
            |(scope, package)| format!("@{scope}/{package}"),
        ));
    }
    Some(name.to_owned())
}

fn module_file_stem(path: &str) -> &str {
    [".d.ts", ".d.mts", ".d.cts"]
        .into_iter()
        .find_map(|suffix| path.strip_suffix(suffix))
        .unwrap_or_else(|| ts_path::remove_file_extension(path))
}

#[derive(Clone, Copy)]
enum ReferenceKind {
    Path,
    Types,
    Lib,
}

struct ReferenceDirective {
    kind: ReferenceKind,
    value: String,
    range: TextRange,
}

fn reference_directives(source: &str) -> Vec<ReferenceDirective> {
    source
        .split_inclusive('\n')
        .scan(0_usize, |offset, line| {
            let line_offset = *offset;
            *offset += line.len();
            Some((line_offset, line))
        })
        .filter_map(|(line_offset, line)| {
            let reference = line
                .trim_start()
                .strip_prefix("///")?
                .trim_start()
                .strip_prefix("<reference")?;
            [
                (ReferenceKind::Types, "types"),
                (ReferenceKind::Lib, "lib"),
                (ReferenceKind::Path, "path"),
            ]
            .into_iter()
            .find_map(|(kind, name)| {
                let (value, value_offset) = reference_attribute_value(reference, name)?;
                let start = line_offset + line.len() - reference.len() + value_offset;
                let end = start + value.len();
                Some(ReferenceDirective {
                    kind,
                    value: value.to_owned(),
                    range: TextRange::new(
                        TextPos::new(u32::try_from(start).ok()?),
                        TextPos::new(u32::try_from(end).ok()?),
                    ),
                })
            })
        })
        .collect()
}

fn source_ignores_processing_diagnostic(source: &SourceFile, range: TextRange) -> bool {
    let Ok(position) = usize::try_from(range.start.get()) else {
        return false;
    };
    let line_starts = source_line_starts(&source.source_text);
    let directives = source_comment_directives(&source.parse, &line_starts);
    let line = source_line_of_position(&line_starts, position);

    for previous in (0..line).rev() {
        if let Some(directive) = directives.get(&previous) {
            return !directive.expect_error;
        }
        let start = line_starts[previous];
        let end = line_starts
            .get(previous + 1)
            .copied()
            .unwrap_or(source.source_text.len());
        if !source_line_is_comment_or_blank(&source.source_text[start..end]) {
            break;
        }
    }

    false
}

fn has_preserved_reference_directive(source: &str) -> bool {
    source.lines().any(|line| {
        let trimmed = line.trim_start();
        trimmed.starts_with("///")
            && trimmed.contains("<reference")
            && (trimmed.contains("preserve=\"true\"") || trimmed.contains("preserve='true'"))
    })
}

fn reference_attribute_value<'source>(
    reference: &'source str,
    name: &str,
) -> Option<(&'source str, usize)> {
    let mut rest = reference;
    while let Some(index) = rest.find(name) {
        let candidate = &rest[index + name.len()..];
        let candidate = candidate.trim_start();
        if let Some(candidate) = candidate.strip_prefix('=') {
            let candidate = candidate.trim_start();
            let quote = candidate.chars().next()?;
            if matches!(quote, '\'' | '"') {
                let value = &candidate[quote.len_utf8()..];
                let value_offset = reference.len() - value.len();
                return value.find(quote).map(|end| (&value[..end], value_offset));
            }
        }
        rest = &candidate[candidate
            .char_indices()
            .nth(1)
            .map_or(candidate.len(), |(i, _)| i)..];
    }
    None
}

fn bundled_library_name(name: &str) -> String {
    let name = name.to_ascii_lowercase();
    if name.starts_with("lib.") && name.ends_with(".d.ts") {
        name
    } else {
        format!("lib.{name}.d.ts")
    }
}

fn serialize_source_map(source_map: &SourceMap, source_root: Option<&str>) -> String {
    #[derive(serde::Serialize)]
    #[serde(rename_all = "camelCase")]
    struct SerializedSourceMap<'a> {
        version: u8,
        file: &'a Option<String>,
        source_root: &'a str,
        sources: &'a [String],
        names: &'a [String],
        mappings: &'a str,
        #[serde(skip_serializing_if = "Option::is_none")]
        sources_content: &'a Option<Vec<String>>,
    }

    let source_root = source_root.map_or_else(String::new, |source_root| {
        if source_root.is_empty() || source_root.ends_with('/') {
            source_root.to_owned()
        } else {
            format!("{source_root}/")
        }
    });
    serde_json::to_string(&SerializedSourceMap {
        version: source_map.version,
        file: &source_map.file,
        source_root: &source_root,
        sources: &source_map.sources,
        names: &source_map.names,
        mappings: &source_map.mappings,
        sources_content: &source_map.sources_content,
    })
    .expect("source map fields are JSON-serializable")
}

fn make_source_map_sources_relative(
    source_map: &mut SourceMap,
    source_directory: &str,
    case_sensitivity: CaseSensitivity,
) {
    for source in &mut source_map.sources {
        if is_absolute(source) {
            *source = ts_path::relative_path_to_directory_or_url(
                source_directory,
                source,
                case_sensitivity,
            );
        }
    }
}

fn strip_directory_prefix(path: &str, directory: &str) -> Option<String> {
    let path = ts_path::normalize_path(path);
    let directory = ts_path::normalize_path(directory)
        .trim_end_matches('/')
        .to_owned();
    let remainder = path.strip_prefix(&directory)?;
    if remainder.is_empty() {
        Some(String::new())
    } else {
        remainder.strip_prefix('/').map(str::to_owned)
    }
}

fn relative_path(from_directory: &str, target: &str) -> String {
    let from = ts_path::normalize_path(from_directory);
    let target = ts_path::normalize_path(target);
    let from_parts = from
        .trim_matches('/')
        .split('/')
        .filter(|part| !part.is_empty())
        .collect::<Vec<_>>();
    let target_parts = target
        .trim_matches('/')
        .split('/')
        .filter(|part| !part.is_empty())
        .collect::<Vec<_>>();
    let common = from_parts
        .iter()
        .zip(&target_parts)
        .take_while(|(left, right)| left == right)
        .count();
    let mut parts = vec![".."; from_parts.len().saturating_sub(common)];
    parts.extend(target_parts[common..].iter().copied());
    if parts.is_empty() {
        ".".to_owned()
    } else {
        parts.join("/")
    }
}

fn preserved_reference_directives(source: &SourceFile, declaration_file: &str) -> String {
    let source_directory = directory_path(&source.file_name);
    let declaration_directory = directory_path(declaration_file);
    let mut output = String::new();
    for line in source.source_text.lines() {
        let trimmed = line.trim_start();
        if !trimmed.starts_with("///")
            || !trimmed.contains("<reference")
            || !(trimmed.contains("preserve=\"true\"") || trimmed.contains("preserve='true'"))
        {
            continue;
        }
        if let Some(reference) = preserved_reference_value(trimmed, "types") {
            output.push_str("/// <reference types=\"");
            output.push_str(reference);
            output.push('"');
            if let Some(mode) = preserved_reference_value(trimmed, "resolution-mode") {
                output.push_str(" resolution-mode=\"");
                output.push_str(mode);
                output.push('"');
            }
            output.push_str(" preserve=\"true\" />\n");
            continue;
        }
        if let Some(reference) = preserved_reference_value(trimmed, "lib") {
            output.push_str("/// <reference lib=\"");
            output.push_str(reference);
            output.push_str("\" preserve=\"true\" />\n");
            continue;
        }
        let Some(reference) = preserved_reference_value(trimmed, "path") else {
            continue;
        };
        let target = resolve_path(&source_directory, &[reference]);
        let target = change_extension(&target, declaration_emit_extension(&target));
        let rewritten = relative_path(&declaration_directory, &target);
        output.push_str("/// <reference path=\"");
        output.push_str(&rewritten);
        output.push_str("\" preserve=\"true\" />\n");
    }
    output
}

fn preserved_reference_value<'a>(directive: &'a str, attribute: &str) -> Option<&'a str> {
    let start = directive.find(&format!("{attribute}="))? + attribute.len() + 1;
    let quote = directive.as_bytes().get(start).copied().map(char::from)?;
    if !matches!(quote, '\'' | '"') {
        return None;
    }
    let value_start = start + 1;
    let value_end = directive[value_start..].find(quote)? + value_start;
    Some(&directive[value_start..value_end])
}

fn has_isolated_declaration_emit_error(source: &SourceFile) -> bool {
    let javascript_source = matches!(
        ts_path::script_kind_from_path(&source.file_name),
        ts_path::ScriptKind::Js | ts_path::ScriptKind::Jsx
    );
    source.parse.arena.iter().any(|(_, node)| {
        let NodeData::ComputedPropertyName(name) = &node.data else {
            return false;
        };
        let Some(expression) = source.parse.arena.get(name.expression) else {
            return true;
        };
        match &expression.data {
            NodeData::NumericLiteral(_)
            | NodeData::StringLiteral(_)
            | NodeData::NoSubstitutionTemplateLiteral(_) => false,
            NodeData::PrefixUnaryExpression(prefix) => !matches!(
                source
                    .parse
                    .arena
                    .get(prefix.operand)
                    .map(|operand| &operand.data),
                Some(NodeData::NumericLiteral(_))
            ),
            _ => true,
        }
    }) || source.parse.arena.iter().any(|(_, node)| {
        let NodeData::VariableStatement(statement) = &node.data else {
            return false;
        };
        if !node_has_modifier(
            &source.parse.arena,
            statement.modifiers.as_ref(),
            ts_ast::SyntaxKind::ExportKeyword,
        ) {
            return false;
        }
        let Some(NodeData::VariableDeclarationList(list)) = source
            .parse
            .arena
            .get(statement.declaration_list)
            .map(|node| &node.data)
        else {
            return false;
        };
        list.declarations.nodes.iter().any(|declaration| {
            matches!(
                source.parse.arena.get(*declaration).map(|node| &node.data),
                Some(NodeData::VariableDeclaration(variable))
                    if variable.type_.is_none()
                        && ((!javascript_source && variable.initializer.is_none())
                            || variable.initializer.is_some_and(|initializer| matches!(
                                source.parse.arena.get(initializer).map(|node| &node.data),
                                Some(NodeData::PropertyAccessExpression(_)
                                    | NodeData::ElementAccessExpression(_)
                                    | NodeData::CallExpression(_)
                                    | NodeData::NewExpression(_))
                            )))
            )
        })
    }) || has_unsupported_isolated_declaration_shape(source)
}

#[allow(clippy::too_many_lines)]
fn has_unsupported_isolated_declaration_shape(source: &SourceFile) -> bool {
    let arena = &source.parse.arena;
    let Some(NodeData::SourceFile(file)) =
        arena.get(source.parse.source_file).map(|node| &node.data)
    else {
        return false;
    };
    let module_file = file.statements.nodes.iter().any(|statement| {
        let Some(node) = arena.get(*statement) else {
            return false;
        };
        matches!(
            node.data,
            NodeData::ImportDeclaration(_)
                | NodeData::ImportEqualsDeclaration(_)
                | NodeData::ExportDeclaration(_)
                | NodeData::ExportAssignment(_)
        ) || declaration_modifiers(node).is_some_and(|modifiers| {
            node_has_modifier(arena, Some(modifiers), ts_ast::SyntaxKind::ExportKeyword)
        })
    });
    let is_public_statement = |node: &ts_ast::Node| {
        !module_file
            || declaration_modifiers(node).is_some_and(|modifiers| {
                node_has_modifier(arena, Some(modifiers), ts_ast::SyntaxKind::ExportKeyword)
            })
    };

    let mut function_values = BTreeSet::new();
    for statement in &file.statements.nodes {
        let Some(node) = arena.get(*statement) else {
            continue;
        };
        match &node.data {
            NodeData::ExportAssignment(assignment)
                if !assignment.is_export_equals
                    && !matches!(
                        arena.get(assignment.expression).map(|node| &node.data),
                        Some(NodeData::Identifier(_))
                    ) =>
            {
                return true;
            }
            NodeData::FunctionDeclaration(function) => {
                if is_public_statement(node) {
                    if let Some(name) = function.name.and_then(|name| identifier_text(arena, name))
                    {
                        function_values.insert(name.to_owned());
                    }
                    if function.type_.is_none() {
                        return true;
                    }
                    if function.parameters.nodes.iter().any(|parameter| {
                        let Some(NodeData::ParameterDeclaration(parameter)) =
                            arena.get(*parameter).map(|node| &node.data)
                        else {
                            return false;
                        };
                        parameter.initializer.is_some_and(|initializer| {
                            arena.iter().any(|(candidate, candidate_node)| {
                                matches!(
                                    &candidate_node.data,
                                    NodeData::ParameterDeclaration(nested)
                                        if nested.initializer.is_some() && nested.type_.is_none()
                                ) && syntax_node_is_within(arena, candidate, initializer)
                            })
                        })
                    }) {
                        return true;
                    }
                }
            }
            NodeData::VariableStatement(variable) if is_public_statement(node) => {
                let Some(NodeData::VariableDeclarationList(list)) =
                    arena.get(variable.declaration_list).map(|node| &node.data)
                else {
                    continue;
                };
                for declaration in &list.declarations.nodes {
                    let Some(NodeData::VariableDeclaration(declaration)) =
                        arena.get(*declaration).map(|node| &node.data)
                    else {
                        continue;
                    };
                    let Some(initializer) = declaration.initializer else {
                        continue;
                    };
                    if matches!(
                        arena.get(initializer).map(|node| &node.data),
                        Some(NodeData::ArrowFunction(_) | NodeData::FunctionExpression(_))
                    ) && let Some(name) = identifier_text(arena, declaration.name)
                    {
                        function_values.insert(name.to_owned());
                    }
                    match arena.get(initializer).map(|node| &node.data) {
                        Some(NodeData::ArrowFunction(function)) if function.type_.is_none() => {
                            return true;
                        }
                        Some(NodeData::FunctionExpression(function))
                            if function.type_.is_none() =>
                        {
                            return true;
                        }
                        _ => {}
                    }
                    if arena.iter().any(|(candidate, candidate_node)| {
                        matches!(candidate_node.data, NodeData::ClassExpression(_))
                            && syntax_node_is_within(arena, candidate, initializer)
                    }) {
                        return true;
                    }
                }
            }
            NodeData::ClassDeclaration(class) if is_public_statement(node) => {
                for member in &class.members.nodes {
                    let Some(NodeData::PropertyDeclaration(property)) =
                        arena.get(*member).map(|node| &node.data)
                    else {
                        continue;
                    };
                    if property.type_.is_none()
                        && property.initializer.is_some_and(|initializer| {
                            matches!(
                                arena.get(initializer).map(|node| &node.data),
                                Some(NodeData::ArrowFunction(_) | NodeData::FunctionExpression(_))
                            )
                        })
                    {
                        return true;
                    }
                }
            }
            NodeData::ModuleDeclaration(module)
                if matches!(
                    arena.get(module.name).map(|node| &node.data),
                    Some(NodeData::StringLiteral(_))
                ) =>
            {
                return true;
            }
            NodeData::EnumDeclaration(enumeration) => {
                if enumeration.members.nodes.iter().any(|member| {
                    let Some(NodeData::EnumMember(member)) =
                        arena.get(*member).map(|node| &node.data)
                    else {
                        return false;
                    };
                    member.initializer.is_some_and(|initializer| {
                        arena.iter().any(|(candidate, candidate_node)| {
                            matches!(candidate_node.data, NodeData::CallExpression(_))
                                && syntax_node_is_within(arena, candidate, initializer)
                        })
                    })
                }) {
                    return true;
                }
            }
            _ => {}
        }
    }

    file.statements.nodes.iter().any(|statement| {
        let Some(NodeData::ExpressionStatement(statement)) =
            arena.get(*statement).map(|node| &node.data)
        else {
            return false;
        };
        let Some(NodeData::BinaryExpression(assignment)) =
            arena.get(statement.expression).map(|node| &node.data)
        else {
            return false;
        };
        if arena
            .get(assignment.operator_token)
            .is_none_or(|operator| operator.kind != ts_ast::SyntaxKind::EqualsToken)
        {
            return false;
        }
        let Some(NodeData::PropertyAccessExpression(access)) =
            arena.get(assignment.left).map(|node| &node.data)
        else {
            return false;
        };
        identifier_text(arena, access.expression).is_some_and(|name| function_values.contains(name))
    })
}

fn source_has_external_module_augmentation(source: &SourceFile) -> bool {
    source.parse.arena.iter().any(|(_, node)| {
        let NodeData::ModuleDeclaration(module) = &node.data else {
            return false;
        };
        matches!(
            source.parse.arena.get(module.name).map(|node| &node.data),
            Some(NodeData::StringLiteral(_))
        )
    })
}

fn has_private_export_type_query(source: &SourceFile) -> bool {
    source.parse.arena.iter().any(|(query_id, node)| {
        let NodeData::TypeQueryNode(query) = &node.data else {
            return false;
        };
        let mut ancestor = source
            .parse
            .arena
            .get(query_id)
            .and_then(|node| node.parent);
        let mut exported_alias = false;
        while let Some(id) = ancestor {
            let Some(node) = source.parse.arena.get(id) else {
                break;
            };
            if let NodeData::TypeAliasDeclaration(alias) = &node.data {
                exported_alias = node_has_modifier(
                    &source.parse.arena,
                    alias.modifiers.as_ref(),
                    ts_ast::SyntaxKind::ExportKeyword,
                );
                break;
            }
            ancestor = node.parent;
        }
        if !exported_alias {
            return false;
        }
        let Some((identifier, name)) =
            leftmost_entity_identifier(&source.parse.arena, query.expr_name)
        else {
            return false;
        };
        let Some(symbol) = source.binding.resolve_name_at(identifier, name) else {
            return false;
        };
        let Some(symbol) = source.binding.symbols.get(symbol) else {
            return false;
        };
        !symbol.declarations.is_empty()
            && symbol.declarations.iter().all(|declaration| {
                declaration_is_nested_in_runtime_block(
                    &source.parse.arena,
                    *declaration,
                    source.parse.source_file,
                )
            })
    })
}

fn has_unserializable_exported_anonymous_class(source: &SourceFile) -> bool {
    let private_mixins = source
        .parse
        .arena
        .iter()
        .filter_map(|(_, node)| {
            let NodeData::VariableDeclaration(variable) = &node.data else {
                return None;
            };
            let NodeData::ClassExpression(class) =
                &source.parse.arena.get(variable.initializer?)?.data
            else {
                return None;
            };
            class
                .members
                .nodes
                .iter()
                .any(|member| anonymous_class_member_is_private(&source.parse.arena, *member))
                .then(|| identifier_text(&source.parse.arena, variable.name).map(str::to_owned))
                .flatten()
        })
        .collect::<BTreeSet<_>>();
    if private_mixins.is_empty() {
        return false;
    }
    let Some(NodeData::SourceFile(file)) = source
        .parse
        .arena
        .get(source.parse.source_file)
        .map(|node| &node.data)
    else {
        return false;
    };
    file.statements.nodes.iter().any(|statement_id| {
        let Some(statement) = source.parse.arena.get(*statement_id) else {
            return false;
        };
        let exported = matches!(&statement.data, NodeData::ExportAssignment(_))
            || match &statement.data {
                NodeData::ClassDeclaration(class) => node_has_modifier(
                    &source.parse.arena,
                    class.modifiers.as_ref(),
                    ts_ast::SyntaxKind::ExportKeyword,
                ),
                NodeData::VariableStatement(variable) => node_has_modifier(
                    &source.parse.arena,
                    variable.modifiers.as_ref(),
                    ts_ast::SyntaxKind::ExportKeyword,
                ),
                _ => false,
            };
        exported
            && source.parse.arena.iter().any(|(_, node)| {
                statement.range.start <= node.range.start
                    && node.range.end <= statement.range.end
                    && matches!(
                        &node.data,
                        NodeData::Identifier(identifier)
                            if private_mixins.contains(&identifier.text)
                    )
            })
    })
}

fn anonymous_class_member_is_private(arena: &ts_ast::NodeArena, member: NodeId) -> bool {
    let (name, modifiers) = match &arena.get(member).map(|node| &node.data) {
        Some(NodeData::PropertyDeclaration(member)) => {
            (Some(member.name), member.modifiers.as_ref())
        }
        Some(NodeData::MethodDeclaration(member)) => (Some(member.name), member.modifiers.as_ref()),
        Some(NodeData::GetAccessorDeclaration(member)) => {
            (Some(member.name), member.modifiers.as_ref())
        }
        Some(NodeData::SetAccessorDeclaration(member)) => {
            (Some(member.name), member.modifiers.as_ref())
        }
        _ => (None, None),
    };
    name.is_some_and(|name| {
        matches!(
            arena.get(name).map(|node| &node.data),
            Some(NodeData::PrivateIdentifier(_))
        )
    }) || modifiers.is_some_and(|modifiers| {
        modifiers.list.nodes.iter().any(|modifier| {
            arena.get(*modifier).is_some_and(|modifier| {
                matches!(
                    modifier.kind,
                    ts_ast::SyntaxKind::PrivateKeyword | ts_ast::SyntaxKind::ProtectedKeyword
                )
            })
        })
    })
}

fn has_unserializable_exported_class_property_type(source: &SourceFile) -> bool {
    source.parse.arena.iter().any(|(_, node)| {
        let NodeData::ClassDeclaration(class) = &node.data else {
            return false;
        };
        if !node_has_modifier(
            &source.parse.arena,
            class.modifiers.as_ref(),
            ts_ast::SyntaxKind::ExportKeyword,
        ) {
            return false;
        }
        class.members.nodes.iter().any(|member| {
            let Some(NodeData::PropertyDeclaration(property)) =
                source.parse.arena.get(*member).map(|node| &node.data)
            else {
                return false;
            };
            if property.type_.is_some()
                || node_has_modifier(
                    &source.parse.arena,
                    property.modifiers.as_ref(),
                    ts_ast::SyntaxKind::PrivateKeyword,
                )
                || node_has_modifier(
                    &source.parse.arena,
                    property.modifiers.as_ref(),
                    ts_ast::SyntaxKind::ProtectedKeyword,
                )
            {
                return false;
            }
            let Some(type_id) = source.checking.type_of_node(*member).or_else(|| {
                property
                    .initializer
                    .and_then(|id| source.checking.type_of_node(id))
            }) else {
                return false;
            };
            let inaccessible =
                inaccessible_named_type_reference(&source.checking, type_id, &mut BTreeSet::new())
                    .or_else(|| {
                        cyclic_alias_type_name(&source.checking, type_id, &mut BTreeSet::new())
                    });
            inaccessible.is_some_and(|name| !source_declares_type_name(source, &name))
        })
    })
}

fn source_declares_type_name(source: &SourceFile, expected: &str) -> bool {
    source.parse.arena.iter().any(|(_, node)| {
        let name = match &node.data {
            NodeData::TypeAliasDeclaration(declaration) => Some(declaration.name),
            NodeData::InterfaceDeclaration(declaration) => Some(declaration.name),
            NodeData::ClassDeclaration(declaration) => declaration.name,
            NodeData::EnumDeclaration(declaration) => Some(declaration.name),
            _ => None,
        };
        name.and_then(|name| identifier_text(&source.parse.arena, name)) == Some(expected)
    })
}

fn leftmost_entity_identifier(arena: &ts_ast::NodeArena, entity: NodeId) -> Option<(NodeId, &str)> {
    match &arena.get(entity)?.data {
        NodeData::Identifier(identifier) => Some((entity, &identifier.text)),
        NodeData::QualifiedName(name) => leftmost_entity_identifier(arena, name.left),
        NodeData::PropertyAccessExpression(access) => {
            leftmost_entity_identifier(arena, access.expression)
        }
        _ => None,
    }
}

fn declaration_is_nested_in_runtime_block(
    arena: &ts_ast::NodeArena,
    declaration: NodeId,
    source_file: NodeId,
) -> bool {
    let mut current = declaration;
    while let Some(parent) = arena.get(current).and_then(|node| node.parent) {
        if parent == source_file {
            return false;
        }
        if matches!(
            arena.get(parent).map(|node| &node.data),
            Some(NodeData::Block(_))
        ) {
            return true;
        }
        current = parent;
    }
    false
}

fn private_type_query_name(source: &SourceFile, root: NodeId) -> Option<String> {
    let root = source.parse.arena.get(root)?;
    source.parse.arena.iter().find_map(|(_, node)| {
        if node.range.start < root.range.start || node.range.end > root.range.end {
            return None;
        }
        let NodeData::TypeQueryNode(query) = &node.data else {
            return None;
        };
        let (identifier, name) = leftmost_entity_identifier(&source.parse.arena, query.expr_name)?;
        let symbol = source.binding.resolve_name_at(identifier, name)?;
        let symbol = source.binding.symbols.get(symbol)?;
        (!symbol.declarations.is_empty()
            && symbol.declarations.iter().all(|declaration| {
                declaration_is_nested_in_runtime_block(
                    &source.parse.arena,
                    *declaration,
                    source.parse.source_file,
                )
            }))
        .then(|| name.to_owned())
    })
}

fn emit_diagnostic(source_file: &SourceFile, error: &ts_printer::EmitError) -> ProgramDiagnostic {
    ProgramDiagnostic {
        file_name: Some(source_file.file_name.clone()),
        range: source_file
            .parse
            .arena
            .get(error.node)
            .map(|node| node.range),
        code: None,
        category: Category::Error,
        message: error.to_string(),
        related_information: Vec::new(),
    }
}

#[allow(clippy::too_many_lines)]
fn add_nonportable_inferred_type_diagnostics(source: &SourceFile, checking: &mut CheckResult) {
    let imports = source_import_bindings(source);
    let Some(NodeData::SourceFile(file)) = source
        .parse
        .arena
        .get(source.parse.source_file)
        .map(|node| &node.data)
    else {
        return;
    };
    for statement in &file.statements.nodes {
        let Some(NodeData::VariableStatement(variable)) =
            source.parse.arena.get(*statement).map(|node| &node.data)
        else {
            continue;
        };
        if !node_has_modifier(
            &source.parse.arena,
            variable.modifiers.as_ref(),
            ts_ast::SyntaxKind::ExportKeyword,
        ) {
            continue;
        }
        let Some(NodeData::VariableDeclarationList(list)) = source
            .parse
            .arena
            .get(variable.declaration_list)
            .map(|node| &node.data)
        else {
            continue;
        };
        for declaration_id in &list.declarations.nodes {
            let Some(NodeData::VariableDeclaration(declaration)) = source
                .parse
                .arena
                .get(*declaration_id)
                .map(|node| &node.data)
            else {
                continue;
            };
            if let Some(annotation) = declaration.type_
                && let Some(private_name) = private_type_query_name(source, annotation)
                && let Some(name) = identifier_text(&source.parse.arena, declaration.name)
            {
                let message =
                    message_by_code(4025).expect("TS4025 must be in the diagnostic catalog");
                checking.diagnostics.push(CheckDiagnostic {
                    node: declaration.name,
                    diagnostic: Diagnostic::with_arguments(
                        message,
                        [name.to_owned(), private_name],
                    ),
                });
                continue;
            }
            if declaration.type_.is_some() {
                continue;
            }
            if declaration.initializer.is_some_and(|initializer| {
                inferred_type_syntax_exceeds_serialization_limit(source, initializer)
            }) {
                let message =
                    message_by_code(7056).expect("TS7056 must be in the diagnostic catalog");
                checking.diagnostics.push(CheckDiagnostic {
                    node: declaration.name,
                    diagnostic: Diagnostic::new(message),
                });
                continue;
            }
            let Some(type_id) = checking.type_of_node(*declaration_id).or_else(|| {
                declaration
                    .initializer
                    .and_then(|node| checking.type_of_node(node))
            }) else {
                continue;
            };
            if identifier_text(&source.parse.arena, declaration.name) == Some("globalThis")
                && checking
                    .named_type_references
                    .get(&type_id)
                    .is_some_and(|reference| reference.name == "typeof globalThis")
            {
                let message =
                    message_by_code(4025).expect("TS4025 must be in the diagnostic catalog");
                checking.diagnostics.push(CheckDiagnostic {
                    node: declaration.name,
                    diagnostic: Diagnostic::with_arguments(message, ["globalThis", "globalThis"]),
                });
                continue;
            }
            let imported_computed_name_is_accessible =
                inaccessible_computed_symbol_name(checking, type_id, &mut BTreeSet::new())
                    .is_some_and(|qualifier| {
                        imports.iter().any(|(local, _, _)| local == &qualifier)
                    });
            if ((inaccessible_imported_unique_symbol(checking, type_id)
                && !imported_computed_name_is_accessible)
                || inferred_empty_object_from_imported_call(
                    source,
                    checking,
                    declaration.initializer,
                    type_id,
                ))
                && let Some(name) = identifier_text(&source.parse.arena, declaration.name)
            {
                let message =
                    message_by_code(2527).expect("TS2527 must be in the diagnostic catalog");
                checking.diagnostics.push(CheckDiagnostic {
                    node: declaration.name,
                    diagnostic: Diagnostic::with_arguments(
                        message,
                        [name.to_owned(), "unique symbol".into()],
                    ),
                });
                continue;
            }
            if let Some(qualifier) =
                inaccessible_computed_symbol_name(checking, type_id, &mut BTreeSet::new())
                && !imports.iter().any(|(local, _, _)| local == &qualifier)
                && let Some((_, _, module)) = imports.first()
                && let Some(name) = identifier_text(&source.parse.arena, declaration.name)
            {
                let message =
                    message_by_code(4023).expect("TS4023 must be in the diagnostic catalog");
                checking.diagnostics.push(CheckDiagnostic {
                    node: declaration.name,
                    diagnostic: Diagnostic::with_arguments(
                        message,
                        [
                            name.to_owned(),
                            qualifier,
                            format!("\"{}\"", module.trim_start_matches("./")),
                        ],
                    ),
                });
                continue;
            }
            let Some((qualifier, module)) =
                nonportable_import_type_reference(checking, type_id, &mut BTreeSet::new())
            else {
                continue;
            };
            let Some(name) = identifier_text(&source.parse.arena, declaration.name) else {
                continue;
            };
            let message = message_by_code(2883).expect("TS2883 must be in the diagnostic catalog");
            checking.diagnostics.push(CheckDiagnostic {
                node: declaration.name,
                diagnostic: Diagnostic::with_arguments(
                    message,
                    [name.to_owned(), qualifier, module],
                ),
            });
        }
    }

    let exported_functions = file
        .statements
        .nodes
        .iter()
        .filter_map(|statement| {
            let node = source.parse.arena.get(*statement)?;
            let NodeData::FunctionDeclaration(function) = &node.data else {
                return None;
            };
            node_has_modifier(
                &source.parse.arena,
                function.modifiers.as_ref(),
                ts_ast::SyntaxKind::ExportKeyword,
            )
            .then(|| {
                function
                    .name
                    .and_then(|name| identifier_text(&source.parse.arena, name))
            })
            .flatten()
        })
        .collect::<BTreeSet<_>>();
    for statement in &file.statements.nodes {
        let Some(NodeData::ExpressionStatement(statement)) =
            source.parse.arena.get(*statement).map(|node| &node.data)
        else {
            continue;
        };
        let Some(NodeData::BinaryExpression(assignment)) = source
            .parse
            .arena
            .get(statement.expression)
            .map(|node| &node.data)
        else {
            continue;
        };
        if source
            .parse
            .arena
            .get(assignment.operator_token)
            .is_none_or(|operator| operator.kind != ts_ast::SyntaxKind::EqualsToken)
        {
            continue;
        }
        let Some(NodeData::PropertyAccessExpression(access)) = source
            .parse
            .arena
            .get(assignment.left)
            .map(|node| &node.data)
        else {
            continue;
        };
        let Some(receiver) = identifier_text(&source.parse.arena, access.expression) else {
            continue;
        };
        if !exported_functions.contains(receiver) {
            continue;
        }
        let Some(NodeData::CallExpression(call)) = source
            .parse
            .arena
            .get(assignment.right)
            .map(|node| &node.data)
        else {
            continue;
        };
        let Some(callee) = identifier_text(&source.parse.arena, call.expression) else {
            continue;
        };
        let Some((_, _, module)) = imports.iter().find(|(local, _, _)| local == callee) else {
            continue;
        };
        let Some(type_id) = checking.type_of_node(assignment.right) else {
            continue;
        };
        let Some(private_name) =
            inaccessible_named_type_reference(checking, type_id, &mut BTreeSet::new())
        else {
            continue;
        };
        let Some(property) = identifier_text(&source.parse.arena, access.name) else {
            continue;
        };
        let message = message_by_code(4032).expect("TS4032 must be in the diagnostic catalog");
        checking.diagnostics.push(CheckDiagnostic {
            node: assignment.left,
            diagnostic: Diagnostic::with_arguments(
                message,
                [
                    property.to_owned(),
                    private_name,
                    format!("\"{}\"", module.trim_start_matches("./")),
                ],
            ),
        });
    }
}

fn inferred_empty_object_from_imported_call(
    source: &SourceFile,
    checking: &CheckResult,
    initializer: Option<NodeId>,
    type_id: TypeId,
) -> bool {
    if checking.import_type_references.contains_key(&type_id)
        || checking.named_type_references.contains_key(&type_id)
    {
        return false;
    }
    let Some(TypeKind::Object(object)) = checking.types.get(type_id).map(|type_| &type_.kind)
    else {
        return false;
    };
    if !object.properties.is_empty()
        || object.string_index_type.is_some()
        || object.number_index_type.is_some()
        || !object.call_signatures.is_empty()
        || !object.construct_signatures.is_empty()
    {
        return false;
    }
    let Some(NodeData::CallExpression(call)) = initializer
        .and_then(|initializer| source.parse.arena.get(initializer))
        .map(|node| &node.data)
    else {
        return false;
    };
    let Some(callee_type) = checking.type_of_node(call.expression) else {
        return false;
    };
    if nonportable_import_type_reference(checking, callee_type, &mut BTreeSet::new()).is_some() {
        return true;
    }
    let mut root = call.expression;
    while let Some(NodeData::PropertyAccessExpression(access)) =
        source.parse.arena.get(root).map(|node| &node.data)
    {
        root = access.expression;
    }
    let Some(root_name) = identifier_text(&source.parse.arena, root) else {
        return false;
    };
    source_import_bindings(source)
        .iter()
        .any(|(local, _, _)| local == root_name)
}

fn inaccessible_imported_unique_symbol(checking: &CheckResult, type_id: TypeId) -> bool {
    fn visit(
        checking: &CheckResult,
        type_id: TypeId,
        imported: bool,
        visited: &mut BTreeSet<TypeId>,
    ) -> bool {
        if !visited.insert(type_id) {
            return false;
        }
        let imported = imported
            || checking.import_type_references.contains_key(&type_id)
            || checking
                .named_type_references
                .get(&type_id)
                .is_some_and(|reference| reference.name.starts_with("import("));
        let Some(kind) = checking.types.get(type_id).map(|type_| &type_.kind) else {
            return false;
        };
        match kind {
            TypeKind::Object(object) => {
                if imported
                    && (object.properties.keys().any(|name| name.starts_with("[#"))
                        || object.readonly_properties.iter().any(|name| {
                            object.properties.get(name).is_some_and(|property| {
                                matches!(
                                    checking.types.get(*property).map(|type_| &type_.kind),
                                    Some(TypeKind::Unknown)
                                )
                            })
                        }))
                {
                    return true;
                }
                object
                    .properties
                    .values()
                    .copied()
                    .chain(object.string_index_type)
                    .chain(object.number_index_type)
                    .any(|part| visit(checking, part, imported, visited))
            }
            TypeKind::Array(element) => visit(checking, *element, imported, visited),
            TypeKind::Tuple(elements)
            | TypeKind::ReadonlyTuple(elements)
            | TypeKind::Union(elements)
            | TypeKind::Intersection(elements) => elements
                .iter()
                .any(|part| visit(checking, *part, imported, visited)),
            TypeKind::Function(signature) | TypeKind::Constructor(signature) => signature
                .parameters
                .iter()
                .copied()
                .chain(signature.rest_parameter)
                .chain(std::iter::once(signature.return_type))
                .any(|part| visit(checking, part, imported, visited)),
            TypeKind::Overload(signatures) => signatures.iter().any(|signature| {
                signature
                    .parameters
                    .iter()
                    .copied()
                    .chain(signature.rest_parameter)
                    .chain(std::iter::once(signature.return_type))
                    .any(|part| visit(checking, part, imported, visited))
            }),
            _ => false,
        }
    }

    visit(checking, type_id, false, &mut BTreeSet::new())
}

const MAX_INFERRED_TYPE_SYNTAX_COMPLEXITY: usize = 1_000_000;

fn inferred_type_syntax_exceeds_serialization_limit(
    source: &SourceFile,
    initializer: NodeId,
) -> bool {
    let Some(NodeData::SourceFile(file)) = source
        .parse
        .arena
        .get(source.parse.source_file)
        .map(|node| &node.data)
    else {
        return false;
    };
    let aliases = file
        .statements
        .nodes
        .iter()
        .filter_map(|statement| {
            let NodeData::TypeAliasDeclaration(alias) = &source.parse.arena.get(*statement)?.data
            else {
                return None;
            };
            Some((
                identifier_text(&source.parse.arena, alias.name)?.to_owned(),
                alias.type_,
            ))
        })
        .collect::<BTreeMap<_, _>>();
    source.parse.arena.iter().any(|(candidate, node)| {
        if !syntax_node_is_within(&source.parse.arena, candidate, initializer) {
            return false;
        }
        let asserted_type = match &node.data {
            NodeData::AsExpression(assertion) => Some(assertion.type_),
            NodeData::TypeAssertion(assertion) => Some(assertion.type_),
            _ => None,
        };
        asserted_type.is_some_and(|type_node| {
            estimated_type_syntax_complexity(
                &source.parse.arena,
                type_node,
                &aliases,
                &mut HashSet::new(),
            ) > MAX_INFERRED_TYPE_SYNTAX_COMPLEXITY
        })
    })
}

fn syntax_node_is_within(arena: &ts_ast::NodeArena, node: NodeId, ancestor: NodeId) -> bool {
    let mut current = Some(node);
    while let Some(id) = current {
        if id == ancestor {
            return true;
        }
        current = arena.get(id).and_then(|node| node.parent);
    }
    false
}

fn estimated_type_syntax_complexity(
    arena: &ts_ast::NodeArena,
    type_node: NodeId,
    aliases: &BTreeMap<String, NodeId>,
    visiting: &mut HashSet<NodeId>,
) -> usize {
    if !visiting.insert(type_node) {
        return 1;
    }
    let cap = MAX_INFERRED_TYPE_SYNTAX_COMPLEXITY.saturating_add(1);
    let add = |left: usize, right: usize| left.saturating_add(right).min(cap);
    let multiply = |left: usize, right: usize| left.saturating_mul(right).min(cap);
    let complexity = match arena.get(type_node).map(|node| &node.data) {
        Some(NodeData::UnionTypeNode(union)) => {
            union.types.nodes.iter().fold(0, |total, member| {
                add(
                    total,
                    estimated_type_syntax_complexity(arena, *member, aliases, visiting),
                )
            })
        }
        Some(NodeData::IntersectionTypeNode(intersection)) => {
            intersection.types.nodes.iter().fold(0, |total, member| {
                add(
                    total,
                    estimated_type_syntax_complexity(arena, *member, aliases, visiting),
                )
            })
        }
        Some(NodeData::TemplateLiteralTypeNode(template)) => template
            .template_spans
            .nodes
            .iter()
            .filter_map(|span| match &arena.get(*span)?.data {
                NodeData::TemplateLiteralTypeSpan(span) => Some(span.type_),
                _ => None,
            })
            .fold(1, |total, span| {
                multiply(
                    total,
                    estimated_type_syntax_complexity(arena, span, aliases, visiting),
                )
            }),
        Some(NodeData::MappedTypeNode(mapped)) => {
            let keys = arena
                .get(mapped.type_parameter)
                .and_then(|parameter| match &parameter.data {
                    NodeData::TypeParameterDeclaration(parameter) => parameter.constraint,
                    _ => None,
                })
                .map_or(1, |constraint| {
                    estimated_type_syntax_complexity(arena, constraint, aliases, visiting)
                });
            let value = mapped.type_.map_or(1, |value| {
                estimated_type_syntax_complexity(arena, value, aliases, visiting)
            });
            multiply(multiply(keys, value), 8)
        }
        Some(NodeData::TypeReferenceNode(reference)) => {
            let alias = identifier_text(arena, reference.type_name)
                .and_then(|name| aliases.get(name))
                .copied();
            alias.map_or(1, |alias| {
                estimated_type_syntax_complexity(arena, alias, aliases, visiting)
            })
        }
        Some(NodeData::ParenthesizedTypeNode(parenthesized)) => {
            estimated_type_syntax_complexity(arena, parenthesized.type_, aliases, visiting)
        }
        Some(NodeData::ArrayTypeNode(array)) => {
            estimated_type_syntax_complexity(arena, array.element_type, aliases, visiting)
        }
        Some(NodeData::TypeOperatorNode(operator)) => {
            estimated_type_syntax_complexity(arena, operator.type_, aliases, visiting)
        }
        _ => 1,
    };
    visiting.remove(&type_node);
    complexity
}

fn source_import_bindings(source: &SourceFile) -> Vec<(String, String, String)> {
    let Some(NodeData::SourceFile(file)) = source
        .parse
        .arena
        .get(source.parse.source_file)
        .map(|node| &node.data)
    else {
        return Vec::new();
    };
    let mut imports = Vec::new();
    for statement in &file.statements.nodes {
        let Some(NodeData::ImportDeclaration(import)) =
            source.parse.arena.get(*statement).map(|node| &node.data)
        else {
            continue;
        };
        let Some((specifier, _)) = string_literal(&source.parse.arena, import.module_specifier)
        else {
            continue;
        };
        let Some(NodeData::ImportClause(clause)) = import
            .import_clause
            .and_then(|clause| source.parse.arena.get(clause))
            .map(|node| &node.data)
        else {
            continue;
        };
        if let Some(local) = clause
            .name
            .and_then(|name| identifier_text(&source.parse.arena, name))
        {
            imports.push((local.to_owned(), "default".into(), specifier.clone()));
        }
        if let Some(NodeData::NamespaceImport(namespace)) = clause
            .named_bindings
            .and_then(|bindings| source.parse.arena.get(bindings))
            .map(|node| &node.data)
            && let Some(local) = identifier_text(&source.parse.arena, namespace.name)
        {
            imports.push((local.to_owned(), "*".into(), specifier.clone()));
        }
        let Some(NodeData::NamedImports(named)) = clause
            .named_bindings
            .and_then(|bindings| source.parse.arena.get(bindings))
            .map(|node| &node.data)
        else {
            continue;
        };
        for element in &named.elements.nodes {
            let Some(NodeData::ImportSpecifier(imported)) =
                source.parse.arena.get(*element).map(|node| &node.data)
            else {
                continue;
            };
            let Some(local) = identifier_text(&source.parse.arena, imported.name) else {
                continue;
            };
            let imported_name = imported
                .property_name
                .and_then(|name| identifier_text(&source.parse.arena, name))
                .unwrap_or(local);
            imports.push((
                local.to_owned(),
                imported_name.to_owned(),
                specifier.clone(),
            ));
        }
    }
    imports
}

fn imported_call_target(
    source: &SourceFile,
    initializer: NodeId,
) -> Option<(String, Option<String>)> {
    let NodeData::CallExpression(call) = &source.parse.arena.get(initializer)?.data else {
        return None;
    };
    match &source.parse.arena.get(call.expression)?.data {
        NodeData::Identifier(identifier) => Some((identifier.text.clone(), None)),
        NodeData::PropertyAccessExpression(access) => Some((
            identifier_text(&source.parse.arena, access.expression)?.to_owned(),
            Some(identifier_text(&source.parse.arena, access.name)?.to_owned()),
        )),
        _ => None,
    }
}

fn imported_function_mapped_symbol_property(
    source: &SourceFile,
    function_name: &str,
) -> Option<String> {
    let return_name = source.parse.arena.iter().find_map(|(_, node)| {
        let NodeData::FunctionDeclaration(function) = &node.data else {
            return None;
        };
        (function
            .name
            .and_then(|name| identifier_text(&source.parse.arena, name))
            == Some(function_name))
        .then(|| {
            let NodeData::TypeQueryNode(query) = &source.parse.arena.get(function.type_?)?.data
            else {
                return None;
            };
            identifier_text(&source.parse.arena, query.expr_name).map(str::to_owned)
        })
        .flatten()
    })?;
    source.parse.arena.iter().find_map(|(_, node)| {
        let NodeData::VariableDeclaration(variable) = &node.data else {
            return None;
        };
        if identifier_text(&source.parse.arena, variable.name) != Some(&return_name) {
            return None;
        }
        let NodeData::MappedTypeNode(mapped) = &source.parse.arena.get(variable.type_?)?.data
        else {
            return None;
        };
        let NodeData::TypeParameterDeclaration(parameter) =
            &source.parse.arena.get(mapped.type_parameter)?.data
        else {
            return None;
        };
        let NodeData::TypeQueryNode(query) = &source.parse.arena.get(parameter.constraint?)?.data
        else {
            return None;
        };
        identifier_text(&source.parse.arena, query.expr_name).map(str::to_owned)
    })
}

fn export_assignment_is_object_assign(source: &SourceFile, expression: NodeId) -> bool {
    let Some(NodeData::CallExpression(call)) =
        source.parse.arena.get(expression).map(|node| &node.data)
    else {
        return false;
    };
    matches!(
        source.parse.arena.get(call.expression).map(|node| &node.data),
        Some(NodeData::PropertyAccessExpression(access))
            if identifier_text(&source.parse.arena, access.expression) == Some("Object")
                && identifier_text(&source.parse.arena, access.name) == Some("assign")
    )
}

fn nested_namespace_import_reference(
    program: &Program,
    target: &SourceFile,
) -> Option<(String, String)> {
    let containing = canonicalize(
        &target.file_name,
        &program.current_directory,
        program.case_sensitivity,
    );
    source_import_bindings(target)
        .into_iter()
        .filter(|(_, imported, _)| imported == "*")
        .find_map(|(local, _, specifier)| {
            let resolved = program.resolved_modules.get(&ResolvedModuleKey::new(
                containing.clone(),
                specifier,
                program.canonical_emit_module_mode(target),
            ))?;
            if resolved.match_indices("/node_modules/").count() < 2 {
                return None;
            }
            let qualifier = target.parse.arena.iter().find_map(|(_, node)| {
                let NodeData::QualifiedName(name) = &node.data else {
                    return None;
                };
                (identifier_text(&target.parse.arena, name.left) == Some(&local))
                    .then(|| identifier_text(&target.parse.arena, name.right).map(str::to_owned))
                    .flatten()
            })?;
            let relative = resolved.split_once("/node_modules/")?.1;
            let module = ts_path::remove_file_extension(relative)
                .trim_end_matches("/index")
                .to_owned();
            Some((qualifier, module))
        })
}

fn nonportable_return_import(
    program: &Program,
    target: &SourceFile,
    function_name: &str,
) -> Option<(String, String)> {
    let containing = canonicalize(
        &target.file_name,
        &program.current_directory,
        program.case_sensitivity,
    );
    let nested_imports = source_import_bindings(target)
        .into_iter()
        .filter_map(|(local, imported, specifier)| {
            let resolved = program.resolved_modules.get(&ResolvedModuleKey::new(
                containing.clone(),
                specifier,
                program.canonical_emit_module_mode(target),
            ))?;
            (resolved.match_indices("/node_modules/").count() >= 2).then(|| {
                let relative = resolved.split_once("/node_modules/").unwrap().1;
                let module = ts_path::remove_file_extension(relative)
                    .trim_end_matches("/index")
                    .to_owned();
                (local, imported, module)
            })
        })
        .collect::<Vec<_>>();
    if nested_imports.is_empty() {
        return None;
    }
    let Some(NodeData::SourceFile(file)) = target
        .parse
        .arena
        .get(target.parse.source_file)
        .map(|node| &node.data)
    else {
        return None;
    };
    for statement in &file.statements.nodes {
        let Some(NodeData::FunctionDeclaration(function)) =
            target.parse.arena.get(*statement).map(|node| &node.data)
        else {
            continue;
        };
        if function
            .name
            .and_then(|name| identifier_text(&target.parse.arena, name))
            != Some(function_name)
        {
            continue;
        }
        let type_node = target.parse.arena.get(function.type_?)?;
        return nested_imports.iter().find_map(|(local, imported, module)| {
            target.parse.arena.iter().find_map(|(_, node)| {
                (type_node.range.start <= node.range.start
                    && node.range.end <= type_node.range.end
                    && matches!(
                        &node.data,
                        NodeData::Identifier(identifier) if identifier.text == *local
                    ))
                .then(|| (imported.clone(), module.clone()))
            })
        });
    }
    None
}

fn nonportable_import_type_reference(
    checking: &CheckResult,
    type_id: TypeId,
    visited: &mut BTreeSet<TypeId>,
) -> Option<(String, String)> {
    if !visited.insert(type_id) {
        return None;
    }
    if let Some(reference) = checking.import_type_references.get(&type_id)
        && reference.module_specifier.contains("/node_modules/")
    {
        return Some((
            reference.qualifier.clone(),
            reference.module_specifier.clone(),
        ));
    }
    if let Some(reference) = checking.named_type_references.get(&type_id)
        && let Some(nonportable) = reference
            .type_arguments
            .iter()
            .find_map(|argument| nonportable_import_type_reference(checking, *argument, visited))
    {
        return Some(nonportable);
    }
    let kind = &checking.types.get(type_id)?.kind;
    let mut children = Vec::new();
    match kind {
        TypeKind::TypeParameter { constraint, .. } => children.extend(constraint),
        TypeKind::Array(element) => children.push(*element),
        TypeKind::Tuple(elements)
        | TypeKind::ReadonlyTuple(elements)
        | TypeKind::Union(elements)
        | TypeKind::Intersection(elements) => children.extend(elements),
        TypeKind::Object(object) => {
            children.extend(object.properties.values());
            children.extend(object.string_index_type);
            children.extend(object.number_index_type);
            for signature in object
                .call_signatures
                .iter()
                .chain(&object.construct_signatures)
            {
                children.extend(&signature.parameters);
                children.extend(signature.rest_parameter);
                children.push(signature.return_type);
            }
        }
        TypeKind::Function(signature) | TypeKind::Constructor(signature) => {
            children.extend(&signature.parameters);
            children.extend(signature.rest_parameter);
            children.push(signature.return_type);
        }
        TypeKind::Overload(signatures) => {
            for signature in signatures {
                children.extend(&signature.parameters);
                children.extend(signature.rest_parameter);
                children.push(signature.return_type);
            }
        }
        _ => {}
    }
    children
        .into_iter()
        .find_map(|child| nonportable_import_type_reference(checking, child, visited))
}

fn inaccessible_computed_symbol_name(
    checking: &CheckResult,
    type_id: TypeId,
    visited: &mut BTreeSet<TypeId>,
) -> Option<String> {
    if !visited.insert(type_id) {
        return None;
    }
    let kind = &checking.types.get(type_id)?.kind;
    let mut children = Vec::new();
    match kind {
        TypeKind::TypeParameter { constraint, .. } => children.extend(constraint),
        TypeKind::Array(element) => children.push(*element),
        TypeKind::Tuple(elements)
        | TypeKind::ReadonlyTuple(elements)
        | TypeKind::Union(elements)
        | TypeKind::Intersection(elements) => children.extend(elements),
        TypeKind::Object(object) => {
            if let Some(name) = object.properties.keys().find_map(|name| {
                name.strip_prefix("[#")
                    .and_then(|name| name.strip_suffix(']'))
                    .and_then(|name| name.split('.').next())
                    .map(str::to_owned)
            }) {
                return Some(name);
            }
            children.extend(object.properties.values());
            children.extend(object.string_index_type);
            children.extend(object.number_index_type);
        }
        TypeKind::Function(signature) | TypeKind::Constructor(signature) => {
            children.extend(&signature.parameters);
            children.extend(signature.rest_parameter);
            children.push(signature.return_type);
        }
        TypeKind::Overload(signatures) => {
            for signature in signatures {
                children.extend(&signature.parameters);
                children.extend(signature.rest_parameter);
                children.push(signature.return_type);
            }
        }
        _ => {}
    }
    children
        .into_iter()
        .find_map(|child| inaccessible_computed_symbol_name(checking, child, visited))
}

fn inaccessible_named_type_reference(
    checking: &CheckResult,
    type_id: TypeId,
    visited: &mut BTreeSet<TypeId>,
) -> Option<String> {
    if !visited.insert(type_id) || checking.import_type_references.contains_key(&type_id) {
        return None;
    }
    if let Some(reference) = checking.named_type_references.get(&type_id)
        && !is_global_library_type_name(&reference.name)
    {
        return Some(reference.name.clone());
    }
    let kind = &checking.types.get(type_id)?.kind;
    let mut children = Vec::new();
    match kind {
        TypeKind::TypeParameter { constraint, .. } => children.extend(constraint),
        TypeKind::Array(element) => children.push(*element),
        TypeKind::Tuple(elements)
        | TypeKind::ReadonlyTuple(elements)
        | TypeKind::Union(elements)
        | TypeKind::Intersection(elements) => children.extend(elements),
        TypeKind::Object(object) => {
            children.extend(object.properties.values());
            children.extend(object.string_index_type);
            children.extend(object.number_index_type);
        }
        TypeKind::Function(signature) | TypeKind::Constructor(signature) => {
            children.extend(&signature.parameters);
            children.extend(signature.rest_parameter);
            children.push(signature.return_type);
        }
        TypeKind::Overload(signatures) => {
            for signature in signatures {
                children.extend(&signature.parameters);
                children.extend(signature.rest_parameter);
                children.push(signature.return_type);
            }
        }
        _ => {}
    }
    children
        .into_iter()
        .find_map(|child| inaccessible_named_type_reference(checking, child, visited))
}

fn is_global_library_type_name(name: &str) -> bool {
    matches!(
        name,
        "Array"
            | "ReadonlyArray"
            | "Promise"
            | "PromiseLike"
            | "PromiseConstructor"
            | "String"
            | "StringConstructor"
            | "Number"
            | "Boolean"
            | "Object"
            | "Function"
            | "CallableFunction"
            | "NewableFunction"
            | "IArguments"
            | "Record"
            | "Omit"
            | "Pick"
            | "Partial"
            | "Required"
            | "Readonly"
            | "Exclude"
            | "Extract"
            | "NonNullable"
            | "Parameters"
            | "ConstructorParameters"
            | "ReturnType"
            | "InstanceType"
    )
}

fn cyclic_alias_type_name(
    checking: &CheckResult,
    type_id: TypeId,
    visited: &mut BTreeSet<TypeId>,
) -> Option<String> {
    if !visited.insert(type_id) {
        return None;
    }
    let kind = &checking.types.get(type_id)?.kind;
    if let TypeKind::TypeParameter { name, .. } = kind
        && let Some(name) = name.strip_prefix("__cyclic_alias__")
    {
        return Some(name.to_owned());
    }
    let mut children = Vec::new();
    match kind {
        TypeKind::TypeParameter { constraint, .. } => children.extend(constraint),
        TypeKind::Array(element) => children.push(*element),
        TypeKind::Tuple(elements)
        | TypeKind::ReadonlyTuple(elements)
        | TypeKind::Union(elements)
        | TypeKind::Intersection(elements) => children.extend(elements),
        TypeKind::Object(object) => {
            children.extend(object.properties.values());
            children.extend(object.string_index_type);
            children.extend(object.number_index_type);
            for signature in object
                .call_signatures
                .iter()
                .chain(&object.construct_signatures)
            {
                children.extend(&signature.parameters);
                children.extend(signature.rest_parameter);
                children.push(signature.return_type);
            }
        }
        TypeKind::Function(signature) | TypeKind::Constructor(signature) => {
            children.extend(&signature.parameters);
            children.extend(signature.rest_parameter);
            children.push(signature.return_type);
        }
        TypeKind::Overload(signatures) => {
            for signature in signatures {
                children.extend(&signature.parameters);
                children.extend(signature.rest_parameter);
                children.push(signature.return_type);
            }
        }
        _ => {}
    }
    children
        .into_iter()
        .find_map(|child| cyclic_alias_type_name(checking, child, visited))
}

fn enum_values_for_emit(
    values: &BTreeMap<NodeId, CheckerConstantValue>,
) -> BTreeMap<NodeId, EmitConstantValue> {
    values
        .iter()
        .map(|(node, value)| {
            let value = match value {
                CheckerConstantValue::Number(value) => EmitConstantValue::Number(*value),
                CheckerConstantValue::String(value) => EmitConstantValue::String(value.clone()),
            };
            (*node, value)
        })
        .collect()
}

fn declaration_node_types_for_emit(
    source: &SourceFile,
    strict_null_checks: bool,
) -> BTreeMap<NodeId, ts_checker::TypeId> {
    let mut node_types = source.checking.node_types.clone();
    for (id, node) in source.parse.arena.iter() {
        if !strict_null_checks
            && let NodeData::ParameterDeclaration(parameter) = &node.data
            && parameter.type_.is_none()
            && let Some(initializer) = parameter.initializer
            && source
                .parse
                .arena
                .get(initializer)
                .is_some_and(|initializer| initializer.kind == ts_ast::SyntaxKind::NullKeyword)
        {
            node_types.insert(initializer, source.checking.types.any());
        }
        if let NodeData::Identifier(identifier) = &node.data
            && !node_types.contains_key(&id)
            && let Some(type_id) = source
                .binding
                .resolve_name_at(id, &identifier.text)
                .and_then(|symbol| source.checking.type_of_symbol(symbol))
        {
            node_types.insert(id, type_id);
        }
        if let NodeData::MethodDeclaration(method) = &node.data
            && !node_types.contains_key(&id)
            && let Some(name) = identifier_text(&source.parse.arena, method.name)
            && let Some(class_symbol) = node
                .parent
                .and_then(|class| source.binding.node_symbols.get(&class).copied())
            && let Some(class_type) = source.checking.type_of_symbol(class_symbol)
            && let Some(type_id) =
                source
                    .checking
                    .types
                    .get(class_type)
                    .and_then(|type_| match &type_.kind {
                        ts_checker::TypeKind::Object(object) => {
                            object.properties.get(name).copied()
                        }
                        _ => None,
                    })
        {
            node_types.insert(id, type_id);
        }
        if !matches!(node.data, NodeData::FunctionDeclaration(_)) || node_types.contains_key(&id) {
            continue;
        }
        let Some(type_id) = source
            .binding
            .node_symbols
            .get(&id)
            .and_then(|symbol| source.checking.type_of_symbol(*symbol))
        else {
            continue;
        };
        node_types.insert(id, type_id);
    }
    node_types
}

fn is_javascript_file_name(file_name: &str) -> bool {
    matches!(
        ts_path::script_kind_from_path(file_name),
        ts_path::ScriptKind::Js | ts_path::ScriptKind::Jsx
    )
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum PrivateImportHelper {
    Get,
    Set,
}

impl PrivateImportHelper {
    const fn name(self) -> &'static str {
        match self {
            Self::Get => "__classPrivateFieldGet",
            Self::Set => "__classPrivateFieldSet",
        }
    }

    const fn required_parameters(self) -> usize {
        match self {
            Self::Get => 4,
            Self::Set => 5,
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum PrivateHelperAssignmentKind {
    None,
    Definite,
    Compound,
}

fn private_helper_assignment_kind(
    arena: &ts_ast::NodeArena,
    access: NodeId,
) -> PrivateHelperAssignmentKind {
    let mut current = access;
    while let Some(parent) = arena.get(current).and_then(|node| node.parent) {
        let Some(node) = arena.get(parent) else {
            return PrivateHelperAssignmentKind::None;
        };
        let object_target = match &node.data {
            NodeData::PropertyAssignment(property) => property.initializer == current,
            NodeData::ShorthandPropertyAssignment(property) => property.name == current,
            NodeData::SpreadAssignment(spread) => spread.expression == current,
            _ => false,
        };
        if object_target {
            let Some(object) = node.parent else {
                return PrivateHelperAssignmentKind::None;
            };
            current = object;
            continue;
        }
        match &node.data {
            NodeData::BinaryExpression(binary) if binary.left == current => {
                let Some(operator) = arena.get(binary.operator_token).map(|node| node.kind) else {
                    return PrivateHelperAssignmentKind::None;
                };
                return if matches!(
                    operator,
                    SyntaxKind::EqualsToken
                        | SyntaxKind::AmpersandAmpersandEqualsToken
                        | SyntaxKind::BarBarEqualsToken
                        | SyntaxKind::QuestionQuestionEqualsToken
                ) {
                    PrivateHelperAssignmentKind::Definite
                } else if operator.is_assignment_operator() {
                    PrivateHelperAssignmentKind::Compound
                } else {
                    PrivateHelperAssignmentKind::None
                };
            }
            NodeData::PrefixUnaryExpression(unary)
                if unary.operand == current
                    && matches!(
                        unary.operator,
                        SyntaxKind::PlusPlusToken | SyntaxKind::MinusMinusToken
                    ) =>
            {
                return PrivateHelperAssignmentKind::Compound;
            }
            NodeData::PostfixUnaryExpression(unary)
                if unary.operand == current
                    && matches!(
                        unary.operator,
                        SyntaxKind::PlusPlusToken | SyntaxKind::MinusMinusToken
                    ) =>
            {
                return PrivateHelperAssignmentKind::Compound;
            }
            NodeData::ForInOrOfStatement(statement) if statement.initializer == current => {
                return PrivateHelperAssignmentKind::Definite;
            }
            NodeData::ParenthesizedExpression(wrapper) if wrapper.expression == current => {}
            NodeData::NonNullExpression(wrapper) if wrapper.expression == current => {}
            NodeData::ArrayLiteralExpression(array) if array.elements.nodes.contains(&current) => {}
            NodeData::SpreadElement(spread) if spread.expression == current => {}
            _ => return PrivateHelperAssignmentKind::None,
        }
        current = parent;
    }
    PrivateHelperAssignmentKind::None
}

fn strict_reserved_identifier_is_name(arena: &ts_ast::NodeArena, id: NodeId) -> bool {
    let Some(parent) = arena
        .get(id)
        .and_then(|node| node.parent)
        .and_then(|parent| arena.get(parent))
    else {
        return false;
    };
    match &parent.data {
        NodeData::PropertyDeclaration(data) => data.name == id,
        NodeData::PropertySignatureDeclaration(data) => data.name == id,
        NodeData::MethodDeclaration(data) => data.name == id,
        NodeData::MethodSignatureDeclaration(data) => data.name == id,
        NodeData::GetAccessorDeclaration(data) => data.name == id,
        NodeData::SetAccessorDeclaration(data) => data.name == id,
        NodeData::EnumMember(data) => data.name == id,
        NodeData::PropertyAssignment(data) => data.name == id,
        NodeData::PropertyAccessExpression(data) => data.name == id,
        NodeData::QualifiedName(data) => data.right == id,
        NodeData::BindingElement(data) => data.property_name == Some(id),
        NodeData::ImportSpecifier(data) => data.property_name == Some(id),
        NodeData::ExportSpecifier(_)
        | NodeData::JsxAttribute(_)
        | NodeData::JsxSelfClosingElement(_)
        | NodeData::JsxOpeningElement(_)
        | NodeData::JsxClosingElement(_) => true,
        _ => false,
    }
}

fn private_helper_access_is_ambient(arena: &ts_ast::NodeArena, access: NodeId) -> bool {
    let mut current = access;
    let mut child = None;
    loop {
        let Some(node) = arena.get(current) else {
            return false;
        };
        let modifiers = match &node.data {
            NodeData::PropertyDeclaration(property) => property.modifiers.as_ref(),
            NodeData::MethodDeclaration(method) => method.modifiers.as_ref(),
            _ => declaration_modifiers(node),
        };
        // The pinned parser starts ambient context after parsing modifiers.
        // Decorator expressions keep the outer context.
        if node_has_modifier(arena, modifiers, SyntaxKind::DeclareKeyword)
            && !child.is_some_and(|child| {
                modifiers.is_some_and(|modifiers| modifiers.list.nodes.contains(&child))
            })
        {
            return true;
        }
        let Some(parent) = node.parent else {
            return false;
        };
        child = Some(current);
        current = parent;
    }
}

fn source_is_external_module(source: &SourceFile) -> bool {
    let lower = source.file_name.to_ascii_lowercase();
    if [".mts", ".cts", ".mjs", ".cjs"]
        .iter()
        .any(|extension| lower.ends_with(extension))
    {
        return true;
    }
    if !source.binding.exports.is_empty() {
        return true;
    }
    let Some(NodeData::SourceFile(file)) = source
        .parse
        .arena
        .get(source.parse.source_file)
        .map(|node| &node.data)
    else {
        return false;
    };
    file.statements.nodes.iter().any(|statement| {
        match source.parse.arena.get(*statement).map(|node| &node.data) {
            Some(
                NodeData::ImportDeclaration(_)
                | NodeData::ExportDeclaration(_)
                | NodeData::ExportAssignment(_),
            ) => true,
            Some(NodeData::ImportEqualsDeclaration(import)) => matches!(
                source
                    .parse
                    .arena
                    .get(import.module_reference)
                    .map(|node| &node.data),
                Some(NodeData::ExternalModuleReference(_))
            ),
            _ => false,
        }
    })
}

fn import_binding_is_const_enum(source: &SourceFile, binding: NodeId) -> bool {
    source
        .binding
        .node_symbols
        .get(&binding)
        .and_then(|symbol| source.checking.symbol_types.get(symbol))
        .is_some_and(|type_id| source.checking.const_enum_types.contains(type_id))
}

fn import_declaration_binds_const_enum(
    source: &SourceFile,
    import: &ts_ast::ImportDeclarationData,
) -> bool {
    import
        .import_clause
        .and_then(|clause| source.parse.arena.get(clause))
        .and_then(|node| match &node.data {
            NodeData::ImportClause(clause) => Some(clause),
            _ => None,
        })
        .is_some_and(|clause| {
            clause
                .name
                .is_some_and(|name| import_binding_is_const_enum(source, name))
                || clause.named_bindings.is_some_and(|bindings| {
                    match source.parse.arena.get(bindings).map(|node| &node.data) {
                        Some(NodeData::NamedImports(imports)) => {
                            imports.elements.nodes.iter().any(|specifier| {
                                matches!(
                                    source.parse.arena.get(*specifier).map(|node| &node.data),
                                    Some(NodeData::ImportSpecifier(specifier))
                                        if import_binding_is_const_enum(source, specifier.name)
                                )
                            })
                        }
                        _ => false,
                    }
                })
        })
}

fn preserve_classic_jsx_factory_import(
    source: &SourceFile,
    meanings: &mut BTreeMap<NodeId, bool>,
    factory: &str,
) {
    let Some(factory_root) = factory.split('.').next() else {
        return;
    };
    let Some(NodeData::SourceFile(file)) = source
        .parse
        .arena
        .get(source.parse.source_file)
        .map(|node| &node.data)
    else {
        return;
    };
    for statement in &file.statements.nodes {
        let Some(NodeData::ImportDeclaration(import)) =
            source.parse.arena.get(*statement).map(|node| &node.data)
        else {
            continue;
        };
        let Some(NodeData::ImportClause(clause)) = import
            .import_clause
            .and_then(|clause| source.parse.arena.get(clause))
            .map(|node| &node.data)
        else {
            continue;
        };
        let binds_factory = clause
            .name
            .and_then(|name| identifier_text(&source.parse.arena, name))
            == Some(factory_root)
            || clause.named_bindings.is_some_and(|bindings| {
                match source.parse.arena.get(bindings).map(|node| &node.data) {
                    Some(NodeData::NamespaceImport(namespace)) => {
                        identifier_text(&source.parse.arena, namespace.name) == Some(factory_root)
                    }
                    Some(NodeData::NamedImports(imports)) => {
                        imports.elements.nodes.iter().any(|specifier| {
                            matches!(
                                source.parse.arena.get(*specifier).map(|node| &node.data),
                                Some(NodeData::ImportSpecifier(specifier))
                                    if identifier_text(&source.parse.arena, specifier.name)
                                        == Some(factory_root)
                            )
                        })
                    }
                    _ => false,
                }
            });
        if binds_factory {
            meanings.insert(*statement, true);
        }
    }
}

fn import_equals_name<'a>(
    source: &'a SourceFile,
    import: &ts_ast::ImportEqualsDeclarationData,
) -> Option<&'a str> {
    match &source.parse.arena.get(import.name)?.data {
        NodeData::Identifier(identifier) => Some(&identifier.text),
        _ => None,
    }
}

fn import_equals_has_inlined_const_enum_access(source: &SourceFile, import_name: &str) -> bool {
    source.checking.enum_access_values.keys().any(|access| {
        let mut current = *access;
        loop {
            match source.parse.arena.get(current).map(|node| &node.data) {
                Some(NodeData::PropertyAccessExpression(access)) => current = access.expression,
                Some(NodeData::ElementAccessExpression(access)) => current = access.expression,
                Some(NodeData::Identifier(identifier)) => break identifier.text == import_name,
                _ => break false,
            }
        }
    })
}

fn import_runtime_meanings_for_emit(
    source: &SourceFile,
    preserve_const_enums: bool,
    amd: bool,
    later_script_variable_names: &HashSet<String>,
) -> BTreeMap<NodeId, bool> {
    let mut meanings = source.checking.import_runtime_meanings.clone();
    let Some(NodeData::SourceFile(file)) = source
        .parse
        .arena
        .get(source.parse.source_file)
        .map(|node| &node.data)
    else {
        return meanings;
    };
    let runtime_identifier_uses =
        amd.then(|| runtime_identifier_uses(&source.parse.arena, source.parse.source_file));
    for statement in &file.statements.nodes {
        if let Some(NodeData::ImportDeclaration(import)) =
            source.parse.arena.get(*statement).map(|node| &node.data)
        {
            if preserve_const_enums && import_declaration_binds_const_enum(source, import) {
                meanings.insert(*statement, true);
            }
            continue;
        }
        if !amd {
            if let Some(NodeData::ImportEqualsDeclaration(import)) =
                source.parse.arena.get(*statement).map(|node| &node.data)
                && !import.is_type_only
                && !matches!(
                    source
                        .parse
                        .arena
                        .get(import.module_reference)
                        .map(|node| &node.data),
                    Some(NodeData::ExternalModuleReference(_))
                )
                && import_equals_name(source, import)
                    .is_some_and(|name| later_script_variable_names.contains(name))
            {
                meanings.insert(*statement, true);
            }
            continue;
        }
        let Some(NodeData::ImportEqualsDeclaration(import)) =
            source.parse.arena.get(*statement).map(|node| &node.data)
        else {
            continue;
        };
        if import.is_type_only {
            continue;
        }
        let Some(import_name) = import_equals_name(source, import) else {
            continue;
        };
        let runtime_uses = runtime_identifier_uses
            .as_ref()
            .expect("AMD uses were collected");
        let has_runtime_use = runtime_uses.contains(import_name);
        if meanings.get(statement) == Some(&false)
            && (!has_runtime_use
                || import_equals_has_inlined_const_enum_access(source, import_name))
        {
            continue;
        }
        // Ambient modules have no implementation initializer, so semantic shape alone cannot
        // distinguish their runtime aliases. Preserve only aliases with binding-resolved uses.
        meanings.insert(*statement, true);
    }
    meanings
}

fn later_top_level_script_variable_names<'a>(
    sources: impl IntoIterator<Item = &'a SourceFile>,
) -> HashSet<String> {
    sources
        .into_iter()
        .filter(|source| {
            !source.is_default_library
                && !ts_path::is_declaration_file(&source.file_name)
                && !source_is_external_module(source)
        })
        .flat_map(|source| {
            let statements = match source
                .parse
                .arena
                .get(source.parse.source_file)
                .map(|node| &node.data)
            {
                Some(NodeData::SourceFile(file)) => file.statements.nodes.as_slice(),
                _ => &[],
            };
            statements
                .iter()
                .filter_map(|statement| {
                    let NodeData::VariableStatement(variable) =
                        &source.parse.arena.get(*statement)?.data
                    else {
                        return None;
                    };
                    let NodeData::VariableDeclarationList(list) =
                        &source.parse.arena.get(variable.declaration_list)?.data
                    else {
                        return None;
                    };
                    Some(list.declarations.nodes.iter().filter_map(|declaration| {
                        let NodeData::VariableDeclaration(variable) =
                            &source.parse.arena.get(*declaration)?.data
                        else {
                            return None;
                        };
                        match source.parse.arena.get(variable.name).map(|node| &node.data) {
                            Some(NodeData::Identifier(identifier)) => Some(identifier.text.clone()),
                            _ => None,
                        }
                    }))
                })
                .flatten()
                .collect::<Vec<_>>()
        })
        .collect()
}

fn append_bundle_declaration_module(
    code: &mut String,
    source: &SourceFile,
    declaration: &str,
    module_name: &str,
    preserve_amd_pragma: bool,
) {
    let preserves_explicit_empty_export = source
        .parse
        .arena
        .get(source.parse.source_file)
        .and_then(|node| match &node.data {
            NodeData::SourceFile(file) => Some(file),
            _ => None,
        })
        .is_some_and(|file| {
            file.statements.nodes.iter().any(|statement| {
                let Some(NodeData::ExportDeclaration(export)) =
                    source.parse.arena.get(*statement).map(|node| &node.data)
                else {
                    return false;
                };
                !export.is_type_only
                    && export.module_specifier.is_none()
                    && matches!(
                        export
                            .export_clause
                            .and_then(|clause| source.parse.arena.get(clause))
                            .map(|node| &node.data),
                        Some(NodeData::NamedExports(exports)) if exports.elements.nodes.is_empty()
                    )
            })
        });
    if preserve_amd_pragma && let Some(pragma) = source.parse.amd_module_names.last() {
        let start = usize::try_from(pragma.range.start.get()).unwrap_or(usize::MAX);
        let end = usize::try_from(pragma.range.end.get()).unwrap_or(usize::MAX);
        if let Some(comment) = source.source_text.get(start..end) {
            code.push_str(comment.trim_end_matches(['\r', '\n']));
            code.push('\n');
        }
    }
    code.push_str("declare module \"");
    code.push_str(&module_name.replace('"', "\\\""));
    code.push_str("\" {\n");
    for line in declaration.lines() {
        if preserve_amd_pragma {
            let trimmed = line.trim_start();
            if trimmed.starts_with("///") && trimmed.contains("<amd-module") {
                continue;
            }
        }
        if line.trim() == "export {};" && !preserves_explicit_empty_export {
            continue;
        }
        let line = line.strip_prefix("export declare ").map_or_else(
            || line.strip_prefix("declare ").unwrap_or(line).to_owned(),
            |line| format!("export {line}"),
        );
        if !line.is_empty() {
            code.push_str("    ");
            code.push_str(&line);
        }
        code.push('\n');
    }
    code.push_str("}\n");
}

fn defer_export_only_bundle_imports(declaration: &str) -> String {
    let lines = declaration.lines().collect::<Vec<_>>();
    let mut deferred = BTreeMap::<usize, Vec<usize>>::new();
    for (import_index, line) in lines.iter().enumerate() {
        let names = declaration_import_local_names(line);
        if names.is_empty() {
            continue;
        }
        let mut last_export = None;
        let mut used_elsewhere = false;
        for (index, candidate) in lines.iter().enumerate() {
            if index == import_index
                || !names
                    .iter()
                    .any(|name| text_contains_identifier(candidate, name))
            {
                continue;
            }
            if candidate.trim_start().starts_with("export {") {
                last_export = Some(index);
            } else {
                used_elsewhere = true;
                break;
            }
        }
        if !used_elsewhere && let Some(export_index) = last_export {
            deferred.entry(export_index).or_default().push(import_index);
        }
    }
    if deferred.is_empty() {
        return declaration.to_owned();
    }
    let deferred_indices = deferred
        .values()
        .flatten()
        .copied()
        .collect::<BTreeSet<_>>();
    let mut output = String::new();
    for (index, line) in lines.iter().enumerate() {
        if !deferred_indices.contains(&index) {
            output.push_str(line);
            output.push('\n');
        }
        if let Some(imports) = deferred.get(&index) {
            for import in imports {
                output.push_str(lines[*import]);
                output.push('\n');
            }
        }
    }
    output
}

fn declaration_import_local_names(line: &str) -> Vec<String> {
    let line = line.trim();
    let Some(clause) = line.strip_prefix("import ") else {
        return Vec::new();
    };
    let Some((clause, _)) = clause.rsplit_once(" from ") else {
        return Vec::new();
    };
    if let Some(namespace) = clause.strip_prefix("* as ") {
        return vec![namespace.trim().to_owned()];
    }
    if let Some(named) = clause
        .strip_prefix('{')
        .and_then(|value| value.strip_suffix('}'))
    {
        return named
            .split(',')
            .filter_map(|specifier| {
                let specifier = specifier
                    .trim()
                    .strip_prefix("type ")
                    .unwrap_or(specifier.trim());
                specifier
                    .split_once(" as ")
                    .map_or(specifier, |(_, local)| local)
                    .split_whitespace()
                    .next()
                    .map(str::to_owned)
            })
            .collect();
    }
    clause
        .split_once(',')
        .map_or(clause, |(default, _)| default)
        .split_whitespace()
        .next()
        .map(str::to_owned)
        .into_iter()
        .collect()
}

fn bundle_declaration_module_name(
    source: &SourceFile,
    bundle_root: &str,
    module: ModuleKind,
) -> String {
    if module == ModuleKind::Amd {
        return amd_bundle_module_name(source, bundle_root);
    }
    let relative = source
        .file_name
        .strip_prefix(bundle_root)
        .unwrap_or(&source.file_name)
        .trim_start_matches('/');
    ts_path::remove_file_extension(relative).to_owned()
}

fn identifier_text(arena: &ts_ast::NodeArena, node: NodeId) -> Option<&str> {
    let NodeData::Identifier(identifier) = &arena.get(node)?.data else {
        return None;
    };
    Some(&identifier.text)
}

fn replace_import_type_reference(
    declaration: &mut String,
    module: &str,
    imported: &str,
    local: &str,
) -> bool {
    let reference = format!("import(\"{module}\").{imported}");
    if !declaration.contains(&reference) {
        return false;
    }
    *declaration = declaration.replace(&reference, local);
    true
}

fn remove_unused_named_declaration_imports(declaration: &str) -> String {
    let body = declaration
        .lines()
        .filter(|line| !line.trim_start().starts_with("import "))
        .collect::<Vec<_>>()
        .join("\n");
    let mut output = declaration
        .lines()
        .filter(|line| {
            let trimmed = line.trim();
            let Some(imports) = trimmed
                .strip_prefix("import { ")
                .and_then(|import| import.split_once(" } from "))
                .map(|(imports, _)| imports)
            else {
                return true;
            };
            imports.split(',').map(str::trim).any(|import| {
                let local = import.split_once(" as ").map_or(import, |(_, local)| local);
                text_contains_identifier(&body, local)
            })
        })
        .collect::<Vec<_>>()
        .join("\n");
    if declaration.ends_with('\n') {
        output.push('\n');
    }
    output
}

fn text_contains_identifier(text: &str, identifier: &str) -> bool {
    text.match_indices(identifier).any(|(start, _)| {
        let before = text[..start].chars().next_back();
        let end = start + identifier.len();
        let after = text[end..].chars().next();
        before.is_none_or(|character| !is_identifier_character(character))
            && after.is_none_or(|character| !is_identifier_character(character))
    })
}

fn is_identifier_character(character: char) -> bool {
    character == '_' || character == '$' || character.is_alphanumeric()
}

fn amd_bundle_module_name(source: &SourceFile, bundle_root: &str) -> String {
    source.parse.amd_module_name.clone().unwrap_or_else(|| {
        let relative = source
            .file_name
            .strip_prefix(bundle_root)
            .unwrap_or(&source.file_name)
            .trim_start_matches('/');
        ts_path::remove_file_extension(relative).to_owned()
    })
}

fn base64_encode(bytes: &[u8]) -> String {
    const ALPHABET: &[u8; 64] = b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";
    let mut encoded = String::with_capacity(bytes.len().div_ceil(3) * 4);
    for chunk in bytes.chunks(3) {
        let first = chunk[0];
        let second = chunk.get(1).copied().unwrap_or(0);
        let third = chunk.get(2).copied().unwrap_or(0);
        encoded.push(char::from(ALPHABET[usize::from(first >> 2)]));
        encoded.push(char::from(
            ALPHABET[usize::from(((first & 0x03) << 4) | (second >> 4))],
        ));
        encoded.push(if chunk.len() > 1 {
            char::from(ALPHABET[usize::from(((second & 0x0f) << 2) | (third >> 6))])
        } else {
            '='
        });
        encoded.push(if chunk.len() > 2 {
            char::from(ALPHABET[usize::from(third & 0x3f)])
        } else {
            '='
        });
    }
    encoded
}

fn percent_encode_source_map_url(url: &str) -> String {
    const HEX: &[u8; 16] = b"0123456789ABCDEF";
    let mut encoded = String::with_capacity(url.len());
    for byte in url.bytes() {
        if byte.is_ascii_alphanumeric()
            || matches!(
                byte,
                b'-' | b'_'
                    | b'.'
                    | b'!'
                    | b'~'
                    | b'*'
                    | b'\''
                    | b'('
                    | b')'
                    | b';'
                    | b'/'
                    | b'?'
                    | b':'
                    | b'@'
                    | b'&'
                    | b'='
                    | b'+'
                    | b'$'
                    | b','
                    | b'#'
            )
        {
            encoded.push(char::from(byte));
        } else {
            encoded.push('%');
            encoded.push(char::from(HEX[usize::from(byte >> 4)]));
            encoded.push(char::from(HEX[usize::from(byte & 0x0f)]));
        }
    }
    encoded
}

fn canonical_static_module_specifiers(
    source: &SourceFile,
    options: &CompilerOptions,
) -> Result<Vec<(NodeRef, String, Option<CanonicalModuleResolutionMode>)>, CanonicalProgramCheckError>
{
    let source_ref = NodeRef::new(source.parse.arena.id(), source.id, source.parse.source_file);
    let Some(NodeData::SourceFile(file)) = source
        .parse
        .arena
        .get(source.parse.source_file)
        .map(|node| &node.data)
    else {
        return Err(CanonicalProgramCheckError::InvalidModuleSourceFile(
            source_ref,
        ));
    };
    // An unrelated source-admission error must not discard existing import usage modes.
    let augmentation_facts = canonical_source_file_facts(source, options).ok();
    let mut specifiers = Vec::new();
    let mut pending = file
        .statements
        .nodes
        .iter()
        .rev()
        .map(|statement| (*statement, source.parse.source_file, false))
        .collect::<Vec<_>>();
    let mut visited = HashSet::new();
    while let Some((statement, parent, inside_ambient_module)) = pending.pop() {
        let Some(node) = source.parse.arena.get(statement) else {
            return Err(CanonicalProgramCheckError::InvalidModuleSourceFile(
                source_ref,
            ));
        };
        if node.parent != Some(parent) || !visited.insert(statement) {
            return Err(CanonicalProgramCheckError::InvalidModuleSourceFile(
                source_ref,
            ));
        }
        if let Some(facts) = &augmentation_facts
            && let Some(augmentation) = CanonicalModuleAugmentation::for_declaration(
                &source.parse.arena,
                source.id,
                statement,
                facts,
            )
            && let Some((text, _)) = string_literal(&source.parse.arena, augmentation.name().node)
        {
            specifiers.push((augmentation.name(), text, None));
        }
        if canonical_ambient_module_statements(
            source,
            statement,
            inside_ambient_module,
            &mut pending,
        )? {
            continue;
        }
        if node.kind == SyntaxKind::JsTypeAliasDeclaration {
            if !inside_ambient_module {
                canonical_jsdoc_typedef_module_specifiers(source, statement, &mut specifiers)?;
            }
            continue;
        }
        if let Some(specifier) = canonical_static_module_specifier(source, node)? {
            specifiers.push(specifier);
        }
    }
    for (_, node) in source.parse.arena.iter() {
        if ts_ast::is_import_call(&source.parse.arena, node)
            && let Some(specifier) = canonical_static_module_specifier(source, node)?
        {
            specifiers.push(specifier);
        }
    }
    Ok(specifiers)
}

fn canonical_ambient_module_statements(
    source: &SourceFile,
    statement: NodeId,
    inside_ambient_module: bool,
    pending: &mut Vec<(NodeId, NodeId, bool)>,
) -> Result<bool, CanonicalProgramCheckError> {
    let source_ref = NodeRef::new(source.parse.arena.id(), source.id, source.parse.source_file);
    let Some(node) = source.parse.arena.get(statement) else {
        return Err(CanonicalProgramCheckError::InvalidModuleSourceFile(
            source_ref,
        ));
    };
    let NodeData::ModuleDeclaration(module) = &node.data else {
        return Ok(false);
    };
    if node.kind != SyntaxKind::ModuleDeclaration {
        return Err(CanonicalProgramCheckError::InvalidModuleSourceFile(
            source_ref,
        ));
    }
    let Some(name) = source.parse.arena.get(module.name) else {
        return Err(CanonicalProgramCheckError::InvalidModuleSourceFile(
            source_ref,
        ));
    };
    if name.parent != Some(statement) {
        return Err(CanonicalProgramCheckError::InvalidModuleSourceFile(
            source_ref,
        ));
    }
    if !(inside_ambient_module
        || name.kind == SyntaxKind::StringLiteral
            && matches!(name.data, NodeData::StringLiteral(_)))
    {
        return Ok(true);
    }
    let Some(body) = module.body else {
        return Ok(true);
    };
    let Some(body_node) = source.parse.arena.get(body) else {
        return Err(CanonicalProgramCheckError::InvalidModuleSourceFile(
            source_ref,
        ));
    };
    if body_node.parent != Some(statement) {
        return Err(CanonicalProgramCheckError::InvalidModuleSourceFile(
            source_ref,
        ));
    }
    match &body_node.data {
        NodeData::ModuleBlock(block) if body_node.kind == SyntaxKind::ModuleBlock => {
            pending.extend(
                block
                    .statements
                    .nodes
                    .iter()
                    .rev()
                    .map(|nested| (*nested, body, true)),
            );
        }
        NodeData::ModuleDeclaration(_) if body_node.kind == SyntaxKind::ModuleDeclaration => {
            pending.push((body, statement, true));
        }
        _ => {
            return Err(CanonicalProgramCheckError::InvalidModuleSourceFile(
                source_ref,
            ));
        }
    }
    Ok(true)
}

fn canonical_static_module_specifier(
    source: &SourceFile,
    node: &Node,
) -> Result<
    Option<(NodeRef, String, Option<CanonicalModuleResolutionMode>)>,
    CanonicalProgramCheckError,
> {
    let (specifier, attributes, type_only, syntax_mode) = match &node.data {
        NodeData::ImportDeclaration(import) => (
            Some(import.module_specifier),
            import.attributes,
            import
                .import_clause
                .and_then(|clause| source.parse.arena.get(clause))
                .is_some_and(|clause| {
                    matches!(
                        &clause.data,
                        NodeData::ImportClause(clause)
                            if clause.phase_modifier == Some(SyntaxKind::TypeKeyword)
                    )
                }),
            None,
        ),
        NodeData::ExportDeclaration(export) => (
            export.module_specifier,
            export.attributes,
            export.is_type_only,
            None,
        ),
        NodeData::ImportEqualsDeclaration(import) => {
            let Some(NodeData::ExternalModuleReference(reference)) = source
                .parse
                .arena
                .get(import.module_reference)
                .map(|node| &node.data)
            else {
                return Ok(None);
            };
            (
                Some(reference.expression),
                None,
                import.is_type_only,
                Some(CanonicalModuleResolutionMode::CommonJs),
            )
        }
        NodeData::VariableStatement(_) if is_javascript_file_name(&source.file_name) => {
            let Some(specifier) = javascript_require_module_specifier(&source.parse, node) else {
                return Ok(None);
            };
            (
                Some(specifier),
                None,
                false,
                Some(CanonicalModuleResolutionMode::CommonJs),
            )
        }
        NodeData::CallExpression(call) if ts_ast::is_import_call(&source.parse.arena, node) => (
            call.arguments.nodes.first().copied().filter(|specifier| {
                source
                    .parse
                    .arena
                    .get(*specifier)
                    .is_some_and(|node| node.kind == SyntaxKind::StringLiteral)
            }),
            None,
            false,
            Some(CanonicalModuleResolutionMode::Esm),
        ),
        _ => return Ok(None),
    };
    let Some(specifier) = specifier else {
        return Ok(None);
    };
    let specifier = NodeRef::new(source.parse.arena.id(), source.id, specifier);
    let Some(specifier_node) = source.parse.arena.get(specifier.node) else {
        return Err(CanonicalProgramCheckError::InvalidModuleSpecifier(
            specifier,
        ));
    };
    match (specifier_node.kind, &specifier_node.data) {
        (SyntaxKind::StringLiteral, NodeData::StringLiteral(_)) => {}
        (SyntaxKind::StringLiteral, _) | (_, NodeData::StringLiteral(_)) => {
            return Err(CanonicalProgramCheckError::InvalidModuleSpecifier(
                specifier,
            ));
        }
        _ => return Ok(None),
    }
    let requested_mode =
        canonical_resolution_mode_override(source, attributes, type_only, specifier)?
            .or(syntax_mode);
    let Some((text, _)) = string_literal(&source.parse.arena, specifier.node) else {
        return Err(CanonicalProgramCheckError::InvalidModuleSpecifier(
            specifier,
        ));
    };
    Ok(Some((specifier, text, requested_mode)))
}

fn canonical_jsdoc_typedef_module_specifiers(
    source: &SourceFile,
    declaration: NodeId,
    specifiers: &mut Vec<(NodeRef, String, Option<CanonicalModuleResolutionMode>)>,
) -> Result<(), CanonicalProgramCheckError> {
    let source_ref = NodeRef::new(source.parse.arena.id(), source.id, source.parse.source_file);
    let Some(node) = source.parse.arena.get(declaration) else {
        return Err(CanonicalProgramCheckError::InvalidModuleSourceFile(
            source_ref,
        ));
    };
    let NodeData::TypeAliasDeclaration(alias) = &node.data else {
        return Err(CanonicalProgramCheckError::InvalidModuleSourceFile(
            source_ref,
        ));
    };
    if node.kind != SyntaxKind::JsTypeAliasDeclaration
        || node.flags != NodeFlags::REPARSED
        || node.parent != Some(source.parse.source_file)
    {
        return Err(CanonicalProgramCheckError::InvalidModuleSourceFile(
            source_ref,
        ));
    }
    let mut pending = vec![(alias.type_, declaration)];
    let mut visited = HashSet::new();
    while let Some((node_id, parent)) = pending.pop() {
        let Some(node) = source.parse.arena.get(node_id) else {
            return Err(CanonicalProgramCheckError::InvalidModuleSourceFile(
                source_ref,
            ));
        };
        if node.parent != Some(parent) || !visited.insert(node_id) {
            return Err(CanonicalProgramCheckError::InvalidModuleSourceFile(
                source_ref,
            ));
        }

        if let NodeData::ImportTypeNode(import) = &node.data {
            if node.kind != SyntaxKind::ImportType {
                return Err(CanonicalProgramCheckError::InvalidModuleSourceFile(
                    source_ref,
                ));
            }
            let argument_ref = NodeRef::new(source.parse.arena.id(), source.id, import.argument);
            let Some(argument) = source.parse.arena.get(import.argument) else {
                return Err(CanonicalProgramCheckError::InvalidModuleSpecifier(
                    argument_ref,
                ));
            };
            let NodeData::LiteralTypeNode(literal) = &argument.data else {
                return Err(CanonicalProgramCheckError::InvalidModuleSpecifier(
                    argument_ref,
                ));
            };
            if argument.kind != SyntaxKind::LiteralType || argument.parent != Some(node_id) {
                return Err(CanonicalProgramCheckError::InvalidModuleSpecifier(
                    argument_ref,
                ));
            }

            let specifier = NodeRef::new(source.parse.arena.id(), source.id, literal.literal);
            let Some(specifier_node) = source.parse.arena.get(specifier.node) else {
                return Err(CanonicalProgramCheckError::InvalidModuleSpecifier(
                    specifier,
                ));
            };
            match (specifier_node.kind, &specifier_node.data) {
                (SyntaxKind::StringLiteral, NodeData::StringLiteral(_)) => {}
                (SyntaxKind::StringLiteral, _) | (_, NodeData::StringLiteral(_)) => {
                    return Err(CanonicalProgramCheckError::InvalidModuleSpecifier(
                        specifier,
                    ));
                }
                _ => continue,
            }
            if specifier_node.parent != Some(import.argument) {
                return Err(CanonicalProgramCheckError::InvalidModuleSpecifier(
                    specifier,
                ));
            }
            let requested_mode =
                canonical_resolution_mode_override(source, import.attributes, true, specifier)?;
            let Some((text, _)) = string_literal(&source.parse.arena, specifier.node) else {
                return Err(CanonicalProgramCheckError::InvalidModuleSpecifier(
                    specifier,
                ));
            };
            specifiers.push((specifier, text, requested_mode));
        }

        let mut children = Vec::new();
        node.for_each_child(|child| children.push(child));
        pending.extend(children.into_iter().rev().map(|child| (child, node_id)));
    }
    Ok(())
}

fn canonical_resolution_mode_override(
    source: &SourceFile,
    attributes: Option<NodeId>,
    type_only: bool,
    specifier: NodeRef,
) -> Result<Option<CanonicalModuleResolutionMode>, CanonicalProgramCheckError> {
    if !type_only {
        return Ok(None);
    }
    let Some(attributes) = attributes else {
        return Ok(None);
    };
    let Some(NodeData::ImportAttributes(attributes)) =
        source.parse.arena.get(attributes).map(|node| &node.data)
    else {
        return Err(
            CanonicalProgramCheckError::ModuleSpecifierResolutionModeUnsupported(specifier),
        );
    };
    let [attribute] = attributes.attributes.nodes.as_slice() else {
        return Ok(None);
    };
    let Some(NodeData::ImportAttribute(attribute)) =
        source.parse.arena.get(*attribute).map(|node| &node.data)
    else {
        return Err(
            CanonicalProgramCheckError::ModuleSpecifierResolutionModeUnsupported(specifier),
        );
    };
    let Some((name, _)) = string_literal(&source.parse.arena, attribute.name) else {
        return Ok(None);
    };
    if name != "resolution-mode" {
        return Ok(None);
    }
    let Some((value, _)) = string_literal(&source.parse.arena, attribute.value) else {
        return Err(
            CanonicalProgramCheckError::ModuleSpecifierResolutionModeUnsupported(specifier),
        );
    };
    match value.as_str() {
        "import" => Ok(Some(CanonicalModuleResolutionMode::Esm)),
        "require" => Ok(Some(CanonicalModuleResolutionMode::CommonJs)),
        _ => Err(CanonicalProgramCheckError::ModuleSpecifierResolutionModeUnsupported(specifier)),
    }
}

fn javascript_require_module_specifier(parse: &ParseResult, statement: &Node) -> Option<NodeId> {
    let NodeData::VariableStatement(variable_statement) = &statement.data else {
        return None;
    };
    let list = parse.arena.get(variable_statement.declaration_list)?;
    let NodeData::VariableDeclarationList(declarations) = &list.data else {
        return None;
    };
    let [declaration] = declarations.declarations.nodes.as_slice() else {
        return None;
    };
    let declaration_record = parse.arena.get(*declaration)?;
    let NodeData::VariableDeclaration(variable) = &declaration_record.data else {
        return None;
    };
    let call = parse.arena.get(variable.initializer?)?;
    let NodeData::CallExpression(require) = &call.data else {
        return None;
    };
    let [specifier] = require.arguments.nodes.as_slice() else {
        return None;
    };
    let callee = parse.arena.get(require.expression)?;
    let NodeData::Identifier(identifier) = &callee.data else {
        return None;
    };

    (statement.kind == SyntaxKind::VariableStatement
        && statement.parent == Some(parse.source_file)
        && statement.flags.0 == 0
        && variable_statement.modifiers.is_none()
        && variable_statement.flow_node.is_none()
        && variable_statement.facts == 0
        && list.kind == SyntaxKind::VariableDeclarationList
        && list.flags.0 == 1 << 1
        && !declarations.declarations.has_trailing_comma
        && declarations.facts == 0
        && declaration_record.kind == SyntaxKind::VariableDeclaration
        && declaration_record.parent == Some(variable_statement.declaration_list)
        && declaration_record.flags.0 == 0
        && variable.type_.is_none()
        && variable.exclamation_token.is_none()
        && call.kind == SyntaxKind::CallExpression
        && call.parent == Some(*declaration)
        && call.flags.0 == 0
        && !require.arguments.has_trailing_comma
        && require.question_dot_token.is_none()
        && require.type_arguments.is_none()
        && require.facts == 0
        && callee.kind == SyntaxKind::Identifier
        && identifier.flow_node.is_none()
        && identifier.text == "require"
        && matches!(
            parse.arena.get(*specifier),
            Some(Node {
                kind: SyntaxKind::StringLiteral,
                data: NodeData::StringLiteral(literal),
                ..
            }) if literal.token_flags.0 == 0 && !literal.text.is_empty()
        ))
    .then_some(*specifier)
}

struct ModuleSpecifier {
    text: String,
    range: TextRange,
    can_resolve_ambient: bool,
    side_effect_only: bool,
    is_augmentation: bool,
    dependency_order: Option<SourceDependencyOrder>,
}

fn parsed_module_specifier(
    parse: &ParseResult,
    node: &Node,
    include_javascript_requires: bool,
) -> Option<ModuleSpecifier> {
    let (text, range, can_resolve_ambient, side_effect_only) = match &node.data {
        NodeData::ImportDeclaration(data) => string_literal(&parse.arena, data.module_specifier)
            .map(|(specifier, range)| (specifier, range, true, data.import_clause.is_none())),
        NodeData::ImportEqualsDeclaration(data) => parse
            .arena
            .get(data.module_reference)
            .and_then(|reference| match &reference.data {
                NodeData::ExternalModuleReference(reference) => {
                    string_literal(&parse.arena, reference.expression)
                }
                _ => None,
            })
            .map(|(specifier, range)| (specifier, range, true, false)),
        NodeData::ExportDeclaration(data) => data
            .module_specifier
            .and_then(|specifier| string_literal(&parse.arena, specifier))
            .map(|(specifier, range)| (specifier, range, true, false)),
        NodeData::ImportTypeNode(data) => {
            let argument = match parse.arena.get(data.argument).map(|node| &node.data) {
                Some(NodeData::LiteralTypeNode(literal)) => literal.literal,
                _ => data.argument,
            };
            string_literal(&parse.arena, argument)
                .map(|(specifier, range)| (specifier, range, true, false))
        }
        NodeData::CallExpression(data) if ts_ast::is_import_call(&parse.arena, node) => data
            .arguments
            .nodes
            .first()
            .and_then(|argument| string_literal(&parse.arena, *argument))
            .map(|(specifier, range)| (specifier, range, true, false)),
        NodeData::VariableStatement(_) if include_javascript_requires => {
            javascript_require_module_specifier(parse, node)
                .and_then(|specifier| string_literal(&parse.arena, specifier))
                .map(|(specifier, range)| (specifier, range, true, false))
        }
        _ => None,
    }?;
    let dependency_order = if matches!(
        node.data,
        NodeData::ImportDeclaration(_)
            | NodeData::ImportEqualsDeclaration(_)
            | NodeData::ExportDeclaration(_)
    ) {
        SourceDependencyOrder::StaticImport(range.start)
    } else {
        SourceDependencyOrder::DynamicImport(range.start)
    };
    Some(ModuleSpecifier {
        text,
        range,
        can_resolve_ambient,
        side_effect_only,
        is_augmentation: false,
        dependency_order: Some(dependency_order),
    })
}

fn static_module_dependency_statements(
    source: &SourceFile,
    options: &CompilerOptions,
) -> HashSet<NodeId> {
    let parse = &source.parse;
    let mut imports = HashSet::new();
    let Some(NodeData::SourceFile(file)) =
        parse.arena.get(parse.source_file).map(|node| &node.data)
    else {
        return imports;
    };
    let is_declaration_file = ts_path::is_declaration_file(&source.file_name);
    let language = if is_javascript_file_name(&source.file_name) {
        CanonicalSourceLanguage::JavaScript
    } else {
        CanonicalSourceLanguage::TypeScript
    };
    let is_external_module = matches!(
        source_file_module_state(
            &source.file_name,
            parse,
            language,
            is_declaration_file,
            source.implied_node_format,
            options,
        ),
        CanonicalModuleState::External | CanonicalModuleState::ExternalAndCommonJs
    );
    let mut pending = file
        .statements
        .nodes
        .iter()
        .rev()
        .map(|statement| (*statement, false))
        .collect::<Vec<_>>();
    while let Some((statement, in_ambient_module)) = pending.pop() {
        let Some(node) = parse.arena.get(statement) else {
            continue;
        };
        if matches!(
            node.data,
            NodeData::ImportDeclaration(_)
                | NodeData::ImportEqualsDeclaration(_)
                | NodeData::ExportDeclaration(_)
        ) {
            if let Some(specifier) = parsed_module_specifier(parse, node, false)
                && !specifier.text.is_empty()
                && (!in_ambient_module
                    || !(ts_path::is_relative(&specifier.text)
                        || ts_path::is_rooted_disk_path(&specifier.text)))
            {
                imports.insert(statement);
            }
            continue;
        }
        // Go traverses only top-level ambient modules in scripts here.
        if in_ambient_module || is_external_module {
            continue;
        }
        let NodeData::ModuleDeclaration(module) = &node.data else {
            continue;
        };
        let is_ambient_module = module.keyword == SyntaxKind::GlobalKeyword
            || parse
                .arena
                .get(module.name)
                .is_some_and(|name| name.kind == SyntaxKind::StringLiteral);
        if !is_ambient_module
            || !(is_declaration_file
                || node_has_modifier(
                    &parse.arena,
                    module.modifiers.as_ref(),
                    SyntaxKind::DeclareKeyword,
                ))
        {
            continue;
        }
        let Some(NodeData::ModuleBlock(block)) = module
            .body
            .and_then(|body| parse.arena.get(body))
            .map(|node| &node.data)
        else {
            continue;
        };
        pending.extend(
            block
                .statements
                .nodes
                .iter()
                .rev()
                .map(|node| (*node, true)),
        );
    }
    imports
}

fn module_specifiers(source: &SourceFile, options: &CompilerOptions) -> Vec<ModuleSpecifier> {
    let parse = &source.parse;
    let is_javascript = is_javascript_file_name(&source.file_name);
    let static_dependencies = static_module_dependency_statements(source, options);
    let mut specifiers = parse
        .arena
        .iter()
        .filter_map(|(id, node)| {
            let mut specifier = parsed_module_specifier(parse, node, is_javascript)?;
            // Preserve resolution candidates outside dependency-bearing scopes.
            if matches!(
                specifier.dependency_order,
                Some(SourceDependencyOrder::StaticImport(_))
            ) && !static_dependencies.contains(&id)
            {
                specifier.dependency_order = None;
            }
            Some(specifier)
        })
        .collect::<Vec<_>>();
    for (specifier, text, _) in
        canonical_static_module_specifiers(source, options).unwrap_or_default()
    {
        let Some(node) = parse.arena.get(specifier.node) else {
            continue;
        };
        if node
            .parent
            .and_then(|parent| parse.arena.get(parent))
            .is_some_and(|parent| {
                matches!(
                    &parent.data,
                    NodeData::ModuleDeclaration(module) if module.name == specifier.node
                )
            })
        {
            specifiers.push(ModuleSpecifier {
                text,
                range: node.range,
                can_resolve_ambient: true,
                side_effect_only: false,
                is_augmentation: true,
                dependency_order: None,
            });
        }
    }
    if let Some(source) = parse.arena.source_text() {
        for (specifier, range, can_resolve_ambient, side_effect_only) in
            jsdoc_import_specifiers(source)
        {
            let already_parsed = specifiers.iter().any(|existing| {
                existing.text == specifier
                    && existing.range.start <= range.start
                    && existing.range.end >= range.end
            });
            if !already_parsed {
                specifiers.push(ModuleSpecifier {
                    text: specifier,
                    range,
                    can_resolve_ambient,
                    side_effect_only,
                    is_augmentation: false,
                    dependency_order: is_javascript
                        .then_some(SourceDependencyOrder::DynamicImport(range.start)),
                });
            }
        }
    }
    specifiers
}

fn module_specifier_is_emittable(parse: &ParseResult, range: TextRange) -> bool {
    let matches_range = |specifier| {
        parse
            .arena
            .get(specifier)
            .is_some_and(|node| node.range == range)
    };

    parse.arena.iter().any(|(_, node)| match &node.data {
        NodeData::ImportDeclaration(import) => {
            matches_range(import.module_specifier)
                && import
                    .import_clause
                    .and_then(|clause| parse.arena.get(clause))
                    .is_some_and(|clause| {
                        matches!(
                            &clause.data,
                            NodeData::ImportClause(clause)
                                if clause.phase_modifier != Some(SyntaxKind::TypeKeyword)
                        )
                    })
        }
        NodeData::ImportEqualsDeclaration(import) => {
            !import.is_type_only
                && parse
                    .arena
                    .get(import.module_reference)
                    .is_some_and(|reference| {
                        matches!(
                            &reference.data,
                            NodeData::ExternalModuleReference(reference)
                                if matches_range(reference.expression)
                        )
                    })
        }
        NodeData::ExportDeclaration(export) => {
            !export.is_type_only && export.module_specifier.is_some_and(matches_range)
        }
        NodeData::CallExpression(call) => {
            call.arguments
                .nodes
                .first()
                .is_some_and(|argument| matches_range(*argument))
                && ts_ast::is_import_call(&parse.arena, node)
        }
        _ => false,
    })
}

fn imported_typescript_extension(specifier: &str) -> Option<&'static str> {
    ts_path::extension_from_path(specifier)
        .filter(|extension| extension.is_typescript())
        .map(FileExtension::as_str)
        .or_else(|| {
            ts_path::SUPPORTED_TS_EXTENSIONS
                .into_iter()
                .find(|extension| specifier.contains(extension.as_str()))
                .map(FileExtension::as_str)
        })
}

fn jsdoc_import_specifiers(source: &str) -> Vec<(String, TextRange, bool, bool)> {
    let mut specifiers = Vec::new();
    let mut search_start = 0;
    while let Some(relative_start) = source[search_start..].find("/**") {
        let comment_start = search_start + relative_start;
        let body_start = comment_start + 3;
        let Some(relative_end) = source[body_start..].find("*/") else {
            break;
        };
        let comment_end = body_start + relative_end;
        let comment = &source[body_start..comment_end];
        let mut import_search = 0;
        while let Some(relative_import) = comment[import_search..].find("import(") {
            let import_start = body_start + import_search + relative_import;
            if source[..import_start]
                .chars()
                .next_back()
                .is_some_and(|character| character == '@' || is_identifier_character(character))
            {
                import_search += relative_import + "import(".len();
                continue;
            }
            let argument_start = import_start + "import(".len();
            let argument = &source[argument_start..comment_end];
            let whitespace = argument.len() - argument.trim_start().len();
            let quote_start = argument_start + whitespace;
            let Some(quote @ ('\'' | '"')) = source[quote_start..].chars().next() else {
                import_search += relative_import + "import(".len();
                continue;
            };
            let value_start = quote_start + quote.len_utf8();
            let Some(value_end_relative) = source[value_start..comment_end].find(quote) else {
                import_search += relative_import + "import(".len();
                continue;
            };
            let value_end = value_start + value_end_relative;
            let after_quote = &source[value_end + quote.len_utf8()..comment_end];
            if !after_quote.trim_start().starts_with(')') {
                import_search += relative_import + "import(".len();
                continue;
            }
            specifiers.push((
                source[value_start..value_end].to_owned(),
                TextRange::new(
                    TextPos::new(u32::try_from(value_start).unwrap_or(u32::MAX)),
                    TextPos::new(u32::try_from(value_end).unwrap_or(u32::MAX)),
                ),
                true,
                false,
            ));
            import_search = value_end.saturating_sub(body_start);
        }
        search_start = comment_end + 2;
    }
    specifiers
}

fn register_ambient_external_modules(
    source_file: &SourceFile,
    options: &CompilerOptions,
    current_directory: &str,
    case_sensitivity: CaseSensitivity,
    modules: &mut BTreeMap<String, String>,
) {
    if source_file.is_default_library
        || !canonical_source_file_facts(source_file, options)
            .is_ok_and(|facts| !facts.is_external_or_common_js_module())
    {
        return;
    }
    let Some(NodeData::SourceFile(source)) = source_file
        .parse
        .arena
        .get(source_file.parse.source_file)
        .map(|node| &node.data)
    else {
        return;
    };
    let target = canonicalize(&source_file.file_name, current_directory, case_sensitivity);
    for statement in &source.statements.nodes {
        let Some(node) = source_file.parse.arena.get(*statement) else {
            continue;
        };
        let NodeData::ModuleDeclaration(module) = &node.data else {
            continue;
        };
        if !ts_path::is_declaration_file(&source_file.file_name)
            && !node_has_modifier(
                &source_file.parse.arena,
                module.modifiers.as_ref(),
                ts_ast::SyntaxKind::DeclareKeyword,
            )
        {
            continue;
        }
        let Some((name, _)) = string_literal(&source_file.parse.arena, module.name) else {
            continue;
        };
        if !module_name_is_relative(&name) {
            modules.entry(name).or_insert_with(|| target.clone());
        }
    }
}

fn source_file_is_external_module(parse: &ParseResult) -> bool {
    let Some(NodeData::SourceFile(source)) =
        parse.arena.get(parse.source_file).map(|node| &node.data)
    else {
        return false;
    };
    source.statements.nodes.iter().any(|statement| {
        let Some(node) = parse.arena.get(*statement) else {
            return false;
        };
        match &node.data {
            NodeData::ImportDeclaration(_)
            | NodeData::ExportDeclaration(_)
            | NodeData::ExportAssignment(_) => true,
            NodeData::ImportEqualsDeclaration(import) => matches!(
                parse
                    .arena
                    .get(import.module_reference)
                    .map(|node| &node.data),
                Some(NodeData::ExternalModuleReference(_))
            ),
            _ => declaration_modifiers(node).is_some_and(|modifiers| {
                node_has_modifier(
                    &parse.arena,
                    Some(modifiers),
                    ts_ast::SyntaxKind::ExportKeyword,
                )
            }),
        }
    }) || source_contains_import_meta(parse)
}

fn source_file_has_commonjs_indicator(parse: &ParseResult) -> bool {
    let Some(NodeData::SourceFile(source)) =
        parse.arena.get(parse.source_file).map(|node| &node.data)
    else {
        return false;
    };
    source.statements.nodes.iter().any(|statement| {
        let Some(NodeData::ExpressionStatement(statement)) =
            parse.arena.get(*statement).map(|node| &node.data)
        else {
            return false;
        };
        let Some(NodeData::BinaryExpression(assignment)) =
            parse.arena.get(statement.expression).map(|node| &node.data)
        else {
            return false;
        };
        parse
            .arena
            .get(assignment.operator_token)
            .is_some_and(|operator| operator.kind == SyntaxKind::EqualsToken)
            && commonjs_export_access(&parse.arena, assignment.left)
    })
}

fn commonjs_export_access(arena: &ts_ast::NodeArena, node: NodeId) -> bool {
    match arena.get(node).map(|node| &node.data) {
        Some(NodeData::Identifier(identifier)) => identifier.text == "exports",
        Some(NodeData::PropertyAccessExpression(access)) => {
            let module_exports = matches!(
                arena.get(access.expression).map(|node| &node.data),
                Some(NodeData::Identifier(identifier)) if identifier.text == "module"
            ) && matches!(
                arena.get(access.name).map(|node| &node.data),
                Some(NodeData::Identifier(identifier)) if identifier.text == "exports"
            );
            module_exports || commonjs_export_access(arena, access.expression)
        }
        Some(NodeData::ElementAccessExpression(access)) => {
            let module_exports = matches!(
                arena.get(access.expression).map(|node| &node.data),
                Some(NodeData::Identifier(identifier)) if identifier.text == "module"
            ) && matches!(
                arena
                    .get(access.argument_expression)
                    .map(|node| &node.data),
                Some(NodeData::StringLiteral(value)) if value.text == "exports"
            );
            module_exports || commonjs_export_access(arena, access.expression)
        }
        _ => false,
    }
}

fn source_contains_jsx(parse: &ParseResult) -> bool {
    parse.arena.iter().any(|(_, node)| {
        matches!(
            node.data,
            NodeData::JsxElement(_) | NodeData::JsxSelfClosingElement(_) | NodeData::JsxFragment(_)
        )
    })
}

fn source_contains_import_meta(parse: &ParseResult) -> bool {
    parse.arena.iter().any(|(_, node)| {
        matches!(
            &node.data,
            NodeData::MetaProperty(meta) if meta.keyword_token == SyntaxKind::ImportKeyword
                && matches!(parse.arena.get(meta.name).map(|node| &node.data), Some(NodeData::Identifier(name)) if name.text == "meta")
        )
    })
}

fn amd_generated_dependency_bases(source: &SourceFile) -> Vec<String> {
    let Some(NodeData::SourceFile(file)) = source
        .parse
        .arena
        .get(source.parse.source_file)
        .map(|node| &node.data)
    else {
        return Vec::new();
    };
    file.statements
        .nodes
        .iter()
        .filter_map(|statement| {
            if source.checking.import_runtime_meanings.get(statement) == Some(&false) {
                return None;
            }
            let Some(NodeData::ImportDeclaration(import)) =
                source.parse.arena.get(*statement).map(|node| &node.data)
            else {
                return None;
            };
            import.import_clause?;
            let (specifier, _) = string_literal(&source.parse.arena, import.module_specifier)?;
            Some(module_temp_base(&specifier))
        })
        .collect()
}

fn module_temp_base(specifier: &str) -> String {
    let segment = specifier
        .rsplit('/')
        .find(|segment| !segment.is_empty())
        .unwrap_or("module");
    let stem = segment.split('.').next().unwrap_or(segment);
    let mut base = String::new();
    for (index, character) in stem.chars().enumerate() {
        if character == '_' || character == '$' || character.is_ascii_alphanumeric() {
            if index == 0 && character.is_ascii_digit() {
                base.push('_');
            }
            base.push(character);
        } else if !base.ends_with('_') {
            base.push('_');
        }
    }
    if base.is_empty() {
        "module".to_owned()
    } else {
        base
    }
}

fn declaration_modifiers(node: &ts_ast::Node) -> Option<&ts_ast::ModifierList> {
    match &node.data {
        NodeData::VariableStatement(data) => data.modifiers.as_ref(),
        NodeData::FunctionDeclaration(data) => data.modifiers.as_ref(),
        NodeData::ClassDeclaration(data) => data.modifiers.as_ref(),
        NodeData::InterfaceDeclaration(data) => data.modifiers.as_ref(),
        NodeData::TypeAliasDeclaration(data) => data.modifiers.as_ref(),
        NodeData::EnumDeclaration(data) => data.modifiers.as_ref(),
        NodeData::ModuleDeclaration(data) => data.modifiers.as_ref(),
        NodeData::ImportDeclaration(data) => data.modifiers.as_ref(),
        NodeData::ImportEqualsDeclaration(data) => data.modifiers.as_ref(),
        _ => None,
    }
}

fn node_has_modifier(
    arena: &ts_ast::NodeArena,
    modifiers: Option<&ts_ast::ModifierList>,
    kind: ts_ast::SyntaxKind,
) -> bool {
    modifiers.is_some_and(|modifiers| {
        modifiers
            .list
            .nodes
            .iter()
            .any(|modifier| arena.get(*modifier).is_some_and(|node| node.kind == kind))
    })
}

fn module_name_is_relative(name: &str) -> bool {
    name.starts_with("./")
        || name.starts_with("../")
        || name.starts_with(".\\")
        || name.starts_with("..\\")
}

fn string_literal(arena: &ts_ast::NodeArena, id: NodeId) -> Option<(String, TextRange)> {
    let node = arena.get(id)?;
    let NodeData::StringLiteral(data) = &node.data else {
        return None;
    };
    Some((data.text.clone(), node.range))
}

fn missing_file_diagnostic(file_name: &str) -> ProgramDiagnostic {
    let message = message_by_code(6053).expect("TS6053 must be in the generated catalog");
    ProgramDiagnostic {
        file_name: None,
        range: None,
        code: Some(message.code()),
        category: message.category(),
        message: message
            .format(&[file_name.to_owned()])
            .expect("TS6053 has one formatting argument"),
        related_information: Vec::new(),
    }
}

fn check_js_requires_allow_js_diagnostic() -> ProgramDiagnostic {
    let message = message_by_code(5052).expect("TS5052 must be in the generated catalog");
    ProgramDiagnostic {
        file_name: None,
        range: None,
        code: Some(message.code()),
        category: message.category(),
        message: message
            .format(&["checkJs".to_owned(), "allowJs".to_owned()])
            .expect("TS5052 has two formatting arguments"),
        related_information: Vec::new(),
    }
}

fn unchecked_javascript_parameter_decorator_range(
    source: &str,
    parse: &ParseResult,
    parameter: &Node,
    decorator: &Node,
) -> TextRange {
    let Some(parent) = parameter.parent.and_then(|parent| parse.arena.get(parent)) else {
        return decorator.range;
    };
    // Start after the nearest preceding child, outside earlier parameter initializers.
    let mut start = parent.range.start;
    parent.for_each_child(|child| {
        if let Some(child) = parse.arena.get(child)
            && child.range.end <= parameter.range.start
        {
            start = start.max(child.range.end);
        }
    });
    let mut scanner = ts_scanner::Scanner::new(source);
    scanner.reset_pos(start.get() as usize);
    loop {
        let token = scanner.scan();
        if token.kind == SyntaxKind::AtToken && token.range.start == decorator.range.start {
            return TextRange::new(token.full_start, decorator.range.end);
        }
        if token.kind == SyntaxKind::EndOfFile || token.range.start >= decorator.range.start {
            return decorator.range;
        }
    }
}

/// Reports TypeScript-only syntax from the original JavaScript AST.
#[allow(clippy::too_many_lines)] // Keep the related syntax rules in one AST walk.
fn javascript_syntax_diagnostics(
    file_name: &str,
    source_text: &str,
    parse: &ParseResult,
    report_parameter_decorators: bool,
) -> Vec<ProgramDiagnostic> {
    const JSDOC_OR_REPARSED: u32 = (1 << 22) | NodeFlags::REPARSED.0;
    let source_node = |id| {
        parse
            .arena
            .get(id)
            .filter(|node| node.flags.0 & JSDOC_OR_REPARSED == 0)
    };
    let mut diagnostics = Vec::new();
    let mut report = |range: TextRange, code, arguments: &[&str]| {
        let message = message_by_code(code)
            .expect("JavaScript syntax diagnostics must be in the diagnostic catalog");
        diagnostics.push(ProgramDiagnostic {
            file_name: Some(file_name.to_owned()),
            range: Some(range),
            code: Some(code),
            category: message.category(),
            message: Diagnostic::with_arguments(message, arguments.iter().copied())
                .render()
                .expect("JavaScript syntax diagnostic arguments must match"),
            related_information: Vec::new(),
        });
    };
    let mut pending = vec![parse.source_file];
    while let Some(node_id) = pending.pop() {
        let Some(node) = source_node(node_id) else {
            continue;
        };
        node.for_each_child(|child| pending.push(child));
        let mut annotation = None;
        let mut question_token = None;
        let mut type_parameters = None;
        let mut modifiers = None;
        let mut signature_without_body = false;

        macro_rules! signature {
            ($data:ident, $has_body:expr) => {{
                annotation = $data.type_;
                type_parameters = $data.type_parameters.as_ref();
                modifiers = $data.modifiers.as_ref();
                signature_without_body = !$has_body;
            }};
        }

        match &node.data {
            NodeData::ParameterDeclaration(parameter) => {
                annotation = parameter.type_;
                question_token = parameter.question_token;
                if let Some(modifiers) = parameter.modifiers.as_ref() {
                    let modifier_nodes = modifiers
                        .list
                        .nodes
                        .iter()
                        .filter_map(|modifier| source_node(*modifier))
                        .collect::<Vec<_>>();
                    if modifier_nodes.iter().any(|node| node.kind.is_modifier())
                        && let (Some(first), Some(last)) =
                            (modifier_nodes.first(), modifier_nodes.last())
                    {
                        report(TextRange::new(first.range.start, last.range.end), 8012, &[]);
                    }
                    if report_parameter_decorators
                        && let Some(decorator) = modifier_nodes
                            .iter()
                            .find(|node| node.kind == SyntaxKind::Decorator)
                    {
                        report(
                            unchecked_javascript_parameter_decorator_range(
                                source_text,
                                parse,
                                node,
                                decorator,
                            ),
                            1206,
                            &[],
                        );
                    }
                }
            }
            NodeData::PropertyDeclaration(property) => {
                annotation = property.type_;
                question_token = property.postfix_token;
                modifiers = property.modifiers.as_ref();
            }
            NodeData::MethodDeclaration(method) => {
                question_token = method.postfix_token;
                signature!(method, method.body.is_some());
            }
            NodeData::ConstructorDeclaration(constructor) => {
                signature!(constructor, constructor.body.is_some());
            }
            NodeData::GetAccessorDeclaration(accessor) => {
                signature!(accessor, accessor.body.is_some());
            }
            NodeData::SetAccessorDeclaration(accessor) => {
                signature!(accessor, accessor.body.is_some());
            }
            NodeData::FunctionDeclaration(function) => {
                signature!(function, function.body.is_some());
            }
            NodeData::FunctionExpression(function) => {
                signature!(function, true);
            }
            NodeData::ArrowFunction(function) => {
                signature!(function, true);
            }
            NodeData::MethodSignatureDeclaration(_) | NodeData::IndexSignatureDeclaration(_) => {
                signature_without_body = true;
            }
            NodeData::VariableDeclaration(variable) => annotation = variable.type_,
            NodeData::VariableStatement(statement) => modifiers = statement.modifiers.as_ref(),
            NodeData::ClassDeclaration(class) => {
                type_parameters = class.type_parameters.as_ref();
                modifiers = class.modifiers.as_ref();
            }
            NodeData::ClassExpression(class) => {
                type_parameters = class.type_parameters.as_ref();
                modifiers = class.modifiers.as_ref();
            }
            NodeData::ImportEqualsDeclaration(_) => report(node.range, 8002, &[]),
            NodeData::ExportAssignment(export) if export.is_export_equals => {
                report(node.range, 8003, &[]);
            }
            NodeData::HeritageClause(heritage)
                if heritage.token == SyntaxKind::ImplementsKeyword =>
            {
                report(node.range, 8005, &[]);
            }
            NodeData::InterfaceDeclaration(interface) => {
                if let Some(name) = source_node(interface.name) {
                    report(name.range, 8006, &["interface"]);
                }
            }
            NodeData::EnumDeclaration(enumeration) => {
                if let Some(name) = source_node(enumeration.name) {
                    report(name.range, 8006, &["enum"]);
                }
            }
            NodeData::ModuleDeclaration(module) => {
                let keyword = match module.keyword {
                    SyntaxKind::NamespaceKeyword => "namespace",
                    SyntaxKind::ModuleKeyword => "module",
                    SyntaxKind::GlobalKeyword => "global",
                    _ => continue,
                };
                if let Some(name) = source_node(module.name) {
                    report(name.range, 8006, &[keyword]);
                }
            }
            NodeData::TypeAliasDeclaration(alias) => {
                if let Some(name) = source_node(alias.name) {
                    report(name.range, 8008, &[]);
                }
            }
            NodeData::ImportDeclaration(import) => {
                if import.import_clause.is_some_and(|clause| {
                    source_node(clause).is_some_and(|node| {
                        matches!(&node.data, NodeData::ImportClause(clause)
                            if clause.phase_modifier == Some(SyntaxKind::TypeKeyword))
                    })
                }) {
                    report(node.range, 8006, &["import type"]);
                }
            }
            NodeData::ExportDeclaration(export) if export.is_type_only => {
                report(node.range, 8006, &["export type"]);
            }
            NodeData::ImportSpecifier(import) if import.is_type_only => {
                report(node.range, 8006, &["import...type"]);
            }
            NodeData::ExportSpecifier(export) if export.is_type_only => {
                report(node.range, 8006, &["export...type"]);
            }
            _ => {}
        }

        if let Some(token) = question_token.and_then(source_node)
            && token.kind == SyntaxKind::QuestionToken
        {
            report(token.range, 8009, &["?"]);
        }
        if signature_without_body {
            report(node.range, 8017, &[]);
        } else if let Some(annotation) = annotation.and_then(source_node) {
            report(annotation.range, 8010, &[]);
        }
        if let Some(parameters) = type_parameters {
            let mut source_parameters = parameters
                .nodes
                .iter()
                .filter_map(|parameter| source_node(*parameter));
            if let Some(first) = source_parameters.next() {
                let last = source_parameters.next_back().unwrap_or(first);
                // Rust retains the angle brackets in this list range; Go excludes them.
                let end = parameters
                    .range
                    .end
                    .get()
                    .saturating_sub(1)
                    .max(last.range.end.get());
                report(
                    TextRange::new(first.range.start, TextPos::new(end)),
                    8004,
                    &[],
                );
            }
        }
        if let Some(modifiers) = modifiers {
            for modifier in &modifiers.list.nodes {
                let Some(modifier) = source_node(*modifier) else {
                    continue;
                };
                let keyword = match modifier.kind {
                    SyntaxKind::AbstractKeyword => "abstract",
                    SyntaxKind::DeclareKeyword => "declare",
                    SyntaxKind::PublicKeyword => "public",
                    SyntaxKind::ProtectedKeyword => "protected",
                    SyntaxKind::PrivateKeyword => "private",
                    SyntaxKind::ReadonlyKeyword => "readonly",
                    SyntaxKind::OverrideKeyword => "override",
                    SyntaxKind::ConstKeyword => "const",
                    SyntaxKind::InKeyword => "in",
                    SyntaxKind::OutKeyword => "out",
                    _ => continue,
                };
                report(modifier.range, 8009, &[keyword]);
            }
        }
    }
    diagnostics.sort_by(compare_program_diagnostics);
    diagnostics
}

fn javascript_file_not_allowed_diagnostic(file_name: &str) -> ProgramDiagnostic {
    let message = message_by_code(6504).expect("TS6504 must be in the generated catalog");
    let reason = message_by_code(1430).expect("TS1430 must be in the generated catalog");
    let root = message_by_code(1427).expect("TS1427 must be in the generated catalog");
    let primary = message
        .format(&[file_name.to_owned()])
        .expect("TS6504 has one formatting argument");
    ProgramDiagnostic {
        file_name: None,
        range: None,
        code: Some(message.code()),
        category: message.category(),
        message: format!("{primary}\n  {}\n    {}", reason.text(), root.text()),
        related_information: Vec::new(),
    }
}

fn canonical_emit_unavailable_diagnostic() -> ProgramDiagnostic {
    ProgramDiagnostic {
        file_name: None,
        range: None,
        code: None,
        category: Category::Error,
        message:
            "Emit is unavailable for Programs constructed with the experimental canonical checker."
                .to_owned(),
        related_information: Vec::new(),
    }
}

fn output_overwrites_input_diagnostic(file_name: &str) -> ProgramDiagnostic {
    let message = message_by_code(5055).expect("TS5055 must be in the generated catalog");
    ProgramDiagnostic {
        file_name: None,
        range: None,
        code: Some(message.code()),
        category: message.category(),
        message: message
            .format(&[file_name.to_owned()])
            .expect("TS5055 has one formatting argument"),
        related_information: Vec::new(),
    }
}

fn output_collision_diagnostic(file_name: &str) -> ProgramDiagnostic {
    let message = message_by_code(5056).expect("TS5056 must be in the generated catalog");
    ProgramDiagnostic {
        file_name: None,
        range: None,
        code: Some(message.code()),
        category: message.category(),
        message: message
            .format(&[file_name.to_owned()])
            .expect("TS5056 has one formatting argument"),
        related_information: Vec::new(),
    }
}

fn suppress_output_path_collisions(
    output: &mut EmitOutput,
    current_directory: &str,
    case_sensitivity: CaseSensitivity,
) {
    let mut paths = BTreeMap::<String, (String, usize)>::new();
    for file in &output.files {
        let canonical = canonicalize(&file.file_name, current_directory, case_sensitivity);
        let entry = paths
            .entry(canonical)
            .or_insert_with(|| (file.file_name.clone(), 0));
        entry.1 += 1;
    }
    let collisions = paths
        .into_iter()
        .filter_map(|(canonical, (file_name, count))| (count > 1).then_some((canonical, file_name)))
        .collect::<BTreeMap<_, _>>();
    if collisions.is_empty() {
        return;
    }
    output.files.retain(|file| {
        let canonical = canonicalize(&file.file_name, current_directory, case_sensitivity);
        !collisions.contains_key(&canonical)
    });
    output.diagnostics.extend(
        collisions
            .into_values()
            .map(|file_name| output_collision_diagnostic(&file_name)),
    );
}

fn emit_declaration_only_diagnostic() -> ProgramDiagnostic {
    let message = message_by_code(5069).expect("TS5069 must be in the generated catalog");
    ProgramDiagnostic {
        file_name: None,
        range: None,
        code: Some(message.code()),
        category: message.category(),
        message: message
            .format(&[
                "emitDeclarationOnly".to_owned(),
                "declaration".to_owned(),
                "composite".to_owned(),
            ])
            .expect("TS5069 has three formatting arguments"),
        related_information: Vec::new(),
    }
}

fn incremental_requires_config_diagnostic() -> ProgramDiagnostic {
    let message = message_by_code(5074).expect("TS5074 must be in the generated catalog");
    ProgramDiagnostic {
        file_name: None,
        range: None,
        code: Some(message.code()),
        category: message.category(),
        message: message.text().to_owned(),
        related_information: Vec::new(),
    }
}

fn module_not_found_diagnostic(
    file_name: &str,
    range: TextRange,
    specifier: &str,
) -> ProgramDiagnostic {
    let message = message_by_code(2307).expect("TS2307 must be in the generated catalog");
    ProgramDiagnostic {
        file_name: Some(file_name.to_owned()),
        range: Some(range),
        code: Some(message.code()),
        category: message.category(),
        message: message
            .format(&[specifier.to_owned()])
            .expect("TS2307 has one formatting argument"),
        related_information: Vec::new(),
    }
}

fn typescript_extension_import_diagnostic(
    file_name: &str,
    range: TextRange,
    extension: &str,
) -> ProgramDiagnostic {
    let message = message_by_code(5097).expect("TS5097 must be in the generated catalog");
    ProgramDiagnostic {
        file_name: Some(file_name.to_owned()),
        range: Some(range),
        code: Some(message.code()),
        category: message.category(),
        message: message
            .format(&[extension.to_owned()])
            .expect("TS5097 has one formatting argument"),
        related_information: Vec::new(),
    }
}

fn side_effect_import_not_found_diagnostic(
    file_name: &str,
    range: TextRange,
    specifier: &str,
) -> ProgramDiagnostic {
    let message = message_by_code(2882).expect("TS2882 must be in the generated catalog");
    ProgramDiagnostic {
        file_name: Some(file_name.to_owned()),
        range: Some(range),
        code: Some(message.code()),
        category: message.category(),
        message: message
            .format(&[specifier.to_owned()])
            .expect("TS2882 has one formatting argument"),
        related_information: Vec::new(),
    }
}

fn type_definition_not_found(name: &str) -> ProgramDiagnostic {
    let message = message_by_code(2688).expect("TS2688 must be in the generated catalog");
    ProgramDiagnostic {
        file_name: None,
        range: None,
        code: Some(message.code()),
        category: message.category(),
        message: message
            .format(&[name.to_owned()])
            .expect("TS2688 has one formatting argument"),
        related_information: Vec::new(),
    }
}

fn compiler_option_key_range(
    file_name: &str,
    source: &str,
    primary: &str,
    fallback: Option<&str>,
) -> Option<TextRange> {
    compiler_option_range(file_name, source, primary, fallback, false)
}

fn compiler_option_diagnostic_range(
    file_name: &str,
    source: &str,
    diagnostic: &Diagnostic,
) -> Option<TextRange> {
    let (primary, fallback, value) = match diagnostic.code() {
        5059 => ("reactNamespace", None, true),
        5067 => ("jsxFactory", None, true),
        5095 | 5109 => ("moduleResolution", None, true),
        5110 => ("module", None, true),
        5096 => ("allowImportingTsExtensions", None, true),
        18_035 => ("jsxFragmentFactory", None, true),
        5051 | 5052 | 5053 | 5069 | 5089 | 5091 | 5098 | 6082 => (
            diagnostic.arguments.first()?.as_str(),
            diagnostic.arguments.get(1).map(String::as_str),
            false,
        ),
        _ => return None,
    };
    compiler_option_range(file_name, source, primary, fallback, value)
}

fn compiler_option_range(
    file_name: &str,
    source: &str,
    primary: &str,
    fallback: Option<&str>,
    on_value: bool,
) -> Option<TextRange> {
    let parsed = ts_config::parse_jsonc(file_name, source).value?;
    let root = parsed.as_object()?;
    let options = root.get("compilerOptions")?.as_object()?;
    let selected = std::iter::once(primary)
        .chain(fallback)
        .find_map(|option| options.keys().find(|key| key.eq_ignore_ascii_case(option)));

    let mut scanner = Scanner::new(source);
    let mut object_depth = 0usize;
    let mut options_depth = None;
    let mut pending_options = false;
    loop {
        let token = scanner.scan();
        match token.kind {
            SyntaxKind::EndOfFile => return None,
            SyntaxKind::OpenBraceToken => {
                object_depth = object_depth.checked_add(1)?;
                if pending_options {
                    options_depth = Some(object_depth);
                    pending_options = false;
                }
            }
            SyntaxKind::CloseBraceToken => {
                if options_depth == Some(object_depth) {
                    options_depth = None;
                }
                object_depth = object_depth.checked_sub(1)?;
            }
            SyntaxKind::StringLiteral => {
                let value = token.value.as_ref()?.to_string_lossy();
                let checkpoint = scanner.mark();
                let is_property = scanner.scan().kind == SyntaxKind::ColonToken;
                scanner.rewind(checkpoint);
                if !is_property {
                    continue;
                }
                if object_depth == 1 && value == "compilerOptions" {
                    if selected.is_none() {
                        return Some(token.range);
                    }
                    pending_options = true;
                } else if options_depth == Some(object_depth)
                    && selected.is_some_and(|selected| value.eq_ignore_ascii_case(selected))
                {
                    if on_value {
                        if scanner.scan().kind != SyntaxKind::ColonToken {
                            return None;
                        }
                        return Some(scanner.scan().range);
                    }
                    return Some(token.range);
                }
            }
            _ => {}
        }
    }
}

fn config_diagnostic(diagnostic: &ConfigDiagnostic) -> ProgramDiagnostic {
    ProgramDiagnostic {
        file_name: Some(diagnostic.file_name.clone()),
        range: None,
        code: Some(diagnostic.code()),
        category: diagnostic.diagnostic.category(),
        message: diagnostic.render(),
        related_information: Vec::new(),
    }
}

#[cfg(test)]
mod tests {
    use std::collections::{BTreeMap, BTreeSet};
    use std::time::{Duration, Instant};

    use ts_checker::semantic::formatter::FunctionTypeDisplayUnavailable;
    use ts_checker::semantic::{
        ArrayTypeError, AssignmentInvariant, CanonicalCheckerContextError,
        CanonicalCheckerDiagnosticRange, CanonicalGlobalInitializationError,
        CanonicalGlobalTypeInitializationError, CanonicalModuleResolutionInput,
        CanonicalModuleResolutionMode, CanonicalTypeMapperStore, DeclaredTypeError,
        DeclaredTypeHostError, DeclaredTypeUnavailable, DerivedTypeError,
        IntrinsicBootstrapOptions, RelationKind, RelationUnavailable, SourceAssertionError,
        SourceCheckError, SourceCheckProvenanceError, SourceFunctionInvariant,
        SourceLiteralCacheError, SourceObjectLiteralError, SymbolMergeError, TypeDataKind,
        TypeDisplayUnavailable, TypeNodeUnavailable, UnsupportedSourceSyntax, VariableInvariant,
    };
    use ts_core::{TextPos, TextRange};
    use ts_diagnostics::{Category, Diagnostic, message_by_code};
    use ts_options::{
        CompilerOptions, ModuleDetectionKind, ModuleKind, ModuleResolutionKind, ScriptTarget,
    };
    use ts_vfs::{FileSystem, MemoryFileSystem};

    use super::{
        CanonicalBindError, CanonicalDeclarationError, CanonicalModuleTargetOmission,
        CanonicalProgramCheckError, CanonicalProgramCheckFailureClass, CanonicalProgramQueries,
        FileId, NodeData, Program, ResolvedModuleKey, SourceFile, SyntaxKind,
        bind_source_file_in_file, canonical_source_file_facts, defer_export_only_bundle_imports,
        empty_check_result, parse_source_file, percent_encode_source_map_url,
        source_file_is_external_module,
    };

    fn plain_esm_bundler_options() -> CompilerOptions {
        CompilerOptions {
            module: ModuleKind::EsNext,
            module_specified: true,
            module_resolution: ModuleResolutionKind::Bundler,
            no_check: true,
            no_lib: true,
            ..CompilerOptions::default()
        }
    }

    #[test]
    fn parses_and_indexes_explicit_roots() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file("/project/main.ts", "const answer: number = 40 + 2;")
            .unwrap();
        let program = Program::new(&fs, "/project", &["main.ts".to_owned()]);
        assert!(
            program.diagnostics().is_empty(),
            "{:?}",
            program.diagnostics()
        );
        assert_eq!(program.source_files().len(), 1);
        assert!(program.source_file("/project/main.ts").is_some());
    }

    #[test]
    fn parser_context_comment_directives_exclude_regex_and_jsx_text() {
        let fs = MemoryFileSystem::new(true);
        let source = concat!(
            "const pattern = /[// @ts-expect-error]/;\n",
            "const view = <div>// @ts-ignore</div>;\n",
            "const visible: string = 1;\n",
            "const ready = true; // @ts-ignore\n",
            "const lineIgnored: string = 2;\n",
            "/* details\n",
            " * @ts-expect-error */\n",
            "const blockIgnored: string = 3;\n",
        );
        fs.write_file("/project/input.tsx", source).unwrap();

        let program = Program::new_with_options(
            &fs,
            "/project",
            &["input.tsx".to_owned()],
            CompilerOptions {
                jsx: ts_options::JsxEmit::Preserve,
                no_lib: true,
                ..CompilerOptions::default()
            },
        );
        let file = program.source_file("/project/input.tsx").unwrap();
        assert_eq!(file.parse.comment_directives.len(), 2);

        let mut diagnostics = program
            .diagnostics()
            .iter()
            .filter(|diagnostic| diagnostic.code == Some(2322))
            .cloned()
            .collect::<Vec<_>>();
        assert_eq!(diagnostics.len(), 3);
        program.apply_comment_directives(&mut diagnostics, &[file.id]);

        let [visible] = diagnostics.as_slice() else {
            panic!("expected one unsuppressed assignment error: {diagnostics:?}");
        };
        assert_eq!(visible.code, Some(2322));
        let range = visible.range.unwrap();
        assert!(
            source[range.start.get() as usize..range.end.get() as usize].contains("visible"),
            "unexpected diagnostic range: {range:?}"
        );
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Keeps the supported classifier matrix exhaustive.
    fn canonical_program_error_classification_accepts_capability_boundaries() {
        let parsed = parse_source_file("const value: number = 1;");
        let file = FileId::new(7);
        let node = ts_ast::NodeRef::new(parsed.arena.id(), file, parsed.source_file);
        let mut store = CanonicalTypeMapperStore::new();
        let bootstrap = store
            .initialize_intrinsic_bootstrap(IntrinsicBootstrapOptions::default())
            .unwrap();
        let type_id = bootstrap.any_type;
        let symbol = bootstrap.undefined_symbol;

        let unsupported = [
            CanonicalProgramCheckError::UnsupportedSourceKind {
                file_name: "/project/input.tsx".to_owned(),
                script_kind: ts_path::ScriptKind::Tsx,
            },
            CanonicalProgramCheckError::PlainEsmModuleResolutionUnsupported {
                file_name: "/project/input.ts".to_owned(),
                module: ModuleKind::CommonJs,
                module_resolution: ModuleResolutionKind::Bundler,
            },
            CanonicalProgramCheckError::ModuleSpecifierResolutionModeUnsupported(node),
            CanonicalProgramCheckError::ExternalModuleTargetUnsupported {
                specifier: node,
                target_file_name: "/project/script.ts".to_owned(),
            },
            CanonicalProgramCheckError::DeclarationBind {
                file_name: "/project/input.ts".to_owned(),
                error: CanonicalDeclarationError::UnsupportedDeclarationFamily(node),
            },
            CanonicalProgramCheckError::Context(
                CanonicalCheckerContextError::GlobalInitialization(
                    CanonicalGlobalInitializationError::ScriptGlobalThisDeclaration {
                        file,
                        declaration: node,
                    },
                ),
            ),
            CanonicalProgramCheckError::Context(
                CanonicalCheckerContextError::GlobalInitialization(
                    CanonicalGlobalInitializationError::GlobalTypes(
                        CanonicalGlobalTypeInitializationError::DeclaredType(
                            DeclaredTypeError::TypeNodeUnavailable(
                                TypeNodeUnavailable::TypeArgumentsUnsupported(node),
                            ),
                        ),
                    ),
                ),
            ),
            CanonicalProgramCheckError::Context(
                CanonicalCheckerContextError::GlobalInitialization(
                    CanonicalGlobalInitializationError::Merge(
                        SymbolMergeError::AliasResolutionRequired(symbol),
                    ),
                ),
            ),
            CanonicalProgramCheckError::SourceCheck {
                file_name: "/project/input.ts".to_owned(),
                error: SourceCheckError::Unsupported(UnsupportedSourceSyntax::MissingVariableType(
                    node,
                )),
            },
            CanonicalProgramCheckError::SourceCheck {
                file_name: "/project/input.ts".to_owned(),
                error: SourceCheckError::Unsupported(UnsupportedSourceSyntax::Class(node)),
            },
            CanonicalProgramCheckError::SourceCheck {
                file_name: "/project/input.ts".to_owned(),
                error: SourceCheckError::DeclaredType(DeclaredTypeError::TypeNodeUnavailable(
                    TypeNodeUnavailable::TypeArgumentsUnsupported(node),
                )),
            },
            CanonicalProgramCheckError::SourceCheck {
                file_name: "/project/input.ts".to_owned(),
                error: SourceCheckError::RelationUnavailable(
                    RelationUnavailable::StructuralRelation {
                        source: type_id,
                        target: type_id,
                        relation: RelationKind::Assignable,
                    },
                ),
            },
            CanonicalProgramCheckError::SourceCheck {
                file_name: "/project/input.ts".to_owned(),
                error: SourceCheckError::TypeDisplayUnavailable(
                    TypeDisplayUnavailable::UnsupportedType {
                        type_id,
                        kind: TypeDataKind::Conditional,
                    },
                ),
            },
            CanonicalProgramCheckError::SourceCheck {
                file_name: "/project/input.ts".to_owned(),
                error: SourceCheckError::TypeDisplayUnavailable(
                    TypeDisplayUnavailable::FunctionType {
                        type_id,
                        reason: FunctionTypeDisplayUnavailable::SourceContext,
                    },
                ),
            },
            CanonicalProgramCheckError::SourceCheck {
                file_name: "/project/input.ts".to_owned(),
                error: SourceCheckError::LiteralCache(
                    SourceLiteralCacheError::UnsupportedUnionConstituent(type_id),
                ),
            },
            CanonicalProgramCheckError::SourceCheck {
                file_name: "/project/input.ts".to_owned(),
                error: SourceCheckError::DerivedType(DerivedTypeError::UnsupportedWideningType(
                    type_id,
                )),
            },
            CanonicalProgramCheckError::SourceCheck {
                file_name: "/project/input.ts".to_owned(),
                error: SourceCheckError::DerivedType(DerivedTypeError::RecursiveWideningType(
                    type_id,
                )),
            },
        ];
        assert!(
            unsupported
                .iter()
                .all(CanonicalProgramCheckError::is_unsupported_boundary)
        );
        assert!(unsupported.iter().all(|error| {
            matches!(
                error.failure_class(),
                CanonicalProgramCheckFailureClass::Unsupported { capability_code }
                    if !capability_code.starts_with("INV.")
            )
        }));
    }

    #[test]
    fn canonical_program_failure_class_exposes_stable_fatal_codes() {
        let parsed = parse_source_file("const value = () => 1;");
        let node = ts_ast::NodeRef::new(parsed.arena.id(), FileId::new(7), parsed.source_file);
        let error = CanonicalProgramCheckError::SourceCheck {
            file_name: "/project/input.ts".to_owned(),
            error: SourceCheckError::Arrow(node),
        };

        assert_eq!(
            error.failure_class(),
            CanonicalProgramCheckFailureClass::Fatal {
                invariant_code: "INV.SOURCE.ARROW",
            }
        );
        assert!(!error.is_unsupported_boundary());

        let class_error = CanonicalProgramCheckError::SourceCheck {
            file_name: "/project/input.ts".to_owned(),
            error: SourceCheckError::Class(node),
        };
        assert_eq!(
            class_error.failure_class(),
            CanonicalProgramCheckFailureClass::Fatal {
                invariant_code: "INV.SOURCE.CLASS",
            }
        );
        assert!(!class_error.is_unsupported_boundary());
    }

    #[test]
    fn canonical_program_error_classification_separates_generic_alias_boundaries() {
        let parsed = parse_source_file("type Id<T> = T;");
        let file = FileId::new(7);
        let node = ts_ast::NodeRef::new(parsed.arena.id(), file, parsed.source_file);
        let mut store = CanonicalTypeMapperStore::new();
        let bootstrap = store
            .initialize_intrinsic_bootstrap(IntrinsicBootstrapOptions::default())
            .unwrap();
        let symbol = bootstrap.undefined_symbol;
        let type_id = bootstrap.any_type;
        let source_error = |error| CanonicalProgramCheckError::SourceCheck {
            file_name: "/project/input.ts".to_owned(),
            error: SourceCheckError::DeclaredType(DeclaredTypeError::TypeNodeUnavailable(error)),
        };

        let unsupported = [
            TypeNodeUnavailable::GenericAliasConstraintUnsupported {
                alias: symbol,
                parameter: node,
            },
            TypeNodeUnavailable::GenericAliasInstantiationUnsupported {
                alias: symbol,
                declared_type: type_id,
            },
            TypeNodeUnavailable::GenericAliasDefaultReferenceUnsupported {
                alias: symbol,
                default_type: node,
                referenced_parameter: symbol,
            },
            TypeNodeUnavailable::CircularGenericAliasDefault {
                alias: symbol,
                default_type: node,
            },
        ];
        assert!(
            unsupported
                .into_iter()
                .map(source_error)
                .all(|error| error.is_unsupported_boundary())
        );

        let invariant = [
            TypeNodeUnavailable::MissingGenericAliasMetadata(symbol),
            TypeNodeUnavailable::InvalidGenericAliasInstantiationCache(symbol),
        ];
        assert!(
            invariant
                .into_iter()
                .map(source_error)
                .all(|error| !error.is_unsupported_boundary())
        );
    }

    #[test]
    fn canonical_program_error_classification_separates_import_alias_capabilities() {
        let parsed = parse_source_file("import type { T } from './target'; const value: T = 1;");
        let file = FileId::new(7);
        let node = ts_ast::NodeRef::new(parsed.arena.id(), file, parsed.source_file);
        let mut store = CanonicalTypeMapperStore::new();
        let symbol = store
            .initialize_intrinsic_bootstrap(IntrinsicBootstrapOptions::default())
            .unwrap()
            .undefined_symbol;
        let source_error = |error| CanonicalProgramCheckError::SourceCheck {
            file_name: "/project/input.ts".to_owned(),
            error: SourceCheckError::DeclaredType(DeclaredTypeError::TypeNodeUnavailable(error)),
        };

        assert!(
            source_error(TypeNodeUnavailable::ImportAliasCapabilityUnsupported(node))
                .is_unsupported_boundary()
        );
        assert!(
            !source_error(TypeNodeUnavailable::InvalidImportAliasTarget {
                node,
                alias: symbol,
                target: symbol,
            })
            .is_unsupported_boundary()
        );
    }

    #[test]
    fn canonical_program_alias_classification_agrees_for_queries_and_display() {
        use ts_checker::semantic::SymbolDisplayError;
        use ts_checker::semantic::alias::{
            CanonicalAliasResolutionError, CanonicalAliasTargetUnavailable,
        };

        let parsed = parse_source_file("import * as target from './target';");
        let file = FileId::new(7);
        let node = ts_ast::NodeRef::new(parsed.arena.id(), file, parsed.source_file);
        let mut store = CanonicalTypeMapperStore::new();
        let symbol = store
            .initialize_intrinsic_bootstrap(IntrinsicBootstrapOptions::default())
            .unwrap()
            .undefined_symbol;
        let check = |error, unsupported| {
            assert_eq!(
                super::type_node_error_is_unsupported(&TypeNodeUnavailable::NamespaceAlias {
                    node,
                    error,
                }),
                unsupported,
            );
            assert_eq!(
                super::symbol_display_error_is_unsupported(SymbolDisplayError::Alias(error)),
                unsupported,
            );
        };
        for (reason, unsupported) in [
            (
                CanonicalAliasTargetUnavailable::ModuleResolutionEntryAbsent(node),
                true,
            ),
            (
                CanonicalAliasTargetUnavailable::UnsupportedAliasDeclaration(node),
                true,
            ),
            (
                CanonicalAliasTargetUnavailable::CommonJsModuleUnsupported {
                    declaration: node,
                    file,
                },
                true,
            ),
            (
                CanonicalAliasTargetUnavailable::InvalidAliasLinks(symbol),
                false,
            ),
            (
                CanonicalAliasTargetUnavailable::ForeignDeclaration(node),
                false,
            ),
            (
                CanonicalAliasTargetUnavailable::MalformedDeclaration(node),
                false,
            ),
        ] {
            check(
                CanonicalAliasResolutionError::TargetUnavailable {
                    alias: symbol,
                    reason,
                },
                unsupported,
            );
        }
        for error in [
            CanonicalAliasResolutionError::InvalidAliasLinks(symbol),
            CanonicalAliasResolutionError::InvalidSymbol(symbol),
            CanonicalAliasResolutionError::SymbolIsNotAlias(symbol),
            CanonicalAliasResolutionError::ResolutionStackInvariant(symbol),
        ] {
            check(error, false);
        }
    }

    #[test]
    fn canonical_program_error_classification_exhausts_function_display_boundaries() {
        let mut store = CanonicalTypeMapperStore::new();
        let type_id = store
            .initialize_intrinsic_bootstrap(IntrinsicBootstrapOptions::default())
            .unwrap()
            .any_type;
        let source_error = |reason| CanonicalProgramCheckError::SourceCheck {
            file_name: "/project/input.ts".to_owned(),
            error: SourceCheckError::TypeDisplayUnavailable(TypeDisplayUnavailable::FunctionType {
                type_id,
                reason,
            }),
        };

        let capability = [
            FunctionTypeDisplayUnavailable::SourceContext,
            FunctionTypeDisplayUnavailable::GenericAlias,
            FunctionTypeDisplayUnavailable::GenericSignature,
            FunctionTypeDisplayUnavailable::ThisParameter,
            FunctionTypeDisplayUnavailable::RestParameter,
            FunctionTypeDisplayUnavailable::InitializedParameter,
            FunctionTypeDisplayUnavailable::DestructuredParameter,
            FunctionTypeDisplayUnavailable::ParameterModifiers,
            FunctionTypeDisplayUnavailable::MissingParameterType,
            FunctionTypeDisplayUnavailable::MissingReturnType,
            FunctionTypeDisplayUnavailable::TypePredicate,
            FunctionTypeDisplayUnavailable::Overloads,
            FunctionTypeDisplayUnavailable::ConstructSignatures,
            FunctionTypeDisplayUnavailable::IndexSignatures,
            FunctionTypeDisplayUnavailable::CallableProperties,
            FunctionTypeDisplayUnavailable::UnvalidatedCallable,
        ];
        assert!(
            capability
                .into_iter()
                .map(source_error)
                .all(|error| error.is_unsupported_boundary())
        );

        let invariant = [
            FunctionTypeDisplayUnavailable::PendingSignature,
            FunctionTypeDisplayUnavailable::UnresolvedReturn,
        ];
        assert!(
            invariant
                .into_iter()
                .map(source_error)
                .all(|error| !error.is_unsupported_boundary())
        );
    }

    #[test]
    fn canonical_program_error_classification_rejects_function_relation_state_failures() {
        let mut store = CanonicalTypeMapperStore::new();
        let bootstrap = store
            .initialize_intrinsic_bootstrap(IntrinsicBootstrapOptions::default())
            .unwrap();
        let type_id = bootstrap.any_type;
        let signature = bootstrap.any_signature;
        let source_error = |error| CanonicalProgramCheckError::SourceCheck {
            file_name: "/project/input.ts".to_owned(),
            error: SourceCheckError::RelationUnavailable(error),
        };
        let invariant = [
            RelationUnavailable::UnresolvedFunctionType(type_id),
            RelationUnavailable::UnresolvedSignatureReturn(signature),
            RelationUnavailable::MalformedFunctionType(type_id),
            RelationUnavailable::StrictFunctionTypesOptionMismatch {
                established: true,
                requested: false,
            },
        ];

        assert!(
            invariant
                .into_iter()
                .map(source_error)
                .all(|error| !error.is_unsupported_boundary())
        );
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Keeps the invariant classifier matrix exhaustive.
    fn canonical_program_error_classification_rejects_invariant_failures() {
        let parsed = parse_source_file("const value: number = 1;");
        let file = FileId::new(7);
        let node = ts_ast::NodeRef::new(parsed.arena.id(), file, parsed.source_file);
        let mut store = CanonicalTypeMapperStore::new();
        let bootstrap = store
            .initialize_intrinsic_bootstrap(IntrinsicBootstrapOptions::default())
            .unwrap();
        let type_id = bootstrap.any_type;
        let symbol = bootstrap.undefined_symbol;
        let signature = bootstrap.any_signature;
        let invariant = [
            CanonicalProgramCheckError::Bind {
                file_name: "/project/input.ts".to_owned(),
                error: CanonicalBindError::InvalidSourceFile(node),
            },
            CanonicalProgramCheckError::InvalidModuleSourceFile(node),
            CanonicalProgramCheckError::InvalidModuleSpecifier(node),
            CanonicalProgramCheckError::MissingResolvedModuleTarget {
                containing_file: "/project/input.ts".to_owned(),
                specifier: node,
                resolved_file_name: "/project/missing.ts".to_owned(),
            },
            CanonicalProgramCheckError::InvalidDiagnosticNode(node),
            CanonicalProgramCheckError::InvalidRelatedDiagnosticNode {
                primary_code: 2451,
                index: 1,
                node,
            },
            CanonicalProgramCheckError::Context(
                CanonicalCheckerContextError::DuplicateFileInOrder(file),
            ),
            CanonicalProgramCheckError::Context(
                CanonicalCheckerContextError::GlobalInitialization(
                    CanonicalGlobalInitializationError::GlobalTypes(
                        CanonicalGlobalTypeInitializationError::InvalidType(type_id),
                    ),
                ),
            ),
            CanonicalProgramCheckError::Context(
                CanonicalCheckerContextError::GlobalInitialization(
                    CanonicalGlobalInitializationError::GlobalTypes(
                        CanonicalGlobalTypeInitializationError::InvalidGlobalObjectDeclaration(
                            node,
                        ),
                    ),
                ),
            ),
            CanonicalProgramCheckError::Context(
                CanonicalCheckerContextError::GlobalInitialization(
                    CanonicalGlobalInitializationError::GlobalTypes(
                        CanonicalGlobalTypeInitializationError::InvalidGlobalObjectBaseResolution(
                            type_id,
                        ),
                    ),
                ),
            ),
            CanonicalProgramCheckError::Context(
                CanonicalCheckerContextError::GlobalInitialization(
                    CanonicalGlobalInitializationError::Merge(SymbolMergeError::InvalidSymbol(
                        symbol,
                    )),
                ),
            ),
            CanonicalProgramCheckError::SourceCheck {
                file_name: "/project/input.ts".to_owned(),
                error: SourceCheckError::Provenance(SourceCheckProvenanceError::MissingFile(file)),
            },
            CanonicalProgramCheckError::SourceCheck {
                file_name: "/project/input.ts".to_owned(),
                error: SourceCheckError::LiteralCache(
                    SourceLiteralCacheError::BootstrapUninitialized,
                ),
            },
            CanonicalProgramCheckError::SourceCheck {
                file_name: "/project/input.ts".to_owned(),
                error: SourceCheckError::DeclaredType(DeclaredTypeError::Unavailable(
                    DeclaredTypeUnavailable::AliasMergedWithDeclaredSymbol(symbol),
                )),
            },
            CanonicalProgramCheckError::SourceCheck {
                file_name: "/project/input.ts".to_owned(),
                error: SourceCheckError::DeclaredType(DeclaredTypeError::Unavailable(
                    DeclaredTypeUnavailable::PostGlobalNameResolutionUnavailable,
                )),
            },
            CanonicalProgramCheckError::SourceCheck {
                file_name: "/project/input.ts".to_owned(),
                error: SourceCheckError::DeclaredType(DeclaredTypeError::TypeNodeUnavailable(
                    TypeNodeUnavailable::InvalidCachedArrayType(type_id),
                )),
            },
            CanonicalProgramCheckError::SourceCheck {
                file_name: "/project/input.ts".to_owned(),
                error: SourceCheckError::DeclaredType(DeclaredTypeError::TypeNodeUnavailable(
                    TypeNodeUnavailable::InvalidFunctionType(node),
                )),
            },
            CanonicalProgramCheckError::SourceCheck {
                file_name: "/project/input.ts".to_owned(),
                error: SourceCheckError::DeclaredType(DeclaredTypeError::TypeNodeUnavailable(
                    TypeNodeUnavailable::InvalidFunctionSignature(signature),
                )),
            },
            CanonicalProgramCheckError::SourceCheck {
                file_name: "/project/input.ts".to_owned(),
                error: SourceCheckError::RelationUnavailable(RelationUnavailable::MalformedUnion(
                    type_id,
                )),
            },
            CanonicalProgramCheckError::SourceCheck {
                file_name: "/project/input.ts".to_owned(),
                error: SourceCheckError::TypeDisplayUnavailable(
                    TypeDisplayUnavailable::InvalidUnion(type_id),
                ),
            },
            CanonicalProgramCheckError::SourceCheck {
                file_name: "/project/input.ts".to_owned(),
                error: SourceCheckError::TypeDisplayUnavailable(
                    TypeDisplayUnavailable::SourceHost(
                        DeclaredTypeHostError::DeclarationsIncomplete(file),
                    ),
                ),
            },
            CanonicalProgramCheckError::SourceCheck {
                file_name: "/project/input.ts".to_owned(),
                error: SourceCheckError::MissingDiagnostic(2322),
            },
            CanonicalProgramCheckError::SourceCheck {
                file_name: "/project/input.ts".to_owned(),
                error: SourceCheckError::Assignment(AssignmentInvariant::MissingNode(node)),
            },
            CanonicalProgramCheckError::SourceCheck {
                file_name: "/project/input.ts".to_owned(),
                error: SourceCheckError::Variable(VariableInvariant::InvalidSymbol(symbol)),
            },
            CanonicalProgramCheckError::SourceCheck {
                file_name: "/project/input.ts".to_owned(),
                error: SourceCheckError::Function(SourceFunctionInvariant::MissingCallableType(
                    symbol,
                )),
            },
            CanonicalProgramCheckError::SourceCheck {
                file_name: "/project/input.ts".to_owned(),
                error: SourceCheckError::Arrow(node),
            },
            CanonicalProgramCheckError::SourceCheck {
                file_name: "/project/input.ts".to_owned(),
                error: SourceCheckError::Call(node),
            },
            CanonicalProgramCheckError::SourceCheck {
                file_name: "/project/input.ts".to_owned(),
                error: SourceCheckError::Enum(node),
            },
            CanonicalProgramCheckError::SourceCheck {
                file_name: "/project/input.ts".to_owned(),
                error: SourceCheckError::Import(node),
            },
            CanonicalProgramCheckError::SourceCheck {
                file_name: "/project/input.ts".to_owned(),
                error: SourceCheckError::Class(node),
            },
            CanonicalProgramCheckError::SourceCheck {
                file_name: "/project/input.ts".to_owned(),
                error: SourceCheckError::Property(node),
            },
            CanonicalProgramCheckError::SourceCheck {
                file_name: "/project/input.ts".to_owned(),
                error: SourceCheckError::Element(node),
            },
            CanonicalProgramCheckError::SourceCheck {
                file_name: "/project/input.ts".to_owned(),
                error: SourceCheckError::PrimitiveOperator(node),
            },
            CanonicalProgramCheckError::SourceCheck {
                file_name: "/project/input.ts".to_owned(),
                error: SourceCheckError::LogicalOperator(node),
            },
            CanonicalProgramCheckError::SourceCheck {
                file_name: "/project/input.ts".to_owned(),
                error: SourceCheckError::Conditional(node),
            },
            CanonicalProgramCheckError::SourceCheck {
                file_name: "/project/input.ts".to_owned(),
                error: SourceCheckError::ArrayType(ArrayTypeError::InvalidReference(type_id)),
            },
            CanonicalProgramCheckError::SourceCheck {
                file_name: "/project/input.ts".to_owned(),
                error: SourceCheckError::LiteralCache(SourceLiteralCacheError::ArrayType(
                    ArrayTypeError::InvalidReference(type_id),
                )),
            },
            CanonicalProgramCheckError::SourceCheck {
                file_name: "/project/input.ts".to_owned(),
                error: SourceCheckError::DerivedType(DerivedTypeError::InvalidWidenedTypeCache {
                    source: type_id,
                    cached: type_id,
                }),
            },
            CanonicalProgramCheckError::SourceCheck {
                file_name: "/project/input.ts".to_owned(),
                error: SourceCheckError::DerivedType(DerivedTypeError::ArrayType(
                    ArrayTypeError::InvalidReference(type_id),
                )),
            },
            CanonicalProgramCheckError::SourceCheck {
                file_name: "/project/input.ts".to_owned(),
                error: SourceCheckError::Assertion(SourceAssertionError::InvalidOperandCache {
                    node,
                    cached: None,
                    expected: type_id,
                }),
            },
            CanonicalProgramCheckError::SourceCheck {
                file_name: "/project/input.ts".to_owned(),
                error: SourceCheckError::RelationUnavailable(
                    RelationUnavailable::MalformedCanonicalArrayReference(type_id),
                ),
            },
            CanonicalProgramCheckError::SourceCheck {
                file_name: "/project/input.ts".to_owned(),
                error: SourceCheckError::TypeDisplayUnavailable(TypeDisplayUnavailable::ArrayType(
                    ArrayTypeError::InvalidReference(type_id),
                )),
            },
        ];
        assert!(
            invariant
                .iter()
                .all(|error| !error.is_unsupported_boundary())
        );
    }

    #[test]
    fn canonical_program_classifies_object_literal_cache_errors_as_invariants() {
        let parsed = parse_source_file("const value = {};");
        let file = FileId::new(7);
        let node = ts_ast::NodeRef::new(parsed.arena.id(), file, parsed.source_file);
        let mut store = CanonicalTypeMapperStore::new();
        let type_id = store
            .initialize_intrinsic_bootstrap(IntrinsicBootstrapOptions::default())
            .unwrap()
            .any_type;
        let errors = [
            SourceObjectLiteralError::Capacity(node),
            SourceObjectLiteralError::InvalidCache {
                node,
                type_: Some(type_id),
            },
        ];

        assert!(errors.into_iter().all(|error| {
            !CanonicalProgramCheckError::SourceCheck {
                file_name: "/project/input.ts".to_owned(),
                error: SourceCheckError::ObjectLiteral(error),
            }
            .is_unsupported_boundary()
        }));
    }

    #[test]
    fn canonical_module_manifest_preserves_static_node_identity_and_unresolved_results() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file("/project/target.ts", "export const value: number = 1;")
            .unwrap();
        fs.write_file(
            "/project/importer.ts",
            concat!(
                "import { value as first } from './target';\n",
                "import { value as second } from './target';\n",
                "export { value as third } from './target';\n",
                "import './missing';\n",
                "type Deferred = import('./target').value;\n",
                "const deferred = import('./target');\n",
            ),
        )
        .unwrap();
        assert!(!fs.file_exists("/project/package.json"));

        let program = Program::new_with_options(
            &fs,
            "/project",
            &["importer.ts".to_owned()],
            plain_esm_bundler_options(),
        );
        let importer = program.source_file("/project/importer.ts").unwrap();
        let target = program.source_file("/project/target.ts").unwrap();
        assert!(
            importer.id.index() < target.id.index(),
            "importer must load first"
        );

        let manifest = program.canonical_module_resolution_manifest().unwrap();
        let entries = manifest.entries();
        assert_eq!(entries.len(), 5);
        let entry_texts = entries
            .iter()
            .map(
                |entry| match &program.node(entry.specifier()).unwrap().data {
                    NodeData::StringLiteral(literal) => literal.text.as_str(),
                    other => panic!("unexpected module specifier {other:?}"),
                },
            )
            .collect::<Vec<_>>();
        assert_eq!(
            entry_texts,
            ["./target", "./target", "./target", "./missing", "./target"]
        );

        let resolved_specifiers = entries[..3]
            .iter()
            .chain(&entries[4..])
            .map(|entry| entry.specifier())
            .collect::<BTreeSet<_>>();
        assert_eq!(resolved_specifiers.len(), 4);
        for entry in entries[..3].iter().chain(&entries[4..]) {
            let CanonicalModuleResolutionInput::Resolved(resolved) = entry.resolution() else {
                panic!("static target import should resolve");
            };
            assert_eq!(resolved.target_file(), target.id);
            assert_eq!(resolved.usage_mode(), CanonicalModuleResolutionMode::Esm);
            assert_eq!(resolved.target_mode(), CanonicalModuleResolutionMode::Esm);
        }
        assert_eq!(
            entries[3].resolution(),
            CanonicalModuleResolutionInput::Unresolved
        );

        let dynamic = entries[4].specifier();
        let parent = program.node(dynamic).unwrap().parent.unwrap();
        let parent = ts_ast::NodeRef::new(dynamic.arena, dynamic.file, parent);
        let call_node = program.node(parent).unwrap();
        let NodeData::CallExpression(call) = &call_node.data else {
            panic!("the dynamic import specifier must retain its original call");
        };
        assert!(ts_ast::is_import_call(&importer.parse.arena, call_node));
        assert_eq!(call.arguments.nodes.as_slice(), &[dynamic.node]);

        let all_target_literals = importer
            .parse
            .arena
            .iter()
            .filter(|(_, node)| {
                matches!(
                    &node.data,
                    NodeData::StringLiteral(literal) if literal.text == "./target"
                )
            })
            .count();
        assert_eq!(all_target_literals, 5);
    }

    #[test]
    fn canonical_module_manifest_requires_proven_omissions_for_unretained_targets() {
        for (depth_limit, explicit_root) in [(0, false), (1, false), (0, true)] {
            let fs = MemoryFileSystem::new(true);
            fs.write_file("/project/main.ts", "import 'dependency'; export {};")
                .unwrap();
            fs.write_file(
                "/project/node_modules/dependency/package.json",
                r#"{"main":"index.js"}"#,
            )
            .unwrap();
            fs.write_file(
                "/project/node_modules/dependency/index.js",
                "export const value = 1;",
            )
            .unwrap();
            let mut roots = vec!["main.ts".to_owned()];
            if explicit_root {
                roots.push("node_modules/dependency/index.js".to_owned());
            }
            let mut program = Program::new_with_options(
                &fs,
                "/project",
                &roots,
                CompilerOptions {
                    allow_js: true,
                    no_check: true,
                    no_lib: true,
                    types: Some(Vec::new()),
                    max_node_module_js_depth: Some(depth_limit),
                    ..plain_esm_bundler_options()
                },
            );
            let admitted = depth_limit > 0 || explicit_root;
            let retained_target = program
                .source_files
                .iter()
                .find(|source| source.file_name == "/project/node_modules/dependency/index.js")
                .map(|source| source.id);
            assert_eq!(retained_target.is_some(), admitted);
            if explicit_root {
                assert_eq!(
                    program
                        .source_node_module_depths
                        .get(&retained_target.unwrap()),
                    Some(&0)
                );
            }
            if admitted {
                assert!(
                    program
                        .file_index
                        .remove("/project/node_modules/dependency/index.js")
                        .is_some()
                );
            } else {
                program.resolved_module_loads.clear();
            }
            let file_index = program.file_index.clone();
            let resolved_modules = program.resolved_modules.clone();
            let raw_resolutions = program.graph_resolutions.clone();
            let error = program.canonical_module_resolution_manifest().unwrap_err();
            assert!(matches!(
                error,
                CanonicalProgramCheckError::MissingResolvedModuleTarget { .. }
            ));
            assert!(!error.failure_class().is_unsupported());
            assert_eq!(
                error.failure_class().code(),
                "INV.PROGRAM.MISSING_MODULE_TARGET"
            );
            assert_eq!(program.file_index, file_index);
            assert_eq!(program.resolved_modules, resolved_modules);
            assert_eq!(program.graph_resolutions, raw_resolutions);
        }
    }

    #[test]
    fn canonical_module_manifest_keeps_later_admission_fatal_after_index_loss() {
        let fs = MemoryFileSystem::new(true);
        for (path, text) in [
            (
                "/project/main.ts",
                "import 'outer'; import './bridge'; export {};",
            ),
            (
                "/project/node_modules/outer/package.json",
                r#"{"types":"index.ts"}"#,
            ),
            (
                "/project/node_modules/outer/index.ts",
                "import 'dependency'; export {};",
            ),
            (
                "/project/bridge.ts",
                "import './node_modules/dependency/index.js'; export {};",
            ),
            (
                "/project/node_modules/dependency/package.json",
                r#"{"main":"index.js"}"#,
            ),
            (
                "/project/node_modules/dependency/index.js",
                "export const value = 1;",
            ),
        ] {
            fs.write_file(path, text).unwrap();
        }
        let mut program = Program::new_with_options(
            &fs,
            "/project",
            &["main.ts".to_owned()],
            CompilerOptions {
                allow_js: true,
                no_check: true,
                no_lib: true,
                types: Some(Vec::new()),
                max_node_module_js_depth: Some(1),
                ..plain_esm_bundler_options()
            },
        );
        let containing = "/project/node_modules/outer/index.ts";
        let target = "/project/node_modules/dependency/index.js";
        let target_id = program.source_file(target).unwrap().id;
        assert_eq!(program.source_node_module_depths.get(&target_id), Some(&1));
        let first_edge = program
            .resolved_module_loads
            .get(&ResolvedModuleKey::new(
                containing.to_owned(),
                "dependency".to_owned(),
                CanonicalModuleResolutionMode::Esm,
            ))
            .unwrap();
        assert!(matches!(
            program.source_load_omission(first_edge.0, &first_edge.1),
            Some(CanonicalModuleTargetOmission::NodeModuleJavaScriptDepth { depth: 2, limit: 1 })
        ));
        assert!(program.canonical_module_resolution_manifest().is_ok());
        let resolved_modules = program.resolved_modules.clone();
        let raw_resolutions = program.graph_resolutions.clone();
        assert!(program.file_index.remove(target).is_some());

        let error = program.canonical_module_resolution_manifest().unwrap_err();
        assert!(matches!(
            &error,
            CanonicalProgramCheckError::MissingResolvedModuleTarget {
                containing_file,
                resolved_file_name,
                ..
            } if containing_file == containing && resolved_file_name == target
        ));
        assert!(!error.failure_class().is_unsupported());
        assert_eq!(
            error.failure_class().code(),
            "INV.PROGRAM.MISSING_MODULE_TARGET"
        );
        assert!(!program.file_index.contains_key(target));
        assert!(
            program
                .source_files
                .iter()
                .any(|source| source.id == target_id)
        );
        assert_eq!(program.resolved_modules, resolved_modules);
        assert_eq!(program.graph_resolutions, raw_resolutions);
    }

    #[test]
    fn canonical_module_manifest_resolves_nested_ambient_imports_in_source_order() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/modules.d.ts",
            concat!(
                "declare module 'target' { export interface Value {} }\n",
                "declare module 'source' {\n",
                "  import { Value as first } from 'target';\n",
                "  namespace Nested { import second = require('target'); }\n",
                "  import { Missing } from 'missing';\n",
                "}\n",
            ),
        )
        .unwrap();

        let program = Program::new_with_options(
            &fs,
            "/project",
            &["modules.d.ts".to_owned()],
            plain_esm_bundler_options(),
        );
        let source = program.source_file("/project/modules.d.ts").unwrap();
        let manifest = program.canonical_module_resolution_manifest().unwrap();
        let entries = manifest.entries();
        assert_eq!(entries.len(), 3);
        assert_eq!(
            entries
                .iter()
                .map(
                    |entry| match &program.node(entry.specifier()).unwrap().data {
                        NodeData::StringLiteral(literal) => literal.text.as_str(),
                        other => panic!("unexpected ambient module specifier {other:?}"),
                    }
                )
                .collect::<Vec<_>>(),
            ["target", "target", "missing"],
        );
        assert_ne!(entries[0].specifier(), entries[1].specifier());
        for (entry, expected_mode) in entries[..2].iter().zip([
            CanonicalModuleResolutionMode::Esm,
            CanonicalModuleResolutionMode::CommonJs,
        ]) {
            let CanonicalModuleResolutionInput::Resolved(resolution) = entry.resolution() else {
                panic!("expected the same-file ambient target to resolve")
            };
            assert_eq!(resolution.target_file(), source.id);
            assert_eq!(resolution.usage_mode(), expected_mode);
        }
        assert_eq!(
            entries[2].resolution(),
            CanonicalModuleResolutionInput::Unresolved,
        );
    }

    #[test]
    fn canonical_module_manifest_interleaves_ambient_and_top_level_imports() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file("/project/first.ts", "export const first = 1;")
            .unwrap();
        fs.write_file("/project/target.ts", "export interface Value {}")
            .unwrap();
        fs.write_file("/project/middle.ts", "export const middle = 1;")
            .unwrap();
        fs.write_file("/project/last.ts", "export const last = 1;")
            .unwrap();
        fs.write_file(
            "/project/input.ts",
            concat!(
                "import { first } from './first';\n",
                "declare module 'wrapper' {\n",
                "  import type { Value } from './target' ",
                "with { 'resolution-mode': 'require' };\n",
                "  export { middle } from './middle';\n",
                "}\n",
                "export { last } from './last';\n",
            ),
        )
        .unwrap();

        let program = Program::new_with_options(
            &fs,
            "/project",
            &["input.ts".to_owned()],
            plain_esm_bundler_options(),
        );
        let manifest = program.canonical_module_resolution_manifest().unwrap();
        let entries = manifest.entries();
        assert_eq!(entries.len(), 5);
        assert_eq!(
            entries[1].resolution(),
            CanonicalModuleResolutionInput::Unresolved,
        );
        assert!(matches!(
            &program.node(entries[1].specifier()).unwrap().data,
            NodeData::StringLiteral(literal) if literal.text == "wrapper"
        ));
        for (entry, (expected_text, expected_mode)) in
            [entries[0], entries[2], entries[3], entries[4]]
                .iter()
                .zip([
                    ("./first", CanonicalModuleResolutionMode::Esm),
                    ("./target", CanonicalModuleResolutionMode::CommonJs),
                    ("./middle", CanonicalModuleResolutionMode::Esm),
                    ("./last", CanonicalModuleResolutionMode::Esm),
                ])
        {
            let NodeData::StringLiteral(literal) = &program.node(entry.specifier()).unwrap().data
            else {
                panic!("expected a source-owned static module specifier")
            };
            assert_eq!(literal.text, expected_text);
            let CanonicalModuleResolutionInput::Resolved(resolution) = entry.resolution() else {
                panic!("expected {expected_text} to resolve")
            };
            assert_eq!(resolution.usage_mode(), expected_mode);
            let expected_path = format!("/project/{}.ts", &expected_text[2..]);
            assert_eq!(
                resolution.target_file(),
                program.source_file(&expected_path).unwrap().id,
            );
        }
    }

    #[test]
    fn canonical_module_manifest_rejects_invalid_nested_ambient_parent_links() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/modules.d.ts",
            "declare module 'source' { import { Value } from 'target'; }",
        )
        .unwrap();
        let mut program = Program::new_with_options(
            &fs,
            "/project",
            &["modules.d.ts".to_owned()],
            plain_esm_bundler_options(),
        );
        let index = program
            .source_file("/project/modules.d.ts")
            .unwrap()
            .id
            .index();
        let source = &mut program.source_files[index];
        let import = source
            .parse
            .arena
            .iter()
            .find_map(|(id, node)| {
                matches!(node.data, NodeData::ImportDeclaration(_)).then_some(id)
            })
            .unwrap();
        source.parse.arena.get_mut(import).unwrap().parent = Some(source.parse.source_file);
        let expected =
            ts_ast::NodeRef::new(source.parse.arena.id(), source.id, source.parse.source_file);

        assert!(matches!(
            program.canonical_module_resolution_manifest(),
            Err(CanonicalProgramCheckError::InvalidModuleSourceFile(actual)) if actual == expected
        ));
    }

    #[test]
    fn canonical_module_manifest_resolves_reparsed_jsdoc_typedef_imports_once() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file("/project/target.ts", "export const value: number = 1;")
            .unwrap();
        fs.write_file(
            "/project/input.js",
            concat!(
                "/** @typedef {import('./target').First | import('./target').Second} Pair */\n",
                "/** @typedef {import('./missing').Missing} Missing */\n",
                "export const value = 1;\n",
            ),
        )
        .unwrap();
        let mut options = plain_esm_bundler_options();
        options.allow_js = true;
        options.no_check = false;
        options.no_emit = true;

        let (program, missing_range) = Program::try_new_with_canonical_checker_and_queries(
            &fs,
            "/project",
            &["input.js".to_owned()],
            options,
            |program, queries| {
                let target = program.source_file("/project/target.ts").unwrap();
                let manifest = program.canonical_module_resolution_manifest().unwrap();
                let entries = manifest.entries();
                assert_eq!(entries.len(), 3);
                assert_eq!(
                    entries
                        .iter()
                        .map(|entry| {
                            match &program.node(entry.specifier()).unwrap().data {
                                NodeData::StringLiteral(literal) => literal.text.as_str(),
                                other => panic!("unexpected JSDoc module specifier {other:?}"),
                            }
                        })
                        .collect::<Vec<_>>(),
                    ["./target", "./target", "./missing"],
                );
                assert_eq!(
                    entries
                        .iter()
                        .map(|entry| entry.specifier())
                        .collect::<BTreeSet<_>>()
                        .len(),
                    entries.len(),
                );

                for entry in &entries[..2] {
                    let CanonicalModuleResolutionInput::Resolved(resolution) = entry.resolution()
                    else {
                        panic!("the JSDoc typedef target must resolve")
                    };
                    assert_eq!(resolution.target_file(), target.id);
                    assert_eq!(resolution.usage_mode(), CanonicalModuleResolutionMode::Esm);
                    assert_eq!(resolution.target_mode(), CanonicalModuleResolutionMode::Esm);
                    assert!(matches!(
                        queries.module_resolution(entry.specifier()),
                        super::CanonicalModuleResolutionLookup::Resolved(resolved)
                            if resolved.target_file() == target.id
                    ));
                }

                let missing = entries[2];
                assert_eq!(
                    missing.resolution(),
                    CanonicalModuleResolutionInput::Unresolved,
                );
                assert_eq!(
                    queries.module_resolution(missing.specifier()),
                    super::CanonicalModuleResolutionLookup::Unresolved,
                );
                program.node(missing.specifier()).unwrap().range
            },
        )
        .unwrap();

        let missing_range = missing_range.unwrap();
        let missing_diagnostics = program
            .diagnostics()
            .iter()
            .filter(|diagnostic| diagnostic.code == Some(2307))
            .collect::<Vec<_>>();
        let [diagnostic] = missing_diagnostics.as_slice() else {
            panic!("expected one missing JSDoc import diagnostic: {missing_diagnostics:?}")
        };
        assert_eq!(diagnostic.file_name.as_deref(), Some("/project/input.js"));
        assert_eq!(diagnostic.range, Some(missing_range));
    }

    #[test]
    fn canonical_module_manifest_ignores_detached_arena_declarations() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file("/project/target.ts", "export const value: number = 1;")
            .unwrap();
        fs.write_file("/project/importer.ts", "import { value } from './target';")
            .unwrap();
        let mut program = Program::new_with_options(
            &fs,
            "/project",
            &["importer.ts".to_owned()],
            plain_esm_bundler_options(),
        );
        let importer_index = program
            .source_file("/project/importer.ts")
            .unwrap()
            .id
            .index();
        let detached_import = program.source_files[importer_index]
            .parse
            .arena
            .iter()
            .find_map(|(_, node)| {
                matches!(&node.data, NodeData::ImportDeclaration(_)).then(|| node.clone())
            })
            .unwrap();
        let detached = program.source_files[importer_index]
            .parse
            .arena
            .alloc(detached_import);
        let source = &program.source_files[importer_index];
        let NodeData::SourceFile(root) = &source
            .parse
            .arena
            .get(source.parse.source_file)
            .unwrap()
            .data
        else {
            panic!("importer root must remain a source file");
        };
        assert!(!root.statements.nodes.contains(&detached));

        let manifest = program.canonical_module_resolution_manifest().unwrap();
        assert_eq!(manifest.entries().len(), 1);
        assert!(matches!(
            manifest.entries()[0].resolution(),
            CanonicalModuleResolutionInput::Resolved(_)
        ));
    }

    #[test]
    fn canonical_module_manifest_skips_recovered_bigint_import_specifiers() {
        for recovered in [
            r#"import { 0n as broken } from "./broken";"#,
            r#"import { broken as 0n } from "./broken";"#,
        ] {
            let fs = MemoryFileSystem::new(true);
            fs.write_file("/project/target.ts", "export const value: number = 1;")
                .unwrap();
            fs.write_file(
                "/project/importer.ts",
                &format!("import {{ value }} from './target';\n{recovered}"),
            )
            .unwrap();
            let program = Program::new_with_options(
                &fs,
                "/project",
                &["importer.ts".to_owned()],
                plain_esm_bundler_options(),
            );

            assert_eq!(
                program
                    .diagnostics()
                    .iter()
                    .filter_map(|diagnostic| diagnostic.code)
                    .collect::<Vec<_>>(),
                [1003, 1128, 1434],
                "{recovered}: {:?}",
                program.diagnostics()
            );
            let manifest = program
                .canonical_module_resolution_manifest()
                .unwrap_or_else(|error| panic!("{recovered}: {error:?}"));
            let [entry] = manifest.entries() else {
                panic!("expected only the valid module import: {recovered}");
            };
            let CanonicalModuleResolutionInput::Resolved(resolved) = entry.resolution() else {
                panic!("the neighboring valid module import must resolve: {recovered}");
            };
            assert_eq!(
                resolved.target_file(),
                program.source_file("/project/target.ts").unwrap().id
            );
        }
    }

    #[test]
    fn canonical_module_manifest_rejects_corrupted_specifier_nodes_as_invariants() {
        for missing_node in [false, true] {
            let fs = MemoryFileSystem::new(true);
            fs.write_file("/project/target.ts", "export const value: number = 1;")
                .unwrap();
            fs.write_file("/project/importer.ts", "import { value } from './target';")
                .unwrap();
            let mut program = Program::new_with_options(
                &fs,
                "/project",
                &["importer.ts".to_owned()],
                plain_esm_bundler_options(),
            );
            let importer_index = program
                .source_file("/project/importer.ts")
                .unwrap()
                .id
                .index();
            let source = &mut program.source_files[importer_index];
            let statement = match &source
                .parse
                .arena
                .get(source.parse.source_file)
                .unwrap()
                .data
            {
                NodeData::SourceFile(file) => file.statements.nodes[0],
                _ => panic!("expected an importer source file"),
            };
            let specifier = match &source.parse.arena.get(statement).unwrap().data {
                NodeData::ImportDeclaration(import) => import.module_specifier,
                _ => panic!("expected an import declaration"),
            };
            let expected = if missing_node {
                let missing = ts_ast::NodeId::new(u32::MAX);
                let NodeData::ImportDeclaration(import) =
                    &mut source.parse.arena.get_mut(statement).unwrap().data
                else {
                    panic!("expected a mutable import declaration");
                };
                import.module_specifier = missing;
                missing
            } else {
                source.parse.arena.get_mut(specifier).unwrap().kind = SyntaxKind::Identifier;
                specifier
            };

            let Err(error) = program.canonical_module_resolution_manifest() else {
                panic!("expected an invalid module specifier, missing={missing_node}");
            };
            assert!(!error.is_unsupported_boundary(), "{error:?}");
            assert!(matches!(
                error,
                CanonicalProgramCheckError::InvalidModuleSpecifier(actual)
                    if actual.node == expected
            ));
        }
    }

    #[test]
    fn canonical_module_manifest_preserves_commonjs_and_esm_configuration() {
        for (module, module_resolution, expected_mode) in [
            (
                ModuleKind::CommonJs,
                ModuleResolutionKind::Bundler,
                CanonicalModuleResolutionMode::CommonJs,
            ),
            (
                ModuleKind::CommonJs,
                ModuleResolutionKind::Node10,
                CanonicalModuleResolutionMode::CommonJs,
            ),
            (
                ModuleKind::EsNext,
                ModuleResolutionKind::Node10,
                CanonicalModuleResolutionMode::Esm,
            ),
        ] {
            let fs = MemoryFileSystem::new(true);
            fs.write_file("/project/target.ts", "export const value: number = 1;")
                .unwrap();
            fs.write_file("/project/importer.ts", "import { value } from './target';")
                .unwrap();
            let mut options = plain_esm_bundler_options();
            options.module = module;
            options.module_resolution = module_resolution;
            let program =
                Program::new_with_options(&fs, "/project", &["importer.ts".to_owned()], options);

            let manifest = program.canonical_module_resolution_manifest().unwrap();
            let [entry] = manifest.entries() else {
                panic!("expected one module resolution for {module:?}/{module_resolution:?}");
            };
            let CanonicalModuleResolutionInput::Resolved(resolved) = entry.resolution() else {
                panic!("expected a resolved module for {module:?}/{module_resolution:?}");
            };
            assert_eq!(resolved.usage_mode(), expected_mode);
            assert_eq!(resolved.target_mode(), expected_mode);
        }
    }

    #[test]
    fn canonical_module_manifest_retains_import_equals_and_attribute_modes() {
        for (importer_text, expected_mode) in [
            (
                "import value = require('./target');",
                CanonicalModuleResolutionMode::CommonJs,
            ),
            (
                "import { value } from './target' with { type: 'json' };",
                CanonicalModuleResolutionMode::Esm,
            ),
            (
                concat!(
                    "import type { Value } from './target' ",
                    "with { 'resolution-mode': 'require' };",
                ),
                CanonicalModuleResolutionMode::CommonJs,
            ),
        ] {
            let fs = MemoryFileSystem::new(true);
            fs.write_file("/project/target.ts", "export const value: number = 1;")
                .unwrap();
            fs.write_file("/project/importer.ts", importer_text)
                .unwrap();
            let program = Program::new_with_options(
                &fs,
                "/project",
                &["importer.ts".to_owned()],
                plain_esm_bundler_options(),
            );

            let manifest = program.canonical_module_resolution_manifest().unwrap();
            let [entry] = manifest.entries() else {
                panic!("expected one module resolution for {importer_text}");
            };
            let CanonicalModuleResolutionInput::Resolved(resolved) = entry.resolution() else {
                panic!("expected a resolved module for {importer_text}");
            };
            assert_eq!(resolved.usage_mode(), expected_mode);
            assert_eq!(resolved.target_mode(), CanonicalModuleResolutionMode::Esm);
        }
    }

    #[test]
    fn canonical_module_manifest_admits_plain_declaration_targets() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/target.d.ts",
            "export declare const value: number;",
        )
        .unwrap();
        fs.write_file("/project/importer.ts", "import { value } from './target';")
            .unwrap();
        let program = Program::new_with_options(
            &fs,
            "/project",
            &["importer.ts".to_owned()],
            plain_esm_bundler_options(),
        );

        let target = program.source_file("/project/target.d.ts").unwrap();
        let manifest = program.canonical_module_resolution_manifest().unwrap();
        let [entry] = manifest.entries() else {
            panic!("expected one declaration-target resolution entry");
        };
        let ts_checker::semantic::CanonicalModuleResolutionInput::Resolved(resolution) =
            entry.resolution()
        else {
            panic!("expected the declaration target to resolve");
        };
        assert_eq!(resolution.target_file(), target.id);
        assert_eq!(resolution.usage_mode(), CanonicalModuleResolutionMode::Esm);
        assert_eq!(resolution.target_mode(), CanonicalModuleResolutionMode::Esm);
    }

    #[test]
    fn canonical_module_manifest_admits_matching_ambient_script_targets() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/modules.d.ts",
            concat!(
                "declare module 'first' { export const value: number; } ",
                "declare module 'second' { export const value: string; }",
            ),
        )
        .unwrap();
        fs.write_file(
            "/project/importer.ts",
            concat!(
                "/// <reference path='./modules.d.ts' />\n",
                "import { value as first } from 'first'; ",
                "import { value as second } from 'second';",
            ),
        )
        .unwrap();
        let program = Program::new_with_options(
            &fs,
            "/project",
            &["importer.ts".to_owned()],
            plain_esm_bundler_options(),
        );

        let target = program.source_file("/project/modules.d.ts").unwrap();
        let manifest = program.canonical_module_resolution_manifest().unwrap();
        assert_eq!(manifest.entries().len(), 2);
        for entry in manifest.entries() {
            let CanonicalModuleResolutionInput::Resolved(resolution) = entry.resolution() else {
                panic!("expected the ambient module to resolve");
            };
            assert_eq!(resolution.target_file(), target.id);
        }
    }

    #[test]
    fn canonical_module_manifest_rejects_resolved_script_targets_as_a_typed_boundary() {
        for source in [
            "const value: number = 1;",
            "declare module 'unrelated' { export const value: number; }",
        ] {
            let fs = MemoryFileSystem::new(true);
            fs.write_file("/project/script.ts", source).unwrap();
            fs.write_file("/project/importer.ts", "import { value } from './script';")
                .unwrap();
            let program = Program::new_with_options(
                &fs,
                "/project",
                &["importer.ts".to_owned()],
                plain_esm_bundler_options(),
            );

            let error = program.canonical_module_resolution_manifest().unwrap_err();
            assert!(error.is_unsupported_boundary(), "{source}: {error:?}");
            assert!(matches!(
                error,
                CanonicalProgramCheckError::ExternalModuleTargetUnsupported {
                    target_file_name,
                    ..
                } if target_file_name == "/project/script.ts"
            ));
        }
    }

    #[test]
    fn canonical_program_projects_unchecked_indexed_access_to_array_reads() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/input.ts",
            "const values: number[] = [1]; const value: number | undefined = values[0];",
        )
        .unwrap();

        for (no_unchecked_indexed_access, expected) in
            [(false, "number"), (true, "number | undefined")]
        {
            let (program, indexed_type) = Program::try_new_with_canonical_checker_and_queries(
                &fs,
                "/project",
                &["input.ts".to_owned()],
                CompilerOptions {
                    lib: Some(vec!["es5".to_owned()]),
                    strict_null_checks: true,
                    strict_null_checks_specified: true,
                    no_unchecked_indexed_access,
                    ..CompilerOptions::default()
                },
                |program, queries| {
                    let source = program.source_file("/project/input.ts").unwrap();
                    let indexed = source
                        .parse
                        .arena
                        .iter()
                        .find_map(|(node, record)| {
                            (record.kind == SyntaxKind::ElementAccessExpression)
                                .then(|| source.node_ref(node).unwrap())
                        })
                        .unwrap();
                    let indexed_type = queries.get_type_at_location(indexed).unwrap();
                    queries.type_to_string(indexed_type).unwrap()
                },
            )
            .unwrap();

            assert_eq!(indexed_type.as_deref(), Some(expected));
            assert!(
                program.diagnostics().is_empty(),
                "{:?}",
                program.diagnostics()
            );
        }
    }

    #[test]
    fn canonical_program_enforces_bigint_literal_targets_without_rejecting_literal_types() {
        let fs = MemoryFileSystem::new(true);
        let source = concat!(
            "type Allowed = 255n; ",
            "const decimal = 255n; ",
            "const hexadecimal = 0xffn; ",
            "const negative = -255n;",
        );
        fs.write_file("/project/input.ts", source).unwrap();

        for (target, expected) in [
            (ScriptTarget::Es5, 3),
            (ScriptTarget::Es2019, 3),
            (ScriptTarget::Es2020, 0),
            (ScriptTarget::EsNext, 0),
        ] {
            let program = Program::try_new_with_canonical_checker(
                &fs,
                "/project",
                &["input.ts".to_owned()],
                CompilerOptions {
                    lib: Some(vec!["es5".to_owned()]),
                    target,
                    ..CompilerOptions::default()
                },
            )
            .unwrap_or_else(|error| panic!("target {target:?}: {error:?}"));

            let diagnostics = program.diagnostics();
            assert_eq!(diagnostics.len(), expected, "target {target:?}");
            for (diagnostic, spelling) in diagnostics.iter().zip(["255n", "0xffn", "255n"]) {
                assert_eq!(diagnostic.code, Some(2737), "target {target:?}");
                let range = diagnostic.range.unwrap();
                assert_eq!(
                    &source[range.start.get() as usize..range.end.get() as usize],
                    spelling,
                );
                assert_eq!(
                    diagnostic.message,
                    "BigInt literals are not available when targeting lower than ES2020.",
                );
            }
        }
    }

    #[test]
    fn canonical_program_checks_quantifier_ranges_and_parse_error_gate() {
        for (separator, parse_errors, quantifier_errors) in [(";", 0, 1), ("", 1, 0)] {
            let fs = MemoryFileSystem::new(true);
            let source = format!(
                "const before = 1{separator} const pattern = /a{{8,7}}/; const wrong: string = 1;"
            );
            fs.write_file("/project/input.ts", &source).unwrap();
            let (program, cold) = Program::try_new_with_canonical_checker_and_queries(
                &fs,
                "/project",
                &["input.ts".to_owned()],
                CompilerOptions {
                    lib: Some(vec!["es5".to_owned()]),
                    target: ScriptTarget::EsNext,
                    ..CompilerOptions::default()
                },
                |_, queries| {
                    let cold = queries.cold_diagnostic_snapshot();
                    assert_eq!(queries.replay_sources().unwrap(), cold);
                    cold
                },
            )
            .unwrap();
            assert_eq!(cold.as_deref(), Some(program.diagnostics()));
            assert_eq!(
                program
                    .source_file("/project/input.ts")
                    .unwrap()
                    .parse
                    .diagnostics
                    .len(),
                parse_errors
            );
            let diagnostics = program.diagnostics();
            assert_eq!(diagnostics.len(), 2, "{source}: {diagnostics:?}");
            assert_eq!(
                diagnostics
                    .iter()
                    .filter(|error| error.code == Some(1_005))
                    .count(),
                parse_errors
            );
            assert_eq!(
                diagnostics
                    .iter()
                    .filter(|error| error.code == Some(2_322))
                    .count(),
                1
            );
            let quantifiers = diagnostics
                .iter()
                .filter(|error| error.code == Some(1_506))
                .collect::<Vec<_>>();
            assert_eq!(quantifiers.len(), quantifier_errors);
            for error in quantifiers {
                let range = error.range.unwrap();
                assert_eq!(
                    &source[range.start.get() as usize..range.end.get() as usize],
                    "8,7"
                );
                assert_eq!(error.message, "Numbers out of order in quantifier.");
            }
        }
    }

    #[test]
    fn canonical_program_projects_bigint_exponentiation_target_capability() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file("/project/input.ts", "const value = 1n ** 2n;")
            .unwrap();

        for (target, expected_literal_errors, expected_exponent_errors) in [
            (ScriptTarget::Es2015, 2, 1),
            (ScriptTarget::Es2016, 2, 0),
            (ScriptTarget::Es2020, 0, 0),
        ] {
            let program = Program::try_new_with_canonical_checker(
                &fs,
                "/project",
                &["input.ts".to_owned()],
                CompilerOptions {
                    lib: Some(vec!["es5".to_owned()]),
                    target,
                    ..CompilerOptions::default()
                },
            )
            .unwrap_or_else(|error| panic!("target {target:?}: {error:?}"));

            assert_eq!(
                program
                    .diagnostics()
                    .iter()
                    .filter(|diagnostic| diagnostic.code == Some(2737))
                    .count(),
                expected_literal_errors,
                "target {target:?}",
            );
            assert_eq!(
                program
                    .diagnostics()
                    .iter()
                    .filter(|diagnostic| diagnostic.code == Some(2791))
                    .count(),
                expected_exponent_errors,
                "target {target:?}",
            );
        }
    }

    #[test]
    fn canonical_program_projects_unused_unreachable_and_isolated_options() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file("/project/input.ts", "export const value = 1;")
            .unwrap();

        let (program, projected) = Program::try_new_with_canonical_checker_and_queries(
            &fs,
            "/project",
            &["input.ts".to_owned()],
            CompilerOptions {
                lib: Some(vec!["es5".to_owned()]),
                no_unused_locals: true,
                no_unused_parameters: true,
                allow_unreachable_code: Some(false),
                preserve_const_enums: true,
                isolated_modules: true,
                ..CompilerOptions::default()
            },
            |_, queries| {
                let options = queries.context.options();
                (
                    options.no_unused_locals,
                    options.no_unused_parameters,
                    options.allow_unreachable_code,
                    options.preserve_const_enums,
                    options.isolated_modules,
                )
            },
        )
        .unwrap();

        assert_eq!(projected, Some((true, true, Some(false), true, true)));
        assert!(
            program.diagnostics().is_empty(),
            "{:?}",
            program.diagnostics()
        );
    }

    #[test]
    fn canonical_program_projects_no_implicit_this_option_independently() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file("/project/input.ts", "const value = 1;")
            .unwrap();

        for strict in [false, true] {
            for explicit in [None, Some(false), Some(true)] {
                for no_implicit_any in [false, true] {
                    let (program, projected) = Program::try_new_with_canonical_checker_and_queries(
                        &fs,
                        "/project",
                        &["input.ts".to_owned()],
                        CompilerOptions {
                            strict,
                            no_implicit_this: explicit.unwrap_or(!strict),
                            no_implicit_this_specified: explicit.is_some(),
                            no_implicit_any,
                            lib: Some(vec!["es5".to_owned()]),
                            ..CompilerOptions::default()
                        },
                        |_, queries| {
                            let options = queries.context.options();
                            (options.no_implicit_this, options.no_implicit_any)
                        },
                    )
                    .unwrap();
                    assert_eq!(
                        projected,
                        Some((explicit.unwrap_or(strict), no_implicit_any)),
                        "strict={strict} explicit={explicit:?} noImplicitAny={no_implicit_any}",
                    );
                    assert!(
                        program.diagnostics().is_empty(),
                        "{:?}",
                        program.diagnostics(),
                    );
                }
            }
        }
    }

    #[test]
    fn strict_reserved_identifier_contexts_match_pinned_go() {
        for (file_name, source, expected) in [
            (
                "a.ts",
                "var implements = 1, interface = 2, let = 3, package = 4, private = 5, protected = 6, public = 7, static = 8, yield = 9;",
                vec![
                    "implements",
                    "interface",
                    "let",
                    "package",
                    "private",
                    "protected",
                    "public",
                    "static",
                    "yield",
                ],
            ),
            (
                "a.ts",
                "var object = { let: 1, interface: 2 }; object.let; object.interface;",
                vec![],
            ),
            (
                "a.ts",
                "var let = 1; var object = { let };",
                vec!["let", "let"],
            ),
            (
                "a.ts",
                "const { interface: value } = { interface: 1 };",
                vec![],
            ),
            (
                "a.ts",
                "declare var let: number; declare function yield(): void;",
                vec![],
            ),
            ("a.d.ts", "var let: number;", vec![]),
            ("a.ts", "class C { method() { var let = 1; } }", vec![]),
            ("a.ts", "export {}; var let = 1;", vec![]),
            ("a.ts", "var let = ;", vec![]),
            ("a.ts", "var await = 1;", vec![]),
        ] {
            let fs = MemoryFileSystem::new(true);
            fs.write_file(&format!("/{file_name}"), source).unwrap();
            let program = Program::new_unchecked_with_options_and_checker(
                &fs,
                "/",
                &[file_name.to_owned()],
                CompilerOptions {
                    no_emit: true,
                    no_lib: true,
                    ..CompilerOptions::default()
                },
                super::ProgramChecker::Canonical,
            );
            let source_file = program.source_file(&format!("/{file_name}")).unwrap();
            let mut diagnostics = Vec::new();
            program
                .add_strict_reserved_identifier_diagnostics(source_file, &mut diagnostics)
                .unwrap();
            diagnostics.sort_by(super::compare_program_diagnostics);
            let actual = diagnostics
                .iter()
                .map(|diagnostic| {
                    assert_eq!(diagnostic.code, Some(1212));
                    let range = diagnostic.range.unwrap();
                    &source[range.start.get() as usize..range.end.get() as usize]
                })
                .collect::<Vec<_>>();
            assert_eq!(actual, expected, "{source}");
        }
    }

    #[test]
    fn canonical_program_projects_always_strict_and_preserves_identifier_ranges() {
        let fs = MemoryFileSystem::new(true);
        let source = "var arguments = 1;\narguments = 2;\n";
        fs.write_file("/project/input.ts", source).unwrap();

        for (always_strict, expected_starts) in [(false, Vec::new()), (true, vec![4_u32, 19_u32])] {
            let program = Program::try_new_with_canonical_checker(
                &fs,
                "/project",
                &["input.ts".to_owned()],
                CompilerOptions {
                    always_strict,
                    lib: Some(vec!["es5".to_owned()]),
                    ..CompilerOptions::default()
                },
            )
            .unwrap();

            let file = program.source_file("/project/input.ts").unwrap();
            assert_eq!(
                canonical_source_file_facts(file, program.options())
                    .unwrap()
                    .is_always_strict(),
                always_strict
            );
            assert_eq!(
                program
                    .diagnostics()
                    .iter()
                    .map(|diagnostic| {
                        assert_eq!(diagnostic.code, Some(1100));
                        assert_eq!(
                            diagnostic.message,
                            "Invalid use of 'arguments' in strict mode."
                        );
                        assert_eq!(diagnostic.file_name.as_deref(), Some("/project/input.ts"));
                        let range = diagnostic.range.unwrap();
                        assert_eq!(
                            &source[range.start.get() as usize..range.end.get() as usize],
                            "arguments"
                        );
                        range.start.get()
                    })
                    .collect::<Vec<_>>(),
                expected_starts,
                "alwaysStrict={always_strict}: {:?}",
                program.diagnostics()
            );
        }
    }

    #[test]
    fn production_program_forwards_upstream_strict_mode_namespace_diagnostics() {
        let fs = MemoryFileSystem::new(true);
        let source = concat!(
            "namespace M {\n",
            "    export function f() {\n",
            "        var arguments = [];\n",
            "    }\n",
            "}",
        );
        fs.write_file("/.src/alwaysStrictModule.ts", source)
            .unwrap();

        for (always_strict, expected_count) in [(false, 0), (true, 1)] {
            let program = Program::new_with_options(
                &fs,
                "/.src",
                &["alwaysStrictModule.ts".to_owned()],
                CompilerOptions {
                    always_strict,
                    module: ModuleKind::CommonJs,
                    module_specified: true,
                    target: ScriptTarget::Es2015,
                    ..CompilerOptions::default()
                },
            );
            let diagnostics = program
                .diagnostics()
                .iter()
                .filter(|diagnostic| diagnostic.code == Some(1100))
                .collect::<Vec<_>>();

            assert_eq!(
                diagnostics.len(),
                expected_count,
                "alwaysStrict={always_strict}: {:?}",
                program.diagnostics()
            );
            if let Some(diagnostic) = diagnostics.first() {
                assert_eq!(
                    diagnostic.file_name.as_deref(),
                    Some("/.src/alwaysStrictModule.ts")
                );
                assert_eq!(
                    diagnostic.range,
                    Some(TextRange::new(TextPos::new(52), TextPos::new(61)))
                );
                assert_eq!(
                    diagnostic.message,
                    "Invalid use of 'arguments' in strict mode."
                );
            }
        }
    }

    #[test]
    fn canonical_program_checks_diagnosed_strict_namespace_function_body() {
        let fs = MemoryFileSystem::new(true);
        let source = concat!(
            "namespace M {\n",
            "    export function f() {\n",
            "        var arguments = [];\n",
            "    }\n",
            "}",
        );
        fs.write_file("/.src/alwaysStrictModule.ts", source)
            .unwrap();

        let program = Program::try_new_with_canonical_checker(
            &fs,
            "/.src",
            &["alwaysStrictModule.ts".to_owned()],
            CompilerOptions {
                always_strict: true,
                module: ModuleKind::CommonJs,
                module_specified: true,
                target: ScriptTarget::Es2015,
                ..CompilerOptions::default()
            },
        )
        .unwrap();

        let [diagnostic] = program.diagnostics() else {
            panic!(
                "expected exactly one strict-mode diagnostic: {:?}",
                program.diagnostics()
            )
        };
        assert_eq!(diagnostic.code, Some(1100));
        assert_eq!(
            diagnostic.file_name.as_deref(),
            Some("/.src/alwaysStrictModule.ts")
        );
        assert_eq!(
            diagnostic.range,
            Some(TextRange::new(TextPos::new(52), TextPos::new(61)))
        );
        assert_eq!(
            diagnostic.message,
            "Invalid use of 'arguments' in strict mode."
        );
    }

    #[test]
    #[allow(clippy::too_many_lines)] // The original source, overload identity, and replay share one check.
    fn canonical_object_subtype_reduction_checks_full_original_and_replays() {
        let source = concat!(
            "// @strict: true\n",
            "// @target: esnext\n",
            "// @noEmit: true\n\n",
            "// https://github.com/microsoft/typescript-go/issues/1164\n\n",
            "function foo(x?: object) {\n",
            "    return Object.entries(x || {})\n",
            "        .sort(([k1, v1], [k2, v2]) => v1.name.localeCompare(v2.name));\n",
            "}\n",
        );
        let fs = MemoryFileSystem::new(true);
        fs.write_file("/project/objectSubtypeReduction.ts", source)
            .unwrap();
        let (program, state) = Program::try_new_with_canonical_checker_and_queries(
            &fs,
            "/project",
            &["objectSubtypeReduction.ts".to_owned()],
            CompilerOptions {
                strict: true,
                strict_specified: true,
                no_emit: true,
                target: ScriptTarget::EsNext,
                ..CompilerOptions::default()
            },
            |program, queries| {
                let file = program
                    .source_file("/project/objectSubtypeReduction.ts")
                    .unwrap()
                    .id;
                let (arena, _) = queries.context.file(file).unwrap();
                let declaration = arena
                    .iter()
                    .find_map(|(node, record)| {
                        (record.kind == ts_ast::SyntaxKind::FunctionDeclaration)
                            .then_some(ts_ast::NodeRef::new(arena.id(), file, node))
                    })
                    .unwrap();
                let returned = queries
                    .context
                    .store()
                    .signature_links(declaration)
                    .and_then(|links| links.resolved_signature.signature())
                    .and_then(|signature| queries.context.store().signature(signature))
                    .and_then(ts_checker::semantic::signatures::Signature::resolved_return_type)
                    .unwrap();
                assert_eq!(
                    queries.context.type_to_string(returned).unwrap(),
                    "[string, any][]"
                );
                let entries = arena
                    .iter()
                    .find_map(|(node, record)| {
                        let ts_ast::NodeData::CallExpression(call) = &record.data else {
                            return None;
                        };
                        let ts_ast::NodeData::PropertyAccessExpression(property) =
                            &arena.get(call.expression)?.data
                        else {
                            return None;
                        };
                        let ts_ast::NodeData::Identifier(name) = &arena.get(property.name)?.data
                        else {
                            return None;
                        };
                        (name.text == "entries").then_some(ts_ast::NodeRef::new(
                            arena.id(),
                            file,
                            node,
                        ))
                    })
                    .unwrap();
                let selected = queries
                    .context
                    .store()
                    .signature_links(entries)
                    .and_then(|links| links.resolved_signature.signature())
                    .and_then(|signature| queries.context.store().signature(signature))
                    .unwrap();
                assert!(selected.target().is_none());
                assert!(selected.type_parameters().is_empty());
                assert_eq!(selected.resolved_return_type(), Some(returned));
                let overload = selected.declaration().unwrap();
                let (library, bound) = queries.context.file(overload.file).unwrap();
                assert!(bound.source_facts().unwrap().is_default_library());
                let ts_ast::NodeData::MethodSignatureDeclaration(method) =
                    &library.get(overload.node).unwrap().data
                else {
                    panic!("entries must select a real library method declaration")
                };
                assert!(method.type_parameters.is_none());
                let before = (
                    queries.context.store().type_len(),
                    queries.context.store().symbol_len(),
                    queries.context.store().signature_len(),
                    queries.context.diagnostics().len(),
                );
                queries.context.recheck_source_file(file).unwrap();
                let after = (
                    queries.context.store().type_len(),
                    queries.context.store().symbol_len(),
                    queries.context.store().signature_len(),
                    queries.context.diagnostics().len(),
                );
                (before, after)
            },
        )
        .unwrap();
        assert!(
            program.diagnostics().is_empty(),
            "{:?}",
            program.diagnostics()
        );
        let (before, after) = state.unwrap();
        assert_eq!(before, after);
    }

    #[test]
    fn canonical_sort_callback_preserves_nested_array_tuple_elements() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/nestedSort.ts",
            concat!(
                "declare function entries(): [string, number[]][];\n",
                "function foo() {\n",
                "    return entries().sort(([k1, v1], [k2, v2]) => 0);\n",
                "}\n",
            ),
        )
        .unwrap();
        let (program, state) = Program::try_new_with_canonical_checker_and_queries(
            &fs,
            "/project",
            &["nestedSort.ts".to_owned()],
            CompilerOptions {
                strict: true,
                strict_specified: true,
                no_emit: true,
                target: ScriptTarget::EsNext,
                ..CompilerOptions::default()
            },
            |program, queries| {
                let file = program.source_file("/project/nestedSort.ts").unwrap().id;
                let (arena, _) = queries.context.file(file).unwrap();
                let function = arena
                    .iter()
                    .find_map(|(node, record)| {
                        let ts_ast::NodeData::FunctionDeclaration(function) = &record.data else {
                            return None;
                        };
                        let ts_ast::NodeData::Identifier(name) = &arena.get(function.name?)?.data
                        else {
                            return None;
                        };
                        (name.text == "foo").then_some(ts_ast::NodeRef::new(arena.id(), file, node))
                    })
                    .unwrap();
                let returned = queries
                    .context
                    .store()
                    .signature_links(function)
                    .and_then(|links| links.resolved_signature.signature())
                    .and_then(|signature| queries.context.store().signature(signature))
                    .and_then(ts_checker::semantic::signatures::Signature::resolved_return_type)
                    .unwrap();
                assert_eq!(
                    queries.context.type_to_string(returned).unwrap(),
                    "[string, number[]][]"
                );
                queries.context.recheck_source_file(file).unwrap();
            },
        )
        .unwrap();
        assert!(program.diagnostics().is_empty());
        assert!(state.is_some());
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Diagnostics and replay checks share the original source and checker.
    fn canonical_conditional_return_expression_matches_original_and_replays() {
        let source = concat!(
            "// @noEmit: true\n",
            "// @target: esnext\n\n",
            "function return1(x: boolean): 3 {\n",
            "    return (x ? (1) : 2);\n",
            "}\n\n",
            "declare function getAny(): any;\n\n",
            "function return2(x: string): string {\n",
            "    return x.startsWith(\"a\") ? getAny() : 1;\n",
            "}\n\n",
            "function return3(x: string): string {\n",
            "    return x.startsWith(\"a\") ? \"a\" : x;\n",
            "}\n\n",
            "function return4(x: string): string {\n",
            "    return (x.startsWith(\"a\") ? getAny() : 1) as string;\n",
            "}\n\n",
            "const return5 = (x: string): string => x.startsWith(\"a\") ? getAny() : 1;\n\n",
            "const return6 = (x: string): string => (x.startsWith(\"a\") ? getAny() : 1) as string;",
        );
        let fs = MemoryFileSystem::new(true);
        fs.write_file("/project/conditionalReturnExpression.ts", source)
            .unwrap();
        let (program, state) = Program::try_new_with_canonical_checker_and_queries(
            &fs,
            "/project",
            &["conditionalReturnExpression.ts".to_owned()],
            CompilerOptions {
                no_emit: true,
                target: ScriptTarget::EsNext,
                ..CompilerOptions::default()
            },
            |program, queries| {
                let file = program
                    .source_file("/project/conditionalReturnExpression.ts")
                    .unwrap()
                    .id;
                let store = queries.context.store();
                let wrapper = queries.context.global_types().string_type;
                let owner = store.type_payload(wrapper).unwrap().symbol().unwrap();
                let method = store
                    .symbol(owner)
                    .and_then(ts_binder::semantic::Symbol::members)
                    .and_then(|members| store.symbol_table(members))
                    .and_then(|members| members.get_source("startsWith"))
                    .unwrap();
                let declaration = store.symbol(method).unwrap().value_declaration().unwrap();
                let signature = store
                    .signature_links(declaration)
                    .and_then(|links| links.resolved_signature.signature())
                    .and_then(|signature| store.signature(signature))
                    .unwrap();
                let bootstrap = store.intrinsic_bootstrap().unwrap();
                assert_eq!(signature.parameters().len(), 2);
                assert_eq!(signature.min_argument_count(), 1);
                assert_eq!(
                    signature.resolved_return_type(),
                    Some(bootstrap.boolean_type)
                );
                assert_eq!(
                    store
                        .value_symbol_links(signature.parameters()[0])
                        .unwrap()
                        .resolved_type,
                    Some(bootstrap.string_type)
                );
                let before = (
                    store.type_len(),
                    store.symbol_len(),
                    store.signature_len(),
                    queries.context.diagnostics().len(),
                );
                queries.context.recheck_source_file(file).unwrap();
                let after = (
                    queries.context.store().type_len(),
                    queries.context.store().symbol_len(),
                    queries.context.store().signature_len(),
                    queries.context.diagnostics().len(),
                );
                (before, after)
            },
        )
        .unwrap();
        let (before, after) = state.unwrap();
        assert_eq!(before, after);
        let expected = [
            (5, 18, "1", "Type '1' is not assignable to type '3'."),
            (5, 23, "2", "Type '2' is not assignable to type '3'."),
            (
                11,
                43,
                "1",
                "Type 'number' is not assignable to type 'string'.",
            ),
            (
                22,
                71,
                "1",
                "Type 'number' is not assignable to type 'string'.",
            ),
        ];
        assert_eq!(program.diagnostics().len(), expected.len());
        for (diagnostic, (line, column, text, message)) in
            program.diagnostics().iter().zip(expected)
        {
            assert_eq!(diagnostic.code, Some(2322));
            assert_eq!(
                diagnostic.file_name.as_deref(),
                Some("/project/conditionalReturnExpression.ts")
            );
            assert_eq!(diagnostic.message, message);
            let range = diagnostic.range.unwrap();
            let start = range.start.get() as usize;
            let end = range.end.get() as usize;
            assert_eq!(&source[start..end], text);
            assert_eq!(
                source[..start]
                    .bytes()
                    .filter(|byte| *byte == b'\n')
                    .count()
                    + 1,
                line
            );
            assert_eq!(
                source[..start].rsplit('\n').next().unwrap().len() + 1,
                column
            );
        }
    }

    #[test]
    fn canonical_string_starts_with_checks_real_parameter_types_and_arity() {
        let source = concat!(
            "declare const value: string;\n",
            "const first: boolean = value.startsWith('a');\n",
            "const positioned: boolean = value.startsWith('a', 1);\n",
            "value.startsWith(1);\n",
            "value.startsWith('a', 'wrong');\n",
            "value.startsWith();\n",
        );
        let fs = MemoryFileSystem::new(true);
        fs.write_file("/project/startsWith.ts", source).unwrap();
        let program = Program::try_new_with_canonical_checker(
            &fs,
            "/project",
            &["startsWith.ts".to_owned()],
            CompilerOptions {
                no_emit: true,
                target: ScriptTarget::EsNext,
                ..CompilerOptions::default()
            },
        )
        .unwrap();
        assert_eq!(
            program
                .diagnostics()
                .iter()
                .map(|diagnostic| diagnostic.code.unwrap())
                .collect::<Vec<_>>(),
            [2345, 2345, 2554]
        );
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Calls, parameters, and diagnostics share the same parsed cases.
    fn canonical_program_recovers_authenticated_strict_arguments_collisions() {
        type StrictCollisionCase = (&'static str, &'static str, &'static [(u32, u32)]);
        let cases: [StrictCollisionCase; 4] = [
            (
                "function.ts",
                concat!(
                    "var arguments = 10;\n",
                    "function foo(a) {\n",
                    "    arguments = 10;\n",
                    "}\n",
                ),
                &[(1100, 4), (1100, 42), (2322, 42)],
            ),
            (
                "arrows.ts",
                concat!(
                    "var first = (arguments: number) => { var arguments = 1; };\n",
                    "var second = (...rest) => { var arguments: any[]; };\n",
                ),
                &[(1100, 13), (1100, 41), (1100, 91)],
            ),
            (
                "collisionArgumentsArrowFunctions.ts",
                concat!(
                    "var f1 = (i: number, ...arguments) => { //arguments is error\n",
                    "    var arguments: any[]; // no error\n",
                    "}\n",
                    "var f12 = (arguments: number, ...rest) => { //arguments is error\n",
                    "    var arguments = 10; // no error\n",
                    "}\n",
                    "var f1NoError = (arguments: number) => { // no error\n",
                    "    var arguments = 10; // no error\n",
                    "}\n\n",
                    "var f2 = (...restParameters) => {\n",
                    "    var arguments = 10; // No Error\n",
                    "}\n",
                    "var f2NoError = () => {\n",
                    "    var arguments = 10; // no error\n",
                    "}",
                ),
                &[
                    (1100, 24),
                    (1100, 69),
                    (1100, 112),
                    (1100, 174),
                    (1100, 221),
                    (1100, 265),
                    (1100, 338),
                    (1100, 400),
                ],
            ),
            (
                "types.ts",
                concat!(
                    "var first: (arguments: number) => void;\n",
                    "var second: { (arguments: number); new (value: number, ...arguments); };\n",
                ),
                &[(1100, 12), (1100, 55), (1100, 98)],
            ),
        ];

        for (file_name, source, expected) in cases {
            let fs = MemoryFileSystem::new(true);
            let path = format!("/project/{file_name}");
            fs.write_file(&path, source).unwrap();
            let program = Program::try_new_with_canonical_checker(
                &fs,
                "/project",
                &[file_name.to_owned()],
                CompilerOptions {
                    always_strict: true,
                    strict: false,
                    strict_specified: true,
                    no_implicit_any: false,
                    no_implicit_any_specified: true,
                    lib: Some(vec!["es5".to_owned()]),
                    target: ScriptTarget::Es2015,
                    ..CompilerOptions::default()
                },
            )
            .unwrap_or_else(|error| panic!("{file_name}: {error:?}"));

            let actual = program
                .diagnostics()
                .iter()
                .map(|diagnostic| {
                    assert_eq!(diagnostic.file_name.as_deref(), Some(path.as_str()));
                    let range = diagnostic.range.unwrap();
                    assert_eq!(
                        &source[range.start.get() as usize..range.end.get() as usize],
                        "arguments"
                    );
                    if diagnostic.code == Some(2322) {
                        assert_eq!(
                            diagnostic.message,
                            "Type 'number' is not assignable to type 'IArguments'."
                        );
                    } else {
                        assert_eq!(
                            diagnostic.message,
                            "Invalid use of 'arguments' in strict mode."
                        );
                    }
                    (diagnostic.code.unwrap(), range.start.get())
                })
                .collect::<Vec<_>>();
            assert_eq!(actual.as_slice(), expected, "{file_name}");
        }
    }

    #[test]
    fn strict_arguments_recovery_keeps_body_errors_and_unrelated_unsupported_source() {
        let sources = [
            (
                concat!(
                    "var first = (arguments: number) => {\n",
                    "    var arguments = 1;\n",
                    "    const unrelated: number = 'wrong';\n",
                    "};\n",
                ),
                Some([1100, 1100, 2322]),
            ),
            (
                concat!(
                    "var first: (arguments: number) => void;\n",
                    "var second: { (arguments: number): Missing; };\n",
                ),
                None,
            ),
        ];

        for (source, expected) in sources {
            let fs = MemoryFileSystem::new(true);
            fs.write_file("/project/input.ts", source).unwrap();
            let result = Program::try_new_with_canonical_checker(
                &fs,
                "/project",
                &["input.ts".to_owned()],
                CompilerOptions {
                    always_strict: true,
                    strict: false,
                    strict_specified: true,
                    no_implicit_any: false,
                    no_implicit_any_specified: true,
                    lib: Some(vec!["es5".to_owned()]),
                    ..CompilerOptions::default()
                },
            );
            if let Some(expected) = expected {
                let program = result.unwrap();
                let diagnostics = program.diagnostics();
                assert_eq!(
                    diagnostics
                        .iter()
                        .map(|diagnostic| diagnostic.code.unwrap())
                        .collect::<Vec<_>>(),
                    expected,
                );
                let diagnostic = diagnostics.last().unwrap();
                assert_eq!(
                    diagnostic.message,
                    "Type 'string' is not assignable to type 'number'."
                );
                let range = diagnostic.range.unwrap();
                assert_eq!(
                    &source[range.start.get() as usize..range.end.get() as usize],
                    "unrelated"
                );
            } else {
                let error = result.unwrap_err();
                assert!(error.is_unsupported_boundary(), "{source}: {error:?}");
            }
        }
    }

    #[test]
    fn strict_arguments_recovery_preserves_isolated_declaration_diagnostics() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/collisions.ts",
            "var first = (arguments: number) => { var arguments = 1; };\n",
        )
        .unwrap();
        fs.write_file(
            "/project/exported.ts",
            "export function isString(value: unknown) { return typeof value === 'string'; }\n",
        )
        .unwrap();

        let program = Program::try_new_with_canonical_checker(
            &fs,
            "/project",
            &["collisions.ts".to_owned(), "exported.ts".to_owned()],
            CompilerOptions {
                always_strict: true,
                strict: false,
                strict_specified: true,
                no_implicit_any: false,
                no_implicit_any_specified: true,
                declaration: true,
                isolated_declarations: true,
                lib: Some(vec!["es5".to_owned()]),
                ..CompilerOptions::default()
            },
        )
        .unwrap();

        assert_eq!(
            program
                .diagnostics()
                .iter()
                .map(|diagnostic| (diagnostic.file_name.as_deref(), diagnostic.code))
                .collect::<Vec<_>>(),
            [
                (Some("/project/collisions.ts"), Some(1100)),
                (Some("/project/collisions.ts"), Some(1100)),
                (Some("/project/exported.ts"), Some(9007)),
            ]
        );
    }

    #[test]
    fn recovered_strict_argument_arrows_recheck_without_changing_checker_state() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/input.ts",
            "var first = (arguments: number) => { var arguments = 1; };\n",
        )
        .unwrap();

        let (program, state) = Program::try_new_with_canonical_checker_and_queries(
            &fs,
            "/project",
            &["input.ts".to_owned()],
            CompilerOptions {
                always_strict: true,
                strict: false,
                strict_specified: true,
                no_implicit_any: false,
                no_implicit_any_specified: true,
                lib: Some(vec!["es5".to_owned()]),
                ..CompilerOptions::default()
            },
            |program, queries| {
                let file = program.source_file("/project/input.ts").unwrap().id;
                let before = (
                    queries.context.store().type_len(),
                    queries.context.store().symbol_len(),
                    queries.context.store().signature_len(),
                    queries.context.store().mapper_len(),
                    queries.context.store().type_resolution_len(),
                    queries.context.diagnostics().len(),
                );
                queries.context.recheck_source_file(file).unwrap();
                let after = (
                    queries.context.store().type_len(),
                    queries.context.store().symbol_len(),
                    queries.context.store().signature_len(),
                    queries.context.store().mapper_len(),
                    queries.context.store().type_resolution_len(),
                    queries.context.diagnostics().len(),
                );
                (before, after)
            },
        )
        .unwrap();

        let (before, after) = state.unwrap();
        assert_eq!(before, after);
        assert_eq!(
            program
                .diagnostics()
                .iter()
                .filter(|diagnostic| diagnostic.code == Some(1100))
                .count(),
            2
        );
    }

    #[test]
    fn canonical_project_replay_keeps_source_order_and_cache_lengths() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/z.tsx",
            concat!(
                "/** @jsxRuntime classic */\n",
                "/** @jsx Custom.h */\n",
                "declare const Custom: any;\n",
                "const first = <div />;\n",
                "const bad: string = null;\n",
            ),
        )
        .unwrap();
        fs.write_file(
            "/project/a.tsx",
            "/** @jsxImportSource absent */\nconst second = <div />;\n",
        )
        .unwrap();
        fs.write_file(
            "/project/ignored.ts",
            "// @ts-nocheck\nconst ignored: string = null;\n",
        )
        .unwrap();
        let (program, cold) = Program::try_new_with_canonical_checker_and_queries(
            &fs,
            "/project",
            &[
                "z.tsx".to_owned(),
                "a.tsx".to_owned(),
                "ignored.ts".to_owned(),
            ],
            CompilerOptions {
                strict: true,
                no_implicit_any: false,
                no_implicit_any_specified: true,
                jsx: ts_options::JsxEmit::ReactJsx,
                module: ModuleKind::EsNext,
                module_specified: true,
                module_resolution: ModuleResolutionKind::Bundler,
                lib: Some(vec!["es5".to_owned()]),
                no_emit: true,
                ..CompilerOptions::default()
            },
            |program, queries| {
                assert_eq!(
                    queries
                        .checked_sources
                        .iter()
                        .map(|checked| checked.source.file_name.as_str())
                        .collect::<Vec<_>>(),
                    ["/project/z.tsx", "/project/a.tsx"],
                );
                let lengths = |queries: &super::CanonicalProgramQueries<'_>| {
                    (
                        queries.context.store().type_len(),
                        queries.context.store().symbol_len(),
                        queries.context.store().signature_len(),
                        queries.context.store().mapper_len(),
                        queries.context.store().type_resolution_len(),
                        queries.context.diagnostics().len(),
                    )
                };
                let before = lengths(queries);
                let cold = queries.cold_diagnostic_snapshot();
                for _ in 0..2 {
                    assert_eq!(queries.replay_sources().unwrap(), cold);
                    assert_eq!(lengths(queries), before);
                }
                let ignored = program.source_file("/project/ignored.ts").unwrap().id;
                let ignored = queries.context.source_file(ignored).unwrap();
                assert!(
                    queries
                        .context
                        .store()
                        .source_file_links(ignored)
                        .is_none_or(|links| !links.type_checked)
                );
                cold
            },
        )
        .unwrap();
        assert_eq!(program.diagnostics(), cold.unwrap());
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Keep the complete upstream fixture and baseline together.
    fn canonical_program_recovers_the_complete_missing_arrow_token_fixture() {
        let source = concat!(
            "namespace missingArrowsWithCurly {\n",
            "    var a = () { };\n",
            "\n",
            "    var b = (): void { }\n",
            "\n",
            "    var c = (x) { };\n",
            "\n",
            "    var d = (x: number, y: string) { };\n",
            "\n",
            "    var e = (x: number, y: string): void { };\n",
            "}\n",
            "\n",
            "namespace missingCurliesWithArrow {\n",
            "    namespace withStatement {\n",
            "        var a = () => var k = 10;};\n",
            "\n",
            "        var b = (): void => var k = 10;}\n",
            "\n",
            "        var c = (x) => var k = 10;};\n",
            "\n",
            "        var d = (x: number, y: string) => var k = 10;};\n",
            "\n",
            "        var e = (x: number, y: string): void => var k = 10;};\n",
            "\n",
            "        var f = () => var k = 10;}\n",
            "    }\n",
            "\n",
            "    namespace withoutStatement {\n",
            "        var a = () => };\n",
            "\n",
            "        var b = (): void => }\n",
            "\n",
            "        var c = (x) => };\n",
            "\n",
            "        var d = (x: number, y: string) => };\n",
            "\n",
            "        var e = (x: number, y: string): void => };\n",
            "\n",
            "        var f = () => }\n",
            "    }\n",
            "}\n",
            "\n",
            "namespace ce_nEst_pas_une_arrow_function {\n",
            "    var a = ();\n",
            "\n",
            "    var b = (): void;\n",
            "\n",
            "    var c = (x);\n",
            "\n",
            "    var d = (x: number, y: string);\n",
            "\n",
            "    var e = (x: number, y: string): void;\n",
            "}\n",
            "\n",
            "namespace okay {\n",
            "    var a = () => { };\n",
            "\n",
            "    var b = (): void => { }\n",
            "\n",
            "    var c = (x) => { };\n",
            "\n",
            "    var d = (x: number, y: string) => { };\n",
            "\n",
            "    var e = (x: number, y: string): void => { };\n",
            "}",
        );
        let fs = MemoryFileSystem::new(true);
        fs.write_file("/project/arrowFunctionsMissingTokens.ts", source)
            .unwrap();

        let (program, state) = Program::try_new_with_canonical_checker_and_queries(
            &fs,
            "/project",
            &["arrowFunctionsMissingTokens.ts".to_owned()],
            CompilerOptions {
                strict: false,
                strict_specified: true,
                no_implicit_any: false,
                no_implicit_any_specified: true,
                target: ScriptTarget::Es2015,
                lib: Some(vec!["es5".to_owned()]),
                ..CompilerOptions::default()
            },
            |program, queries| {
                let file = program
                    .source_file("/project/arrowFunctionsMissingTokens.ts")
                    .unwrap();
                let missing_start = source.find("var c = (x);").unwrap() + "var c = (".len();
                let identifier = file
                    .parse
                    .arena
                    .iter()
                    .find_map(|(node, record)| {
                        (record.kind == SyntaxKind::Identifier
                            && record.range.start.get() as usize == missing_start)
                            .then_some(file.node_ref(node).unwrap())
                    })
                    .expect("expected the unresolved parenthesized identifier");
                let error_type = queries
                    .context
                    .store()
                    .intrinsic_bootstrap()
                    .unwrap()
                    .error_type;
                assert_eq!(
                    queries
                        .context
                        .store()
                        .type_node_links(identifier)
                        .and_then(|links| links.resolved_type),
                    Some(error_type)
                );
                let before = (
                    queries.context.store().type_len(),
                    queries.context.store().symbol_len(),
                    queries.context.store().signature_len(),
                    queries.context.store().mapper_len(),
                    queries.context.store().type_resolution_len(),
                    queries.context.diagnostics().len(),
                );
                queries.context.recheck_source_file(file.id).unwrap();
                let after = (
                    queries.context.store().type_len(),
                    queries.context.store().symbol_len(),
                    queries.context.store().signature_len(),
                    queries.context.store().mapper_len(),
                    queries.context.store().type_resolution_len(),
                    queries.context.diagnostics().len(),
                );
                (before, after)
            },
        )
        .unwrap();
        let (before, after) = state.unwrap();
        assert_eq!(before, after);

        let expected = [
            (2, 16, 1005, "{", "'=>' expected."),
            (4, 22, 1005, "{", "'=>' expected."),
            (6, 17, 1005, "{", "'=>' expected."),
            (8, 36, 1005, "{", "'=>' expected."),
            (10, 42, 1005, "{", "'=>' expected."),
            (15, 23, 1005, "var", "'{' expected."),
            (17, 29, 1005, "var", "'{' expected."),
            (19, 24, 1005, "var", "'{' expected."),
            (21, 43, 1005, "var", "'{' expected."),
            (23, 49, 1005, "var", "'{' expected."),
            (25, 23, 1005, "var", "'{' expected."),
            (29, 23, 1109, "}", "Expression expected."),
            (31, 29, 1109, "}", "Expression expected."),
            (33, 24, 1109, "}", "Expression expected."),
            (35, 43, 1109, "}", "Expression expected."),
            (37, 49, 1109, "}", "Expression expected."),
            (39, 23, 1109, "}", "Expression expected."),
            (40, 5, 1128, "}", "Declaration or statement expected."),
            (41, 1, 1128, "}", "Declaration or statement expected."),
            (44, 14, 1109, ")", "Expression expected."),
            (46, 21, 1005, ";", "'=>' expected."),
            (48, 14, 2304, "x", "Cannot find name 'x'."),
            (50, 35, 1005, ";", "'=>' expected."),
            (52, 41, 1005, ";", "'=>' expected."),
        ];
        assert_eq!(program.diagnostics().len(), expected.len());
        for (diagnostic, (line, column, code, spelling, message)) in
            program.diagnostics().iter().zip(expected)
        {
            let line_start = source
                .lines()
                .take(line - 1)
                .map(|line| line.len() + 1)
                .sum::<usize>();
            let start = line_start + column - 1;
            let end = start + spelling.len();
            assert_eq!(
                (
                    diagnostic.file_name.as_deref(),
                    diagnostic.code,
                    diagnostic.range,
                    diagnostic.message.as_str(),
                ),
                (
                    Some("/project/arrowFunctionsMissingTokens.ts"),
                    Some(code),
                    Some(TextRange::new(
                        TextPos::new(u32::try_from(start).unwrap()),
                        TextPos::new(u32::try_from(end).unwrap()),
                    )),
                    message,
                ),
                "line {line}, column {column}",
            );
            assert_eq!(&source[start..end], spelling);
        }
    }

    #[test]
    fn malformed_arrow_recovery_does_not_hide_unrelated_source() {
        for source in [
            concat!(
                "namespace Recovery {\n",
                "    var ordinary = () => {};\n",
                "}\n",
            ),
            concat!(
                "namespace Recovery {\n",
                "    var recovered = () { };\n",
                "    var unrelated = unsupported();\n",
                "}\n",
            ),
            concat!(
                "namespace Recovery {\n",
                "    var recovered = () { };\n",
                "    var first = (missing);\n",
                "    var second = (other);\n",
                "}\n",
            ),
            concat!(
                "namespace Recovery {\n",
                "    var recovered = () { };\n",
                "    class Unrelated { method() {} }\n",
                "}\n",
            ),
        ] {
            let fs = MemoryFileSystem::new(true);
            fs.write_file("/project/input.ts", source).unwrap();
            let Err(error) = Program::try_new_with_canonical_checker(
                &fs,
                "/project",
                &["input.ts".to_owned()],
                CompilerOptions {
                    strict: false,
                    strict_specified: true,
                    no_implicit_any: false,
                    no_implicit_any_specified: true,
                    lib: Some(vec!["es5".to_owned()]),
                    ..CompilerOptions::default()
                },
            ) else {
                panic!("expected unrelated unsupported syntax to remain rejected: {source}");
            };
            assert!(error.is_unsupported_boundary(), "{source}: {error:?}");
        }
    }

    #[test]
    fn canonical_program_checks_multi_file_primitive_assignments_atomically() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file("/project/first.ts", r#"const first: number = "wrong";"#)
            .unwrap();
        fs.write_file("/project/second.ts", "const second: string = 1;")
            .unwrap();
        let program = Program::try_new_with_canonical_checker(
            &fs,
            "/project",
            &["first.ts".to_owned(), "second.ts".to_owned()],
            CompilerOptions {
                lib: Some(vec!["es5".to_owned()]),
                ..CompilerOptions::default()
            },
        )
        .unwrap();

        let es5 = program
            .source_file("/__typescript/lib/lib.es5.d.ts")
            .unwrap();
        assert!(!program.options().skip_lib_check);
        assert!(es5.is_default_library);
        assert!(
            canonical_source_file_facts(es5, program.options())
                .unwrap()
                .is_default_library()
        );
        assert!(
            !canonical_source_file_facts(
                program.source_file("/project/first.ts").unwrap(),
                program.options(),
            )
            .unwrap()
            .is_default_library()
        );
        assert!(es5.checking.diagnostics.is_empty());

        let diagnostics = program.diagnostics();
        assert_eq!(diagnostics.len(), 2, "{diagnostics:?}");
        assert_eq!(
            diagnostics[0].file_name.as_deref(),
            Some("/project/first.ts")
        );
        assert_eq!(diagnostics[0].code, Some(2322));
        assert_eq!(
            diagnostics[0].message,
            "Type 'string' is not assignable to type 'number'."
        );
        assert_eq!(
            diagnostics[1].file_name.as_deref(),
            Some("/project/second.ts")
        );
        assert_eq!(diagnostics[1].code, Some(2322));
        assert_eq!(
            diagnostics[1].message,
            "Type 'number' is not assignable to type 'string'."
        );

        for (file_name, variable_name, diagnostic) in [
            ("/project/first.ts", "first", &diagnostics[0]),
            ("/project/second.ts", "second", &diagnostics[1]),
        ] {
            let source = program.source_file(file_name).unwrap();
            let variable_range = source
                .parse
                .arena
                .iter()
                .find_map(|(_, node)| match &node.data {
                    NodeData::Identifier(identifier) if identifier.text == variable_name => {
                        Some(node.range)
                    }
                    _ => None,
                })
                .unwrap();
            assert_eq!(diagnostic.range, Some(variable_range));
            assert!(source.checking.diagnostics.is_empty());
        }

        let emit = program.emit();
        assert!(emit.files.is_empty());
        assert_eq!(emit.diagnostics.len(), 1);
        assert_eq!(emit.diagnostics[0].code, None);
        assert_eq!(emit.diagnostics[0].category, Category::Error);
        assert!(emit.diagnostics[0].message.contains("Emit is unavailable"));
    }

    #[test]
    fn canonical_program_diagnostic_uses_exact_range_and_preserves_node_default() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file("/project/input.ts", "const target: number = 1;")
            .unwrap();
        let program = Program::new_with_options(
            &fs,
            "/project",
            &["input.ts".to_owned()],
            CompilerOptions {
                no_check: true,
                no_lib: true,
                ..CompilerOptions::default()
            },
        );
        let source = program.source_file("/project/input.ts").unwrap();
        let (identifier, identifier_record) = source
            .parse
            .arena
            .iter()
            .find(|(_, record)| {
                matches!(&record.data, NodeData::Identifier(identifier) if identifier.text == "target")
            })
            .unwrap();
        let anchor = source.node_ref(identifier).unwrap();
        let exact_range = TextRange::new(
            TextPos::new(identifier_record.range.start.get() + 1),
            TextPos::new(identifier_record.range.start.get() + 3),
        );
        let diagnostic = Diagnostic::with_arguments(message_by_code(2300).unwrap(), ["target"]);
        let node_default = program
            .canonical_program_diagnostic(Some(anchor), None, &diagnostic, std::iter::empty())
            .unwrap();
        let exact = program
            .canonical_program_diagnostic(
                Some(anchor),
                Some(CanonicalCheckerDiagnosticRange::new(anchor, exact_range)),
                &diagnostic,
                std::iter::empty(),
            )
            .unwrap();

        assert_eq!(node_default.file_name.as_deref(), Some("/project/input.ts"));
        assert_eq!(node_default.range, Some(identifier_record.range));
        assert_eq!(exact.range, Some(exact_range));
        let mut normalized = exact.clone();
        normalized.range = node_default.range;
        assert_eq!(normalized, node_default);

        let later_range = TextRange::new(
            TextPos::new(identifier_record.range.start.get() + 3),
            TextPos::new(identifier_record.range.start.get() + 4),
        );
        let later = program
            .canonical_program_diagnostic(
                Some(anchor),
                Some(CanonicalCheckerDiagnosticRange::new(anchor, later_range)),
                &diagnostic,
                std::iter::empty(),
            )
            .unwrap();
        let mut ordered = [later, exact];
        ordered.sort_by(super::compare_program_diagnostics);
        assert_eq!(ordered[0].range, Some(exact_range));
        assert_eq!(ordered[1].range, Some(later_range));
    }

    #[test]
    fn canonical_program_diagnostic_rejects_invalid_range_overrides() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file("/project/input.ts", "const target: number = 1;")
            .unwrap();
        let program = Program::new_with_options(
            &fs,
            "/project",
            &["input.ts".to_owned()],
            CompilerOptions {
                no_check: true,
                no_lib: true,
                ..CompilerOptions::default()
            },
        );
        let source = program.source_file("/project/input.ts").unwrap();
        let (identifier, identifier_record) = source
            .parse
            .arena
            .iter()
            .find(|(_, record)| {
                matches!(&record.data, NodeData::Identifier(identifier) if identifier.text == "target")
            })
            .unwrap();
        let anchor = source.node_ref(identifier).unwrap();
        let source_range = source
            .parse
            .arena
            .get(source.parse.source_file)
            .unwrap()
            .range;
        let valid_range = TextRange::new(
            identifier_record.range.start,
            TextPos::new(identifier_record.range.start.get() + 1),
        );
        let empty = CanonicalCheckerDiagnosticRange::new(
            anchor,
            TextRange::new(identifier_record.range.start, identifier_record.range.start),
        );
        let outside_anchor = CanonicalCheckerDiagnosticRange::new(
            anchor,
            TextRange::new(
                TextPos::new(identifier_record.range.start.get() - 1),
                identifier_record.range.end,
            ),
        );
        let outside_source = CanonicalCheckerDiagnosticRange::new(
            anchor,
            TextRange::new(source_range.end, TextPos::new(source_range.end.get() + 1)),
        );
        let foreign = CanonicalCheckerDiagnosticRange::new(
            ts_ast::NodeRef::new(source.parse.arena.id(), FileId::new(99), identifier),
            valid_range,
        );
        let valid = CanonicalCheckerDiagnosticRange::new(anchor, valid_range);
        let diagnostic = Diagnostic::with_arguments(message_by_code(2300).unwrap(), ["target"]);

        for (node, range_override) in [
            (Some(anchor), empty),
            (Some(anchor), outside_anchor),
            (Some(anchor), outside_source),
            (Some(anchor), foreign),
            (None, valid),
        ] {
            let error = program
                .canonical_program_diagnostic(
                    node,
                    Some(range_override),
                    &diagnostic,
                    std::iter::empty(),
                )
                .unwrap_err();
            assert_eq!(
                error,
                CanonicalProgramCheckError::InvalidDiagnosticRange {
                    node,
                    range_override,
                }
            );
            assert!(!error.is_unsupported_boundary());
        }
        assert!(program.diagnostics().is_empty());
    }

    #[test]
    fn canonical_program_diagnostic_owns_same_and_cross_file_related_records_in_order() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/first.ts",
            "const primary: number = 1; const same: number = 2;",
        )
        .unwrap();
        fs.write_file("/project/second.ts", "const cross: number = 3;")
            .unwrap();
        let program = Program::new_with_options(
            &fs,
            "/project",
            &["first.ts".to_owned(), "second.ts".to_owned()],
            CompilerOptions {
                no_check: true,
                no_lib: true,
                ..CompilerOptions::default()
            },
        );
        let node_named = |file_name: &str, expected: &str| {
            let source = program.source_file(file_name).unwrap();
            source
                .parse
                .arena
                .iter()
                .find_map(|(node, data)| match &data.data {
                    NodeData::Identifier(identifier) if identifier.text == expected => {
                        source.node_ref(node)
                    }
                    _ => None,
                })
                .unwrap()
        };
        let primary_node = node_named("/project/first.ts", "primary");
        let same_file_node = node_named("/project/first.ts", "same");
        let cross_file_node = node_named("/project/second.ts", "cross");
        let primary = Diagnostic::with_arguments(message_by_code(2451).unwrap(), ["primary"]);
        let leading = Diagnostic::with_arguments(message_by_code(6203).unwrap(), ["primary"]);
        let follow_on = Diagnostic::new(message_by_code(6204).unwrap());

        let owned = program
            .canonical_program_diagnostic(
                Some(primary_node),
                None,
                &primary,
                [
                    (Some(same_file_node), &leading),
                    (Some(cross_file_node), &follow_on),
                ],
            )
            .unwrap();

        assert_eq!(owned.file_name.as_deref(), Some("/project/first.ts"));
        assert_eq!(owned.code, Some(2451));
        assert_eq!(owned.related_information.len(), 2);
        assert_eq!(
            owned
                .related_information
                .iter()
                .map(|related| (
                    related.file_name.as_deref(),
                    related.code,
                    related.message.as_str(),
                    related.related_information.len(),
                ))
                .collect::<Vec<_>>(),
            [
                (
                    Some("/project/first.ts"),
                    Some(6203),
                    "'primary' was also declared here.",
                    0,
                ),
                (Some("/project/second.ts"), Some(6204), "and here.", 0,),
            ]
        );
        assert!(program.diagnostics().is_empty());
    }

    #[test]
    fn canonical_program_suppresses_binder_related_records_for_skipped_declarations() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/input.d.ts",
            concat!("export default class first {}\n", "export default 0;",),
        )
        .unwrap();
        let program = Program::try_new_with_canonical_checker(
            &fs,
            "/project",
            &["input.d.ts".to_owned()],
            CompilerOptions {
                lib: Some(vec!["es5".to_owned()]),
                skip_lib_check: true,
                ..CompilerOptions::default()
            },
        )
        .unwrap();

        assert!(
            program.diagnostics().is_empty(),
            "{:?}",
            program.diagnostics()
        );
    }

    #[test]
    fn canonical_program_diagnostic_rejects_a_later_foreign_related_node_atomically() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/input.ts",
            "const primary: number = 1; const related: number = 2;",
        )
        .unwrap();
        let program = Program::new_with_options(
            &fs,
            "/project",
            &["input.ts".to_owned()],
            CompilerOptions {
                no_check: true,
                no_lib: true,
                ..CompilerOptions::default()
            },
        );
        let source = program.source_file("/project/input.ts").unwrap();
        let identifiers = source
            .parse
            .arena
            .iter()
            .filter(|(_, data)| matches!(&data.data, NodeData::Identifier(_)))
            .map(|(node, _)| source.node_ref(node).unwrap())
            .collect::<Vec<_>>();
        assert_eq!(identifiers.len(), 2);
        let foreign = parse_source_file("const foreign: number = 3;");
        let foreign_node =
            ts_ast::NodeRef::new(foreign.arena.id(), identifiers[0].file, foreign.source_file);
        let primary = Diagnostic::with_arguments(message_by_code(2451).unwrap(), ["primary"]);
        let leading = Diagnostic::with_arguments(message_by_code(6203).unwrap(), ["primary"]);
        let follow_on = Diagnostic::new(message_by_code(6204).unwrap());

        let error = program
            .canonical_program_diagnostic(
                Some(identifiers[0]),
                None,
                &primary,
                [
                    (Some(identifiers[1]), &leading),
                    (Some(foreign_node), &follow_on),
                ],
            )
            .unwrap_err();

        assert_eq!(
            error,
            CanonicalProgramCheckError::InvalidRelatedDiagnosticNode {
                primary_code: 2451,
                index: 1,
                node: foreign_node,
            }
        );
        assert!(!error.is_unsupported_boundary());
        assert!(program.diagnostics().is_empty());
    }

    #[test]
    fn canonical_program_checks_later_class_methods_without_losing_earlier_diagnostics() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file("/project/first.ts", r#"const first: number = "wrong";"#)
            .unwrap();
        fs.write_file(
            "/project/later.ts",
            "class Later { method(value: string) {} }",
        )
        .unwrap();

        let program = Program::try_new_with_canonical_checker(
            &fs,
            "/project",
            &["first.ts".to_owned(), "later.ts".to_owned()],
            CompilerOptions {
                lib: Some(vec!["es5".to_owned()]),
                ..CompilerOptions::default()
            },
        )
        .unwrap();

        assert_eq!(program.checker, super::ProgramChecker::Canonical);
        let [diagnostic] = program.diagnostics() else {
            panic!("the later class must retain the earlier assignment diagnostic");
        };
        assert_eq!(diagnostic.file_name.as_deref(), Some("/project/first.ts"));
        assert_eq!(diagnostic.code, Some(2322));
        assert_eq!(
            diagnostic.range,
            Some(TextRange::new(TextPos::new(6), TextPos::new(11))),
        );
        assert_eq!(
            diagnostic.message,
            "Type 'string' is not assignable to type 'number'.",
        );
        assert!(diagnostic.related_information.is_empty());
    }

    #[test]
    fn canonical_program_rejects_a_later_unsupported_construction_without_fallback() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file("/project/first.ts", r#"const first: number = "wrong";"#)
            .unwrap();
        // Reuse the unsupported construction input from canonical_class_members.rs.
        fs.write_file(
            "/project/later.ts",
            "class Model { value!: string; }\nconst model = new Model(1);\n",
        )
        .unwrap();

        let Err(error) = Program::try_new_with_canonical_checker(
            &fs,
            "/project",
            &["first.ts".to_owned(), "later.ts".to_owned()],
            CompilerOptions {
                lib: Some(vec!["es5".to_owned()]),
                ..CompilerOptions::default()
            },
        ) else {
            panic!("expected unsupported construction in the later source file");
        };

        assert!(matches!(
            error,
            CanonicalProgramCheckError::SourceCheck {
                file_name,
                error: SourceCheckError::Unsupported(_),
            } if file_name == "/project/later.ts"
        ));
    }

    #[test]
    fn canonical_program_honors_forced_module_detection_for_plain_ts_files() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file("/project/first.ts", r#"const value: number = "wrong";"#)
            .unwrap();
        fs.write_file("/project/second.ts", "const value: string = 1;")
            .unwrap();

        let program = Program::try_new_with_canonical_checker(
            &fs,
            "/project",
            &["first.ts".to_owned(), "second.ts".to_owned()],
            CompilerOptions {
                lib: Some(vec!["es5".to_owned()]),
                module_detection: ModuleDetectionKind::Force,
                ..CompilerOptions::default()
            },
        )
        .unwrap();

        assert_eq!(
            program
                .diagnostics()
                .iter()
                .filter(|diagnostic| diagnostic.code == Some(2322))
                .count(),
            2
        );
    }

    #[test]
    fn canonical_program_constructs_global_object_with_merged_es2015_libraries() {
        for source in [
            "var value = new Object();",
            "interface Foo {} var value = <Foo> new Object();",
        ] {
            let fs = MemoryFileSystem::new(true);
            fs.write_file("/project/input.ts", source).unwrap();

            let program = Program::try_new_with_canonical_checker(
                &fs,
                "/project",
                &["input.ts".to_owned()],
                CompilerOptions {
                    target: ScriptTarget::Es2015,
                    ..CompilerOptions::default()
                },
            )
            .unwrap_or_else(|error| panic!("{source}: {error:?}"));

            assert!(
                program.diagnostics().is_empty(),
                "{source}: {:?}",
                program.diagnostics()
            );
        }
    }

    #[test]
    fn canonical_missing_node_globals_follow_wildcard_type_configuration() {
        for (types, expected_code) in [(None, 2591), (Some(vec!["*".to_owned()]), 2580)] {
            let fs = MemoryFileSystem::new(true);
            fs.write_file("/project/main.ts", "const value = module;")
                .unwrap();

            let program = Program::try_new_with_canonical_checker(
                &fs,
                "/project",
                &["main.ts".to_owned()],
                CompilerOptions {
                    lib: Some(vec!["es5".to_owned()]),
                    types,
                    ..CompilerOptions::default()
                },
            )
            .unwrap();

            let [diagnostic] = program.diagnostics() else {
                panic!(
                    "expected one missing Node global diagnostic: {:?}",
                    program.diagnostics()
                );
            };
            assert_eq!(diagnostic.code, Some(expected_code));
        }
    }

    #[test]
    fn canonical_program_checks_typescript_syntax_in_tsx_files() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file("/project/component.tsx", "const value: number = 'wrong';")
            .unwrap();

        let program = Program::try_new_with_canonical_checker(
            &fs,
            "/project",
            &["component.tsx".to_owned()],
            CompilerOptions {
                lib: Some(vec!["es5".to_owned()]),
                ..CompilerOptions::default()
            },
        )
        .unwrap();
        let [diagnostic] = program.diagnostics() else {
            panic!(
                "expected one TSX semantic diagnostic: {:?}",
                program.diagnostics()
            );
        };
        assert_eq!(
            diagnostic.file_name.as_deref(),
            Some("/project/component.tsx")
        );
        assert_eq!(diagnostic.code, Some(2322));
    }

    #[test]
    fn canonical_program_recovers_complete_unclosed_jsx_tag_fixture() {
        let source = concat!(
            "declare const React: any\n",
            "\n",
            "let Foo = {\n",
            "  Bar() {}\n",
            "}\n",
            "\n",
            "let Baz = () => {}\n",
            "\n",
            "let x = <    Foo.Bar >Hello\n",
            "\n",
            "let y = <   Baz >Hello",
        );
        let fs = MemoryFileSystem::new(true);
        fs.write_file("/project/errorSpanForUnclosedJsxTag.tsx", source)
            .unwrap();

        let (program, state) = Program::try_new_with_canonical_checker_and_queries(
            &fs,
            "/project",
            &["errorSpanForUnclosedJsxTag.tsx".to_owned()],
            CompilerOptions {
                jsx: ts_options::JsxEmit::React,
                target: ScriptTarget::Es2015,
                lib: Some(vec!["es5".to_owned()]),
                ..CompilerOptions::default()
            },
            |program, queries| {
                let file = program
                    .source_file("/project/errorSpanForUnclosedJsxTag.tsx")
                    .unwrap()
                    .id;
                let before = (
                    queries.context.store().type_len(),
                    queries.context.store().symbol_len(),
                    queries.context.store().signature_len(),
                    queries.context.store().mapper_len(),
                    queries.context.store().type_resolution_len(),
                    queries.context.diagnostics().len(),
                );
                queries.context.recheck_source_file(file).unwrap();
                let after = (
                    queries.context.store().type_len(),
                    queries.context.store().symbol_len(),
                    queries.context.store().signature_len(),
                    queries.context.store().mapper_len(),
                    queries.context.store().type_resolution_len(),
                    queries.context.diagnostics().len(),
                );
                (before, after)
            },
        )
        .unwrap();
        let (before, after) = state.unwrap();
        assert_eq!(before, after);

        let foo_start = u32::try_from(source.find("Foo.Bar").unwrap()).unwrap();
        let baz_start = u32::try_from(source.rfind("Baz").unwrap()).unwrap();
        let eof = u32::try_from(source.len()).unwrap();
        assert_eq!(
            program
                .diagnostics()
                .iter()
                .map(|diagnostic| (
                    diagnostic.file_name.as_deref(),
                    diagnostic.code,
                    diagnostic.range,
                    diagnostic.message.as_str(),
                ))
                .collect::<Vec<_>>(),
            [
                (
                    Some("/project/errorSpanForUnclosedJsxTag.tsx"),
                    Some(17008),
                    Some(TextRange::new(
                        TextPos::new(foo_start),
                        TextPos::new(foo_start + 7),
                    )),
                    "JSX element 'Foo.Bar' has no corresponding closing tag.",
                ),
                (
                    Some("/project/errorSpanForUnclosedJsxTag.tsx"),
                    Some(17008),
                    Some(TextRange::new(
                        TextPos::new(baz_start),
                        TextPos::new(baz_start + 3),
                    )),
                    "JSX element 'Baz' has no corresponding closing tag.",
                ),
                (
                    Some("/project/errorSpanForUnclosedJsxTag.tsx"),
                    Some(1005),
                    Some(TextRange::new(TextPos::new(eof), TextPos::new(eof))),
                    "'</' expected.",
                ),
            ]
        );
    }

    #[test]
    fn unclosed_jsx_recovery_does_not_hide_unrelated_object_methods() {
        for source in [
            concat!(
                "declare const React: any\n",
                "let Foo = { Bar() { unsupported(); } }\n",
                "let Baz = () => {}\n",
                "let x = <Foo.Bar>Hello\n",
                "let y = <Baz>Hello",
            ),
            concat!(
                "declare const React: any\n",
                "let Foo = { Bar() {}, Other() {} }\n",
                "let Baz = () => {}\n",
                "let x = <Foo.Bar>Hello\n",
                "let y = <Baz>Hello",
            ),
            concat!(
                "declare const React: any\n",
                "let Foo = { Other() {} }\n",
                "let Baz = () => {}\n",
                "let x = <Foo.Bar>Hello\n",
                "let y = <Baz>Hello",
            ),
            concat!(
                "declare const React: any\n",
                "let Foo = { Bar() {} }\n",
                "let Baz = () => {}\n",
                "let unrelated = Missing\n",
                "let x = <Foo.Bar>Hello\n",
                "let y = <Baz>Hello",
            ),
            concat!(
                "declare const React: any\n",
                "let Foo = { Bar() {} }\n",
                "let Baz = () => {}\n",
                "let x = <Foo.Bar>Hello<Baz>Hello</Baz></Foo.Bar>",
            ),
        ] {
            let fs = MemoryFileSystem::new(true);
            fs.write_file("/project/input.tsx", source).unwrap();
            let Err(error) = Program::try_new_with_canonical_checker(
                &fs,
                "/project",
                &["input.tsx".to_owned()],
                CompilerOptions {
                    jsx: ts_options::JsxEmit::React,
                    target: ScriptTarget::Es2015,
                    lib: Some(vec!["es5".to_owned()]),
                    ..CompilerOptions::default()
                },
            ) else {
                panic!("expected unrelated unsupported JSX syntax to remain rejected: {source}");
            };
            assert!(error.is_unsupported_boundary(), "{source}: {error:?}");
        }
    }

    #[test]
    fn canonical_program_reports_missing_jsx_option_for_each_opening() {
        let fs = MemoryFileSystem::new(true);
        let source = concat!(
            "const view = <div><span /></div>;\n",
            "const fragment = <><span /></>;\n",
        );
        fs.write_file("/project/component.tsx", source).unwrap();

        let program = Program::try_new_with_canonical_checker(
            &fs,
            "/project",
            &["component.tsx".to_owned()],
            CompilerOptions {
                lib: Some(vec!["es5".to_owned()]),
                no_emit: true,
                no_implicit_any: false,
                ..CompilerOptions::default()
            },
        )
        .unwrap();

        let openings = program
            .diagnostics()
            .iter()
            .filter(|diagnostic| diagnostic.code == Some(17004))
            .map(|diagnostic| {
                assert_eq!(
                    diagnostic.message,
                    "Cannot use JSX unless the '--jsx' flag is provided."
                );
                let range = diagnostic.range.unwrap();
                &source[range.start.get() as usize..range.end.get() as usize]
            })
            .collect::<Vec<_>>();
        assert_eq!(openings, ["<div>", "<span />", "<>", "<span />"]);
    }

    #[test]
    fn missing_jsx_option_diagnostics_preserve_recovered_opening_ranges() {
        for (file_name, source, expected) in [
            ("conflict.tsx", "const value = <div>\n<<<<<<< HEAD", "<div>"),
            (
                "input.js",
                "const value = \"oops\";\nconst result = + <number> value;\n",
                "<number>",
            ),
        ] {
            let fs = MemoryFileSystem::new(true);
            let path = format!("/project/{file_name}");
            fs.write_file(&path, source).unwrap();
            let program = Program::new_unchecked_with_options_and_checker(
                &fs,
                "/project",
                &[file_name.to_owned()],
                CompilerOptions {
                    allow_js: true,
                    no_emit: true,
                    ..CompilerOptions::default()
                },
                super::ProgramChecker::Canonical,
            );
            let parser_diagnostics = program.diagnostics().to_vec();
            let source_file = program.source_file(&path).unwrap();
            let mut diagnostics = Vec::new();

            program.add_missing_jsx_option_diagnostics(source_file, &mut diagnostics);

            let [diagnostic] = diagnostics.as_slice() else {
                panic!("expected one JSX option diagnostic for {file_name}: {diagnostics:?}");
            };
            assert_eq!(diagnostic.code, Some(17004));
            let range = diagnostic.range.unwrap();
            assert_eq!(
                &source[range.start.get() as usize..range.end.get() as usize],
                expected
            );
            assert_eq!(program.diagnostics(), parser_diagnostics);
        }
    }

    #[test]
    fn canonical_jsx_option_diagnostics_honor_configured_modes_and_javascript_checking() {
        for jsx in [ts_options::JsxEmit::Preserve, ts_options::JsxEmit::React] {
            let fs = MemoryFileSystem::new(true);
            fs.write_file("/project/component.tsx", "const view = <div />;")
                .unwrap();
            let program = Program::try_new_with_canonical_checker(
                &fs,
                "/project",
                &["component.tsx".to_owned()],
                CompilerOptions {
                    jsx,
                    lib: Some(vec!["es5".to_owned()]),
                    no_emit: true,
                    no_implicit_any: false,
                    ..CompilerOptions::default()
                },
            )
            .unwrap();
            assert!(
                program
                    .diagnostics()
                    .iter()
                    .all(|diagnostic| diagnostic.code != Some(17004)),
                "{jsx:?}: {:?}",
                program.diagnostics()
            );
        }

        for check_js in [false, true] {
            let fs = MemoryFileSystem::new(true);
            fs.write_file("/project/component.js", "const view = <div />;")
                .unwrap();
            let program = Program::try_new_with_canonical_checker(
                &fs,
                "/project",
                &["component.js".to_owned()],
                CompilerOptions {
                    allow_js: true,
                    check_js,
                    lib: Some(vec!["es5".to_owned()]),
                    no_emit: true,
                    no_implicit_any: false,
                    ..CompilerOptions::default()
                },
            )
            .unwrap();
            assert_eq!(
                program
                    .diagnostics()
                    .iter()
                    .any(|diagnostic| diagnostic.code == Some(17004)),
                check_js,
                "checkJs={check_js}: {:?}",
                program.diagnostics()
            );
        }
    }

    #[test]
    fn canonical_jsx_option_diagnostics_follow_comment_directives() {
        for directive in ["// @ts-ignore", "// @ts-expect-error"] {
            let fs = MemoryFileSystem::new(true);
            let source = format!("{directive}\nconst view = <div />;\n");
            fs.write_file("/project/component.tsx", &source).unwrap();
            let program = Program::try_new_with_canonical_checker(
                &fs,
                "/project",
                &["component.tsx".to_owned()],
                CompilerOptions {
                    lib: Some(vec!["es5".to_owned()]),
                    no_emit: true,
                    no_implicit_any: false,
                    ..CompilerOptions::default()
                },
            )
            .unwrap();

            assert!(
                program.diagnostics().is_empty(),
                "{directive}: {:?}",
                program.diagnostics()
            );
        }
    }

    #[test]
    fn canonical_program_preserves_fixed_module_formats() {
        for file_name in ["module.mts", "module.cts", "module.d.mts", "module.d.cts"] {
            let fs = MemoryFileSystem::new(true);
            let source = if ts_path::is_declaration_file(file_name) {
                "export interface Value { value: number }"
            } else {
                "export const value: number = 1;"
            };
            fs.write_file(&format!("/project/{file_name}"), source)
                .unwrap();

            let program = Program::try_new_with_canonical_checker(
                &fs,
                "/project",
                &[file_name.to_owned()],
                CompilerOptions {
                    lib: Some(vec!["es5".to_owned()]),
                    skip_lib_check: true,
                    ..CompilerOptions::default()
                },
            )
            .unwrap_or_else(|error| panic!("failed to check {file_name}: {error:?}"));
            let source = program
                .source_file(&format!("/project/{file_name}"))
                .unwrap();
            assert!(
                canonical_source_file_facts(source, program.options())
                    .unwrap()
                    .is_external_module()
            );
        }
    }

    #[test]
    fn canonical_program_rejects_import_meta_before_binding() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file("/project/main.ts", "const url = import.meta.url;")
            .unwrap();

        let error = Program::try_new_with_canonical_checker(
            &fs,
            "/project",
            &["main.ts".to_owned()],
            CompilerOptions {
                lib: Some(vec!["es5".to_owned()]),
                ..CompilerOptions::default()
            },
        )
        .unwrap_err();
        assert!(matches!(
            error,
            CanonicalProgramCheckError::ImportMetaModuleIndicatorUnsupported { file_name }
                if file_name == "/project/main.ts"
        ));
    }

    #[test]
    fn canonical_program_checks_supported_ordinary_declarations() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file("/project/lib.es5.d.ts", "interface Value { value: number }")
            .unwrap();

        let checked = Program::try_new_with_canonical_checker(
            &fs,
            "/project",
            &["lib.es5.d.ts".to_owned()],
            CompilerOptions {
                lib: Some(vec!["es5".to_owned()]),
                ..CompilerOptions::default()
            },
        )
        .unwrap();
        assert!(
            checked.diagnostics().is_empty(),
            "{:?}",
            checked.diagnostics()
        );

        let program = Program::try_new_with_canonical_checker(
            &fs,
            "/project",
            &["lib.es5.d.ts".to_owned()],
            CompilerOptions {
                lib: Some(vec!["es5".to_owned()]),
                module_detection: ModuleDetectionKind::Force,
                skip_lib_check: true,
                ..CompilerOptions::default()
            },
        )
        .unwrap();
        assert!(program.diagnostics().is_empty());
        let declaration = program.source_file("/project/lib.es5.d.ts").unwrap();
        let facts = canonical_source_file_facts(declaration, program.options()).unwrap();
        assert!(facts.is_declaration_file());
        assert!(!facts.is_default_library());
        assert!(!facts.is_external_or_common_js_module());
    }

    #[test]
    fn canonical_program_checks_erasable_import_assignments_only_in_typescript() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file("/project/target.js", "module.exports = { value: 1 };\n")
            .unwrap();
        fs.write_file(
            "/project/input.ts",
            "import target = require('./target.js');\n",
        )
        .unwrap();

        let program = Program::try_new_with_canonical_checker(
            &fs,
            "/project",
            &["target.js".to_owned(), "input.ts".to_owned()],
            CompilerOptions {
                allow_js: true,
                check_js: true,
                erasable_syntax_only: true,
                lib: Some(vec!["es5".to_owned()]),
                module: ModuleKind::EsNext,
                module_specified: true,
                no_emit: true,
                ..CompilerOptions::default()
            },
        )
        .unwrap();

        let diagnostics = program.diagnostics();
        assert_eq!(diagnostics.len(), 2, "{diagnostics:?}");
        assert_eq!(diagnostics[0].code, Some(1202));
        assert_eq!(diagnostics[1].code, Some(1294));
        for diagnostic in diagnostics {
            assert_eq!(diagnostic.file_name.as_deref(), Some("/project/input.ts"));
            assert_eq!(diagnostic.range.unwrap().start.get(), 0);
        }
    }

    #[test]
    fn external_module_detection_distinguishes_import_equals_references() {
        let external = parse_source_file(r#"import value = require("./value");"#);
        assert!(source_file_is_external_module(&external));

        let internal = parse_source_file(
            "declare namespace values { const value: number; } import alias = values.value;",
        );
        assert!(!source_file_is_external_module(&internal));

        let import_meta = parse_source_file("const url = import.meta.url;");
        assert!(source_file_is_external_module(&import_meta));
    }

    #[test]
    fn canonical_program_preserves_node_package_module_facts() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file("/project/package.json", r#"{"type":"module"}"#)
            .unwrap();
        fs.write_file("/project/main.ts", "const value: number = 1;")
            .unwrap();

        let program = Program::try_new_with_canonical_checker(
            &fs,
            "/project",
            &["main.ts".to_owned()],
            CompilerOptions {
                lib: Some(vec!["es5".to_owned()]),
                module: ModuleKind::NodeNext,
                module_resolution: ModuleResolutionKind::NodeNext,
                module_specified: true,
                ..CompilerOptions::default()
            },
        )
        .unwrap();
        let source = program.source_file("/project/main.ts").unwrap();
        assert!(
            canonical_source_file_facts(source, program.options())
                .unwrap()
                .is_external_module()
        );
        assert!(
            program.diagnostics().is_empty(),
            "{:?}",
            program.diagnostics()
        );
    }

    #[test]
    fn program_node_refs_disambiguate_identical_file_local_ids() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file("/project/first.ts", "export const value = 1;")
            .unwrap();
        fs.write_file("/project/second.ts", "export const value = 2;")
            .unwrap();
        let program = Program::new_with_options(
            &fs,
            "/project",
            &["first.ts".to_owned(), "second.ts".to_owned()],
            CompilerOptions {
                no_lib: true,
                ..CompilerOptions::default()
            },
        );
        let first = program.source_file("/project/first.ts").unwrap();
        let second = program.source_file("/project/second.ts").unwrap();

        assert_eq!(first.parse.source_file, second.parse.source_file);
        assert_ne!(first.id, second.id);
        assert_eq!(first.binding.file_id(), Some(first.id));
        assert_eq!(second.binding.file_id(), Some(second.id));

        let first_ref = first.node_ref(first.parse.source_file).unwrap();
        let second_ref = second.node_ref(second.parse.source_file).unwrap();
        assert_ne!(first_ref, second_ref);
        assert_eq!(
            program.node(first_ref).unwrap().kind,
            SyntaxKind::SourceFile
        );
        assert_eq!(
            program.node(second_ref).unwrap().kind,
            SyntaxKind::SourceFile
        );
    }

    #[test]
    fn program_node_refs_reject_another_program_with_equal_dense_ids() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file("/project/main.ts", "export const value = 1;")
            .unwrap();
        let options = CompilerOptions {
            no_lib: true,
            ..CompilerOptions::default()
        };
        let first =
            Program::new_with_options(&fs, "/project", &["main.ts".to_owned()], options.clone());
        let second = Program::new_with_options(&fs, "/project", &["main.ts".to_owned()], options);
        let first_source = first.source_file("/project/main.ts").unwrap();
        let second_source = second.source_file("/project/main.ts").unwrap();
        let reference = first_source
            .node_ref(first_source.parse.source_file)
            .unwrap();

        assert_eq!(first_source.id, second_source.id);
        assert_eq!(
            first_source.parse.source_file,
            second_source.parse.source_file
        );
        assert_ne!(
            first_source.parse.arena.id(),
            second_source.parse.arena.id()
        );
        assert!(first.node(reference).is_some());
        assert!(second.node(reference).is_none());
    }

    #[test]
    fn source_file_node_refs_fail_closed_for_cross_wired_bindings() {
        let first = parse_source_file("export const first = 1;");
        let second = parse_source_file("export const second = 2;");
        let id = FileId::new(7);
        let binding = bind_source_file_in_file(&first.arena, first.source_file, id);
        let source = SourceFile {
            id,
            file_name: "second.ts".to_owned(),
            source_text: "export const second = 2;".to_owned(),
            parse: second,
            binding,
            checking: empty_check_result(),
            is_default_library: false,
            implied_node_format: ModuleKind::None,
        };

        assert_eq!(source.node_ref(source.parse.source_file), None);
    }

    #[test]
    fn reports_missing_files_and_deduplicates_canonical_names() {
        let fs = MemoryFileSystem::new(false);
        fs.write_file("/project/Main.ts", "const value = 1;")
            .unwrap();
        fs.write_file("/project/other.ts", "const other = 2;")
            .unwrap();
        let program = Program::new(
            &fs,
            "/project",
            &[
                "Main.ts".to_owned(),
                "main.ts".to_owned(),
                "other.ts".to_owned(),
                "missing.ts".to_owned(),
            ],
        );
        assert_eq!(program.source_files().len(), 2);
        assert_eq!(program.diagnostics().len(), 1);
        assert_eq!(program.diagnostics()[0].code, Some(6053));
        assert_eq!(program.source_file("main.ts").unwrap().id, FileId::new(0));
        assert_eq!(program.source_file("other.ts").unwrap().id, FileId::new(1));
    }

    #[test]
    fn assigns_unique_ids_to_transitive_and_bundled_sources() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/main.ts",
            "import { value } from './dependency'; export const result = value;",
        )
        .unwrap();
        fs.write_file("/project/dependency.ts", "export const value = 1;")
            .unwrap();
        let program = Program::new_with_options(
            &fs,
            "/project",
            &["main.ts".to_owned()],
            CompilerOptions::default(),
        );

        assert!(program.source_file("/project/dependency.ts").is_some());
        assert!(
            program
                .source_files()
                .iter()
                .any(|source| source.is_default_library)
        );
        let ids = program
            .source_files()
            .iter()
            .map(|source| source.id)
            .collect::<BTreeSet<_>>();
        assert_eq!(ids.len(), program.source_files().len());
        for (index, source) in program.source_files().iter().enumerate() {
            let expected = FileId::new(u32::try_from(index).unwrap());
            assert_eq!(source.id, expected);
            assert_eq!(source.binding.file_id(), Some(expected));
            assert_eq!(
                program.source_file_by_id(expected).unwrap().file_name,
                source.file_name
            );
        }
    }

    fn assert_canonical_semantic_order(
        program: &Program,
        queries: &CanonicalProgramQueries<'_>,
        expected: &[&str],
    ) {
        let sources = program.canonical_semantic_sources();
        let ids = sources.iter().map(|source| source.id).collect::<Vec<_>>();
        assert_eq!(queries.context.file_order(), ids);
        assert_eq!(
            sources
                .iter()
                .map(|source| ts_path::base_file_name(&source.file_name))
                .collect::<Vec<_>>(),
            expected
        );
        assert!(!program.source_files()[0].is_default_library);
        for (index, source) in program.source_files().iter().enumerate() {
            let id = FileId::new(u32::try_from(index).unwrap());
            assert_eq!(source.id, id);
            assert_eq!(source.binding.file_id(), Some(id));
            assert_eq!(
                program.source_file_by_id(id).unwrap().file_name,
                source.file_name
            );
        }
    }

    #[test]
    fn canonical_semantic_library_order_matches_pinned_es2015_priority() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file("/project/input.ts", "export {};").unwrap();
        let (program, result) = Program::try_new_with_canonical_checker_and_queries(
            &fs,
            "/project",
            &["input.ts".to_owned()],
            CompilerOptions {
                target: ScriptTarget::Es2015,
                ..CompilerOptions::default()
            },
            |program, queries| {
                assert_canonical_semantic_order(
                    program,
                    queries,
                    &[
                        "lib.es6.d.ts",
                        "lib.es5.d.ts",
                        "lib.es2015.d.ts",
                        "lib.dom.d.ts",
                        "lib.dom.iterable.d.ts",
                        "lib.webworker.importscripts.d.ts",
                        "lib.scripthost.d.ts",
                        "lib.es2015.core.d.ts",
                        "lib.es2015.collection.d.ts",
                        "lib.es2015.generator.d.ts",
                        "lib.es2015.iterable.d.ts",
                        "lib.es2015.promise.d.ts",
                        "lib.es2015.proxy.d.ts",
                        "lib.es2015.reflect.d.ts",
                        "lib.es2015.symbol.d.ts",
                        "lib.es2015.symbol.wellknown.d.ts",
                        "lib.es2018.asynciterable.d.ts",
                        "lib.decorators.d.ts",
                        "lib.decorators.legacy.d.ts",
                        "input.ts",
                    ],
                );
            },
        )
        .unwrap();
        assert_eq!(result, Some(()));
        assert!(
            program.diagnostics().is_empty(),
            "{:?}",
            program.diagnostics()
        );
    }

    #[test]
    fn canonical_semantic_library_order_is_independent_of_explicit_roots() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file("/project/input.ts", "export {};").unwrap();
        for roots in [
            ["es2015.symbol.wellknown", "scripthost", "es5"],
            ["es5", "scripthost", "es2015.symbol.wellknown"],
        ] {
            let (program, result) = Program::try_new_with_canonical_checker_and_queries(
                &fs,
                "/project",
                &["input.ts".to_owned()],
                CompilerOptions {
                    lib: Some(roots.map(str::to_owned).into()),
                    ..CompilerOptions::default()
                },
                |program, queries| {
                    assert_canonical_semantic_order(
                        program,
                        queries,
                        &[
                            "lib.es5.d.ts",
                            "lib.scripthost.d.ts",
                            "lib.es2015.symbol.d.ts",
                            "lib.es2015.symbol.wellknown.d.ts",
                            "lib.decorators.d.ts",
                            "lib.decorators.legacy.d.ts",
                            "input.ts",
                        ],
                    );
                },
            )
            .unwrap();
            assert_eq!(result, Some(()));
            assert!(
                program.diagnostics().is_empty(),
                "{:?}",
                program.diagnostics()
            );
        }
    }

    #[test]
    fn canonical_semantic_library_order_includes_transitive_references() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file("/project/input.ts", "import './dependency'; export {};")
            .unwrap();
        fs.write_file("/project/other.ts", "export {};").unwrap();
        fs.write_file(
            "/project/dependency.ts",
            concat!(
                "/// <reference lib=\"es2015.symbol.wellknown\" />\n",
                "/// <reference lib=\"scripthost\" />\n",
                "export {};",
            ),
        )
        .unwrap();
        let (program, result) = Program::try_new_with_canonical_checker_and_queries(
            &fs,
            "/project",
            &["input.ts".to_owned(), "other.ts".to_owned()],
            CompilerOptions {
                lib: Some(vec!["es5".to_owned()]),
                module: ModuleKind::EsNext,
                module_resolution: ModuleResolutionKind::Bundler,
                ..CompilerOptions::default()
            },
            |program, queries| {
                assert_canonical_semantic_order(
                    program,
                    queries,
                    &[
                        "lib.es5.d.ts",
                        "lib.scripthost.d.ts",
                        "lib.es2015.symbol.d.ts",
                        "lib.es2015.symbol.wellknown.d.ts",
                        "lib.decorators.d.ts",
                        "lib.decorators.legacy.d.ts",
                        "dependency.ts",
                        "input.ts",
                        "other.ts",
                    ],
                );
            },
        )
        .unwrap();
        assert_eq!(result, Some(()));
        assert!(
            program.diagnostics().is_empty(),
            "{:?}",
            program.diagnostics()
        );
    }

    fn canonical_source_order_options() -> CompilerOptions {
        CompilerOptions {
            lib: Some(vec!["es5".to_owned()]),
            module: ModuleKind::EsNext,
            module_resolution: ModuleResolutionKind::Bundler,
            ..CompilerOptions::default()
        }
    }

    fn assert_module_dependency_scope(
        input_name: &str,
        input: &str,
        target_name: &str,
        specifier: &str,
        module_detection: ModuleDetectionKind,
        dependency_first: bool,
    ) {
        let fs = MemoryFileSystem::new(true);
        let input_path = format!("/project/{input_name}");
        let target_path = format!("/project/{target_name}");
        fs.write_file(&input_path, input).unwrap();
        fs.write_file(&target_path, "export interface X {};")
            .unwrap();
        let mut program = Program::new_unchecked_with_options_and_checker(
            &fs,
            "/project",
            &[input_name.to_owned(), target_name.to_owned()],
            CompilerOptions {
                module_detection,
                ..canonical_source_order_options()
            },
            super::ProgramChecker::Canonical,
        );
        program.load_remaining_program_graph(&fs);
        let targets = program
            .resolved_modules
            .iter()
            .filter_map(|(key, target)| {
                (key.containing_file == input_path && key.specifier == specifier).then_some(target)
            })
            .collect::<Vec<_>>();
        assert!(!targets.is_empty(), "resolution missing for {input}");
        for target in targets {
            assert_eq!(target, &target_path, "resolution changed for {input}");
        }
        assert_eq!(
            program.source_file_by_id(FileId::new(0)).unwrap().file_name,
            input_path
        );
        assert_eq!(
            program.source_file_by_id(FileId::new(1)).unwrap().file_name,
            target_path
        );
        let ordinary = program
            .canonical_semantic_sources()
            .into_iter()
            .filter(|source| !source.is_default_library)
            .map(|source| source.id)
            .collect::<Vec<_>>();
        let expected = if dependency_first {
            [FileId::new(1), FileId::new(0)]
        } else {
            [FileId::new(0), FileId::new(1)]
        };
        assert_eq!(ordinary, expected, "{input_name}: {input}");
    }

    #[test]
    fn canonical_semantic_source_order_excludes_augmentation_body_static_imports() {
        for input in [
            "export {}; declare module './dep' { import { X } from './dep'; }",
            "export {}; declare module './dep' { export { X } from './dep'; }",
            "export {}; declare global { import { X } from './dep'; }",
        ] {
            assert_module_dependency_scope(
                "input.d.ts",
                input,
                "dep.d.ts",
                "./dep",
                ModuleDetectionKind::Auto,
                false,
            );
        }
    }

    #[test]
    fn canonical_semantic_source_order_applies_ambient_and_namespace_scope_rules() {
        for (input, target, specifier, dependency_first) in [
            (
                "declare namespace N { import X = require('./dep'); }",
                "dep.d.ts",
                "./dep",
                false,
            ),
            (
                "declare module 'ambient' { import { X } from './dep'; }",
                "dep.d.ts",
                "./dep",
                false,
            ),
            (
                "declare module 'ambient' { export { X } from '/project/dep.d.ts'; }",
                "dep.d.ts",
                "/project/dep.d.ts",
                false,
            ),
            (
                "declare module 'ambient' { import { X } from 'pkg'; export { X } from 'pkg'; }",
                "node_modules/pkg/index.d.ts",
                "pkg",
                true,
            ),
            (
                "module 'ambient' { import X = require('pkg'); }",
                "node_modules/pkg/index.d.ts",
                "pkg",
                true,
            ),
            (
                "declare module 'ambient' { namespace N { import { X } from 'pkg'; } }",
                "node_modules/pkg/index.d.ts",
                "pkg",
                false,
            ),
            (
                "declare module 'ambient' { module 'nested' { import { X } from 'pkg'; } }",
                "node_modules/pkg/index.d.ts",
                "pkg",
                false,
            ),
        ] {
            assert_module_dependency_scope(
                "input.d.ts",
                input,
                target,
                specifier,
                ModuleDetectionKind::Auto,
                dependency_first,
            );
        }
    }

    #[test]
    fn canonical_semantic_source_order_uses_module_detection_for_ambient_scopes() {
        for (file_name, input, detection, dependency_first) in [
            (
                "input.ts",
                "declare module 'ambient' { import { X } from 'pkg'; }",
                ModuleDetectionKind::Legacy,
                true,
            ),
            (
                "input.ts",
                "declare module 'ambient' { import { X } from 'pkg'; }",
                ModuleDetectionKind::Force,
                false,
            ),
            (
                "input.ts",
                "module 'ambient' { import { X } from 'pkg'; }",
                ModuleDetectionKind::Legacy,
                false,
            ),
            (
                "input.d.ts",
                "module 'ambient' { import { X } from 'pkg'; }",
                ModuleDetectionKind::Force,
                true,
            ),
            (
                "input.mts",
                "declare module 'ambient' { import { X } from 'pkg'; }",
                ModuleDetectionKind::Auto,
                false,
            ),
            (
                "input.d.mts",
                "module 'ambient' { import { X } from 'pkg'; }",
                ModuleDetectionKind::Auto,
                true,
            ),
        ] {
            assert_module_dependency_scope(
                file_name,
                input,
                "node_modules/pkg/index.d.ts",
                "pkg",
                detection,
                dependency_first,
            );
        }
    }

    #[test]
    fn canonical_semantic_source_order_keeps_dynamic_imports_in_augmentations() {
        assert_module_dependency_scope(
            "input.d.ts",
            "export {}; declare module './dep' { type Added = import('./dep').X; }",
            "dep.d.ts",
            "./dep",
            ModuleDetectionKind::Auto,
            true,
        );
    }

    #[test]
    fn canonical_semantic_source_order_follows_imports_and_repeated_roots() {
        let fs = MemoryFileSystem::new(true);
        for (name, text) in [
            ("input.ts", "import './z'; import './a'; export {};"),
            ("other.ts", "export {};"),
            ("z.ts", "import './shared'; export {};"),
            ("a.ts", "import './shared'; export {};"),
            ("shared.ts", "export {};"),
        ] {
            fs.write_file(&format!("/project/{name}"), text).unwrap();
        }
        for (roots, expected) in [
            (
                vec!["input.ts", "other.ts", "input.ts", "z.ts"],
                ["shared.ts", "z.ts", "a.ts", "input.ts", "other.ts"],
            ),
            (
                vec!["other.ts", "a.ts", "input.ts", "z.ts", "a.ts"],
                ["other.ts", "shared.ts", "a.ts", "z.ts", "input.ts"],
            ),
        ] {
            let roots = roots.into_iter().map(str::to_owned).collect::<Vec<_>>();
            let (program, result) = Program::try_new_with_canonical_checker_and_queries(
                &fs,
                "/project",
                &roots,
                canonical_source_order_options(),
                |program, queries| {
                    let expected = [
                        "lib.es5.d.ts",
                        "lib.decorators.d.ts",
                        "lib.decorators.legacy.d.ts",
                    ]
                    .into_iter()
                    .chain(expected)
                    .collect::<Vec<_>>();
                    assert_canonical_semantic_order(program, queries, &expected);
                },
            )
            .unwrap();
            assert_eq!(result, Some(()));
            assert!(
                program.diagnostics().is_empty(),
                "{:?}",
                program.diagnostics()
            );
        }
    }

    #[test]
    fn canonical_semantic_source_order_stops_import_cycles_on_first_visit() {
        let fs = MemoryFileSystem::new(true);
        for (name, text) in [
            (
                "a.ts",
                "import './b'; import './c'; import './a'; export {};",
            ),
            ("b.ts", "import './c'; import './a'; export {};"),
            ("c.ts", "import './b'; export {};"),
            ("other.ts", "import './c'; export {};"),
        ] {
            fs.write_file(&format!("/project/{name}"), text).unwrap();
        }
        let (program, result) = Program::try_new_with_canonical_checker_and_queries(
            &fs,
            "/project",
            &["a.ts".to_owned(), "other.ts".to_owned(), "b.ts".to_owned()],
            canonical_source_order_options(),
            |program, queries| {
                assert_canonical_semantic_order(
                    program,
                    queries,
                    &[
                        "lib.es5.d.ts",
                        "lib.decorators.d.ts",
                        "lib.decorators.legacy.d.ts",
                        "c.ts",
                        "b.ts",
                        "a.ts",
                        "other.ts",
                    ],
                );
            },
        )
        .unwrap();
        assert_eq!(result, Some(()));
        assert!(
            program.diagnostics().is_empty(),
            "{:?}",
            program.diagnostics()
        );
    }

    #[test]
    fn canonical_semantic_source_order_groups_path_and_type_references_before_imports() {
        let fs = MemoryFileSystem::new(true);
        for (name, text) in [
            (
                "input.ts",
                concat!(
                    "/// <reference types=\"sample\" />\n",
                    "/// <reference path=\"path-first\" />\n",
                    "/// <reference path=\"path-second.ts\" />\n",
                    "import './imported'; export {};",
                ),
            ),
            ("other.ts", "export {};"),
            (
                "path-first.ts",
                "/// <reference path=\"shared.ts\" />\nexport {};",
            ),
            ("path-second.ts", "import './shared'; export {};"),
            ("shared.ts", "export {};"),
            ("imported.ts", "export {};"),
            ("node_modules/@types/sample/index.d.ts", "export {};"),
        ] {
            fs.write_file(&format!("/project/{name}"), text).unwrap();
        }
        let (program, result) = Program::try_new_with_canonical_checker_and_queries(
            &fs,
            "/project",
            &["input.ts".to_owned(), "other.ts".to_owned()],
            CompilerOptions {
                types: Some(Vec::new()),
                ..canonical_source_order_options()
            },
            |program, queries| {
                assert_canonical_semantic_order(
                    program,
                    queries,
                    &[
                        "lib.es5.d.ts",
                        "lib.decorators.d.ts",
                        "lib.decorators.legacy.d.ts",
                        "shared.ts",
                        "path-first.ts",
                        "path-second.ts",
                        "index.d.ts",
                        "imported.ts",
                        "input.ts",
                        "other.ts",
                    ],
                );
            },
        )
        .unwrap();
        assert_eq!(result, Some(()));
        assert!(
            program.diagnostics().is_empty(),
            "{:?}",
            program.diagnostics()
        );
    }

    #[test]
    fn canonical_semantic_source_order_visits_automatic_types_after_explicit_roots() {
        let fs = MemoryFileSystem::new(true);
        for (name, text) in [
            ("input.ts", "import './dependency'; export {};"),
            ("dependency.ts", "export {};"),
            (
                "node_modules/@types/sample/index.d.ts",
                "/// <reference path=\"nested.d.ts\" />\nexport {};",
            ),
            ("node_modules/@types/sample/nested.d.ts", "export {};"),
        ] {
            fs.write_file(&format!("/project/{name}"), text).unwrap();
        }
        let (program, result) = Program::try_new_with_canonical_checker_and_queries(
            &fs,
            "/project",
            &["input.ts".to_owned()],
            CompilerOptions {
                types: Some(vec!["sample".to_owned()]),
                ..canonical_source_order_options()
            },
            |program, queries| {
                assert_canonical_semantic_order(
                    program,
                    queries,
                    &[
                        "lib.es5.d.ts",
                        "lib.decorators.d.ts",
                        "lib.decorators.legacy.d.ts",
                        "dependency.ts",
                        "input.ts",
                        "nested.d.ts",
                        "index.d.ts",
                    ],
                );
            },
        )
        .unwrap();
        assert_eq!(result, Some(()));
        assert!(
            program.diagnostics().is_empty(),
            "{:?}",
            program.diagnostics()
        );
    }

    #[test]
    fn canonical_semantic_source_order_keeps_ambient_matches_out_of_dependency_edges() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file("/project/input.ts", "import 'ambient'; export {};")
            .unwrap();
        fs.write_file("/project/ambient.d.ts", "declare module 'ambient' {}")
            .unwrap();
        let (program, result) = Program::try_new_with_canonical_checker_and_queries(
            &fs,
            "/project",
            &["input.ts".to_owned(), "ambient.d.ts".to_owned()],
            CompilerOptions {
                skip_lib_check: true,
                ..canonical_source_order_options()
            },
            |program, queries| {
                assert_canonical_semantic_order(
                    program,
                    queries,
                    &[
                        "lib.es5.d.ts",
                        "lib.decorators.d.ts",
                        "lib.decorators.legacy.d.ts",
                        "input.ts",
                        "ambient.d.ts",
                    ],
                );
            },
        )
        .unwrap();
        assert_eq!(result, Some(()));
        assert!(
            program.diagnostics().is_empty(),
            "{:?}",
            program.diagnostics()
        );
    }

    #[test]
    fn canonical_semantic_source_order_preserves_roots_with_no_resolve() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file("/project/input.ts", "import './dependency'; export {};")
            .unwrap();
        fs.write_file("/project/dependency.ts", "export {};")
            .unwrap();
        let (program, result) = Program::try_new_with_canonical_checker_and_queries(
            &fs,
            "/project",
            &["input.ts".to_owned(), "dependency.ts".to_owned()],
            CompilerOptions {
                no_resolve: true,
                ..canonical_source_order_options()
            },
            |program, queries| {
                assert_canonical_semantic_order(
                    program,
                    queries,
                    &[
                        "lib.es5.d.ts",
                        "lib.decorators.d.ts",
                        "lib.decorators.legacy.d.ts",
                        "input.ts",
                        "dependency.ts",
                    ],
                );
            },
        )
        .unwrap();
        assert_eq!(result, Some(()));
        assert!(
            program.diagnostics().is_empty(),
            "{:?}",
            program.diagnostics()
        );
    }

    #[test]
    fn canonical_semantic_source_order_controls_merged_declarations() {
        let fs = MemoryFileSystem::new(true);
        for (name, text) in [
            (
                "input.d.ts",
                "/// <reference path=\"dependency.d.ts\" />\ninterface Merged {}",
            ),
            ("other.d.ts", "interface Merged {}"),
            ("dependency.d.ts", "interface Merged {}"),
        ] {
            fs.write_file(&format!("/project/{name}"), text).unwrap();
        }
        let (program, result) = Program::try_new_with_canonical_checker_and_queries(
            &fs,
            "/project",
            &["input.d.ts".to_owned(), "other.d.ts".to_owned()],
            CompilerOptions {
                skip_lib_check: true,
                ..canonical_source_order_options()
            },
            |program, queries| {
                assert_canonical_semantic_order(
                    program,
                    queries,
                    &[
                        "lib.es5.d.ts",
                        "lib.decorators.d.ts",
                        "lib.decorators.legacy.d.ts",
                        "dependency.d.ts",
                        "input.d.ts",
                        "other.d.ts",
                    ],
                );
                let symbol = queries
                    .context
                    .store()
                    .symbol_table(queries.context.globals())
                    .unwrap()
                    .get_source("Merged")
                    .unwrap();
                let files = queries
                    .get_symbol_declarations(symbol)
                    .unwrap()
                    .iter()
                    .map(|declaration| {
                        assert!(program.node(*declaration).is_some());
                        let source = program.source_file_by_id(declaration.file).unwrap();
                        ts_path::base_file_name(&source.file_name)
                    })
                    .collect::<Vec<_>>();
                assert_eq!(files, ["dependency.d.ts", "input.d.ts", "other.d.ts"]);
            },
        )
        .unwrap();
        assert_eq!(result, Some(()));
        assert!(
            program.diagnostics().is_empty(),
            "{:?}",
            program.diagnostics()
        );
    }

    const PRIVATE_WRITE_HELPER_SOURCE: &str = concat!(
        "class Example {\n",
        "    #state = { value: 0 };\n",
        "\n",
        "    update(source: { value: { value: number } }) {\n",
        "        ({ value: this.#state } = source);\n",
        "    }\n",
        "}\n",
        "export {};\n",
    );

    const PRIVATE_HELPER_GLOBALS: &str = concat!(
        "interface IArguments {}\ninterface Array<T> {}\n",
        "interface ReadonlyArray<T> {}\ninterface Object {}\n",
        "interface Function {}\ninterface String {}\ninterface Number {}\n",
        "interface CallableFunction {}\ninterface NewableFunction {}\n",
        "interface Boolean {}\ninterface RegExp {}\n",
    );

    const PRIVATE_HELPER_COMPOUND_SOURCE: &str =
        "class C { #state = 0; update() { this.#state += 1; } } export {};";

    const PRIVATE_HELPER_READ_SOURCE: &str =
        "export class Model { #value = 1; getValue() { return this.#value; } }";

    fn private_write_helper_options() -> CompilerOptions {
        CompilerOptions {
            target: ScriptTarget::Es2015,
            module: ModuleKind::CommonJs,
            module_specified: true,
            module_resolution: ModuleResolutionKind::Node10,
            import_helpers: true,
            es_module_interop: false,
            no_lib: true,
            ..CompilerOptions::default()
        }
    }

    fn private_write_helper_files(source: &str, declarations: Option<&str>) -> MemoryFileSystem {
        let fs = MemoryFileSystem::new(true);
        fs.write_file("/project/input.ts", source).unwrap();
        if let Some(declarations) = declarations {
            fs.write_file(
                "/project/node_modules/tslib/package.json",
                r#"{"name":"tslib","main":"tslib.js","typings":"tslib.d.ts"}"#,
            )
            .unwrap();
            fs.write_file("/project/node_modules/tslib/tslib.d.ts", declarations)
                .unwrap();
            fs.write_file(
                "/project/node_modules/tslib/tslib.js",
                "module.exports = {};",
            )
            .unwrap();
        }
        fs
    }

    fn private_helper_program(
        source: &str,
        declarations: Option<&str>,
        options: CompilerOptions,
    ) -> Program {
        let fs = private_write_helper_files(source, declarations);
        let mut program = Program::new_unchecked_with_options_and_checker(
            &fs,
            "/project",
            &["input.ts".to_owned()],
            options,
            super::ProgramChecker::Canonical,
        );
        program.load_remaining_program_graph(&fs);
        program
    }

    fn private_helper_composition_program(
        source: &str,
        declarations: &str,
        additional_files: &[(&str, &str)],
    ) -> Program {
        let fs = private_write_helper_files(source, Some(declarations));
        fs.write_file("/project/globals.d.ts", PRIVATE_HELPER_GLOBALS)
            .unwrap();
        for (path, text) in additional_files {
            fs.write_file(path, text).unwrap();
        }
        let mut program = Program::new_unchecked_with_options_and_checker(
            &fs,
            "/project",
            &["globals.d.ts".to_owned(), "input.ts".to_owned()],
            CompilerOptions {
                no_emit: true,
                skip_lib_check: true,
                ..private_write_helper_options()
            },
            super::ProgramChecker::Canonical,
        );
        program.load_remaining_program_graph(&fs);
        program
    }

    // Bind the real program graph without claiming class-body checker support.
    fn private_write_helper_context(program: &Program) -> super::CanonicalCheckerContext<'_> {
        let sources = program.canonical_semantic_sources();
        let mut binder = ts_binder::CanonicalBinder::new();
        for source in &sources {
            binder
                .bind_source_file_with_facts(
                    &source.parse.arena,
                    source.parse.source_file,
                    source.id,
                    canonical_source_file_facts(source, &program.options).unwrap(),
                )
                .unwrap();
        }
        for source in &sources {
            if super::is_javascript_file_name(&source.file_name) {
                binder.bind_javascript_declaration_slice(&source.parse.arena, source.id)
            } else {
                binder.bind_typescript_declaration_slice(&source.parse.arena, source.id)
            }
            .unwrap();
        }
        super::CanonicalCheckerContext::new_with_module_resolutions(
            binder.finish(),
            sources
                .into_iter()
                .map(|source| (source.id, &source.parse.arena))
                .collect(),
            program.canonical_checker_options(),
            program.canonical_module_resolution_manifest().unwrap(),
        )
        .unwrap()
    }

    #[test]
    fn canonical_private_write_helpers_resolve_tslib_and_preserve_diagnostic_range() {
        let fs = private_write_helper_files(
            PRIVATE_WRITE_HELPER_SOURCE,
            Some(
                "export declare function __classPrivateFieldGet(a: any, b: any, c: any, d: any): any;",
            ),
        );
        let mut program = Program::new_unchecked_with_options_and_checker(
            &fs,
            "/project",
            &[
                "input.ts".to_owned(),
                "node_modules/tslib/tslib.js".to_owned(),
            ],
            private_write_helper_options(),
            super::ProgramChecker::Canonical,
        );
        program.load_remaining_program_graph(&fs);
        let source = program.source_file("/project/input.ts").unwrap();
        let requirements = program.canonical_external_helper_requirements(source);
        let [(access, helper)] = requirements.as_slice() else {
            panic!("one private-set requirement is expected: {requirements:?}");
        };
        assert_eq!(*helper, "__classPrivateFieldSet");
        assert_eq!(
            program.node(*access).unwrap().kind,
            SyntaxKind::PropertyAccessExpression
        );
        let files = program
            .canonical_semantic_sources()
            .into_iter()
            .map(|source| ts_path::base_file_name(&source.file_name))
            .collect::<Vec<_>>();
        assert_eq!(files, ["tslib.d.ts", "input.ts"]);
        let mut context = private_write_helper_context(&program);
        let mut diagnostics = Vec::new();
        program
            .add_external_helper_diagnostics(source, &mut context, &mut diagnostics)
            .unwrap();
        let [diagnostic] = diagnostics.as_slice() else {
            panic!("one missing-helper diagnostic is expected: {diagnostics:?}");
        };
        let start = PRIVATE_WRITE_HELPER_SOURCE.find("this.#state").unwrap();
        let expected_range = TextRange::new(
            TextPos::new(u32::try_from(start).unwrap()),
            TextPos::new(u32::try_from(start + "this.#state".len()).unwrap()),
        );
        assert_eq!(diagnostic.code, Some(2343));
        assert_eq!(diagnostic.range, Some(expected_range));
        assert_eq!(diagnostic.file_name.as_deref(), Some("/project/input.ts"));
        assert_eq!(
            diagnostic.message,
            "This syntax requires an imported helper named '__classPrivateFieldSet' which does not exist in 'tslib'. Consider upgrading your version of 'tslib'.",
        );
        assert_eq!(
            program
                .diagnostics()
                .iter()
                .map(|diagnostic| diagnostic.code)
                .collect::<Vec<_>>(),
            [Some(6504)],
        );
        assert_eq!(
            program.diagnostics()[0].message,
            concat!(
                "File 'node_modules/tslib/tslib.js' is a JavaScript file. ",
                "Did you mean to enable the 'allowJs' option?\n",
                "  The file is in the program because:\n",
                "    Root file specified for compilation",
            ),
        );
    }

    #[test]
    fn canonical_private_write_helpers_check_exports_and_missing_modules() {
        for (declarations, expected_code) in [
            (None, Some(2354)),
            (Some("export type __classPrivateFieldSet = {};"), Some(2343)),
            (
                Some(
                    "export declare function __classPrivateFieldSet(a: any, b: any, c: any, d: any, e: any): any;",
                ),
                None,
            ),
        ] {
            let fs = private_write_helper_files(PRIVATE_WRITE_HELPER_SOURCE, declarations);
            let mut program = Program::new_unchecked_with_options_and_checker(
                &fs,
                "/project",
                &["input.ts".to_owned()],
                private_write_helper_options(),
                super::ProgramChecker::Canonical,
            );
            program.load_remaining_program_graph(&fs);
            let mut context = private_write_helper_context(&program);
            let source = program.source_file("/project/input.ts").unwrap();
            let mut diagnostics = Vec::new();
            program
                .add_external_helper_diagnostics(source, &mut context, &mut diagnostics)
                .unwrap();
            assert_eq!(
                diagnostics
                    .iter()
                    .filter_map(|diagnostic| diagnostic.code)
                    .collect::<Vec<_>>(),
                expected_code.into_iter().collect::<Vec<_>>(),
            );
            if let Some(diagnostic) = diagnostics.first() {
                let range = diagnostic.range.unwrap();
                assert_eq!(
                    &source.source_text[usize::try_from(range.start.get()).unwrap()
                        ..usize::try_from(range.end.get()).unwrap()],
                    "this.#state",
                );
            }
        }
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Loading and semantic checks use the same source identities.
    fn canonical_private_helpers_keep_loading_separate_from_checking() {
        for (options, required, loaded) in [
            (private_write_helper_options(), true, true),
            (
                CompilerOptions {
                    import_helpers: false,
                    ..private_write_helper_options()
                },
                false,
                false,
            ),
            (
                CompilerOptions {
                    target: ScriptTarget::Es2022,
                    ..private_write_helper_options()
                },
                true,
                true,
            ),
            (
                CompilerOptions {
                    target: ScriptTarget::EsNext,
                    ..private_write_helper_options()
                },
                false,
                true,
            ),
            (
                CompilerOptions {
                    no_emit: true,
                    ..private_write_helper_options()
                },
                true,
                true,
            ),
            (
                CompilerOptions {
                    emit_declaration_only: true,
                    declaration: true,
                    ..private_write_helper_options()
                },
                true,
                true,
            ),
            (
                CompilerOptions {
                    no_check: true,
                    ..private_write_helper_options()
                },
                false,
                true,
            ),
            (
                CompilerOptions {
                    no_emit_helpers: true,
                    ..private_write_helper_options()
                },
                true,
                true,
            ),
            (
                CompilerOptions {
                    target: ScriptTarget::Es2022,
                    use_define_for_class_fields: Some(false),
                    ..private_write_helper_options()
                },
                true,
                true,
            ),
            (
                CompilerOptions {
                    target: ScriptTarget::EsNext,
                    use_define_for_class_fields: Some(false),
                    ..private_write_helper_options()
                },
                true,
                true,
            ),
        ] {
            let fs = private_write_helper_files(PRIVATE_WRITE_HELPER_SOURCE, Some("export {};"));
            let mut program = Program::new_unchecked_with_options_and_checker(
                &fs,
                "/project",
                &["input.ts".to_owned()],
                options,
                super::ProgramChecker::Canonical,
            );
            program.load_remaining_program_graph(&fs);
            let source = program.source_file("/project/input.ts").unwrap();
            assert_eq!(
                !program
                    .canonical_external_helper_requirements(source)
                    .is_empty(),
                required,
                "{:?}",
                program.options,
            );
            assert_eq!(
                program
                    .source_file("/project/node_modules/tslib/tslib.d.ts")
                    .is_some(),
                loaded,
            );
        }
    }

    #[test]
    fn canonical_private_write_helpers_ignore_reads_and_use_the_first_write() {
        for source in [
            "class C { #state = 0; read() { return this.#state; } } export {};",
            "class C { #state = { value: 0 }; read(source: any) { ({ value: this.#state.value } = source); } } export {};",
            "class C { #key = 'value'; read(source: any) { let value = 0; ({ [this.#key]: value } = source); } } export {};",
            "class C { #state = 0; } // this.#state = 1\nconst text = 'this.#state = 1'; export {};",
            "class C { #state = 0; write() { this.#state = 1; } }",
        ] {
            let fs = private_write_helper_files(source, Some("export {};"));
            let program = Program::new_unchecked_with_options_and_checker(
                &fs,
                "/project",
                &["input.ts".to_owned()],
                private_write_helper_options(),
                super::ProgramChecker::Canonical,
            );
            let source = program.source_file("/project/input.ts").unwrap();
            assert!(
                program
                    .canonical_external_helper_requirements(source)
                    .iter()
                    .all(|(_, helper)| *helper != "__classPrivateFieldSet")
            );
        }

        let text = concat!(
            "class C { #state = 0; read() { return this.#state; } ",
            "write() { this.#state = 1; this.#state += 2; } } export {};",
        );
        let fs = private_write_helper_files(text, Some("export {};"));
        let program = Program::new_unchecked_with_options_and_checker(
            &fs,
            "/project",
            &["input.ts".to_owned()],
            private_write_helper_options(),
            super::ProgramChecker::Canonical,
        );
        let source = program.source_file("/project/input.ts").unwrap();
        let requirements = program
            .canonical_external_helper_requirements(source)
            .into_iter()
            .filter(|(_, helper)| *helper == "__classPrivateFieldSet")
            .collect::<Vec<_>>();
        assert_eq!(requirements.len(), 1);
        assert_eq!(
            program.node(requirements[0].0).unwrap().range.start.get(),
            u32::try_from(text.find("this.#state =").unwrap()).unwrap(),
        );
    }

    #[test]
    fn canonical_private_write_helpers_preserve_import_star_and_default() {
        let text = concat!(
            "import * as left from './left'; import right from './right'; ",
            "export const value = left.value + right; ",
            "class C { #state = 0; write() { this.#state = 1; } }",
        );
        let fs = private_write_helper_files(text, Some("export {};"));
        fs.write_file("/project/left.ts", "export const value = 1;")
            .unwrap();
        fs.write_file("/project/right.ts", "export default 2;")
            .unwrap();
        let program = Program::new_unchecked_with_options_and_checker(
            &fs,
            "/project",
            &["input.ts".to_owned()],
            CompilerOptions {
                es_module_interop: true,
                ..private_write_helper_options()
            },
            super::ProgramChecker::Canonical,
        );
        let source = program.source_file("/project/input.ts").unwrap();
        let imports = program.canonical_commonjs_import_helpers(source);
        let combined = program.canonical_external_helper_requirements(source);
        assert_eq!(
            imports
                .iter()
                .map(|(_, helper)| *helper)
                .collect::<Vec<_>>(),
            ["__importStar", "__importDefault"],
        );
        assert_eq!(
            combined
                .iter()
                .filter(|(_, helper)| *helper != "__classPrivateFieldSet")
                .copied()
                .collect::<Vec<_>>(),
            imports,
        );
        assert_eq!(combined.len(), 3);
    }

    #[test]
    fn canonical_import_helpers_preserve_import_only_missing_module_diagnostics() {
        let text = "import * as left from './left'; import right from './right'; export const value = left.value + right;";
        let fs = private_write_helper_files(text, None);
        fs.write_file("/project/left.ts", "export const value = 1;")
            .unwrap();
        fs.write_file("/project/right.ts", "export default 2;")
            .unwrap();
        let mut program = Program::new_unchecked_with_options_and_checker(
            &fs,
            "/project",
            &["input.ts".to_owned()],
            CompilerOptions {
                es_module_interop: true,
                ..private_write_helper_options()
            },
            super::ProgramChecker::Canonical,
        );
        program.load_remaining_program_graph(&fs);
        let source = program.source_file("/project/input.ts").unwrap();
        let mut context = private_write_helper_context(&program);
        let mut diagnostics = Vec::new();
        program
            .add_external_helper_diagnostics(source, &mut context, &mut diagnostics)
            .unwrap();
        assert_eq!(diagnostics.len(), 2);
        assert!(
            diagnostics
                .iter()
                .all(|diagnostic| diagnostic.code == Some(2354))
        );
        assert_eq!(diagnostics[0].range.unwrap().start.get(), 0);
        assert_eq!(
            diagnostics[1].range.unwrap().start.get(),
            u32::try_from(text.find("import right").unwrap()).unwrap(),
        );
    }

    #[test]
    fn canonical_private_helpers_classify_pinned_assignment_forms() {
        use super::PrivateHelperAssignmentKind::{Compound, Definite, None};

        for (statement, expected) in [
            ("this.#state = 1;", Definite),
            ("this.#state &&= 1;", Definite),
            ("this.#state ||= 1;", Definite),
            ("this.#state ??= 1;", Definite),
            ("for (this.#state in values) {}", Definite),
            ("for (this.#state of values) {}", Definite),
            ("for await (this.#state of values) {}", Definite),
            ("for ([this.#state] of values) {}", Definite),
            ("for ({ value: this.#state } of values) {}", Definite),
            ("[this.#state] = values;", Definite),
            ("[...this.#state] = values;", Definite),
            ("({ value: this.#state } = values);", Definite),
            ("({ value: [this.#state] } = values);", Definite),
            ("({ ...this.#state } = values);", Definite),
            ("({ value: this.#state = 1 } = values);", Definite),
            ("((this.#state)) = 1;", Definite),
            ("this.#state! = 1;", Definite),
            ("((this.#state!)) = 1;", Definite),
            ("this.#state += 1;", Compound),
            ("this.#state -= 1;", Compound),
            ("this.#state *= 1;", Compound),
            ("this.#state /= 1;", Compound),
            ("this.#state %= 1;", Compound),
            ("this.#state **= 1;", Compound),
            ("this.#state <<= 1;", Compound),
            ("this.#state >>= 1;", Compound),
            ("this.#state >>>= 1;", Compound),
            ("this.#state &= 1;", Compound),
            ("this.#state |= 1;", Compound),
            ("this.#state ^= 1;", Compound),
            ("++this.#state;", Compound),
            ("--this.#state;", Compound),
            ("this.#state++;", Compound),
            ("this.#state--;", Compound),
            ("return this.#state;", None),
            ("this.#state.value = 1;", None),
            ("values[this.#state] = 1;", None),
            ("({ value: this.#state.value } = values);", None),
            ("({ [this.#state]: value } = values);", None),
            ("({ value = this.#state } = values);", None),
            ("(this.#state as number) = 1;", None),
            ("(this.#state satisfies number) = 1;", None),
            ("(<number>this.#state) = 1;", None),
        ] {
            let text = format!(
                "class C {{ #state = 0; async update(values: unknown) {{ {statement} }} }} export {{}};"
            );
            let program =
                private_helper_program(&text, Some("export {};"), private_write_helper_options());
            let source = program.source_file("/project/input.ts").unwrap();
            assert!(source.parse.diagnostics.is_empty(), "{statement}");
            let requirements = program.canonical_private_helper_requirements(source);
            let expected_helpers: &[&str] = match expected {
                Definite => &["__classPrivateFieldSet"],
                Compound => &["__classPrivateFieldSet", "__classPrivateFieldGet"],
                None => &["__classPrivateFieldGet"],
            };
            assert_eq!(
                requirements
                    .iter()
                    .map(|(_, helper)| *helper)
                    .collect::<Vec<_>>(),
                expected_helpers,
                "{statement}",
            );
            for (access, _) in requirements {
                let range = program.node(access).unwrap().range;
                assert_eq!(
                    &text[usize::try_from(range.start.get()).unwrap()
                        ..usize::try_from(range.end.get()).unwrap()],
                    "this.#state",
                    "{statement}",
                );
            }
        }
    }

    #[test]
    fn canonical_private_helpers_use_access_ambient_context() {
        for text in [
            "declare class C { #state: number; write() { this.#state = 1; } } export {};",
            "class Live { #state = 0; } declare class C { #state: number; write() { this.#state = 1; } } export {};",
            "class Live { #other = 0; } declare class C { #state: number; write() { this.#state = 1; } } export {};",
            "declare namespace N { class C { #state: number; write() { this.#state = 1; } } } export {};",
            "declare function write() { target.#state = 1; } export {};",
            "class C { #state = 0; declare value = this.#state = 1; } export {};",
            "class C { #state = 0; declare write() { this.#state = 1; } } export {};",
        ] {
            let program =
                private_helper_program(text, Some("export {};"), private_write_helper_options());
            let source = program.source_file("/project/input.ts").unwrap();
            assert!(
                program
                    .canonical_private_helper_requirements(source)
                    .is_empty(),
                "{text}",
            );
            assert!(
                program
                    .source_file("/project/node_modules/tslib/tslib.d.ts")
                    .is_some()
            );
        }

        for (text, helper) in [
            (
                "class C { declare #state: number; write() { this.#state = 1; } } export {};",
                "__classPrivateFieldSet",
            ),
            (
                "class C { #state = 0; declare get value() { return this.#state; } } export {};",
                "__classPrivateFieldGet",
            ),
            (
                "declare function dec(value: unknown): unknown; class C { #state = 0; method() { @dec(this.#state) declare class Ambient {} } } export {};",
                "__classPrivateFieldGet",
            ),
            (
                "declare class Ambient { #state: number; write() { this.#state = 1; } } class Live { #state = 0; write() { this.#state = 1; } } export {};",
                "__classPrivateFieldSet",
            ),
        ] {
            let program =
                private_helper_program(text, Some("export {};"), private_write_helper_options());
            let source = program.source_file("/project/input.ts").unwrap();
            let requirements = program.canonical_private_helper_requirements(source);
            assert_eq!(
                requirements
                    .iter()
                    .map(|(_, helper)| *helper)
                    .collect::<Vec<_>>(),
                [helper],
                "{text}"
            );
            assert_eq!(
                program.node(requirements[0].0).unwrap().range.start.get(),
                u32::try_from(text.rfind("this.#state").unwrap()).unwrap(),
                "{text}",
            );
        }
    }

    #[test]
    fn canonical_private_helpers_do_not_require_lexical_declarations() {
        for text in [
            "class C { #state = 0; } const c = new C(); c.#state = 1; export {};",
            "const c = {}; c.#state = 1; export {};",
            "class C { write() { this.#state = 1; } } export {};",
        ] {
            let program =
                private_helper_program(text, Some("export {};"), private_write_helper_options());
            let source = program.source_file("/project/input.ts").unwrap();
            let mut context = private_write_helper_context(&program);
            let mut diagnostics = Vec::new();
            program
                .add_external_helper_diagnostics(source, &mut context, &mut diagnostics)
                .unwrap();
            assert_eq!(diagnostics.len(), 1, "{text}: {diagnostics:?}");
            assert_eq!(diagnostics[0].code, Some(2343));
            assert!(diagnostics[0].message.contains("__classPrivateFieldSet"));
            let range = diagnostics[0].range.unwrap();
            let access = &text[usize::try_from(range.start.get()).unwrap()
                ..usize::try_from(range.end.get()).unwrap()];
            assert!(matches!(access, "c.#state" | "this.#state"), "{access}");
        }
    }

    #[test]
    fn canonical_private_helpers_deduplicate_requests_and_missing_modules() {
        let text = concat!(
            "class C { #state = 0; write() { ",
            "this.#state += 1; this.#state = 2; return this.#state; } } export {};",
        );
        for declarations in [None, Some("export {};")] {
            let program =
                private_helper_program(text, declarations, private_write_helper_options());
            let source = program.source_file("/project/input.ts").unwrap();
            let requirements = program.canonical_private_helper_requirements(source);
            assert_eq!(
                requirements
                    .iter()
                    .map(|(_, helper)| *helper)
                    .collect::<Vec<_>>(),
                ["__classPrivateFieldSet", "__classPrivateFieldGet"],
            );
            assert_eq!(requirements[0].0, requirements[1].0);
            let mut context = private_write_helper_context(&program);
            let mut diagnostics = Vec::new();
            program
                .add_external_helper_diagnostics(source, &mut context, &mut diagnostics)
                .unwrap();
            let sorted = program.canonical_diagnostic_snapshot(&diagnostics);
            if declarations.is_some() {
                assert_eq!(sorted.len(), 2);
                assert!(sorted[0].message.contains("__classPrivateFieldGet"));
                assert!(sorted[1].message.contains("__classPrivateFieldSet"));
                assert!(
                    sorted
                        .iter()
                        .all(|diagnostic| diagnostic.code == Some(2343))
                );
            } else {
                assert_eq!(sorted.len(), 1);
                assert_eq!(sorted[0].code, Some(2354));
            }
            assert!(sorted.iter().all(|diagnostic| {
                diagnostic.range.unwrap().start.get()
                    == u32::try_from(text.find("this.#state").unwrap()).unwrap()
            }));
        }
    }

    #[test]
    fn canonical_import_helper_loading_uses_file_options_without_helper_requests() {
        for (file_name, text, expected) in [
            ("input.ts", "const value = 1;", [false, true, true, true]),
            ("input.ts", "export {};", [true; 4]),
            ("input.tsx", "const value = 1;", [false, true, true, true]),
            ("input.js", "const value = 1;", [true; 4]),
            ("input.jsx", "const value = 1;", [true; 4]),
            ("input.js", "module.exports = {};", [true; 4]),
            ("input.d.ts", "export {};", [false; 4]),
            ("input.d.mts", "export {};", [false; 4]),
            ("input.d.cts", "export {};", [false; 4]),
        ] {
            for ((isolated_modules, verbatim_module_syntax, module_detection), loaded) in [
                (false, false, ModuleDetectionKind::Auto),
                (true, false, ModuleDetectionKind::Auto),
                (false, true, ModuleDetectionKind::Auto),
                (false, false, ModuleDetectionKind::Force),
            ]
            .into_iter()
            .zip(expected)
            {
                let fs = private_write_helper_files("", Some("export {};"));
                let path = format!("/project/{file_name}");
                fs.write_file(&path, text).unwrap();
                let mut program = Program::new_unchecked_with_options_and_checker(
                    &fs,
                    "/project",
                    &[file_name.to_owned()],
                    CompilerOptions {
                        isolated_modules,
                        verbatim_module_syntax,
                        module_detection,
                        no_check: true,
                        no_emit: true,
                        allow_js: true,
                        ..private_write_helper_options()
                    },
                    super::ProgramChecker::Canonical,
                );
                program.load_remaining_program_graph(&fs);
                let source = program.source_file(&path).unwrap();
                assert!(
                    program
                        .canonical_external_helper_requirements(source)
                        .is_empty()
                );
                assert_eq!(
                    program
                        .source_file("/project/node_modules/tslib/tslib.d.ts")
                        .is_some(),
                    loaded,
                    "{file_name}: {:?}",
                    program.options,
                );
                assert_eq!(
                    program
                        .graph_resolutions
                        .iter()
                        .filter(|resolution| {
                            resolution.request.kind
                                == super::ProgramGraphResolutionKind::ImportHelpers
                                && resolution.request.containing_file == path
                        })
                        .count(),
                    usize::from(loaded),
                    "{file_name}: {:?}",
                    program.options,
                );
            }
        }
    }

    #[test]
    fn canonical_import_helpers_preserve_per_file_resolution_modes() {
        use super::CanonicalModuleResolutionMode::{CommonJs, Esm};

        for (file_name, module, package_is_esm, mode) in [
            ("input.ts", ModuleKind::CommonJs, false, CommonJs),
            ("input.ts", ModuleKind::EsNext, false, Esm),
            ("input.ts", ModuleKind::Preserve, false, Esm),
            ("input.ts", ModuleKind::NodeNext, false, CommonJs),
            ("input.ts", ModuleKind::NodeNext, true, Esm),
            ("input.mts", ModuleKind::NodeNext, false, Esm),
            ("input.cts", ModuleKind::NodeNext, true, CommonJs),
        ] {
            let fs = MemoryFileSystem::new(true);
            let path = format!("/project/{file_name}");
            fs.write_file(&path, PRIVATE_WRITE_HELPER_SOURCE).unwrap();
            fs.write_file(
                "/project/package.json",
                if package_is_esm {
                    r#"{"type":"module"}"#
                } else {
                    r#"{"type":"commonjs"}"#
                },
            )
            .unwrap();
            fs.write_file(
                "/project/node_modules/tslib/package.json",
                r#"{"name":"tslib","exports":{"import":{"types":"./esm.d.mts"},"require":{"types":"./cjs.d.cts"}}}"#,
            ).unwrap();
            for target in ["esm.d.mts", "cjs.d.cts"] {
                fs.write_file(
                    &format!("/project/node_modules/tslib/{target}"),
                    "export {};",
                )
                .unwrap();
            }
            let mut program = Program::new_unchecked_with_options_and_checker(
                &fs,
                "/project",
                &[file_name.to_owned()],
                CompilerOptions {
                    module,
                    module_resolution: if module == ModuleKind::NodeNext {
                        ModuleResolutionKind::NodeNext
                    } else {
                        ModuleResolutionKind::Bundler
                    },
                    no_emit: true,
                    ..private_write_helper_options()
                },
                super::ProgramChecker::Canonical,
            );
            program.load_remaining_program_graph(&fs);
            let expected_target = match mode {
                CommonJs => "/project/node_modules/tslib/cjs.d.cts",
                Esm => "/project/node_modules/tslib/esm.d.mts",
                super::CanonicalModuleResolutionMode::None => unreachable!(),
            };
            assert_eq!(
                program
                    .resolved_modules
                    .get(&super::ResolvedModuleKey::new(
                        path.clone(),
                        "tslib".to_owned(),
                        mode,
                    ))
                    .map(String::as_str),
                Some(expected_target),
                "{file_name}: {module:?}",
            );
            let requests = program
                .graph_resolutions
                .iter()
                .filter(|resolution| {
                    resolution.request.kind == super::ProgramGraphResolutionKind::ImportHelpers
                        && resolution.request.containing_file == path
                })
                .collect::<Vec<_>>();
            assert_eq!(requests.len(), 1);
            assert_eq!(
                requests[0].request.mode,
                Some(match mode {
                    CommonJs => ts_module::ModuleFormat::CommonJs,
                    Esm => ts_module::ModuleFormat::Esm,
                    super::CanonicalModuleResolutionMode::None => unreachable!(),
                })
            );
            let mut context = private_write_helper_context(&program);
            let source = program.source_file(&path).unwrap();
            let mut diagnostics = Vec::new();
            program
                .add_external_helper_diagnostics(source, &mut context, &mut diagnostics)
                .unwrap();
            assert_eq!(
                diagnostics.len(),
                1,
                "{file_name}: {module:?}: {diagnostics:?}"
            );
            assert_eq!(diagnostics[0].code, Some(2343));
        }
    }

    #[test]
    fn canonical_private_helpers_compose_real_arity_queries() {
        for (get, set, get_valid, set_valid) in [
            (
                "(a: unknown, b: unknown, c: unknown, d: unknown): unknown",
                "(a: unknown, b: unknown, c: unknown, d: unknown, e: unknown): unknown",
                true,
                true,
            ),
            (
                "(a: unknown, b: unknown, c: unknown): unknown",
                "(a: unknown, b: unknown, c: unknown, d: unknown): unknown",
                false,
                false,
            ),
            (
                "(a: unknown, b: unknown, c: unknown): unknown",
                "(a: unknown, b: unknown, c: unknown, d: unknown, e: unknown): unknown",
                false,
                true,
            ),
            (
                "<T>(a: T, b: unknown, c: unknown, d?: unknown): T",
                "<T>(a: T, b: unknown, c: unknown, d: unknown, e?: unknown): T",
                true,
                true,
            ),
            (
                "(...args: [unknown, unknown, unknown, unknown]): Missing",
                "(...args: [unknown, unknown, unknown, unknown, unknown]): Missing",
                true,
                true,
            ),
            (
                "(...args: unknown[]): Missing",
                "(...args: unknown[]): Missing",
                false,
                false,
            ),
        ] {
            let declarations = format!(
                "export declare function __classPrivateFieldGet{get}; export declare function __classPrivateFieldSet{set};"
            );
            let program = private_helper_composition_program(
                PRIVATE_HELPER_COMPOUND_SOURCE,
                &declarations,
                &[],
            );
            let source = program.source_file("/project/input.ts").unwrap();
            let mut context = private_write_helper_context(&program);
            let mut diagnostics = Vec::new();
            program
                .add_external_helper_diagnostics(source, &mut context, &mut diagnostics)
                .unwrap_or_else(|error| panic!("{declarations}: {error:?}"));
            let sorted = program.canonical_diagnostic_snapshot(&diagnostics);
            let expected = [
                (get_valid, "__classPrivateFieldGet", 4),
                (set_valid, "__classPrivateFieldSet", 5),
            ]
            .into_iter()
            .filter(|(valid, _, _)| !valid)
            .collect::<Vec<_>>();
            assert_eq!(sorted.len(), expected.len(), "{declarations}: {sorted:?}");
            for (diagnostic, (_, helper, arity)) in sorted.iter().zip(expected) {
                assert_eq!(diagnostic.code, Some(2807));
                assert!(
                    diagnostic
                        .message
                        .contains(&format!("'{helper}' with {arity} parameters"))
                );
            }
            let warm = (
                context.store().type_len(),
                context.store().symbol_len(),
                context.store().signature_len(),
                context.store().mapper_len(),
                context.store().type_resolution_len(),
            );
            let mut repeated = Vec::new();
            program
                .add_external_helper_diagnostics(source, &mut context, &mut repeated)
                .unwrap();
            assert_eq!(program.canonical_diagnostic_snapshot(&repeated), sorted);
            assert_eq!(
                (
                    context.store().type_len(),
                    context.store().symbol_len(),
                    context.store().signature_len(),
                    context.store().mapper_len(),
                    context.store().type_resolution_len()
                ),
                warm
            );
            for file in program.source_files() {
                assert!(
                    context
                        .store()
                        .source_file_links(context.source_file(file.id).unwrap())
                        .is_none_or(|links| !links.type_checked)
                );
            }
        }
    }

    #[test]
    fn canonical_private_helpers_compose_stars_and_type_only_aliases() {
        let leaf = concat!(
            "export declare function __classPrivateFieldGet(a: unknown, b: unknown, c: unknown, d: unknown): Missing;",
            "export declare function __classPrivateFieldSet(a: unknown, b: unknown, c: unknown, d: unknown, e: unknown): Missing;",
        );
        for declarations in [
            "export * from './helpers';",
            "export type * from './helpers';",
            "export { __classPrivateFieldGet, __classPrivateFieldSet } from './helpers';",
            "export type { __classPrivateFieldGet, __classPrivateFieldSet } from './helpers';",
        ] {
            let program = private_helper_composition_program(
                PRIVATE_HELPER_COMPOUND_SOURCE,
                declarations,
                &[("/project/node_modules/tslib/helpers.d.ts", leaf)],
            );
            let source = program.source_file("/project/input.ts").unwrap();
            let mut context = private_write_helper_context(&program);
            for _ in 0..2 {
                let mut diagnostics = Vec::new();
                program
                    .add_external_helper_diagnostics(source, &mut context, &mut diagnostics)
                    .unwrap();
                assert!(diagnostics.is_empty(), "{declarations}: {diagnostics:?}");
            }
            assert!(context.diagnostics().is_empty());
        }
    }

    #[test]
    fn canonical_private_helpers_require_value_meaning_and_callability() {
        for (declarations, code) in [
            (
                "export type __classPrivateFieldGet = unknown; export interface __classPrivateFieldSet {}",
                2343,
            ),
            (
                "export declare const __classPrivateFieldGet: number; export declare const __classPrivateFieldSet: unknown;",
                2807,
            ),
            (
                "export declare const __classPrivateFieldGet: {}; export declare const __classPrivateFieldSet: { tag: number };",
                2807,
            ),
        ] {
            let program = private_helper_composition_program(
                PRIVATE_HELPER_COMPOUND_SOURCE,
                declarations,
                &[],
            );
            let source = program.source_file("/project/input.ts").unwrap();
            let mut context = private_write_helper_context(&program);
            let mut diagnostics = Vec::new();
            program
                .add_external_helper_diagnostics(source, &mut context, &mut diagnostics)
                .unwrap();
            assert_eq!(diagnostics.len(), 2, "{declarations}: {diagnostics:?}");
            assert!(
                diagnostics
                    .iter()
                    .all(|diagnostic| diagnostic.code == Some(code))
            );
        }
    }

    #[test]
    fn canonical_private_helpers_reject_callable_variables_and_type_only_aliases() {
        for (declarations, helper_file) in [
            (
                concat!(
                    "export declare const __classPrivateFieldGet: (a: unknown, b: unknown, c: unknown, d: unknown) => unknown;\n",
                    "export declare const __classPrivateFieldSet: (a: unknown, b: unknown, c: unknown, d: unknown, e: unknown) => unknown;\n",
                ),
                None,
            ),
            (
                "export type { get as __classPrivateFieldGet, set as __classPrivateFieldSet } from './helpers';",
                Some(concat!(
                    "export declare const get: (a: unknown, b: unknown, c: unknown, d: unknown) => unknown;\n",
                    "export declare const set: (a: unknown, b: unknown, c: unknown, d: unknown, e: unknown) => unknown;\n",
                )),
            ),
        ] {
            let additional =
                helper_file.map(|text| ("/project/node_modules/tslib/helpers.d.ts", text));
            let program = private_helper_composition_program(
                PRIVATE_HELPER_COMPOUND_SOURCE,
                declarations,
                additional.as_slice(),
            );
            let source = program.source_file("/project/input.ts").unwrap();
            let mut context = private_write_helper_context(&program);
            for _ in 0..2 {
                let mut diagnostics = Vec::new();
                program
                    .add_external_helper_diagnostics(source, &mut context, &mut diagnostics)
                    .unwrap_or_else(|error| panic!("{declarations}: {error:?}"));
                let sorted = program.canonical_diagnostic_snapshot(&diagnostics);
                assert_eq!(sorted.len(), 2, "{declarations}: {sorted:?}");
                for (diagnostic, (helper, arity)) in sorted
                    .iter()
                    .zip([("__classPrivateFieldGet", 4), ("__classPrivateFieldSet", 5)])
                {
                    assert_eq!(diagnostic.code, Some(2807));
                    assert_eq!(diagnostic.file_name.as_deref(), Some("/project/input.ts"));
                    assert_eq!(
                        diagnostic.range,
                        Some(TextRange::new(TextPos::new(33), TextPos::new(44)))
                    );
                    assert_eq!(
                        diagnostic.message,
                        format!(
                            concat!(
                                "This syntax requires an imported helper named '{0}' with {1} ",
                                "parameters, which is not compatible with the one in 'tslib'. ",
                                "Consider upgrading your version of 'tslib'.",
                            ),
                            helper, arity,
                        )
                    );
                }
            }
            assert!(context.diagnostics().is_empty());
        }
    }

    #[test]
    fn canonical_private_helpers_preserve_provider_failures_atomically() {
        for declarations in [
            "export * from './missing';",
            "export declare function __classPrivateFieldGet(this: object, a: unknown, b: unknown, c: unknown, d: unknown): unknown;",
            "export declare function __classPrivateFieldGet(a: unknown): unknown; export declare function __classPrivateFieldGet(a: unknown, b: unknown, c: unknown, d: unknown): unknown;",
            "export declare function __classPrivateFieldGet<T>(a: T, b: unknown, c: unknown, d?: unknown): Missing;",
        ] {
            let program = private_helper_composition_program(
                PRIVATE_HELPER_COMPOUND_SOURCE,
                declarations,
                &[],
            );
            let source = program.source_file("/project/input.ts").unwrap();
            let mut context = private_write_helper_context(&program);
            let sentinel = super::ProgramDiagnostic {
                file_name: None,
                range: None,
                code: Some(1234),
                category: ts_diagnostics::Category::Error,
                message: "existing diagnostic".to_owned(),
                related_information: Vec::new(),
            };
            let mut diagnostics = vec![sentinel.clone()];
            let error = program
                .add_external_helper_diagnostics(source, &mut context, &mut diagnostics)
                .unwrap_err();
            assert!(
                matches!(
                    &error,
                    super::CanonicalProgramCheckError::ImportHelper { .. }
                ),
                "{error:?}"
            );
            assert!(error.is_unsupported_boundary(), "{declarations}: {error:?}");
            assert_eq!(diagnostics, [sentinel]);
        }
    }

    #[test]
    fn canonical_private_helpers_keep_foreign_source_identities_fatal() {
        let program = private_helper_composition_program(
            PRIVATE_HELPER_COMPOUND_SOURCE,
            "export declare function __classPrivateFieldGet(a: unknown, b: unknown, c: unknown, d: unknown): unknown;",
            &[],
        );
        let source = program.source_file("/project/input.ts").unwrap();
        let target = program
            .source_file("/project/node_modules/tslib/tslib.d.ts")
            .unwrap();
        let mut context = private_write_helper_context(&program);
        let foreign = private_write_helper_context(&program);
        let (_, bound) = foreign.file(target.id).unwrap();
        let module = bound.symbol(bound.source_file()).unwrap();
        let (node, _) = program.canonical_external_helper_requirements(source)[0];
        let before = (
            context.store().type_len(),
            context.store().symbol_len(),
            context.store().signature_len(),
            context.store().mapper_len(),
            context.store().type_resolution_len(),
        );
        let error = program
            .private_import_helper_diagnostic(
                source,
                node,
                super::PrivateImportHelper::Get,
                module,
                &mut context,
            )
            .unwrap_err();
        assert!(matches!(
            &error,
            super::CanonicalProgramCheckError::ImportHelper { error, .. }
                if matches!(error.as_ref(),
                    super::CanonicalImportHelperError::Export(
                        super::CanonicalModuleExportQueryError::InvalidModule(invalid)
                    ) if *invalid == module)
        ));
        assert!(!error.is_unsupported_boundary());
        assert_eq!(
            error.failure_class(),
            super::CanonicalProgramCheckFailureClass::Fatal {
                invariant_code: "INV.PROGRAM.IMPORT_HELPER",
            }
        );
        assert_eq!(
            (
                context.store().type_len(),
                context.store().symbol_len(),
                context.store().signature_len(),
                context.store().mapper_len(),
                context.store().type_resolution_len(),
            ),
            before
        );
        assert!(context.diagnostics().is_empty());
    }

    #[test]
    fn review_helper_compiler_callable_variables_keep_public_diagnostic_ownership() {
        let callable = "(a: unknown, b: unknown, c: unknown, d: unknown) => Missing";
        for through_type_only_alias in [false, true] {
            let declarations = if through_type_only_alias {
                "export type { helper as __classPrivateFieldGet } from './helpers';".to_owned()
            } else {
                format!("export declare const __classPrivateFieldGet: {callable};")
            };
            let fs = private_write_helper_files(PRIVATE_HELPER_READ_SOURCE, Some(&declarations));
            fs.write_file("/project/globals.d.ts", PRIVATE_HELPER_GLOBALS)
                .unwrap();
            let helper_path = if through_type_only_alias {
                let path = "/project/node_modules/tslib/helpers.d.ts";
                fs.write_file(path, &format!("export declare const helper: {callable};"))
                    .unwrap();
                path
            } else {
                "/project/node_modules/tslib/tslib.d.ts"
            };
            let start =
                u32::try_from(PRIVATE_HELPER_READ_SOURCE.find("this.#value").unwrap()).unwrap();
            let expected_range = TextRange::new(TextPos::new(start), TextPos::new(start + 11));
            let (program, snapshot) = Program::try_new_with_canonical_checker_and_queries(
                &fs,
                "/project",
                &["globals.d.ts".to_owned(), "input.ts".to_owned()],
                CompilerOptions {
                    no_emit: true,
                    skip_lib_check: true,
                    ..private_write_helper_options()
                },
                |program, queries| {
                    let helper = program.source_file(helper_path).unwrap();
                    let annotation = helper
                        .parse
                        .arena
                        .iter()
                        .find_map(|(_, record)| {
                            let NodeData::VariableDeclaration(variable) = &record.data else {
                                return None;
                            };
                            variable.type_.and_then(|node| helper.node_ref(node))
                        })
                        .unwrap();
                    assert!(
                        queries
                            .context
                            .store()
                            .type_node_links(annotation)
                            .is_none()
                    );
                    let cold = queries.cold_diagnostic_snapshot();
                    assert_eq!(cold.len(), 1, "{declarations}: {cold:?}");
                    assert_eq!(cold[0].code, Some(2807));
                    assert_eq!(cold[0].file_name.as_deref(), Some("/project/input.ts"));
                    assert_eq!(cold[0].range, Some(expected_range));
                    assert_eq!(
                        cold[0].message,
                        concat!(
                            "This syntax requires an imported helper named '__classPrivateFieldGet' with 4 ",
                            "parameters, which is not compatible with the one in 'tslib'. ",
                            "Consider upgrading your version of 'tslib'.",
                        )
                    );
                    assert_eq!(queries.replay_sources().unwrap(), cold);
                    assert_eq!(queries.cold_diagnostic_snapshot(), cold);
                    assert!(
                        queries
                            .context
                            .store()
                            .type_node_links(annotation)
                            .is_none()
                    );
                    cold
                },
            )
            .unwrap();
            assert_eq!(snapshot.as_deref(), Some(program.diagnostics()));
        }
    }

    #[test]
    fn review_helper_compiler_incompatible_values_do_not_publish_partial_diagnostics() {
        let program = private_helper_composition_program(
            PRIVATE_HELPER_COMPOUND_SOURCE,
            concat!(
                "export declare const __classPrivateFieldSet: ",
                "(a: unknown, b: unknown, c: unknown, d: unknown, e: unknown) => Missing; ",
                "export declare function __classPrivateFieldGet(this: object, ",
                "a: unknown, b: unknown, c: unknown, d: unknown): unknown;",
            ),
            &[],
        );
        let source = program.source_file("/project/input.ts").unwrap();
        let target = program
            .source_file("/project/node_modules/tslib/tslib.d.ts")
            .unwrap();
        let requirements = program.canonical_external_helper_requirements(source);
        assert_eq!(requirements[0].1, "__classPrivateFieldSet");
        assert_eq!(requirements[1].1, "__classPrivateFieldGet");
        let mut context = private_write_helper_context(&program);
        let (_, bound) = context.file(target.id).unwrap();
        let module = bound.symbol(bound.source_file()).unwrap();
        let negative = program
            .private_import_helper_diagnostic(
                source,
                requirements[0].0,
                super::PrivateImportHelper::Set,
                module,
                &mut context,
            )
            .unwrap()
            .unwrap();
        assert_eq!(negative.code, Some(2807));
        let sentinel = super::ProgramDiagnostic {
            file_name: None,
            range: None,
            code: Some(1234),
            category: ts_diagnostics::Category::Error,
            message: "existing diagnostic".to_owned(),
            related_information: Vec::new(),
        };
        for _ in 0..2 {
            let mut diagnostics = vec![sentinel.clone()];
            let error = program
                .add_external_helper_diagnostics(source, &mut context, &mut diagnostics)
                .unwrap_err();
            assert!(matches!(
                &error,
                super::CanonicalProgramCheckError::ImportHelper { error, .. }
                    if matches!(error.as_ref(), super::CanonicalImportHelperError::Signature(_))
            ));
            assert_eq!(
                error.failure_class(),
                super::CanonicalProgramCheckFailureClass::Unsupported {
                    capability_code: "T06.IMPORT_HELPER_SIGNATURE",
                }
            );
            assert_eq!(diagnostics.as_slice(), std::slice::from_ref(&sentinel));
            assert!(context.diagnostics().is_empty());
        }
    }

    #[test]
    fn canonical_private_helpers_retain_alias_cycle_events() {
        let program = private_helper_composition_program(
            PRIVATE_HELPER_COMPOUND_SOURCE,
            "export { __classPrivateFieldSet } from './cycle';",
            &[(
                "/project/node_modules/tslib/cycle.d.ts",
                "export { __classPrivateFieldSet } from './tslib';",
            )],
        );
        let source = program.source_file("/project/input.ts").unwrap();
        let mut context = private_write_helper_context(&program);
        let mut diagnostics = Vec::new();
        let error = program
            .add_external_helper_diagnostics(source, &mut context, &mut diagnostics)
            .unwrap_err();
        let super::CanonicalProgramCheckError::ImportHelper { error, .. } = error else {
            panic!("expected helper alias error");
        };
        let super::CanonicalImportHelperError::AliasUnresolved { resolution, .. } = *error else {
            panic!("expected unresolved alias: {error:?}");
        };
        assert_eq!(resolution.target, super::AliasTargetState::Unknown);
        assert!(!resolution.events.is_empty());
        assert!(
            resolution
                .events
                .iter()
                .all(|event| event.diagnostic_code() == 2303)
        );
        assert!(diagnostics.is_empty());
    }

    #[test]
    fn canonical_private_helper_callbacks_and_replay_use_checked_sources() {
        for declarations in [
            "export {};",
            "export declare function __classPrivateFieldGet(a: unknown, b: unknown, c: unknown): unknown;",
            "export declare function __classPrivateFieldGet(a: unknown, b: unknown, c: unknown, d: unknown): unknown;",
        ] {
            let fs = private_write_helper_files(PRIVATE_HELPER_READ_SOURCE, Some(declarations));
            fs.write_file("/project/globals.d.ts", PRIVATE_HELPER_GLOBALS)
                .unwrap();
            let (program, snapshot) = Program::try_new_with_canonical_checker_and_queries(
                &fs,
                "/project",
                &["globals.d.ts".to_owned(), "input.ts".to_owned()],
                CompilerOptions {
                    no_emit: true,
                    skip_lib_check: true,
                    ..private_write_helper_options()
                },
                |_, queries| {
                    let cold = queries.cold_diagnostic_snapshot();
                    assert_eq!(queries.has_diagnostics(), !cold.is_empty());
                    assert_eq!(queries.replay_sources().unwrap(), cold);
                    assert_eq!(queries.cold_diagnostic_snapshot(), cold);
                    cold
                },
            )
            .unwrap();
            assert_eq!(snapshot.as_deref(), Some(program.diagnostics()));
            let expected = if declarations == "export {};" {
                Some(2343)
            } else if declarations.contains("d: unknown") {
                None
            } else {
                Some(2807)
            };
            assert_eq!(
                program
                    .diagnostics()
                    .iter()
                    .filter_map(|diagnostic| diagnostic.code)
                    .collect::<Vec<_>>(),
                expected.into_iter().collect::<Vec<_>>()
            );
        }
    }

    #[test]
    fn canonical_private_helper_failure_and_no_check_do_not_call_queries() {
        let declarations = "export declare function __classPrivateFieldGet(this: object, a: unknown, b: unknown, c: unknown, d: unknown): unknown;";
        for no_check in [false, true] {
            let fs = private_write_helper_files(PRIVATE_HELPER_READ_SOURCE, Some(declarations));
            fs.write_file("/project/globals.d.ts", PRIVATE_HELPER_GLOBALS)
                .unwrap();
            let mut called = false;
            let result = Program::try_new_with_canonical_checker_and_queries(
                &fs,
                "/project",
                &["globals.d.ts".to_owned(), "input.ts".to_owned()],
                CompilerOptions {
                    no_emit: true,
                    no_check,
                    skip_lib_check: true,
                    ..private_write_helper_options()
                },
                |_, _| {
                    called = true;
                },
            );
            assert!(!called);
            if no_check {
                let (program, query) = result.unwrap();
                assert!(query.is_none());
                assert!(
                    program
                        .source_file("/project/node_modules/tslib/tslib.d.ts")
                        .is_some()
                );
            } else {
                let error = result.unwrap_err();
                assert!(
                    matches!(
                        error,
                        super::CanonicalProgramCheckError::ImportHelper { .. }
                    ),
                    "{error:?}"
                );
                assert!(error.is_unsupported_boundary());
            }
        }
    }

    #[test]
    fn canonical_semantic_source_order_places_helpers_before_jsx_and_explicit_imports() {
        let fs = MemoryFileSystem::new(true);
        for (name, text) in [
            (
                "input.tsx",
                concat!(
                    "import chosen from './dependency'; export const value = chosen;\n",
                    "export const view = <div />;",
                ),
            ),
            ("dependency.ts", "export default 1;"),
            ("node_modules/tslib/index.d.ts", "export {};"),
            ("node_modules/react/jsx-runtime.d.ts", "export {};"),
        ] {
            fs.write_file(&format!("/project/{name}"), text).unwrap();
        }
        let mut program = Program::new_unchecked_with_options_and_checker(
            &fs,
            "/project",
            &["input.tsx".to_owned()],
            CompilerOptions {
                module: ModuleKind::CommonJs,
                module_resolution: ModuleResolutionKind::Node10,
                jsx: ts_options::JsxEmit::ReactJsx,
                import_helpers: true,
                es_module_interop: true,
                ..canonical_source_order_options()
            },
            super::ProgramChecker::Canonical,
        );
        program.load_remaining_program_graph(&fs);
        let semantic = program
            .canonical_semantic_sources()
            .into_iter()
            .map(|source| ts_path::base_file_name(&source.file_name))
            .collect::<Vec<_>>();
        assert_eq!(
            semantic,
            [
                "lib.es5.d.ts",
                "lib.decorators.d.ts",
                "lib.decorators.legacy.d.ts",
                "index.d.ts",
                "jsx-runtime.d.ts",
                "dependency.ts",
                "input.tsx",
            ]
        );
        let storage = program
            .source_files()
            .iter()
            .filter(|source| !source.is_default_library)
            .map(|source| ts_path::base_file_name(&source.file_name))
            .collect::<Vec<_>>();
        assert_eq!(
            storage,
            [
                "input.tsx",
                "jsx-runtime.d.ts",
                "index.d.ts",
                "dependency.ts"
            ]
        );
    }

    #[test]
    fn canonical_semantic_source_order_groups_static_and_dynamic_imports() {
        for (input, text, roots, expected) in [
            (
                "input.ts",
                concat!(
                    "/** @typedef {import('./ignored').Ignored} Ignored */\n",
                    "const early = import('./dynamic');\n",
                    "import './static';\n",
                    "type Loaded = import('./types').Item; export {};",
                ),
                vec!["input.ts", "ignored.ts"],
                vec![
                    "static.ts",
                    "dynamic.ts",
                    "types.ts",
                    "input.ts",
                    "ignored.ts",
                ],
            ),
            (
                "input.js",
                concat!(
                    "/** @typedef {import('./doc').Doc} Doc */\n",
                    "const value = require('./required');\n",
                    "import './static';",
                ),
                vec!["input.js"],
                vec!["static.ts", "doc.ts", "required.ts", "input.js"],
            ),
        ] {
            let fs = MemoryFileSystem::new(true);
            fs.write_file(&format!("/project/{input}"), text).unwrap();
            for (name, contents) in [
                ("static.ts", "export {};"),
                ("dynamic.ts", "export {};"),
                ("types.ts", "export interface Item {}"),
                ("ignored.ts", "export interface Ignored {}"),
                ("doc.ts", "export interface Doc {}"),
                ("required.ts", "export const value = 1;"),
            ] {
                fs.write_file(&format!("/project/{name}"), contents)
                    .unwrap();
            }
            let roots = roots.into_iter().map(str::to_owned).collect::<Vec<_>>();
            let mut program = Program::new_unchecked_with_options_and_checker(
                &fs,
                "/project",
                &roots,
                CompilerOptions {
                    allow_js: input == "input.js",
                    ..canonical_source_order_options()
                },
                super::ProgramChecker::Canonical,
            );
            program.load_remaining_program_graph(&fs);
            let semantic = program
                .canonical_semantic_sources()
                .into_iter()
                .map(|source| ts_path::base_file_name(&source.file_name))
                .collect::<Vec<_>>();
            let expected = [
                "lib.es5.d.ts",
                "lib.decorators.d.ts",
                "lib.decorators.legacy.d.ts",
            ]
            .into_iter()
            .chain(expected)
            .collect::<Vec<_>>();
            assert_eq!(semantic, expected, "{input}");
            assert_eq!(program.source_files()[0].id, FileId::new(0));
        }
    }

    #[test]
    fn canonical_semantic_library_order_controls_merged_declarations() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file("/project/input.d.ts", "interface Array<T> { own: T; }")
            .unwrap();
        let (program, result) = Program::try_new_with_canonical_checker_and_queries(
            &fs,
            "/project",
            &["input.d.ts".to_owned()],
            CompilerOptions {
                target: ScriptTarget::Es2015,
                skip_lib_check: true,
                ..CompilerOptions::default()
            },
            |program, queries| {
                for (name, expected) in [
                    (
                        "Date",
                        vec![
                            "lib.es5.d.ts",
                            "lib.es5.d.ts",
                            "lib.es5.d.ts",
                            "lib.scripthost.d.ts",
                            "lib.es2015.symbol.wellknown.d.ts",
                        ],
                    ),
                    (
                        "Array",
                        vec![
                            "lib.es5.d.ts",
                            "lib.es5.d.ts",
                            "lib.es2015.core.d.ts",
                            "lib.es2015.iterable.d.ts",
                            "lib.es2015.symbol.wellknown.d.ts",
                            "input.d.ts",
                        ],
                    ),
                ] {
                    let symbol = queries
                        .context
                        .store()
                        .symbol_table(queries.context.globals())
                        .unwrap()
                        .get_source(name)
                        .unwrap();
                    let declarations = queries.get_symbol_declarations(symbol).unwrap();
                    let files = declarations
                        .iter()
                        .map(|declaration| {
                            assert!(program.node(*declaration).is_some());
                            let file = program.source_file_by_id(declaration.file).unwrap();
                            ts_path::base_file_name(&file.file_name)
                        })
                        .collect::<Vec<_>>();
                    assert_eq!(files, expected, "{name}");
                }
            },
        )
        .unwrap();
        assert_eq!(result, Some(()));
        assert!(
            program.diagnostics().is_empty(),
            "{:?}",
            program.diagnostics()
        );
    }

    #[test]
    fn file_ids_are_stable_only_within_one_program_lifetime() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file("/project/first.ts", "export const first = 1;")
            .unwrap();
        fs.write_file("/project/second.ts", "export const second = 2;")
            .unwrap();
        let first_program = Program::new(
            &fs,
            "/project",
            &["first.ts".to_owned(), "second.ts".to_owned()],
        );
        let rebuilt_program = Program::new(
            &fs,
            "/project",
            &["second.ts".to_owned(), "first.ts".to_owned()],
        );

        let first_id = first_program.source_file("first.ts").unwrap().id;
        assert_eq!(first_program.source_file("first.ts").unwrap().id, first_id);
        assert_eq!(first_id, FileId::new(0));
        assert_eq!(
            rebuilt_program.source_file("first.ts").unwrap().id,
            FileId::new(1)
        );
    }

    #[test]
    fn propagates_parser_diagnostic_codes() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file("/project/main.ts", "function () { const value = ;")
            .unwrap();
        let program = Program::new(&fs, "/project", &["main.ts".to_owned()]);
        for code in [1003, 1109, 1005] {
            assert!(
                program
                    .diagnostics()
                    .iter()
                    .any(|diagnostic| diagnostic.code == Some(code)),
                "missing TS{code}: {:?}",
                program.diagnostics()
            );
        }
        assert!(
            program
                .diagnostics()
                .iter()
                .all(|diagnostic| diagnostic.category == Category::Error)
        );
    }

    #[test]
    fn suppresses_declaration_with_private_imported_expando_property_type() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/a.ts",
            "interface I {} export function f(): I { return null as I; }",
        )
        .unwrap();
        fs.write_file(
            "/project/b.ts",
            concat!(
                "import { f } from './a';\n",
                "export function q() {}\n",
                "q.val = f();",
            ),
        )
        .unwrap();
        let program = Program::new_with_options(
            &fs,
            "/project",
            &["a.ts".to_owned(), "b.ts".to_owned()],
            CompilerOptions {
                declaration: true,
                module: ModuleKind::CommonJs,
                no_lib: true,
                ..CompilerOptions::default()
            },
        );
        assert!(
            program
                .diagnostics()
                .iter()
                .any(|diagnostic| diagnostic.code == Some(4032)),
            "{:?}",
            program.diagnostics()
        );
        let emitted = program.emit();
        assert!(
            emitted
                .files
                .iter()
                .any(|file| file.file_name.ends_with("a.d.ts")),
            "{:?}",
            emitted.files
        );
        assert!(
            !emitted
                .files
                .iter()
                .any(|file| file.file_name.ends_with("b.d.ts")),
            "{:?}",
            emitted.files
        );
    }

    #[test]
    fn strip_internal_omits_annotated_declarations_only_from_declaration_emit() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/main.ts",
            concat!(
                "/** @internal */ class Hidden {}\n",
                "class Visible {\n",
                "  foo(): void {}\n",
                "  // @internal\n",
                "  bar(): void {}\n",
                "}\n",
            ),
        )
        .unwrap();
        let program = Program::new_with_options(
            &fs,
            "/project",
            &["main.ts".to_owned()],
            CompilerOptions {
                declaration: true,
                no_lib: true,
                strip_internal: true,
                target: ScriptTarget::Es2015,
                ..CompilerOptions::default()
            },
        );
        let emitted = program.emit();
        let javascript = emitted
            .files
            .iter()
            .find(|file| file.file_name == "/project/main.js")
            .unwrap();
        assert!(
            javascript.text.contains("class Hidden"),
            "{}",
            javascript.text
        );
        assert!(javascript.text.contains("bar()"), "{}", javascript.text);
        let declaration = emitted
            .files
            .iter()
            .find(|file| file.file_name == "/project/main.d.ts")
            .unwrap();
        assert_eq!(
            declaration.text,
            "declare class Visible {\n    foo(): void;\n}\n"
        );
    }

    #[test]
    fn constructs_roots_from_config_files() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/tsconfig.json",
            "{ \"files\": [\"src/a.ts\", \"src/b.ts\"], \"compilerOptions\": { \"noLib\": true } }",
        )
        .unwrap();
        fs.write_file("/project/src/a.ts", "let a = 1;").unwrap();
        fs.write_file("/project/src/b.ts", "let b = 2;").unwrap();
        let program = Program::from_config(&fs, "/project/tsconfig.json");
        assert_eq!(
            program
                .source_files()
                .iter()
                .filter(|file| !file.is_default_library)
                .count(),
            2
        );
        assert!(program.diagnostics().is_empty());
    }

    #[test]
    fn loads_explicit_and_automatic_type_directives() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file("/project/main.ts", "ENV_GLOBAL; AUTO_GLOBAL;")
            .unwrap();
        fs.write_file(
            "/project/types/env/index.d.ts",
            "declare const ENV_GLOBAL: string;",
        )
        .unwrap();
        fs.write_file(
            "/project/node_modules/@types/auto/index.d.ts",
            "declare const AUTO_GLOBAL: number;",
        )
        .unwrap();
        fs.write_file(
            "/project/tsconfig.json",
            r#"{
                "files": ["main.ts"],
                "compilerOptions": {
                    "noLib": true,
                    "typeRoots": ["types", "node_modules/@types"],
                    "types": ["env", "auto", "missing"]
                }
            }"#,
        )
        .unwrap();
        let program = Program::from_config(&fs, "/project/tsconfig.json");
        assert!(
            program
                .source_file("/project/types/env/index.d.ts")
                .is_some()
        );
        assert!(
            program
                .source_file("/project/node_modules/@types/auto/index.d.ts")
                .is_some()
        );
        let [diagnostic] = program.diagnostics() else {
            panic!(
                "expected one missing explicit type: {:?}",
                program.diagnostics()
            );
        };
        assert_eq!(diagnostic.code, Some(2688));
        assert_eq!(diagnostic.file_name, None);
        assert_eq!(diagnostic.range, None);

        fs.write_file(
            "/project/automatic.json",
            r#"{"files":["main.ts"],"compilerOptions":{"noLib":true}}"#,
        )
        .unwrap();
        let automatic = Program::from_config(&fs, "/project/automatic.json");
        assert!(
            automatic
                .source_file("/project/node_modules/@types/auto/index.d.ts")
                .is_some()
        );
    }

    #[test]
    fn missing_triple_slash_type_reference_reports_exact_value_range() {
        let fs = MemoryFileSystem::new(true);
        let source = concat!(
            "/// <reference types=\"cookie-session\"/>\n",
            "declare const foo: number;\n",
        );
        fs.write_file("/project/types.d.ts", source).unwrap();

        let program = Program::new_with_options(
            &fs,
            "/project",
            &["types.d.ts".to_owned()],
            CompilerOptions {
                no_lib: true,
                ..CompilerOptions::default()
            },
        );

        let [diagnostic] = program.diagnostics() else {
            panic!(
                "expected one missing triple-slash type: {:?}",
                program.diagnostics()
            );
        };
        assert_eq!(diagnostic.code, Some(2688));
        assert_eq!(diagnostic.file_name.as_deref(), Some("/project/types.d.ts"));
        assert_eq!(
            diagnostic.range,
            Some(TextRange::new(TextPos::new(22), TextPos::new(36)))
        );
        assert_eq!(
            diagnostic.message,
            "Cannot find type definition file for 'cookie-session'."
        );
    }

    #[test]
    fn missing_triple_slash_type_reference_keeps_multiline_attribute_offsets() {
        let fs = MemoryFileSystem::new(true);
        let source = concat!(
            "// leading comment\r\n",
            "  /// <reference preserve='true' types = 'cookie-session' />\r\n",
            "declare const foo: number;\n",
        );
        fs.write_file("/project/types.d.ts", source).unwrap();

        let program = Program::new_with_options(
            &fs,
            "/project",
            &["types.d.ts".to_owned()],
            CompilerOptions {
                no_lib: true,
                ..CompilerOptions::default()
            },
        );

        let [diagnostic] = program.diagnostics() else {
            panic!(
                "expected one missing triple-slash type: {:?}",
                program.diagnostics()
            );
        };
        let range = diagnostic.range.expect("missing reference value range");
        assert_eq!(
            &source[range.start.get() as usize..range.end.get() as usize],
            "cookie-session"
        );
        assert_eq!(
            range.start.get() as usize,
            source.find("cookie-session").unwrap()
        );
    }

    #[test]
    fn preceding_ts_ignore_suppresses_missing_triple_slash_type_reference() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/types.d.ts",
            concat!(
                "// @ts-ignore\n",
                "/// <reference types=\"cookie-session\"/>\n",
                "declare const foo: number;\n",
            ),
        )
        .unwrap();

        let program = Program::new_with_options(
            &fs,
            "/project",
            &["types.d.ts".to_owned()],
            CompilerOptions {
                no_lib: true,
                ..CompilerOptions::default()
            },
        );

        assert!(
            program.diagnostics().is_empty(),
            "{:?}",
            program.diagnostics()
        );
    }

    #[test]
    fn no_resolve_skips_missing_path_and_type_reference_diagnostics() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/main.ts",
            concat!(
                "/// <reference path='./missing.ts' />\n",
                "/// <reference types='missing-types' />\n",
                "const value: number = 1;\n",
            ),
        )
        .unwrap();

        for no_resolve in [false, true] {
            let program = Program::new_with_options(
                &fs,
                "/project",
                &["main.ts".to_owned()],
                CompilerOptions {
                    no_lib: true,
                    no_resolve,
                    ..CompilerOptions::default()
                },
            );
            let codes = program
                .diagnostics()
                .iter()
                .filter_map(|diagnostic| diagnostic.code)
                .collect::<Vec<_>>();
            let expected = if no_resolve {
                Vec::new()
            } else {
                vec![6053, 2688]
            };
            assert_eq!(codes, expected, "noResolve={no_resolve}");
        }
    }

    #[test]
    fn no_resolve_preserves_explicit_library_references() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/main.ts",
            "/// <reference lib='es2015.promise' />\nconst value: number = 1;\n",
        )
        .unwrap();

        let program = Program::new_with_options(
            &fs,
            "/project",
            &["main.ts".to_owned()],
            CompilerOptions {
                lib: Some(Vec::new()),
                no_resolve: true,
                ..CompilerOptions::default()
            },
        );

        assert!(
            program.diagnostics().is_empty(),
            "{:?}",
            program.diagnostics()
        );
        assert!(
            program
                .source_file("/__typescript/lib/lib.es2015.promise.d.ts")
                .is_some()
        );
    }

    #[test]
    fn follows_triple_slash_path_type_and_lib_references() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/main.ts",
            concat!(
                "/// <reference path='./globals.d.ts' />\n",
                "/// <reference path='./extensionless' />\n",
                "/// <reference types=\"pkg\" />\n",
                "/// <reference lib='es2015.promise' />\n",
                "GLOBAL; NESTED; EXTENSIONLESS; PACKAGE_GLOBAL; Promise;\n",
            ),
        )
        .unwrap();
        fs.write_file(
            "/project/globals.d.ts",
            "/// <reference path='./nested.d.ts' />\ndeclare const GLOBAL: string;",
        )
        .unwrap();
        fs.write_file("/project/nested.d.ts", "declare const NESTED: number;")
            .unwrap();
        fs.write_file(
            "/project/extensionless.ts",
            "declare const EXTENSIONLESS: symbol;",
        )
        .unwrap();
        fs.write_file(
            "/project/node_modules/@types/pkg/index.d.ts",
            "declare const PACKAGE_GLOBAL: boolean;",
        )
        .unwrap();
        let program = Program::new_with_options(
            &fs,
            "/project",
            &["main.ts".to_owned()],
            CompilerOptions {
                lib: Some(Vec::new()),
                ..CompilerOptions::default()
            },
        );
        assert!(
            program.diagnostics().is_empty(),
            "{:?}",
            program.diagnostics()
        );
        for file in [
            "/project/globals.d.ts",
            "/project/nested.d.ts",
            "/project/extensionless.ts",
            "/project/node_modules/@types/pkg/index.d.ts",
            "/__typescript/lib/lib.es2015.promise.d.ts",
        ] {
            assert!(program.source_file(file).is_some(), "missing {file}");
        }

        fs.write_file(
            "/project/no-default.ts",
            "/// <reference no-default-lib='true' />\nArray;",
        )
        .unwrap();
        let no_default = Program::new_with_options(
            &fs,
            "/project",
            &["no-default.ts".to_owned()],
            CompilerOptions::default(),
        );
        assert!(!no_default.options().no_lib);
        assert!(
            no_default
                .source_file("/__typescript/lib/lib.d.ts")
                .is_some()
        );
        assert!(
            no_default.diagnostics().is_empty(),
            "{:?}",
            no_default.diagnostics()
        );
    }

    #[test]
    fn emits_path_references_discovered_through_imported_modules() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file("/project/ref.ts", "var x = 1;").unwrap();
        fs.write_file(
            "/project/a.ts",
            "/// <reference path=\"ref.ts\"/>\nexport var y;",
        )
        .unwrap();
        fs.write_file("/project/b.ts", "import y = require(\"./a\");")
            .unwrap();
        let program = Program::new_with_options(
            &fs,
            "/project",
            &["b.ts".to_owned()],
            CompilerOptions {
                module: ModuleKind::CommonJs,
                no_lib: true,
                ..CompilerOptions::default()
            },
        );
        assert!(
            program.diagnostics().is_empty(),
            "{:?}",
            program.diagnostics()
        );
        let emitted = program.emit();
        assert!(
            emitted
                .files
                .iter()
                .any(|file| file.file_name == "/project/ref.js"),
            "{:?}",
            emitted.files
        );
    }

    #[test]
    fn preserves_resolved_script_path_references_with_commonjs_output() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/node.d.ts",
            "declare function require(moduleName: string): any;",
        )
        .unwrap();
        fs.write_file(
            "/project/ns.ts",
            concat!(
                "/// <reference path=\"node.d.ts\"/>\n",
                "namespace myAssert { export type cool = 'cool'; }\n",
                "var myAssert = require('assert');\n",
            ),
        )
        .unwrap();
        let program = Program::new_with_options(
            &fs,
            "/project",
            &["ns.ts".to_owned()],
            CompilerOptions {
                module: ModuleKind::CommonJs,
                target: ScriptTarget::Es2015,
                no_lib: true,
                ..CompilerOptions::default()
            },
        );
        let output = program.emit();
        let javascript = output
            .files
            .iter()
            .find(|file| file.file_name == "/project/ns.js")
            .unwrap();
        assert_eq!(
            javascript.text,
            concat!(
                "\"use strict\";\n",
                "/// <reference path=\"node.d.ts\"/>\n",
                "var myAssert = require('assert');\n",
            )
        );

        fs.write_file("/project/dep.ts", "export namespace M { }")
            .unwrap();
        fs.write_file(
            "/project/external.ts",
            concat!(
                "/// <reference path='dep.ts'/>\n",
                "declare namespace bar { interface alpha { } }\n",
                "import f = require('./dep');\n",
                "namespace bar { var x: alpha; }\n",
            ),
        )
        .unwrap();
        let external = Program::new_with_options(
            &fs,
            "/project",
            &["external.ts".to_owned()],
            CompilerOptions {
                module: ModuleKind::CommonJs,
                target: ScriptTarget::Es2015,
                no_lib: true,
                ..CompilerOptions::default()
            },
        )
        .emit();
        let javascript = external
            .files
            .iter()
            .find(|file| file.file_name == "/project/external.js")
            .unwrap();
        let marker = javascript.text.find("Object.defineProperty").unwrap();
        let reference = javascript
            .text
            .find("/// <reference path='dep.ts'/>")
            .unwrap();
        let namespace = javascript.text.find("var bar;").unwrap();
        assert!(
            marker < reference && reference < namespace,
            "{}",
            javascript.text
        );
    }

    #[test]
    fn drops_resolved_path_reference_owned_by_erased_import_equals() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/decls.ts",
            concat!(
                "declare module 'equ' { export class C {} }\n",
                "declare module 'equ2' { export var x: number; }\n",
            ),
        )
        .unwrap();
        fs.write_file(
            "/project/consumer.ts",
            concat!(
                "/// <reference path=\"decls.ts\" />\n",
                "import imp1 = require('equ');\n",
                "\n",
                "// Ambient external module members are always exported\n",
                "import imp3 = require('equ2');\n",
                "var n = imp3.x;\n",
            ),
        )
        .unwrap();
        let emitted = Program::new_with_options(
            &fs,
            "/project",
            &["consumer.ts".to_owned()],
            CompilerOptions {
                module: ModuleKind::CommonJs,
                target: ScriptTarget::Es2015,
                no_lib: true,
                ..CompilerOptions::default()
            },
        )
        .emit();
        assert!(emitted.diagnostics.is_empty(), "{:?}", emitted.diagnostics);
        let javascript = emitted
            .files
            .iter()
            .find(|file| file.file_name == "/project/consumer.js")
            .unwrap();
        assert!(
            !javascript.text.contains("<reference"),
            "{}",
            javascript.text
        );
        assert!(
            javascript
                .text
                .contains("// Ambient external module members are always exported\nconst imp3 = require(\"equ2\");"),
            "{}",
            javascript.text
        );
    }

    #[test]
    fn emits_shebang_before_generated_prologues_and_references() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/types.d.ts",
            "declare module 'pkg' { export const value: number; }",
        )
        .unwrap();
        fs.write_file(
            "/project/main.ts",
            concat!(
                "#!/usr/bin/env node\n\n",
                "/// <reference path=\"types.d.ts\"/>\n\n",
                "import { value } from 'pkg';\n",
                "use(value);\n",
            ),
        )
        .unwrap();
        let emitted = Program::new_with_options(
            &fs,
            "/project",
            &["main.ts".to_owned()],
            CompilerOptions {
                module: ModuleKind::CommonJs,
                no_lib: true,
                target: ScriptTarget::Es2015,
                ..CompilerOptions::default()
            },
        )
        .emit();
        let javascript = emitted
            .files
            .iter()
            .find(|file| file.file_name == "/project/main.js")
            .unwrap();
        assert!(
            javascript.text.starts_with(concat!(
                "#!/usr/bin/env node\n",
                "\"use strict\";\n",
                "/// <reference path=\"types.d.ts\"/>\n",
                "Object.defineProperty(exports, \"__esModule\", { value: true });\n",
            )),
            "{}",
            javascript.text
        );

        fs.write_file("/project/invalid.ts", "var value = 1;\n#!/usr/bin/env node")
            .unwrap();
        let invalid = Program::new_with_options(
            &fs,
            "/project",
            &["invalid.ts".to_owned()],
            CompilerOptions {
                no_lib: true,
                target: ScriptTarget::Es2015,
                ..CompilerOptions::default()
            },
        )
        .emit();
        assert!(!invalid.files[0].text.starts_with("#!"));
    }

    #[test]
    fn declaration_emit_preserves_non_nullable_generic_logical_or_return() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/main.ts",
            concat!(
                "function fail(): never { throw new Error(); }\n",
                "function value<T>(input: T) { return input || fail(); }",
            ),
        )
        .unwrap();
        let program = Program::new_with_options(
            &fs,
            "/project",
            &["main.ts".to_owned()],
            CompilerOptions {
                declaration: true,
                strict: true,
                ..CompilerOptions::default()
            },
        );
        assert!(
            program.diagnostics().is_empty(),
            "{:?}",
            program.diagnostics()
        );
        let emitted = program.emit();
        let declaration = emitted
            .files
            .iter()
            .find(|file| file.file_name == "/project/main.d.ts")
            .expect("declaration output");
        assert!(
            declaration
                .text
                .contains("function value<T>(input: T): NonNullable<T>;"),
            "{}",
            declaration.text
        );
    }

    #[test]
    fn preserved_declaration_references_are_canonical_and_target_declarations() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file("/project/dep.ts", "export interface Dep {}")
            .unwrap();
        fs.write_file(
            "/project/node_modules/@types/pkg/index.d.ts",
            "declare interface PackageType {}",
        )
        .unwrap();
        fs.write_file(
            "/project/main.ts",
            concat!(
                "///<reference path='dep.ts' preserve=\"true\" />\n",
                "///<reference types='pkg' preserve=\"true\" />\n",
                "export const value = 1;",
            ),
        )
        .unwrap();
        let program = Program::new_with_options(
            &fs,
            "/project",
            &["main.ts".to_owned()],
            CompilerOptions {
                declaration: true,
                no_lib: true,
                ..CompilerOptions::default()
            },
        );
        let emitted = program.emit();
        assert!(emitted.diagnostics.is_empty(), "{:?}", emitted.diagnostics);
        let declaration = emitted
            .files
            .iter()
            .find(|file| file.file_name == "/project/main.d.ts")
            .unwrap();
        assert!(
            declaration.text.starts_with(concat!(
                "/// <reference path=\"dep.d.ts\" preserve=\"true\" />\n",
                "/// <reference types=\"pkg\" preserve=\"true\" />\n",
            )),
            "{}",
            declaration.text
        );
    }

    #[test]
    fn declarations_use_named_classes_from_erroneous_ambient_inputs() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/declFile.d.ts",
            concat!(
                "declare namespace M {\n",
                "    declare var x;\n",
                "    declare function f();\n",
                "    declare namespace N {}\n",
                "    declare class C {}\n",
                "}\n",
            ),
        )
        .unwrap();
        fs.write_file(
            "/project/client.ts",
            concat!(
                "///<reference path=\"declFile.d.ts\" preserve=\"true\"/>\n",
                "var value = new M.C();\n",
            ),
        )
        .unwrap();
        let program = Program::new_with_options(
            &fs,
            "/project",
            &["client.ts".to_owned()],
            CompilerOptions {
                declaration: true,
                no_lib: true,
                target: ScriptTarget::Es2015,
                ..CompilerOptions::default()
            },
        );
        assert!(
            program
                .diagnostics()
                .iter()
                .any(|diagnostic| diagnostic.code == Some(1038)),
            "{:?}",
            program.diagnostics()
        );
        let emitted = program.emit();
        let declaration = emitted
            .files
            .iter()
            .find(|file| file.file_name == "/project/client.d.ts")
            .unwrap();
        assert!(
            declaration.text.contains("declare var value: M.C;"),
            "{}",
            declaration.text
        );
    }

    #[test]
    fn declaration_emit_recovers_inferred_class_method_signatures() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/input.ts",
            concat!(
                "interface Example {}\n",
                "class Example {\n",
                "    f() { return ''; }\n",
                "    h(x = 4, nullable = null, label = '') {}\n",
                "}\n",
            ),
        )
        .unwrap();
        let program = Program::new_with_options(
            &fs,
            "/project",
            &["input.ts".to_owned()],
            CompilerOptions {
                declaration: true,
                no_lib: true,
                strict: false,
                target: ScriptTarget::Es2015,
                ..CompilerOptions::default()
            },
        );
        let emitted = program.emit();
        assert!(emitted.diagnostics.is_empty(), "{:?}", emitted.diagnostics);
        let declaration = emitted
            .files
            .iter()
            .find(|file| file.file_name == "/project/input.d.ts")
            .unwrap();
        assert!(
            declaration.text.contains("f(): string;"),
            "{}",
            declaration.text
        );
        assert!(
            declaration
                .text
                .contains("h(x?: number, nullable?: any, label?: string): void;"),
            "{}",
            declaration.text
        );
    }

    #[test]
    fn bundled_declarations_preserve_deduplicated_references_without_declaration_inputs() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/declFile.d.ts",
            concat!(
                "declare namespace M {\n",
                "    declare var x;\n",
                "    declare function f();\n",
                "    declare namespace N {}\n",
                "    declare class C {}\n",
                "}\n",
            ),
        )
        .unwrap();
        for file in ["client.ts", "other.ts"] {
            fs.write_file(
                &format!("/project/{file}"),
                concat!(
                    "///<reference path=\"declFile.d.ts\" preserve=\"true\"/>\n",
                    "var value = new M.C();\n",
                ),
            )
            .unwrap();
        }
        let program = Program::new_with_options(
            &fs,
            "/project",
            &[
                "declFile.d.ts".to_owned(),
                "client.ts".to_owned(),
                "other.ts".to_owned(),
            ],
            CompilerOptions {
                declaration: true,
                out_file: Some("out.js".into()),
                no_lib: true,
                target: ScriptTarget::Es2015,
                ..CompilerOptions::default()
            },
        );
        assert!(
            program
                .diagnostics()
                .iter()
                .any(|diagnostic| diagnostic.code == Some(1038)),
            "{:?}",
            program.diagnostics()
        );
        let emitted = program.emit();
        let declaration = emitted
            .files
            .iter()
            .find(|file| file.file_name == "/project/out.d.ts")
            .unwrap();
        let directive = "/// <reference path=\"declFile.d.ts\" preserve=\"true\" />";
        assert_eq!(declaration.text.matches(directive).count(), 1);
        assert!(declaration.text.starts_with(directive));
        assert!(
            declaration.text.contains("declare var value: M.C;"),
            "{}",
            declaration.text
        );
        assert!(!declaration.text.contains("declare namespace M"));
    }

    #[test]
    fn discovers_config_include_patterns() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/tsconfig.json",
            "{ \"include\": [\"src/**/*.ts\"], \"exclude\": [\"src/generated\"], \"compilerOptions\": { \"noLib\": true } }",
        )
        .unwrap();
        fs.write_file("/project/src/a.ts", "let a = 1;").unwrap();
        fs.write_file("/project/src/nested/b.ts", "let b = 2;")
            .unwrap();
        fs.write_file("/project/src/generated/c.ts", "let c = 3;")
            .unwrap();
        let program = Program::from_config(&fs, "/project/tsconfig.json");
        assert_eq!(
            program
                .source_files()
                .iter()
                .filter(|file| !file.is_default_library)
                .count(),
            2
        );
        assert!(program.diagnostics().is_empty());
    }

    #[test]
    fn resolves_inherited_options_and_base_relative_globs() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/repo/base/tsconfig.json",
            r#"{
                "include": ["src/**/*.ts"],
                "exclude": ["src/generated"],
                "compilerOptions": { "target": "es2015", "noLib": true }
            }"#,
        )
        .unwrap();
        fs.write_file(
            "/repo/app/tsconfig.json",
            r#"{"extends":"../base/tsconfig.json"}"#,
        )
        .unwrap();
        fs.write_file("/repo/base/src/a.ts", "const a = 1;")
            .unwrap();
        fs.write_file("/repo/base/src/nested/b.ts", "const b = 2;")
            .unwrap();
        fs.write_file("/repo/base/src/generated/skip.ts", "const skip = 3;")
            .unwrap();
        fs.write_file("/repo/app/unrelated.ts", "const unrelated = 4;")
            .unwrap();

        let program = Program::from_config(&fs, "/repo/app/tsconfig.json");
        assert!(
            program.diagnostics().is_empty(),
            "{:?}",
            program.diagnostics()
        );
        assert_eq!(program.options().target, ts_options::ScriptTarget::Es2015);
        assert_eq!(
            program
                .source_files()
                .iter()
                .filter(|file| !file.is_default_library)
                .count(),
            2
        );
        assert!(program.source_file("/repo/base/src/a.ts").is_some());
        assert!(program.source_file("/repo/base/src/nested/b.ts").is_some());
        assert!(
            program
                .source_file("/repo/base/src/generated/skip.ts")
                .is_none()
        );
        assert!(program.source_file("/repo/app/unrelated.ts").is_none());
    }

    #[test]
    fn retains_parser_diagnostics_with_file_ranges() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file("/bad.ts", "const value: = ;").unwrap();
        let program = Program::new(&fs, "/", &["bad.ts".to_owned()]);
        assert!(!program.diagnostics().is_empty());
        assert_eq!(
            program.diagnostics()[0].file_name.as_deref(),
            Some("/bad.ts")
        );
        assert!(program.diagnostics()[0].range.is_some());
    }

    #[test]
    fn emits_recovered_class_statements_and_erases_keyword_named_interfaces() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/class.ts",
            "class C { public const var export foo = 10; var constructor() { } }",
        )
        .unwrap();
        fs.write_file("/interface.ts", "interface string {}")
            .unwrap();
        let options = CompilerOptions {
            no_lib: true,
            target: ScriptTarget::Es2015,
            ..CompilerOptions::default()
        };

        let class_program =
            Program::new_with_options(&fs, "/", &["class.ts".to_owned()], options.clone());
        let class_output = class_program.emit();
        assert!(
            class_output.diagnostics.is_empty(),
            "{:?}",
            class_output.diagnostics
        );
        assert_eq!(class_output.files.len(), 1);
        assert!(class_output.files[0].text.contains("var constructor;"));
        assert!(class_output.files[0].text.contains("() => { };"));

        let interface_program =
            Program::new_with_options(&fs, "/", &["interface.ts".to_owned()], options);
        let interface_output = interface_program.emit();
        assert!(
            interface_output.diagnostics.is_empty(),
            "{:?}",
            interface_output.diagnostics
        );
        assert_eq!(interface_output.files.len(), 1);
        assert_eq!(interface_output.files[0].text, "\"use strict\";\n");
        assert_eq!(
            interface_program
                .diagnostics()
                .iter()
                .filter_map(|diagnostic| diagnostic.code)
                .collect::<Vec<_>>(),
            [2427]
        );
    }

    #[test]
    fn reports_missing_function_implementations_without_rejecting_ambient_declarations() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/main.ts",
            r"
                namespace M { function foo(); }
                function valid(value: string): string;
                function valid(value: string): string { return value; }
            ",
        )
        .unwrap();
        fs.write_file(
            "/project/tsconfig.json",
            r#"{
                "files": ["main.ts"],
                "compilerOptions": {
                    "noLib": true,
                    "noEmit": true,
                    "noImplicitAny": true
                }
            }"#,
        )
        .unwrap();
        let program = Program::from_config(&fs, "/project/tsconfig.json");
        assert_eq!(
            program
                .diagnostics()
                .iter()
                .filter_map(|diagnostic| diagnostic.code)
                .collect::<Vec<_>>(),
            [2391, 7010]
        );

        fs.write_file(
            "/project/ambient.d.ts",
            "function fromDeclarationFile(); declare function explicitlyAmbient();",
        )
        .unwrap();
        let ambient = Program::new_with_options(
            &fs,
            "/project",
            &["ambient.d.ts".to_owned()],
            CompilerOptions {
                no_lib: true,
                no_emit: true,
                ..CompilerOptions::default()
            },
        );
        // No TS2391 for ambient declarations; the missing modifier reports
        // TS1046 and default-on noImplicitAny reports implicit-any returns
        // (oracle-verified).
        assert_eq!(
            ambient
                .diagnostics()
                .iter()
                .filter_map(|diagnostic| diagnostic.code)
                .collect::<Vec<_>>(),
            [1046, 7010, 7010]
        );
    }

    #[test]
    fn accepts_dotted_ambient_namespace_declarations() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/main.ts",
            "declare namespace Foo.Bar { export var foo; }; Foo.Bar.foo = 5;",
        )
        .unwrap();
        let program = Program::new_with_options(
            &fs,
            "/project",
            &["main.ts".to_owned()],
            CompilerOptions {
                no_lib: true,
                no_emit: true,
                target: ScriptTarget::Es2015,
                ..CompilerOptions::default()
            },
        );
        assert!(
            program.diagnostics().is_empty(),
            "{:?}",
            program.diagnostics()
        );
    }

    #[test]
    fn binds_files_and_reports_duplicate_block_declarations() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file("/duplicate.ts", "let value = 1; let value = 2;")
            .unwrap();
        let program = Program::new(&fs, "/", &["duplicate.ts".to_owned()]);
        assert_eq!(program.source_files()[0].binding.symbols.len(), 1);
        assert!(
            program
                .diagnostics()
                .iter()
                .any(|diagnostic| diagnostic.code == Some(2451))
        );
    }

    #[test]
    fn ambient_external_modules_do_not_conflict_with_global_block_variables() {
        for module in [ModuleKind::CommonJs, ModuleKind::Preserve] {
            let fs = MemoryFileSystem::new(true);
            fs.write_file(
                "/project/node.d.ts",
                r#"
                    declare function require(moduleName: string): any;
                    declare module "fs" {
                        export function readFileSync(path: string): string;
                    }
                "#,
            )
            .unwrap();
            fs.write_file(
                "/project/app.js",
                r#"const fs = require("fs"); fs.readFileSync("/a/b/c");"#,
            )
            .unwrap();
            let program = Program::new_with_options(
                &fs,
                "/project",
                &["node.d.ts".to_owned(), "app.js".to_owned()],
                CompilerOptions {
                    allow_js: true,
                    module,
                    no_lib: true,
                    ..CompilerOptions::default()
                },
            );
            assert!(
                !program
                    .diagnostics()
                    .iter()
                    .any(|diagnostic| diagnostic.code == Some(2451)),
                "{module:?}: {:?}",
                program.diagnostics()
            );
        }

        let fs = MemoryFileSystem::new(true);
        fs.write_file("/project/first.ts", "const collision = 1;")
            .unwrap();
        fs.write_file("/project/second.ts", "const collision = 2;")
            .unwrap();
        let program = Program::new_with_options(
            &fs,
            "/project",
            &["first.ts".to_owned(), "second.ts".to_owned()],
            CompilerOptions {
                no_lib: true,
                ..CompilerOptions::default()
            },
        );
        assert!(
            program
                .diagnostics()
                .iter()
                .any(|diagnostic| diagnostic.code == Some(2451)),
            "{:?}",
            program.diagnostics()
        );
    }

    #[test]
    fn follows_relative_imports_and_reports_unresolved_modules() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/main.ts",
            "import { value } from './dep.js'; import { missing } from './missing'; value; missing;",
        )
        .unwrap();
        fs.write_file("/project/dep.ts", "export const value = 1;")
            .unwrap();
        let program = Program::new_with_module_resolution(
            &fs,
            "/project",
            &["main.ts".to_owned()],
            ts_module::ResolutionOptions::default(),
        );
        assert_eq!(program.source_files().len(), 2);
        assert!(program.source_file("/project/dep.ts").is_some());
        assert!(
            program
                .diagnostics()
                .iter()
                .any(|diagnostic| diagnostic.code == Some(2307))
        );
    }

    #[test]
    fn checks_unresolved_side_effect_imports_by_default_unless_explicitly_disabled() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/main.ts",
            "import './side-effect'; import { value } from './binding'; value;",
        )
        .unwrap();
        let defaults = Program::new_with_options(
            &fs,
            "/project",
            &["main.ts".to_owned()],
            CompilerOptions {
                no_lib: true,
                ..CompilerOptions::default()
            },
        );
        assert_eq!(
            defaults
                .diagnostics()
                .iter()
                .filter_map(|diagnostic| diagnostic.code)
                .collect::<Vec<_>>(),
            [2882, 2307]
        );

        let unchecked = Program::new_with_options(
            &fs,
            "/project",
            &["main.ts".to_owned()],
            CompilerOptions {
                no_lib: true,
                no_unchecked_side_effect_imports: false,
                no_unchecked_side_effect_imports_specified: true,
                ..CompilerOptions::default()
            },
        );
        assert_eq!(
            unchecked
                .diagnostics()
                .iter()
                .filter_map(|diagnostic| diagnostic.code)
                .collect::<Vec<_>>(),
            [2307]
        );

        let checked = Program::new_with_options(
            &fs,
            "/project",
            &["main.ts".to_owned()],
            CompilerOptions {
                no_lib: true,
                no_unchecked_side_effect_imports: true,
                no_unchecked_side_effect_imports_specified: true,
                ..CompilerOptions::default()
            },
        );
        assert_eq!(
            checked
                .diagnostics()
                .iter()
                .filter_map(|diagnostic| diagnostic.code)
                .collect::<Vec<_>>(),
            [2882, 2307]
        );
    }

    #[test]
    fn skip_lib_check_suppresses_only_unresolved_declaration_file_imports() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/main.ts",
            "import './types'; import { missing } from './missing-user'; missing;",
        )
        .unwrap();
        fs.write_file(
            "/project/types.d.ts",
            concat!(
                "import './missing-side-effect';\n",
                "import { Missing } from './missing-binding';\n",
                "import { Present } from './present';\n",
                "export { Missing, Present };\n",
            ),
        )
        .unwrap();
        fs.write_file(
            "/project/present.d.ts",
            "export interface Present { value: number; }",
        )
        .unwrap();

        let checked = Program::new_with_options(
            &fs,
            "/project",
            &["main.ts".to_owned()],
            CompilerOptions {
                no_lib: true,
                no_unchecked_side_effect_imports: true,
                no_unchecked_side_effect_imports_specified: true,
                ..CompilerOptions::default()
            },
        );
        assert_eq!(
            checked
                .diagnostics()
                .iter()
                .filter(|diagnostic| matches!(diagnostic.code, Some(2307 | 2882)))
                .map(|diagnostic| (diagnostic.file_name.as_deref(), diagnostic.code))
                .collect::<Vec<_>>(),
            [
                (Some("/project/main.ts"), Some(2307)),
                (Some("/project/types.d.ts"), Some(2882)),
                (Some("/project/types.d.ts"), Some(2307)),
            ]
        );
        assert!(checked.source_file("/project/present.d.ts").is_some());

        let skipped = Program::new_with_options(
            &fs,
            "/project",
            &["main.ts".to_owned()],
            CompilerOptions {
                no_lib: true,
                no_unchecked_side_effect_imports: true,
                no_unchecked_side_effect_imports_specified: true,
                skip_lib_check: true,
                ..CompilerOptions::default()
            },
        );
        assert_eq!(
            skipped
                .diagnostics()
                .iter()
                .filter(|diagnostic| matches!(diagnostic.code, Some(2307 | 2882)))
                .map(|diagnostic| (diagnostic.file_name.as_deref(), diagnostic.code))
                .collect::<Vec<_>>(),
            [(Some("/project/main.ts"), Some(2307))]
        );
        assert!(skipped.source_file("/project/present.d.ts").is_some());
    }

    #[test]
    fn skip_lib_check_suppresses_rooted_declaration_type_reference_diagnostics() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/types.d.ts",
            concat!(
                "/// <reference types=\"missing-types\" />\n",
                "import { Missing } from './missing-binding';\n",
                "export { Missing };\n",
            ),
        )
        .unwrap();

        let program = Program::new_with_options(
            &fs,
            "/project",
            &["types.d.ts".to_owned()],
            CompilerOptions {
                no_lib: true,
                skip_lib_check: true,
                ..CompilerOptions::default()
            },
        );
        assert!(
            program.diagnostics().is_empty(),
            "{:?}",
            program.diagnostics()
        );
    }

    #[test]
    fn skip_lib_check_preserves_type_references_in_typescript_sources() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/input.ts",
            "/// <reference types=\"missing-types\" />\nexport {};\n",
        )
        .unwrap();
        let program = Program::new_with_options(
            &fs,
            "/project",
            &["input.ts".to_owned()],
            CompilerOptions {
                no_lib: true,
                skip_lib_check: true,
                ..CompilerOptions::default()
            },
        );
        let [diagnostic] = program.diagnostics() else {
            panic!("{:?}", program.diagnostics());
        };
        assert_eq!(diagnostic.code, Some(2688));
        assert_eq!(diagnostic.file_name.as_deref(), Some("/project/input.ts"));
    }

    #[test]
    fn skip_lib_check_preserves_global_missing_type_directive_diagnostics() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file("/project/types.d.ts", "export {};\n")
            .unwrap();
        let program = Program::new_with_options(
            &fs,
            "/project",
            &["types.d.ts".to_owned()],
            CompilerOptions {
                no_lib: true,
                skip_lib_check: true,
                types: Some(vec!["missing-types".to_owned()]),
                ..CompilerOptions::default()
            },
        );
        let [diagnostic] = program.diagnostics() else {
            panic!("{:?}", program.diagnostics());
        };
        assert_eq!(diagnostic.code, Some(2688));
        assert_eq!(diagnostic.file_name, None);
        assert_eq!(diagnostic.range, None);
    }

    #[test]
    fn resolves_external_import_equals_module_references() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/main.ts",
            concat!(
                "import present = require('./dep');\n",
                "import nested = present.value;\n",
                "import missing = require('./missing');\n",
                "present.value; nested; missing;\n",
            ),
        )
        .unwrap();
        fs.write_file("/project/dep.ts", "export const value = 1;")
            .unwrap();

        let program = Program::new_with_module_resolution(
            &fs,
            "/project",
            &["main.ts".to_owned()],
            ts_module::ResolutionOptions::default(),
        );
        assert!(program.source_file("/project/dep.ts").is_some());
        assert_eq!(
            program
                .diagnostics()
                .iter()
                .filter(|diagnostic| diagnostic.code == Some(2307))
                .count(),
            1
        );
    }

    #[test]
    fn resolves_import_equals_against_top_level_ambient_modules() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/ambient.ts",
            r#"declare module "M" { const value: number; }"#,
        )
        .unwrap();
        fs.write_file("/project/main.ts", r#"import M = require("M"); M.value;"#)
            .unwrap();

        let program = Program::new_with_module_resolution(
            &fs,
            "/project",
            &["main.ts".to_owned(), "ambient.ts".to_owned()],
            ts_module::ResolutionOptions::default(),
        );
        assert!(
            !program
                .diagnostics()
                .iter()
                .any(|diagnostic| diagnostic.code == Some(2307)),
            "{:?}",
            program.diagnostics()
        );
        assert_eq!(
            program
                .resolved_modules
                .get(&super::ResolvedModuleKey::new(
                    "/project/main.ts".to_owned(),
                    "M".to_owned(),
                    CanonicalModuleResolutionMode::CommonJs,
                ))
                .map(String::as_str),
            Some("/project/ambient.ts")
        );
    }

    #[test]
    fn resolves_import_equals_against_referenced_ambient_modules() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/ambient.ts",
            r#"declare module "M" { export class Value {} }"#,
        )
        .unwrap();
        fs.write_file(
            "/project/main.ts",
            r#"/// <reference path="ambient.ts" />
import M = require("M");
export function create() { return new M.Value(); }"#,
        )
        .unwrap();

        let program = Program::new_with_module_resolution(
            &fs,
            "/project",
            &["main.ts".to_owned()],
            ts_module::ResolutionOptions::default(),
        );
        assert!(
            !program
                .diagnostics()
                .iter()
                .any(|diagnostic| diagnostic.code == Some(2307)),
            "{:?}",
            program.diagnostics()
        );
        assert_eq!(
            program
                .resolved_modules
                .get(&super::ResolvedModuleKey::new(
                    "/project/main.ts".to_owned(),
                    "M".to_owned(),
                    CanonicalModuleResolutionMode::CommonJs,
                ))
                .map(String::as_str),
            Some("/project/ambient.ts")
        );
    }

    #[test]
    fn resolves_es_imports_against_top_level_ambient_modules() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/ambient.d.ts",
            r#"declare module "url" { export class Url {} export function parse(): Url; }"#,
        )
        .unwrap();
        fs.write_file(
            "/project/main.ts",
            r#"import { parse } from "url"; export const thing = parse();"#,
        )
        .unwrap();
        let program = Program::new_with_options(
            &fs,
            "/project",
            &["main.ts".to_owned(), "ambient.d.ts".to_owned()],
            CompilerOptions {
                declaration: true,
                emit_declaration_only: true,
                no_lib: true,
                ..CompilerOptions::default()
            },
        );
        assert!(
            !program
                .diagnostics()
                .iter()
                .any(|diagnostic| diagnostic.code == Some(2307)),
            "{:?}",
            program.diagnostics()
        );
        let declaration = program
            .emit()
            .files
            .into_iter()
            .find(|file| file.file_name == "/project/main.d.ts")
            .unwrap();
        assert_eq!(
            declaration.text,
            "export declare const thing: import(\"url\").Url;\n"
        );
    }

    #[test]
    fn elides_semantically_type_only_imports_from_merged_ambient_modules() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/ambient.ts",
            r#"
                declare module "foo" {
                    namespace B { export interface A {} }
                    interface B { bar(name: string): B.A; }
                    export = B;
                }
                declare module "runtime" {
                    class Runtime {}
                    export = Runtime;
                }
            "#,
        )
        .unwrap();
        fs.write_file(
            "/project/main.ts",
            concat!(
                "///<reference path='ambient.ts' />\n",
                "import foo = require(\"foo\");\n",
                "import Runtime = require(\"runtime\");\n",
                "import Missing = require(\"missing\");\n",
                "import \"foo\";\n",
                "declare var z: foo;\n",
                "z.bar(\"hello\");\n",
                "var x: foo.A = foo.bar(\"hello\");\n",
                "new Runtime();\n",
                "Missing.run();\n",
            ),
        )
        .unwrap();
        let program = Program::new_with_options(
            &fs,
            "/project",
            &["main.ts".to_owned(), "ambient.ts".to_owned()],
            CompilerOptions {
                module: ModuleKind::CommonJs,
                target: ScriptTarget::Es2015,
                no_lib: true,
                ..CompilerOptions::default()
            },
        );
        let emitted = program.emit();
        assert!(emitted.diagnostics.is_empty(), "{:?}", emitted.diagnostics);
        let javascript = emitted
            .files
            .iter()
            .find(|file| file.file_name == "/project/main.js")
            .unwrap();
        assert!(!javascript.text.contains("const foo = require(\"foo\")"));
        assert!(!javascript.text.contains("reference path"));
        assert!(
            javascript
                .text
                .contains("const Runtime = require(\"runtime\");")
        );
        assert!(
            javascript
                .text
                .contains("const Missing = require(\"missing\");")
        );
        assert!(javascript.text.contains("require(\"foo\");"));
        assert!(javascript.text.contains("foo.bar(\"hello\")"));
    }

    #[test]
    fn emits_amd_wrapper_for_ambient_import_equals_consumer() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/ambient.ts",
            r#"declare module "M" { const value: number; }"#,
        )
        .unwrap();
        fs.write_file(
            "/project/main.ts",
            concat!(
                "///<amd-module name='Consumer'/>\n",
                "///<amd-dependency path='side' name='side'/>\n",
                "import M = require(\"M\");\n",
                "M.value;\n",
            ),
        )
        .unwrap();

        let program = Program::new_with_options(
            &fs,
            "/project",
            &["main.ts".to_owned(), "ambient.ts".to_owned()],
            CompilerOptions {
                module: ModuleKind::Amd,
                target: ScriptTarget::Es2015,
                no_lib: true,
                ..CompilerOptions::default()
            },
        );
        assert!(
            program.diagnostics().is_empty(),
            "{:?}",
            program.diagnostics()
        );
        let emitted = program.emit();
        assert!(emitted.diagnostics.is_empty(), "{:?}", emitted.diagnostics);
        let javascript = emitted
            .files
            .iter()
            .find(|file| file.file_name == "/project/main.js")
            .unwrap();
        assert_eq!(
            javascript.text,
            concat!(
                "///<amd-dependency path='side' name='side'/>\n",
                "define(\"Consumer\", [\"require\", \"exports\", \"side\", \"M\"], function (require, exports, side, M) {\n",
                "    \"use strict\";\n",
                "    Object.defineProperty(exports, \"__esModule\", { value: true });\n",
                "    ///<amd-module name='Consumer'/>\n",
                "    M.value;\n",
                "});\n",
            )
        );
    }

    #[test]
    fn amd_elides_import_equals_used_only_in_erased_generic_types() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/types.ts",
            "interface Foo<T> { value: T; } export = Foo;",
        )
        .unwrap();
        fs.write_file(
            "/project/main.ts",
            "import Foo = require(\"./types\"); export let value: Foo<string>;",
        )
        .unwrap();

        let program = Program::new_with_options(
            &fs,
            "/project",
            &["main.ts".to_owned(), "types.ts".to_owned()],
            CompilerOptions {
                module: ModuleKind::Amd,
                target: ScriptTarget::Es2015,
                declaration: true,
                no_lib: true,
                ..CompilerOptions::default()
            },
        );
        let emitted = program.emit();
        assert!(emitted.diagnostics.is_empty(), "{:?}", emitted.diagnostics);
        let javascript = emitted
            .files
            .iter()
            .find(|file| file.file_name == "/project/main.js")
            .unwrap();
        assert!(
            javascript
                .text
                .starts_with("define([\"require\", \"exports\"], function (require, exports)"),
            "{}",
            javascript.text
        );
        assert!(!javascript.text.contains("./types"), "{}", javascript.text);
    }

    #[test]
    fn relative_ambient_module_names_do_not_satisfy_resolution() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/ambient.ts",
            r#"declare module "./M" { const value: number; }"#,
        )
        .unwrap();
        fs.write_file("/project/main.ts", r#"import M = require("./M"); M.value;"#)
            .unwrap();

        let program = Program::new_with_module_resolution(
            &fs,
            "/project",
            &["main.ts".to_owned(), "ambient.ts".to_owned()],
            ts_module::ResolutionOptions::default(),
        );
        assert!(
            program
                .diagnostics()
                .iter()
                .any(|diagnostic| diagnostic.code == Some(2307)),
            "{:?}",
            program.diagnostics()
        );
    }

    #[test]
    fn module_augmentations_do_not_satisfy_ambient_resolution() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/augmentation.ts",
            r#"export {}; declare module "M" { const value: number; }"#,
        )
        .unwrap();
        fs.write_file("/project/main.ts", r#"import M = require("M"); M.value;"#)
            .unwrap();

        let program = Program::new_with_module_resolution(
            &fs,
            "/project",
            &["main.ts".to_owned(), "augmentation.ts".to_owned()],
            ts_module::ResolutionOptions::default(),
        );
        assert!(
            program
                .diagnostics()
                .iter()
                .any(|diagnostic| diagnostic.code == Some(2307)),
            "{:?}",
            program.diagnostics()
        );
    }

    #[test]
    fn checks_named_default_and_type_imports_across_files() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/dep.ts",
            r"
                export const count: number = 1;
                const internal: number = 2;
                export { internal as value };
                export type Box<T> = Array<T>;
                export default function label(value: string): string { return value; }
            ",
        )
        .unwrap();
        fs.write_file(
            "/project/main.ts",
            r#"
                import label, { count, value, Box } from "./dep";
                const total: number = count + value;
                const wrong: string = count;
                const boxed: Box<number> = [1, "wrong"];
                label(1);
            "#,
        )
        .unwrap();
        let program = Program::new_with_module_resolution(
            &fs,
            "/project",
            &["main.ts".to_owned()],
            ts_module::ResolutionOptions::default(),
        );
        assert_eq!(program.source_files().len(), 2);
        assert_eq!(
            program
                .diagnostics()
                .iter()
                .filter_map(|diagnostic| diagnostic.code)
                .collect::<Vec<_>>(),
            [2322, 2322, 2345]
        );
    }

    #[test]
    fn declaration_files_contribute_globals_and_report_duplicates() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/globals.d.ts",
            "interface Shared { value: string; } declare const duplicate: number;",
        )
        .unwrap();
        fs.write_file("/project/other.d.ts", "declare const duplicate: string;")
            .unwrap();
        fs.write_file(
            "/project/main.ts",
            "const good: Shared = { value: 'ok' }; const bad: Shared = { value: 1 };",
        )
        .unwrap();
        let program = Program::new(
            &fs,
            "/project",
            &[
                "globals.d.ts".to_owned(),
                "other.d.ts".to_owned(),
                "main.ts".to_owned(),
            ],
        );
        assert!(
            program
                .diagnostics()
                .iter()
                .any(|diagnostic| diagnostic.code == Some(2451))
        );
        assert!(
            program
                .diagnostics()
                .iter()
                .any(|diagnostic| diagnostic.code == Some(2322))
        );
        assert!(
            !program
                .diagnostics()
                .iter()
                .any(|diagnostic| diagnostic.code == Some(2304))
        );
        assert!(
            program
                .diagnostics()
                .iter()
                .all(|diagnostic| diagnostic.category == Category::Error)
        );
    }

    #[test]
    fn resolves_nested_ambient_namespace_members_across_files() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/functions.d.ts",
            r"
                declare namespace A {
                    namespace AA {
                        function func(): number;
                    }
                }
            ",
        )
        .unwrap();
        fs.write_file(
            "/project/values.d.ts",
            "declare namespace A { namespace AA { const value: string; } }",
        )
        .unwrap();
        fs.write_file(
            "/project/main.ts",
            "const count: number = A.AA.func(); const text: string = A.AA.value;",
        )
        .unwrap();
        let program = Program::new_with_options(
            &fs,
            "/project",
            &[
                "main.ts".to_owned(),
                "functions.d.ts".to_owned(),
                "values.d.ts".to_owned(),
            ],
            CompilerOptions {
                no_lib: true,
                ..CompilerOptions::default()
            },
        );
        assert!(
            program.diagnostics().is_empty(),
            "{:?}",
            program.diagnostics()
        );
    }

    #[test]
    fn resolves_exported_namespaces_through_namespace_imports() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/library.ts",
            "export namespace Tools { export function value(): number { return 1; } }",
        )
        .unwrap();
        fs.write_file(
            "/project/main.ts",
            "import * as Library from './library'; const value: number = Library.Tools.value();",
        )
        .unwrap();
        let program = Program::new_with_options(
            &fs,
            "/project",
            &["main.ts".to_owned()],
            CompilerOptions {
                module: ModuleKind::EsNext,
                target: ScriptTarget::Es2015,
                no_lib: true,
                ..CompilerOptions::default()
            },
        );
        assert!(
            program.diagnostics().is_empty(),
            "{:?}",
            program.diagnostics()
        );
    }

    #[test]
    fn emits_type_erased_modern_javascript() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/main.ts",
            "interface Point { x: number } const point: Point = { x: 1 };",
        )
        .unwrap();
        let program = Program::new(&fs, "/project", &["main.ts".to_owned()]);
        let emitted = program.emit();
        assert!(emitted.diagnostics.is_empty());
        assert_eq!(emitted.files[0].file_name, "/project/main.js");
        assert_eq!(
            emitted.files[0].text,
            "\"use strict\";\nvar point = { x: 1 };\n"
        );
    }

    #[test]
    fn emit_paths_follow_jsx_and_module_extension_rules() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file("/project/view.tsx", "const view = 1;")
            .unwrap();
        fs.write_file("/project/module.mts", "const value = 1;")
            .unwrap();
        let program = Program::new(
            &fs,
            "/project",
            &["view.tsx".to_owned(), "module.mts".to_owned()],
        );
        let emitted = program.emit();
        let paths: Vec<_> = emitted
            .files
            .iter()
            .map(|file| file.file_name.as_str())
            .collect();
        assert!(paths.contains(&"/project/view.js"));
        assert!(paths.contains(&"/project/module.mjs"));
    }

    #[test]
    fn cts_sources_use_commonjs_and_import_async_helpers() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/notmodule.cts",
            concat!("export async function foo() {\n", "  await 0;\n", "}",),
        )
        .unwrap();
        let program = Program::new_with_options(
            &fs,
            "/project",
            &["notmodule.cts".to_owned()],
            CompilerOptions {
                import_helpers: true,
                module: ModuleKind::EsNext,
                target: ScriptTarget::Es2015,
                no_lib: true,
                ..CompilerOptions::default()
            },
        );
        let emitted = program.emit();
        let javascript = emitted
            .files
            .iter()
            .find(|file| file.file_name == "/project/notmodule.cjs")
            .unwrap();
        assert_eq!(
            javascript.text,
            concat!(
                "\"use strict\";\n",
                "Object.defineProperty(exports, \"__esModule\", { value: true });\n",
                "exports.foo = foo;\n",
                "const tslib_1 = require(\"tslib\");\n",
                "function foo() {\n",
                "    return tslib_1.__awaiter(this, void 0, void 0, function* () {\n",
                "        yield 0;\n",
                "    });\n",
                "}\n",
            )
        );
    }

    #[test]
    fn parses_and_emits_tsx_roots() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file("/project/view.tsx", "const view = <Box label=\"ok\" />;")
            .unwrap();
        let program = Program::new_with_options(
            &fs,
            "/project",
            &["view.tsx".to_owned()],
            CompilerOptions {
                no_lib: true,
                ..CompilerOptions::default()
            },
        );
        assert!(
            program.diagnostics().is_empty(),
            "{:?}",
            program.diagnostics()
        );
        let emitted = program.emit();
        assert!(emitted.diagnostics.is_empty(), "{:?}", emitted.diagnostics);
        assert_eq!(emitted.files.len(), 1);
        assert_eq!(emitted.files[0].file_name, "/project/view.js");
        assert_eq!(
            emitted.files[0].text,
            "\"use strict\";\nvar view = <Box label=\"ok\" />;\n"
        );
    }

    #[test]
    fn javascript_sources_use_jsx_language_variant_without_jsx_option() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file("/project/a.js", "~< <\n").unwrap();
        let program = Program::new_with_options(
            &fs,
            "/project",
            &["a.js".to_owned()],
            CompilerOptions {
                allow_js: true,
                target: ScriptTarget::Es2015,
                no_lib: true,
                out_dir: Some("/project/out".to_owned()),
                ..CompilerOptions::default()
            },
        );
        assert_eq!(
            program.emit().files[0].text,
            "\"use strict\";\n~< /> <\n;\n"
        );
    }

    #[test]
    fn checks_annotated_variable_assignability() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/type-error.ts",
            "import { missing } from './absent'; const value: string = 1;",
        )
        .unwrap();
        let program = Program::new(&fs, "/", &["type-error.ts".to_owned()]);
        assert!(
            program
                .diagnostics()
                .iter()
                .any(|diagnostic| diagnostic.code == Some(2322))
        );
    }

    #[test]
    fn reports_enum_and_advanced_type_operator_diagnostics() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/advanced-types.ts",
            r#"
                enum State { Ready, Running = 3, Finished }
                type Record = { id: number; label: string };
                type Keys = keyof Record;
                type Values = Record[Keys];
                type Element<T> = T extends readonly (infer U)[] ? U : never;
                type Labels<T> = {
                    [K in keyof T as K extends "id" ? never : K]: T[K]
                };
                const state: State = "Ready";
                const key: Keys = "missing";
                const value: Values = false;
                const element: Element<string[]> = 1;
                const labels: Labels<Record> = { label: "ok", id: 1 };
            "#,
        )
        .unwrap();
        let program = Program::new_with_options(
            &fs,
            "/",
            &["advanced-types.ts".to_owned()],
            CompilerOptions {
                no_lib: true,
                ..CompilerOptions::default()
            },
        );
        assert_eq!(
            program
                .diagnostics()
                .iter()
                .filter_map(|diagnostic| diagnostic.code)
                .collect::<Vec<_>>(),
            [2322, 2322, 2322, 2322, 2353]
        );
    }

    #[test]
    fn no_check_skips_semantic_diagnostics() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file("/type-error.ts", "const value: string = 1;")
            .unwrap();
        let program = Program::new_with_options(
            &fs,
            "/",
            &["type-error.ts".to_owned()],
            CompilerOptions {
                no_check: true,
                ..CompilerOptions::default()
            },
        );
        assert_eq!(program.source_files().len(), 1);
        assert!(!program.source_files()[0].is_default_library);
        assert!(
            !program
                .diagnostics()
                .iter()
                .any(|diagnostic| matches!(diagnostic.code, Some(2307 | 2322)))
        );
        assert_eq!(program.emit().files.len(), 1);
    }

    #[test]
    fn checks_large_class_graphs_instead_of_failing_open() {
        use std::fmt::Write as _;
        let fs = MemoryFileSystem::new(true);
        let mut source = format!("/*{}*/\n", "x".repeat(100_000));
        for index in 0..100 {
            writeln!(source, "class C{index} {{}}").unwrap();
        }
        source.push_str("const value: string = 1;\n");
        fs.write_file("/large.ts", &source).unwrap();
        let program = Program::new_with_options(
            &fs,
            "/",
            &["large.ts".to_owned()],
            CompilerOptions {
                no_lib: true,
                ..CompilerOptions::default()
            },
        );
        assert!(
            program
                .diagnostics()
                .iter()
                .any(|diagnostic| diagnostic.code == Some(2322)),
            "large programs must receive semantic diagnostics"
        );
    }

    #[test]
    fn check_js_controls_javascript_semantic_diagnostics() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file("/input.js", "const value = true; value.missing;")
            .unwrap();
        let unchecked = Program::new_with_options(
            &fs,
            "/",
            &["input.js".to_owned()],
            CompilerOptions {
                allow_js: true,
                check_js: false,
                no_lib: true,
                ..CompilerOptions::default()
            },
        );
        assert!(
            !unchecked
                .diagnostics()
                .iter()
                .any(|diagnostic| diagnostic.code == Some(2339))
        );

        let checked = Program::new_with_options(
            &fs,
            "/",
            &["input.js".to_owned()],
            CompilerOptions {
                allow_js: true,
                check_js: true,
                no_lib: true,
                ..CompilerOptions::default()
            },
        );
        assert!(
            checked
                .diagnostics()
                .iter()
                .any(|diagnostic| diagnostic.code == Some(2339))
        );
    }

    #[test]
    fn unchecked_javascript_parameter_decorators_match_upstream() {
        let source = concat!(
            "function dec(target, key, index) {}\n",
            "\n",
            "class Foo {\n",
            "    method(@dec x) {}\n",
            "}\n",
        );
        let fs = MemoryFileSystem::new(true);
        fs.write_file("/a.js", source).unwrap();
        let program = Program::try_new_with_canonical_checker(
            &fs,
            "/",
            &["a.js".to_owned()],
            CompilerOptions {
                allow_js: true,
                check_js: false,
                no_emit: true,
                ..CompilerOptions::default()
            },
        )
        .unwrap();
        let [diagnostic] = program.diagnostics() else {
            panic!(
                "expected the parameter decorator diagnostic: {:?}",
                program.diagnostics()
            );
        };
        assert_eq!(diagnostic.code, Some(1206));
        assert_eq!(diagnostic.file_name.as_deref(), Some("/a.js"));
        assert_eq!(diagnostic.message, "Decorators are not valid here.");
        let range = diagnostic.range.unwrap();
        assert_eq!(range.start.get() as usize, source.find("@dec").unwrap());
        assert_eq!(range.end.get() - range.start.get(), 4);
    }

    #[test]
    fn unchecked_javascript_parameter_decorators_respect_options_and_directives() {
        for (file_name, prefix, check_js, experimental_decorators, expected) in [
            ("a.js", "", false, false, true),
            ("a.js", "", false, true, false),
            ("a.js", "", true, false, false),
            ("a.js", "// @ts-check\n", false, false, false),
            ("a.js", "// @ts-nocheck\n", true, false, true),
            ("a.ts", "", false, false, false),
        ] {
            let fs = MemoryFileSystem::new(true);
            let source = format!(
                "{prefix}function dec() {{}} class Foo {{ method(@dec @dec x, @dec y) {{}} }}"
            );
            fs.write_file(&format!("/{file_name}"), &source).unwrap();
            let program = Program::new_unchecked_with_options_and_checker(
                &fs,
                "/",
                &[file_name.to_owned()],
                CompilerOptions {
                    allow_js: true,
                    check_js,
                    experimental_decorators,
                    no_emit: true,
                    ..CompilerOptions::default()
                },
                super::ProgramChecker::Canonical,
            );
            let ranges = program
                .diagnostics()
                .iter()
                .filter(|diagnostic| diagnostic.code == Some(1206))
                .map(|diagnostic| diagnostic.range.unwrap())
                .collect::<Vec<_>>();
            if expected {
                assert_eq!(ranges.len(), 2);
                assert_eq!(ranges[0].start.get() as usize, source.find("@dec").unwrap());
                assert_eq!(
                    ranges[1].start.get() as usize,
                    source.rfind("@dec").unwrap() - 1
                );
                for (range, expected) in ranges.into_iter().zip(["@dec", " @dec"]) {
                    assert_eq!(
                        &source[range.start.get() as usize..range.end.get() as usize],
                        expected
                    );
                }
            } else {
                assert!(
                    ranges.is_empty(),
                    "{file_name}, {prefix:?}, checkJs={check_js}"
                );
            }
        }
    }

    #[test]
    fn canonical_javascript_parameter_decorators_follow_the_checking_phase() {
        let original = "function dec() {} class Foo { method(@dec @dec x, @dec y) {} }";
        for (prefix, check_js, experimental_decorators, no_check, expected) in [
            ("", false, false, false, Some(["@dec", " @dec"])),
            ("", false, true, false, None),
            ("", true, false, false, Some(["@", "@"])),
            ("// @ts-check\n", false, false, false, Some(["@", "@"])),
            (
                "// @ts-nocheck\n",
                true,
                false,
                false,
                Some(["@dec", " @dec"]),
            ),
            ("", true, false, true, None),
            ("", false, false, true, Some(["@dec", " @dec"])),
        ] {
            let fs = MemoryFileSystem::new(true);
            let source = format!("{prefix}{original}");
            fs.write_file("/a.js", &source).unwrap();
            let program = Program::try_new_with_canonical_checker(
                &fs,
                "/",
                &["a.js".to_owned()],
                CompilerOptions {
                    allow_js: true,
                    check_js,
                    experimental_decorators,
                    no_check,
                    no_emit: true,
                    ..CompilerOptions::default()
                },
            )
            .unwrap();
            let ranges = program
                .diagnostics()
                .iter()
                .filter(|diagnostic| diagnostic.code == Some(1206))
                .map(|diagnostic| diagnostic.range.unwrap())
                .collect::<Vec<_>>();
            if let Some(expected) = expected {
                assert_eq!(ranges.len(), 2);
                for (range, expected) in ranges.into_iter().zip(expected) {
                    assert_eq!(
                        &source[range.start.get() as usize..range.end.get() as usize],
                        expected,
                    );
                }
            } else {
                assert!(
                    ranges.is_empty(),
                    "{prefix:?}, checkJs={check_js}, noCheck={no_check}"
                );
            }
        }

        let source = "function dec() {}\nclass Foo { method(@dec x) { this.missing; return x; } }";
        for no_check in [false, true] {
            let fs = MemoryFileSystem::new(true);
            fs.write_file("/a.js", source).unwrap();
            let program = Program::try_new_with_canonical_checker(
                &fs,
                "/",
                &["a.js".to_owned()],
                CompilerOptions {
                    allow_js: true,
                    check_js: true,
                    no_implicit_any: true,
                    no_check,
                    no_emit: true,
                    ..CompilerOptions::default()
                },
            )
            .unwrap();
            let codes = program
                .diagnostics()
                .iter()
                .map(|diagnostic| diagnostic.code.unwrap())
                .collect::<Vec<_>>();
            let expected = if no_check {
                vec![]
            } else {
                vec![1206, 7006, 2339]
            };
            assert_eq!(codes, expected, "noCheck={no_check}");
        }
    }

    #[test]
    fn unchecked_javascript_parameter_decorators_keep_leading_trivia() {
        for (source, expected) in [
            (
                "function dec() {} class Foo { method( /* first */ @dec x,\n // second\n @dec y) { this.missing; } }",
                vec![" /* first */ @dec", "\n // second\n @dec"],
            ),
            (
                "function dec() {} class Foo { method(seed = /[,)]@dec/, /* actual */ @dec x) {} }",
                vec![" /* actual */ @dec"],
            ),
            (
                "function dec() {}\nclass Foo {\n// @ts-expect-error\nmethod(@dec x) {\nthis.missing;\n}\n}",
                vec!["@dec"],
            ),
        ] {
            let fs = MemoryFileSystem::new(true);
            fs.write_file("/a.js", source).unwrap();
            let program = Program::new_unchecked_with_options_and_checker(
                &fs,
                "/",
                &["a.js".to_owned()],
                CompilerOptions {
                    allow_js: true,
                    no_emit: true,
                    ..CompilerOptions::default()
                },
                super::ProgramChecker::Canonical,
            );
            let diagnostics = program.diagnostics();
            assert_eq!(diagnostics.len(), expected.len(), "{source}");
            for (diagnostic, expected) in diagnostics.iter().zip(expected) {
                assert_eq!(diagnostic.code, Some(1206));
                let range = diagnostic.range.unwrap();
                assert_eq!(range.start.get() as usize, source.find(expected).unwrap());
                assert_eq!(range.len() as usize, expected.len());
                assert_eq!(
                    &source[range.start.get() as usize..range.end.get() as usize],
                    expected
                );
            }
            let file = program.source_file("/a.js").unwrap();
            for (_, node) in file.parse.arena.iter() {
                if matches!(node.data, NodeData::Decorator(_)) {
                    assert_eq!(
                        &source[node.range.start.get() as usize..node.range.end.get() as usize],
                        "@dec"
                    );
                }
            }
        }
    }

    #[test]
    fn checked_javascript_parameter_decorators_preserve_trivia_and_directive_controls() {
        for (source, no_check, expected) in [
            (
                "function dec() {} class Foo { method( /* first */ @dec x,\n // second\n @dec y) { this.missing; } }",
                false,
                vec![1206, 7006, 1206, 7006, 2339],
            ),
            (
                "function dec() {} class Foo { method( /* first */ @dec x,\n // second\n @dec y) { this.missing; } }",
                true,
                vec![],
            ),
            (
                "function dec() {}\nclass Foo {\n// @ts-expect-error\nmethod(@dec x) {\nthis.missing;\n}\n}",
                false,
                vec![2339],
            ),
        ] {
            let fs = MemoryFileSystem::new(true);
            fs.write_file("/a.js", source).unwrap();
            let program = Program::try_new_with_canonical_checker(
                &fs,
                "/",
                &["a.js".to_owned()],
                CompilerOptions {
                    allow_js: true,
                    check_js: true,
                    no_check,
                    no_implicit_any: true,
                    no_emit: true,
                    ..CompilerOptions::default()
                },
            )
            .unwrap();
            assert_eq!(
                program
                    .diagnostics()
                    .iter()
                    .map(|diagnostic| diagnostic.code.unwrap())
                    .collect::<Vec<_>>(),
                expected,
                "{source}"
            );
            for diagnostic in program.diagnostics() {
                if diagnostic.code == Some(1206) {
                    let range = diagnostic.range.unwrap();
                    assert_eq!(
                        &source[range.start.get() as usize..range.end.get() as usize],
                        "@"
                    );
                }
            }
        }
    }

    #[test]
    fn emits_const_enum_accesses_as_commented_constants() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/const-enum.ts",
            concat!(
                "const enum TestType { foo, bar }\n",
                "type TestTypeStr = keyof typeof TestType;\n",
                "function f1(f: TestType) { }\n",
                "function f2(f: TestTypeStr) { }\n",
                "f1(TestType.foo)\n",
                "f1(TestType.bar)\n",
                "f2('foo')\n",
                "f2('bar')\n",
            ),
        )
        .unwrap();
        let program = Program::new_with_options(
            &fs,
            "/",
            &["const-enum.ts".to_owned()],
            CompilerOptions {
                target: ScriptTarget::Es2015,
                no_lib: true,
                ..CompilerOptions::default()
            },
        );
        let emitted = program.emit();
        assert_eq!(
            emitted.files[0].text,
            concat!(
                "\"use strict\";\n",
                "function f1(f) { }\n",
                "function f2(f) { }\n",
                "f1(0 /* TestType.foo */);\n",
                "f1(1 /* TestType.bar */);\n",
                "f2('foo');\n",
                "f2('bar');\n",
            )
        );
    }

    #[test]
    fn const_enum_emit_respects_preserve_isolated_and_no_check() {
        let source = "const enum E { Value = 1, Value2 = Value } E.Value2;";
        for (options, expected_access) in [
            (
                CompilerOptions {
                    preserve_const_enums: true,
                    target: ScriptTarget::Es2015,
                    no_lib: true,
                    ..CompilerOptions::default()
                },
                "1 /* E.Value2 */;",
            ),
            (
                CompilerOptions {
                    isolated_modules: true,
                    target: ScriptTarget::Es2015,
                    no_lib: true,
                    ..CompilerOptions::default()
                },
                "E.Value2;",
            ),
            (
                CompilerOptions {
                    no_check: true,
                    target: ScriptTarget::Es2015,
                    no_lib: true,
                    ..CompilerOptions::default()
                },
                "1 /* E.Value2 */;",
            ),
        ] {
            let fs = MemoryFileSystem::new(true);
            fs.write_file("/mode.ts", source).unwrap();
            let program = Program::new_with_options(&fs, "/", &["mode.ts".to_owned()], options);
            assert!(
                program.diagnostics().is_empty(),
                "{:?}",
                program.diagnostics()
            );
            let javascript = &program.emit().files[0].text;
            if javascript.contains("var E;") {
                assert!(javascript.contains("E[E[\"Value2\"] = 1] = \"Value2\";"));
            }
            assert!(javascript.contains(expected_access), "{javascript}");
        }
    }

    #[test]
    fn const_enum_fallbacks_do_not_capture_same_named_non_const_enums() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/scoped-enums.ts",
            concat!(
                "function ordinary() { return E.A; enum E { A } }\n",
                "function constant() { return E.A; const enum E { A } }\n",
                "const config = { a: After.A };\n",
                "const enum After { A = 2 }\n",
            ),
        )
        .unwrap();
        let program = Program::new_with_options(
            &fs,
            "/",
            &["scoped-enums.ts".to_owned()],
            CompilerOptions {
                target: ScriptTarget::Es2015,
                no_lib: true,
                ..CompilerOptions::default()
            },
        );
        let javascript = &program.emit().files[0].text;
        assert!(javascript.contains("return E.A;"), "{javascript}");
        assert!(javascript.contains("return 0 /* E.A */;"), "{javascript}");
        assert!(javascript.contains("a: 2 /* After.A */"), "{javascript}");
    }

    #[test]
    fn const_enum_property_accesses_inline_in_computed_names() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/property.ts",
            concat!(
                "const enum G { A = 1, B = 2, C = A + B, D = A * 2 }\n",
                "var o: { [idx: number]: boolean } = { 1: true };\n",
                "var a = G.A; var a1 = G[\"A\"]; var g = o[G.A];\n",
                "class C { [G.A]() { } get [G.B]() { return true; } set [G.B](x: number) { } }\n",
            ),
        )
        .unwrap();
        let program = Program::new_with_options(
            &fs,
            "/",
            &["property.ts".to_owned()],
            CompilerOptions {
                target: ScriptTarget::Es2015,
                no_lib: true,
                ..CompilerOptions::default()
            },
        );
        let javascript = &program.emit().files[0].text;
        assert!(!javascript.contains("var G;"), "{javascript}");
        for expected in [
            "1 /* G.A */",
            "1 /* G[\"A\"] */",
            "o[1 /* G.A */]",
            "[1 /* G.A */]()",
            "get [2 /* G.B */]()",
            "set [2 /* G.B */](x)",
        ] {
            assert!(
                javascript.contains(expected),
                "missing {expected}: {javascript}"
            );
        }
    }

    #[test]
    fn erased_exported_const_enum_has_no_commonjs_export() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/exported.ts",
            "export const enum E { A = 1 } export const value = E.A;",
        )
        .unwrap();
        let program = Program::new_with_options(
            &fs,
            "/",
            &["exported.ts".to_owned()],
            CompilerOptions {
                module: ModuleKind::CommonJs,
                target: ScriptTarget::Es2015,
                no_lib: true,
                ..CompilerOptions::default()
            },
        );
        let javascript = &program.emit().files[0].text;
        assert!(!javascript.contains("exports.E"), "{javascript}");
        assert!(
            javascript.contains("exports.value = 1 /* E.A */;"),
            "{javascript}"
        );
    }

    #[test]
    fn type_only_import_expression_does_not_emit_commonjs_helpers() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/p1/index.ts",
            concat!(
                "export interface Ref<T> { current: T; }\n",
                "export function useRef<T>(current: T): Ref<T> { return { current }; }\n",
                "export const useParser = () => useRef<typeof import(\"csv-parse\")>(null);\n",
            ),
        )
        .unwrap();
        fs.write_file(
            "/p1/node_modules/csv-parse/lib/index.d.ts",
            "export function bar(): number;",
        )
        .unwrap();
        fs.write_file(
            "/p1/node_modules/csv-parse/package.json",
            r#"{"main":"./lib","types":["./lib/index.d.ts"]}"#,
        )
        .unwrap();
        let program = Program::new_with_options(
            &fs,
            "/p1",
            &["index.ts".to_owned()],
            CompilerOptions {
                declaration: true,
                module: ModuleKind::CommonJs,
                target: ScriptTarget::Es2015,
                no_lib: true,
                ..CompilerOptions::default()
            },
        );
        assert!(
            program
                .source_file("/p1/node_modules/csv-parse/lib/index.d.ts")
                .is_some(),
            "{:?}",
            program.diagnostics()
        );
        let emitted = program.emit();
        let javascript = emitted
            .files
            .iter()
            .find(|file| file.file_name == "/p1/index.js")
            .unwrap();
        assert!(
            !javascript.text.contains("__createBinding"),
            "{javascript:?}"
        );
        let declaration = emitted
            .files
            .iter()
            .find(|file| file.file_name == "/p1/index.d.ts")
            .unwrap();
        assert!(
            declaration.text.contains("typeof import(\"csv-parse\")"),
            "{declaration:?}"
        );
    }

    #[test]
    fn no_emit_on_error_suppresses_all_outputs() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file("/type-error.ts", "const value: string = 1;")
            .unwrap();
        let program = Program::new_with_options(
            &fs,
            "/",
            &["type-error.ts".to_owned()],
            CompilerOptions {
                no_emit_on_error: true,
                no_lib: true,
                ..CompilerOptions::default()
            },
        );
        assert!(
            program
                .diagnostics()
                .iter()
                .any(|diagnostic| diagnostic.code == Some(2322))
        );
        assert!(program.emit().files.is_empty());

        let ordinary = Program::new_with_options(
            &fs,
            "/",
            &["type-error.ts".to_owned()],
            CompilerOptions {
                no_lib: true,
                ..CompilerOptions::default()
            },
        );
        assert_eq!(ordinary.emit().files.len(), 1);
    }

    #[test]
    fn auto_accessors_require_es2015_when_no_emit_on_error_is_enabled() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file("/auto-accessor.ts", "class C { accessor value = 1; }")
            .unwrap();

        let es5 = Program::new_with_options(
            &fs,
            "/",
            &["auto-accessor.ts".to_owned()],
            CompilerOptions {
                target: ScriptTarget::Es5,
                no_emit_on_error: true,
                no_lib: true,
                ..CompilerOptions::default()
            },
        );
        assert!(
            es5.diagnostics()
                .iter()
                .any(|diagnostic| diagnostic.code == Some(18045))
        );
        assert!(es5.emit().files.is_empty());

        let es2015 = Program::new_with_options(
            &fs,
            "/",
            &["auto-accessor.ts".to_owned()],
            CompilerOptions {
                target: ScriptTarget::Es2015,
                no_emit_on_error: true,
                no_lib: true,
                ..CompilerOptions::default()
            },
        );
        assert!(
            es2015
                .diagnostics()
                .iter()
                .all(|diagnostic| diagnostic.code != Some(18045))
        );
        assert_eq!(es2015.emit().files.len(), 1);
    }

    #[test]
    fn out_file_concatenates_sources_once_in_root_order() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file("/project/first.ts", "const first = 1;")
            .unwrap();
        fs.write_file("/project/second.ts", "const second = 2;")
            .unwrap();
        let program = Program::new_with_options(
            &fs,
            "/project",
            &["second.ts".to_owned(), "first.ts".to_owned()],
            CompilerOptions {
                out_file: Some("dist/out.js".into()),
                module: ModuleKind::Amd,
                target: ScriptTarget::Es2015,
                source_map: true,
                no_lib: true,
                ..CompilerOptions::default()
            },
        );
        let emitted = program.emit();
        assert!(emitted.diagnostics.is_empty(), "{:?}", emitted.diagnostics);
        assert_eq!(emitted.files.len(), 2);
        let javascript = emitted
            .files
            .iter()
            .find(|file| file.file_name == "/project/dist/out.js")
            .unwrap();
        assert_eq!(
            javascript.text,
            "\"use strict\";\nconst second = 2;\nconst first = 1;\n//# sourceMappingURL=out.js.map"
        );
        let map = emitted
            .files
            .iter()
            .find(|file| file.file_name == "/project/dist/out.js.map")
            .unwrap();
        assert!(
            map.text
                .contains("\"sources\":[\"/project/second.ts\",\"/project/first.ts\"]")
        );
    }

    #[test]
    fn out_file_qualifies_members_from_later_reopened_namespaces() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/a.ts",
            "namespace ts { export function print() { return sys.version; } }",
        )
        .unwrap();
        fs.write_file(
            "/project/b.ts",
            "namespace ts { export const sys = { version: '1.0' }; }",
        )
        .unwrap();
        let program = Program::new_with_options(
            &fs,
            "/project",
            &["a.ts".to_owned(), "b.ts".to_owned()],
            CompilerOptions {
                out_file: Some("out.js".into()),
                target: ScriptTarget::Es2015,
                no_lib: true,
                ..CompilerOptions::default()
            },
        );
        let emitted = program.emit();
        assert!(emitted.diagnostics.is_empty(), "{:?}", emitted.diagnostics);
        let javascript = emitted
            .files
            .iter()
            .find(|file| file.file_name == "/project/out.js")
            .unwrap();
        assert!(
            javascript.text.contains("return ts.sys.version;"),
            "{}",
            javascript.text
        );
    }

    #[test]
    fn amd_out_file_emits_dependency_ordered_named_declaration_modules() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/Class.ts",
            concat!(
                "import { Configurable } from './Configurable';\n",
                "export class HiddenClass {}\n",
                "export class ActualClass extends Configurable(HiddenClass) {}\n",
            ),
        )
        .unwrap();
        fs.write_file(
            "/project/Configurable.ts",
            concat!(
                "export type Constructor<T = {}> = new (...args: any[]) => T;\n",
                "export function Configurable<TBase extends Constructor>(Base: TBase) { return Base; }\n",
            ),
        )
        .unwrap();

        let program = Program::new_with_module_resolution(
            &fs,
            "/project",
            &["Class.ts".to_owned()],
            ts_module::ResolutionOptions::default(),
        );
        let emitted = Program {
            options: CompilerOptions {
                declaration: true,
                out_file: Some("dist.js".into()),
                module: ModuleKind::Amd,
                target: ScriptTarget::Es2015,
                no_lib: true,
                ..CompilerOptions::default()
            },
            ..program
        }
        .emit();
        assert!(emitted.diagnostics.is_empty(), "{:?}", emitted.diagnostics);
        let declaration = emitted
            .files
            .iter()
            .find(|file| file.file_name == "/project/dist.d.ts")
            .unwrap();
        assert_eq!(
            declaration.text,
            concat!(
                "declare module \"Configurable\" {\n",
                "    export type Constructor<T = {}> = new (...args: any[]) => T;\n",
                "    export function Configurable<TBase extends Constructor>(Base: TBase): TBase;\n",
                "}\n",
                "declare module \"Class\" {\n",
                "    export class HiddenClass {\n",
                "    }\n",
                "    const ActualClass_base: typeof HiddenClass;\n",
                "    export class ActualClass extends ActualClass_base {\n",
                "    }\n",
                "}\n",
            )
        );
        let javascript = emitted
            .files
            .iter()
            .find(|file| file.file_name == "/project/dist.js")
            .unwrap();
        assert!(javascript.text.starts_with("define(\"Configurable\""));
        assert!(
            javascript
                .text
                .contains("define(\"Class\", [\"require\", \"exports\", \"Configurable\"]")
        );
    }

    #[test]
    fn system_out_file_rewrites_dependencies_and_uniquifies_wrapper_names() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file("/project/ref/a.ts", "export class A {}")
            .unwrap();
        fs.write_file(
            "/project/b.ts",
            "import { A } from './ref/a'; export class B extends A {}",
        )
        .unwrap();
        let program = Program::new_with_options(
            &fs,
            "/project",
            &["ref/a.ts".to_owned(), "b.ts".to_owned()],
            CompilerOptions {
                out_file: Some("all.js".into()),
                module: ModuleKind::System,
                target: ScriptTarget::Es2015,
                no_lib: true,
                ..CompilerOptions::default()
            },
        );
        let emitted = program.emit();
        assert!(emitted.diagnostics.is_empty(), "{:?}", emitted.diagnostics);
        let javascript = emitted
            .files
            .iter()
            .find(|file| file.file_name == "/project/all.js")
            .unwrap();
        assert!(
            javascript
                .text
                .contains("System.register(\"ref/a\", [], function (exports_1, context_1) {")
        );
        assert!(
            javascript
                .text
                .contains("System.register(\"b\", [\"ref/a\"], function (exports_2, context_2) {")
        );
    }

    #[test]
    fn amd_out_file_preserves_each_module_pragma_once_in_declarations() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/a.ts",
            "/// <amd-module name=\"NamedA\" />\nexport class Foo {}\n",
        )
        .unwrap();
        fs.write_file(
            "/project/b.ts",
            "/// <amd-module name=\"NamedB\" />\nexport class Bar {}\n",
        )
        .unwrap();
        let program = Program::new_with_options(
            &fs,
            "/project",
            &["a.ts".to_owned(), "b.ts".to_owned()],
            CompilerOptions {
                declaration: true,
                out_file: Some("out.js".into()),
                module: ModuleKind::Amd,
                target: ScriptTarget::Es2015,
                no_lib: true,
                ..CompilerOptions::default()
            },
        );
        let emitted = program.emit();
        assert!(emitted.diagnostics.is_empty(), "{:?}", emitted.diagnostics);
        let declaration = emitted
            .files
            .iter()
            .find(|file| file.file_name == "/project/out.d.ts")
            .unwrap();
        assert_eq!(
            declaration.text,
            concat!(
                "/// <amd-module name=\"NamedA\" />\n",
                "declare module \"NamedA\" {\n",
                "    export class Foo {\n",
                "    }\n",
                "}\n",
                "/// <amd-module name=\"NamedB\" />\n",
                "declare module \"NamedB\" {\n",
                "    export class Bar {\n",
                "    }\n",
                "}\n",
            )
        );
    }

    #[test]
    fn commonjs_out_file_bundles_declarations_with_late_export_names() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file("/project/index.ts", "export * from './nested';")
            .unwrap();
        fs.write_file(
            "/project/nested/base.ts",
            "import { B } from './shared'; export function f() { return new B(); }",
        )
        .unwrap();
        fs.write_file(
            "/project/nested/derived.ts",
            "import { f } from './base'; export function g() { return f(); }",
        )
        .unwrap();
        fs.write_file(
            "/project/nested/index.ts",
            "export * from './base'; export * from './derived'; export * from './shared';",
        )
        .unwrap();
        fs.write_file("/project/nested/shared.ts", "export class B {}")
            .unwrap();
        let program = Program::new_with_options(
            &fs,
            "/project",
            &["index.ts".to_owned()],
            CompilerOptions {
                declaration: true,
                emit_declaration_only: true,
                out_file: Some("dist/out.d.ts".into()),
                module: ModuleKind::CommonJs,
                target: ScriptTarget::Es2015,
                no_lib: true,
                ..CompilerOptions::default()
            },
        );
        let emitted = program.emit();
        assert!(emitted.diagnostics.is_empty(), "{:?}", emitted.diagnostics);
        let declaration = emitted
            .files
            .iter()
            .find(|file| file.file_name == "/project/dist/out.d.ts")
            .unwrap();
        assert_eq!(
            declaration.text,
            concat!(
                "declare module \"nested/shared\" {\n",
                "    export class B {\n",
                "    }\n",
                "}\n",
                "declare module \"nested/base\" {\n",
                "    import { B } from \"nested/shared\";\n",
                "    export function f(): B;\n",
                "}\n",
                "declare module \"nested/derived\" {\n",
                "    export function g(): import(\"nested\").B;\n",
                "}\n",
                "declare module \"nested/index\" {\n",
                "    export * from \"nested/base\";\n",
                "    export * from \"nested/derived\";\n",
                "    export * from \"nested/shared\";\n",
                "}\n",
                "declare module \"index\" {\n",
                "    export * from \"nested/index\";\n",
                "}\n",
            )
        );
    }

    #[test]
    fn path_mapped_ambient_return_types_emit_as_import_types() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/repo/packages/a/index.d.ts",
            concat!(
                "declare module '@scope/a' {\n",
                "    export type Result = { value: string };\n",
                "    export function create(value: string): Result;\n",
                "}\n",
            ),
        )
        .unwrap();
        fs.write_file(
            "/repo/packages/b/src/index.ts",
            concat!(
                "import { create } from '@scope/a';\n",
                "export function read(value: string) { return create(value); }\n",
            ),
        )
        .unwrap();
        let program = Program::new_with_options(
            &fs,
            "/repo/packages/b",
            &["src/index.ts".to_owned()],
            CompilerOptions {
                declaration: true,
                emit_declaration_only: true,
                base_url: Some("/repo/packages/b".into()),
                paths: BTreeMap::from([("@scope/a".into(), vec!["../a".into()])]),
                no_lib: true,
                ..CompilerOptions::default()
            },
        );
        assert!(
            program.diagnostics().is_empty(),
            "{:?}",
            program.diagnostics()
        );
        let emitted = program.emit();
        let declaration = emitted
            .files
            .iter()
            .find(|file| file.file_name.ends_with("index.d.ts"))
            .unwrap();
        assert_eq!(
            declaration.text,
            "export declare function read(value: string): import(\"@scope/a\").Result;\n"
        );
    }

    #[test]
    fn path_mapped_factory_default_export_preserves_imported_type() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/repo/packages/core/src/SvgIcon.d.ts",
            concat!(
                "export interface SomeInterface { myProp: string; }\n",
                "declare const SvgIcon: SomeInterface;\n",
                "export default SvgIcon;\n",
            ),
        )
        .unwrap();
        fs.write_file(
            "/repo/packages/core/src/utils.d.ts",
            concat!(
                "import SvgIcon from './SvgIcon';\n",
                "export function createSvgIcon(path: string, name: string): typeof SvgIcon;\n",
            ),
        )
        .unwrap();
        fs.write_file(
            "/repo/packages/lab/src/index.ts",
            concat!(
                "import { createSvgIcon } from '@scope/core/utils';\n",
                "export default createSvgIcon('Hello', 'ArrowLeft');\n",
            ),
        )
        .unwrap();
        let program = Program::new_with_options(
            &fs,
            "/repo/packages/lab",
            &["src/index.ts".to_owned()],
            CompilerOptions {
                declaration: true,
                emit_declaration_only: true,
                base_url: Some("/repo/packages".into()),
                paths: BTreeMap::from([("@scope/core/*".into(), vec!["./core/src/*".into()])]),
                no_lib: true,
                ..CompilerOptions::default()
            },
        );
        assert!(
            program.diagnostics().is_empty(),
            "{:?}",
            program.diagnostics()
        );
        let emitted = program.emit();
        let declaration = emitted
            .files
            .iter()
            .find(|file| file.file_name.ends_with("index.d.ts"))
            .unwrap();
        assert_eq!(
            declaration.text,
            concat!(
                "declare const _default: import(\"@scope/core/SvgIcon\").SomeInterface;\n",
                "export default _default;\n",
            )
        );
    }

    #[test]
    fn anonymous_mixin_heritage_preserves_constructor_object_shape() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/wrappers.ts",
            concat!(
                "export type Constructor<T = {}> = new (...args: any[]) => T;\n",
                "export function Timestamped<TBase extends Constructor>(Base: TBase) {\n",
                "    return class extends Base { timestamp: number = 1; };\n",
                "}\n",
            ),
        )
        .unwrap();
        fs.write_file(
            "/project/index.ts",
            concat!(
                "import { Timestamped } from './wrappers';\n",
                "export class User { name = ''; }\n",
                "export class TimestampedUser extends Timestamped(User) {}\n",
            ),
        )
        .unwrap();
        let program = Program::new_with_options(
            &fs,
            "/project",
            &["index.ts".to_owned()],
            CompilerOptions {
                declaration: true,
                emit_declaration_only: true,
                module: ModuleKind::CommonJs,
                target: ScriptTarget::Es2015,
                no_lib: true,
                ..CompilerOptions::default()
            },
        );
        assert!(
            program.diagnostics().is_empty(),
            "{:?}",
            program.diagnostics()
        );
        let emitted = program.emit();
        let declaration = emitted
            .files
            .iter()
            .find(|file| file.file_name == "/project/index.d.ts")
            .unwrap();
        assert!(
            declaration.text.contains(concat!(
                "declare const TimestampedUser_base: {\n",
                "    new (...args: any[]): {\n",
                "        timestamp: number;\n",
                "    };\n",
                "} & typeof User;",
            )),
            "{}",
            declaration.text
        );
    }

    #[test]
    fn bundled_export_only_imports_follow_the_export_alias() {
        assert_eq!(
            defer_export_only_bundle_imports(concat!(
                "import versions from \"versions.static\";\n",
                "export { versions };\n",
            )),
            concat!(
                "export { versions };\n",
                "import versions from \"versions.static\";\n",
            )
        );
        assert_eq!(
            defer_export_only_bundle_imports(concat!(
                "import { B } from \"shared\";\n",
                "export function make(): B;\n",
            )),
            concat!(
                "import { B } from \"shared\";\n",
                "export function make(): B;\n",
            )
        );
    }

    #[test]
    fn config_options_control_emit_and_resolution() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/tsconfig.json",
            "{ \"files\": [\"main.ts\"], \"compilerOptions\": { \"noEmit\": true, \"module\": \"esnext\", \"noLib\": true } }",
        )
        .unwrap();
        fs.write_file("/project/main.ts", "const value = 1;")
            .unwrap();
        let program = Program::from_config(&fs, "/project/tsconfig.json");
        assert!(program.diagnostics().is_empty());
        assert!(program.options().no_emit);
        assert!(program.emit().files.is_empty());
    }

    #[test]
    fn config_without_module_preserves_ecmascript_exports() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/tsconfig.json",
            r#"{"files":["main.ts"],"compilerOptions":{"target":"es2015","noLib":true}}"#,
        )
        .unwrap();
        fs.write_file("/project/main.ts", "export class Model {}")
            .unwrap();

        let program = Program::from_config(&fs, "/project/tsconfig.json");
        assert_eq!(program.options().module, ModuleKind::None);
        let javascript = &program.emit().files[0].text;
        assert!(javascript.contains("export class Model"), "{javascript}");
        assert!(!javascript.contains("exports.Model"), "{javascript}");
    }

    #[test]
    fn config_options_control_target_module_and_source_maps() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/tsconfig.json",
            "{ \"files\": [\"main.ts\"], \"compilerOptions\": { \"target\": \"es2015\", \"module\": \"commonjs\", \"sourceMap\": true, \"noLib\": true } }",
        )
        .unwrap();
        fs.write_file(
            "/project/main.ts",
            "const value = (input: number) => input; export { value };",
        )
        .unwrap();
        let program = Program::from_config(&fs, "/project/tsconfig.json");
        assert!(
            program.diagnostics().is_empty(),
            "{:?}",
            program.diagnostics()
        );
        let emitted = program.emit();
        assert!(emitted.diagnostics.is_empty());
        assert_eq!(emitted.files.len(), 2);
        let map = emitted
            .files
            .iter()
            .find(|file| file.file_name.rsplit('/').next() == Some("main.js.map"))
            .unwrap();
        assert!(
            map.text
                .starts_with("{\"version\":3,\"file\":\"main.js\",\"sourceRoot\":\"\"")
        );
        let javascript = emitted
            .files
            .iter()
            .find(|file| file.file_name.rsplit('/').next() == Some("main.js"))
            .unwrap();
        assert!(javascript.text.contains("exports.value"));
        assert!(javascript.text.contains("sourceMappingURL=main.js.map"));
    }

    #[test]
    fn config_reports_inferred_common_source_directory_on_output_option() {
        let fs = MemoryFileSystem::new(true);
        let config = concat!(
            "{\n",
            "    \"files\": [\"src/index.ts\", \"lib/globals.d.ts\"],\n",
            "    \"compilerOptions\": {\n",
            "        // \"outDir\": \"ignored\"\n",
            "        \"outDir\": \"bin\",\n",
            "        \"declaration\": true,\n",
            "        \"noLib\": true\n",
            "    }\n",
            "}\n",
        );
        fs.write_file("/app/tsconfig.json", config).unwrap();
        fs.write_file("/app/lib/globals.d.ts", "declare const outside: number;")
            .unwrap();
        fs.write_file("/app/src/index.ts", "export const value: number = 1;")
            .unwrap();

        let program = Program::from_config(&fs, "/app/tsconfig.json");
        let [diagnostic] = program.diagnostics() else {
            panic!(
                "expected one inferred root diagnostic: {:?}",
                program.diagnostics()
            )
        };
        let start = u32::try_from(config.rfind("\"outDir\"").unwrap()).unwrap();
        assert_eq!(diagnostic.code, Some(5011));
        assert_eq!(diagnostic.file_name.as_deref(), Some("/app/tsconfig.json"));
        assert_eq!(
            diagnostic.range,
            Some(TextRange::new(TextPos::new(start), TextPos::new(start + 8)))
        );
        assert_eq!(
            diagnostic.message,
            concat!(
                "The common source directory of 'tsconfig.json' is './src'. ",
                "The 'rootDir' setting must be explicitly set to this or another path ",
                "to adjust your output's file layout.\n",
                "  Visit https://aka.ms/ts6 for migration information.",
            )
        );
    }

    #[test]
    fn canonical_config_reports_inferred_common_source_directory() {
        let fs = MemoryFileSystem::new(true);
        let config = "{\"compilerOptions\":{\"outDir\":\"bin\"}}";
        fs.write_file("/app/tsconfig.json", config).unwrap();
        fs.write_file("/app/src/index.ts", "export const value: number = 1;")
            .unwrap();

        let program = Program::try_new_with_canonical_checker_with_config_path(
            &fs,
            "/app",
            &["src/index.ts".to_owned()],
            CompilerOptions {
                lib: Some(vec!["es5".to_owned()]),
                out_dir: Some("/app/bin".to_owned()),
                root_dir: Some("/app".to_owned()),
                ..CompilerOptions::default()
            },
            Some("/app/tsconfig.json"),
        )
        .unwrap();

        let [diagnostic] = program.diagnostics() else {
            panic!(
                "expected one canonical root diagnostic: {:?}",
                program.diagnostics()
            )
        };
        assert_eq!(diagnostic.code, Some(5011));
        let range = diagnostic.range.unwrap();
        assert_eq!(
            &config[range.start.get() as usize..range.end.get() as usize],
            "\"outDir\""
        );
    }

    #[test]
    fn common_source_directory_diagnostic_respects_project_output_guards() {
        for (extra, file_name) in [
            (", \"rootDir\": \"src\"", "src/index.ts"),
            (", \"noEmit\": true", "src/index.ts"),
            (", \"composite\": true", "src/index.ts"),
            ("", "index.ts"),
        ] {
            let fs = MemoryFileSystem::new(true);
            fs.write_file(
                "/app/tsconfig.json",
                &format!(
                    "{{\"files\":[\"{file_name}\"],\"compilerOptions\":{{\"outDir\":\"bin\",\"noLib\":true{extra}}}}}"
                ),
            )
            .unwrap();
            fs.write_file(
                &format!("/app/{file_name}"),
                "export const value: number = 1;",
            )
            .unwrap();

            let program = Program::from_config(&fs, "/app/tsconfig.json");
            assert!(
                program
                    .diagnostics()
                    .iter()
                    .all(|diagnostic| diagnostic.code != Some(5011)),
                "{file_name} with {extra}: {:?}",
                program.diagnostics(),
            );
        }
    }

    #[test]
    fn out_dir_and_root_dir_preserve_source_structure() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/tsconfig.json",
            r#"{
                "files": ["src/main.ts", "src/nested/other.ts"],
                "compilerOptions": {
                    "outDir": "build",
                    "rootDir": "src",
                    "sourceMap": true,
                    "noLib": true
                }
            }"#,
        )
        .unwrap();
        fs.write_file("/project/src/main.ts", "const main = 1;")
            .unwrap();
        fs.write_file("/project/src/nested/other.ts", "const other = 2;")
            .unwrap();
        let program = Program::from_config(&fs, "/project/tsconfig.json");
        let emitted = program.emit();
        let paths = emitted
            .files
            .iter()
            .map(|file| file.file_name.as_str())
            .collect::<Vec<_>>();
        assert!(paths.contains(&"/project/build/main.js"));
        assert!(paths.contains(&"/project/build/main.js.map"));
        assert!(paths.contains(&"/project/build/nested/other.js"));
        assert!(paths.contains(&"/project/build/nested/other.js.map"));
    }

    #[test]
    fn inline_source_maps_are_embedded_without_map_files() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/tsconfig.json",
            r#"{
                "files": ["src/main.ts"],
                "compilerOptions": {
                    "outDir": "build",
                    "mapRoot": "maps",
                    "inlineSourceMap": true,
                    "noLib": true
                }
            }"#,
        )
        .unwrap();
        fs.write_file("/project/src/main.ts", "const main = 1;")
            .unwrap();
        let program = Program::from_config(&fs, "/project/tsconfig.json");
        assert_eq!(
            program
                .logical_source_map_path("/project/build/src/main.js.map")
                .as_deref(),
            Some("/project/maps/src/main.js.map")
        );
        let emitted = program.emit();
        assert_eq!(emitted.files.len(), 1);
        assert_eq!(emitted.files[0].file_name, "/project/build/src/main.js");
        assert!(
            emitted.files[0]
                .text
                .contains("sourceMappingURL=data:application/json;base64,")
        );
    }

    #[test]
    fn emits_declarations_and_declaration_maps_to_declaration_dir() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/tsconfig.json",
            r#"{
                "files": ["src/api.mts"],
                "compilerOptions": {
                    "outDir": "dist",
                    "rootDir": "src",
                    "declaration": true,
                    "declarationMap": true,
                    "declarationDir": "types",
                    "noLib": true
                }
            }"#,
        )
        .unwrap();
        fs.write_file(
            "/project/src/api.mts",
            r"
                export const version: number = 1;
                export function identity<T>(value: T): T { return value; }
                export interface Box<T> { value: T; }
                export type Maybe<T> = T | undefined;
                export enum Color { Red, Blue = 2 }
            ",
        )
        .unwrap();
        let program = Program::from_config(&fs, "/project/tsconfig.json");
        assert!(
            program.diagnostics().is_empty(),
            "{:?}",
            program.diagnostics()
        );
        let emitted = program.emit();
        assert!(emitted.diagnostics.is_empty(), "{:?}", emitted.diagnostics);
        let declaration = emitted
            .files
            .iter()
            .find(|file| file.file_name == "/project/types/api.d.mts")
            .unwrap();
        assert_eq!(
            declaration.text,
            "export declare const version: number;\nexport declare function identity<T>(value: T): T;\nexport interface Box<T> {\n    value: T;\n}\nexport type Maybe<T> = T | undefined;\nexport declare enum Color {\n    Red = 0,\n    Blue = 2\n}\n//# sourceMappingURL=api.d.mts.map"
        );
        assert!(
            emitted
                .files
                .iter()
                .any(|file| file.file_name == "/project/types/api.d.mts.map")
        );
        assert!(
            emitted
                .files
                .iter()
                .any(|file| file.file_name == "/project/dist/api.mjs")
        );
    }

    #[test]
    fn declaration_emit_consumes_reachable_private_declarations() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/main.ts",
            "type T = { x: number }; export interface I { f: T; }",
        )
        .unwrap();
        let program = Program::new_with_options(
            &fs,
            "/project",
            &["main.ts".to_owned()],
            CompilerOptions {
                declaration: true,
                module: ModuleKind::CommonJs,
                target: ScriptTarget::Es2015,
                no_emit_on_error: true,
                no_lib: true,
                ..CompilerOptions::default()
            },
        );
        let emitted = program.emit();
        assert!(emitted.diagnostics.is_empty(), "{:?}", emitted.diagnostics);
        let declaration = emitted
            .files
            .iter()
            .find(|file| file.file_name == "/project/main.d.ts")
            .unwrap();
        assert_eq!(
            declaration.text,
            concat!(
                "type T = {\n",
                "    x: number;\n",
                "};\n",
                "export interface I {\n",
                "    f: T;\n",
                "}\n",
                "export {};\n",
            )
        );

        for (source, expected) in [
            (
                "namespace M { namespace N {} export import X = N; }",
                concat!(
                    "declare namespace M {\n",
                    "    namespace N {\n",
                    "    }\n",
                    "    export import X = N;\n",
                    "    export {};\n",
                    "}\n",
                ),
            ),
            (
                "namespace M { namespace N { class C {} } import R = N; export import X = R; }",
                concat!(
                    "declare namespace M {\n",
                    "    namespace N {\n",
                    "    }\n",
                    "    import R = N;\n",
                    "    export import X = R;\n",
                    "    export {};\n",
                    "}\n",
                ),
            ),
            (
                "namespace M { class C {} export var value: C = new C(); }",
                concat!(
                    "declare namespace M {\n",
                    "    class C {\n",
                    "    }\n",
                    "    export var value: C;\n",
                    "    export {};\n",
                    "}\n",
                ),
            ),
        ] {
            let fs = MemoryFileSystem::new(true);
            fs.write_file("/project/alias.ts", source).unwrap();
            let program = Program::new_with_options(
                &fs,
                "/project",
                &["alias.ts".to_owned()],
                CompilerOptions {
                    declaration: true,
                    module: ModuleKind::None,
                    target: ScriptTarget::Es2015,
                    no_lib: true,
                    ..CompilerOptions::default()
                },
            );
            let emitted = program.emit();
            assert!(emitted.diagnostics.is_empty(), "{:?}", emitted.diagnostics);
            let declaration = emitted
                .files
                .iter()
                .find(|file| file.file_name == "/project/alias.d.ts")
                .unwrap();
            assert_eq!(declaration.text, expected);
        }
    }

    #[test]
    fn declaration_emit_spreads_imported_type_only_alias_shape() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/type.ts",
            "export type Type = { x?: { [Enum.A]: 0 } };",
        )
        .unwrap();
        fs.write_file(
            "/project/index.ts",
            "import { type Type } from './type'; export const foo = { ...({} as Type) };",
        )
        .unwrap();
        let program = Program::new_with_options(
            &fs,
            "/project",
            &["type.ts".to_owned(), "index.ts".to_owned()],
            CompilerOptions {
                declaration: true,
                emit_declaration_only: true,
                target: ScriptTarget::Es2015,
                no_lib: true,
                ..CompilerOptions::default()
            },
        );
        let index = program
            .source_files
            .iter()
            .find(|source| source.file_name == "/project/index.ts")
            .unwrap();
        let symbol = index
            .binding
            .root_scope()
            .unwrap()
            .symbols
            .get("foo")
            .unwrap();
        let type_id = index.checking.type_of_symbol(symbol).unwrap();
        assert_eq!(
            index
                .checking
                .type_of_node(index.binding.symbols.get(symbol).unwrap().declarations[0]),
            Some(type_id)
        );
        assert!(
            matches!(
                index.checking.types.get(type_id).map(|type_| &type_.kind),
                Some(ts_checker::TypeKind::Object(object)) if object.properties.contains_key("x")
            ),
            "{}",
            index.checking.types.display(type_id)
        );
        let emitted = program.emit();
        let declaration = emitted
            .files
            .iter()
            .find(|file| file.file_name == "/project/index.d.ts")
            .unwrap();
        assert!(declaration.text.contains("x?:"), "{}", declaration.text);
    }

    #[test]
    fn declaration_emit_preserves_cross_module_default_type_identity() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/color.ts",
            "interface Color { c: string; } export default Color;",
        )
        .unwrap();
        fs.write_file(
            "/project/file1.ts",
            "import Color from './color'; export declare function styled(): Color;",
        )
        .unwrap();
        fs.write_file(
            "/project/file2.ts",
            "import { styled } from './file1'; export const A = styled();",
        )
        .unwrap();
        let program = Program::new_with_options(
            &fs,
            "/project",
            &["color.ts".into(), "file1.ts".into(), "file2.ts".into()],
            CompilerOptions {
                declaration: true,
                module: ModuleKind::CommonJs,
                target: ScriptTarget::Es2015,
                no_lib: true,
                ..CompilerOptions::default()
            },
        );
        let emitted = program.emit();
        assert!(emitted.diagnostics.is_empty(), "{:?}", emitted.diagnostics);
        let declaration = emitted
            .files
            .iter()
            .find(|file| file.file_name == "/project/file2.d.ts")
            .unwrap();
        assert_eq!(
            declaration.text,
            "export declare const A: import(\"./color\").default;\n"
        );
    }

    #[test]
    fn namespace_alias_runtime_emit_tracks_instantiation_and_source_order() {
        for (source, expected) in [
            (
                "namespace M { namespace N {} export import X = N; }",
                "\"use strict\";\nvar M;\n(function (M) {\n})(M || (M = {}));\n",
            ),
            (
                "namespace M { namespace N { class C {} } import R = N; export import X = R; }",
                concat!(
                    "\"use strict\";\n",
                    "var M;\n",
                    "(function (M) {\n",
                    "    let N;\n",
                    "    (function (N) {\n",
                    "        class C {\n",
                    "        }\n",
                    "    })(N || (N = {}));\n",
                    "    var R = N;\n",
                    "    M.X = R;\n",
                    "})(M || (M = {}));\n",
                ),
            ),
        ] {
            let fs = MemoryFileSystem::new(true);
            fs.write_file("/project/alias.ts", source).unwrap();
            let program = Program::new_with_options(
                &fs,
                "/project",
                &["alias.ts".to_owned()],
                CompilerOptions {
                    module: ModuleKind::None,
                    target: ScriptTarget::Es2015,
                    no_lib: true,
                    ..CompilerOptions::default()
                },
            );
            let emitted = program.emit();
            assert!(emitted.diagnostics.is_empty(), "{:?}", emitted.diagnostics);
            let javascript = emitted
                .files
                .iter()
                .find(|file| file.file_name == "/project/alias.js")
                .unwrap();
            assert_eq!(javascript.text, expected);
        }
    }

    #[test]
    fn declaration_emit_uses_evaluated_const_enum_values() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/enum.ts",
            concat!(
                "const enum E {\n",
                "    a = 10, b = a, c = (a + 1), e, d = ~e,\n",
                "    f = a << 2 >> 1, g = a << 2 >>> 1, h = a | b\n",
                "}\n",
            ),
        )
        .unwrap();
        let program = Program::new_with_options(
            &fs,
            "/project",
            &["enum.ts".to_owned()],
            CompilerOptions {
                declaration: true,
                target: ScriptTarget::Es2015,
                no_lib: true,
                ..CompilerOptions::default()
            },
        );
        let emitted = program.emit();
        let javascript = emitted
            .files
            .iter()
            .find(|file| file.file_name == "/project/enum.js")
            .unwrap();
        assert_eq!(javascript.text, "\"use strict\";\n");
        let declaration = emitted
            .files
            .iter()
            .find(|file| file.file_name == "/project/enum.d.ts")
            .unwrap();
        assert_eq!(
            declaration.text,
            concat!(
                "declare const enum E {\n",
                "    a = 10,\n",
                "    b = 10,\n",
                "    c = 11,\n",
                "    e = 12,\n",
                "    d = -13,\n",
                "    f = 20,\n",
                "    g = 20,\n",
                "    h = 10\n",
                "}\n",
            )
        );
    }

    #[test]
    fn emit_declaration_only_suppresses_javascript() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/tsconfig.json",
            r#"{
                "files": ["src/index.ts"],
                "compilerOptions": { "outDir": "types", "declaration": true, "emitDeclarationOnly": true, "noLib": true }
            }"#,
        )
        .unwrap();
        fs.write_file(
            "/project/src/index.ts",
            "export const value: string = 'ok';",
        )
        .unwrap();
        let program = Program::from_config(&fs, "/project/tsconfig.json");
        let emitted = program.emit();
        assert_eq!(emitted.files.len(), 1);
        assert_eq!(emitted.files[0].file_name, "/project/types/src/index.d.ts");
        assert_eq!(
            emitted.files[0].text,
            "export declare const value: string;\n"
        );
    }

    #[test]
    fn emit_declaration_only_requires_declaration_or_composite() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file("/project/index.ts", "var hello = 'yo!';")
            .unwrap();
        let program = Program::new_with_options(
            &fs,
            "/project",
            &["index.ts".to_owned()],
            CompilerOptions {
                emit_declaration_only: true,
                no_lib: true,
                ..CompilerOptions::default()
            },
        );
        assert_eq!(
            program
                .diagnostics()
                .iter()
                .filter_map(|diagnostic| diagnostic.code)
                .collect::<Vec<_>>(),
            [5069]
        );
        assert!(program.emit().files.is_empty());
    }

    #[test]
    fn incremental_compilation_requires_known_project_or_build_info() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file("/project/index.ts", "const value = 1;")
            .unwrap();
        let invalid = Program::new_with_options(
            &fs,
            "/project",
            &["index.ts".to_owned()],
            CompilerOptions {
                incremental: true,
                incremental_specified: true,
                no_check: true,
                no_lib: true,
                ..CompilerOptions::default()
            },
        );
        let [diagnostic] = invalid.diagnostics() else {
            panic!(
                "expected one incremental diagnostic: {:?}",
                invalid.diagnostics()
            )
        };
        assert_eq!(diagnostic.code, Some(5074));
        assert_eq!(
            diagnostic.message,
            "Option '--incremental' is only valid with a known configuration file (like 'tsconfig.json') or when '--tsBuildInfoFile' is explicitly provided.",
        );

        let explicit = Program::new_with_options(
            &fs,
            "/project",
            &["index.ts".to_owned()],
            CompilerOptions {
                incremental: true,
                incremental_specified: true,
                ts_build_info_file: Some("/project/cache.tsbuildinfo".to_owned()),
                no_check: true,
                no_lib: true,
                ..CompilerOptions::default()
            },
        );
        assert!(
            explicit.diagnostics().is_empty(),
            "{:?}",
            explicit.diagnostics()
        );

        fs.write_file(
            "/project/tsconfig.json",
            concat!(
                "{\"files\":[\"index.ts\"],\"compilerOptions\":{",
                "\"incremental\":true,\"noCheck\":true,\"noLib\":true}}",
            ),
        )
        .unwrap();
        let configured = Program::from_config(&fs, "/project/tsconfig.json");
        assert!(
            configured.diagnostics().is_empty(),
            "{:?}",
            configured.diagnostics(),
        );
    }

    #[test]
    fn declaration_only_config_diagnostics_are_located_once_without_checking() {
        let fs = MemoryFileSystem::new(true);
        let config = concat!(
            "{\n",
            "  \"files\": [\"index.ts\"],\n",
            "  \"compilerOptions\": {\n",
            "    \"emitDeclarationOnly\": true,\n",
            "    \"noCheck\": true,\n",
            "    \"noEmit\": true,\n",
            "    \"noLib\": true\n",
            "  }\n",
            "}\n",
        );
        fs.write_file("/project/tsconfig.json", config).unwrap();
        fs.write_file("/project/index.ts", "export const value: number = 'wrong';")
            .unwrap();

        let program = Program::from_config(&fs, "/project/tsconfig.json");
        let [diagnostic] = program.diagnostics() else {
            panic!(
                "expected one declaration-only diagnostic: {:?}",
                program.diagnostics()
            )
        };
        assert_eq!(diagnostic.code, Some(5069));
        let range = diagnostic.range.unwrap();
        assert_eq!(
            &config[usize::try_from(range.start.get()).unwrap()
                ..usize::try_from(range.end.get()).unwrap()],
            "\"emitDeclarationOnly\"",
        );
    }

    #[test]
    fn invalid_jsx_option_diagnostics_use_exact_config_value_ranges() {
        for (options, code, value) in [
            (
                "\"jsxFactory\": \"Element.createElement=\"",
                5067,
                "\"Element.createElement=\"",
            ),
            (
                "\"reactNamespace\": \"my-React-Lib\"",
                5059,
                "\"my-React-Lib\"",
            ),
            (
                "\"jsxFactory\": \"h\", \"jsxFragmentFactory\": \"234\"",
                18_035,
                "\"234\"",
            ),
        ] {
            let fs = MemoryFileSystem::new(true);
            let config = format!(
                "{{\"files\":[\"index.ts\"],\"compilerOptions\":{{{options},\"noLib\":true}}}}",
            );
            fs.write_file("/project/tsconfig.json", &config).unwrap();
            fs.write_file("/project/index.ts", "export {};").unwrap();

            let program = Program::from_config(&fs, "/project/tsconfig.json");
            let [diagnostic] = program.diagnostics() else {
                panic!("expected one JSX diagnostic: {:?}", program.diagnostics())
            };
            assert_eq!(diagnostic.code, Some(code));
            let range = diagnostic.range.unwrap();
            assert_eq!(
                &config[usize::try_from(range.start.get()).unwrap()
                    ..usize::try_from(range.end.get()).unwrap()],
                value,
            );
        }
    }

    #[test]
    fn typescript_extension_import_diagnostic_uses_boolean_config_value() {
        for (rewrite, expected) in [(false, Some(5096)), (true, None)] {
            let fs = MemoryFileSystem::new(true);
            let config = serde_json::json!({
                "files": ["index.ts"],
                "compilerOptions": {
                    "allowImportingTsExtensions": true,
                    "rewriteRelativeImportExtensions": rewrite,
                    "noCheck": true,
                    "noLib": true,
                },
            })
            .to_string();
            fs.write_file("/project/tsconfig.json", &config).unwrap();
            fs.write_file("/project/index.ts", "export {};").unwrap();

            let program = Program::from_config(&fs, "/project/tsconfig.json");
            let diagnostic = program.diagnostics().first();
            assert_eq!(diagnostic.and_then(|diagnostic| diagnostic.code), expected);
            if let Some(diagnostic) = diagnostic {
                let range = diagnostic.range.unwrap();
                assert_eq!(
                    &config[usize::try_from(range.start.get()).unwrap()
                        ..usize::try_from(range.end.get()).unwrap()],
                    "true",
                );
            }
        }
    }

    #[test]
    fn config_option_diagnostics_follow_source_span_order() {
        let fs = MemoryFileSystem::new(true);
        let config = concat!(
            "{\n",
            "  \"files\": [\"index.ts\"],\n",
            "  \"compilerOptions\": {\n",
            "    \"jsx\": \"react-jsx\",\n",
            "    \"jsxFragmentFactory\": \"234\",\n",
            "    \"jsxFactory\": \"h\",\n",
            "    \"noEmit\": true,\n",
            "    \"noLib\": true\n",
            "  }\n",
            "}\n",
        );
        fs.write_file("/project/tsconfig.json", config).unwrap();
        fs.write_file("/project/index.ts", "export {};").unwrap();

        let program = Program::from_config(&fs, "/project/tsconfig.json");
        assert_eq!(
            program
                .diagnostics()
                .iter()
                .filter_map(|diagnostic| diagnostic.code)
                .collect::<Vec<_>>(),
            [5089, 18_035, 5089],
        );
        let spans = program
            .diagnostics()
            .iter()
            .map(|diagnostic| {
                let range = diagnostic.range.unwrap();
                &config[usize::try_from(range.start.get()).unwrap()
                    ..usize::try_from(range.end.get()).unwrap()]
            })
            .collect::<Vec<_>>();
        assert_eq!(
            spans,
            ["\"jsxFragmentFactory\"", "\"234\"", "\"jsxFactory\""]
        );
    }

    #[test]
    fn missing_node_module_kind_falls_back_to_compiler_options_config_key() {
        let fs = MemoryFileSystem::new(true);
        let config = concat!(
            "{\n",
            "  \"files\": [\"index.ts\"],\n",
            "  \"compilerOptions\": {\n",
            "    \"moduleResolution\": \"nodenext\",\n",
            "    \"noEmit\": true,\n",
            "    \"noLib\": true\n",
            "  }\n",
            "}\n",
        );
        fs.write_file("/project/tsconfig.json", config).unwrap();
        fs.write_file("/project/index.ts", "export {};").unwrap();

        let program = Program::from_config(&fs, "/project/tsconfig.json");
        let [diagnostic] = program.diagnostics() else {
            panic!(
                "expected one missing-module diagnostic: {:?}",
                program.diagnostics()
            )
        };
        assert_eq!(diagnostic.code, Some(5110));
        let range = diagnostic.range.unwrap();
        assert_eq!(
            &config[usize::try_from(range.start.get()).unwrap()
                ..usize::try_from(range.end.get()).unwrap()],
            "\"compilerOptions\"",
        );
    }

    #[test]
    fn declaration_directory_diagnostic_retains_exact_config_key_range() {
        let fs = MemoryFileSystem::new(true);
        let config = concat!(
            "{\n",
            "  \"files\": [\"index.ts\"],\n",
            "  \"compilerOptions\": { \"declarationDir\": \"out\", \"noLib\": true }\n",
            "}\n",
        );
        fs.write_file("/project/tsconfig.json", config).unwrap();
        fs.write_file("/project/index.ts", "export {};").unwrap();

        let program = Program::from_config(&fs, "/project/tsconfig.json");
        let [diagnostic] = program.diagnostics() else {
            panic!(
                "expected one declaration-directory diagnostic: {:?}",
                program.diagnostics()
            )
        };
        assert_eq!(diagnostic.code, Some(5069));
        assert_eq!(
            diagnostic.file_name.as_deref(),
            Some("/project/tsconfig.json")
        );
        assert_eq!(
            diagnostic.message,
            "Option 'declarationDir' cannot be specified without specifying option 'declaration' or option 'composite'.",
        );
        let range = diagnostic.range.unwrap();
        assert_eq!(
            &config[usize::try_from(range.start.get()).unwrap()
                ..usize::try_from(range.end.get()).unwrap()],
            "\"declarationDir\"",
        );
    }

    #[test]
    fn incompatible_bundler_diagnostics_retain_config_value_ranges_and_order() {
        let fs = MemoryFileSystem::new(true);
        let config = concat!(
            "{\n",
            "  \"files\": [\"index.ts\"],\n",
            "  \"compilerOptions\": {\n",
            "    \"module\": \"nodenext\",\n",
            "    \"moduleResolution\": \"bundler\",\n",
            "    \"noEmit\": true,\n",
            "    \"noLib\": true\n",
            "  }\n",
            "}\n",
        );
        fs.write_file("/project/tsconfig.json", config).unwrap();
        fs.write_file("/project/index.ts", "export {};").unwrap();

        let program = Program::from_config(&fs, "/project/tsconfig.json");
        assert_eq!(
            program
                .diagnostics()
                .iter()
                .filter_map(|diagnostic| diagnostic.code)
                .collect::<Vec<_>>(),
            [5095, 5109],
        );
        for diagnostic in program.diagnostics() {
            assert_eq!(
                diagnostic.file_name.as_deref(),
                Some("/project/tsconfig.json")
            );
            let range = diagnostic.range.unwrap();
            assert_eq!(
                &config[usize::try_from(range.start.get()).unwrap()
                    ..usize::try_from(range.end.get()).unwrap()],
                "\"bundler\"",
            );
        }
    }

    #[test]
    fn config_loads_target_default_libraries_without_emitting_them() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/tsconfig.json",
            r#"{
                "files": ["main.ts"],
                "compilerOptions": { "target": "es2015" }
            }"#,
        )
        .unwrap();
        fs.write_file("/project/main.ts", "Array; Promise;")
            .unwrap();
        let program = Program::from_config(&fs, "/project/tsconfig.json");
        assert!(
            !program
                .diagnostics()
                .iter()
                .any(|diagnostic| diagnostic.code == Some(2304))
        );
        assert!(
            program.source_files().iter().any(|file| {
                file.is_default_library && file.file_name.ends_with("/lib.es6.d.ts")
            })
        );
        let emitted = program.emit();
        assert!(
            emitted
                .files
                .iter()
                .all(|file| !file.file_name.contains("/__typescript/lib/"))
        );
    }

    #[test]
    fn no_lib_removes_default_library_globals() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/tsconfig.json",
            r#"{
                "files": ["main.ts"],
                "compilerOptions": { "noLib": true }
            }"#,
        )
        .unwrap();
        fs.write_file("/project/main.ts", "Array; Promise;")
            .unwrap();
        let program = Program::from_config(&fs, "/project/tsconfig.json");
        assert_eq!(
            program
                .diagnostics()
                .iter()
                .filter(|diagnostic| diagnostic.code == Some(2304))
                .count(),
            2
        );
        assert!(
            !program
                .source_files()
                .iter()
                .any(|file| file.is_default_library)
        );
    }

    #[test]
    fn explicit_lib_overrides_target_default_selection() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/tsconfig.json",
            r#"{
                "files": ["main.ts"],
                "compilerOptions": {
                    "target": "es5",
                    "lib": ["es5", "es2015.promise"]
                }
            }"#,
        )
        .unwrap();
        fs.write_file("/project/main.ts", "Array; Promise;")
            .unwrap();
        let program = Program::from_config(&fs, "/project/tsconfig.json");
        assert!(
            !program
                .diagnostics()
                .iter()
                .any(|diagnostic| diagnostic.code == Some(2304))
        );
        assert!(program.source_files().iter().any(|file| {
            file.is_default_library && file.file_name.ends_with("/lib.es2015.promise.d.ts")
        }));
        assert!(
            !program.source_files().iter().any(|file| {
                file.is_default_library && file.file_name.ends_with("/lib.dom.d.ts")
            })
        );
    }

    #[test]
    fn target_selects_distinct_default_library_roots() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file("/project/main.ts", "Array;").unwrap();
        let es5 = Program::new_with_options(
            &fs,
            "/project",
            &["main.ts".to_owned()],
            CompilerOptions {
                target: ts_options::ScriptTarget::Es5,
                ..CompilerOptions::default()
            },
        );
        let es2015 = Program::new_with_options(
            &fs,
            "/project",
            &["main.ts".to_owned()],
            CompilerOptions {
                target: ts_options::ScriptTarget::Es2015,
                ..CompilerOptions::default()
            },
        );
        assert!(
            es5.source_files()
                .iter()
                .any(|file| { file.is_default_library && file.file_name.ends_with("/lib.d.ts") })
        );
        assert!(
            es2015.source_files().iter().any(|file| {
                file.is_default_library && file.file_name.ends_with("/lib.es6.d.ts")
            })
        );
    }

    #[test]
    fn checks_core_default_library_array_and_promise_generics() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/tsconfig.json",
            r#"{
                "files": ["main.ts"],
                "compilerOptions": { "target": "es2015", "lib": ["es5"] }
            }"#,
        )
        .unwrap();
        fs.write_file(
            "/project/main.ts",
            r#"
                const values: Array<number> = [1, 2];
                const wrongElement: string = values[0];
                values.push("wrong");
                const wrongMap: Array<string> = values.map(value => value + 1);

                let promise: PromiseLike<number>;
                promise.then((value: string) => value);
            "#,
        )
        .unwrap();
        let program = Program::from_config(&fs, "/project/tsconfig.json");
        assert_eq!(
            program
                .diagnostics()
                .iter()
                .filter_map(|diagnostic| diagnostic.code)
                .collect::<Vec<_>>(),
            // Oracle-verified under default-on strict: the unassigned
            // `promise` read adds TS2454.
            [2322, 2345, 2322, 2454, 2345]
        );
    }

    #[test]
    fn checks_core_default_library_within_debug_budget() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/tsconfig.json",
            r#"{
                "files": ["main.ts"],
                "compilerOptions": { "target": "es5", "lib": ["es5"] }
            }"#,
        )
        .unwrap();
        fs.write_file(
            "/project/main.ts",
            "const values: Array<number> = [1, 2, 3]; values.map(value => value + 1);",
        )
        .unwrap();
        let started = Instant::now();
        let program = Program::from_config(&fs, "/project/tsconfig.json");
        let elapsed = started.elapsed();
        assert!(
            program.diagnostics().is_empty(),
            "{:?}",
            program.diagnostics()
        );
        assert!(
            elapsed < Duration::from_secs(2),
            "cold debug default-library check took {elapsed:?}"
        );
    }

    #[test]
    fn retains_strict_function_types_configuration_for_checker_construction() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file("/project/main.ts", "const value = 1;")
            .unwrap();

        fs.write_file(
            "/project/tsconfig.json",
            r#"{
                "files": ["main.ts"],
                "compilerOptions": { "noLib": true }
            }"#,
        )
        .unwrap();
        let defaults = Program::from_config(&fs, "/project/tsconfig.json");
        assert!(defaults.options().strict_function_types);
        assert!(!defaults.options().strict_function_types_specified);

        fs.write_file(
            "/project/tsconfig.json",
            r#"{
                "files": ["main.ts"],
                "compilerOptions": { "noLib": true, "strict": false }
            }"#,
        )
        .unwrap();
        let inherited = Program::from_config(&fs, "/project/tsconfig.json");
        assert!(!inherited.options().strict_function_types);
        assert!(!inherited.options().strict_function_types_specified);

        fs.write_file(
            "/project/tsconfig.json",
            r#"{
                "files": ["main.ts"],
                "compilerOptions": {
                    "noLib": true,
                    "strict": false,
                    "strictFunctionTypes": true
                }
            }"#,
        )
        .unwrap();
        let overridden = Program::from_config(&fs, "/project/tsconfig.json");
        assert!(overridden.options().strict_function_types);
        assert!(overridden.options().strict_function_types_specified);
    }

    #[test]
    fn enforces_strict_null_checks() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/tsconfig.json",
            r#"{
                "files": ["main.ts"],
                "compilerOptions": { "noLib": true, "strictNullChecks": true }
            }"#,
        )
        .unwrap();
        fs.write_file(
            "/project/main.ts",
            "const text: string = null; const count: number = null;",
        )
        .unwrap();
        let strict = Program::from_config(&fs, "/project/tsconfig.json");
        assert_eq!(
            strict
                .diagnostics()
                .iter()
                .filter_map(|diagnostic| diagnostic.code)
                .collect::<Vec<_>>(),
            [2322, 2322]
        );

        fs.write_file(
            "/project/tsconfig.json",
            r#"{
                "files": ["main.ts"],
                "compilerOptions": { "noLib": true, "strictNullChecks": false }
            }"#,
        )
        .unwrap();
        let loose = Program::from_config(&fs, "/project/tsconfig.json");
        assert!(loose.diagnostics().is_empty(), "{:?}", loose.diagnostics());
    }

    #[test]
    fn enforces_exact_optional_property_types_from_config() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/tsconfig.json",
            r#"{
                "files": ["main.ts"],
                "compilerOptions": {
                    "noLib": true,
                    "strictNullChecks": true,
                    "exactOptionalPropertyTypes": true
                }
            }"#,
        )
        .unwrap();
        fs.write_file(
            "/project/main.ts",
            "declare function take(value: { text?: string }): void; take({ text: undefined });",
        )
        .unwrap();
        let program = Program::from_config(&fs, "/project/tsconfig.json");
        assert_eq!(
            program
                .diagnostics()
                .iter()
                .filter_map(|diagnostic| diagnostic.code)
                .collect::<Vec<_>>(),
            [2379]
        );

        fs.write_file(
            "/project/tsconfig.json",
            r#"{
                "files": ["main.ts"],
                "compilerOptions": {
                    "noLib": true,
                    "strict": false,
                    "exactOptionalPropertyTypes": true
                }
            }"#,
        )
        .unwrap();
        let invalid = Program::from_config(&fs, "/project/tsconfig.json");
        assert_eq!(
            invalid
                .diagnostics()
                .iter()
                .filter_map(|diagnostic| diagnostic.code)
                .collect::<Vec<_>>(),
            [5052]
        );
    }

    #[test]
    fn checks_delete_operands_with_exact_optional_property_types() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/main.ts",
            r"
                interface Model {
                    required: number;
                    includesUndefined: number | undefined;
                    optional?: number;
                }
                declare const model: Model;
                delete model.required;
                delete model.includesUndefined;
                delete model.optional;
            ",
        )
        .unwrap();
        fs.write_file(
            "/project/tsconfig.json",
            r#"{
                "files": ["main.ts"],
                "compilerOptions": {
                    "noLib": true,
                    "strictNullChecks": true,
                    "exactOptionalPropertyTypes": true
                }
            }"#,
        )
        .unwrap();
        let exact = Program::from_config(&fs, "/project/tsconfig.json");
        assert_eq!(
            exact
                .diagnostics()
                .iter()
                .filter_map(|diagnostic| diagnostic.code)
                .collect::<Vec<_>>(),
            [2790, 2790]
        );

        fs.write_file(
            "/project/tsconfig.json",
            r#"{
                "files": ["main.ts"],
                "compilerOptions": {
                    "noLib": true,
                    "strictNullChecks": true,
                    "exactOptionalPropertyTypes": false
                }
            }"#,
        )
        .unwrap();
        let legacy = Program::from_config(&fs, "/project/tsconfig.json");
        assert_eq!(
            legacy
                .diagnostics()
                .iter()
                .filter_map(|diagnostic| diagnostic.code)
                .collect::<Vec<_>>(),
            [2790]
        );
    }

    #[test]
    fn reports_contextual_exact_optional_diagnostic_codes() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/main.ts",
            r"
                interface Options { text?: string; }
                declare let options: Options;
                options.text = undefined;
                const initialized: Options = { text: undefined };
                declare function take(value: Options): void;
                take({ text: undefined });
            ",
        )
        .unwrap();
        fs.write_file(
            "/project/tsconfig.json",
            r#"{
                "files": ["main.ts"],
                "compilerOptions": {
                    "noLib": true,
                    "strictNullChecks": true,
                    "exactOptionalPropertyTypes": true
                }
            }"#,
        )
        .unwrap();
        let exact = Program::from_config(&fs, "/project/tsconfig.json");
        assert_eq!(
            exact
                .diagnostics()
                .iter()
                .filter_map(|diagnostic| diagnostic.code)
                .collect::<Vec<_>>(),
            [2412, 2375, 2379]
        );

        fs.write_file(
            "/project/tsconfig.json",
            r#"{
                "files": ["main.ts"],
                "compilerOptions": {
                    "noLib": true,
                    "strictNullChecks": true,
                    "exactOptionalPropertyTypes": false
                }
            }"#,
        )
        .unwrap();
        let legacy = Program::from_config(&fs, "/project/tsconfig.json");
        assert!(
            legacy.diagnostics().is_empty(),
            "{:?}",
            legacy.diagnostics()
        );
    }

    #[test]
    fn reports_implicit_any_and_unused_bindings() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/tsconfig.json",
            r#"{
                "files": ["main.ts"],
                "compilerOptions": {
                    "noLib": true,
                    "noImplicitAny": true,
                    "noUnusedLocals": true,
                    "noUnusedParameters": true
                }
            }"#,
        )
        .unwrap();
        fs.write_file(
            "/project/main.ts",
            r"
                function work(used, unused, _ignored) {
                    const local = 1;
                    const read = 2;
                    return used + read;
                }
            ",
        )
        .unwrap();
        let program = Program::from_config(&fs, "/project/tsconfig.json");
        assert_eq!(
            program
                .diagnostics()
                .iter()
                .filter_map(|diagnostic| diagnostic.code)
                .collect::<Vec<_>>(),
            [7006, 7006, 7006, 6133, 6133]
        );
    }

    #[test]
    fn skip_lib_check_suppresses_declaration_file_semantics() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file("/project/main.ts", "const value: Broken = { text: 'ok' };")
            .unwrap();
        fs.write_file(
            "/project/broken.d.ts",
            "interface Broken { text: string; } declare const invalid: string = 1;",
        )
        .unwrap();
        fs.write_file(
            "/project/tsconfig.json",
            r#"{
                "files": ["main.ts", "broken.d.ts"],
                "compilerOptions": { "noLib": true, "skipLibCheck": false }
            }"#,
        )
        .unwrap();
        let checked = Program::from_config(&fs, "/project/tsconfig.json");
        assert_eq!(
            checked
                .diagnostics()
                .iter()
                .filter_map(|diagnostic| diagnostic.code)
                .collect::<Vec<_>>(),
            [1039, 2322]
        );

        fs.write_file(
            "/project/tsconfig.json",
            r#"{
                "files": ["main.ts", "broken.d.ts"],
                "compilerOptions": { "noLib": true, "skipLibCheck": true }
            }"#,
        )
        .unwrap();
        let skipped = Program::from_config(&fs, "/project/tsconfig.json");
        assert!(
            skipped.diagnostics().is_empty(),
            "{:?}",
            skipped.diagnostics()
        );
    }

    #[test]
    fn reports_accidental_get_accessor_calls_across_files() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/model.ts",
            "export class Model { get value(): number { return 1; } set label(value: string) {} }",
        )
        .unwrap();
        fs.write_file(
            "/project/main.ts",
            r"
                import { Model } from './model';
                declare const model: Model;
                const value: number = model.value;
                const label: string = model.label;
                model.value();
            ",
        )
        .unwrap();
        fs.write_file(
            "/project/tsconfig.json",
            r#"{
                "files": ["main.ts"],
                "compilerOptions": { "noLib": true, "noEmit": true }
            }"#,
        )
        .unwrap();
        let program = Program::from_config(&fs, "/project/tsconfig.json");
        assert_eq!(
            program
                .diagnostics()
                .iter()
                .filter_map(|diagnostic| diagnostic.code)
                .collect::<Vec<_>>(),
            [6234]
        );
    }

    #[test]
    fn checks_structural_shapes_and_generic_argument_inference() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/tsconfig.json",
            r#"{
                "files": ["main.ts"],
                "compilerOptions": { "noLib": true, "strict": true }
            }"#,
        )
        .unwrap();
        fs.write_file(
            "/project/main.ts",
            r#"
                interface Base { readonly id: number; note?: string; }
                interface Entry extends Base { value: string; }
                const good: Entry = { id: 1, value: "ok" };
                const missing: Entry = { id: 1 };
                const excess: Entry = { id: 1, value: "ok", other: true };
                good.id = 2;
                function unwrap<T>(box: { value: T }): T { return box.value; }
                const inferred: number = unwrap({ value: 1 });
                const wrong: string = unwrap({ value: 1 });
            "#,
        )
        .unwrap();
        let program = Program::from_config(&fs, "/project/tsconfig.json");
        assert_eq!(
            program
                .diagnostics()
                .iter()
                .filter_map(|diagnostic| diagnostic.code)
                .collect::<Vec<_>>(),
            // Oracle-verified: a single missing property reports TS2741
            // rather than plain TS2322.
            [2741, 2353, 2540, 2322]
        );
    }

    #[test]
    fn declaration_emit_uses_inferred_readonly_object_types() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/main.ts",
            "export var basePrototype = { get primaryPath() { return this.collection; } };",
        )
        .unwrap();
        let program = Program::new_with_options(
            &fs,
            "/project",
            &["main.ts".to_owned()],
            CompilerOptions {
                declaration: true,
                no_lib: true,
                module: ModuleKind::CommonJs,
                target: ScriptTarget::Es2015,
                ..CompilerOptions::default()
            },
        );
        let emitted = program.emit();
        let declaration = emitted
            .files
            .iter()
            .find(|file| file.file_name == "/project/main.d.ts")
            .unwrap();
        assert_eq!(
            declaration.text,
            "export declare var basePrototype: {\n    readonly primaryPath: any;\n};\n"
        );
    }

    #[test]
    fn declaration_emit_serializes_ambient_const_literals() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/main.ts",
            concat!(
                "function f<T>(x: T): T { return x; }\n",
                "enum E { A, B, C, \"non identifier\" }\n",
                "const c1 = \"abc\";\n",
                "const c2 = 123;\n",
                "const c3 = c1;\n",
                "const c4 = c2;\n",
                "const c5 = f(123);\n",
                "const c6 = f(-123);\n",
                "const c7 = true;\n",
                "const c8 = E.A;\n",
                "const c8b = E[\"non identifier\"];\n",
                "const c9 = { x: \"abc\" };\n",
                "const c10 = [123];\n",
                "const c11 = \"abc\" + \"def\";\n",
                "const c12 = 123 + 456;\n",
                "const c13 = Math.random() > 0.5 ? \"abc\" : \"def\";\n",
                "const c14 = Math.random() > 0.5 ? 123 : 456;\n",
            ),
        )
        .unwrap();
        let program = Program::new_with_options(
            &fs,
            "/project",
            &["main.ts".to_owned()],
            CompilerOptions {
                declaration: true,
                no_lib: true,
                target: ScriptTarget::Es2015,
                ..CompilerOptions::default()
            },
        );
        let emitted = program.emit();
        let declaration = emitted
            .files
            .iter()
            .find(|file| file.file_name == "/project/main.d.ts")
            .unwrap();
        assert_eq!(
            declaration.text,
            concat!(
                "declare function f<T>(x: T): T;\n",
                "declare enum E {\n",
                "    A = 0,\n",
                "    B = 1,\n",
                "    C = 2,\n",
                "    \"non identifier\" = 3\n",
                "}\n",
                "declare const c1 = \"abc\";\n",
                "declare const c2 = 123;\n",
                "declare const c3 = \"abc\";\n",
                "declare const c4 = 123;\n",
                "declare const c5 = 123;\n",
                "declare const c6 = -123;\n",
                "declare const c7 = true;\n",
                "declare const c8 = E.A;\n",
                "declare const c8b = E[\"non identifier\"];\n",
                "declare const c9: {\n",
                "    x: string;\n",
                "};\n",
                "declare const c10: number[];\n",
                "declare const c11: string;\n",
                "declare const c12: number;\n",
                "declare const c13: string;\n",
                "declare const c14: number;\n",
            )
        );
    }

    #[test]
    fn javascript_declaration_emit_synthesizes_accessor_namespaces() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/a.js",
            concat!(
                "export const t1 = { p: 'value', get getter() { return 'value'; } };\n",
                "export const t2 = { v: 'value', set setter(v) {} };\n",
                "export const t3 = { p: 'value', get value() { return 'value'; }, set value(v) {} };\n",
            ),
        )
        .unwrap();
        let program = Program::new_with_options(
            &fs,
            "/project",
            &["a.js".to_owned()],
            CompilerOptions {
                allow_js: true,
                check_js: true,
                declaration: true,
                emit_declaration_only: true,
                no_lib: true,
                target: ScriptTarget::Es2015,
                ..CompilerOptions::default()
            },
        );
        let emitted = program.emit();
        let declaration = emitted
            .files
            .iter()
            .find(|file| file.file_name == "/project/a.d.ts")
            .unwrap();
        assert_eq!(
            declaration.text,
            concat!(
                "export namespace t1 {\n    let p: string;\n    const getter: string;\n}\n",
                "export namespace t2 {\n    let v: string;\n    let setter: any;\n}\n",
                "export namespace t3 {\n    let p_1: string;\n    export { p_1 as p };\n    export let value: string;\n}\n",
            )
        );
    }

    #[test]
    fn javascript_declaration_emit_keeps_trailing_jsdoc_typedefs() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/types.js",
            concat!(
                "export {};\n",
                "/**\n",
                " * @typedef {Record<Keyword, ParamValueTyped>} ParamStateRecord a Record containing\n",
                " * keyword pairs with descriptions of parameters.\n",
                " */\n",
            ),
        )
        .unwrap();
        let program = Program::new_with_options(
            &fs,
            "/",
            &["types.js".to_owned()],
            CompilerOptions {
                check_js: true,
                declaration: true,
                emit_declaration_only: true,
                module: ModuleKind::Preserve,
                no_lib: true,
                target: ScriptTarget::Es2015,
                ..CompilerOptions::default()
            },
        );
        let declaration = program
            .emit()
            .files
            .into_iter()
            .find(|file| file.file_name == "/types.d.ts")
            .unwrap();
        assert_eq!(
            declaration.text,
            concat!(
                "/**\n",
                " * a Record containing\n",
                " * keyword pairs with descriptions of parameters.\n",
                " */\n",
                "export type ParamStateRecord = Record<Keyword, ParamValueTyped>;\n",
            )
        );
    }

    #[test]
    fn declaration_emit_infers_deep_reverse_mapped_types() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/input.ts",
            concat!(
                "export type NativeTypeValidator<T> = (value: any) => T | undefined;\n",
                "export type Validator<T> = NativeTypeValidator<T> | ObjectValidator<T>;\n",
                "export type ObjectValidator<O> = { [K in keyof O]: Validator<O[K]> };\n",
                "export declare const validate: <V>(value: ObjectValidator<V>) => (input: any) => V;\n",
                "export declare const stringValidator: NativeTypeValidator<string>;\n",
                "export const validator = validate({ nested: { leaf: stringValidator } });\n",
            ),
        )
        .unwrap();
        let declaration = Program::new_with_options(
            &fs,
            "/project",
            &["input.ts".to_owned()],
            CompilerOptions {
                declaration: true,
                emit_declaration_only: true,
                no_lib: true,
                ..CompilerOptions::default()
            },
        )
        .emit()
        .files
        .into_iter()
        .find(|file| file.file_name == "/project/input.d.ts")
        .unwrap();
        assert!(
            declaration.text.contains(concat!(
                "export declare const validator: (input: any) => {\n",
                "    nested: {\n",
                "        leaf: string;\n",
            )),
            "{}",
            declaration.text
        );
    }

    #[test]
    fn javascript_declaration_emit_hoists_functions_before_object_namespaces() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/a.js",
            "const foo = { f1: (params) => { } };\nfunction f2(x) { foo.f1({ x }); }",
        )
        .unwrap();
        let program = Program::new_with_options(
            &fs,
            "/project",
            &["a.js".to_owned()],
            CompilerOptions {
                allow_js: true,
                check_js: true,
                declaration: true,
                emit_declaration_only: true,
                no_lib: true,
                target: ScriptTarget::Es2015,
                ..CompilerOptions::default()
            },
        );
        let declaration = program
            .emit()
            .files
            .into_iter()
            .find(|file| file.file_name == "/project/a.d.ts")
            .unwrap();
        assert_eq!(
            declaration.text,
            "declare function f2(x: any): void;\ndeclare namespace foo {\n    function f1(params: any): void;\n}\n"
        );
    }

    #[test]
    fn javascript_declaration_emit_preserves_inline_jsdoc_casts_and_typedefs() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/a.js",
            concat!(
                "/** @typedef {{ } & { name?: string }} P */\n",
                "const value = /** @type {*} */(null);\n",
                "export let cast = /** @type {P} */(value);\n",
                "export function use(input = /** @type {P} */(value)) {}\n",
                "export class C {\n",
                "  /** @readonly */ field = /** @type {P} */(value);\n",
                "  get current() { return /** @type {P} */(value); }\n",
                "  set current(next) {}\n",
                "}\n",
                "export default /** @type {P} */(value);\n",
            ),
        )
        .unwrap();
        let program = Program::new_with_options(
            &fs,
            "/project",
            &["a.js".to_owned()],
            CompilerOptions {
                allow_js: true,
                check_js: true,
                declaration: true,
                emit_declaration_only: true,
                no_lib: true,
                target: ScriptTarget::Es2015,
                ..CompilerOptions::default()
            },
        );
        let declaration = program
            .emit()
            .files
            .into_iter()
            .find(|file| file.file_name == "/project/a.d.ts")
            .unwrap()
            .text;
        assert_eq!(
            declaration,
            concat!(
                "export type P = {} & {\n",
                "    name?: string;\n",
                "};\n",
                "export declare let cast: P;\n",
                "export declare function use(input?: P): void;\n",
                "export declare class C {\n",
                "    /** @readonly */ readonly field: P;\n",
                "    get current(): P;\n",
                "    set current(next: P);\n",
                "}\n",
                "declare const _default: P;\n",
                "export default _default;\n",
            )
        );
    }

    #[test]
    fn javascript_declaration_emit_synthesizes_amd_like_module_exports() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/typing.d.ts",
            "declare function define<T = unknown>(name: string, modules: string[], ready: (...modules: unknown[]) => T): void;",
        )
        .unwrap();
        fs.write_file(
            "/project/deps/BaseClass.d.ts",
            concat!(
                "declare module \"deps/BaseClass\" {\n",
                "    class BaseClass {\n",
                "        static extends<A>(a: A): new () => A & BaseClass;\n",
                "    }\n",
                "    export = BaseClass;\n",
                "}\n",
            ),
        )
        .unwrap();
        fs.write_file(
            "/project/ExtendedClass.js",
            concat!(
                "define(\"lib/ExtendedClass\", [\"deps/BaseClass\"],\n",
                "/** @param {typeof import(\"deps/BaseClass\")} BaseClass */\n",
                "(BaseClass) => {\n",
                "    const ExtendedClass = BaseClass.extends({\n",
                "        f: function() { return \"something\"; }\n",
                "    });\n",
                "    const module = {};\n",
                "    module.exports = ExtendedClass;\n",
                "    return module.exports;\n",
                "});\n",
            ),
        )
        .unwrap();
        let program = Program::new_with_options(
            &fs,
            "/project",
            &[
                "typing.d.ts".to_owned(),
                "deps/BaseClass.d.ts".to_owned(),
                "ExtendedClass.js".to_owned(),
            ],
            CompilerOptions {
                allow_js: true,
                check_js: true,
                declaration: true,
                emit_declaration_only: true,
                no_lib: true,
                target: ScriptTarget::Es2015,
                ..CompilerOptions::default()
            },
        );
        assert!(
            program.diagnostics().is_empty(),
            "{:?}",
            program.diagnostics()
        );
        let declaration = program
            .emit()
            .files
            .into_iter()
            .find(|file| file.file_name == "/project/ExtendedClass.d.ts")
            .unwrap();
        assert_eq!(
            declaration.text,
            concat!(
                "export = ExtendedClass;\n",
                "declare const ExtendedClass: new () => {\n",
                "    f: () => \"something\";\n",
                "} & import(\"deps/BaseClass\");\n",
            )
        );
    }

    #[test]
    fn javascript_declaration_emit_consumes_arguments_and_jsdoc_metadata() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/a.js",
            concat!(
                "function f(x) { arguments; }\n",
                "const bar = { arguments: {} };\n",
                "class A {\n",
                "    /** @param {object} [foo={}] */\n",
                "    constructor(foo = {}) {\n",
                "        /** @type object */\n",
                "        this.arguments = foo;\n",
                "    }\n",
                "    get info() { return { bar: {} }; }\n",
                "}\n",
                "class B {\n",
                "    m() {\n",
                "        /** @type object */\n",
                "        this.foo = arguments;\n",
                "    }\n",
                "}\n",
            ),
        )
        .unwrap();
        let program = Program::new_with_options(
            &fs,
            "/project",
            &["a.js".to_owned()],
            CompilerOptions {
                allow_js: true,
                check_js: true,
                declaration: true,
                emit_declaration_only: true,
                target: ScriptTarget::Es2015,
                ..CompilerOptions::default()
            },
        );
        let declaration = program
            .emit()
            .files
            .into_iter()
            .find(|file| file.file_name == "/project/a.d.ts")
            .unwrap();
        assert_eq!(
            declaration.text,
            concat!(
                "declare function f(x: any): void;\n",
                "declare const bar: {\n    arguments: {};\n};\n",
                "declare class A {\n",
                "    /** @type object */\n",
                "    arguments: object;\n",
                "    /** @param {object} [foo={}] */\n",
                "    constructor(foo?: object);\n",
                "    get info(): {\n        bar: {};\n    };\n",
                "}\n",
                "declare class B {\n",
                "    /** @type object */\n",
                "    foo: object;\n",
                "    m(): void;\n",
                "}\n",
            )
        );
    }

    #[test]
    fn cyclic_inferred_alias_diagnostic_suppresses_only_declaration_output() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/main.ts",
            concat!(
                "type Bad<Arr> = Arr extends infer Inner ? Bad<Inner> : Arr;\n",
                "declare function flat<A>(arr: A): Bad<A>[];\n",
                "function foo<T>(arr: T[]) { return flat(arr); }\n",
            ),
        )
        .unwrap();
        let program = Program::new_with_options(
            &fs,
            "/project",
            &["main.ts".to_owned()],
            CompilerOptions {
                declaration: true,
                no_lib: true,
                target: ScriptTarget::Es2015,
                ..CompilerOptions::default()
            },
        );
        assert!(
            program
                .diagnostics()
                .iter()
                .any(|diagnostic| diagnostic.code == Some(5088))
        );
        let emitted = program.emit();
        assert!(
            emitted
                .files
                .iter()
                .any(|file| file.file_name == "/project/main.js")
        );
        assert!(
            !emitted
                .files
                .iter()
                .any(|file| file.file_name == "/project/main.d.ts")
        );
    }

    #[test]
    fn private_name_export_diagnostic_suppresses_declaration_output() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/main.ts",
            "if (false) { export var hidden = 0; } export type Public = typeof hidden; }",
        )
        .unwrap();
        let program = Program::new_with_options(
            &fs,
            "/project",
            &["main.ts".to_owned()],
            CompilerOptions {
                declaration: true,
                no_lib: true,
                target: ScriptTarget::Es2015,
                ..CompilerOptions::default()
            },
        );
        assert!(
            !program
                .emit()
                .files
                .iter()
                .any(|file| file.file_name == "/project/main.d.ts")
        );
    }

    #[test]
    fn block_scoped_private_type_query_reports_exported_variable() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/main.ts",
            "{ var a = \"\"; } export let b: typeof a;",
        )
        .unwrap();
        let program = Program::new_with_options(
            &fs,
            "/project",
            &["main.ts".to_owned()],
            CompilerOptions {
                declaration: true,
                emit_declaration_only: true,
                no_lib: true,
                target: ScriptTarget::Es2015,
                ..CompilerOptions::default()
            },
        );

        assert!(
            program
                .diagnostics()
                .iter()
                .any(|diagnostic| diagnostic.code == Some(4025))
        );
        assert!(
            !program
                .emit()
                .files
                .iter()
                .any(|file| file.file_name == "/project/main.d.ts")
        );
    }

    #[test]
    fn isolated_declaration_annotation_diagnostic_suppresses_declaration_output() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/main.ts",
            "declare const internal: { value: number }; export const value = internal.value;",
        )
        .unwrap();
        let program = Program::new_with_options(
            &fs,
            "/project",
            &["main.ts".to_owned()],
            CompilerOptions {
                declaration: true,
                isolated_declarations: true,
                no_lib: true,
                target: ScriptTarget::Es2015,
                ..CompilerOptions::default()
            },
        );
        assert!(
            !program
                .emit()
                .files
                .iter()
                .any(|file| file.file_name == "/project/main.d.ts")
        );
    }

    #[test]
    fn canonical_isolated_declarations_report_only_inferred_exported_return_types() {
        let fs = MemoryFileSystem::new(true);
        let source = concat!(
            "export function isString(value: unknown) {\n",
            "  return typeof value === \"string\";\n",
            "}\n",
            "export function isExplicitString(value: unknown): value is string {\n",
            "  return typeof value === \"string\";\n",
            "}\n",
            "function local(value: unknown) {\n",
            "  return typeof value === \"string\";\n",
            "}\n",
        );
        fs.write_file("/project/predicate.ts", source).unwrap();

        let program = Program::try_new_with_canonical_checker(
            &fs,
            "/project",
            &["predicate.ts".to_owned()],
            CompilerOptions {
                declaration: true,
                isolated_declarations: true,
                lib: Some(vec!["es5".to_owned()]),
                ..CompilerOptions::default()
            },
        )
        .unwrap();

        let [diagnostic] = program.diagnostics() else {
            panic!(
                "expected one isolated declaration diagnostic: {:?}",
                program.diagnostics()
            )
        };
        assert_eq!(diagnostic.code, Some(9007));
        assert_eq!(
            diagnostic.file_name.as_deref(),
            Some("/project/predicate.ts")
        );
        assert_eq!(
            diagnostic.message,
            "Function must have an explicit return type annotation with --isolatedDeclarations.",
        );
        let range = diagnostic.range.unwrap();
        assert_eq!(range.start.get(), 16);
        assert_eq!(
            &source[usize::try_from(range.start.get()).unwrap()
                ..usize::try_from(range.end.get()).unwrap()],
            "isString",
        );

        let [suggestion] = diagnostic.related_information.as_slice() else {
            panic!("expected the upstream return-type suggestion")
        };
        assert_eq!(suggestion.code, Some(9031));
        assert_eq!(suggestion.file_name, diagnostic.file_name);
        assert_eq!(suggestion.range, diagnostic.range);
        assert_eq!(
            suggestion.message,
            "Add a return type to the function declaration.",
        );
    }

    #[test]
    fn private_anonymous_mixin_diagnostic_suppresses_declaration_output() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/main.ts",
            concat!(
                "declare function mix<T>(value: T): T;\n",
                "const Mixin = class { protected dispose() {} private assert() {} };\n",
                "export default class extends mix(Mixin) {}\n",
            ),
        )
        .unwrap();
        let program = Program::new_with_options(
            &fs,
            "/project",
            &["main.ts".to_owned()],
            CompilerOptions {
                declaration: true,
                module: ModuleKind::CommonJs,
                no_lib: true,
                target: ScriptTarget::Es2015,
                ..CompilerOptions::default()
            },
        );
        assert!(
            !program
                .emit()
                .files
                .iter()
                .any(|file| file.file_name == "/project/main.d.ts")
        );
    }

    #[test]
    fn exported_anonymous_class_private_name_suppresses_declaration_output() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/main.ts",
            "export const Value = class { #value = 1; };",
        )
        .unwrap();
        let program = Program::new_with_options(
            &fs,
            "/project",
            &["main.ts".to_owned()],
            CompilerOptions {
                declaration: true,
                no_lib: true,
                target: ScriptTarget::Es2015,
                ..CompilerOptions::default()
            },
        );
        assert!(
            !program
                .emit()
                .files
                .iter()
                .any(|file| file.file_name == "/project/main.d.ts")
        );
    }

    #[test]
    fn nonportable_nested_package_inference_suppresses_declaration_output() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/node_modules/foo/node_modules/nested/index.d.ts",
            "export interface NestedProps {}",
        )
        .unwrap();
        fs.write_file(
            "/project/node_modules/foo/index.d.ts",
            concat!(
                "import { NestedProps } from 'nested';\n",
                "export function foo(): [NestedProps];\n",
            ),
        )
        .unwrap();
        fs.write_file(
            "/project/main.ts",
            "import { foo } from 'foo'; export const value = foo();",
        )
        .unwrap();
        let program = Program::new_with_options(
            &fs,
            "/project",
            &["main.ts".to_owned()],
            CompilerOptions {
                declaration: true,
                no_lib: true,
                module: ModuleKind::CommonJs,
                target: ScriptTarget::Es2015,
                ..CompilerOptions::default()
            },
        );
        let entry = program
            .source_files
            .iter()
            .find(|source| source.file_name == "/project/main.ts")
            .unwrap();
        assert!(
            program
                .diagnostics()
                .iter()
                .any(|diagnostic| diagnostic.code == Some(2883)),
            "refs={:?}, types={:?}",
            entry.checking.import_type_references,
            entry.checking.types
        );
        assert!(
            !program
                .emit()
                .files
                .iter()
                .any(|file| file.file_name == "/project/main.d.ts")
        );
    }

    #[test]
    fn nonportable_package_entry_alias_inference_suppresses_declaration_output() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/node_modules/some-dep/dist/inner.d.ts",
            concat!(
                "export type Other = { other: string };\n",
                "export type SomeType = { arg: Other };",
            ),
        )
        .unwrap();
        fs.write_file(
            "/project/node_modules/some-dep/dist/index.d.ts",
            concat!(
                "export type OtherType = import('./inner').Other;\n",
                "export type SomeType = import('./inner').SomeType;",
            ),
        )
        .unwrap();
        fs.write_file(
            "/project/node_modules/some-dep/package.json",
            r#"{"name":"some-dep","types":"./dist/index.d.ts","exports":{".":"./dist/index.js"}}"#,
        )
        .unwrap();
        fs.write_file(
            "/project/src/index.ts",
            concat!(
                "import { SomeType } from 'some-dep';\n",
                "export const foo = (thing: SomeType) => thing;\n",
                "export const bar = (thing: SomeType) => thing.arg;",
            ),
        )
        .unwrap();
        let program = Program::new_with_options(
            &fs,
            "/project",
            &["src/index.ts".to_owned()],
            CompilerOptions {
                declaration: true,
                no_lib: true,
                module: ModuleKind::NodeNext,
                target: ScriptTarget::Es2015,
                strict: true,
                ..CompilerOptions::default()
            },
        );
        let entry = program
            .source_files
            .iter()
            .find(|source| source.file_name == "/project/src/index.ts")
            .unwrap();

        assert_eq!(
            program
                .diagnostics()
                .iter()
                .filter(|diagnostic| diagnostic.code == Some(2883))
                .count(),
            2,
            "diagnostics={:?}, refs={:?}, named={:?}, types={:?}",
            program.diagnostics(),
            entry.checking.import_type_references,
            entry.checking.named_type_references,
            entry.checking.types,
        );
        assert!(
            !program
                .emit()
                .files
                .iter()
                .any(|file| file.file_name == "/project/src/index.d.ts")
        );
    }

    #[test]
    fn node_next_uses_the_nearest_package_type_for_javascript_emit() {
        for (package_json, common_js) in [
            ("{\"name\":\"pkg\"}", true),
            ("{\"name\":\"pkg\",\"type\":\"module\"}", false),
        ] {
            let fs = MemoryFileSystem::new(true);
            fs.write_file("/project/package.json", package_json)
                .unwrap();
            fs.write_file(
                "/project/index.ts",
                "import { Shape } from './types'; export type Public = Shape;",
            )
            .unwrap();
            fs.write_file("/project/types.ts", "export interface Shape {}")
                .unwrap();
            let program = Program::new_with_options(
                &fs,
                "/project",
                &["index.ts".to_owned()],
                CompilerOptions {
                    module: ModuleKind::NodeNext,
                    no_lib: true,
                    target: ScriptTarget::Es2015,
                    ..CompilerOptions::default()
                },
            );
            let javascript = program
                .emit()
                .files
                .into_iter()
                .find(|file| file.file_name == "/project/index.js")
                .unwrap();
            assert_eq!(javascript.text.contains("__esModule"), common_js);
            assert_eq!(javascript.text.contains("export {};"), !common_js);
        }
    }

    #[test]
    fn inferred_external_return_types_use_import_types_without_runtime_imports() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/node_modules/pkg/package.json",
            "{\"name\":\"pkg\",\"types\":\"index.d.ts\"}",
        )
        .unwrap();
        fs.write_file(
            "/project/node_modules/pkg/index.d.ts",
            "export declare function createPlugin(): PluginConfig; export declare class PluginConfig {}",
        )
        .unwrap();
        fs.write_file(
            "/project/index.ts",
            "import { createPlugin } from 'pkg'; export function plugins() { return [createPlugin()]; }",
        )
        .unwrap();
        let program = Program::new_with_options(
            &fs,
            "/project",
            &["index.ts".to_owned()],
            CompilerOptions {
                declaration: true,
                module: ModuleKind::NodeNext,
                no_lib: true,
                target: ScriptTarget::Es2015,
                ..CompilerOptions::default()
            },
        );
        let source = program.source_file("/project/index.ts").unwrap();
        let declaration = program
            .emit()
            .files
            .into_iter()
            .find(|file| file.file_name == "/project/index.d.ts")
            .unwrap();
        assert_eq!(
            declaration.text,
            "export declare function plugins(): import(\"pkg\").PluginConfig[];\n",
            "reachability={:?}, import refs={:?}",
            source.checking.declaration_reachability,
            source.checking.import_type_references,
        );
    }

    #[test]
    fn declaration_emit_preserves_ambient_auto_accessors() {
        let source = concat!(
            "declare class AmbientClass { accessor prop1: string; static accessor prop2: number; private accessor prop3: boolean; private static accessor prop4: symbol; }\n",
            "declare namespace AmbientNamespace { class C { accessor prop: string; } }\n",
            "declare module \"some-module\" { export class ExportedClass { accessor value: any; } }\n",
            "class RegularClass { accessor shouldError: string; }\n",
        );
        let expected = concat!(
            "declare class AmbientClass {\n    accessor prop1: string;\n    static accessor prop2: number;\n    private accessor prop3;\n    private static accessor prop4;\n}\n",
            "declare namespace AmbientNamespace {\n    class C {\n        accessor prop: string;\n    }\n}\n",
            "declare module \"some-module\" {\n    class ExportedClass {\n        accessor value: any;\n    }\n}\n",
            "declare class RegularClass {\n    accessor shouldError: string;\n}\n",
        );
        for target in [ScriptTarget::Es5, ScriptTarget::Es2015] {
            let fs = MemoryFileSystem::new(true);
            fs.write_file("/project/main.ts", source).unwrap();
            let program = Program::new_with_options(
                &fs,
                "/project",
                &["main.ts".to_owned()],
                CompilerOptions {
                    declaration: true,
                    no_lib: true,
                    module: ModuleKind::None,
                    target,
                    ..CompilerOptions::default()
                },
            );
            let emitted = program.emit();
            let declaration = emitted
                .files
                .iter()
                .find(|file| file.file_name == "/project/main.d.ts")
                .unwrap();
            assert_eq!(declaration.text, expected);
        }
    }

    #[test]
    fn declaration_emit_preserves_cross_file_alias_operator_provenance() {
        let fs = MemoryFileSystem::new(true);
        let body = concat!(
            "type O = { prop: string; prop2: string }; ",
            "type I = { prop: string }; ",
            "export const fn = (v: O['prop'], p: Omit<O, 'prop'>, key: keyof O, p2: Omit<O, keyof I>) => {};",
        );
        fs.write_file("/project/a.ts", body).unwrap();
        fs.write_file(
            "/project/aExp.ts",
            &body
                .replace("type O", "export type O")
                .replace("type I", "export type I"),
        )
        .unwrap();
        fs.write_file(
            "/project/b.ts",
            "import { fn } from './a'; import { fn as fnExp } from './aExp'; export const f = fn; export const fExp = fnExp;",
        )
        .unwrap();
        let program = Program::new_with_options(
            &fs,
            "/project",
            &["b.ts".to_owned()],
            CompilerOptions {
                declaration: true,
                module: ModuleKind::CommonJs,
                strict: true,
                ..CompilerOptions::default()
            },
        );
        let emitted = program.emit();
        assert!(emitted.diagnostics.is_empty(), "{:?}", emitted.diagnostics);
        let declaration = emitted
            .files
            .iter()
            .find(|file| file.file_name == "/project/b.d.ts")
            .unwrap();
        assert!(
            declaration
                .text
                .contains("p: Omit<{\n    prop: string;\n    prop2: string;\n}, \"prop\">")
                && declaration
                    .text
                    .contains("key: keyof {\n    prop: string;\n    prop2: string;\n}")
                && declaration
                    .text
                    .contains("v: import(\"./aExp\").O[\"prop\"]")
                && declaration
                    .text
                    .contains("p2: Omit<import(\"./aExp\").O, keyof import(\"./aExp\").I>"),
            "{}",
            declaration.text
        );
    }

    #[test]
    fn declaration_emit_preserves_cross_file_import_type_wrapper() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/box.d.ts",
            "export declare class Box<T> { value: T; }",
        )
        .unwrap();
        fs.write_file(
            "/project/boxed.d.ts",
            concat!(
                "export declare const boxed: import(\"./box\").Box<{\n",
                "    nested: import(\"./box\").Box<number>;\n",
                "}>;",
            ),
        )
        .unwrap();
        fs.write_file(
            "/project/main.ts",
            "import { boxed } from './boxed'; export const value = boxed;",
        )
        .unwrap();
        let program = Program::new_with_options(
            &fs,
            "/project",
            &["main.ts".to_owned()],
            CompilerOptions {
                declaration: true,
                no_lib: true,
                module: ModuleKind::CommonJs,
                strict: true,
                ..CompilerOptions::default()
            },
        );
        let emitted = program.emit();
        assert!(emitted.diagnostics.is_empty(), "{:?}", emitted.diagnostics);
        let declaration = emitted
            .files
            .iter()
            .find(|file| file.file_name == "/project/main.d.ts")
            .unwrap();
        assert!(
            declaration.text.contains(concat!(
                "export declare const value: import(\"./box\").Box<{\n",
                "    nested: import(\"./box\").Box<number>;\n",
                "}>;",
            )),
            "{}",
            declaration.text
        );
    }

    #[test]
    fn declaration_emit_preserves_nested_optional_alias_parameters_across_files() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/a.ts",
            concat!(
                "export type X = string; ",
                "export const fn = { o: (a?: (X | undefined)[]) => {} };",
            ),
        )
        .unwrap();
        fs.write_file(
            "/project/b.ts",
            "import { fn } from './a'; export const value = { fn };",
        )
        .unwrap();
        let program = Program::new_with_options(
            &fs,
            "/project",
            &["a.ts".to_owned(), "b.ts".to_owned()],
            CompilerOptions {
                declaration: true,
                no_lib: true,
                module: ModuleKind::CommonJs,
                ..CompilerOptions::default()
            },
        );
        let emitted = program.emit();
        assert!(emitted.diagnostics.is_empty(), "{:?}", emitted.diagnostics);
        let a = emitted
            .files
            .iter()
            .find(|file| file.file_name == "/project/a.d.ts")
            .unwrap();
        let b = emitted
            .files
            .iter()
            .find(|file| file.file_name == "/project/b.d.ts")
            .unwrap();
        assert!(
            a.text.contains("o: (a?: (X | undefined)[]) => void;"),
            "{}",
            a.text
        );
        assert!(
            b.text
                .contains("o: (a?: (import(\"./a\").X | undefined)[]) => void;"),
            "{}",
            b.text
        );
    }

    #[test]
    fn resolves_non_relative_imports_from_base_url() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file("/proj/defs/cc.ts", "export const enum CharCode { A, B }")
            .unwrap();
        fs.write_file(
            "/proj/component/file.ts",
            "import { CharCode } from 'defs/cc'; export const value = CharCode.A;",
        )
        .unwrap();
        let program = Program::new_with_options(
            &fs,
            "/proj",
            &["component/file.ts".to_owned()],
            CompilerOptions {
                base_url: Some("/proj".into()),
                no_lib: true,
                ..CompilerOptions::default()
            },
        );
        assert!(
            program
                .diagnostics()
                .iter()
                .all(|diagnostic| diagnostic.code != Some(2307)),
            "{:?}",
            program.diagnostics()
        );
        assert!(program.source_file("/proj/defs/cc.ts").is_some());
    }

    #[test]
    fn invalid_out_file_module_kind_does_not_emit() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file("/project/main.ts", "export const value = 1;")
            .unwrap();
        fs.write_file("/project/global.ts", "const globalValue = 2;")
            .unwrap();
        let program = Program::new_with_options(
            &fs,
            "/project",
            &["main.ts".to_owned()],
            CompilerOptions {
                module: ModuleKind::EsNext,
                out_file: Some("/project/bundle.js".into()),
                no_lib: true,
                ..CompilerOptions::default()
            },
        );
        assert!(program.emit().files.is_empty());

        let unspecified_module = Program::new_with_options(
            &fs,
            "/project",
            &["main.ts".to_owned()],
            CompilerOptions {
                out_file: Some("/project/bundle.js".into()),
                no_lib: true,
                ..CompilerOptions::default()
            },
        );
        assert!(unspecified_module.emit().files.is_empty());

        let mixed_unspecified_module = Program::new_with_options(
            &fs,
            "/project",
            &["main.ts".to_owned(), "global.ts".to_owned()],
            CompilerOptions {
                out_file: Some("/project/bundle.js".into()),
                no_lib: true,
                ..CompilerOptions::default()
            },
        );
        let emitted = mixed_unspecified_module.emit();
        assert_eq!(emitted.files.len(), 1);
        assert_eq!(
            emitted.files[0].text,
            "\"use strict\";\nvar globalValue = 2;\n"
        );

        let commonjs_scripts = Program::new_with_options(
            &fs,
            "/project",
            &["global.ts".to_owned()],
            CompilerOptions {
                module: ModuleKind::CommonJs,
                out_file: Some("/project/bundle.js".into()),
                no_lib: true,
                ..CompilerOptions::default()
            },
        );
        let emitted = commonjs_scripts.emit();
        assert_eq!(emitted.files.len(), 1);
        assert_eq!(
            emitted.files[0].text,
            "\"use strict\";\nvar globalValue = 2;\n"
        );
    }

    #[test]
    fn resolved_node_modules_sources_are_not_emit_roots() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file("/project/main.ts", "import { value } from 'pkg'; value;")
            .unwrap();
        fs.write_file(
            "/project/node_modules/pkg/index.ts",
            "export const value = 1;",
        )
        .unwrap();
        let program = Program::new_with_options(
            &fs,
            "/project",
            &["main.ts".to_owned()],
            CompilerOptions {
                no_lib: true,
                ..CompilerOptions::default()
            },
        );
        let emitted = program.emit();
        assert!(
            emitted
                .files
                .iter()
                .any(|file| file.file_name == "/project/main.js")
        );
        assert!(
            emitted
                .files
                .iter()
                .all(|file| !file.file_name.contains("node_modules"))
        );
    }

    #[test]
    fn json_modules_are_copied_without_declaration_files() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/main.ts",
            "import data = require('./data.json'); export const value = data.value;",
        )
        .unwrap();
        fs.write_file("/project/data.json", "{ \"value\": 1 }")
            .unwrap();
        let program = Program::new_with_options(
            &fs,
            "/project",
            &["main.ts".to_owned()],
            CompilerOptions {
                declaration: true,
                resolve_json_module: true,
                out_dir: Some("/project/out".into()),
                no_lib: true,
                ..CompilerOptions::default()
            },
        );
        let emitted = program.emit();
        assert!(
            emitted
                .files
                .iter()
                .any(|file| file.file_name == "/project/out/data.json")
        );
        assert!(
            emitted
                .files
                .iter()
                .all(|file| file.file_name != "/project/out/data.d.ts")
        );
    }

    #[test]
    fn amd_out_file_emits_json_as_a_named_value_module() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/main.ts",
            "import * as data from './data.json'; export { data };",
        )
        .unwrap();
        fs.write_file("/project/data.json", "{\n    \"value\": 1\n}\n")
            .unwrap();
        let program = Program::new_with_options(
            &fs,
            "/project",
            &["main.ts".to_owned()],
            CompilerOptions {
                module: ModuleKind::Amd,
                out_file: Some("/project/out.js".into()),
                resolve_json_module: true,
                no_lib: true,
                ..CompilerOptions::default()
            },
        );
        let output = &program.emit().files[0].text;
        assert!(
            output.starts_with("define(\"data\", [], {\n    \"value\": 1\n});\n"),
            "{output}"
        );
    }

    #[test]
    fn isolated_declaration_errors_suppress_declaration_output() {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(
            "/project/main.ts",
            "const key: 0 = 0; export const value = { [key]: 1 };",
        )
        .unwrap();
        let program = Program::new_with_options(
            &fs,
            "/project",
            &["main.ts".to_owned()],
            CompilerOptions {
                declaration: true,
                isolated_declarations: true,
                no_lib: true,
                ..CompilerOptions::default()
            },
        );
        let emitted = program.emit();
        assert!(
            emitted
                .files
                .iter()
                .any(|file| file.file_name == "/project/main.js")
        );
        assert!(
            emitted
                .files
                .iter()
                .all(|file| file.file_name != "/project/main.d.ts")
        );
    }

    #[test]
    fn percent_encodes_source_map_urls_without_encoding_path_separators() {
        assert_eq!(
            percent_encode_source_map_url("../maps/① file[one].js.map"),
            "../maps/%E2%91%A0%20file%5Bone%5D.js.map"
        );
    }
}
