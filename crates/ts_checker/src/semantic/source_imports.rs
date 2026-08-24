//! Exact source planning for ESM imports, JSDoc imports, and named reexports.
//!
//! This slice accepts leading, top-level side-effect imports, default imports,
//! namespace imports, and named imports, including explicit named `default`
//! bindings. Imports and named or namespace reexports must use identifier
//! names. Alias discovery belongs to the production alias host. A
//! successful alias may traverse named and explicit default reexports before
//! reaching an authenticated exported declaration in another retained source.
//! JavaScript `JSDoc` typedef targets retain their exact parser-owned reparsed
//! flag. Comment-only typedef imports authenticate promoted `CommonJS` type
//! exports through their exact module-specifier nodes. Value preparation
//! supports initialized annotated `const` declarations,
//! authenticated `CommonJS` variables and named assignments, exact
//! `export declare const` declarations in retained declaration files, and
//! annotated `FunctionDeclaration`s, and already-published inferred object
//! constants with authenticated fresh-to-widened provenance. Declaration-file
//! bodies are never source checked by this leaf; only the final imported
//! annotation is queried.
//!
//! Source integration separates declaration checking from value use. Every
//! binding is resolved through [`resolve_source_import_binding`], including
//! unused imports, while [`prepare_source_import_value`] queries the target's
//! annotation or callable graph only for a proven later value read. Preparation
//! returns eventual target/alias value-link payloads without publishing the
//! import alias. After the whole source has checked,
//! [`preflight_prepared_source_import_publications`] validates and exposes
//! those payloads for the source checker's one combined atomic publication
//! batch. Importer-first Program order never recursively checks the target
//! source: `CanonicalTypeQuery` materializes its canonical type lazily.
//!
//! The split follows the pinned TypeScript-Go paths in
//! `internal/checker/checker.go`: `checkImportDeclaration` proves import
//! bindings, `resolveAlias` selects the direct export, `getTypeOfAlias` owns
//! the alias value cache, and `getTypeOfVariableOrParameterOrProperty` obtains
//! the annotated target value type.

use std::collections::{HashMap, HashSet};

use ts_ast::{Node, NodeArena, NodeData, NodeFlags, NodeRef, SyntaxKind};
use ts_binder::{
    BoundFile, CanonicalNameResolutionError, CanonicalNameResolver, CanonicalResolutionLocation,
    CheckFlags, EscapedName, InternalSymbolName, SemanticSymbolId, SymbolData, SymbolFlags,
};

use super::{
    AliasTargetState, CanonicalCheckerDiagnostics, CanonicalCheckerOptions, CanonicalGlobalTypes,
    CanonicalTypeMapperStore, DeclaredTypeError, DeclaredTypeHost, ProductionAliasTargetHost,
    SignatureId, TypeId, TypeNodeLinks, ValueSymbolLinks,
    alias::{
        CanonicalAliasResolutionError, CanonicalAliasResolutionEvent, CanonicalAliasResolver,
        CanonicalAliasTargetHost, CanonicalImmediateAliasTarget,
    },
    array_types::CanonicalArrayTargets,
    derived_types::DerivedObjectLiteralValidation,
    enums,
    instantiate::InstantiationSession,
    jsdoc::{
        JsDocImportType, PlannedJsDocType, plan_javascript_source_jsdoc,
        preflight_planned_jsdoc_type, resolve_planned_jsdoc_type,
    },
    source_callables::{
        SourceCallableError, SourceCallableFamily, SourceCallablePlan, SourceCallableState,
        StoredSourceCallableValidation, plan_source_callable,
        publish_inferred_source_callable_return, source_callable_state,
        validate_stored_source_callable,
    },
    store::SourceNodeParent,
    type_nodes::{
        CanonicalJsDocImportTypeTarget, CanonicalTypeQuery, CanonicalTypeReferenceAliasTarget,
    },
    type_records::{TypeData, TypeRecord},
    types::{ObjectFlags, TypeFlags},
    variables::{VariableBindingKind, VariablePlanError, plan_top_level_variable},
};

const NODE_FLAG_CONST: u32 = 1 << 1;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[cfg_attr(not(test), allow(dead_code))]
enum SourceImportPhase {
    Value,
    Type,
}

/// One exact local binding introduced by a supported default or named import.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct SourceImportBindingPlan {
    pub(super) declaration: NodeRef,
    pub(super) imported_name: NodeRef,
    pub(super) local_name: NodeRef,
    pub(super) imported_text: String,
    pub(super) local_text: String,
    pub(super) alias_symbol: SemanticSymbolId,
}

/// Read-only plan for one complete top-level import statement.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct SourceImportPlan {
    pub(super) declaration: NodeRef,
    pub(super) module_specifier: NodeRef,
    pub(super) bindings: Vec<SourceImportBindingPlan>,
}

/// One parser-owned JavaScript typedef whose body imports a qualified type.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct SourceJsDocTypedefImportPlan {
    pub(super) host_declaration: NodeRef,
    pub(super) local_declaration: NodeRef,
    pub(super) local_symbol: SemanticSymbolId,
    pub(super) import_type: NodeRef,
    pub(super) module_specifier: NodeRef,
    pub(super) imported_name: NodeRef,
}

/// One JSDoc typedef resolved through an authenticated CommonJS export.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct ResolvedSourceJsDocTypedefImport {
    pub(super) plan: SourceJsDocTypedefImportPlan,
    pub(super) module_symbol: SemanticSymbolId,
    pub(super) target_symbol: SemanticSymbolId,
    pub(super) target_declaration: NodeRef,
}

impl ResolvedSourceJsDocTypedefImport {
    pub(super) const fn type_capability(self) -> CanonicalJsDocImportTypeTarget {
        CanonicalJsDocImportTypeTarget::new(
            self.plan.local_declaration,
            self.plan.local_symbol,
            self.plan.import_type,
            self.plan.module_specifier,
            self.plan.imported_name,
            self.module_symbol,
            self.target_symbol,
            self.target_declaration,
        )
    }
}

/// One exact alias binding introduced into a module's export table.
#[derive(Clone, Debug, Eq, PartialEq)]
#[cfg_attr(not(test), allow(dead_code))]
pub(super) struct SourceNamedReexportBindingPlan {
    pub(super) declaration: NodeRef,
    pub(super) imported_name: NodeRef,
    pub(super) exported_name: NodeRef,
    pub(super) imported_text: String,
    pub(super) exported_text: String,
    pub(super) alias_symbol: SemanticSymbolId,
    pub(super) syntactic_type_only: bool,
}

/// Read-only plan for one complete top-level named reexport statement.
#[derive(Clone, Debug, Eq, PartialEq)]
#[cfg_attr(not(test), allow(dead_code))]
pub(super) struct SourceNamedReexportPlan {
    pub(super) declaration: NodeRef,
    pub(super) module_specifier: NodeRef,
    pub(super) bindings: Vec<SourceNamedReexportBindingPlan>,
}

/// One named reexport whose immediate and final alias identities were proven.
#[derive(Clone, Debug, Eq, PartialEq)]
#[cfg_attr(not(test), allow(dead_code))]
pub(super) struct ResolvedSourceNamedReexportBinding {
    pub(super) binding: SourceNamedReexportBindingPlan,
    pub(super) immediate_target_symbol: SemanticSymbolId,
    pub(super) target_symbol: SemanticSymbolId,
    pub(super) type_only_declaration: Option<NodeRef>,
}

/// A later identifier expression proven to read one planned import binding.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct PlannedSourceImportRead {
    pub(super) node: NodeRef,
    pub(super) resolved_symbol: SemanticSymbolId,
    pub(super) value_symbol: SemanticSymbolId,
}

/// A binding whose immediate and final alias targets have been resolved
/// without querying its value type. Every import declaration uses this state,
/// including imports that have no value read in the checked source.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct ResolvedSourceImportBinding {
    pub(super) binding: SourceImportBindingPlan,
    pub(super) immediate_target_symbol: SemanticSymbolId,
    pub(super) target_symbol: SemanticSymbolId,
}

/// One independently resolved type-only binding whose final target is a simple
/// exported type declaration in another retained ESM source.
#[derive(Clone, Debug, Eq, PartialEq)]
#[cfg_attr(not(test), allow(dead_code))]
pub(super) struct ResolvedSourceTypeImportBinding {
    pub(super) binding: SourceImportBindingPlan,
    pub(super) immediate_target_symbol: SemanticSymbolId,
    pub(super) target_symbol: SemanticSymbolId,
    pub(super) target_declaration: NodeRef,
}

/// Deferred exact value-link publications for one resolved import binding.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct PreparedSourceImportValue {
    pub(super) binding: SourceImportBindingPlan,
    pub(super) immediate_target_symbol: SemanticSymbolId,
    pub(super) target_symbol: SemanticSymbolId,
    pub(super) target_declaration: NodeRef,
    pub(super) type_: TypeId,
    target: PreparedSourceImportTarget,
    target_links: ValueSymbolLinks,
    alias_links: ValueSymbolLinks,
}

/// Target-specific cache proof retained between lazy preparation and the
/// source checker's final alias-link publication batch.
#[derive(Clone, Debug, Eq, PartialEq)]
enum PreparedSourceImportTarget {
    AnnotatedConst {
        type_node: NodeRef,
        type_links: Option<TypeNodeLinks>,
    },
    DeclarationNumericConst {
        initializer: NodeRef,
        literal: String,
    },
    AnnotatedFunction {
        signature: SignatureId,
    },
    ConstEnum {
        declared_type: TypeId,
    },
    ExportedObject {
        expression: NodeRef,
    },
    PublishedObjectConst {
        expression: NodeRef,
        expression_type: TypeId,
    },
    JavaScriptAnnotatedConst {
        annotation: Option<PlannedJsDocType>,
    },
    CommonJsNamedExport {
        assignments: Vec<CommonJsNamedExportAssignment>,
    },
    ModuleNamespace {
        properties: Vec<PreparedSourceImportModuleProperty>,
    },
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct PreparedSourceImportModuleProperty {
    name: EscapedName,
    symbol: SemanticSymbolId,
    target_symbol: SemanticSymbolId,
    value_symbol: SemanticSymbolId,
    type_: TypeId,
    namespace: Option<Box<PreparedSourceImportNestedNamespace>>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct PreparedSourceImportNestedNamespace {
    declaration: NodeRef,
    properties: Vec<PreparedSourceImportModuleProperty>,
    links: ValueSymbolLinks,
}

enum PlannedSourceImportValueTarget {
    AnnotatedConst {
        declaration: NodeRef,
        type_node: NodeRef,
    },
    DeclarationNumericConst {
        declaration: NodeRef,
        initializer: NodeRef,
        literal: String,
    },
    AnnotatedFunction(Box<SourceCallablePlan>),
    ConstEnum {
        declaration: NodeRef,
    },
    ExportedObject {
        declaration: NodeRef,
        expression: NodeRef,
        type_: TypeId,
    },
    PublishedObjectConst {
        declaration: NodeRef,
        expression: NodeRef,
        expression_type: TypeId,
        type_: TypeId,
    },
    JavaScriptAnnotatedConst {
        declaration: NodeRef,
        annotation: Option<PlannedJsDocType>,
        cached_type: Option<TypeId>,
    },
    CommonJsNamedExport {
        declaration: NodeRef,
        assignments: Vec<CommonJsNamedExportAssignment>,
        cached_type: TypeId,
    },
    ModuleNamespace {
        declaration: NodeRef,
        members: Vec<PlannedSourceImportModuleMember>,
    },
}

struct PlannedSourceImportModuleMember {
    name: EscapedName,
    symbol: SemanticSymbolId,
    value_symbol: SemanticSymbolId,
    target: PlannedSourceImportValueTarget,
}

#[derive(Clone, Copy)]
struct AuthenticatedSourceImportExportedObject {
    declaration: NodeRef,
    expression: NodeRef,
    export_equals: bool,
}

#[derive(Clone, Copy)]
struct AuthenticatedSyntheticImportNamespace {
    function: NodeRef,
    namespace: NodeRef,
    assignment: SemanticSymbolId,
    original: SemanticSymbolId,
    default: SemanticSymbolId,
    module: SemanticSymbolId,
    originating_import: NodeRef,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct CommonJsNamedExportAssignment {
    expression: NodeRef,
    left: NodeRef,
    right: NodeRef,
}

/// One fully preflighted value-link payload for the source checker's combined
/// final publication batch.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct PreparedSourceImportPublication {
    pub(super) symbol: SemanticSymbolId,
    pub(super) links: ValueSymbolLinks,
}

/// Valid TypeScript import forms outside this dependency-closed slice.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum SourceImportUnsupported {
    Declaration {
        node: NodeRef,
        kind: SyntaxKind,
    },
    JavaScriptSource(NodeRef),
    CommonJsSource(NodeRef),
    ScriptSource(NodeRef),
    ImportShape(NodeRef),
    ExportShape(NodeRef),
    ImportClause(NodeRef),
    ExportClause(NodeRef),
    NamedBindings(NodeRef),
    EmptyNamedExports(NodeRef),
    Binding(NodeRef),
    ExportBinding(NodeRef),
    TypeOnly(NodeRef),
    ImportAttributes(NodeRef),
    ExportAttributes(NodeRef),
    NonIdentifierImportName(NodeRef),
    NonIdentifierLocalName(NodeRef),
    NonIdentifierReexportName(NodeRef),
    NonIdentifierExportName(NodeRef),
    MergedAlias(NodeRef),
    TargetSymbol {
        alias: SemanticSymbolId,
        target: SemanticSymbolId,
        flags: SymbolFlags,
    },
    SameSourceTarget {
        binding: NodeRef,
        target: NodeRef,
    },
    TargetDeclaration(NodeRef),
    TargetNotExportedConst(NodeRef),
    MissingTargetAnnotation(NodeRef),
    MissingTargetInitializer(NodeRef),
    UnexpectedTargetInitializer(NodeRef),
    TypeOnlyAlias(SemanticSymbolId),
    ValueAlias(SemanticSymbolId),
    #[cfg_attr(not(test), allow(dead_code))]
    TargetTypeDeclaration(NodeRef),
    #[cfg_attr(not(test), allow(dead_code))]
    TargetTypeNotExported(NodeRef),
    #[cfg_attr(not(test), allow(dead_code))]
    TargetTypeShape(NodeRef),
    #[cfg_attr(not(test), allow(dead_code))]
    TypeReference(NodeRef),
    #[cfg_attr(not(test), allow(dead_code))]
    ValueUseOfTypeOnlyImport(NodeRef),
}

/// Malformed AST/binder provenance or poisoned checker state.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum SourceImportInvariant {
    InvalidSource(NodeRef),
    MissingSourceFacts(NodeRef),
    InvalidTopLevelDeclaration(NodeRef),
    InvalidNode(NodeRef),
    InvalidAliasSymbol(SemanticSymbolId),
    MissingAliasSymbol(NodeRef),
    DuplicateAlias(SemanticSymbolId),
    DuplicateLocalName(NodeRef),
    DuplicateExportName(NodeRef),
    AliasDeclarationMismatch {
        alias: SemanticSymbolId,
        declaration: NodeRef,
    },
    AliasNameMismatch {
        alias: SemanticSymbolId,
        name: NodeRef,
    },
    InvalidAliasLinks(SemanticSymbolId),
    InvalidIdentifierCache(NodeRef),
    InvalidTypeReferenceCache(NodeRef),
    ReadBindingMismatch(NodeRef),
    InvalidTargetSymbol(SemanticSymbolId),
    TargetNameMismatch {
        target: SemanticSymbolId,
        name: NodeRef,
    },
    InvalidTargetLinks(SemanticSymbolId),
    InvalidAliasValueLinks(SemanticSymbolId),
    CachedTypeMismatch {
        symbol: SemanticSymbolId,
        cached: TypeId,
        expected: TypeId,
    },
    DuplicatePreparedSymbol(SemanticSymbolId),
    PreparedStateChanged(SemanticSymbolId),
}

/// Exact failure domain for supported ESM import and reexport bindings.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) enum SourceImportError {
    Unsupported(SourceImportUnsupported),
    Invariant(SourceImportInvariant),
    Alias(CanonicalAliasResolutionError),
    DeclaredType(DeclaredTypeError),
    Variable(VariablePlanError),
    Callable(SourceCallableError),
    CircularAlias {
        alias: SemanticSymbolId,
        events: Vec<CanonicalAliasResolutionEvent>,
    },
}

impl SourceImportError {
    /// Best source node for integration into the source checker's error layer.
    pub(super) const fn node(&self) -> Option<NodeRef> {
        match self {
            Self::Unsupported(reason) => match *reason {
                SourceImportUnsupported::Declaration { node, .. }
                | SourceImportUnsupported::JavaScriptSource(node)
                | SourceImportUnsupported::CommonJsSource(node)
                | SourceImportUnsupported::ScriptSource(node)
                | SourceImportUnsupported::ImportShape(node)
                | SourceImportUnsupported::ExportShape(node)
                | SourceImportUnsupported::ImportClause(node)
                | SourceImportUnsupported::ExportClause(node)
                | SourceImportUnsupported::NamedBindings(node)
                | SourceImportUnsupported::EmptyNamedExports(node)
                | SourceImportUnsupported::Binding(node)
                | SourceImportUnsupported::ExportBinding(node)
                | SourceImportUnsupported::TypeOnly(node)
                | SourceImportUnsupported::ImportAttributes(node)
                | SourceImportUnsupported::ExportAttributes(node)
                | SourceImportUnsupported::NonIdentifierImportName(node)
                | SourceImportUnsupported::NonIdentifierLocalName(node)
                | SourceImportUnsupported::NonIdentifierReexportName(node)
                | SourceImportUnsupported::NonIdentifierExportName(node)
                | SourceImportUnsupported::MergedAlias(node)
                | SourceImportUnsupported::TargetDeclaration(node)
                | SourceImportUnsupported::TargetNotExportedConst(node)
                | SourceImportUnsupported::MissingTargetAnnotation(node)
                | SourceImportUnsupported::MissingTargetInitializer(node)
                | SourceImportUnsupported::UnexpectedTargetInitializer(node)
                | SourceImportUnsupported::TargetTypeDeclaration(node)
                | SourceImportUnsupported::TargetTypeNotExported(node)
                | SourceImportUnsupported::TargetTypeShape(node)
                | SourceImportUnsupported::TypeReference(node)
                | SourceImportUnsupported::ValueUseOfTypeOnlyImport(node) => Some(node),
                SourceImportUnsupported::SameSourceTarget { binding, .. } => Some(binding),
                SourceImportUnsupported::TargetSymbol { .. }
                | SourceImportUnsupported::TypeOnlyAlias(_)
                | SourceImportUnsupported::ValueAlias(_) => None,
            },
            Self::Invariant(reason) => match *reason {
                SourceImportInvariant::InvalidSource(node)
                | SourceImportInvariant::MissingSourceFacts(node)
                | SourceImportInvariant::InvalidTopLevelDeclaration(node)
                | SourceImportInvariant::InvalidNode(node)
                | SourceImportInvariant::MissingAliasSymbol(node)
                | SourceImportInvariant::DuplicateLocalName(node)
                | SourceImportInvariant::DuplicateExportName(node)
                | SourceImportInvariant::AliasNameMismatch { name: node, .. }
                | SourceImportInvariant::TargetNameMismatch { name: node, .. }
                | SourceImportInvariant::InvalidIdentifierCache(node)
                | SourceImportInvariant::InvalidTypeReferenceCache(node)
                | SourceImportInvariant::ReadBindingMismatch(node) => Some(node),
                SourceImportInvariant::AliasDeclarationMismatch { declaration, .. } => {
                    Some(declaration)
                }
                SourceImportInvariant::InvalidAliasSymbol(_)
                | SourceImportInvariant::DuplicateAlias(_)
                | SourceImportInvariant::InvalidAliasLinks(_)
                | SourceImportInvariant::InvalidTargetSymbol(_)
                | SourceImportInvariant::InvalidTargetLinks(_)
                | SourceImportInvariant::InvalidAliasValueLinks(_)
                | SourceImportInvariant::CachedTypeMismatch { .. }
                | SourceImportInvariant::DuplicatePreparedSymbol(_)
                | SourceImportInvariant::PreparedStateChanged(_) => None,
            },
            Self::Callable(error) => error.node(),
            Self::Alias(_)
            | Self::DeclaredType(_)
            | Self::Variable(_)
            | Self::CircularAlias { .. } => None,
        }
    }
}

impl std::fmt::Display for SourceImportError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Unsupported(reason) => {
                write!(formatter, "source import is unsupported: {reason:?}")
            }
            Self::Invariant(reason) => {
                write!(formatter, "source import invariant failed: {reason:?}")
            }
            Self::Alias(error) => error.fmt(formatter),
            Self::DeclaredType(error) => error.fmt(formatter),
            Self::Variable(error) => {
                write!(formatter, "target variable planning failed: {error:?}")
            }
            Self::Callable(error) => {
                write!(formatter, "target callable planning failed: {error:?}")
            }
            Self::CircularAlias { alias, .. } => {
                write!(formatter, "source import alias is circular: {alias:?}")
            }
        }
    }
}

impl std::error::Error for SourceImportError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Alias(error) => Some(error),
            Self::DeclaredType(error) => Some(error),
            Self::Unsupported(_)
            | Self::Invariant(_)
            | Self::Variable(_)
            | Self::Callable(_)
            | Self::CircularAlias { .. } => None,
        }
    }
}

impl From<CanonicalAliasResolutionError> for SourceImportError {
    fn from(error: CanonicalAliasResolutionError) -> Self {
        Self::Alias(error)
    }
}

impl From<DeclaredTypeError> for SourceImportError {
    fn from(error: DeclaredTypeError) -> Self {
        Self::DeclaredType(error)
    }
}

impl From<VariablePlanError> for SourceImportError {
    fn from(error: VariablePlanError) -> Self {
        Self::Variable(error)
    }
}

impl From<SourceCallableError> for SourceImportError {
    fn from(error: SourceCallableError) -> Self {
        Self::Callable(error)
    }
}

fn unsupported(reason: SourceImportUnsupported) -> SourceImportError {
    SourceImportError::Unsupported(reason)
}

fn invariant(reason: SourceImportInvariant) -> SourceImportError {
    SourceImportError::Invariant(reason)
}

/// Proves one complete top-level default or named-value import without writes.
///
/// Statement-order ownership stays with the source planner: it must call this
/// only while traversing the leading import prefix.
pub(super) fn plan_top_level_named_value_import(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    declaration: NodeRef,
) -> Result<SourceImportPlan, SourceImportError> {
    plan_top_level_named_import(arena, bound, store, declaration, SourceImportPhase::Value)
}

/// Proves one complete leading default or named `import type` declaration.
///
/// The clause-level `type` marker is required. Mixed imports and the
/// specifier-level `import { type T }` spelling remain outside this leaf so a
/// plan always has one unambiguous namespace.
#[cfg_attr(not(test), allow(dead_code))]
pub(super) fn plan_top_level_named_type_import(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    declaration: NodeRef,
) -> Result<SourceImportPlan, SourceImportError> {
    plan_top_level_named_import(arena, bound, store, declaration, SourceImportPhase::Type)
}

/// Authenticates the exact parser-owned body of a comment-only typedef import.
pub(super) fn plan_source_jsdoc_typedef_import(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    host_declaration: NodeRef,
    local_declaration: NodeRef,
    imported: &JsDocImportType,
) -> Result<SourceJsDocTypedefImportPlan, SourceImportError> {
    validate_source_identity(arena, bound, store, bound.source_file())?;
    let facts = bound.source_facts().ok_or_else(|| {
        invariant(SourceImportInvariant::MissingSourceFacts(
            bound.source_file(),
        ))
    })?;
    let host = checked_node(arena, bound, store, host_declaration)?;
    let declaration = checked_node(arena, bound, store, local_declaration)?;
    let NodeData::TypeAliasDeclaration(alias) = &declaration.data else {
        return Err(unsupported(SourceImportUnsupported::Binding(
            local_declaration,
        )));
    };
    let local_symbol = bound
        .symbol(local_declaration)
        .ok_or_else(|| invariant(SourceImportInvariant::MissingAliasSymbol(local_declaration)))?;
    let local = store
        .symbol(local_symbol)
        .ok_or_else(|| invariant(SourceImportInvariant::InvalidAliasSymbol(local_symbol)))?;
    let local_name = NodeRef::new(local_declaration.arena, local_declaration.file, alias.name);
    let local_name_record = checked_node(arena, bound, store, local_name)?;
    let NodeData::Identifier(local_identifier) = &local_name_record.data else {
        return Err(invariant(SourceImportInvariant::AliasNameMismatch {
            alias: local_symbol,
            name: local_name,
        }));
    };
    if !facts.is_javascript_file()
        || facts.is_declaration_file()
        || host.kind != SyntaxKind::VariableDeclaration
        || declaration.kind != SyntaxKind::JsTypeAliasDeclaration
        || declaration.flags != NodeFlags::REPARSED
        || declaration.parent != Some(bound.source_file().node)
        || alias.flow_node.is_some()
        || alias.local_symbol.is_some()
        || alias.next_container.is_some()
        || alias.symbol.is_some()
        || alias.type_parameters.is_some()
        || alias.modifiers.is_some()
        || local_name_record.kind != SyntaxKind::Identifier
        || local_name_record.flags.0 != 0
        || local_name_record.parent != Some(local_declaration.node)
        || local_identifier.flow_node.is_some()
        || local.flags() != SymbolFlags::TYPE_ALIAS
        || local.check_flags() != CheckFlags::NONE
        || local.declarations() != Some(&[local_declaration])
        || local.value_declaration().is_some()
        || local.members().is_some()
        || local.exports().is_some()
        || local.export_symbol().is_some()
        || local.name().as_bytes() != local_identifier.text.as_bytes()
        || store.get_merged_symbol(local_symbol) != Some(local_symbol)
    {
        return Err(unsupported(SourceImportUnsupported::Binding(
            local_declaration,
        )));
    }

    let import_type = NodeRef::new(local_declaration.arena, local_declaration.file, alias.type_);
    let import_record = checked_node(arena, bound, store, import_type)?;
    let NodeData::ImportTypeNode(import) = &import_record.data else {
        return Err(unsupported(SourceImportUnsupported::TypeReference(
            import_type,
        )));
    };
    let argument = NodeRef::new(import_type.arena, import_type.file, import.argument);
    let argument_record = checked_node(arena, bound, store, argument)?;
    let NodeData::LiteralTypeNode(literal_type) = &argument_record.data else {
        return Err(unsupported(SourceImportUnsupported::TypeReference(
            import_type,
        )));
    };
    let module_specifier = NodeRef::new(argument.arena, argument.file, literal_type.literal);
    let specifier_record = checked_node(arena, bound, store, module_specifier)?;
    let NodeData::StringLiteral(specifier) = &specifier_record.data else {
        return Err(unsupported(SourceImportUnsupported::TypeReference(
            import_type,
        )));
    };
    let Some(imported_name) = import.qualifier else {
        return Err(unsupported(SourceImportUnsupported::TypeReference(
            import_type,
        )));
    };
    let imported_name = NodeRef::new(import_type.arena, import_type.file, imported_name);
    let qualifier_record = checked_node(arena, bound, store, imported_name)?;
    let NodeData::Identifier(qualifier) = &qualifier_record.data else {
        return Err(unsupported(SourceImportUnsupported::TypeReference(
            imported_name,
        )));
    };
    if import_record.kind != SyntaxKind::ImportType
        || import_record.flags.0 != 0
        || import_record.parent != Some(local_declaration.node)
        || import.attributes.is_some()
        || import.is_type_of
        || import.type_arguments.is_some()
        || argument_record.kind != SyntaxKind::LiteralType
        || argument_record.flags.0 != 0
        || argument_record.parent != Some(import_type.node)
        || specifier_record.kind != SyntaxKind::StringLiteral
        || specifier_record.flags.0 != 0
        || specifier_record.parent != Some(argument.node)
        || specifier.token_flags.0 != 0
        || specifier.text != imported.specifier()
        || qualifier_record.kind != SyntaxKind::Identifier
        || qualifier_record.flags.0 != 0
        || qualifier_record.parent != Some(import_type.node)
        || qualifier.flow_node.is_some()
        || qualifier.text.is_empty()
        || imported.qualifier() != Some(qualifier.text.as_str())
        || imported.is_type_of()
        || !imported.type_arguments().is_empty()
        || store
            .symbol_node_links(imported_name)
            .and_then(|links| links.resolved_symbol)
            .is_some_and(|symbol| store.symbol(symbol).is_none())
    {
        return Err(unsupported(SourceImportUnsupported::TypeReference(
            import_type,
        )));
    }

    Ok(SourceJsDocTypedefImportPlan {
        host_declaration,
        local_declaration,
        local_symbol,
        import_type,
        module_specifier,
        imported_name,
    })
}

/// Resolves a comment-only typedef through the exact promoted CommonJS export.
pub(super) fn resolve_source_jsdoc_typedef_import(
    store: &CanonicalTypeMapperStore,
    alias_host: &ProductionAliasTargetHost<'_, '_, '_>,
    declared_host: &DeclaredTypeHost<'_>,
    plan: SourceJsDocTypedefImportPlan,
) -> Result<ResolvedSourceJsDocTypedefImport, SourceImportError> {
    let (resolved, module_symbol) = alias_host
        .resolve_jsdoc_import_type_module(store, plan.import_type, plan.module_specifier)
        .map_err(|reason| {
            SourceImportError::Alias(CanonicalAliasResolutionError::TargetUnavailable {
                alias: plan.local_symbol,
                reason,
            })
        })?;
    let module = store
        .symbol(module_symbol)
        .ok_or_else(|| invariant(SourceImportInvariant::InvalidTargetSymbol(module_symbol)))?;
    let exports = module
        .exports()
        .and_then(|exports| store.symbol_table(exports))
        .ok_or_else(|| invariant(SourceImportInvariant::InvalidTargetSymbol(module_symbol)))?;
    let promoted_symbol = exports
        .get(InternalSymbolName::ExportEquals.as_ref())
        .ok_or_else(|| {
            unsupported(SourceImportUnsupported::TargetTypeNotExported(
                plan.import_type,
            ))
        })?;
    if !super::alias::is_promoted_commonjs_export_alias(store, promoted_symbol) {
        return Err(invariant(SourceImportInvariant::InvalidTargetSymbol(
            promoted_symbol,
        )));
    }
    let qualifier = declared_host
        .node(plan.imported_name)
        .and_then(|record| match &record.data {
            NodeData::Identifier(identifier) => Some(identifier.text.as_str()),
            _ => None,
        })
        .ok_or_else(|| invariant(SourceImportInvariant::InvalidNode(plan.imported_name)))?;
    let target_symbol = exports.get_source(qualifier).ok_or_else(|| {
        unsupported(SourceImportUnsupported::TargetTypeNotExported(
            plan.import_type,
        ))
    })?;
    let promoted_target = store
        .symbol(promoted_symbol)
        .and_then(ts_binder::semantic::Symbol::exports)
        .and_then(|exports| store.symbol_table(exports))
        .and_then(|exports| exports.get_source(qualifier));
    if promoted_target != Some(target_symbol)
        || store.get_parent_of_symbol(target_symbol) != Some(module_symbol)
        || store.get_merged_symbol(target_symbol) != Some(target_symbol)
        || store
            .symbol_node_links(plan.imported_name)
            .and_then(|links| links.resolved_symbol)
            .is_some_and(|cached| cached != target_symbol)
    {
        return Err(invariant(SourceImportInvariant::InvalidTargetSymbol(
            target_symbol,
        )));
    }

    let target_declaration =
        plan_direct_exported_type_target(store, declared_host, plan.local_symbol, target_symbol)?;
    let target = store
        .symbol(target_symbol)
        .ok_or_else(|| invariant(SourceImportInvariant::InvalidTargetSymbol(target_symbol)))?;
    let target_facts = declared_host
        .bound_file(target_declaration)
        .and_then(BoundFile::source_facts);
    if target.flags() != SymbolFlags::TYPE_ALIAS
        || target_declaration.file != resolved.target_file()
        || target_declaration.file == plan.local_declaration.file
        || target_facts
            .is_none_or(|facts| !facts.is_javascript_file() || !facts.is_common_js_module())
    {
        return Err(unsupported(SourceImportUnsupported::TargetTypeDeclaration(
            target_declaration,
        )));
    }

    Ok(ResolvedSourceJsDocTypedefImport {
        plan,
        module_symbol,
        target_symbol,
        target_declaration,
    })
}

/// Proves a top-level `import name = require("module")` or local namespace alias.
///
/// The returned binding uses the same alias-resolution and value-publication
/// path as ordinary imports. Local aliases retain their reference node in
/// `module_specifier`; only external aliases require a module-manifest entry.
pub(super) fn plan_top_level_import_equals(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    declaration: NodeRef,
) -> Result<SourceImportPlan, SourceImportError> {
    let source = bound.source_file();
    validate_source_identity(arena, bound, store, source)?;
    let facts = bound
        .source_facts()
        .ok_or_else(|| invariant(SourceImportInvariant::MissingSourceFacts(source)))?;
    if facts.is_javascript_file() {
        return Err(unsupported(SourceImportUnsupported::JavaScriptSource(
            source,
        )));
    }

    let source_record = checked_node(arena, bound, store, source)?;
    let NodeData::SourceFile(source_data) = &source_record.data else {
        return Err(invariant(SourceImportInvariant::InvalidSource(source)));
    };
    let record = checked_node(arena, bound, store, declaration)?;
    let NodeData::ImportEqualsDeclaration(import) = &record.data else {
        return Err(unsupported(SourceImportUnsupported::Declaration {
            node: declaration,
            kind: record.kind,
        }));
    };
    if record.kind != SyntaxKind::ImportEqualsDeclaration
        || record.parent != Some(source.node)
        || record.flags.0 != 0
        || !range_contains(source_record, record)
        || import.flow_node.is_some()
        || import.local_symbol.is_some()
        || import.symbol.is_some()
        || import.facts != 0
        || source_data
            .statements
            .nodes
            .iter()
            .filter(|node| **node == declaration.node)
            .count()
            != 1
    {
        return Err(unsupported(SourceImportUnsupported::ImportShape(
            declaration,
        )));
    }
    let exported = if import.modifiers.is_some() {
        if !facts.is_external_module()
            || !has_exact_modifier_sequence(
                arena,
                bound,
                store,
                declaration,
                import.modifiers.as_ref(),
                &[(SyntaxKind::ExportKeyword, "export")],
            )?
        {
            return Err(unsupported(SourceImportUnsupported::ImportShape(
                declaration,
            )));
        }
        true
    } else {
        false
    };

    let reference = NodeRef::new(declaration.arena, declaration.file, import.module_reference);
    let reference_record = checked_node(arena, bound, store, reference)?;
    if reference_record.parent != Some(declaration.node) || reference_record.flags.0 != 0 {
        return Err(unsupported(SourceImportUnsupported::ImportShape(reference)));
    }
    let module_specifier = match &reference_record.data {
        NodeData::ExternalModuleReference(external)
            if reference_record.kind == SyntaxKind::ExternalModuleReference =>
        {
            let specifier = NodeRef::new(declaration.arena, declaration.file, external.expression);
            let record = checked_node(arena, bound, store, specifier)?;
            if record.parent != Some(reference.node)
                || record.flags.0 != 0
                || !matches!(
                    &record.data,
                    NodeData::StringLiteral(literal)
                        if record.kind == SyntaxKind::StringLiteral
                            && literal.token_flags.0 == 0
                            && !literal.text.is_empty()
                )
            {
                return Err(unsupported(SourceImportUnsupported::ImportShape(specifier)));
            }
            specifier
        }
        NodeData::Identifier(identifier)
            if reference_record.kind == SyntaxKind::Identifier
                && identifier.flow_node.is_none()
                && !identifier.text.is_empty() =>
        {
            reference
        }
        NodeData::QualifiedName(_) if reference_record.kind == SyntaxKind::QualifiedName => {
            reference
        }
        _ => return Err(unsupported(SourceImportUnsupported::ImportShape(reference))),
    };

    let local_name = NodeRef::new(declaration.arena, declaration.file, import.name);
    let local_text = exact_identifier(
        arena,
        bound,
        store,
        local_name,
        declaration,
        SourceImportUnsupported::NonIdentifierLocalName(local_name),
    )?;
    let alias_symbol = bound
        .symbol(declaration)
        .ok_or_else(|| invariant(SourceImportInvariant::MissingAliasSymbol(declaration)))?;
    if exported {
        validate_reexport_alias_symbol(
            bound,
            store,
            source,
            alias_symbol,
            declaration,
            local_name,
            &local_text,
        )?;
    } else {
        validate_alias_symbol(store, alias_symbol, declaration, local_name, &local_text)?;
    }
    if import.is_type_only {
        preflight_type_import_value_links(store, alias_symbol)?;
    } else {
        preflight_alias_value_links(store, alias_symbol)?;
    }

    Ok(SourceImportPlan {
        declaration,
        module_specifier,
        bindings: vec![SourceImportBindingPlan {
            declaration,
            imported_name: local_name,
            local_name,
            imported_text: "*".to_owned(),
            local_text,
            alias_symbol,
        }],
    })
}

fn plan_top_level_named_import(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    declaration: NodeRef,
    phase: SourceImportPhase,
) -> Result<SourceImportPlan, SourceImportError> {
    let source = bound.source_file();
    validate_source_identity(arena, bound, store, source)?;
    let facts = bound
        .source_facts()
        .ok_or_else(|| invariant(SourceImportInvariant::MissingSourceFacts(source)))?;
    if facts.is_javascript_file() && phase == SourceImportPhase::Type {
        return Err(unsupported(SourceImportUnsupported::JavaScriptSource(
            source,
        )));
    }
    if facts.is_common_js_module() && !facts.is_javascript_file() {
        return Err(unsupported(SourceImportUnsupported::CommonJsSource(source)));
    }
    if !facts.is_external_module() {
        return Err(unsupported(SourceImportUnsupported::ScriptSource(source)));
    }
    let source_record = checked_node(arena, bound, store, source)?;
    let NodeData::SourceFile(source_data) = &source_record.data else {
        return Err(invariant(SourceImportInvariant::InvalidSource(source)));
    };
    let record = checked_node(arena, bound, store, declaration)?;
    let NodeData::ImportDeclaration(import) = &record.data else {
        return Err(unsupported(SourceImportUnsupported::Declaration {
            node: declaration,
            kind: record.kind,
        }));
    };
    if record.kind != SyntaxKind::ImportDeclaration {
        return Err(unsupported(SourceImportUnsupported::Declaration {
            node: declaration,
            kind: record.kind,
        }));
    }
    if record.parent != Some(source.node)
        || !range_contains(source_record, record)
        || source_data
            .statements
            .nodes
            .iter()
            .filter(|node| **node == declaration.node)
            .count()
            != 1
    {
        return Err(invariant(
            SourceImportInvariant::InvalidTopLevelDeclaration(declaration),
        ));
    }
    if record.flags.0 != 0
        || import.flow_node.is_some()
        || import.symbol.is_some()
        || import.facts != 0
        || import.modifiers.is_some()
    {
        return Err(unsupported(SourceImportUnsupported::ImportShape(
            declaration,
        )));
    }
    if let Some(attributes) = import.attributes {
        if phase != SourceImportPhase::Value {
            return Err(unsupported(SourceImportUnsupported::ImportAttributes(
                declaration,
            )));
        }
        validate_value_import_attributes(
            arena,
            bound,
            store,
            declaration,
            NodeRef::new(declaration.arena, declaration.file, attributes),
        )?;
    }

    let module_specifier =
        NodeRef::new(declaration.arena, declaration.file, import.module_specifier);
    let specifier_record = checked_node(arena, bound, store, module_specifier)?;
    if specifier_record.kind != SyntaxKind::StringLiteral
        || specifier_record.parent != Some(declaration.node)
        || specifier_record.flags.0 != 0
        || !range_contains(record, specifier_record)
        || !matches!(
            &specifier_record.data,
            NodeData::StringLiteral(literal) if literal.token_flags.0 == 0 && !literal.text.is_empty()
        )
    {
        return Err(unsupported(SourceImportUnsupported::ImportShape(
            module_specifier,
        )));
    }

    let Some(clause) = import
        .import_clause
        .map(|node| NodeRef::new(declaration.arena, declaration.file, node))
    else {
        if phase != SourceImportPhase::Value {
            return Err(unsupported(SourceImportUnsupported::ImportClause(
                declaration,
            )));
        }
        return Ok(SourceImportPlan {
            declaration,
            module_specifier,
            bindings: Vec::new(),
        });
    };
    let clause_record = checked_node(arena, bound, store, clause)?;
    let NodeData::ImportClause(clause_data) = &clause_record.data else {
        return Err(unsupported(SourceImportUnsupported::ImportClause(clause)));
    };
    if clause_record.kind != SyntaxKind::ImportClause
        || clause_record.parent != Some(declaration.node)
        || clause_record.flags.0 != 0
        || !range_contains(record, clause_record)
        || clause_data.local_symbol.is_some()
        || clause_data.symbol.is_some()
        || clause_data.facts != 0
    {
        return Err(unsupported(SourceImportUnsupported::ImportClause(clause)));
    }
    if clause_data.phase_modifier
        != match phase {
            SourceImportPhase::Value => None,
            SourceImportPhase::Type => Some(SyntaxKind::TypeKeyword),
        }
    {
        if clause_data.phase_modifier == Some(SyntaxKind::TypeKeyword) {
            return Err(unsupported(SourceImportUnsupported::TypeOnly(clause)));
        }
        return Err(unsupported(SourceImportUnsupported::ImportClause(clause)));
    }
    let named = clause_data
        .named_bindings
        .map(|node| NodeRef::new(declaration.arena, declaration.file, node));
    if clause_data.name.is_none() && named.is_none() {
        return Err(unsupported(SourceImportUnsupported::NamedBindings(clause)));
    }

    let named_count = match named {
        Some(named) => match &checked_node(arena, bound, store, named)?.data {
            NodeData::NamedImports(named) => named.elements.nodes.len(),
            NodeData::NamespaceImport(_) => 1,
            _ => 0,
        },
        None => 0,
    };
    let binding_capacity = usize::from(clause_data.name.is_some()) + named_count;
    let mut aliases = HashSet::with_capacity(binding_capacity);
    let mut local_names = HashSet::with_capacity(binding_capacity);
    let mut bindings = Vec::with_capacity(binding_capacity);

    if let Some(name) = clause_data.name {
        let local_name = NodeRef::new(declaration.arena, declaration.file, name);
        let local_text = exact_identifier(
            arena,
            bound,
            store,
            local_name,
            clause,
            SourceImportUnsupported::NonIdentifierLocalName(local_name),
        )?;
        let alias_symbol = bound
            .symbol(clause)
            .ok_or_else(|| invariant(SourceImportInvariant::MissingAliasSymbol(clause)))?;
        if phase == SourceImportPhase::Value {
            if store
                .symbol(alias_symbol)
                .is_some_and(|record| record.export_symbol().is_some())
                && !import_alias_is_exported_type_local(
                    bound,
                    store,
                    alias_symbol,
                    clause,
                    &local_text,
                )
            {
                return Err(invariant(SourceImportInvariant::InvalidAliasSymbol(
                    alias_symbol,
                )));
            }
            validate_alias_symbol(store, alias_symbol, clause, local_name, &local_text)?;
            preflight_alias_value_links(store, alias_symbol)?;
        }
        aliases.insert(alias_symbol);
        local_names.insert(local_text.clone());
        bindings.push(SourceImportBindingPlan {
            declaration: clause,
            imported_name: local_name,
            local_name,
            imported_text: "default".to_owned(),
            local_text,
            alias_symbol,
        });
    }

    if let Some(namespace) = named.filter(|named| {
        checked_node(arena, bound, store, *named)
            .is_ok_and(|record| matches!(record.data, NodeData::NamespaceImport(_)))
    }) {
        let namespace_record = checked_node(arena, bound, store, namespace)?;
        let NodeData::NamespaceImport(namespace_data) = &namespace_record.data else {
            return Err(unsupported(SourceImportUnsupported::NamedBindings(
                namespace,
            )));
        };
        if phase != SourceImportPhase::Value {
            return Err(unsupported(SourceImportUnsupported::TypeOnly(namespace)));
        }
        if namespace_record.kind != SyntaxKind::NamespaceImport
            || namespace_record.parent != Some(clause.node)
            || namespace_record.flags.0 != 0
            || !range_contains(clause_record, namespace_record)
            || namespace_data.local_symbol.is_some()
            || namespace_data.symbol.is_some()
        {
            return Err(unsupported(SourceImportUnsupported::NamedBindings(
                namespace,
            )));
        }

        let local_name = NodeRef::new(declaration.arena, declaration.file, namespace_data.name);
        let local_text = exact_identifier(
            arena,
            bound,
            store,
            local_name,
            namespace,
            SourceImportUnsupported::NonIdentifierLocalName(local_name),
        )?;
        let alias_symbol = bound
            .symbol(namespace)
            .ok_or_else(|| invariant(SourceImportInvariant::MissingAliasSymbol(namespace)))?;
        if store
            .symbol(alias_symbol)
            .is_some_and(|record| record.export_symbol().is_some())
            && !import_alias_is_exported_type_local(
                bound,
                store,
                alias_symbol,
                namespace,
                &local_text,
            )
        {
            return Err(invariant(SourceImportInvariant::InvalidAliasSymbol(
                alias_symbol,
            )));
        }
        validate_alias_symbol(store, alias_symbol, namespace, local_name, &local_text)?;
        if !aliases.insert(alias_symbol) {
            return Err(invariant(SourceImportInvariant::DuplicateAlias(
                alias_symbol,
            )));
        }
        if !local_names.insert(local_text.clone()) {
            return Err(invariant(SourceImportInvariant::DuplicateLocalName(
                local_name,
            )));
        }
        preflight_alias_value_links(store, alias_symbol)?;
        bindings.push(SourceImportBindingPlan {
            declaration: namespace,
            imported_name: local_name,
            local_name,
            imported_text: "*".to_owned(),
            local_text,
            alias_symbol,
        });
    } else if let Some(named) = named {
        let named_record = checked_node(arena, bound, store, named)?;
        let NodeData::NamedImports(named_data) = &named_record.data else {
            return Err(unsupported(SourceImportUnsupported::NamedBindings(named)));
        };
        if named_record.kind != SyntaxKind::NamedImports
            || named_record.parent != Some(clause.node)
            || named_record.flags.0 != 0
            || !range_contains(clause_record, named_record)
            || named_data.facts != 0
            || named_data.elements.range != named_record.range
            || named_data.elements.has_trailing_comma
        {
            return Err(unsupported(SourceImportUnsupported::NamedBindings(named)));
        }
        for &binding in &named_data.elements.nodes {
            let binding = NodeRef::new(declaration.arena, declaration.file, binding);
            let binding_record = checked_node(arena, bound, store, binding)?;
            let NodeData::ImportSpecifier(specifier) = &binding_record.data else {
                return Err(unsupported(SourceImportUnsupported::Binding(binding)));
            };
            if binding_record.kind != SyntaxKind::ImportSpecifier
                || binding_record.parent != Some(named.node)
                || binding_record.flags.0 != 0
                || !range_contains(named_record, binding_record)
                || specifier.local_symbol.is_some()
                || specifier.symbol.is_some()
                || specifier.facts != 0
            {
                return Err(unsupported(SourceImportUnsupported::Binding(binding)));
            }
            if specifier.is_type_only {
                return Err(unsupported(SourceImportUnsupported::TypeOnly(binding)));
            }

            let imported_name = NodeRef::new(
                declaration.arena,
                declaration.file,
                specifier.property_name.unwrap_or(specifier.name),
            );
            let local_name = NodeRef::new(declaration.arena, declaration.file, specifier.name);
            let imported_text = exact_identifier(
                arena,
                bound,
                store,
                imported_name,
                binding,
                SourceImportUnsupported::NonIdentifierImportName(imported_name),
            )?;
            let local_text = exact_identifier(
                arena,
                bound,
                store,
                local_name,
                binding,
                SourceImportUnsupported::NonIdentifierLocalName(local_name),
            )?;

            let alias_symbol = bound
                .symbol(binding)
                .ok_or_else(|| invariant(SourceImportInvariant::MissingAliasSymbol(binding)))?;
            if store
                .symbol(alias_symbol)
                .is_some_and(|record| record.export_symbol().is_some())
                && !import_alias_is_exported_type_local(
                    bound,
                    store,
                    alias_symbol,
                    binding,
                    &local_text,
                )
            {
                return Err(invariant(SourceImportInvariant::InvalidAliasSymbol(
                    alias_symbol,
                )));
            }
            if phase == SourceImportPhase::Type {
                if !local_names.insert(local_text.clone()) || !aliases.insert(alias_symbol) {
                    return Err(unsupported(SourceImportUnsupported::Binding(binding)));
                }
            } else {
                validate_alias_symbol(store, alias_symbol, binding, local_name, &local_text)?;
                if !aliases.insert(alias_symbol) {
                    return Err(invariant(SourceImportInvariant::DuplicateAlias(
                        alias_symbol,
                    )));
                }
                if !local_names.insert(local_text.clone()) {
                    return Err(invariant(SourceImportInvariant::DuplicateLocalName(
                        local_name,
                    )));
                }
                preflight_alias_value_links(store, alias_symbol)?;
            }
            bindings.push(SourceImportBindingPlan {
                declaration: binding,
                imported_name,
                local_name,
                imported_text,
                local_text,
                alias_symbol,
            });
        }
    }

    if phase == SourceImportPhase::Type {
        for binding in &bindings {
            validate_alias_symbol(
                store,
                binding.alias_symbol,
                binding.declaration,
                binding.local_name,
                &binding.local_text,
            )?;
            preflight_type_import_value_links(store, binding.alias_symbol)?;
        }
    }

    Ok(SourceImportPlan {
        declaration,
        module_specifier,
        bindings,
    })
}

fn validate_value_import_attributes(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    declaration: NodeRef,
    attributes: NodeRef,
) -> Result<(), SourceImportError> {
    let declaration_record = checked_node(arena, bound, store, declaration)?;
    let record = checked_node(arena, bound, store, attributes)?;
    let NodeData::ImportAttributes(data) = &record.data else {
        return Err(unsupported(SourceImportUnsupported::ImportAttributes(
            attributes,
        )));
    };
    if record.kind != SyntaxKind::ImportAttributes
        || record.flags.0 != 0
        || record.parent != Some(declaration.node)
        || !range_contains(declaration_record, record)
        || data.token != SyntaxKind::WithKeyword
        || data.facts != 0
        || data.attributes.nodes.is_empty()
        || data.attributes.range.start < record.range.start
        || data.attributes.range.end > record.range.end
    {
        return Err(unsupported(SourceImportUnsupported::ImportAttributes(
            attributes,
        )));
    }

    let mut names = HashSet::with_capacity(data.attributes.nodes.len());
    let mut previous_end = data.attributes.range.start;
    for attribute in &data.attributes.nodes {
        let attribute = NodeRef::new(attributes.arena, attributes.file, *attribute);
        let attribute_record = checked_node(arena, bound, store, attribute)?;
        let NodeData::ImportAttribute(entry) = &attribute_record.data else {
            return Err(unsupported(SourceImportUnsupported::ImportAttributes(
                attribute,
            )));
        };
        if attribute_record.kind != SyntaxKind::ImportAttribute
            || attribute_record.flags.0 != 0
            || attribute_record.parent != Some(attributes.node)
            || attribute_record.range.start < previous_end
            || attribute_record.range.end > data.attributes.range.end
            || entry.facts != 0
        {
            return Err(unsupported(SourceImportUnsupported::ImportAttributes(
                attribute,
            )));
        }
        let name = NodeRef::new(attribute.arena, attribute.file, entry.name);
        let name_record = checked_node(arena, bound, store, name)?;
        let text = match &name_record.data {
            NodeData::Identifier(identifier)
                if name_record.kind == SyntaxKind::Identifier && identifier.flow_node.is_none() =>
            {
                identifier.text.as_str()
            }
            NodeData::StringLiteral(literal)
                if name_record.kind == SyntaxKind::StringLiteral && literal.token_flags.0 == 0 =>
            {
                literal.text.as_str()
            }
            _ => {
                return Err(unsupported(SourceImportUnsupported::ImportAttributes(name)));
            }
        };
        if name_record.flags.0 != 0
            || name_record.parent != Some(attribute.node)
            || !range_contains(attribute_record, name_record)
            || text.is_empty()
            || !names.insert(text)
        {
            return Err(unsupported(SourceImportUnsupported::ImportAttributes(name)));
        }

        let value = NodeRef::new(attribute.arena, attribute.file, entry.value);
        let value_record = checked_node(arena, bound, store, value)?;
        if value_record.parent != Some(attribute.node)
            || value_record.flags.0 != 0
            || value_record.range.start < name_record.range.end
            || value_record.range.end != attribute_record.range.end
            || !matches!(
                &value_record.data,
                NodeData::StringLiteral(literal)
                    if value_record.kind == SyntaxKind::StringLiteral
                        && literal.token_flags.0 == 0
            )
        {
            return Err(unsupported(SourceImportUnsupported::ImportAttributes(
                value,
            )));
        }
        previous_end = attribute_record.range.end;
    }
    Ok(())
}

/// Proves one complete top-level named or namespace reexport without checker writes.
///
/// Identifier-named `export { source as public } from "./target"` and
/// `export * as public from "./target"` forms are admitted. Named bindings
/// can use `default`. Star, local, attribute-bearing, and `CommonJS` forms
/// require separate module support.
#[cfg_attr(not(test), allow(dead_code))]
#[allow(clippy::too_many_lines)] // One exact export-declaration provenance walk.
pub(super) fn plan_top_level_named_reexport(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    declaration: NodeRef,
) -> Result<SourceNamedReexportPlan, SourceImportError> {
    let source = bound.source_file();
    validate_source_identity(arena, bound, store, source)?;
    let facts = bound
        .source_facts()
        .ok_or_else(|| invariant(SourceImportInvariant::MissingSourceFacts(source)))?;
    if facts.is_common_js_module() && !facts.is_javascript_file() {
        return Err(unsupported(SourceImportUnsupported::CommonJsSource(source)));
    }
    if !facts.is_external_module() {
        return Err(unsupported(SourceImportUnsupported::ScriptSource(source)));
    }
    let source_record = checked_node(arena, bound, store, source)?;
    let NodeData::SourceFile(source_data) = &source_record.data else {
        return Err(invariant(SourceImportInvariant::InvalidSource(source)));
    };
    let record = checked_node(arena, bound, store, declaration)?;
    let NodeData::ExportDeclaration(export) = &record.data else {
        return Err(unsupported(SourceImportUnsupported::Declaration {
            node: declaration,
            kind: record.kind,
        }));
    };
    if record.kind != SyntaxKind::ExportDeclaration {
        return Err(unsupported(SourceImportUnsupported::Declaration {
            node: declaration,
            kind: record.kind,
        }));
    }
    if record.parent != Some(source.node)
        || !range_contains(source_record, record)
        || source_data
            .statements
            .nodes
            .iter()
            .filter(|node| **node == declaration.node)
            .count()
            != 1
    {
        return Err(invariant(
            SourceImportInvariant::InvalidTopLevelDeclaration(declaration),
        ));
    }
    if record.flags.0 != 0
        || export.flow_node.is_some()
        || export.symbol.is_some()
        || export.facts != 0
        || export.modifiers.is_some()
    {
        return Err(unsupported(SourceImportUnsupported::ExportShape(
            declaration,
        )));
    }
    if export.attributes.is_some() {
        return Err(unsupported(SourceImportUnsupported::ExportAttributes(
            declaration,
        )));
    }

    let module_specifier = export
        .module_specifier
        .map(|node| NodeRef::new(declaration.arena, declaration.file, node))
        .ok_or_else(|| unsupported(SourceImportUnsupported::ExportShape(declaration)))?;
    let specifier_record = checked_node(arena, bound, store, module_specifier)?;
    if specifier_record.kind != SyntaxKind::StringLiteral
        || specifier_record.parent != Some(declaration.node)
        || specifier_record.flags.0 != 0
        || !range_contains(record, specifier_record)
        || !matches!(
            &specifier_record.data,
            NodeData::StringLiteral(literal) if literal.token_flags.0 == 0 && !literal.text.is_empty()
        )
    {
        return Err(unsupported(SourceImportUnsupported::ExportShape(
            module_specifier,
        )));
    }

    let clause = export
        .export_clause
        .map(|node| NodeRef::new(declaration.arena, declaration.file, node))
        .ok_or_else(|| unsupported(SourceImportUnsupported::ExportClause(declaration)))?;
    let clause_record = checked_node(arena, bound, store, clause)?;
    if let NodeData::NamespaceExport(namespace) = &clause_record.data {
        if clause_record.kind != SyntaxKind::NamespaceExport
            || clause_record.parent != Some(declaration.node)
            || clause_record.flags.0 != 0
            || !range_contains(record, clause_record)
            || namespace.symbol.is_some()
        {
            return Err(unsupported(SourceImportUnsupported::ExportClause(clause)));
        }

        let exported_name = NodeRef::new(declaration.arena, declaration.file, namespace.name);
        let exported_text = exact_identifier(
            arena,
            bound,
            store,
            exported_name,
            clause,
            SourceImportUnsupported::NonIdentifierExportName(exported_name),
        )?;
        let alias_symbol = bound
            .symbol(clause)
            .ok_or_else(|| invariant(SourceImportInvariant::MissingAliasSymbol(clause)))?;
        validate_reexport_alias_symbol(
            bound,
            store,
            source,
            alias_symbol,
            clause,
            exported_name,
            &exported_text,
        )?;
        if export.is_type_only {
            preflight_type_import_value_links(store, alias_symbol)?;
        } else {
            preflight_alias_value_links(store, alias_symbol)?;
        }

        return Ok(SourceNamedReexportPlan {
            declaration,
            module_specifier,
            bindings: vec![SourceNamedReexportBindingPlan {
                declaration: clause,
                imported_name: exported_name,
                exported_name,
                imported_text: "*".to_owned(),
                exported_text,
                alias_symbol,
                syntactic_type_only: export.is_type_only,
            }],
        });
    }
    let NodeData::NamedExports(named) = &clause_record.data else {
        return Err(unsupported(SourceImportUnsupported::ExportClause(clause)));
    };
    if clause_record.kind != SyntaxKind::NamedExports
        || clause_record.parent != Some(declaration.node)
        || clause_record.flags.0 != 0
        || !range_contains(record, clause_record)
        || named.facts != 0
        || named.elements.range != clause_record.range
        || named.elements.has_trailing_comma
    {
        return Err(unsupported(SourceImportUnsupported::ExportClause(clause)));
    }
    if named.elements.nodes.is_empty() {
        return Err(unsupported(SourceImportUnsupported::EmptyNamedExports(
            clause,
        )));
    }

    let mut aliases = HashSet::with_capacity(named.elements.nodes.len());
    let mut exported_names = HashSet::with_capacity(named.elements.nodes.len());
    let mut bindings = Vec::with_capacity(named.elements.nodes.len());
    for &binding in &named.elements.nodes {
        let binding = NodeRef::new(declaration.arena, declaration.file, binding);
        let binding_record = checked_node(arena, bound, store, binding)?;
        let NodeData::ExportSpecifier(specifier) = &binding_record.data else {
            return Err(unsupported(SourceImportUnsupported::ExportBinding(binding)));
        };
        if binding_record.kind != SyntaxKind::ExportSpecifier
            || binding_record.parent != Some(clause.node)
            || binding_record.flags.0 != 0
            || !range_contains(clause_record, binding_record)
            || specifier.local_symbol.is_some()
            || specifier.symbol.is_some()
            || specifier.facts != 0
        {
            return Err(unsupported(SourceImportUnsupported::ExportBinding(binding)));
        }

        let imported_name = NodeRef::new(
            declaration.arena,
            declaration.file,
            specifier.property_name.unwrap_or(specifier.name),
        );
        let exported_name = NodeRef::new(declaration.arena, declaration.file, specifier.name);
        let imported_text = exact_identifier(
            arena,
            bound,
            store,
            imported_name,
            binding,
            SourceImportUnsupported::NonIdentifierReexportName(imported_name),
        )?;
        let exported_text = exact_identifier(
            arena,
            bound,
            store,
            exported_name,
            binding,
            SourceImportUnsupported::NonIdentifierExportName(exported_name),
        )?;
        let alias_symbol = bound
            .symbol(binding)
            .ok_or_else(|| invariant(SourceImportInvariant::MissingAliasSymbol(binding)))?;
        if !aliases.insert(alias_symbol) {
            return Err(invariant(SourceImportInvariant::DuplicateAlias(
                alias_symbol,
            )));
        }
        if !exported_names.insert(exported_text.clone()) {
            return Err(invariant(SourceImportInvariant::DuplicateExportName(
                exported_name,
            )));
        }
        validate_reexport_alias_symbol(
            bound,
            store,
            source,
            alias_symbol,
            binding,
            exported_name,
            &exported_text,
        )?;
        let syntactic_type_only = export.is_type_only || specifier.is_type_only;
        if syntactic_type_only {
            preflight_type_import_value_links(store, alias_symbol)?;
        } else {
            preflight_alias_value_links(store, alias_symbol)?;
        }
        bindings.push(SourceNamedReexportBindingPlan {
            declaration: binding,
            imported_name,
            exported_name,
            imported_text,
            exported_text,
            alias_symbol,
            syntactic_type_only,
        });
    }

    Ok(SourceNamedReexportPlan {
        declaration,
        module_specifier,
        bindings,
    })
}

/// Resolves one named reexport through the exact module manifest.
///
/// The immediate alias identity is retained separately from the final target
/// so a consumer can prove every named hop without reconstructing an export
/// table. No value or declared type is queried here.
#[cfg_attr(not(test), allow(dead_code))]
#[allow(clippy::too_many_lines)] // Immediate/final cache proof is one transaction.
pub(super) fn resolve_source_named_reexport_binding(
    store: &mut CanonicalTypeMapperStore,
    alias_host: &mut ProductionAliasTargetHost<'_, '_, '_>,
    binding: &SourceNamedReexportBindingPlan,
) -> Result<ResolvedSourceNamedReexportBinding, SourceImportError> {
    let alias = binding.alias_symbol;
    let record = store
        .symbol(alias)
        .ok_or_else(|| invariant(SourceImportInvariant::InvalidAliasSymbol(alias)))?;
    if record.flags() != SymbolFlags::ALIAS
        || record.check_flags() != CheckFlags::NONE
        || record.declarations() != Some(&[binding.declaration])
        || record.value_declaration().is_some()
        || record.members().is_some()
        || record.exports().is_some()
        || record.parent().is_none()
        || record.export_symbol().is_some()
        || record.name().as_bytes() != binding.exported_text.as_bytes()
        || store.get_merged_symbol(alias) != Some(alias)
    {
        return Err(invariant(SourceImportInvariant::InvalidAliasSymbol(alias)));
    }
    if binding.syntactic_type_only && !store.ensure_alias_symbol_links(alias) {
        return Err(invariant(SourceImportInvariant::InvalidAliasLinks(alias)));
    }

    let independently_derived = alias_host
        .get_target_of_alias_declaration(store, alias)
        .map_err(|reason| {
            SourceImportError::Alias(CanonicalAliasResolutionError::TargetUnavailable {
                alias,
                reason,
            })
        })?;
    let CanonicalImmediateAliasTarget::Resolved(immediate_target) = independently_derived else {
        return Err(invariant(SourceImportInvariant::InvalidAliasLinks(alias)));
    };
    let immediate_flags = store
        .symbol(immediate_target)
        .ok_or_else(|| invariant(SourceImportInvariant::InvalidTargetSymbol(immediate_target)))?
        .flags();
    let immediate_is_alias = source_import_target_is_authenticated_alias(store, immediate_target)?;
    if let Some(links) = store.alias_symbol_links(alias)
        && (links
            .immediate_target
            .is_some_and(|cached| cached != immediate_target)
            || (!immediate_is_alias
                && match links.alias_target {
                    AliasTargetState::Unresolved => false,
                    AliasTargetState::Resolved(cached) => cached != immediate_target,
                    AliasTargetState::Unknown => true,
                }))
    {
        return Err(invariant(SourceImportInvariant::InvalidAliasLinks(alias)));
    }

    let immediate =
        CanonicalAliasResolver::new(store, alias_host).get_immediate_aliased_symbol(alias)?;
    if immediate != Some(immediate_target) {
        return Err(invariant(SourceImportInvariant::InvalidAliasLinks(alias)));
    }
    let resolution = CanonicalAliasResolver::new(store, alias_host).resolve_alias(alias)?;
    let target = match resolution.target {
        AliasTargetState::Unknown if immediate_is_alias => {
            return Err(SourceImportError::CircularAlias {
                alias,
                events: resolution.events,
            });
        }
        AliasTargetState::Unknown | AliasTargetState::Unresolved => {
            return Err(invariant(SourceImportInvariant::InvalidAliasLinks(alias)));
        }
        AliasTargetState::Resolved(target) if !resolution.events.is_empty() => {
            return Err(SourceImportError::CircularAlias {
                alias,
                events: resolution.events,
            });
        }
        AliasTargetState::Resolved(target) => target,
    };
    if immediate_flags != SymbolFlags::ALIAS && immediate_is_alias && target == immediate_target {
        return Err(unsupported(SourceImportUnsupported::TargetSymbol {
            alias,
            target,
            flags: immediate_flags,
        }));
    }
    let (independent_immediate, independent_target) =
        independently_resolve_source_alias_chain(store, alias_host, alias)?;
    if independent_immediate != immediate_target || independent_target != target {
        return Err(invariant(SourceImportInvariant::InvalidAliasLinks(alias)));
    }
    if !immediate_is_alias && target != immediate_target {
        return Err(invariant(SourceImportInvariant::InvalidAliasLinks(alias)));
    }

    let links = store
        .alias_symbol_links(alias)
        .ok_or_else(|| invariant(SourceImportInvariant::InvalidAliasLinks(alias)))?;
    let expected_type_only = if binding.syntactic_type_only {
        Some(binding.declaration)
    } else if immediate_is_alias {
        store
            .alias_symbol_links(immediate_target)
            .ok_or_else(|| invariant(SourceImportInvariant::InvalidAliasLinks(immediate_target)))?
            .type_only_declaration
    } else {
        None
    };
    if expected_type_only.is_some() {
        preflight_type_import_value_links(store, alias)?;
    }
    if links.immediate_target != Some(immediate_target)
        || links.alias_target != AliasTargetState::Resolved(target)
        || links.type_only_declaration != expected_type_only
    {
        return Err(invariant(SourceImportInvariant::InvalidAliasLinks(alias)));
    }

    Ok(ResolvedSourceNamedReexportBinding {
        binding: binding.clone(),
        immediate_target_symbol: immediate_target,
        target_symbol: target,
        type_only_declaration: links.type_only_declaration,
    })
}

/// Proves that an identifier expression reads the supplied import binding.
pub(super) fn plan_source_import_identifier_read(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    binding: &SourceImportBindingPlan,
    node: NodeRef,
    name: &str,
    resolved_alias: SemanticSymbolId,
) -> Result<PlannedSourceImportRead, SourceImportError> {
    let record = checked_node(arena, bound, store, node)?;
    if record.kind != SyntaxKind::Identifier
        || record.flags.0 != 0
        || !matches!(
            &record.data,
            NodeData::Identifier(identifier)
                if identifier.flow_node.is_none() && identifier.text == name
        )
        || name != binding.local_text
        || resolved_alias != binding.alias_symbol
    {
        return Err(invariant(SourceImportInvariant::ReadBindingMismatch(node)));
    }
    validate_alias_symbol(
        store,
        binding.alias_symbol,
        binding.declaration,
        binding.local_name,
        &binding.local_text,
    )?;
    if store.symbol_node_links(node).is_some_and(|links| {
        links
            .resolved_symbol
            .is_some_and(|cached| cached != binding.alias_symbol)
    }) {
        return Err(invariant(SourceImportInvariant::InvalidIdentifierCache(
            node,
        )));
    }
    preflight_alias_value_links(store, binding.alias_symbol)?;
    Ok(PlannedSourceImportRead {
        node,
        resolved_symbol: binding.alias_symbol,
        value_symbol: binding.alias_symbol,
    })
}

/// Resolves one import declaration binding without querying its value type.
///
/// The production host is called directly before any sparse alias cache is
/// trusted. This independently re-derives the immediate target from the exact
/// declaration, module-resolution manifest entry, and target export table.
pub(super) fn resolve_source_import_binding(
    store: &mut CanonicalTypeMapperStore,
    alias_host: &mut ProductionAliasTargetHost<'_, '_, '_>,
    binding: &SourceImportBindingPlan,
) -> Result<ResolvedSourceImportBinding, SourceImportError> {
    resolve_source_import_binding_phase(store, alias_host, binding, SourceImportPhase::Value)
}

/// Resolves a used namespace module's re-export aliases without querying values.
///
/// Source execution calls this immediately before preparing a namespace value,
/// so unused namespace imports retain their existing lazy alias behavior.
#[cfg_attr(not(test), allow(dead_code))]
pub(super) fn resolve_source_import_namespace_exports(
    store: &mut CanonicalTypeMapperStore,
    alias_host: &mut ProductionAliasTargetHost<'_, '_, '_>,
    resolved: &ResolvedSourceImportBinding,
) -> Result<(), SourceImportError> {
    if store.export_type_links(resolved.target_symbol).is_some() {
        authenticate_synthetic_import_namespace_identity(
            store,
            resolved.binding.alias_symbol,
            resolved.target_symbol,
        )?;
        return Ok(());
    }
    let module = store.symbol(resolved.target_symbol).ok_or_else(|| {
        invariant(SourceImportInvariant::InvalidTargetSymbol(
            resolved.target_symbol,
        ))
    })?;
    if !module.flags().intersects(SymbolFlags::MODULE)
        || !module.flags().intersects(SymbolFlags::VALUE)
    {
        return Ok(());
    }
    let Some(exports) = store
        .module_symbol_links(resolved.target_symbol)
        .and_then(|links| links.resolved_exports)
        .or_else(|| module.exports())
    else {
        return Ok(());
    };
    let exports = store.symbol_table(exports).ok_or_else(|| {
        invariant(SourceImportInvariant::InvalidTargetSymbol(
            resolved.target_symbol,
        ))
    })?;
    let aliases = exports
        .iter()
        .filter_map(|(_, symbol)| {
            store
                .symbol(symbol)
                .is_some_and(|record| record.flags() == SymbolFlags::ALIAS)
                .then_some(symbol)
        })
        .collect::<Vec<_>>();

    for alias in aliases {
        if store
            .alias_symbol_links(alias)
            .is_some_and(|links| links.type_only_declaration.is_some())
        {
            continue;
        }
        let resolution = CanonicalAliasResolver::new(store, alias_host).resolve_alias(alias)?;
        let AliasTargetState::Resolved(_) = resolution.target else {
            return Err(SourceImportError::CircularAlias {
                alias,
                events: resolution.events,
            });
        };
        if !resolution.events.is_empty() {
            return Err(SourceImportError::CircularAlias {
                alias,
                events: resolution.events,
            });
        }
        independently_resolve_source_alias_chain(store, alias_host, alias)?;
    }
    Ok(())
}

/// Resolves one type-only import through the exact module manifest and proves
/// that its final target is one explicitly exported type alias or
/// interface. The target's declared type remains lazy.
#[cfg_attr(not(test), allow(dead_code))]
pub(super) fn resolve_source_type_import_binding(
    store: &mut CanonicalTypeMapperStore,
    alias_host: &mut ProductionAliasTargetHost<'_, '_, '_>,
    declared_host: &DeclaredTypeHost<'_>,
    binding: &SourceImportBindingPlan,
) -> Result<ResolvedSourceTypeImportBinding, SourceImportError> {
    let resolved =
        resolve_source_import_binding_phase(store, alias_host, binding, SourceImportPhase::Type)?;
    let target_declaration = plan_direct_exported_type_target(
        store,
        declared_host,
        binding.alias_symbol,
        resolved.target_symbol,
    )?;
    if target_declaration.file == binding.declaration.file {
        return Err(unsupported(SourceImportUnsupported::SameSourceTarget {
            binding: binding.declaration,
            target: target_declaration,
        }));
    }
    Ok(ResolvedSourceTypeImportBinding {
        binding: binding.clone(),
        immediate_target_symbol: resolved.immediate_target_symbol,
        target_symbol: resolved.target_symbol,
        target_declaration,
    })
}

fn resolve_source_import_binding_phase(
    store: &mut CanonicalTypeMapperStore,
    alias_host: &mut ProductionAliasTargetHost<'_, '_, '_>,
    binding: &SourceImportBindingPlan,
    phase: SourceImportPhase,
) -> Result<ResolvedSourceImportBinding, SourceImportError> {
    validate_alias_symbol(
        store,
        binding.alias_symbol,
        binding.declaration,
        binding.local_name,
        &binding.local_text,
    )?;
    if phase == SourceImportPhase::Type && !store.ensure_alias_symbol_links(binding.alias_symbol) {
        return Err(invariant(SourceImportInvariant::InvalidAliasLinks(
            binding.alias_symbol,
        )));
    }

    let independently_derived = alias_host
        .get_target_of_alias_declaration(store, binding.alias_symbol)
        .map_err(|reason| {
            SourceImportError::Alias(CanonicalAliasResolutionError::TargetUnavailable {
                alias: binding.alias_symbol,
                reason,
            })
        })?;
    let CanonicalImmediateAliasTarget::Resolved(direct_target) = independently_derived else {
        return Err(invariant(SourceImportInvariant::InvalidAliasLinks(
            binding.alias_symbol,
        )));
    };
    let direct_flags = store
        .symbol(direct_target)
        .ok_or_else(|| invariant(SourceImportInvariant::InvalidTargetSymbol(direct_target)))?
        .flags();
    let direct_is_alias = source_import_target_is_authenticated_alias(store, direct_target)?;

    if let Some(links) = store.alias_symbol_links(binding.alias_symbol) {
        match (phase, links.type_only_declaration) {
            (SourceImportPhase::Value, Some(_)) => {
                return Err(unsupported(SourceImportUnsupported::TypeOnlyAlias(
                    binding.alias_symbol,
                )));
            }
            (SourceImportPhase::Type, Some(marker)) if marker == binding.declaration => {}
            (SourceImportPhase::Type, _) => {
                return Err(unsupported(SourceImportUnsupported::ValueAlias(
                    binding.alias_symbol,
                )));
            }
            (SourceImportPhase::Value, None) => {}
        }
        if links
            .immediate_target
            .is_some_and(|cached| cached != direct_target)
            || (!direct_is_alias
                && match links.alias_target {
                    AliasTargetState::Unresolved => false,
                    AliasTargetState::Resolved(cached) => cached != direct_target,
                    AliasTargetState::Unknown => true,
                })
        {
            return Err(invariant(SourceImportInvariant::InvalidAliasLinks(
                binding.alias_symbol,
            )));
        }
    }

    let immediate = CanonicalAliasResolver::new(store, alias_host)
        .get_immediate_aliased_symbol(binding.alias_symbol)?;
    if immediate != Some(direct_target) {
        return Err(invariant(SourceImportInvariant::InvalidAliasLinks(
            binding.alias_symbol,
        )));
    }

    let resolution =
        CanonicalAliasResolver::new(store, alias_host).resolve_alias(binding.alias_symbol)?;
    let resolved_target = match resolution.target {
        AliasTargetState::Unknown if direct_is_alias => {
            return Err(SourceImportError::CircularAlias {
                alias: binding.alias_symbol,
                events: resolution.events,
            });
        }
        AliasTargetState::Unknown | AliasTargetState::Unresolved => {
            return Err(invariant(SourceImportInvariant::InvalidAliasLinks(
                binding.alias_symbol,
            )));
        }
        AliasTargetState::Resolved(target) if !resolution.events.is_empty() => {
            return Err(SourceImportError::CircularAlias {
                alias: binding.alias_symbol,
                events: resolution.events,
            });
        }
        AliasTargetState::Resolved(target) => target,
    };
    if direct_flags != SymbolFlags::ALIAS && direct_is_alias && resolved_target == direct_target {
        return Err(unsupported(SourceImportUnsupported::TargetSymbol {
            alias: binding.alias_symbol,
            target: direct_target,
            flags: direct_flags,
        }));
    }
    let (independent_immediate, independent_target) =
        independently_resolve_source_alias_chain(store, alias_host, binding.alias_symbol)?;
    if independent_immediate != direct_target || independent_target != resolved_target {
        return Err(invariant(SourceImportInvariant::InvalidAliasLinks(
            binding.alias_symbol,
        )));
    }

    if !direct_is_alias && resolved_target != direct_target {
        return Err(invariant(SourceImportInvariant::InvalidAliasLinks(
            binding.alias_symbol,
        )));
    }

    let alias_links = store
        .alias_symbol_links(binding.alias_symbol)
        .ok_or_else(|| {
            invariant(SourceImportInvariant::InvalidAliasLinks(
                binding.alias_symbol,
            ))
        })?;
    match (phase, alias_links.type_only_declaration) {
        (SourceImportPhase::Value, Some(_)) => {
            return Err(unsupported(SourceImportUnsupported::TypeOnlyAlias(
                binding.alias_symbol,
            )));
        }
        (SourceImportPhase::Type, Some(marker)) if marker == binding.declaration => {}
        (SourceImportPhase::Type, _) => {
            return Err(unsupported(SourceImportUnsupported::ValueAlias(
                binding.alias_symbol,
            )));
        }
        (SourceImportPhase::Value, None) => {}
    }
    if alias_links.immediate_target != Some(direct_target)
        || alias_links.alias_target != AliasTargetState::Resolved(resolved_target)
        || match phase {
            SourceImportPhase::Value => alias_links.type_only_declaration.is_some(),
            SourceImportPhase::Type => {
                alias_links.type_only_declaration != Some(binding.declaration)
            }
        }
    {
        return Err(invariant(SourceImportInvariant::InvalidAliasLinks(
            binding.alias_symbol,
        )));
    }

    Ok(ResolvedSourceImportBinding {
        binding: binding.clone(),
        immediate_target_symbol: direct_target,
        target_symbol: resolved_target,
    })
}

fn source_import_target_is_authenticated_alias(
    store: &CanonicalTypeMapperStore,
    symbol: SemanticSymbolId,
) -> Result<bool, SourceImportError> {
    let record = store
        .symbol(symbol)
        .ok_or_else(|| invariant(SourceImportInvariant::InvalidTargetSymbol(symbol)))?;
    let flags = record.flags();
    if flags == SymbolFlags::ALIAS {
        return Ok(true);
    }
    if !flags.intersects(SymbolFlags::ALIAS) {
        return Ok(false);
    }
    if !super::alias::is_promoted_commonjs_export_alias(store, symbol) {
        return Err(invariant(SourceImportInvariant::InvalidTargetSymbol(
            symbol,
        )));
    }
    Ok(true)
}

/// Re-derives one alias chain directly from the immutable production host and
/// compares every already-published hop with that chain. This prevents a warm
/// cached final target from bypassing module-resolution provenance while
/// preserving the pinned laziness of nested `immediate_target` links.
fn independently_resolve_source_alias_chain(
    store: &mut CanonicalTypeMapperStore,
    alias_host: &mut ProductionAliasTargetHost<'_, '_, '_>,
    alias: SemanticSymbolId,
) -> Result<(SemanticSymbolId, SemanticSymbolId), SourceImportError> {
    let mut current = alias;
    let mut visited = HashSet::new();
    let mut hops = Vec::new();
    let mut first_target = None;
    loop {
        if !visited.insert(current) {
            return Err(SourceImportError::CircularAlias {
                alias,
                events: Vec::new(),
            });
        }
        if !source_import_target_is_authenticated_alias(store, current)? {
            break;
        }
        let (target, syntactic_type_only) = alias_host
            .get_target_and_type_only_of_alias_declaration(store, current)
            .map_err(|reason| {
                SourceImportError::Alias(CanonicalAliasResolutionError::TargetUnavailable {
                    alias: current,
                    reason,
                })
            })?;
        let CanonicalImmediateAliasTarget::Resolved(next) = target else {
            return Err(invariant(SourceImportInvariant::InvalidAliasLinks(current)));
        };
        if store.symbol(next).is_none() {
            return Err(invariant(SourceImportInvariant::InvalidTargetSymbol(next)));
        }
        if first_target.is_none() {
            first_target = Some(next);
        }
        hops.push((current, next, syntactic_type_only));
        current = next;
    }

    let first_target =
        first_target.ok_or_else(|| invariant(SourceImportInvariant::InvalidAliasSymbol(alias)))?;
    let mut resolved = current;
    let mut root_target = None;
    let mut propagated_type_only = None;
    for (hop, immediate, syntactic_type_only) in hops.into_iter().rev() {
        let expected_type_only = syntactic_type_only.or(propagated_type_only);
        let links = store
            .alias_symbol_links(hop)
            .ok_or_else(|| invariant(SourceImportInvariant::InvalidAliasLinks(hop)))?;
        if links
            .immediate_target
            .is_some_and(|cached| cached != immediate)
            || links.alias_target != AliasTargetState::Resolved(resolved)
            || links.type_only_declaration != expected_type_only
        {
            return Err(invariant(SourceImportInvariant::InvalidAliasLinks(hop)));
        }
        root_target = Some(resolved);
        propagated_type_only = expected_type_only;
        resolved = store
            .get_merged_symbol(resolved)
            .ok_or_else(|| invariant(SourceImportInvariant::InvalidTargetSymbol(resolved)))?;
    }
    let root_target =
        root_target.ok_or_else(|| invariant(SourceImportInvariant::InvalidAliasSymbol(alias)))?;
    Ok((first_target, root_target))
}

/// Proves that one leaf of an exact importer annotation root references a
/// resolved type-only binding and returns the immutable capability consumed
/// by [`CanonicalTypeQuery`]. No node or type links are published here.
#[cfg_attr(not(test), allow(dead_code))]
pub(super) fn plan_source_type_import_reference(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    resolved: &ResolvedSourceTypeImportBinding,
    root: NodeRef,
    reference: NodeRef,
) -> Result<CanonicalTypeReferenceAliasTarget, SourceImportError> {
    let binding = &resolved.binding;
    if !root.is_for(binding.declaration.arena, binding.declaration.file)
        || !reference.is_for(root.arena, root.file)
    {
        return Err(unsupported(SourceImportUnsupported::TypeReference(
            reference,
        )));
    }
    validate_resolved_type_import(store, host, resolved)?;
    let (arena, bound) = host
        .source(reference)
        .ok_or_else(|| invariant(SourceImportInvariant::InvalidNode(reference)))?;
    let record = checked_node(arena, bound, store, reference)?;
    let NodeData::TypeReferenceNode(reference_data) = &record.data else {
        return Err(unsupported(SourceImportUnsupported::TypeReference(
            reference,
        )));
    };
    if record.kind != SyntaxKind::TypeReference || record.flags.0 != 0 {
        return Err(unsupported(SourceImportUnsupported::TypeReference(
            reference,
        )));
    }
    let name = NodeRef::new(reference.arena, reference.file, reference_data.type_name);
    let name_record = checked_node(arena, bound, store, name)?;
    if name_record.parent != Some(reference.node)
        || !matches!(
            &name_record.data,
            NodeData::Identifier(identifier)
                if name_record.kind == SyntaxKind::Identifier
                    && name_record.flags.0 == 0
                    && identifier.flow_node.is_none()
                    && identifier.text == binding.local_text
        )
    {
        return Err(unsupported(SourceImportUnsupported::TypeReference(
            reference,
        )));
    }
    if let Some(arguments) = &reference_data.type_arguments {
        if arguments.nodes.is_empty()
            || arguments.has_trailing_comma
            || arguments.range.start < name_record.range.end
            || arguments.range.end != record.range.end
            || arguments.range.start >= arguments.range.end
        {
            return Err(unsupported(SourceImportUnsupported::TypeReference(
                reference,
            )));
        }
        let mut previous_end = name_record.range.end;
        let mut seen = HashSet::with_capacity(arguments.nodes.len());
        for argument in &arguments.nodes {
            let argument = NodeRef::new(reference.arena, reference.file, *argument);
            let argument_record = checked_node(arena, bound, store, argument)?;
            if argument_record.parent != Some(reference.node)
                || argument_record.range.start < previous_end
                || argument_record.range.start <= arguments.range.start
                || argument_record.range.end >= arguments.range.end
                || argument_record.range.start < record.range.start
                || argument_record.range.end > record.range.end
                || !seen.insert(argument)
            {
                return Err(unsupported(SourceImportUnsupported::TypeReference(
                    reference,
                )));
            }
            previous_end = argument_record.range.end;
        }
    }

    let mut callback_host = host.name_resolver_host(store)?;
    let result = CanonicalNameResolver::new(arena, bound, store.symbol_store(), &mut callback_host)
        .map_err(DeclaredTypeError::from)?
        .resolve(
            Some(CanonicalResolutionLocation::Bound(name)),
            &binding.local_text,
            SymbolFlags::TYPE,
            None,
            true,
            false,
        );
    if !matches!(
        result,
        Ok(Some(alias))
            | Err(CanonicalNameResolutionError::AliasResolutionUnavailable(alias))
            if alias == binding.alias_symbol
    ) {
        return Err(unsupported(SourceImportUnsupported::TypeReference(
            reference,
        )));
    }
    if store.symbol_node_links(reference).is_some_and(|links| {
        links
            .resolved_symbol
            .is_some_and(|cached| cached != resolved.target_symbol)
    }) {
        return Err(invariant(SourceImportInvariant::InvalidIdentifierCache(
            reference,
        )));
    }
    if let Some(links) = store.type_node_links(reference) {
        let target_type = match store
            .symbol(resolved.target_symbol)
            .ok_or_else(|| {
                invariant(SourceImportInvariant::InvalidTargetSymbol(
                    resolved.target_symbol,
                ))
            })?
            .flags()
        {
            SymbolFlags::TYPE_ALIAS => store
                .type_alias_links(resolved.target_symbol)
                .and_then(|links| links.declared_type),
            SymbolFlags::INTERFACE => store
                .declared_type_links(resolved.target_symbol)
                .and_then(|links| links.declared_type),
            _ => {
                return Err(invariant(SourceImportInvariant::InvalidTargetSymbol(
                    resolved.target_symbol,
                )));
            }
        };
        if links.outer_type_parameters.is_some()
            || links.resolved_type.is_some_and(|cached| {
                store.type_payload(cached).is_none()
                    || reference_data.type_arguments.is_none() && target_type != Some(cached)
            })
        {
            return Err(invariant(SourceImportInvariant::InvalidTypeReferenceCache(
                reference,
            )));
        }
    }

    Ok(CanonicalTypeReferenceAliasTarget::new(
        root,
        reference,
        binding.declaration,
        binding.alias_symbol,
        resolved.immediate_target_symbol,
        resolved.target_symbol,
    ))
}

/// Classifies an expression read of a proven type-only binding without
/// fabricating a value type. Source integration may translate this boundary
/// into TS1361 while retaining the exact read node.
#[cfg_attr(not(test), allow(dead_code))]
pub(super) fn reject_source_type_import_value_use(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    resolved: &ResolvedSourceTypeImportBinding,
    node: NodeRef,
    name: &str,
    resolved_alias: SemanticSymbolId,
) -> Result<(), SourceImportError> {
    let binding = &resolved.binding;
    let record = checked_node(arena, bound, store, node)?;
    if record.kind != SyntaxKind::Identifier
        || record.flags.0 != 0
        || !matches!(
            &record.data,
            NodeData::Identifier(identifier)
                if identifier.flow_node.is_none() && identifier.text == name
        )
        || name != binding.local_text
        || resolved_alias != binding.alias_symbol
    {
        return Err(invariant(SourceImportInvariant::ReadBindingMismatch(node)));
    }
    validate_alias_symbol(
        store,
        binding.alias_symbol,
        binding.declaration,
        binding.local_name,
        &binding.local_text,
    )?;
    let links = store
        .alias_symbol_links(binding.alias_symbol)
        .ok_or_else(|| {
            invariant(SourceImportInvariant::InvalidAliasLinks(
                binding.alias_symbol,
            ))
        })?;
    if links.immediate_target != Some(resolved.immediate_target_symbol)
        || links.alias_target != AliasTargetState::Resolved(resolved.target_symbol)
        || links.type_only_declaration != Some(binding.declaration)
    {
        return Err(invariant(SourceImportInvariant::InvalidAliasLinks(
            binding.alias_symbol,
        )));
    }
    Err(unsupported(
        SourceImportUnsupported::ValueUseOfTypeOnlyImport(node),
    ))
}

/// Lazily types one resolved binding for one proven value read. Cold
/// export-equals objects publish their authenticated target values first;
/// import-alias writes remain deferred. The caller owns the
/// instantiation-session query boundary.
#[allow(clippy::too_many_arguments)]
pub(super) fn prepare_source_import_value(
    store: &mut CanonicalTypeMapperStore,
    declared_host: &DeclaredTypeHost<'_>,
    global_types: &CanonicalGlobalTypes,
    options: CanonicalCheckerOptions,
    session: &mut InstantiationSession,
    diagnostics: &mut CanonicalCheckerDiagnostics,
    resolved: &ResolvedSourceImportBinding,
    read: &PlannedSourceImportRead,
) -> Result<PreparedSourceImportValue, SourceImportError> {
    validate_planned_import_read(store, declared_host, resolved, read)?;
    let binding = &resolved.binding;
    let target = resolved.target_symbol;
    let alias_links = store
        .alias_symbol_links(binding.alias_symbol)
        .ok_or_else(|| {
            invariant(SourceImportInvariant::InvalidAliasLinks(
                binding.alias_symbol,
            ))
        })?;
    if alias_links.immediate_target != Some(resolved.immediate_target_symbol)
        || alias_links.alias_target != AliasTargetState::Resolved(target)
        || alias_links.type_only_declaration.is_some()
    {
        return Err(invariant(SourceImportInvariant::InvalidAliasLinks(
            binding.alias_symbol,
        )));
    }
    preflight_alias_value_links(store, binding.alias_symbol)?;
    preflight_import_target_value_links(store, target)?;
    let cached_alias_type = store
        .value_symbol_links(binding.alias_symbol)
        .and_then(|links| links.resolved_type);
    let cached_target_type = store
        .value_symbol_links(target)
        .and_then(|links| links.resolved_type);
    if let Some(cached) = cached_alias_type
        && cached_target_type != Some(cached)
    {
        return Err(invariant(SourceImportInvariant::InvalidAliasValueLinks(
            binding.alias_symbol,
        )));
    }

    if cached_target_type.is_none()
        && store.symbol(target).is_some_and(|symbol| {
            symbol.flags() == SymbolFlags::PROPERTY
                || symbol.flags() == SymbolFlags::PROPERTY | SymbolFlags::NAMESPACE_MODULE
        })
    {
        materialize_cold_export_equals_object_target(
            store,
            declared_host,
            binding.alias_symbol,
            target,
        )?;
    }

    let planned_target = plan_direct_import_value_target(
        store,
        declared_host,
        global_types,
        options,
        binding.alias_symbol,
        target,
        None,
    )?;
    let target_declaration = match &planned_target {
        PlannedSourceImportValueTarget::AnnotatedConst { declaration, .. }
        | PlannedSourceImportValueTarget::DeclarationNumericConst { declaration, .. }
        | PlannedSourceImportValueTarget::ConstEnum { declaration }
        | PlannedSourceImportValueTarget::ExportedObject { declaration, .. }
        | PlannedSourceImportValueTarget::PublishedObjectConst { declaration, .. }
        | PlannedSourceImportValueTarget::JavaScriptAnnotatedConst { declaration, .. }
        | PlannedSourceImportValueTarget::CommonJsNamedExport { declaration, .. }
        | PlannedSourceImportValueTarget::ModuleNamespace { declaration, .. } => *declaration,
        PlannedSourceImportValueTarget::AnnotatedFunction(callable) => callable.declaration,
    };
    if target_declaration.file == binding.declaration.file {
        return Err(unsupported(SourceImportUnsupported::SameSourceTarget {
            binding: binding.declaration,
            target: target_declaration,
        }));
    }
    let (type_, prepared_target) = match planned_target {
        PlannedSourceImportValueTarget::AnnotatedConst { type_node, .. } => {
            let type_ = CanonicalTypeQuery::new_with_global_types_and_session(
                store,
                declared_host,
                global_types,
                options,
                session,
                diagnostics,
            )?
            .get_type_from_type_node(type_node)?;
            let type_links = store.type_node_links(type_node).cloned();
            (
                type_,
                PreparedSourceImportTarget::AnnotatedConst {
                    type_node,
                    type_links,
                },
            )
        }
        PlannedSourceImportValueTarget::DeclarationNumericConst {
            initializer,
            literal,
            ..
        } => {
            let type_ = declaration_numeric_literal_type(store, target, &literal)?;
            (
                type_,
                PreparedSourceImportTarget::DeclarationNumericConst {
                    initializer,
                    literal,
                },
            )
        }
        PlannedSourceImportValueTarget::AnnotatedFunction(callable) => {
            let type_ = CanonicalTypeQuery::new_with_global_types_and_session(
                store,
                declared_host,
                global_types,
                options,
                session,
                diagnostics,
            )?
            .get_type_of_source_callable(callable.declaration, callable.owner_symbol)?;
            let provenance = store
                .source_callable_provenance(type_)
                .filter(|provenance| {
                    provenance.family == SourceCallableFamily::FunctionDeclaration
                        && provenance.declaration == callable.declaration
                        && provenance.owner_symbol == callable.owner_symbol
                })
                .ok_or_else(|| {
                    invariant(SourceImportInvariant::InvalidTargetLinks(
                        callable.owner_symbol,
                    ))
                })?;
            CanonicalTypeQuery::new_with_global_types_and_session(
                store,
                declared_host,
                global_types,
                options,
                session,
                diagnostics,
            )?
            .get_return_type_of_signature(provenance.signature)?;
            if !matches!(
                validate_stored_source_callable(store, type_),
                StoredSourceCallableValidation::Valid(_)
            ) {
                return Err(invariant(SourceImportInvariant::InvalidTargetLinks(
                    callable.owner_symbol,
                )));
            }
            (
                type_,
                PreparedSourceImportTarget::AnnotatedFunction {
                    signature: provenance.signature,
                },
            )
        }
        PlannedSourceImportValueTarget::ConstEnum { .. } => {
            let enumeration = enums::get_enum_semantics(store, declared_host, target)
                .map_err(DeclaredTypeError::from)?;
            (
                enumeration.value_type,
                PreparedSourceImportTarget::ConstEnum {
                    declared_type: enumeration.declared_type,
                },
            )
        }
        PlannedSourceImportValueTarget::ExportedObject {
            expression, type_, ..
        } => (
            type_,
            PreparedSourceImportTarget::ExportedObject { expression },
        ),
        PlannedSourceImportValueTarget::PublishedObjectConst {
            expression,
            expression_type,
            type_,
            ..
        } => (
            type_,
            PreparedSourceImportTarget::PublishedObjectConst {
                expression,
                expression_type,
            },
        ),
        PlannedSourceImportValueTarget::JavaScriptAnnotatedConst {
            declaration,
            annotation,
            cached_type,
        } => {
            let type_ = if let Some(annotation) = &annotation {
                resolve_planned_jsdoc_type(store, global_types, options, annotation).map_err(
                    |_| unsupported(SourceImportUnsupported::TargetDeclaration(declaration)),
                )?
            } else {
                cached_type.ok_or_else(|| {
                    unsupported(SourceImportUnsupported::MissingTargetAnnotation(
                        declaration,
                    ))
                })?
            };
            (
                type_,
                PreparedSourceImportTarget::JavaScriptAnnotatedConst { annotation },
            )
        }
        PlannedSourceImportValueTarget::CommonJsNamedExport {
            assignments,
            cached_type,
            ..
        } => (
            cached_type,
            PreparedSourceImportTarget::CommonJsNamedExport { assignments },
        ),
        PlannedSourceImportValueTarget::ModuleNamespace {
            declaration,
            members,
        } => {
            let (type_, properties) = materialize_imported_module_namespace(
                store,
                declared_host,
                global_types,
                options,
                session,
                diagnostics,
                declaration,
                target,
                members,
                None,
            )?;
            (
                type_,
                PreparedSourceImportTarget::ModuleNamespace { properties },
            )
        }
    };
    let target_links = prepare_value_links(store, target, type_, false)?;
    let alias_value_links = prepare_value_links(store, binding.alias_symbol, type_, true)?;

    Ok(PreparedSourceImportValue {
        binding: binding.clone(),
        immediate_target_symbol: resolved.immediate_target_symbol,
        target_symbol: target,
        target_declaration,
        type_,
        target: prepared_target,
        target_links,
        alias_links: alias_value_links,
    })
}

/// Read-only final preflight for payloads that the source checker can append
/// to its combined atomic publication batch.
pub(super) fn preflight_prepared_source_import_publications(
    store: &CanonicalTypeMapperStore,
    prepared: &[PreparedSourceImportValue],
) -> Result<Vec<PreparedSourceImportPublication>, SourceImportError> {
    let mut publications = Vec::<PreparedSourceImportPublication>::new();
    let mut publication_indices = HashMap::<SemanticSymbolId, usize>::new();
    for value in prepared {
        validate_prepared_import_value(store, value)?;
        if let PreparedSourceImportTarget::ModuleNamespace { properties } = &value.target {
            collect_nested_namespace_publications(
                properties,
                &mut publications,
                &mut publication_indices,
            )?;
        }
        for (symbol, links) in [
            (value.target_symbol, &value.target_links),
            (value.binding.alias_symbol, &value.alias_links),
        ] {
            push_prepared_import_publication(
                symbol,
                links,
                &mut publications,
                &mut publication_indices,
            )?;
        }
    }

    for publication in &publications {
        let type_ = publication.links.resolved_type.ok_or(invariant(
            SourceImportInvariant::PreparedStateChanged(publication.symbol),
        ))?;
        let current = prepare_value_links(
            store,
            publication.symbol,
            type_,
            store
                .symbol(publication.symbol)
                .is_some_and(|record| record.flags() == SymbolFlags::ALIAS),
        )?;
        if current != publication.links {
            return Err(invariant(SourceImportInvariant::PreparedStateChanged(
                publication.symbol,
            )));
        }
    }

    Ok(publications)
}

fn collect_nested_namespace_publications(
    properties: &[PreparedSourceImportModuleProperty],
    publications: &mut Vec<PreparedSourceImportPublication>,
    publication_indices: &mut HashMap<SemanticSymbolId, usize>,
) -> Result<(), SourceImportError> {
    for property in properties {
        let Some(namespace) = &property.namespace else {
            continue;
        };
        collect_nested_namespace_publications(
            &namespace.properties,
            publications,
            publication_indices,
        )?;
        push_prepared_import_publication(
            property.value_symbol,
            &namespace.links,
            publications,
            publication_indices,
        )?;
    }
    Ok(())
}

fn push_prepared_import_publication(
    symbol: SemanticSymbolId,
    links: &ValueSymbolLinks,
    publications: &mut Vec<PreparedSourceImportPublication>,
    publication_indices: &mut HashMap<SemanticSymbolId, usize>,
) -> Result<(), SourceImportError> {
    if let Some(&index) = publication_indices.get(&symbol) {
        if publications[index].links != *links {
            return Err(invariant(SourceImportInvariant::DuplicatePreparedSymbol(
                symbol,
            )));
        }
        return Ok(());
    }
    publication_indices.insert(symbol, publications.len());
    publications.push(PreparedSourceImportPublication {
        symbol,
        links: links.clone(),
    });
    Ok(())
}

fn validate_source_identity(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    source: NodeRef,
) -> Result<(), SourceImportError> {
    if source != bound.source_file()
        || !source.is_for(arena.id(), bound.file_id())
        || bound.node_arena_revision() != arena.revision()
        || !bound.declarations_complete()
        || !bound.contains(source)
        || !store.contains_node_ref(source)
    {
        return Err(invariant(SourceImportInvariant::InvalidSource(source)));
    }
    Ok(())
}

fn checked_node<'arena>(
    arena: &'arena NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    node: NodeRef,
) -> Result<&'arena Node, SourceImportError> {
    if !node.is_for(arena.id(), bound.file_id())
        || !bound.contains(node)
        || !store.contains_node_ref(node)
    {
        return Err(invariant(SourceImportInvariant::InvalidNode(node)));
    }
    arena
        .get(node.node)
        .filter(|record| record.data.matches_syntax_kind(record.kind))
        .ok_or_else(|| invariant(SourceImportInvariant::InvalidNode(node)))
}

fn range_contains(parent: &Node, child: &Node) -> bool {
    parent.range.start.get() <= child.range.start.get()
        && child.range.start.get() <= child.range.end.get()
        && child.range.end.get() <= parent.range.end.get()
}

fn exact_identifier(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    name: NodeRef,
    parent: NodeRef,
    unsupported_reason: SourceImportUnsupported,
) -> Result<String, SourceImportError> {
    let record = checked_node(arena, bound, store, name)?;
    let NodeData::Identifier(identifier) = &record.data else {
        return Err(unsupported(unsupported_reason));
    };
    if record.kind != SyntaxKind::Identifier
        || record.parent != Some(parent.node)
        || record.flags.0 != 0
        || identifier.flow_node.is_some()
        || identifier.text.is_empty()
    {
        return Err(unsupported(unsupported_reason));
    }
    Ok(identifier.text.clone())
}

fn import_alias_is_exported_type_local(
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    alias: SemanticSymbolId,
    declaration: NodeRef,
    name: &str,
) -> bool {
    let Some(record) = store.symbol(alias) else {
        return false;
    };
    let Some([_, type_declaration]) = record.declarations() else {
        return false;
    };
    let Some(export) = record.export_symbol() else {
        return false;
    };

    import_alias_has_exported_type_local(store, alias, declaration, name)
        && bound.symbol(declaration) == Some(alias)
        && bound.local_symbol(*type_declaration) == Some(alias)
        && bound.symbol(*type_declaration) == Some(export)
        && store
            .symbol(export)
            .and_then(ts_binder::semantic::Symbol::parent)
            == bound.symbol(bound.source_file())
}

fn import_alias_has_exported_type_local(
    store: &CanonicalTypeMapperStore,
    alias: SemanticSymbolId,
    declaration: NodeRef,
    name: &str,
) -> bool {
    let Some(record) = store.symbol(alias) else {
        return false;
    };
    let Some([import, type_declaration]) = record.declarations() else {
        return false;
    };
    let Some(export) = record.export_symbol() else {
        return false;
    };
    let Some(export_record) = store.symbol(export) else {
        return false;
    };
    let Some(module) = export_record.parent() else {
        return false;
    };
    let Some(module_record) = store.symbol(module) else {
        return false;
    };
    let Some(SourceNodeParent::Parent(mut import_declaration)) =
        store.source_node_parent(declaration)
    else {
        return false;
    };
    match store.source_node_kind(declaration) {
        Some(SyntaxKind::ImportClause) => {}
        Some(SyntaxKind::NamespaceImport) => {
            if store.source_node_kind(import_declaration) != Some(SyntaxKind::ImportClause) {
                return false;
            }
            let Some(SourceNodeParent::Parent(parent)) =
                store.source_node_parent(import_declaration)
            else {
                return false;
            };
            import_declaration = parent;
        }
        Some(SyntaxKind::ImportSpecifier) => {
            if store.source_node_kind(import_declaration) != Some(SyntaxKind::NamedImports) {
                return false;
            }
            let Some(SourceNodeParent::Parent(clause)) =
                store.source_node_parent(import_declaration)
            else {
                return false;
            };
            if store.source_node_kind(clause) != Some(SyntaxKind::ImportClause) {
                return false;
            }
            let Some(SourceNodeParent::Parent(parent)) = store.source_node_parent(clause) else {
                return false;
            };
            import_declaration = parent;
        }
        _ => return false,
    }
    let Some(SourceNodeParent::Parent(source)) = store.source_node_parent(import_declaration)
    else {
        return false;
    };

    *import == declaration
        && declaration.is_for(source.arena, source.file)
        && type_declaration.is_for(source.arena, source.file)
        && store.source_node_kind(import_declaration) == Some(SyntaxKind::ImportDeclaration)
        && store.source_node_kind(source) == Some(SyntaxKind::SourceFile)
        && store.source_node_kind(*type_declaration) == Some(SyntaxKind::TypeAliasDeclaration)
        && store.source_node_parent(*type_declaration) == Some(SourceNodeParent::Parent(source))
        && store.source_node_is_exported(*type_declaration) == Some(true)
        && record.flags() == SymbolFlags::ALIAS
        && record.check_flags() == CheckFlags::NONE
        && record.name().as_bytes() == name.as_bytes()
        && record.value_declaration().is_none()
        && record.members().is_none()
        && record.exports().is_none()
        && record.parent().is_none()
        && store.get_merged_symbol(alias) == Some(alias)
        && export_record.flags() == SymbolFlags::TYPE_ALIAS
        && export_record.check_flags() == CheckFlags::NONE
        && export_record.name().as_bytes() == name.as_bytes()
        && export_record.declarations() == Some(&[*type_declaration])
        && export_record.value_declaration().is_none()
        && export_record.members().is_none()
        && export_record.exports().is_none()
        && export_record.parent() == Some(module)
        && export_record.export_symbol().is_none()
        && store.get_merged_symbol(export) == Some(export)
        && module_record.flags().intersects(SymbolFlags::MODULE)
        && module_record
            .declarations()
            .is_some_and(|declarations| declarations.contains(&source))
        && module_record
            .exports()
            .and_then(|exports| store.symbol_table(exports))
            .and_then(|exports| exports.get_source(name))
            == Some(export)
}

fn validate_alias_symbol(
    store: &CanonicalTypeMapperStore,
    alias: SemanticSymbolId,
    declaration: NodeRef,
    name: NodeRef,
    name_text: &str,
) -> Result<(), SourceImportError> {
    let record = store
        .symbol(alias)
        .ok_or_else(|| invariant(SourceImportInvariant::InvalidAliasSymbol(alias)))?;
    let merged = store.get_merged_symbol(alias);
    let exported_type_local =
        import_alias_has_exported_type_local(store, alias, declaration, name_text);
    if merged.is_some_and(|target| target != alias)
        || (record.flags().intersects(SymbolFlags::ALIAS)
            && record.flags() != SymbolFlags::ALIAS
            && record
                .declarations()
                .is_some_and(|declarations| declarations.contains(&declaration)))
    {
        return Err(unsupported(SourceImportUnsupported::MergedAlias(
            declaration,
        )));
    }
    let valid_parent = record.parent().is_none_or(|parent| {
        let Some(SourceNodeParent::Parent(source)) = store.source_node_parent(declaration) else {
            return false;
        };
        store.source_node_kind(declaration) == Some(SyntaxKind::ImportEqualsDeclaration)
            && store.source_node_kind(source) == Some(SyntaxKind::SourceFile)
            && store.get_merged_symbol(parent) == Some(parent)
            && store.get_parent_of_symbol(alias) == Some(parent)
            && store.symbol(parent).is_some_and(|module| {
                module.flags().intersects(SymbolFlags::MODULE)
                    && module
                        .declarations()
                        .is_some_and(|declarations| declarations.contains(&source))
                    && module
                        .exports()
                        .and_then(|exports| store.symbol_table(exports))
                        .and_then(|exports| exports.get_source(name_text))
                        == Some(alias)
            })
    });
    if record.flags() != SymbolFlags::ALIAS
        || record.check_flags() != CheckFlags::NONE
        || record.value_declaration().is_some()
        || record.members().is_some()
        || record.exports().is_some()
        || !valid_parent
        || record.export_symbol().is_some() != exported_type_local
        || merged != Some(alias)
    {
        return Err(invariant(SourceImportInvariant::InvalidAliasSymbol(alias)));
    }
    if !exported_type_local && record.declarations() != Some(&[declaration]) {
        return Err(invariant(SourceImportInvariant::AliasDeclarationMismatch {
            alias,
            declaration,
        }));
    }
    if record.name().as_bytes() != name_text.as_bytes() {
        return Err(invariant(SourceImportInvariant::AliasNameMismatch {
            alias,
            name,
        }));
    }
    if let Some(links) = store.alias_symbol_links(alias)
        && (links
            .immediate_target
            .is_some_and(|target| store.symbol(target).is_none())
            || links
                .alias_target
                .symbol()
                .is_some_and(|target| store.symbol(target).is_none())
            || links
                .type_only_declaration
                .is_some_and(|node| !store.contains_node_ref(node)))
    {
        return Err(invariant(SourceImportInvariant::InvalidAliasLinks(alias)));
    }
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn validate_reexport_alias_symbol(
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    source: NodeRef,
    alias: SemanticSymbolId,
    declaration: NodeRef,
    name: NodeRef,
    name_text: &str,
) -> Result<(), SourceImportError> {
    let module = bound
        .symbol(source)
        .ok_or_else(|| invariant(SourceImportInvariant::MissingAliasSymbol(source)))?;
    let module_record = store
        .symbol(module)
        .ok_or_else(|| invariant(SourceImportInvariant::InvalidAliasSymbol(module)))?;
    let exports = module_record
        .exports()
        .and_then(|exports| store.symbol_table(exports))
        .ok_or_else(|| invariant(SourceImportInvariant::InvalidAliasSymbol(module)))?;
    let record = store
        .symbol(alias)
        .ok_or_else(|| invariant(SourceImportInvariant::InvalidAliasSymbol(alias)))?;
    let merged = store.get_merged_symbol(alias);
    if merged.is_some_and(|target| target != alias)
        || (record.flags().intersects(SymbolFlags::ALIAS)
            && record.flags() != SymbolFlags::ALIAS
            && record
                .declarations()
                .is_some_and(|declarations| declarations.contains(&declaration)))
    {
        return Err(unsupported(SourceImportUnsupported::MergedAlias(
            declaration,
        )));
    }
    if bound.symbol(declaration) != Some(alias)
        || exports.get_source(name_text) != Some(alias)
        || record.flags() != SymbolFlags::ALIAS
        || record.check_flags() != CheckFlags::NONE
        || record.value_declaration().is_some()
        || record.members().is_some()
        || record.exports().is_some()
        || record.parent() != Some(module)
        || record.export_symbol().is_some()
        || merged != Some(alias)
    {
        return Err(invariant(SourceImportInvariant::InvalidAliasSymbol(alias)));
    }
    if record.declarations() != Some(&[declaration]) {
        return Err(invariant(SourceImportInvariant::AliasDeclarationMismatch {
            alias,
            declaration,
        }));
    }
    if record.name().as_bytes() != name_text.as_bytes() {
        return Err(invariant(SourceImportInvariant::AliasNameMismatch {
            alias,
            name,
        }));
    }
    if let Some(links) = store.alias_symbol_links(alias)
        && (links
            .immediate_target
            .is_some_and(|target| store.symbol(target).is_none())
            || links
                .alias_target
                .symbol()
                .is_some_and(|target| store.symbol(target).is_none())
            || links
                .type_only_declaration
                .is_some_and(|node| !store.contains_node_ref(node)))
    {
        return Err(invariant(SourceImportInvariant::InvalidAliasLinks(alias)));
    }
    Ok(())
}

fn preflight_alias_value_links(
    store: &CanonicalTypeMapperStore,
    alias: SemanticSymbolId,
) -> Result<(), SourceImportError> {
    let Some(links) = store.value_symbol_links(alias) else {
        return Ok(());
    };
    if links.write_type.is_some()
        || links.target.is_some()
        || links.mapper.is_some()
        || links.name_type.is_some()
        || links.containing_type.is_some()
        || links.function_or_constructor_checked
        || links
            .resolved_type
            .is_some_and(|type_| store.type_payload(type_).is_none())
    {
        return Err(invariant(SourceImportInvariant::InvalidAliasValueLinks(
            alias,
        )));
    }
    Ok(())
}

fn preflight_import_target_value_links(
    store: &CanonicalTypeMapperStore,
    target: SemanticSymbolId,
) -> Result<(), SourceImportError> {
    let Some(links) = store.value_symbol_links(target) else {
        return Ok(());
    };
    if links.write_type.is_some()
        || links.target.is_some()
        || links.mapper.is_some()
        || links.name_type.is_some()
        || links.containing_type.is_some()
        || links.function_or_constructor_checked
        || links
            .resolved_type
            .is_some_and(|type_| store.type_payload(type_).is_none())
    {
        return Err(invariant(SourceImportInvariant::InvalidTargetLinks(target)));
    }
    Ok(())
}

fn preflight_type_import_value_links(
    store: &CanonicalTypeMapperStore,
    alias: SemanticSymbolId,
) -> Result<(), SourceImportError> {
    preflight_alias_value_links(store, alias)?;
    if store
        .value_symbol_links(alias)
        .is_some_and(|links| links.resolved_type.is_some())
    {
        return Err(invariant(SourceImportInvariant::InvalidAliasValueLinks(
            alias,
        )));
    }
    Ok(())
}

#[cfg_attr(not(test), allow(dead_code))]
fn validate_resolved_type_import(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    resolved: &ResolvedSourceTypeImportBinding,
) -> Result<(), SourceImportError> {
    let binding = &resolved.binding;
    validate_alias_symbol(
        store,
        binding.alias_symbol,
        binding.declaration,
        binding.local_name,
        &binding.local_text,
    )?;
    let links = store
        .alias_symbol_links(binding.alias_symbol)
        .ok_or_else(|| {
            invariant(SourceImportInvariant::InvalidAliasLinks(
                binding.alias_symbol,
            ))
        })?;
    if links.immediate_target != Some(resolved.immediate_target_symbol)
        || links.alias_target != AliasTargetState::Resolved(resolved.target_symbol)
        || links.type_only_declaration != Some(binding.declaration)
        || plan_direct_exported_type_target(
            store,
            host,
            binding.alias_symbol,
            resolved.target_symbol,
        )? != resolved.target_declaration
    {
        return Err(invariant(SourceImportInvariant::InvalidAliasLinks(
            binding.alias_symbol,
        )));
    }
    Ok(())
}

fn validate_planned_import_read(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    resolved: &ResolvedSourceImportBinding,
    read: &PlannedSourceImportRead,
) -> Result<(), SourceImportError> {
    let binding = &resolved.binding;
    if read.resolved_symbol != binding.alias_symbol
        || read.value_symbol != binding.alias_symbol
        || !store.contains_node_ref(read.node)
    {
        return Err(invariant(SourceImportInvariant::ReadBindingMismatch(
            read.node,
        )));
    }
    let (arena, bound) = host
        .source(read.node)
        .ok_or_else(|| invariant(SourceImportInvariant::InvalidNode(read.node)))?;
    let record = checked_node(arena, bound, store, read.node)?;
    if record.kind != SyntaxKind::Identifier
        || record.flags.0 != 0
        || !matches!(
            &record.data,
            NodeData::Identifier(identifier)
                if identifier.flow_node.is_none() && identifier.text == binding.local_text
        )
    {
        return Err(invariant(SourceImportInvariant::ReadBindingMismatch(
            read.node,
        )));
    }
    if store.symbol_node_links(read.node).is_some_and(|links| {
        links
            .resolved_symbol
            .is_some_and(|cached| cached != binding.alias_symbol)
    }) {
        return Err(invariant(SourceImportInvariant::InvalidIdentifierCache(
            read.node,
        )));
    }
    Ok(())
}

#[cfg_attr(not(test), allow(dead_code))]
fn plan_direct_exported_type_target(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    alias: SemanticSymbolId,
    target: SemanticSymbolId,
) -> Result<NodeRef, SourceImportError> {
    let target_record = store
        .symbol(target)
        .ok_or_else(|| invariant(SourceImportInvariant::InvalidTargetSymbol(target)))?;
    if target_record.flags() != SymbolFlags::TYPE_ALIAS
        && target_record.flags() != SymbolFlags::INTERFACE
    {
        return Err(unsupported(SourceImportUnsupported::TargetSymbol {
            alias,
            target,
            flags: target_record.flags(),
        }));
    }
    let Some([declaration]) = target_record.declarations() else {
        return Err(unsupported(SourceImportUnsupported::TargetSymbol {
            alias,
            target,
            flags: target_record.flags(),
        }));
    };
    let declaration = *declaration;
    if target_record.value_declaration().is_some() {
        return Err(invariant(SourceImportInvariant::InvalidTargetSymbol(
            target,
        )));
    }
    let (arena, bound) = host
        .source(declaration)
        .ok_or_else(|| unsupported(SourceImportUnsupported::TargetTypeDeclaration(declaration)))?;
    let facts = bound.source_facts().ok_or_else(|| {
        invariant(SourceImportInvariant::MissingSourceFacts(
            bound.source_file(),
        ))
    })?;
    let commonjs_javascript = facts.is_javascript_file() && facts.is_common_js_module();
    if (facts.is_common_js_module() || facts.is_javascript_file()) && !commonjs_javascript
        || !facts.is_external_or_common_js_module()
        || !host.symbol_matches(store, declaration, target)
    {
        return Err(unsupported(SourceImportUnsupported::TargetTypeDeclaration(
            declaration,
        )));
    }
    let source_record = checked_node(arena, bound, store, bound.source_file())?;
    let NodeData::SourceFile(source) = &source_record.data else {
        return Err(invariant(SourceImportInvariant::InvalidSource(
            bound.source_file(),
        )));
    };
    if source
        .statements
        .nodes
        .iter()
        .filter(|node| **node == declaration.node)
        .count()
        != 1
    {
        return Err(unsupported(SourceImportUnsupported::TargetTypeDeclaration(
            declaration,
        )));
    }

    let record = checked_node(arena, bound, store, declaration)?;
    let expected_flags = if commonjs_javascript && record.kind == SyntaxKind::JsTypeAliasDeclaration
    {
        NodeFlags::REPARSED
    } else {
        NodeFlags(0)
    };
    if record.parent != Some(bound.source_file().node) || record.flags != expected_flags {
        return Err(unsupported(SourceImportUnsupported::TargetTypeDeclaration(
            declaration,
        )));
    }
    let (name_node, modifiers) = match &record.data {
        NodeData::TypeAliasDeclaration(type_alias)
            if (record.kind == SyntaxKind::TypeAliasDeclaration
                || commonjs_javascript && record.kind == SyntaxKind::JsTypeAliasDeclaration)
                && target_record.flags() == SymbolFlags::TYPE_ALIAS
                && type_alias.flow_node.is_none()
                && type_alias.local_symbol.is_none()
                && type_alias.symbol.is_none() =>
        {
            let type_node = NodeRef::new(declaration.arena, declaration.file, type_alias.type_);
            if checked_node(arena, bound, store, type_node)?.parent != Some(declaration.node) {
                return Err(unsupported(SourceImportUnsupported::TargetTypeShape(
                    declaration,
                )));
            }
            (type_alias.name, type_alias.modifiers.as_ref())
        }
        NodeData::InterfaceDeclaration(interface)
            if record.kind == SyntaxKind::InterfaceDeclaration
                && target_record.flags() == SymbolFlags::INTERFACE
                && interface.flow_node.is_none()
                && interface.local_symbol.is_none()
                && interface.symbol.is_none()
                && interface.heritage_clauses.is_none() =>
        {
            (interface.name, interface.modifiers.as_ref())
        }
        _ => {
            return Err(unsupported(SourceImportUnsupported::TargetTypeShape(
                declaration,
            )));
        }
    };
    let name = NodeRef::new(declaration.arena, declaration.file, name_node);
    let name_record = checked_node(arena, bound, store, name)?;
    if name_record.parent != Some(declaration.node)
        || !matches!(
            &name_record.data,
            NodeData::Identifier(identifier)
                if name_record.kind == SyntaxKind::Identifier
                    && name_record.flags.0 == 0
                    && identifier.flow_node.is_none()
                    && identifier.text.as_bytes() == target_record.name().as_bytes()
        )
    {
        return Err(invariant(SourceImportInvariant::TargetNameMismatch {
            target,
            name,
        }));
    }
    let explicitly_exported = if commonjs_javascript {
        let Some(module) = bound.symbol(bound.source_file()) else {
            return Err(unsupported(SourceImportUnsupported::TargetTypeNotExported(
                declaration,
            )));
        };
        store
            .symbol(module)
            .and_then(ts_binder::semantic::Symbol::exports)
            .and_then(|exports| store.symbol_table(exports))
            .and_then(|exports| exports.get(target_record.name()))
            == Some(target)
    } else {
        has_exact_export_modifier(arena, bound, store, declaration, modifiers)?
    };
    if !explicitly_exported {
        return Err(unsupported(SourceImportUnsupported::TargetTypeNotExported(
            declaration,
        )));
    }
    Ok(declaration)
}

fn plan_direct_import_value_target(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    global_types: &CanonicalGlobalTypes,
    options: CanonicalCheckerOptions,
    alias: SemanticSymbolId,
    target: SemanticSymbolId,
    namespace_module: Option<SemanticSymbolId>,
) -> Result<PlannedSourceImportValueTarget, SourceImportError> {
    let record = store
        .symbol(target)
        .ok_or_else(|| invariant(SourceImportInvariant::InvalidTargetSymbol(target)))?;
    let flags = record.flags();
    if flags == SymbolFlags::BLOCK_SCOPED_VARIABLE || flags == SymbolFlags::FUNCTION_SCOPED_VARIABLE
    {
        let target_source = record.value_declaration().and_then(|declaration| {
            host.source(declaration)
                .and_then(|(_, bound)| bound.source_facts().map(|facts| (declaration, facts)))
        });
        if let Some((declaration, facts)) = target_source
            && facts.is_javascript_file()
        {
            if flags == SymbolFlags::FUNCTION_SCOPED_VARIABLE {
                if !facts.is_common_js_module() {
                    return Err(unsupported(SourceImportUnsupported::TargetSymbol {
                        alias,
                        target,
                        flags,
                    }));
                }
                if store.source_node_kind(declaration) == Some(SyntaxKind::BinaryExpression) {
                    return plan_direct_commonjs_named_export_target(store, host, alias, target);
                }
            }
            return plan_direct_javascript_const_target(
                store,
                host,
                global_types,
                options,
                alias,
                target,
            );
        }
        if flags != SymbolFlags::BLOCK_SCOPED_VARIABLE {
            return Err(unsupported(SourceImportUnsupported::TargetSymbol {
                alias,
                target,
                flags,
            }));
        }
        return plan_direct_typescript_const_target(store, host, global_types, alias, target);
    }
    if flags == SymbolFlags::FUNCTION {
        return plan_direct_annotated_function_target(
            store,
            host,
            global_types,
            alias,
            target,
            namespace_module,
        )
        .map(Box::new)
        .map(PlannedSourceImportValueTarget::AnnotatedFunction);
    }
    if flags == SymbolFlags::CONST_ENUM {
        return plan_direct_const_enum_target(store, host, alias, target);
    }
    if flags == SymbolFlags::PROPERTY
        || flags == SymbolFlags::PROPERTY | SymbolFlags::NAMESPACE_MODULE
    {
        return plan_direct_exported_object_target(store, host, alias, target);
    }
    if flags.intersects(SymbolFlags::MODULE) && flags.intersects(SymbolFlags::VALUE) {
        return plan_direct_imported_module_namespace(
            store,
            host,
            global_types,
            options,
            alias,
            target,
        );
    }
    Err(unsupported(SourceImportUnsupported::TargetSymbol {
        alias,
        target,
        flags,
    }))
}

fn plan_direct_const_enum_target(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    alias: SemanticSymbolId,
    target: SemanticSymbolId,
) -> Result<PlannedSourceImportValueTarget, SourceImportError> {
    let record = store
        .symbol(target)
        .ok_or_else(|| invariant(SourceImportInvariant::InvalidTargetSymbol(target)))?;
    let Some([declaration]) = record.declarations() else {
        return Err(unsupported(SourceImportUnsupported::TargetSymbol {
            alias,
            target,
            flags: record.flags(),
        }));
    };
    let declaration = *declaration;
    let (arena, bound) = host
        .source(declaration)
        .ok_or_else(|| unsupported(SourceImportUnsupported::TargetDeclaration(declaration)))?;
    let facts = bound.source_facts().ok_or_else(|| {
        invariant(SourceImportInvariant::MissingSourceFacts(
            bound.source_file(),
        ))
    })?;
    let declaration_record = checked_node(arena, bound, store, declaration)?;
    let NodeData::EnumDeclaration(enumeration) = &declaration_record.data else {
        return Err(unsupported(SourceImportUnsupported::TargetDeclaration(
            declaration,
        )));
    };
    let Some(module) = bound.symbol(bound.source_file()) else {
        return Err(unsupported(SourceImportUnsupported::TargetDeclaration(
            declaration,
        )));
    };
    let name = NodeRef::new(declaration.arena, declaration.file, enumeration.name);
    let name_text = exact_identifier(
        arena,
        bound,
        store,
        name,
        declaration,
        SourceImportUnsupported::TargetDeclaration(name),
    )?;
    if record.flags() != SymbolFlags::CONST_ENUM
        || record.check_flags() != CheckFlags::NONE
        || record.value_declaration() != Some(declaration)
        || record.parent() != Some(module)
        || record.name().as_bytes() != name_text.as_bytes()
        || declaration_record.kind != SyntaxKind::EnumDeclaration
        || declaration_record.parent != Some(bound.source_file().node)
        || declaration_record.flags.0 != 0
        || !facts.is_external_module()
        || facts.is_javascript_file()
        || bound.symbol(declaration) != Some(target)
        || store.get_merged_symbol(target) != Some(target)
        || store
            .symbol(module)
            .and_then(ts_binder::semantic::Symbol::exports)
            .and_then(|exports| store.symbol_table(exports))
            .and_then(|exports| exports.get(record.name()))
            != Some(target)
    {
        return Err(unsupported(SourceImportUnsupported::TargetDeclaration(
            declaration,
        )));
    }
    enums::preflight_enum(store, host, target).map_err(DeclaredTypeError::from)?;
    Ok(PlannedSourceImportValueTarget::ConstEnum { declaration })
}

fn authenticate_direct_exported_object_target(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    alias: SemanticSymbolId,
    target: SemanticSymbolId,
) -> Result<AuthenticatedSourceImportExportedObject, SourceImportError> {
    let record = store
        .symbol(target)
        .ok_or_else(|| invariant(SourceImportInvariant::InvalidTargetSymbol(target)))?;
    let Some([declaration]) = record.declarations() else {
        return Err(unsupported(SourceImportUnsupported::TargetSymbol {
            alias,
            target,
            flags: record.flags(),
        }));
    };
    let declaration = *declaration;
    let (arena, bound) = host
        .source(declaration)
        .ok_or_else(|| unsupported(SourceImportUnsupported::TargetDeclaration(declaration)))?;
    let declaration_record = checked_node(arena, bound, store, declaration)?;
    let NodeData::ExportAssignment(assignment) = &declaration_record.data else {
        return Err(unsupported(SourceImportUnsupported::TargetDeclaration(
            declaration,
        )));
    };
    let Some(module) = bound.symbol(bound.source_file()) else {
        return Err(unsupported(SourceImportUnsupported::TargetDeclaration(
            declaration,
        )));
    };
    let expected_name = if assignment.is_export_equals {
        InternalSymbolName::ExportEquals.as_ref()
    } else {
        InternalSymbolName::Default.as_ref()
    };
    let promoted = record.flags() == SymbolFlags::PROPERTY | SymbolFlags::NAMESPACE_MODULE;
    let valid_promoted_exports = if promoted {
        assignment.is_export_equals
            && record
                .exports()
                .and_then(|exports| store.symbol_table(exports))
                .is_some_and(|exports| {
                    !exports.is_empty()
                        && exports.iter().all(|(name, symbol)| {
                            store.symbol(symbol).is_some_and(|export| {
                                export
                                    .flags()
                                    .intersects(SymbolFlags::TYPE | SymbolFlags::NAMESPACE)
                                    && store
                                        .symbol(module)
                                        .and_then(ts_binder::semantic::Symbol::exports)
                                        .and_then(|exports| store.symbol_table(exports))
                                        .and_then(|exports| exports.get(name))
                                        == Some(symbol)
                            })
                        })
                })
    } else {
        record.exports().is_none()
    };
    if record.check_flags() != CheckFlags::NONE
        || record.parent() != Some(module)
        || record.name() != expected_name
        || record.value_declaration() != Some(declaration)
        || record.members().is_some()
        || record.export_symbol().is_some()
        || !valid_promoted_exports
        || declaration_record.kind != SyntaxKind::ExportAssignment
        || declaration_record.flags.0 != 0
        || declaration_record.parent != Some(bound.source_file().node)
        || assignment.flow_node.is_some()
        || assignment.modifiers.is_some()
        || assignment.symbol.is_some()
        || assignment.type_.is_some()
        || assignment.facts != 0
        || bound.symbol(declaration) != Some(target)
        || store.get_merged_symbol(target) != Some(target)
        || bound
            .source_facts()
            .is_none_or(|facts| !facts.is_external_module() || facts.is_javascript_file())
        || store
            .symbol(module)
            .and_then(ts_binder::semantic::Symbol::exports)
            .and_then(|exports| store.symbol_table(exports))
            .and_then(|exports| exports.get(expected_name))
            != Some(target)
    {
        return Err(unsupported(SourceImportUnsupported::TargetDeclaration(
            declaration,
        )));
    }

    let expression = NodeRef::new(declaration.arena, declaration.file, assignment.expression);
    let expression_record = checked_node(arena, bound, store, expression)?;
    if expression_record.kind != SyntaxKind::ObjectLiteralExpression
        || !matches!(expression_record.data, NodeData::ObjectLiteralExpression(_))
        || expression_record.parent != Some(declaration.node)
        || expression_record.flags.0 != 0
    {
        return Err(unsupported(SourceImportUnsupported::TargetDeclaration(
            expression,
        )));
    }

    Ok(AuthenticatedSourceImportExportedObject {
        declaration,
        expression,
        export_equals: assignment.is_export_equals,
    })
}

fn plan_direct_exported_object_target(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    alias: SemanticSymbolId,
    target: SemanticSymbolId,
) -> Result<PlannedSourceImportValueTarget, SourceImportError> {
    let AuthenticatedSourceImportExportedObject {
        declaration,
        expression,
        ..
    } = authenticate_direct_exported_object_target(store, host, alias, target)?;
    let Some(type_) = store
        .value_symbol_links(target)
        .and_then(|links| links.resolved_type)
    else {
        return Err(unsupported(SourceImportUnsupported::TargetDeclaration(
            declaration,
        )));
    };
    if store
        .type_node_links(expression)
        .and_then(|links| links.resolved_type)
        != Some(type_)
        || store
            .type_payload(type_)
            .is_none_or(|record| record.data().structured().is_none())
    {
        return Err(invariant(SourceImportInvariant::InvalidTargetLinks(target)));
    }

    Ok(PlannedSourceImportValueTarget::ExportedObject {
        declaration,
        expression,
        type_,
    })
}

fn materialize_cold_export_equals_object_target(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    alias: SemanticSymbolId,
    target: SemanticSymbolId,
) -> Result<(), SourceImportError> {
    let authenticated = authenticate_direct_exported_object_target(store, host, alias, target)?;
    if !authenticated.export_equals {
        return Ok(());
    }
    if store.type_node_links(authenticated.expression).is_some() {
        return Err(invariant(SourceImportInvariant::InvalidTargetLinks(target)));
    }

    let (arena, bound) = host.source(authenticated.declaration).ok_or_else(|| {
        unsupported(SourceImportUnsupported::TargetDeclaration(
            authenticated.declaration,
        ))
    })?;
    let plan = super::object_members::plan_object_literal(store, host, authenticated.expression)
        .map_err(|error| match error {
            super::object_members::PropertyObjectError::UnsupportedMember { node, .. } => {
                unsupported(SourceImportUnsupported::TargetDeclaration(node))
            }
            _ => invariant(SourceImportInvariant::InvalidTargetLinks(target)),
        })?;
    if let Some(spread) = plan.spreads.first() {
        return Err(unsupported(SourceImportUnsupported::TargetDeclaration(
            spread.expression,
        )));
    }
    let (number, string) = store
        .intrinsic_bootstrap()
        .map(|bootstrap| (bootstrap.number_type, bootstrap.string_type))
        .ok_or_else(|| invariant(SourceImportInvariant::InvalidTargetLinks(target)))?;
    let mut property_types = Vec::with_capacity(plan.properties.len());
    for property in &plan.properties {
        let declaration = checked_node(arena, bound, store, property.declaration)?;
        let NodeData::PropertyAssignment(assignment) = &declaration.data else {
            return Err(unsupported(SourceImportUnsupported::TargetDeclaration(
                property.declaration,
            )));
        };
        if property.readonly
            || declaration.kind != SyntaxKind::PropertyAssignment
            || declaration.parent != Some(authenticated.expression.node)
            || declaration.flags.0 != 0
            || assignment.initializer != property.type_node.node
            || assignment.postfix_token.is_some()
            || assignment.symbol.is_some()
            || assignment.type_.is_some()
            || assignment.facts != 0
            || assignment.modifiers.is_some()
        {
            return Err(unsupported(SourceImportUnsupported::TargetDeclaration(
                property.declaration,
            )));
        }
        let initializer = checked_node(arena, bound, store, property.type_node)?;
        if initializer.parent != Some(property.declaration.node) || initializer.flags.0 != 0 {
            return Err(unsupported(SourceImportUnsupported::TargetDeclaration(
                property.type_node,
            )));
        }
        if store
            .type_node_links(property.type_node)
            .is_some_and(|links| links != &TypeNodeLinks::default())
        {
            return Err(invariant(SourceImportInvariant::InvalidTargetLinks(target)));
        }
        let type_ = match &initializer.data {
            NodeData::NumericLiteral(literal)
                if initializer.kind == SyntaxKind::NumericLiteral
                    && literal.token_flags.0 == 0
                    && !literal.text.is_empty()
                    && source_spelling_matches(arena, initializer, &literal.text)
                    && ts_jsnum::from_string(&literal.text).value().is_finite() =>
            {
                number
            }
            NodeData::StringLiteral(literal)
                if initializer.kind == SyntaxKind::StringLiteral && literal.token_flags.0 == 0 =>
            {
                string
            }
            _ => {
                return Err(unsupported(SourceImportUnsupported::TargetDeclaration(
                    property.type_node,
                )));
            }
        };
        property_types.push(type_);
    }

    if !store
        .try_reserve_value_symbol_links(usize::from(store.value_symbol_links(target).is_none()))
    {
        return Err(invariant(SourceImportInvariant::InvalidTargetLinks(target)));
    }
    let type_ = super::object_members::publish_object_literal(store, &plan, &property_types)
        .map_err(|_| invariant(SourceImportInvariant::InvalidTargetLinks(target)))?;
    if !store.set_value_symbol_links(
        target,
        ValueSymbolLinks {
            resolved_type: Some(type_),
            ..ValueSymbolLinks::default()
        },
    ) {
        return Err(invariant(SourceImportInvariant::InvalidTargetLinks(target)));
    }
    Ok(())
}

fn plan_direct_imported_module_namespace(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    global_types: &CanonicalGlobalTypes,
    options: CanonicalCheckerOptions,
    alias: SemanticSymbolId,
    module: SemanticSymbolId,
) -> Result<PlannedSourceImportValueTarget, SourceImportError> {
    let record = store
        .symbol(module)
        .ok_or_else(|| invariant(SourceImportInvariant::InvalidTargetSymbol(module)))?;
    if store.export_type_links(module).is_some() {
        return plan_synthetic_import_namespace(store, host, global_types, alias, module);
    }
    let Some([declaration]) = record.declarations() else {
        return Err(unsupported(SourceImportUnsupported::TargetSymbol {
            alias,
            target: module,
            flags: record.flags(),
        }));
    };
    let declaration = *declaration;
    let (arena, bound) = host
        .source(declaration)
        .ok_or_else(|| unsupported(SourceImportUnsupported::TargetDeclaration(declaration)))?;
    let declaration_record = checked_node(arena, bound, store, declaration)?;
    if bound.symbol(declaration) != Some(module) {
        return Err(invariant(SourceImportInvariant::InvalidTargetSymbol(
            module,
        )));
    }
    preflight_import_target_value_links(store, module)?;
    let valid_declaration = match declaration_record.kind {
        SyntaxKind::SourceFile => declaration == bound.source_file(),
        SyntaxKind::ModuleDeclaration => {
            valid_imported_namespace_declaration(arena, bound, store, declaration, module)?
        }
        _ => false,
    };
    if !valid_declaration {
        return Err(unsupported(SourceImportUnsupported::TargetDeclaration(
            declaration,
        )));
    }

    let exports = store
        .module_symbol_links(module)
        .and_then(|links| links.resolved_exports)
        .or_else(|| record.exports())
        .and_then(|exports| store.symbol_table(exports))
        .ok_or_else(|| unsupported(SourceImportUnsupported::TargetDeclaration(declaration)))?;
    let mut members = Vec::with_capacity(exports.len());
    for (name, symbol) in exports.iter() {
        let Some(name_text) = name.as_utf8() else {
            continue;
        };
        let record = store
            .symbol(symbol)
            .ok_or_else(|| invariant(SourceImportInvariant::InvalidTargetSymbol(symbol)))?;
        let value_symbol = if record.flags() == SymbolFlags::ALIAS {
            let links = store.alias_symbol_links(symbol).ok_or_else(|| {
                unsupported(SourceImportUnsupported::TargetDeclaration(declaration))
            })?;
            if links.type_only_declaration.is_some() {
                continue;
            }
            let AliasTargetState::Resolved(target) = links.alias_target else {
                return Err(unsupported(SourceImportUnsupported::TargetDeclaration(
                    declaration,
                )));
            };
            target
        } else {
            symbol
        };
        let value = store
            .symbol(value_symbol)
            .ok_or_else(|| invariant(SourceImportInvariant::InvalidTargetSymbol(value_symbol)))?;
        if !value.flags().intersects(SymbolFlags::VALUE) {
            continue;
        }
        let target = plan_direct_import_value_target(
            store,
            host,
            global_types,
            options,
            alias,
            value_symbol,
            Some(module),
        )
        .map_err(|error| match error {
            SourceImportError::Callable(SourceCallableError::Invariant(_))
                if declaration_record.kind == SyntaxKind::ModuleDeclaration
                    && value.parent() == Some(module) =>
            {
                unsupported(SourceImportUnsupported::TargetDeclaration(
                    value.value_declaration().unwrap_or(declaration),
                ))
            }
            other => other,
        })?;
        members.push(PlannedSourceImportModuleMember {
            name: EscapedName::source(name_text),
            symbol,
            value_symbol,
            target,
        });
    }
    members.sort_by_key(|member| {
        store
            .symbol(member.symbol)
            .and_then(|symbol| symbol.declarations())
            .and_then(|declarations| declarations.first())
            .and_then(|declaration| {
                host.source(*declaration)
                    .and_then(|(arena, _)| arena.get(declaration.node))
            })
            .map(|declaration| declaration.range.start)
    });
    Ok(PlannedSourceImportValueTarget::ModuleNamespace {
        declaration,
        members,
    })
}

fn authenticate_synthetic_import_namespace_identity(
    store: &CanonicalTypeMapperStore,
    alias: SemanticSymbolId,
    synthetic: SemanticSymbolId,
) -> Result<AuthenticatedSyntheticImportNamespace, SourceImportError> {
    let invalid = || invariant(SourceImportInvariant::InvalidTargetLinks(synthetic));
    let record = store.symbol(synthetic).ok_or_else(invalid)?;
    let links = store.export_type_links(synthetic).ok_or_else(invalid)?;
    let original = links.target.ok_or_else(invalid)?;
    let originating_import = links.originating_import.ok_or_else(invalid)?;
    let owner = store.symbol(original).ok_or_else(invalid)?;
    let Some([function, namespace]) = owner.declarations() else {
        return Err(invalid());
    };
    let function = *function;
    let namespace = *namespace;
    let exports = record
        .exports()
        .and_then(|exports| store.symbol_table(exports))
        .ok_or_else(invalid)?;
    let default = exports
        .get(InternalSymbolName::Default.as_ref())
        .ok_or_else(invalid)?;
    let default_record = store.symbol(default).ok_or_else(invalid)?;
    let module = default_record.parent().ok_or_else(invalid)?;
    let module_record = store.symbol(module).ok_or_else(invalid)?;
    let module_exports = module_record
        .exports()
        .and_then(|exports| store.symbol_table(exports))
        .ok_or_else(invalid)?;
    let assignment = module_exports
        .get(InternalSymbolName::ExportEquals.as_ref())
        .ok_or_else(invalid)?;
    let alias_record = store.symbol(alias).ok_or_else(invalid)?;
    let Some([binding]) = alias_record.declarations() else {
        return Err(invalid());
    };
    let binding = *binding;
    let Some(SourceNodeParent::Parent(clause)) = store.source_node_parent(binding) else {
        return Err(invalid());
    };

    if record.flags() != SymbolFlags::FUNCTION | SymbolFlags::NAMESPACE_MODULE
        || record.check_flags() != CheckFlags::NONE
        || record.name() != owner.name()
        || record.declarations() != owner.declarations()
        || record.value_declaration() != Some(function)
        || record.members().is_some()
        || record.parent() != owner.parent()
        || record.export_symbol().is_some()
        || store.get_merged_symbol(synthetic) != Some(synthetic)
        || owner.flags() != SymbolFlags::FUNCTION | SymbolFlags::NAMESPACE_MODULE
        || owner.check_flags() != CheckFlags::NONE
        || owner.value_declaration() != Some(function)
        || owner.members().is_some()
        || owner.exports().is_some()
        || owner.parent().is_some()
        || owner.export_symbol().is_some()
        || store.get_merged_symbol(original) != Some(original)
        || exports.len() != 1
        || default_record.flags() != SymbolFlags::ALIAS
        || default_record.check_flags() != CheckFlags::NONE
        || default_record.name() != InternalSymbolName::Default.as_ref()
        || default_record.declarations().is_some()
        || default_record.value_declaration().is_some()
        || default_record.members().is_some()
        || default_record.exports().is_some()
        || default_record.export_symbol().is_some()
        || store.get_merged_symbol(default) != Some(default)
        || store.alias_symbol_links(default)
            != Some(&super::AliasSymbolLinks {
                immediate_target: Some(original),
                alias_target: AliasTargetState::Resolved(original),
                ..super::AliasSymbolLinks::default()
            })
        || module_record.flags() != SymbolFlags::VALUE_MODULE
        || module_record.check_flags() != CheckFlags::NONE
        || module_exports.len() != 1
        || store.get_merged_symbol(module) != Some(module)
        || store.source_node_kind(binding) != Some(SyntaxKind::NamespaceImport)
        || store.source_node_kind(clause) != Some(SyntaxKind::ImportClause)
        || store.source_node_parent(clause) != Some(SourceNodeParent::Parent(originating_import))
        || store.source_node_kind(originating_import) != Some(SyntaxKind::ImportDeclaration)
        || alias_record.flags() != SymbolFlags::ALIAS
        || alias_record.name() != owner.name()
        || store.alias_symbol_links(alias).is_none_or(|alias_links| {
            alias_links.immediate_target != Some(synthetic)
                || alias_links.alias_target != AliasTargetState::Resolved(synthetic)
                || alias_links.type_only_declaration.is_some()
        })
    {
        return Err(invalid());
    }

    let assignment_record = store.symbol(assignment).ok_or_else(invalid)?;
    let Some([assignment_declaration]) = assignment_record.declarations() else {
        return Err(invalid());
    };
    if assignment_record.flags() != SymbolFlags::ALIAS
        || assignment_record.check_flags() != CheckFlags::NONE
        || assignment_record.name() != InternalSymbolName::ExportEquals.as_ref()
        || assignment_record.value_declaration() != Some(*assignment_declaration)
        || assignment_record.members().is_some()
        || assignment_record.exports().is_some()
        || assignment_record.parent() != Some(module)
        || assignment_record.export_symbol().is_some()
        || store.get_merged_symbol(assignment) != Some(assignment)
        || store.source_node_kind(*assignment_declaration) != Some(SyntaxKind::ExportAssignment)
        || store
            .alias_symbol_links(assignment)
            .is_some_and(|assignment_links| {
                assignment_links.type_only_declaration.is_some()
                    || assignment_links
                        .immediate_target
                        .is_some_and(|target| target != original)
                    || assignment_links.alias_target == AliasTargetState::Unknown
                    || assignment_links
                        .alias_target
                        .symbol()
                        .is_some_and(|target| target != original)
            })
    {
        return Err(invalid());
    }

    Ok(AuthenticatedSyntheticImportNamespace {
        function,
        namespace,
        assignment,
        original,
        default,
        module,
        originating_import,
    })
}

pub(super) fn synthetic_source_import_origin(
    store: &CanonicalTypeMapperStore,
    alias: SemanticSymbolId,
    type_: TypeId,
) -> Option<NodeRef> {
    let synthetic = store.alias_symbol_links(alias)?.alias_target.symbol()?;
    let authenticated =
        authenticate_synthetic_import_namespace_identity(store, alias, synthetic).ok()?;
    let record = store.type_payload(type_)?;
    let structured = record.data().structured()?;
    let [property] = structured.properties.as_deref()? else {
        return None;
    };
    let property = *property;
    let members = structured
        .members
        .and_then(|members| store.symbol_table(members))?;
    let callable = store.source_callable_type_for_owner(authenticated.original)?;
    let callable_provenance = store.source_callable_provenance(callable)?;
    let signature = store.signature(callable_provenance.signature)?;
    let void = store.intrinsic_bootstrap()?.void_type;
    if record.flags() != TypeFlags::OBJECT
        || record.object_flags() != ObjectFlags::ANONYMOUS | ObjectFlags::MEMBERS_RESOLVED
        || record.symbol().is_some()
        || structured.call_signature_count != 0
        || structured.signatures.is_some()
        || structured.index_infos.is_some()
        || members.len() != 1
        || members.get(InternalSymbolName::Default.as_ref()) != Some(property)
        || store.symbol(property).is_none_or(|symbol| {
            symbol.flags() != SymbolFlags::PROPERTY
                || symbol.check_flags() != CheckFlags::NONE
                || symbol.name() != InternalSymbolName::Default.as_ref()
                || symbol.declarations().is_some()
                || symbol.value_declaration().is_some()
                || symbol.members().is_some()
                || symbol.exports().is_some()
                || symbol.parent().is_some()
                || symbol.export_symbol().is_some()
        })
        || store.value_symbol_links(property)
            != Some(&ValueSymbolLinks {
                resolved_type: Some(callable),
                ..ValueSymbolLinks::default()
            })
        || callable_provenance.family != SourceCallableFamily::FunctionDeclaration
        || callable_provenance.declaration != authenticated.function
        || callable_provenance.owner_symbol != authenticated.original
        || !signature.parameters().is_empty()
        || signature.resolved_return_type() != Some(void)
        || !matches!(
            validate_stored_source_callable(store, callable),
            StoredSourceCallableValidation::Valid(_)
        )
    {
        return None;
    }
    Some(authenticated.originating_import)
}

fn plan_synthetic_import_namespace(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    global_types: &CanonicalGlobalTypes,
    alias: SemanticSymbolId,
    synthetic: SemanticSymbolId,
) -> Result<PlannedSourceImportValueTarget, SourceImportError> {
    let authenticated = authenticate_synthetic_import_namespace_identity(store, alias, synthetic)?;
    let invalid = || invariant(SourceImportInvariant::InvalidTargetLinks(synthetic));
    let (arena, bound) = host.source(authenticated.function).ok_or_else(invalid)?;
    let facts = bound.source_facts().ok_or_else(invalid)?;
    let function = checked_node(arena, bound, store, authenticated.function)?;
    let NodeData::FunctionDeclaration(function_data) = &function.data else {
        return Err(invalid());
    };
    let namespace = checked_node(arena, bound, store, authenticated.namespace)?;
    let NodeData::ModuleDeclaration(namespace_data) = &namespace.data else {
        return Err(invalid());
    };
    let namespace_body = namespace_data
        .body
        .map(|node| {
            NodeRef::new(
                authenticated.namespace.arena,
                authenticated.namespace.file,
                node,
            )
        })
        .ok_or_else(invalid)?;
    let block = checked_node(arena, bound, store, namespace_body)?;
    let NodeData::ModuleBlock(block_data) = &block.data else {
        return Err(invalid());
    };
    let source = checked_node(arena, bound, store, bound.source_file())?;
    let NodeData::SourceFile(source_data) = &source.data else {
        return Err(invalid());
    };
    let assignment_declaration = store
        .symbol(authenticated.assignment)
        .and_then(ts_binder::semantic::Symbol::value_declaration)
        .ok_or_else(invalid)?;
    let assignment = checked_node(arena, bound, store, assignment_declaration)?;
    let NodeData::ExportAssignment(assignment_data) = &assignment.data else {
        return Err(invalid());
    };
    let expression = NodeRef::new(
        assignment_declaration.arena,
        assignment_declaration.file,
        assignment_data.expression,
    );
    let expression_record = checked_node(arena, bound, store, expression)?;
    let NodeData::Identifier(expression_name) = &expression_record.data else {
        return Err(invalid());
    };
    let function_name = function_data
        .name
        .map(|node| {
            NodeRef::new(
                authenticated.function.arena,
                authenticated.function.file,
                node,
            )
        })
        .ok_or_else(invalid)?;
    let function_name_text = exact_identifier(
        arena,
        bound,
        store,
        function_name,
        authenticated.function,
        SourceImportUnsupported::TargetDeclaration(function_name),
    )?;
    let namespace_name = NodeRef::new(
        authenticated.namespace.arena,
        authenticated.namespace.file,
        namespace_data.name,
    );
    let namespace_name_text = exact_identifier(
        arena,
        bound,
        store,
        namespace_name,
        authenticated.namespace,
        SourceImportUnsupported::TargetDeclaration(namespace_name),
    )?;
    let return_type = function_data
        .type_
        .map(|node| {
            NodeRef::new(
                authenticated.function.arena,
                authenticated.function.file,
                node,
            )
        })
        .ok_or_else(invalid)?;
    let return_record = checked_node(arena, bound, store, return_type)?;
    if !facts.is_declaration_file()
        || !facts.is_external_module()
        || facts.is_javascript_file()
        || source_data.statements.nodes.as_slice()
            != [
                authenticated.function.node,
                authenticated.namespace.node,
                assignment_declaration.node,
            ]
        || bound.symbol(bound.source_file()) != Some(authenticated.module)
        || bound.symbol(authenticated.function) != Some(authenticated.original)
        || bound.symbol(authenticated.namespace) != Some(authenticated.original)
        || bound.symbol(assignment_declaration) != Some(authenticated.assignment)
        || function.kind != SyntaxKind::FunctionDeclaration
        || function.parent != Some(bound.source_file().node)
        || function.flags.0 != 0
        || function_data.asterisk_token.is_some()
        || function_data.body.is_some()
        || !function_data.parameters.nodes.is_empty()
        || function_data.parameters.has_trailing_comma
        || function_data.type_parameters.is_some()
        || function_data.facts != 0
        || !has_exact_modifier_sequence(
            arena,
            bound,
            store,
            authenticated.function,
            function_data.modifiers.as_ref(),
            &[(SyntaxKind::DeclareKeyword, "declare")],
        )?
        || return_record.kind != SyntaxKind::VoidKeyword
        || return_record.parent != Some(authenticated.function.node)
        || return_record.flags.0 != 0
        || !matches!(return_record.data, NodeData::KeywordTypeNode(_))
        || namespace.kind != SyntaxKind::ModuleDeclaration
        || namespace.parent != Some(bound.source_file().node)
        || namespace.flags.0 != 0
        || namespace_data.keyword != SyntaxKind::NamespaceKeyword
        || !has_exact_modifier_sequence(
            arena,
            bound,
            store,
            authenticated.namespace,
            namespace_data.modifiers.as_ref(),
            &[(SyntaxKind::DeclareKeyword, "declare")],
        )?
        || block.kind != SyntaxKind::ModuleBlock
        || block.parent != Some(authenticated.namespace.node)
        || block.flags.0 != 0
        || block_data.flow_node.is_some()
        || !block_data.statements.nodes.is_empty()
        || block_data.statements.has_trailing_comma
        || block_data.facts != 0
        || assignment.kind != SyntaxKind::ExportAssignment
        || assignment.parent != Some(bound.source_file().node)
        || assignment.flags.0 != 0
        || !assignment_data.is_export_equals
        || assignment_data.flow_node.is_some()
        || assignment_data.modifiers.is_some()
        || assignment_data.symbol.is_some()
        || assignment_data.type_.is_some()
        || assignment_data.facts != 0
        || expression_record.kind != SyntaxKind::Identifier
        || expression_record.parent != Some(assignment_declaration.node)
        || expression_record.flags.0 != 0
        || expression_name.flow_node.is_some()
        || expression_name.text != function_name_text
        || namespace_name_text != function_name_text
        || store
            .symbol(authenticated.original)
            .and_then(|owner| owner.name().as_utf8())
            != Some(function_name_text.as_str())
    {
        return Err(invalid());
    }

    let (import_arena, import_bound) = host
        .source(authenticated.originating_import)
        .ok_or_else(invalid)?;
    let import = checked_node(
        import_arena,
        import_bound,
        store,
        authenticated.originating_import,
    )?;
    let NodeData::ImportDeclaration(import_data) = &import.data else {
        return Err(invalid());
    };
    let clause = import_data
        .import_clause
        .map(|node| {
            NodeRef::new(
                authenticated.originating_import.arena,
                authenticated.originating_import.file,
                node,
            )
        })
        .ok_or_else(invalid)?;
    let clause_record = checked_node(import_arena, import_bound, store, clause)?;
    let NodeData::ImportClause(clause_data) = &clause_record.data else {
        return Err(invalid());
    };
    let binding = clause_data
        .named_bindings
        .map(|node| NodeRef::new(clause.arena, clause.file, node))
        .ok_or_else(invalid)?;
    let binding_record = checked_node(import_arena, import_bound, store, binding)?;
    let NodeData::NamespaceImport(binding_data) = &binding_record.data else {
        return Err(invalid());
    };
    let imported_name = NodeRef::new(binding.arena, binding.file, binding_data.name);
    let imported_name_text = exact_identifier(
        import_arena,
        import_bound,
        store,
        imported_name,
        binding,
        SourceImportUnsupported::TargetDeclaration(imported_name),
    )?;
    if import.kind != SyntaxKind::ImportDeclaration
        || import.parent != Some(import_bound.source_file().node)
        || import.flags.0 != 0
        || import_data.attributes.is_some()
        || import_data.flow_node.is_some()
        || import_data.modifiers.is_some()
        || import_data.symbol.is_some()
        || import_data.facts != 0
        || clause_record.kind != SyntaxKind::ImportClause
        || clause_record.parent != Some(authenticated.originating_import.node)
        || clause_record.flags.0 != 0
        || clause_data.name.is_some()
        || clause_data.phase_modifier.is_some()
        || clause_data.local_symbol.is_some()
        || clause_data.symbol.is_some()
        || clause_data.facts != 0
        || binding_record.kind != SyntaxKind::NamespaceImport
        || binding_record.parent != Some(clause.node)
        || binding_record.flags.0 != 0
        || binding_data.local_symbol.is_some()
        || binding_data.symbol.is_some()
        || import_bound.symbol(binding) != Some(alias)
        || imported_name_text != function_name_text
    {
        return Err(invalid());
    }

    preflight_import_target_value_links(store, synthetic)?;
    preflight_import_target_value_links(store, authenticated.original)?;
    let callable = plan_source_callable(
        store,
        host,
        authenticated.function,
        authenticated.original,
        Some(CanonicalArrayTargets::from_global_types(global_types)),
    )?;
    if callable.family != SourceCallableFamily::FunctionDeclaration
        || callable.declaration != authenticated.function
        || callable.owner_symbol != authenticated.original
        || !callable.parameters.is_empty()
        || !callable.type_parameters.is_empty()
        || callable.return_type.type_node() != Some(return_type)
    {
        return Err(invalid());
    }

    Ok(PlannedSourceImportValueTarget::ModuleNamespace {
        declaration: authenticated.function,
        members: vec![PlannedSourceImportModuleMember {
            name: EscapedName::internal(InternalSymbolName::Default),
            symbol: authenticated.default,
            value_symbol: authenticated.original,
            target: PlannedSourceImportValueTarget::AnnotatedFunction(Box::new(callable)),
        }],
    })
}

fn valid_imported_namespace_declaration(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    declaration: NodeRef,
    module: SemanticSymbolId,
) -> Result<bool, SourceImportError> {
    let declaration_record = checked_node(arena, bound, store, declaration)?;
    let NodeData::ModuleDeclaration(namespace) = &declaration_record.data else {
        return Ok(false);
    };
    let Some(record) = store.symbol(module) else {
        return Ok(false);
    };
    let name = NodeRef::new(declaration.arena, declaration.file, namespace.name);
    let name_record = checked_node(arena, bound, store, name)?;
    if !matches!(
        &name_record.data,
        NodeData::Identifier(identifier)
            if name_record.kind == SyntaxKind::Identifier
                && name_record.parent == Some(declaration.node)
                && name_record.flags.0 == 0
                && identifier.flow_node.is_none()
                && identifier.text.as_bytes() == record.name().as_bytes()
    ) {
        return Ok(false);
    }

    let Some(parent) = declaration_record.parent else {
        return Ok(false);
    };
    let expected_parent = if parent == bound.source_file().node {
        bound.symbol(bound.source_file())
    } else {
        let block = NodeRef::new(declaration.arena, declaration.file, parent);
        let block_record = checked_node(arena, bound, store, block)?;
        let NodeData::ModuleBlock(block_data) = &block_record.data else {
            return Ok(false);
        };
        if block_record.kind != SyntaxKind::ModuleBlock
            || block_data
                .statements
                .nodes
                .iter()
                .filter(|candidate| **candidate == declaration.node)
                .count()
                != 1
        {
            return Ok(false);
        }
        let Some(owner_node) = block_record.parent else {
            return Ok(false);
        };
        let owner_declaration = NodeRef::new(declaration.arena, declaration.file, owner_node);
        let owner_record = checked_node(arena, bound, store, owner_declaration)?;
        let NodeData::ModuleDeclaration(owner_namespace) = &owner_record.data else {
            return Ok(false);
        };
        if owner_record.kind != SyntaxKind::ModuleDeclaration
            || owner_namespace.body != Some(block.node)
        {
            return Ok(false);
        }
        bound.symbol(owner_declaration)
    };

    Ok(if let Some(expected_parent) = expected_parent {
        record.parent() == Some(expected_parent)
            && store
                .symbol(expected_parent)
                .and_then(ts_binder::semantic::Symbol::exports)
                .and_then(|exports| store.symbol_table(exports))
                .and_then(|exports| exports.get(record.name()))
                == Some(module)
    } else {
        parent == bound.source_file().node && record.parent().is_none()
    })
}

#[allow(clippy::too_many_arguments)]
fn materialize_imported_module_namespace(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    global_types: &CanonicalGlobalTypes,
    options: CanonicalCheckerOptions,
    session: &mut InstantiationSession,
    diagnostics: &mut CanonicalCheckerDiagnostics,
    declaration: NodeRef,
    module: SemanticSymbolId,
    members: Vec<PlannedSourceImportModuleMember>,
    expected_type: Option<TypeId>,
) -> Result<(TypeId, Vec<PreparedSourceImportModuleProperty>), SourceImportError> {
    let owner =
        (store.source_node_kind(declaration) == Some(SyntaxKind::SourceFile)).then_some(module);
    let cached = store
        .value_symbol_links(module)
        .and_then(|links| links.resolved_type);
    if expected_type.is_some() && cached.is_some() && expected_type != cached {
        return Err(invariant(SourceImportInvariant::InvalidTargetLinks(module)));
    }
    let existing = expected_type.or(cached).or_else(|| {
        owner.and_then(|owner| {
            store.types().find_map(|(type_, record)| {
                (record.symbol() == Some(owner)
                    && record.object_flags()
                        == ObjectFlags::ANONYMOUS | ObjectFlags::MEMBERS_RESOLVED)
                    .then_some(type_)
            })
        })
    });
    if let Some(existing) = existing {
        let structured = store
            .type_payload(existing)
            .filter(|record| {
                record.symbol() == owner
                    && record.object_flags()
                        == ObjectFlags::ANONYMOUS | ObjectFlags::MEMBERS_RESOLVED
            })
            .and_then(|record| record.data().structured())
            .ok_or_else(|| invariant(SourceImportInvariant::InvalidTargetLinks(module)))?;
        let property_symbols = structured.properties.as_deref().unwrap_or_default();
        if property_symbols.len() != members.len() {
            return Err(invariant(SourceImportInvariant::InvalidTargetLinks(module)));
        }
        let table = structured
            .members
            .and_then(|members| store.symbol_table(members));
        let existing_members = members
            .into_iter()
            .map(|member| {
                let symbol = table
                    .and_then(|table| table.get(member.name.as_ref()))
                    .filter(|symbol| property_symbols.contains(symbol))
                    .ok_or_else(|| invariant(SourceImportInvariant::InvalidTargetLinks(module)))?;
                let type_ = store
                    .value_symbol_links(symbol)
                    .filter(|links| links.target == owner.map(|_| member.symbol))
                    .and_then(|links| links.resolved_type)
                    .ok_or_else(|| invariant(SourceImportInvariant::InvalidTargetLinks(module)))?;
                if store
                    .value_symbol_links(member.value_symbol)
                    .and_then(|links| links.resolved_type)
                    .is_some_and(|cached| cached != type_)
                {
                    return Err(invariant(SourceImportInvariant::InvalidTargetLinks(module)));
                }
                Ok((member, symbol, type_))
            })
            .collect::<Result<Vec<_>, SourceImportError>>()?;
        let mut properties = Vec::with_capacity(existing_members.len());
        for (member, symbol, type_) in existing_members {
            let namespace = match member.target {
                PlannedSourceImportValueTarget::ModuleNamespace {
                    declaration,
                    members,
                } => {
                    let (nested_type, properties) = materialize_imported_module_namespace(
                        store,
                        host,
                        global_types,
                        options,
                        session,
                        diagnostics,
                        declaration,
                        member.value_symbol,
                        members,
                        Some(type_),
                    )?;
                    if nested_type != type_ {
                        return Err(invariant(SourceImportInvariant::InvalidTargetLinks(module)));
                    }
                    Some(Box::new(PreparedSourceImportNestedNamespace {
                        declaration,
                        properties,
                        links: prepare_value_links(store, member.value_symbol, nested_type, false)?,
                    }))
                }
                _ => None,
            };
            properties.push(PreparedSourceImportModuleProperty {
                name: member.name,
                symbol,
                target_symbol: member.symbol,
                value_symbol: member.value_symbol,
                type_,
                namespace,
            });
        }
        return Ok((existing, properties));
    }

    preflight_imported_module_namespace_members(
        store,
        host,
        global_types,
        options,
        session,
        diagnostics,
        &members,
    )?;

    let mut resolved_members = Vec::with_capacity(members.len());
    for member in members {
        let (type_, namespace) = match member.target {
            PlannedSourceImportValueTarget::AnnotatedConst { type_node, .. } => (
                CanonicalTypeQuery::new_with_global_types_and_session(
                    store,
                    host,
                    global_types,
                    options,
                    session,
                    diagnostics,
                )?
                .get_type_from_type_node(type_node)?,
                None,
            ),
            PlannedSourceImportValueTarget::AnnotatedFunction(callable) => {
                let type_ = CanonicalTypeQuery::new_with_global_types_and_session(
                    store,
                    host,
                    global_types,
                    options,
                    session,
                    diagnostics,
                )?
                .get_type_of_source_callable(callable.declaration, callable.owner_symbol)?;
                let signature = store
                    .source_callable_provenance(type_)
                    .map(|provenance| provenance.signature)
                    .ok_or_else(|| {
                        invariant(SourceImportInvariant::InvalidTargetLinks(
                            callable.owner_symbol,
                        ))
                    })?;
                if callable.return_type.is_inferred()
                    && store
                        .signature(signature)
                        .and_then(super::signatures::Signature::resolved_return_type)
                        .is_none()
                {
                    let void = store
                        .intrinsic_bootstrap()
                        .map(|bootstrap| bootstrap.void_type)
                        .ok_or_else(|| {
                            invariant(SourceImportInvariant::InvalidTargetLinks(
                                callable.owner_symbol,
                            ))
                        })?;
                    publish_inferred_source_callable_return(store, &callable, signature, void)?;
                }
                CanonicalTypeQuery::new_with_global_types_and_session(
                    store,
                    host,
                    global_types,
                    options,
                    session,
                    diagnostics,
                )?
                .get_return_type_of_signature(signature)?;
                (type_, None)
            }
            PlannedSourceImportValueTarget::ConstEnum { .. } => (
                enums::get_enum_semantics(store, host, member.value_symbol)
                    .map_err(DeclaredTypeError::from)?
                    .value_type,
                None,
            ),
            PlannedSourceImportValueTarget::ExportedObject { type_, .. } => (type_, None),
            PlannedSourceImportValueTarget::PublishedObjectConst { type_, .. } => (type_, None),
            PlannedSourceImportValueTarget::DeclarationNumericConst { literal, .. } => (
                declaration_numeric_literal_type(store, member.value_symbol, &literal)?,
                None,
            ),
            PlannedSourceImportValueTarget::JavaScriptAnnotatedConst {
                declaration,
                annotation,
                cached_type,
            } => {
                let type_ = if let Some(annotation) = annotation {
                    resolve_planned_jsdoc_type(store, global_types, options, &annotation).map_err(
                        |_| unsupported(SourceImportUnsupported::TargetDeclaration(declaration)),
                    )?
                } else {
                    cached_type.ok_or_else(|| {
                        unsupported(SourceImportUnsupported::MissingTargetAnnotation(
                            declaration,
                        ))
                    })?
                };
                (type_, None)
            }
            PlannedSourceImportValueTarget::CommonJsNamedExport { cached_type, .. } => {
                (cached_type, None)
            }
            PlannedSourceImportValueTarget::ModuleNamespace {
                declaration,
                members,
            } => {
                let (type_, properties) = materialize_imported_module_namespace(
                    store,
                    host,
                    global_types,
                    options,
                    session,
                    diagnostics,
                    declaration,
                    member.value_symbol,
                    members,
                    None,
                )?;
                let links = prepare_value_links(store, member.value_symbol, type_, false)?;
                (
                    type_,
                    Some(Box::new(PreparedSourceImportNestedNamespace {
                        declaration,
                        properties,
                        links,
                    })),
                )
            }
        };
        if let Some(links) = store.value_symbol_links(member.value_symbol)
            && links.resolved_type.is_some_and(|cached| cached != type_)
        {
            return Err(invariant(SourceImportInvariant::CachedTypeMismatch {
                symbol: member.value_symbol,
                cached: links.resolved_type.expect("cached type was checked"),
                expected: type_,
            }));
        }
        resolved_members.push((
            member.name,
            member.symbol,
            member.value_symbol,
            type_,
            namespace,
        ));
    }

    let count = resolved_members.len();
    if !store.try_reserve_types(1)
        || !store.try_reserve_checker_symbol_allocations(count, usize::from(count != 0))
        || !store.try_reserve_value_symbol_links(count)
    {
        return Err(invariant(SourceImportInvariant::InvalidTargetLinks(module)));
    }
    let table = if count == 0 {
        None
    } else {
        Some(store.alloc_symbol_table())
    };
    let mut properties = Vec::with_capacity(count);
    for (name, target_symbol, value_symbol, type_, namespace) in resolved_members {
        let symbol = store
            .alloc_symbol(SymbolData::new(SymbolFlags::PROPERTY, name.clone()))
            .ok_or_else(|| invariant(SourceImportInvariant::InvalidTargetLinks(module)))?;
        if !store.set_value_symbol_links(
            symbol,
            ValueSymbolLinks {
                resolved_type: Some(type_),
                target: owner.map(|_| target_symbol),
                ..ValueSymbolLinks::default()
            },
        ) || table
            .is_none_or(|table| store.insert_symbol(table, name.clone(), symbol) != Some(None))
        {
            return Err(invariant(SourceImportInvariant::InvalidTargetLinks(module)));
        }
        properties.push(PreparedSourceImportModuleProperty {
            name,
            symbol,
            target_symbol,
            value_symbol,
            type_,
            namespace,
        });
    }
    let type_ = store
        .alloc_plain_object_type(ObjectFlags::ANONYMOUS, owner)
        .ok_or_else(|| invariant(SourceImportInvariant::InvalidTargetLinks(module)))?;
    let property_symbols = (!properties.is_empty())
        .then(|| properties.iter().map(|property| property.symbol).collect());
    if !store.set_structured_type_members(type_, table, property_symbols, None, None, None) {
        return Err(invariant(SourceImportInvariant::InvalidTargetLinks(module)));
    }
    Ok((type_, properties))
}

#[allow(clippy::too_many_arguments)]
fn preflight_imported_module_namespace_members(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    global_types: &CanonicalGlobalTypes,
    options: CanonicalCheckerOptions,
    session: &mut InstantiationSession,
    diagnostics: &mut CanonicalCheckerDiagnostics,
    members: &[PlannedSourceImportModuleMember],
) -> Result<(), SourceImportError> {
    for member in members {
        match &member.target {
            PlannedSourceImportValueTarget::AnnotatedConst { type_node, .. } => {
                CanonicalTypeQuery::new_with_global_types_and_session(
                    store,
                    host,
                    global_types,
                    options,
                    session,
                    diagnostics,
                )?
                .preflight_type_from_type_node(*type_node)?;
            }
            PlannedSourceImportValueTarget::AnnotatedFunction(callable) => {
                CanonicalTypeQuery::new_with_global_types_and_session(
                    store,
                    host,
                    global_types,
                    options,
                    session,
                    diagnostics,
                )?
                .preflight_type_of_source_callable(callable.declaration, callable.owner_symbol)?;
            }
            PlannedSourceImportValueTarget::DeclarationNumericConst { .. }
            | PlannedSourceImportValueTarget::JavaScriptAnnotatedConst { .. }
            | PlannedSourceImportValueTarget::CommonJsNamedExport { .. }
            | PlannedSourceImportValueTarget::ExportedObject { .. }
            | PlannedSourceImportValueTarget::PublishedObjectConst { .. } => {}
            PlannedSourceImportValueTarget::ConstEnum { .. } => {
                enums::preflight_enum(store, host, member.value_symbol)
                    .map_err(DeclaredTypeError::from)?;
            }
            PlannedSourceImportValueTarget::ModuleNamespace { members, .. } => {
                preflight_imported_module_namespace_members(
                    store,
                    host,
                    global_types,
                    options,
                    session,
                    diagnostics,
                    members,
                )?;
            }
        }
    }
    Ok(())
}

fn plan_direct_commonjs_named_export_target(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    alias: SemanticSymbolId,
    target: SemanticSymbolId,
) -> Result<PlannedSourceImportValueTarget, SourceImportError> {
    let target_record = store
        .symbol(target)
        .ok_or_else(|| invariant(SourceImportInvariant::InvalidTargetSymbol(target)))?;
    let Some(declarations) = target_record
        .declarations()
        .filter(|declarations| !declarations.is_empty())
    else {
        return Err(unsupported(SourceImportUnsupported::TargetSymbol {
            alias,
            target,
            flags: target_record.flags(),
        }));
    };
    let declaration = target_record
        .value_declaration()
        .filter(|declaration| declarations.contains(declaration))
        .ok_or_else(|| invariant(SourceImportInvariant::InvalidTargetSymbol(target)))?;
    let (arena, bound) = host
        .source(declaration)
        .ok_or_else(|| unsupported(SourceImportUnsupported::TargetDeclaration(declaration)))?;
    let facts = bound.source_facts().ok_or_else(|| {
        invariant(SourceImportInvariant::MissingSourceFacts(
            bound.source_file(),
        ))
    })?;
    let declaration_record = checked_node(arena, bound, store, declaration)?;
    if !facts.is_javascript_file()
        || !facts.is_common_js_module()
        || target_record.flags() != SymbolFlags::FUNCTION_SCOPED_VARIABLE
        || target_record.check_flags() != CheckFlags::NONE
        || target_record.value_declaration() != Some(declaration)
        || declaration_record.kind != SyntaxKind::BinaryExpression
    {
        return Err(unsupported(SourceImportUnsupported::TargetDeclaration(
            declaration,
        )));
    }
    let symbol_type = store
        .value_symbol_links(target)
        .map(|links| {
            let expected = ValueSymbolLinks {
                resolved_type: links.resolved_type,
                ..ValueSymbolLinks::default()
            };
            if links != &expected
                || links
                    .resolved_type
                    .is_some_and(|type_| store.type_payload(type_).is_none())
            {
                return Err(invariant(SourceImportInvariant::InvalidTargetLinks(target)));
            }
            Ok(links.resolved_type)
        })
        .transpose()?
        .flatten();
    let mut assignments = Vec::with_capacity(declarations.len());
    let mut assignment_type = None;
    for &candidate in declarations {
        let candidate_record = checked_node(arena, bound, store, candidate)?;
        let statement = candidate_record
            .parent
            .map(|node| NodeRef::new(candidate.arena, candidate.file, node))
            .ok_or_else(|| unsupported(SourceImportUnsupported::TargetDeclaration(candidate)))?;
        let assignment =
            super::assignment::plan_commonjs_named_assignment(arena, bound, store, statement)
                .map_err(|error| match error {
                    super::assignment::AssignmentPlanError::Unsupported(_) => {
                        unsupported(SourceImportUnsupported::TargetDeclaration(candidate))
                    }
                    super::assignment::AssignmentPlanError::Invariant(_) => {
                        invariant(SourceImportInvariant::InvalidTargetSymbol(target))
                    }
                    super::assignment::AssignmentPlanError::DeclaredType(error) => {
                        SourceImportError::DeclaredType(error)
                    }
                })?
                .ok_or_else(|| {
                    unsupported(SourceImportUnsupported::TargetDeclaration(candidate))
                })?;
        if assignment.expression != candidate || assignment.target_symbol != target {
            return Err(invariant(SourceImportInvariant::InvalidTargetSymbol(
                target,
            )));
        }
        let assignment = CommonJsNamedExportAssignment {
            expression: assignment.expression,
            left: assignment.left,
            right: assignment.right,
        };
        let cached = validate_commonjs_named_export_assignment_cache(
            store,
            target,
            assignment,
            symbol_type,
        )?;
        if candidate == declaration {
            assignment_type = cached;
        }
        assignments.push(assignment);
    }
    if declarations.len() != 1 && symbol_type.is_none() {
        return Err(unsupported(
            SourceImportUnsupported::MissingTargetAnnotation(declaration),
        ));
    }
    let cached_type = symbol_type.or(assignment_type).ok_or_else(|| {
        unsupported(SourceImportUnsupported::MissingTargetAnnotation(
            declaration,
        ))
    })?;

    Ok(PlannedSourceImportValueTarget::CommonJsNamedExport {
        declaration,
        assignments,
        cached_type,
    })
}

fn validate_commonjs_named_export_assignment_cache(
    store: &CanonicalTypeMapperStore,
    target: SemanticSymbolId,
    assignment: CommonJsNamedExportAssignment,
    symbol_type: Option<TypeId>,
) -> Result<Option<TypeId>, SourceImportError> {
    let node_type = |node| {
        let Some(links) = store.type_node_links(node) else {
            return Ok(None);
        };
        let expected = TypeNodeLinks {
            resolved_type: links.resolved_type,
            ..TypeNodeLinks::default()
        };
        if links != &expected
            || links
                .resolved_type
                .is_some_and(|type_| store.type_payload(type_).is_none())
        {
            return Err(invariant(SourceImportInvariant::InvalidTargetLinks(target)));
        }
        Ok(links.resolved_type)
    };
    let right = node_type(assignment.right)?;
    let left = node_type(assignment.left)?;
    let expression = node_type(assignment.expression)?;
    if let (Some(right), Some(expression)) = (right, expression)
        && !commonjs_assignment_value_types_match(store, right, expression)
    {
        return Err(invariant(SourceImportInvariant::CachedTypeMismatch {
            symbol: target,
            cached: right,
            expected: expression,
        }));
    }
    let assigned = expression.or(right);
    if let Some(left) = left {
        let annotation_matches = symbol_type == Some(left);
        if !annotation_matches
            && assigned.is_some_and(|assigned| {
                !commonjs_assignment_value_types_match(store, left, assigned)
            })
        {
            return Err(invariant(SourceImportInvariant::CachedTypeMismatch {
                symbol: target,
                cached: left,
                expected: assigned.expect("the conflicting assignment type is present"),
            }));
        }
        if let (Some(symbol_type), Some(assigned)) = (symbol_type, assigned)
            && !annotation_matches
            && !commonjs_export_type_contains_value(store, symbol_type, assigned)
        {
            return Err(invariant(SourceImportInvariant::CachedTypeMismatch {
                symbol: target,
                cached: symbol_type,
                expected: assigned,
            }));
        }
    } else if let (Some(symbol_type), Some(assigned)) = (symbol_type, assigned)
        && !commonjs_export_type_contains_value(store, symbol_type, assigned)
    {
        return Err(invariant(SourceImportInvariant::CachedTypeMismatch {
            symbol: target,
            cached: symbol_type,
            expected: assigned,
        }));
    }
    Ok(assigned.or(left))
}

fn commonjs_assignment_value_types_match(
    store: &CanonicalTypeMapperStore,
    left: TypeId,
    right: TypeId,
) -> bool {
    if left == right {
        return true;
    }
    let Some(left_record) = store.type_payload(left) else {
        return false;
    };
    let Some(right_record) = store.type_payload(right) else {
        return false;
    };
    match (left_record.data(), right_record.data()) {
        (TypeData::Literal(left), TypeData::Literal(right)) => {
            left.regular_type == right.regular_type
        }
        (TypeData::Literal(_), _) => {
            commonjs_literal_base_type(store, left_record.flags()) == Some(right)
        }
        (_, TypeData::Literal(_)) => {
            commonjs_literal_base_type(store, right_record.flags()) == Some(left)
        }
        _ => false,
    }
}

fn commonjs_literal_base_type(
    store: &CanonicalTypeMapperStore,
    flags: TypeFlags,
) -> Option<TypeId> {
    let bootstrap = store.intrinsic_bootstrap()?;
    if flags.intersects(TypeFlags::STRING_LITERAL) {
        Some(bootstrap.string_type)
    } else if flags.intersects(TypeFlags::NUMBER_LITERAL) {
        Some(bootstrap.number_type)
    } else if flags.intersects(TypeFlags::BIG_INT_LITERAL) {
        Some(bootstrap.bigint_type)
    } else if flags.intersects(TypeFlags::BOOLEAN_LITERAL) {
        Some(bootstrap.boolean_type)
    } else {
        None
    }
}

fn commonjs_export_type_contains_value(
    store: &CanonicalTypeMapperStore,
    exported: TypeId,
    assigned: TypeId,
) -> bool {
    if commonjs_assignment_value_types_match(store, exported, assigned) {
        return true;
    }
    let Some(TypeData::Union(union)) = store.type_payload(exported).map(TypeRecord::data) else {
        return false;
    };
    union
        .union
        .types
        .iter()
        .copied()
        .any(|candidate| commonjs_assignment_value_types_match(store, candidate, assigned))
}

fn plan_direct_javascript_const_target(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    global_types: &CanonicalGlobalTypes,
    options: CanonicalCheckerOptions,
    alias: SemanticSymbolId,
    target: SemanticSymbolId,
) -> Result<PlannedSourceImportValueTarget, SourceImportError> {
    let target_record = store
        .symbol(target)
        .ok_or_else(|| invariant(SourceImportInvariant::InvalidTargetSymbol(target)))?;
    let Some([declaration]) = target_record.declarations() else {
        return Err(unsupported(SourceImportUnsupported::TargetSymbol {
            alias,
            target,
            flags: target_record.flags(),
        }));
    };
    let declaration = *declaration;
    let (arena, bound) = host
        .source(declaration)
        .ok_or_else(|| unsupported(SourceImportUnsupported::TargetDeclaration(declaration)))?;
    let facts = bound.source_facts().ok_or_else(|| {
        invariant(SourceImportInvariant::MissingSourceFacts(
            bound.source_file(),
        ))
    })?;
    let record = checked_node(arena, bound, store, declaration)?;
    let NodeData::VariableDeclaration(variable) = &record.data else {
        return Err(unsupported(SourceImportUnsupported::TargetDeclaration(
            declaration,
        )));
    };
    let commonjs_variable = facts.is_common_js_module()
        && target_record.flags() == SymbolFlags::FUNCTION_SCOPED_VARIABLE;
    if !facts.is_javascript_file()
        || !facts.is_external_or_common_js_module()
        || record.kind != SyntaxKind::VariableDeclaration
        || record.flags.0 != 0
        || target_record.flags() != SymbolFlags::BLOCK_SCOPED_VARIABLE && !commonjs_variable
        || target_record.value_declaration() != Some(declaration)
        || variable.type_.is_some()
        || variable.initializer.is_none()
        || variable.exclamation_token.is_some()
        || variable.local_symbol.is_some()
        || variable.symbol.is_some()
        || variable.facts != 0
    {
        return Err(unsupported(SourceImportUnsupported::TargetDeclaration(
            declaration,
        )));
    }
    let name = NodeRef::new(declaration.arena, declaration.file, variable.name);
    let name_text = exact_identifier(
        arena,
        bound,
        store,
        name,
        declaration,
        SourceImportUnsupported::TargetDeclaration(name),
    )?;
    if name_text.as_bytes() != target_record.name().as_bytes() {
        return Err(invariant(SourceImportInvariant::TargetNameMismatch {
            target,
            name,
        }));
    }
    if commonjs_variable {
        authenticate_commonjs_local_variable_target(arena, bound, store, target, declaration)?;
    }

    let jsdoc = plan_javascript_source_jsdoc(arena, bound.source_file())
        .map_err(|_| unsupported(SourceImportUnsupported::TargetDeclaration(declaration)))?;
    if !jsdoc.diagnostics().is_empty() {
        return Err(unsupported(SourceImportUnsupported::TargetDeclaration(
            declaration,
        )));
    }
    let annotation = jsdoc
        .declaration(declaration)
        .and_then(|declaration| declaration.type_())
        .cloned();
    let cached_type = store
        .value_symbol_links(target)
        .and_then(|links| links.resolved_type);
    if annotation.is_none() && cached_type.is_none() {
        return Err(unsupported(
            SourceImportUnsupported::MissingTargetAnnotation(declaration),
        ));
    }
    if let Some(annotation) = &annotation {
        preflight_planned_jsdoc_type(store, global_types, options, annotation)
            .map_err(|_| unsupported(SourceImportUnsupported::TargetDeclaration(declaration)))?;
    }

    Ok(PlannedSourceImportValueTarget::JavaScriptAnnotatedConst {
        declaration,
        annotation,
        cached_type,
    })
}

fn authenticate_commonjs_local_variable_target(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    target: SemanticSymbolId,
    declaration: NodeRef,
) -> Result<(), SourceImportError> {
    let target_record = store
        .symbol(target)
        .ok_or_else(|| invariant(SourceImportInvariant::InvalidTargetSymbol(target)))?;
    let source = bound.source_file();
    let declaration_record = checked_node(arena, bound, store, declaration)?;
    let list = declaration_record
        .parent
        .map(|node| NodeRef::new(declaration.arena, declaration.file, node))
        .ok_or_else(|| unsupported(SourceImportUnsupported::TargetDeclaration(declaration)))?;
    let list_record = checked_node(arena, bound, store, list)?;
    let NodeData::VariableDeclarationList(list_data) = &list_record.data else {
        return Err(unsupported(SourceImportUnsupported::TargetDeclaration(
            declaration,
        )));
    };
    let statement = list_record
        .parent
        .map(|node| NodeRef::new(declaration.arena, declaration.file, node))
        .ok_or_else(|| unsupported(SourceImportUnsupported::TargetDeclaration(declaration)))?;
    let statement_record = checked_node(arena, bound, store, statement)?;
    let NodeData::VariableStatement(statement_data) = &statement_record.data else {
        return Err(unsupported(SourceImportUnsupported::TargetDeclaration(
            declaration,
        )));
    };
    let source_record = checked_node(arena, bound, store, source)?;
    let NodeData::SourceFile(source_data) = &source_record.data else {
        return Err(invariant(SourceImportInvariant::InvalidSource(source)));
    };
    if target_record.flags() != SymbolFlags::FUNCTION_SCOPED_VARIABLE
        || target_record.check_flags() != CheckFlags::NONE
        || target_record.declarations() != Some(&[declaration])
        || target_record.value_declaration() != Some(declaration)
        || target_record.members().is_some()
        || target_record.exports().is_some()
        || target_record.parent().is_some()
        || target_record.export_symbol().is_some()
        || store.get_merged_symbol(target) != Some(target)
        || bound.symbol(declaration) != Some(target)
        || bound.local_symbol(declaration).is_some()
        || bound
            .locals(source)
            .and_then(|locals| store.symbol_table(locals))
            .and_then(|locals| locals.get(target_record.name()))
            != Some(target)
        || list_record.kind != SyntaxKind::VariableDeclarationList
        || list_record.flags.0 != 0
        || list_data.facts != 0
        || list_data
            .declarations
            .nodes
            .iter()
            .filter(|node| **node == declaration.node)
            .count()
            != 1
        || statement_record.kind != SyntaxKind::VariableStatement
        || statement_record.parent != Some(source.node)
        || statement_record.flags.0 != 0
        || statement_data.declaration_list != list.node
        || statement_data.modifiers.is_some()
        || statement_data.flow_node.is_some()
        || statement_data.facts != 0
        || source_data
            .statements
            .nodes
            .iter()
            .filter(|node| **node == statement.node)
            .count()
            != 1
    {
        return Err(invariant(SourceImportInvariant::InvalidTargetSymbol(
            target,
        )));
    }
    Ok(())
}

fn plan_direct_annotated_function_target(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    global_types: &CanonicalGlobalTypes,
    alias: SemanticSymbolId,
    target: SemanticSymbolId,
    namespace_module: Option<SemanticSymbolId>,
) -> Result<SourceCallablePlan, SourceImportError> {
    let target_record = store
        .symbol(target)
        .ok_or_else(|| invariant(SourceImportInvariant::InvalidTargetSymbol(target)))?;
    if target_record.flags() != SymbolFlags::FUNCTION {
        return Err(unsupported(SourceImportUnsupported::TargetSymbol {
            alias,
            target,
            flags: target_record.flags(),
        }));
    }
    let Some([declaration]) = target_record.declarations() else {
        return Err(unsupported(SourceImportUnsupported::TargetSymbol {
            alias,
            target,
            flags: target_record.flags(),
        }));
    };
    let declaration = *declaration;
    if target_record.value_declaration() != Some(declaration) {
        return Err(invariant(SourceImportInvariant::InvalidTargetSymbol(
            target,
        )));
    }
    let inferred_return = host.node(declaration).is_some_and(|record| {
        matches!(&record.data, NodeData::FunctionDeclaration(function) if function.type_.is_none())
    });
    if inferred_return
        && let Some(type_) = store.source_callable_type_for_owner(target)
        && store.value_symbol_links(target)
            != Some(&ValueSymbolLinks {
                resolved_type: Some(type_),
                ..ValueSymbolLinks::default()
            })
    {
        return Err(invariant(SourceImportInvariant::InvalidTargetLinks(target)));
    }
    let callable = plan_source_callable(
        store,
        host,
        declaration,
        target,
        Some(CanonicalArrayTargets::from_global_types(global_types)),
    )?;
    if callable.return_type.is_inferred() {
        let state = source_callable_state(store, &callable, false)
            .map_err(|_| invariant(SourceImportInvariant::InvalidTargetLinks(target)))?;
        match state {
            SourceCallableState::Resolved { type_, signature } => {
                if store.source_callable_type_for_owner(target) != Some(type_)
                    || store
                        .value_symbol_links(target)
                        .and_then(|links| links.resolved_type)
                        != Some(type_)
                    || store
                        .signature(signature)
                        .and_then(super::signatures::Signature::resolved_return_type)
                        .is_none()
                    || !matches!(
                        validate_stored_source_callable(store, type_),
                        StoredSourceCallableValidation::Valid(_)
                    )
                {
                    return Err(invariant(SourceImportInvariant::InvalidTargetLinks(target)));
                }
            }
            SourceCallableState::Cold | SourceCallableState::AwaitingInferredReturn { .. } => {
                let Some(module) = namespace_module else {
                    return Err(unsupported(SourceImportUnsupported::TargetSymbol {
                        alias,
                        target,
                        flags: target_record.flags(),
                    }));
                };
                if !exact_namespace_empty_void_function(store, host, &callable, module)? {
                    return Err(unsupported(SourceImportUnsupported::TargetSymbol {
                        alias,
                        target,
                        flags: target_record.flags(),
                    }));
                }
            }
            _ => {
                return Err(unsupported(SourceImportUnsupported::TargetSymbol {
                    alias,
                    target,
                    flags: target_record.flags(),
                }));
            }
        }
    }
    if callable.family != SourceCallableFamily::FunctionDeclaration
        || callable.declaration != declaration
        || callable.owner_symbol != target
    {
        return Err(invariant(SourceImportInvariant::InvalidTargetSymbol(
            target,
        )));
    }
    Ok(callable)
}

fn exact_namespace_empty_void_function(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    callable: &SourceCallablePlan,
    module: SemanticSymbolId,
) -> Result<bool, SourceImportError> {
    let declaration = callable.declaration;
    let Some((arena, bound)) = host.source(declaration) else {
        return Ok(false);
    };
    let Some(facts) = bound.source_facts() else {
        return Ok(false);
    };
    let Some(owner) = store.symbol(callable.owner_symbol) else {
        return Ok(false);
    };
    let Some(module_record) = store.symbol(module) else {
        return Ok(false);
    };
    let declaration_record = checked_node(arena, bound, store, declaration)?;
    let NodeData::FunctionDeclaration(function) = &declaration_record.data else {
        return Ok(false);
    };
    let body = callable.body;
    let body_record = checked_node(arena, bound, store, body)?;
    let NodeData::Block(block) = &body_record.data else {
        return Ok(false);
    };
    let Some(name) = function.name else {
        return Ok(false);
    };
    let name = NodeRef::new(declaration.arena, declaration.file, name);
    let name_text = exact_identifier(
        arena,
        bound,
        store,
        name,
        declaration,
        SourceImportUnsupported::TargetDeclaration(name),
    )?;
    let source_record = checked_node(arena, bound, store, bound.source_file())?;
    let NodeData::SourceFile(source) = &source_record.data else {
        return Ok(false);
    };
    let valid_container = if declaration_record.parent == Some(bound.source_file().node) {
        bound.symbol(bound.source_file()) == Some(module)
            && source
                .statements
                .nodes
                .iter()
                .filter(|node| **node == declaration.node)
                .count()
                == 1
    } else if let Some(parent) = declaration_record.parent {
        let namespace_block = NodeRef::new(declaration.arena, declaration.file, parent);
        let namespace_block_record = checked_node(arena, bound, store, namespace_block)?;
        let NodeData::ModuleBlock(namespace_block_data) = &namespace_block_record.data else {
            return Ok(false);
        };
        let Some(namespace_node) = namespace_block_record.parent else {
            return Ok(false);
        };
        let namespace = NodeRef::new(declaration.arena, declaration.file, namespace_node);
        let namespace_record = checked_node(arena, bound, store, namespace)?;
        let NodeData::ModuleDeclaration(namespace_data) = &namespace_record.data else {
            return Ok(false);
        };
        namespace_block_record.kind == SyntaxKind::ModuleBlock
            && namespace_record.kind == SyntaxKind::ModuleDeclaration
            && namespace_data.body == Some(namespace_block.node)
            && bound.symbol(namespace) == Some(module)
            && module_record.declarations() == Some(&[namespace])
            && valid_imported_namespace_declaration(arena, bound, store, namespace, module)?
            && namespace_block_data
                .statements
                .nodes
                .iter()
                .filter(|node| **node == declaration.node)
                .count()
                == 1
    } else {
        false
    };
    Ok(facts.is_external_module()
        && !facts.is_declaration_file()
        && !facts.is_javascript_file()
        && valid_container
        && bound.symbol(declaration) == Some(callable.owner_symbol)
        && owner.flags() == SymbolFlags::FUNCTION
        && owner.parent() == Some(module)
        && owner.name().as_bytes() == name_text.as_bytes()
        && module_record
            .exports()
            .and_then(|exports| store.symbol_table(exports))
            .and_then(|exports| exports.get(owner.name()))
            == Some(callable.owner_symbol)
        && declaration_record.kind == SyntaxKind::FunctionDeclaration
        && declaration_record.flags.0 == 0
        && function.parameters.nodes.is_empty()
        && !function.parameters.has_trailing_comma
        && function.type_parameters.is_none()
        && function.type_.is_none()
        && function.body == Some(body.node)
        && function.facts == 0
        && has_exact_modifier_sequence(
            arena,
            bound,
            store,
            declaration,
            function.modifiers.as_ref(),
            &[(SyntaxKind::ExportKeyword, "export")],
        )?
        && callable.family == SourceCallableFamily::FunctionDeclaration
        && callable.owner_parent == Some(module)
        && callable.export_local.is_some()
        && callable.type_parameters.is_empty()
        && callable.parameters.is_empty()
        && callable.return_type.is_inferred()
        && !callable.body_mode.is_ambient()
        && callable.flags == super::signatures::SignatureFlags::NONE
        && callable.min_argument_count == 0
        && body_record.kind == SyntaxKind::Block
        && body_record.parent == Some(declaration.node)
        && body_record.flags.0 == 0
        && block.flow_node.is_none()
        && block.next_container.is_none()
        && block.statements.nodes.is_empty()
        && !block.statements.has_trailing_comma
        && block.facts == 0)
}

fn plan_direct_typescript_const_target(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    global_types: &CanonicalGlobalTypes,
    alias: SemanticSymbolId,
    target: SemanticSymbolId,
) -> Result<PlannedSourceImportValueTarget, SourceImportError> {
    let target_record = store
        .symbol(target)
        .ok_or_else(|| invariant(SourceImportInvariant::InvalidTargetSymbol(target)))?;
    if target_record.flags() != SymbolFlags::BLOCK_SCOPED_VARIABLE {
        return Err(unsupported(SourceImportUnsupported::TargetSymbol {
            alias,
            target,
            flags: target_record.flags(),
        }));
    }
    let Some([declaration]) = target_record.declarations() else {
        return Err(unsupported(SourceImportUnsupported::TargetSymbol {
            alias,
            target,
            flags: target_record.flags(),
        }));
    };
    let declaration = *declaration;
    if target_record.value_declaration() != Some(declaration) {
        return Err(invariant(SourceImportInvariant::InvalidTargetSymbol(
            target,
        )));
    }
    let (arena, bound) = host
        .source(declaration)
        .ok_or_else(|| unsupported(SourceImportUnsupported::TargetDeclaration(declaration)))?;
    let facts = bound.source_facts().ok_or_else(|| {
        invariant(SourceImportInvariant::MissingSourceFacts(
            bound.source_file(),
        ))
    })?;
    if facts.is_javascript_file() || facts.is_common_js_module() || !facts.is_external_module() {
        return Err(unsupported(SourceImportUnsupported::TargetDeclaration(
            declaration,
        )));
    }
    let record = checked_node(arena, bound, store, declaration)?;
    let NodeData::VariableDeclaration(variable) = &record.data else {
        return Err(unsupported(SourceImportUnsupported::TargetDeclaration(
            declaration,
        )));
    };
    if record.kind != SyntaxKind::VariableDeclaration
        || record.flags.0 != 0
        || variable.exclamation_token.is_some()
        || variable.local_symbol.is_some()
        || variable.symbol.is_some()
        || variable.facts != 0
    {
        return Err(unsupported(SourceImportUnsupported::TargetDeclaration(
            declaration,
        )));
    }

    let name = NodeRef::new(declaration.arena, declaration.file, variable.name);
    let name_record = checked_node(arena, bound, store, name)?;
    let NodeData::Identifier(identifier) = &name_record.data else {
        return Err(unsupported(SourceImportUnsupported::TargetDeclaration(
            name,
        )));
    };
    if name_record.kind != SyntaxKind::Identifier
        || name_record.parent != Some(declaration.node)
        || name_record.flags.0 != 0
        || identifier.flow_node.is_some()
        || identifier.text.is_empty()
    {
        return Err(unsupported(SourceImportUnsupported::TargetDeclaration(
            name,
        )));
    }
    if identifier.text.as_bytes() != target_record.name().as_bytes() {
        return Err(invariant(SourceImportInvariant::TargetNameMismatch {
            target,
            name,
        }));
    }

    let list = record
        .parent
        .map(|node| NodeRef::new(declaration.arena, declaration.file, node))
        .ok_or_else(|| unsupported(SourceImportUnsupported::TargetNotExportedConst(declaration)))?;
    let list_record = checked_node(arena, bound, store, list)?;
    let NodeData::VariableDeclarationList(list_data) = &list_record.data else {
        return Err(unsupported(
            SourceImportUnsupported::TargetNotExportedConst(declaration),
        ));
    };
    if list_record.kind != SyntaxKind::VariableDeclarationList
        || list_record.flags.0 != NODE_FLAG_CONST
        || list_data.facts != 0
        || !list_data.declarations.nodes.contains(&declaration.node)
        || (facts.is_declaration_file()
            && list_data.declarations.nodes.as_slice() != [declaration.node])
    {
        return Err(unsupported(
            SourceImportUnsupported::TargetNotExportedConst(declaration),
        ));
    }
    let statement = list_record
        .parent
        .map(|node| NodeRef::new(declaration.arena, declaration.file, node))
        .ok_or_else(|| unsupported(SourceImportUnsupported::TargetNotExportedConst(declaration)))?;
    let statement_record = checked_node(arena, bound, store, statement)?;
    let NodeData::VariableStatement(statement_data) = &statement_record.data else {
        return Err(unsupported(
            SourceImportUnsupported::TargetNotExportedConst(declaration),
        ));
    };
    let inferred_declaration_literal =
        facts.is_declaration_file() && variable.type_.is_none() && variable.initializer.is_some();
    let has_exact_export_modifiers = if inferred_declaration_literal {
        has_exact_export_modifier(
            arena,
            bound,
            store,
            statement,
            statement_data.modifiers.as_ref(),
        )?
    } else if facts.is_declaration_file() {
        has_exact_export_declare_modifiers(
            arena,
            bound,
            store,
            statement,
            statement_data.modifiers.as_ref(),
        )?
    } else {
        has_exact_export_modifier(
            arena,
            bound,
            store,
            statement,
            statement_data.modifiers.as_ref(),
        )?
    };
    if statement_record.kind != SyntaxKind::VariableStatement
        || statement_record.parent != Some(bound.source_file().node)
        || statement_record.flags.0 != 0
        || statement_data.declaration_list != list.node
        || statement_data.flow_node.is_some()
        || statement_data.facts != 0
        || !has_exact_export_modifiers
    {
        return Err(unsupported(
            SourceImportUnsupported::TargetNotExportedConst(declaration),
        ));
    }
    let source_record = checked_node(arena, bound, store, bound.source_file())?;
    let NodeData::SourceFile(source_data) = &source_record.data else {
        return Err(invariant(SourceImportInvariant::InvalidSource(
            bound.source_file(),
        )));
    };
    if source_data
        .statements
        .nodes
        .iter()
        .filter(|node| **node == statement.node)
        .count()
        != 1
    {
        return Err(unsupported(
            SourceImportUnsupported::TargetNotExportedConst(declaration),
        ));
    }

    plan_top_level_variable(
        bound,
        store,
        declaration,
        name,
        &identifier.text,
        VariableBindingKind::Const,
        true,
    )?;
    if inferred_declaration_literal {
        let initializer = NodeRef::new(
            declaration.arena,
            declaration.file,
            variable
                .initializer
                .expect("inferred declaration literal has an initializer"),
        );
        let initializer_record = checked_node(arena, bound, store, initializer)?;
        let NodeData::NumericLiteral(literal) = &initializer_record.data else {
            return Err(unsupported(SourceImportUnsupported::TargetDeclaration(
                initializer,
            )));
        };
        if initializer_record.kind != SyntaxKind::NumericLiteral
            || initializer_record.parent != Some(declaration.node)
            || initializer_record.flags.0 != 0
            || literal.token_flags.0 != 0
            || literal.text.is_empty()
            || !literal.text.bytes().all(|byte| byte.is_ascii_digit())
            || !source_spelling_matches(arena, initializer_record, &literal.text)
            || !ts_jsnum::from_string(&literal.text).value().is_finite()
        {
            return Err(unsupported(SourceImportUnsupported::TargetDeclaration(
                initializer,
            )));
        }
        return Ok(PlannedSourceImportValueTarget::DeclarationNumericConst {
            declaration,
            initializer,
            literal: literal.text.clone(),
        });
    }
    if !facts.is_declaration_file() && variable.type_.is_none() {
        let expression = variable
            .initializer
            .map(|node| NodeRef::new(declaration.arena, declaration.file, node))
            .ok_or_else(|| {
                unsupported(SourceImportUnsupported::MissingTargetInitializer(
                    declaration,
                ))
            })?;
        let expression_record = checked_node(arena, bound, store, expression)?;
        let NodeData::ObjectLiteralExpression(object) = &expression_record.data else {
            return Err(unsupported(
                SourceImportUnsupported::MissingTargetAnnotation(declaration),
            ));
        };
        if expression_record.kind != SyntaxKind::ObjectLiteralExpression
            || expression_record.flags.0 != 0
            || expression_record.parent != Some(declaration.node)
            || object.symbol.is_some()
            || object.facts != 0
        {
            return Err(unsupported(SourceImportUnsupported::TargetDeclaration(
                expression,
            )));
        }
        let expression_type = store
            .type_node_links(expression)
            .and_then(|links| {
                (links
                    == &TypeNodeLinks {
                        resolved_type: links.resolved_type,
                        ..TypeNodeLinks::default()
                    })
                    .then_some(links.resolved_type)
                    .flatten()
            })
            .ok_or_else(|| {
                unsupported(SourceImportUnsupported::MissingTargetAnnotation(
                    declaration,
                ))
            })?;
        let type_ = store
            .value_symbol_links(target)
            .and_then(|links| links.resolved_type)
            .ok_or_else(|| {
                unsupported(SourceImportUnsupported::MissingTargetAnnotation(
                    declaration,
                ))
            })?;
        if !published_object_const_type_is_exact(store, global_types, expression_type, type_) {
            return Err(invariant(SourceImportInvariant::InvalidTargetLinks(target)));
        }
        return Ok(PlannedSourceImportValueTarget::PublishedObjectConst {
            declaration,
            expression,
            expression_type,
            type_,
        });
    }
    let type_node = variable
        .type_
        .map(|node| NodeRef::new(declaration.arena, declaration.file, node))
        .ok_or_else(|| {
            unsupported(SourceImportUnsupported::MissingTargetAnnotation(
                declaration,
            ))
        })?;
    if checked_node(arena, bound, store, type_node)?.parent != Some(declaration.node) {
        return Err(unsupported(SourceImportUnsupported::TargetDeclaration(
            type_node,
        )));
    }
    match (facts.is_declaration_file(), variable.initializer) {
        (true, None) => {}
        (true, Some(initializer)) => {
            return Err(unsupported(
                SourceImportUnsupported::UnexpectedTargetInitializer(NodeRef::new(
                    declaration.arena,
                    declaration.file,
                    initializer,
                )),
            ));
        }
        (false, None) => {
            return Err(unsupported(
                SourceImportUnsupported::MissingTargetInitializer(declaration),
            ));
        }
        (false, Some(initializer)) => {
            let initializer = NodeRef::new(declaration.arena, declaration.file, initializer);
            if checked_node(arena, bound, store, initializer)?.parent != Some(declaration.node) {
                return Err(unsupported(SourceImportUnsupported::TargetDeclaration(
                    initializer,
                )));
            }
        }
    }
    Ok(PlannedSourceImportValueTarget::AnnotatedConst {
        declaration,
        type_node,
    })
}

fn published_object_const_type_is_exact(
    store: &CanonicalTypeMapperStore,
    global_types: &CanonicalGlobalTypes,
    expression_type: TypeId,
    value_type: TypeId,
) -> bool {
    let Some(expression) = store.type_payload(expression_type) else {
        return false;
    };
    if expression.flags() != TypeFlags::OBJECT
        || !expression
            .object_flags()
            .contains(ObjectFlags::OBJECT_LITERAL | ObjectFlags::MEMBERS_RESOLVED)
    {
        return false;
    }
    if expression_type == value_type {
        return true;
    }
    let DerivedObjectLiteralValidation::Valid { source, .. } =
        store.validate_derived_object_literal_with_global_types(value_type, global_types)
    else {
        return false;
    };
    source == expression_type
        || matches!(
            store.validate_derived_object_literal_with_global_types(source, global_types),
            DerivedObjectLiteralValidation::Valid { source, .. } if source == expression_type
        )
}

fn declaration_numeric_literal_type(
    store: &mut CanonicalTypeMapperStore,
    target: SemanticSymbolId,
    literal: &str,
) -> Result<TypeId, SourceImportError> {
    let regular = store
        .regular_number_literal_type(ts_jsnum::from_string(literal))
        .map_err(|_| invariant(SourceImportInvariant::InvalidTargetLinks(target)))?;
    store
        .fresh_type_of_literal_type(regular)
        .map_err(|_| invariant(SourceImportInvariant::InvalidTargetLinks(target)))
}

fn has_exact_export_modifier(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    statement: NodeRef,
    modifiers: Option<&ts_ast::ModifierList>,
) -> Result<bool, SourceImportError> {
    let Some(modifiers) = modifiers else {
        return Ok(false);
    };
    let [modifier] = modifiers.list.nodes.as_slice() else {
        return Ok(false);
    };
    let modifier = NodeRef::new(statement.arena, statement.file, *modifier);
    let record = checked_node(arena, bound, store, modifier)?;
    Ok(modifiers.flags.0 == 0
        && !modifiers.list.has_trailing_comma
        && record.kind == SyntaxKind::ExportKeyword
        && matches!(&record.data, NodeData::Token(_))
        && record.flags.0 == 0
        && record.parent == Some(statement.node))
}

fn has_exact_export_declare_modifiers(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    statement: NodeRef,
    modifiers: Option<&ts_ast::ModifierList>,
) -> Result<bool, SourceImportError> {
    has_exact_modifier_sequence(
        arena,
        bound,
        store,
        statement,
        modifiers,
        &[
            (SyntaxKind::ExportKeyword, "export"),
            (SyntaxKind::DeclareKeyword, "declare"),
        ],
    )
}

fn has_exact_modifier_sequence(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    statement: NodeRef,
    modifiers: Option<&ts_ast::ModifierList>,
    expected: &[(SyntaxKind, &str)],
) -> Result<bool, SourceImportError> {
    let Some(modifiers) = modifiers else {
        return Ok(false);
    };
    if modifiers.flags.0 != 0
        || modifiers.list.has_trailing_comma
        || modifiers.list.nodes.len() != expected.len()
    {
        return Ok(false);
    }
    let statement_record = checked_node(arena, bound, store, statement)?;
    if modifiers.list.range.start != statement_record.range.start
        || modifiers.list.range.end.get() > statement_record.range.end.get()
    {
        return Ok(false);
    }
    let mut previous_end = None;
    for (index, (&modifier, &(expected_kind, expected_spelling))) in
        modifiers.list.nodes.iter().zip(expected).enumerate()
    {
        let modifier = NodeRef::new(statement.arena, statement.file, modifier);
        let record = checked_node(arena, bound, store, modifier)?;
        if record.kind != expected_kind
            || !matches!(&record.data, NodeData::Token(_))
            || record.flags.0 != 0
            || record.parent != Some(statement.node)
            || !range_contains(statement_record, record)
            || (index == 0 && record.range.start != statement_record.range.start)
            || previous_end.is_some_and(|end| end > record.range.start.get())
            || !source_spelling_matches(arena, record, expected_spelling)
        {
            return Ok(false);
        }
        previous_end = Some(record.range.end.get());
    }
    Ok(true)
}

fn source_spelling_matches(arena: &NodeArena, node: &Node, expected: &str) -> bool {
    let Some(source) = arena.source_text() else {
        return true;
    };
    source.get(node.range.start.get() as usize..node.range.end.get() as usize) == Some(expected)
}

fn prepare_value_links(
    store: &CanonicalTypeMapperStore,
    symbol: SemanticSymbolId,
    type_: TypeId,
    alias: bool,
) -> Result<ValueSymbolLinks, SourceImportError> {
    let record = store.symbol(symbol).ok_or_else(|| {
        invariant(if alias {
            SourceImportInvariant::InvalidAliasSymbol(symbol)
        } else {
            SourceImportInvariant::InvalidTargetSymbol(symbol)
        })
    })?;
    if (alias && record.flags() != SymbolFlags::ALIAS)
        || (!alias
            && record.flags() != SymbolFlags::BLOCK_SCOPED_VARIABLE
            && record.flags() != SymbolFlags::FUNCTION_SCOPED_VARIABLE
            && record.flags() != SymbolFlags::FUNCTION
            && record.flags() != SymbolFlags::CONST_ENUM
            && record.flags() != SymbolFlags::PROPERTY
            && !record.flags().intersects(SymbolFlags::MODULE))
        || store.type_payload(type_).is_none()
    {
        return Err(invariant(if alias {
            SourceImportInvariant::InvalidAliasValueLinks(symbol)
        } else {
            SourceImportInvariant::InvalidTargetLinks(symbol)
        }));
    }
    let mut links = store
        .value_symbol_links(symbol)
        .cloned()
        .unwrap_or_default();
    if links.write_type.is_some()
        || links.target.is_some()
        || links.mapper.is_some()
        || links.name_type.is_some()
        || links.containing_type.is_some()
        || links.function_or_constructor_checked
    {
        return Err(invariant(if alias {
            SourceImportInvariant::InvalidAliasValueLinks(symbol)
        } else {
            SourceImportInvariant::InvalidTargetLinks(symbol)
        }));
    }
    if let Some(cached) = links.resolved_type
        && cached != type_
    {
        return Err(invariant(SourceImportInvariant::CachedTypeMismatch {
            symbol,
            cached,
            expected: type_,
        }));
    }
    links.resolved_type = Some(type_);
    Ok(links)
}

fn validate_prepared_import_value(
    store: &CanonicalTypeMapperStore,
    prepared: &PreparedSourceImportValue,
) -> Result<(), SourceImportError> {
    validate_alias_symbol(
        store,
        prepared.binding.alias_symbol,
        prepared.binding.declaration,
        prepared.binding.local_name,
        &prepared.binding.local_text,
    )?;
    let alias_links = store
        .alias_symbol_links(prepared.binding.alias_symbol)
        .ok_or_else(|| {
            invariant(SourceImportInvariant::InvalidAliasLinks(
                prepared.binding.alias_symbol,
            ))
        })?;
    let target_valid = match &prepared.target {
        PreparedSourceImportTarget::AnnotatedConst {
            type_node,
            type_links,
        } => {
            store.symbol(prepared.target_symbol).is_some_and(|target| {
                target.flags() == SymbolFlags::BLOCK_SCOPED_VARIABLE
                    && target.value_declaration() == Some(prepared.target_declaration)
            }) && store.type_node_links(*type_node) == type_links.as_ref()
        }
        PreparedSourceImportTarget::DeclarationNumericConst {
            initializer,
            literal,
        } => {
            let cached_type = store
                .intrinsic_bootstrap()
                .and_then(|bootstrap| {
                    bootstrap.cached_number_literal_type(ts_jsnum::from_string(literal))
                })
                .and_then(|regular| store.fresh_type_of_literal_type(regular).ok());
            store.symbol(prepared.target_symbol).is_some_and(|target| {
                target.flags() == SymbolFlags::BLOCK_SCOPED_VARIABLE
                    && target.value_declaration() == Some(prepared.target_declaration)
            }) && store.source_node_kind(*initializer) == Some(SyntaxKind::NumericLiteral)
                && store.source_node_parent(*initializer)
                    == Some(SourceNodeParent::Parent(prepared.target_declaration))
                && cached_type == Some(prepared.type_)
        }
        PreparedSourceImportTarget::AnnotatedFunction { signature } => {
            store.symbol(prepared.target_symbol).is_some_and(|target| {
                target.flags() == SymbolFlags::FUNCTION
                    && target.value_declaration() == Some(prepared.target_declaration)
            }) && store.source_callable_type_for_owner(prepared.target_symbol)
                == Some(prepared.type_)
                && store
                    .source_callable_provenance(prepared.type_)
                    .is_some_and(|provenance| {
                        provenance.family == SourceCallableFamily::FunctionDeclaration
                            && provenance.declaration == prepared.target_declaration
                            && provenance.owner_symbol == prepared.target_symbol
                            && provenance.signature == *signature
                    })
                && store
                    .signature(*signature)
                    .is_some_and(|signature| signature.resolved_return_type().is_some())
                && matches!(
                    validate_stored_source_callable(store, prepared.type_),
                    StoredSourceCallableValidation::Valid(_)
                )
        }
        PreparedSourceImportTarget::ConstEnum { declared_type } => {
            store.symbol(prepared.target_symbol).is_some_and(|target| {
                target.flags() == SymbolFlags::CONST_ENUM
                    && target.value_declaration() == Some(prepared.target_declaration)
            }) && store
                .declared_type_links(prepared.target_symbol)
                .and_then(|links| links.declared_type)
                == Some(*declared_type)
                && enums::canonical_enum_type_owner(store, *declared_type)
                    == Some(prepared.target_symbol)
                && store
                    .value_symbol_links(prepared.target_symbol)
                    .and_then(|links| links.resolved_type)
                    == Some(prepared.type_)
                && store
                    .type_payload(prepared.type_)
                    .is_some_and(|record| record.symbol() == Some(prepared.target_symbol))
        }
        PreparedSourceImportTarget::ExportedObject { expression } => {
            store.symbol(prepared.target_symbol).is_some_and(|target| {
                (target.flags() == SymbolFlags::PROPERTY
                    || target.flags() == SymbolFlags::PROPERTY | SymbolFlags::NAMESPACE_MODULE)
                    && target.declarations() == Some(&[prepared.target_declaration])
                    && target.value_declaration() == Some(prepared.target_declaration)
            }) && store.source_node_kind(prepared.target_declaration)
                == Some(SyntaxKind::ExportAssignment)
                && store.source_node_kind(*expression) == Some(SyntaxKind::ObjectLiteralExpression)
                && store.source_node_parent(*expression)
                    == Some(SourceNodeParent::Parent(prepared.target_declaration))
                && store
                    .value_symbol_links(prepared.target_symbol)
                    .and_then(|links| links.resolved_type)
                    == Some(prepared.type_)
                && store
                    .type_node_links(*expression)
                    .and_then(|links| links.resolved_type)
                    == Some(prepared.type_)
        }
        PreparedSourceImportTarget::PublishedObjectConst {
            expression,
            expression_type,
        } => {
            store.symbol(prepared.target_symbol).is_some_and(|target| {
                target.flags() == SymbolFlags::BLOCK_SCOPED_VARIABLE
                    && target.check_flags() == CheckFlags::NONE
                    && target.declarations() == Some(&[prepared.target_declaration])
                    && target.value_declaration() == Some(prepared.target_declaration)
            }) && store.source_node_kind(prepared.target_declaration)
                == Some(SyntaxKind::VariableDeclaration)
                && store.source_node_kind(*expression) == Some(SyntaxKind::ObjectLiteralExpression)
                && store.source_node_parent(*expression)
                    == Some(SourceNodeParent::Parent(prepared.target_declaration))
                && store
                    .type_node_links(*expression)
                    .and_then(|links| links.resolved_type)
                    == Some(*expression_type)
                && store
                    .value_symbol_links(prepared.target_symbol)
                    .and_then(|links| links.resolved_type)
                    == Some(prepared.type_)
                && (prepared.type_ == *expression_type
                    || matches!(
                        store.validate_derived_object_literal_for_relation(prepared.type_),
                        DerivedObjectLiteralValidation::Valid { source, .. }
                            if source == *expression_type
                                || matches!(
                                    store.validate_derived_object_literal_for_relation(source),
                                    DerivedObjectLiteralValidation::Valid { source, .. }
                                        if source == *expression_type
                                )
                    ))
        }
        PreparedSourceImportTarget::JavaScriptAnnotatedConst { annotation } => {
            let valid_target = store.symbol(prepared.target_symbol).is_some_and(|target| {
                (target.flags() == SymbolFlags::BLOCK_SCOPED_VARIABLE
                    || target.flags() == SymbolFlags::FUNCTION_SCOPED_VARIABLE
                        && target.check_flags() == CheckFlags::NONE
                        && target.declarations() == Some(&[prepared.target_declaration])
                        && target.parent().is_none()
                        && target.members().is_none()
                        && target.exports().is_none()
                        && target.export_symbol().is_none()
                        && store.get_merged_symbol(prepared.target_symbol)
                            == Some(prepared.target_symbol))
                    && target.value_declaration() == Some(prepared.target_declaration)
                    && store.source_node_kind(prepared.target_declaration)
                        == Some(SyntaxKind::VariableDeclaration)
            });
            valid_target
                && (annotation.is_some()
                    || store
                        .value_symbol_links(prepared.target_symbol)
                        .and_then(|links| links.resolved_type)
                        == Some(prepared.type_))
        }
        PreparedSourceImportTarget::CommonJsNamedExport { assignments } => {
            let valid_target = store.symbol(prepared.target_symbol).is_some_and(|target| {
                target.flags() == SymbolFlags::FUNCTION_SCOPED_VARIABLE
                    && target.check_flags() == CheckFlags::NONE
                    && target.declarations().is_some_and(|declarations| {
                        !declarations.is_empty()
                            && declarations.len() == assignments.len()
                            && declarations.contains(&prepared.target_declaration)
                            && declarations.iter().zip(assignments).all(
                                |(declaration, assignment)| {
                                    *declaration == assignment.expression
                                        && declaration.arena == prepared.target_declaration.arena
                                        && declaration.file == prepared.target_declaration.file
                                        && store.source_node_kind(*declaration)
                                            == Some(SyntaxKind::BinaryExpression)
                                        && store.source_node_parent(assignment.left)
                                            == Some(SourceNodeParent::Parent(*declaration))
                                        && store.source_node_parent(assignment.right)
                                            == Some(SourceNodeParent::Parent(*declaration))
                                },
                            )
                    })
                    && target.value_declaration() == Some(prepared.target_declaration)
                    && target.members().is_none()
                    && target.exports().is_none()
                    && target.export_symbol().is_none()
                    && store.get_merged_symbol(prepared.target_symbol)
                        == Some(prepared.target_symbol)
                    && target.parent().is_some_and(|module| {
                        store.symbol(module).is_some_and(|module_record| {
                            module_record.flags() == SymbolFlags::VALUE_MODULE
                                && module_record
                                    .exports()
                                    .and_then(|exports| store.symbol_table(exports))
                                    .and_then(|exports| exports.get(target.name()))
                                    == Some(prepared.target_symbol)
                        })
                    })
            });
            valid_target
                && store.source_node_kind(prepared.target_declaration)
                    == Some(SyntaxKind::BinaryExpression)
                && {
                    let symbol_type = store
                        .value_symbol_links(prepared.target_symbol)
                        .and_then(|links| links.resolved_type);
                    let mut assignment_type = None;
                    assignments.iter().copied().all(|assignment| {
                        let Ok(cached) = validate_commonjs_named_export_assignment_cache(
                            store,
                            prepared.target_symbol,
                            assignment,
                            symbol_type,
                        ) else {
                            return false;
                        };
                        if assignment.expression == prepared.target_declaration {
                            assignment_type = cached;
                        }
                        true
                    }) && symbol_type
                        .or(assignment_type)
                        .is_some_and(|type_| type_ == prepared.type_)
                        && (assignments.len() == 1 || symbol_type == Some(prepared.type_))
                }
        }
        PreparedSourceImportTarget::ModuleNamespace { properties } => {
            valid_prepared_imported_namespace(
                store,
                Some(prepared.binding.alias_symbol),
                prepared.target_symbol,
                prepared.target_declaration,
                prepared.type_,
                properties,
            )
        }
    };
    if alias_links.immediate_target != Some(prepared.immediate_target_symbol)
        || alias_links.alias_target != AliasTargetState::Resolved(prepared.target_symbol)
        || alias_links.type_only_declaration.is_some()
        || !target_valid
    {
        return Err(invariant(SourceImportInvariant::PreparedStateChanged(
            prepared.binding.alias_symbol,
        )));
    }
    if prepare_value_links(store, prepared.target_symbol, prepared.type_, false)?
        != prepared.target_links
        || prepare_value_links(store, prepared.binding.alias_symbol, prepared.type_, true)?
            != prepared.alias_links
    {
        return Err(invariant(SourceImportInvariant::PreparedStateChanged(
            prepared.binding.alias_symbol,
        )));
    }
    Ok(())
}

fn valid_prepared_imported_namespace(
    store: &CanonicalTypeMapperStore,
    import_alias: Option<SemanticSymbolId>,
    module: SemanticSymbolId,
    declaration: NodeRef,
    type_: TypeId,
    properties: &[PreparedSourceImportModuleProperty],
) -> bool {
    let Some(target) = store.symbol(module) else {
        return false;
    };
    let Some(record) = store.type_payload(type_) else {
        return false;
    };
    let Some(structured) = record.data().structured() else {
        return false;
    };
    let exports = store
        .module_symbol_links(module)
        .and_then(|links| links.resolved_exports)
        .or_else(|| target.exports())
        .and_then(|exports| store.symbol_table(exports));
    let symbols = structured.properties.as_deref().unwrap_or_default();
    let members = structured
        .members
        .and_then(|members| store.symbol_table(members));
    let owner =
        (store.source_node_kind(declaration) == Some(SyntaxKind::SourceFile)).then_some(module);
    let synthetic = if store.export_type_links(module).is_some() {
        let Some(alias) = import_alias else {
            return false;
        };
        let Ok(authenticated) =
            authenticate_synthetic_import_namespace_identity(store, alias, module)
        else {
            return false;
        };
        if authenticated.function != declaration {
            return false;
        }
        Some(authenticated)
    } else {
        None
    };
    target.flags().intersects(SymbolFlags::MODULE)
        && target.flags().intersects(SymbolFlags::VALUE)
        && (synthetic.is_some() || target.declarations() == Some(&[declaration]))
        && exports.is_some()
        && record.symbol() == owner
        && record.object_flags() == ObjectFlags::ANONYMOUS | ObjectFlags::MEMBERS_RESOLVED
        && structured.call_signature_count == 0
        && structured.signatures.is_none()
        && symbols.len() == properties.len()
        && members.map_or(0, ts_binder::semantic::SymbolTable::len) == properties.len()
        && properties.iter().all(|property| {
            symbols.contains(&property.symbol)
                && members.and_then(|members| members.get(property.name.as_ref()))
                    == Some(property.symbol)
                && exports.and_then(|exports| exports.get(property.name.as_ref()))
                    == Some(property.target_symbol)
                && store.symbol(property.symbol).is_some_and(|record| {
                    record.flags() == SymbolFlags::PROPERTY
                        && record.name() == property.name.as_ref()
                        && record.parent().is_none()
                        && record.declarations().is_none()
                })
                && store
                    .value_symbol_links(property.symbol)
                    .is_some_and(|links| {
                        links.resolved_type == Some(property.type_)
                            && links.target == owner.map(|_| property.target_symbol)
                    })
                && store.symbol(property.target_symbol).is_some_and(|target| {
                    if target.flags() == SymbolFlags::ALIAS {
                        store
                            .alias_symbol_links(property.target_symbol)
                            .is_some_and(|links| {
                                links.alias_target
                                    == AliasTargetState::Resolved(property.value_symbol)
                                    && links.type_only_declaration.is_none()
                            })
                    } else {
                        property.target_symbol == property.value_symbol
                    }
                })
                && store
                    .value_symbol_links(property.value_symbol)
                    .and_then(|links| links.resolved_type)
                    .is_none_or(|cached| cached == property.type_)
                && match &property.namespace {
                    Some(namespace) => {
                        prepare_value_links(store, property.value_symbol, property.type_, false)
                            .is_ok_and(|links| links == namespace.links)
                            && valid_prepared_imported_namespace(
                                store,
                                None,
                                property.value_symbol,
                                namespace.declaration,
                                property.type_,
                                &namespace.properties,
                            )
                    }
                    None => {
                        synthetic.is_some_and(|authenticated| {
                            property.name.as_ref() == InternalSymbolName::Default.as_ref()
                                && property.target_symbol == authenticated.default
                                && property.value_symbol == authenticated.original
                        }) || store
                            .symbol(property.value_symbol)
                            .is_some_and(|value| !value.flags().intersects(SymbolFlags::MODULE))
                    }
                }
        })
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;

    use ts_ast::{FileId, NodeFlags, NodeId};
    use ts_binder::{
        CanonicalBinder, CanonicalModuleState, CanonicalNameResolverOptions,
        CanonicalSourceFileFacts, CanonicalSourceLanguage, EscapedName,
    };
    use ts_parser::{ParseResult, parse_javascript_source_file, parse_source_file};

    use super::*;
    use crate::semantic::{
        AliasSymbolLinks, CanonicalTypeFormatFlags, IntrinsicBootstrapOptions, SymbolNodeLinks,
        TypeAliasLinks,
        alias::CanonicalAliasTargetUnavailable,
        bootstrap::UnionReduction,
        formatter::type_to_string_with_host_global_types_and_flags,
        global_types::initialize_global_library_types,
        instantiate::InstantiationLimits,
        jsdoc::JsDocType,
        module_resolution::{
            CanonicalModuleResolutionEntry, CanonicalModuleResolutionManifest,
            CanonicalModuleResolutionManifestInput, CanonicalModuleResolutionMode,
            CanonicalResolvedModuleInput, validate_module_resolution_manifest,
        },
        production::GlobalMergeCompletion,
    };

    #[derive(Clone, Copy)]
    struct Route {
        source: usize,
        specifier: usize,
        target: Option<usize>,
    }

    struct FixtureFile {
        file: FileId,
        parsed: ParseResult,
    }

    struct Fixture {
        files: Vec<FixtureFile>,
        bound: BTreeMap<FileId, BoundFile>,
        manifest: CanonicalModuleResolutionManifest,
        global_types: CanonicalGlobalTypes,
        store: CanonicalTypeMapperStore,
    }

    #[derive(Clone, Copy)]
    enum JsDocImportManifestState {
        Resolved,
        Unresolved,
        Absent,
    }

    impl Fixture {
        fn plan_import(&self, source: usize, import: usize) -> SourceImportPlan {
            let file = &self.files[source];
            let bound = self.bound.get(&file.file).unwrap();
            let declaration = file
                .parsed
                .arena
                .iter()
                .filter_map(|(node, record)| {
                    (record.kind == SyntaxKind::ImportDeclaration).then_some(node)
                })
                .nth(import)
                .expect("fixture contains requested import");
            plan_top_level_named_value_import(
                &file.parsed.arena,
                bound,
                &self.store,
                NodeRef::new(file.parsed.arena.id(), file.file, declaration),
            )
            .unwrap()
        }

        fn try_plan_import_equals(
            &self,
            source: usize,
            import: usize,
        ) -> Result<SourceImportPlan, SourceImportError> {
            let file = &self.files[source];
            let bound = self.bound.get(&file.file).unwrap();
            let declaration = file
                .parsed
                .arena
                .iter()
                .filter_map(|(node, record)| {
                    (record.kind == SyntaxKind::ImportEqualsDeclaration).then_some(node)
                })
                .nth(import)
                .expect("fixture contains requested import-equals declaration");
            plan_top_level_import_equals(
                &file.parsed.arena,
                bound,
                &self.store,
                NodeRef::new(file.parsed.arena.id(), file.file, declaration),
            )
        }

        fn plan_type_import(&self, source: usize, import: usize) -> SourceImportPlan {
            let file = &self.files[source];
            let bound = self.bound.get(&file.file).unwrap();
            let declaration = file
                .parsed
                .arena
                .iter()
                .filter_map(|(node, record)| {
                    (record.kind == SyntaxKind::ImportDeclaration).then_some(node)
                })
                .nth(import)
                .expect("fixture contains requested import");
            plan_top_level_named_type_import(
                &file.parsed.arena,
                bound,
                &self.store,
                NodeRef::new(file.parsed.arena.id(), file.file, declaration),
            )
            .unwrap()
        }

        fn try_plan_reexport(
            &self,
            source: usize,
            export: usize,
        ) -> Result<SourceNamedReexportPlan, SourceImportError> {
            let file = &self.files[source];
            let bound = self.bound.get(&file.file).unwrap();
            let declaration = file
                .parsed
                .arena
                .iter()
                .filter_map(|(node, record)| {
                    (record.kind == SyntaxKind::ExportDeclaration).then_some(node)
                })
                .nth(export)
                .expect("fixture contains requested export");
            plan_top_level_named_reexport(
                &file.parsed.arena,
                bound,
                &self.store,
                NodeRef::new(file.parsed.arena.id(), file.file, declaration),
            )
        }

        fn plan_reexport(&self, source: usize, export: usize) -> SourceNamedReexportPlan {
            self.try_plan_reexport(source, export).unwrap()
        }
    }

    fn parsed(source: &str) -> ParseResult {
        let parsed = parse_source_file(source);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        parsed
    }

    fn facts(file: FileId, module_state: CanonicalModuleState) -> CanonicalSourceFileFacts {
        facts_with_declaration_flag(file, module_state, false)
    }

    fn facts_with_declaration_flag(
        file: FileId,
        module_state: CanonicalModuleState,
        declaration_file: bool,
    ) -> CanonicalSourceFileFacts {
        CanonicalSourceFileFacts::new(
            EscapedName::source(format!("\"/project/{}.ts\"", file.index())),
            CanonicalSourceLanguage::TypeScript,
            declaration_file,
            module_state,
        )
    }

    fn module_specifiers(parsed: &ParseResult) -> Vec<NodeId> {
        let mut specifiers = parsed
            .arena
            .iter()
            .filter_map(|(_, record)| match &record.data {
                NodeData::ImportDeclaration(import) => Some(import.module_specifier),
                NodeData::ImportEqualsDeclaration(import) => parsed
                    .arena
                    .get(import.module_reference)
                    .and_then(|reference| match &reference.data {
                        NodeData::ExternalModuleReference(reference) => Some(reference.expression),
                        _ => None,
                    }),
                NodeData::ExportDeclaration(export) => export.module_specifier,
                _ => None,
            })
            .collect::<Vec<_>>();
        specifiers.sort_unstable_by_key(|node| parsed.arena.get(*node).unwrap().range.start);
        specifiers
    }

    fn fixture(sources: &[&str], routes: &[Route]) -> Fixture {
        fixture_with_module_states(
            sources,
            routes,
            &vec![CanonicalModuleState::External; sources.len()],
        )
    }

    fn fixture_with_module_states(
        sources: &[&str],
        routes: &[Route],
        module_states: &[CanonicalModuleState],
    ) -> Fixture {
        fixture_with_module_states_and_wrapper_flags(sources, routes, module_states, None, &[])
    }

    fn fixture_with_declaration_files(
        sources: &[&str],
        routes: &[Route],
        declaration_files: &[usize],
    ) -> Fixture {
        fixture_with_module_states_and_wrapper_flags(
            sources,
            routes,
            &vec![CanonicalModuleState::External; sources.len()],
            None,
            declaration_files,
        )
    }

    fn fixture_with_module_states_and_wrapper_flags(
        sources: &[&str],
        routes: &[Route],
        module_states: &[CanonicalModuleState],
        flagged_wrapper: Option<SyntaxKind>,
        declaration_files: &[usize],
    ) -> Fixture {
        assert_eq!(sources.len(), module_states.len());
        let mut files = sources
            .iter()
            .enumerate()
            .map(|(index, source)| {
                let index = u32::try_from(index).expect("fixture file count fits u32");
                FixtureFile {
                    file: FileId::new(700 + index),
                    parsed: parsed(source),
                }
            })
            .collect::<Vec<_>>();
        if let Some(kind) = flagged_wrapper {
            let flagged = files[0]
                .parsed
                .arena
                .iter()
                .find_map(|(node, record)| (record.kind == kind).then_some(node))
                .expect("fixture contains the requested composite wrapper");
            files[0].parsed.arena.get_mut(flagged).unwrap().flags = NodeFlags(1);
        }
        let mut binder = CanonicalBinder::new();
        for (index, (file, module_state)) in
            files.iter().zip(module_states.iter().copied()).enumerate()
        {
            binder
                .bind_source_file_with_facts(
                    &file.parsed.arena,
                    file.parsed.source_file,
                    file.file,
                    facts_with_declaration_flag(
                        file.file,
                        module_state,
                        declaration_files.contains(&index),
                    ),
                )
                .unwrap();
        }
        for file in &files {
            binder
                .bind_typescript_declaration_slice(&file.parsed.arena, file.file)
                .unwrap();
        }
        let (symbols, bound) = binder.finish().try_into_parts().unwrap();
        let entries = routes.iter().map(|route| {
            let source = &files[route.source];
            let specifier = module_specifiers(&source.parsed)[route.specifier];
            let reference = NodeRef::new(source.parsed.arena.id(), source.file, specifier);
            match route.target {
                Some(target) => CanonicalModuleResolutionEntry::resolved(
                    reference,
                    CanonicalResolvedModuleInput::new(
                        files[target].file,
                        CanonicalModuleResolutionMode::Esm,
                        CanonicalModuleResolutionMode::Esm,
                    ),
                ),
                None => CanonicalModuleResolutionEntry::unresolved(reference),
            }
        });
        let manifest = validate_module_resolution_manifest(
            CanonicalModuleResolutionManifestInput::new(entries),
            &symbols,
            files.iter().map(|file| {
                (
                    file.file,
                    &file.parsed.arena,
                    bound.get(&file.file).unwrap(),
                )
            }),
        )
        .unwrap();
        let mut store = CanonicalTypeMapperStore::from_symbol_store(symbols);
        for file in &files {
            assert!(
                store
                    .register_source_file(&file.parsed.arena, file.parsed.source_file, file.file)
                    .is_some()
            );
        }
        store
            .initialize_intrinsic_bootstrap(IntrinsicBootstrapOptions::default())
            .unwrap();
        let globals = store.intrinsic_bootstrap().unwrap().globals;
        for (file, module_state) in files.iter().zip(module_states.iter().copied()) {
            if module_state != CanonicalModuleState::Script {
                continue;
            }
            let bound = bound.get(&file.file).unwrap();
            let Some(locals) = bound.locals(bound.source_file()) else {
                continue;
            };
            let symbols = store
                .symbol_table(locals)
                .unwrap()
                .iter()
                .map(|(_, symbol)| symbol)
                .collect::<Vec<_>>();
            for symbol in symbols {
                store.merge_global_symbol(globals, symbol).unwrap();
            }
        }
        let sources = || {
            files.iter().map(|file| {
                (
                    &file.parsed.arena,
                    bound.get(&file.file).expect("fixture bound every file"),
                )
            })
        };
        let declared_host = DeclaredTypeHost::new_after_global_merge(
            sources(),
            GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
        )
        .unwrap();
        let global_types =
            initialize_global_library_types(&mut store, &declared_host, globals, false).unwrap();
        Fixture {
            files,
            bound,
            manifest,
            global_types,
            store,
        }
    }

    fn javascript_commonjs_fixture(
        importer: &str,
        javascript: &str,
        typedef_flags: Option<NodeFlags>,
    ) -> Fixture {
        let importer_file = FileId::new(970);
        let target_file = FileId::new(971);
        let mut javascript = parse_javascript_source_file(javascript);
        assert!(
            javascript.diagnostics.is_empty(),
            "{:?}",
            javascript.diagnostics,
        );
        if let Some(flags) = typedef_flags {
            let declaration = javascript
                .arena
                .iter()
                .find_map(|(node, record)| {
                    (record.kind == SyntaxKind::JsTypeAliasDeclaration).then_some(node)
                })
                .expect("fixture contains a parser-owned JavaScript typedef");
            javascript.arena.get_mut(declaration).unwrap().flags = flags;
        }
        let files = vec![
            FixtureFile {
                file: importer_file,
                parsed: parsed(importer),
            },
            FixtureFile {
                file: target_file,
                parsed: javascript,
            },
        ];
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &files[0].parsed.arena,
                files[0].parsed.source_file,
                importer_file,
                facts(importer_file, CanonicalModuleState::External),
            )
            .unwrap();
        binder
            .bind_source_file_with_facts(
                &files[1].parsed.arena,
                files[1].parsed.source_file,
                target_file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source("\"/project/target.js\""),
                    CanonicalSourceLanguage::JavaScript,
                    false,
                    CanonicalModuleState::CommonJs,
                ),
            )
            .unwrap();
        binder
            .bind_typescript_declaration_slice(&files[0].parsed.arena, importer_file)
            .unwrap();
        binder
            .bind_javascript_declaration_slice(&files[1].parsed.arena, target_file)
            .unwrap();
        let (symbols, bound) = binder.finish().try_into_parts().unwrap();
        let entries = module_specifiers(&files[0].parsed)
            .into_iter()
            .map(|specifier| {
                CanonicalModuleResolutionEntry::resolved(
                    NodeRef::new(files[0].parsed.arena.id(), importer_file, specifier),
                    CanonicalResolvedModuleInput::new(
                        target_file,
                        CanonicalModuleResolutionMode::Esm,
                        CanonicalModuleResolutionMode::CommonJs,
                    ),
                )
            });
        let manifest = validate_module_resolution_manifest(
            CanonicalModuleResolutionManifestInput::new(entries),
            &symbols,
            files.iter().map(|file| {
                (
                    file.file,
                    &file.parsed.arena,
                    bound.get(&file.file).unwrap(),
                )
            }),
        )
        .unwrap();
        let mut store = CanonicalTypeMapperStore::from_symbol_store(symbols);
        for file in &files {
            assert!(
                store
                    .register_source_file(&file.parsed.arena, file.parsed.source_file, file.file)
                    .is_some()
            );
        }
        store
            .initialize_intrinsic_bootstrap(IntrinsicBootstrapOptions::default())
            .unwrap();
        let globals = store.intrinsic_bootstrap().unwrap().globals;
        let sources = || {
            files.iter().map(|file| {
                (
                    &file.parsed.arena,
                    bound.get(&file.file).expect("fixture bound every file"),
                )
            })
        };
        let declared_host = DeclaredTypeHost::new_after_global_merge(
            sources(),
            GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
        )
        .unwrap();
        let global_types =
            initialize_global_library_types(&mut store, &declared_host, globals, false).unwrap();
        Fixture {
            files,
            bound,
            manifest,
            global_types,
            store,
        }
    }

    fn javascript_jsdoc_commonjs_fixture(
        importer: &str,
        target: &str,
        resolution: JsDocImportManifestState,
    ) -> Fixture {
        let importer_file = FileId::new(972);
        let target_file = FileId::new(973);
        let files = vec![
            FixtureFile {
                file: importer_file,
                parsed: parse_javascript_source_file(importer),
            },
            FixtureFile {
                file: target_file,
                parsed: parse_javascript_source_file(target),
            },
        ];
        for file in &files {
            assert!(
                file.parsed.diagnostics.is_empty(),
                "{:?}",
                file.parsed.diagnostics
            );
        }

        let mut binder = CanonicalBinder::new();
        for (file, state) in files
            .iter()
            .zip([CanonicalModuleState::Script, CanonicalModuleState::CommonJs])
        {
            binder
                .bind_source_file_with_facts(
                    &file.parsed.arena,
                    file.parsed.source_file,
                    file.file,
                    CanonicalSourceFileFacts::new(
                        EscapedName::source(format!("\"/project/{}.js\"", file.file.index())),
                        CanonicalSourceLanguage::JavaScript,
                        false,
                        state,
                    ),
                )
                .unwrap();
        }
        for file in &files {
            binder
                .bind_javascript_declaration_slice(&file.parsed.arena, file.file)
                .unwrap();
        }
        let (symbols, bound) = binder.finish().try_into_parts().unwrap();
        let import_type = files[0]
            .parsed
            .arena
            .iter()
            .find_map(|(_, record)| match &record.data {
                NodeData::ImportTypeNode(import) => Some(import.argument),
                _ => None,
            })
            .expect("the importer contains one JSDoc import type");
        let NodeData::LiteralTypeNode(argument) =
            &files[0].parsed.arena.get(import_type).unwrap().data
        else {
            panic!("the JSDoc import must use a literal module argument")
        };
        let specifier = NodeRef::new(files[0].parsed.arena.id(), importer_file, argument.literal);
        let entries = match resolution {
            JsDocImportManifestState::Resolved => {
                vec![CanonicalModuleResolutionEntry::resolved(
                    specifier,
                    CanonicalResolvedModuleInput::new(
                        target_file,
                        CanonicalModuleResolutionMode::Esm,
                        CanonicalModuleResolutionMode::CommonJs,
                    ),
                )]
            }
            JsDocImportManifestState::Unresolved => {
                vec![CanonicalModuleResolutionEntry::unresolved(specifier)]
            }
            JsDocImportManifestState::Absent => Vec::new(),
        };
        let manifest = validate_module_resolution_manifest(
            CanonicalModuleResolutionManifestInput::new(entries),
            &symbols,
            files.iter().map(|file| {
                (
                    file.file,
                    &file.parsed.arena,
                    bound.get(&file.file).unwrap(),
                )
            }),
        )
        .unwrap();
        let mut store = CanonicalTypeMapperStore::from_symbol_store(symbols);
        for file in &files {
            assert!(
                store
                    .register_source_file(&file.parsed.arena, file.parsed.source_file, file.file)
                    .is_some()
            );
        }
        store
            .initialize_intrinsic_bootstrap(IntrinsicBootstrapOptions::default())
            .unwrap();
        let globals = store.intrinsic_bootstrap().unwrap().globals;
        let importer_bound = bound.get(&importer_file).unwrap();
        if let Some(locals) = importer_bound.locals(importer_bound.source_file()) {
            let symbols = store
                .symbol_table(locals)
                .unwrap()
                .iter()
                .map(|(_, symbol)| symbol)
                .collect::<Vec<_>>();
            for symbol in symbols {
                store.merge_global_symbol(globals, symbol).unwrap();
            }
        }
        let sources = || {
            files.iter().map(|file| {
                (
                    &file.parsed.arena,
                    bound.get(&file.file).expect("fixture bound every file"),
                )
            })
        };
        let declared_host = DeclaredTypeHost::new_after_global_merge(
            sources(),
            GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
        )
        .unwrap();
        let global_types =
            initialize_global_library_types(&mut store, &declared_host, globals, false).unwrap();
        Fixture {
            files,
            bound,
            manifest,
            global_types,
            store,
        }
    }

    fn plan_jsdoc_typedef_import(fixture: &Fixture) -> SourceJsDocTypedefImportPlan {
        let file = &fixture.files[0];
        let bound = fixture.bound.get(&file.file).unwrap();
        let jsdoc = plan_javascript_source_jsdoc(&file.parsed.arena, bound.source_file()).unwrap();
        let (declaration, typedef) = jsdoc
            .declarations()
            .iter()
            .find_map(|declaration| {
                declaration
                    .typedefs()
                    .iter()
                    .find(|typedef| typedef.source_declaration().is_some())
                    .map(|typedef| (declaration, typedef))
            })
            .expect("the importer has one source-owned JSDoc typedef");
        let JsDocType::Import(imported) = typedef.type_().unwrap().type_() else {
            panic!("the source-owned JSDoc typedef must import a type")
        };
        plan_source_jsdoc_typedef_import(
            &file.parsed.arena,
            bound,
            &fixture.store,
            declaration.node(),
            typedef.source_declaration().unwrap(),
            imported,
        )
        .unwrap()
    }

    fn resolve_jsdoc_typedef_import(
        fixture: &Fixture,
        plan: SourceJsDocTypedefImportPlan,
    ) -> Result<ResolvedSourceJsDocTypedefImport, SourceImportError> {
        let sources = || {
            fixture
                .files
                .iter()
                .map(|file| (&file.parsed.arena, fixture.bound.get(&file.file).unwrap()))
        };
        let declared_host = DeclaredTypeHost::new_after_global_merge(
            sources(),
            GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
        )
        .unwrap();
        let alias_host =
            ProductionAliasTargetHost::new(&fixture.store, sources(), &fixture.manifest).unwrap();
        resolve_source_jsdoc_typedef_import(&fixture.store, &alias_host, &declared_host, plan)
    }

    fn query_jsdoc_typedef_import(
        fixture: &mut Fixture,
        resolved: ResolvedSourceJsDocTypedefImport,
    ) -> Result<TypeId, DeclaredTypeError> {
        let Fixture {
            files,
            bound,
            global_types,
            store,
            ..
        } = fixture;
        let declared_host = DeclaredTypeHost::new_after_global_merge(
            files.iter().map(|file| {
                (
                    &file.parsed.arena,
                    bound.get(&file.file).expect("fixture bound every file"),
                )
            }),
            GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
        )
        .unwrap();
        CanonicalTypeQuery::new_with_global_types(
            store,
            &declared_host,
            global_types,
            CanonicalCheckerOptions::default(),
            &mut CanonicalCheckerDiagnostics::default(),
        )?
        .with_jsdoc_import_type_target(resolved.type_capability())?
        .get_declared_type_of_symbol(resolved.plan.local_symbol)
    }

    fn resolve_all(
        fixture: &mut Fixture,
        bindings: &[SourceImportBindingPlan],
    ) -> Result<Vec<ResolvedSourceImportBinding>, SourceImportError> {
        let Fixture {
            files,
            bound,
            manifest,
            store,
            ..
        } = fixture;
        let sources = || {
            files.iter().map(|file| {
                (
                    &file.parsed.arena,
                    bound.get(&file.file).expect("fixture bound every file"),
                )
            })
        };
        let mut alias_host = ProductionAliasTargetHost::new(store, sources(), manifest).unwrap();
        bindings
            .iter()
            .map(|binding| resolve_source_import_binding(store, &mut alias_host, binding))
            .collect()
    }

    fn resolve_namespace_exports(
        fixture: &mut Fixture,
        resolved: &ResolvedSourceImportBinding,
    ) -> Result<(), SourceImportError> {
        let Fixture {
            files,
            bound,
            manifest,
            store,
            ..
        } = fixture;
        let sources = || {
            files.iter().map(|file| {
                (
                    &file.parsed.arena,
                    bound.get(&file.file).expect("fixture bound every file"),
                )
            })
        };
        let mut alias_host = ProductionAliasTargetHost::new(store, sources(), manifest).unwrap();
        resolve_source_import_namespace_exports(store, &mut alias_host, resolved)
    }

    fn resolve_all_types(
        fixture: &mut Fixture,
        bindings: &[SourceImportBindingPlan],
    ) -> Result<Vec<ResolvedSourceTypeImportBinding>, SourceImportError> {
        let Fixture {
            files,
            bound,
            manifest,
            store,
            ..
        } = fixture;
        let sources = || {
            files.iter().map(|file| {
                (
                    &file.parsed.arena,
                    bound.get(&file.file).expect("fixture bound every file"),
                )
            })
        };
        let declared_host = DeclaredTypeHost::new_after_global_merge(
            sources(),
            GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
        )
        .unwrap();
        let mut alias_host = ProductionAliasTargetHost::new(store, sources(), manifest).unwrap();
        bindings
            .iter()
            .map(|binding| {
                resolve_source_type_import_binding(store, &mut alias_host, &declared_host, binding)
            })
            .collect()
    }

    fn resolve_all_reexports(
        fixture: &mut Fixture,
        bindings: &[SourceNamedReexportBindingPlan],
    ) -> Result<Vec<ResolvedSourceNamedReexportBinding>, SourceImportError> {
        let Fixture {
            files,
            bound,
            manifest,
            store,
            ..
        } = fixture;
        let sources = || {
            files.iter().map(|file| {
                (
                    &file.parsed.arena,
                    bound.get(&file.file).expect("fixture bound every file"),
                )
            })
        };
        let mut alias_host = ProductionAliasTargetHost::new(store, sources(), manifest).unwrap();
        bindings
            .iter()
            .map(|binding| resolve_source_named_reexport_binding(store, &mut alias_host, binding))
            .collect()
    }

    fn type_reference(fixture: &Fixture, source: usize, name: &str) -> NodeRef {
        let file = &fixture.files[source];
        file.parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                let NodeData::TypeReferenceNode(reference) = &record.data else {
                    return None;
                };
                let name_node = file.parsed.arena.get(reference.type_name)?;
                matches!(
                    &name_node.data,
                    NodeData::Identifier(identifier) if identifier.text == name
                )
                .then_some(NodeRef::new(file.parsed.arena.id(), file.file, node))
            })
            .unwrap_or_else(|| panic!("fixture contains type reference {name}"))
    }

    fn variable_type_node(fixture: &Fixture, source: usize, name: &str) -> NodeRef {
        let file = &fixture.files[source];
        file.parsed
            .arena
            .iter()
            .find_map(|(_, record)| {
                let NodeData::VariableDeclaration(variable) = &record.data else {
                    return None;
                };
                let name_node = file.parsed.arena.get(variable.name)?;
                matches!(
                    &name_node.data,
                    NodeData::Identifier(identifier) if identifier.text == name
                )
                .then(|| {
                    NodeRef::new(
                        file.parsed.arena.id(),
                        file.file,
                        variable.type_.expect("fixture variable is annotated"),
                    )
                })
            })
            .unwrap_or_else(|| panic!("fixture contains annotated variable {name}"))
    }

    fn plan_type_reference_capability(
        fixture: &Fixture,
        resolved: &ResolvedSourceTypeImportBinding,
        reference: NodeRef,
    ) -> CanonicalTypeReferenceAliasTarget {
        try_plan_type_reference_capability(fixture, resolved, reference).unwrap()
    }

    fn plan_type_reference_capability_for_root(
        fixture: &Fixture,
        resolved: &ResolvedSourceTypeImportBinding,
        root: NodeRef,
        reference: NodeRef,
    ) -> CanonicalTypeReferenceAliasTarget {
        try_plan_type_reference_capability_for_root(fixture, resolved, root, reference).unwrap()
    }

    fn try_plan_type_reference_capability(
        fixture: &Fixture,
        resolved: &ResolvedSourceTypeImportBinding,
        reference: NodeRef,
    ) -> Result<CanonicalTypeReferenceAliasTarget, SourceImportError> {
        try_plan_type_reference_capability_for_root(fixture, resolved, reference, reference)
    }

    fn try_plan_type_reference_capability_for_root(
        fixture: &Fixture,
        resolved: &ResolvedSourceTypeImportBinding,
        root: NodeRef,
        reference: NodeRef,
    ) -> Result<CanonicalTypeReferenceAliasTarget, SourceImportError> {
        let sources = || {
            fixture.files.iter().map(|file| {
                (
                    &file.parsed.arena,
                    fixture
                        .bound
                        .get(&file.file)
                        .expect("fixture bound every file"),
                )
            })
        };
        let declared_host = DeclaredTypeHost::new_after_global_merge(
            sources(),
            GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
        )
        .unwrap();
        plan_source_type_import_reference(&fixture.store, &declared_host, resolved, root, reference)
    }

    fn query_type_with_import_capability(
        fixture: &mut Fixture,
        node: NodeRef,
        capability: CanonicalTypeReferenceAliasTarget,
    ) -> Result<TypeId, DeclaredTypeError> {
        query_type_with_import_capabilities(fixture, node, [capability])
    }

    fn query_type_with_import_capabilities(
        fixture: &mut Fixture,
        node: NodeRef,
        capabilities: impl IntoIterator<Item = CanonicalTypeReferenceAliasTarget>,
    ) -> Result<TypeId, DeclaredTypeError> {
        let Fixture {
            files,
            bound,
            global_types,
            store,
            ..
        } = fixture;
        let sources = || {
            files.iter().map(|file| {
                (
                    &file.parsed.arena,
                    bound.get(&file.file).expect("fixture bound every file"),
                )
            })
        };
        let declared_host = DeclaredTypeHost::new_after_global_merge(
            sources(),
            GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
        )
        .unwrap();
        CanonicalTypeQuery::new_with_global_types(
            store,
            &declared_host,
            global_types,
            CanonicalCheckerOptions::default(),
            &mut CanonicalCheckerDiagnostics::default(),
        )?
        .with_type_reference_alias_targets(capabilities)?
        .get_type_from_type_node(node)
    }

    fn query_type_without_import_capability(
        fixture: &mut Fixture,
        reference: NodeRef,
    ) -> Result<TypeId, DeclaredTypeError> {
        let Fixture {
            files,
            bound,
            global_types,
            store,
            ..
        } = fixture;
        let sources = || {
            files.iter().map(|file| {
                (
                    &file.parsed.arena,
                    bound.get(&file.file).expect("fixture bound every file"),
                )
            })
        };
        let declared_host = DeclaredTypeHost::new_after_global_merge(
            sources(),
            GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
        )
        .unwrap();
        CanonicalTypeQuery::new_with_global_types(
            store,
            &declared_host,
            global_types,
            CanonicalCheckerOptions::default(),
            &mut CanonicalCheckerDiagnostics::default(),
        )?
        .get_type_from_type_node(reference)
    }

    fn store_state(
        store: &CanonicalTypeMapperStore,
    ) -> (usize, usize, [usize; 26], (usize, usize, usize, u64)) {
        (
            store.type_len(),
            store.mapper_len(),
            store.checker_link_allocated_lengths(),
            store.type_resolution_internal_state(),
        )
    }

    fn query_declared_type(
        fixture: &mut Fixture,
        symbol: SemanticSymbolId,
    ) -> Result<TypeId, DeclaredTypeError> {
        let Fixture {
            files,
            bound,
            global_types,
            store,
            ..
        } = fixture;
        let sources = || {
            files.iter().map(|file| {
                (
                    &file.parsed.arena,
                    bound.get(&file.file).expect("fixture bound every file"),
                )
            })
        };
        let declared_host = DeclaredTypeHost::new_after_global_merge(
            sources(),
            GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
        )
        .unwrap();
        CanonicalTypeQuery::new_with_global_types(
            store,
            &declared_host,
            global_types,
            CanonicalCheckerOptions::default(),
            &mut CanonicalCheckerDiagnostics::default(),
        )?
        .get_declared_type_of_symbol(symbol)
    }

    fn query_source_callable_with_import_capability(
        fixture: &mut Fixture,
        declaration: NodeRef,
        owner_symbol: SemanticSymbolId,
        capability: CanonicalTypeReferenceAliasTarget,
    ) -> Result<TypeId, DeclaredTypeError> {
        let Fixture {
            files,
            bound,
            global_types,
            store,
            ..
        } = fixture;
        let sources = || {
            files.iter().map(|file| {
                (
                    &file.parsed.arena,
                    bound.get(&file.file).expect("fixture bound every file"),
                )
            })
        };
        let declared_host = DeclaredTypeHost::new_after_global_merge(
            sources(),
            GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
        )
        .unwrap();
        CanonicalTypeQuery::new_with_global_types(
            store,
            &declared_host,
            global_types,
            CanonicalCheckerOptions::default(),
            &mut CanonicalCheckerDiagnostics::default(),
        )?
        .with_type_reference_alias_targets([capability])?
        .get_type_of_source_callable(declaration, owner_symbol)
    }

    fn prepare_one(
        fixture: &mut Fixture,
        resolved: &ResolvedSourceImportBinding,
        read: &PlannedSourceImportRead,
    ) -> Result<PreparedSourceImportValue, SourceImportError> {
        let Fixture {
            files,
            bound,
            global_types,
            store,
            ..
        } = fixture;
        let sources = || {
            files.iter().map(|file| {
                (
                    &file.parsed.arena,
                    bound.get(&file.file).expect("fixture bound every file"),
                )
            })
        };
        let declared_host = DeclaredTypeHost::new_after_global_merge(
            sources(),
            GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
        )
        .unwrap();
        let mut session = InstantiationSession::new(InstantiationLimits::default());
        prepare_source_import_value(
            store,
            &declared_host,
            global_types,
            CanonicalCheckerOptions::default(),
            &mut session,
            &mut CanonicalCheckerDiagnostics::default(),
            resolved,
            read,
        )
    }

    fn display_type(fixture: &Fixture, type_: TypeId) -> String {
        let sources = || {
            fixture.files.iter().map(|file| {
                (
                    &file.parsed.arena,
                    fixture
                        .bound
                        .get(&file.file)
                        .expect("fixture bound every file"),
                )
            })
        };
        let host = DeclaredTypeHost::new_after_global_merge(
            sources(),
            GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
        )
        .unwrap();
        type_to_string_with_host_global_types_and_flags(
            &fixture.store,
            &host,
            &fixture.global_types,
            type_,
            CanonicalTypeFormatFlags::TYPE_TO_STRING_DEFAULT,
        )
        .unwrap()
    }

    fn publish_for_test(
        store: &mut CanonicalTypeMapperStore,
        prepared: &[PreparedSourceImportValue],
    ) {
        let publications = preflight_prepared_source_import_publications(store, prepared).unwrap();
        for publication in publications {
            assert!(store.set_value_symbol_links(publication.symbol, publication.links));
        }
    }

    fn identifier_initializer(fixture: &Fixture, source: usize, name: &str) -> NodeRef {
        let file = &fixture.files[source];
        file.parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                let NodeData::Identifier(identifier) = &record.data else {
                    return None;
                };
                if identifier.text != name {
                    return None;
                }
                let parent = record
                    .parent
                    .and_then(|parent| file.parsed.arena.get(parent))?;
                matches!(
                    &parent.data,
                    NodeData::VariableDeclaration(variable) if variable.initializer == Some(node)
                )
                .then_some(NodeRef::new(file.parsed.arena.id(), file.file, node))
            })
            .expect("fixture contains requested identifier initializer")
    }

    fn binding_symbol(plan: &SourceImportPlan, local: &str) -> SemanticSymbolId {
        plan.bindings
            .iter()
            .find(|binding| binding.local_text == local)
            .unwrap_or_else(|| panic!("missing import binding {local}"))
            .alias_symbol
    }

    fn direct_export(fixture: &Fixture, source: usize, name: &str) -> SemanticSymbolId {
        let bound = fixture.bound.get(&fixture.files[source].file).unwrap();
        let module = bound.symbol(bound.source_file()).unwrap();
        let exports = fixture.store.symbol(module).unwrap().exports().unwrap();
        fixture
            .store
            .symbol_table(exports)
            .unwrap()
            .get_source(name)
            .unwrap()
    }

    #[test]
    fn side_effect_and_empty_named_imports_do_not_allocate_alias_state() {
        for (source, type_only) in [
            (r#"import "./target";"#, false),
            (r#"import {} from "./target";"#, false),
            (r#"import type {} from "./target";"#, true),
        ] {
            let fixture = fixture(
                &[source, "export type Model = number;"],
                &[Route {
                    source: 0,
                    specifier: 0,
                    target: Some(1),
                }],
            );
            let before = store_state(&fixture.store);
            let plan = if type_only {
                fixture.plan_type_import(0, 0)
            } else {
                fixture.plan_import(0, 0)
            };
            assert!(plan.bindings.is_empty());
            assert_eq!(plan.module_specifier.file, fixture.files[0].file);
            assert_eq!(store_state(&fixture.store), before);
        }
    }

    #[test]
    fn default_import_reused_by_an_exported_type_resolves_and_publishes_its_value() {
        let mut fixture = fixture(
            &[
                r#"import test from "./target"; export type test = string; const copied = test;"#,
                "export const value: number = 1; export { value as default };",
            ],
            &[Route {
                source: 0,
                specifier: 0,
                target: Some(1),
            }],
        );
        let file = &fixture.files[0];
        let bound = fixture.bound.get(&file.file).unwrap();
        let declaration = file
            .parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::ImportDeclaration).then_some(NodeRef::new(
                    file.parsed.arena.id(),
                    file.file,
                    node,
                ))
            })
            .unwrap();
        let NodeData::ImportDeclaration(import) =
            &file.parsed.arena.get(declaration.node).unwrap().data
        else {
            panic!("expected the default import")
        };
        let clause = NodeRef::new(
            file.parsed.arena.id(),
            file.file,
            import.import_clause.unwrap(),
        );
        let alias = bound.symbol(clause).unwrap();
        let export = direct_export(&fixture, 0, "test");
        assert_eq!(
            fixture.store.symbol(alias).unwrap().export_symbol(),
            Some(export)
        );
        let before = store_state(&fixture.store);

        for _ in 0..2 {
            let plan = plan_top_level_named_value_import(
                &file.parsed.arena,
                bound,
                &fixture.store,
                declaration,
            )
            .unwrap();
            let [binding] = plan.bindings.as_slice() else {
                panic!("expected the merged default import binding")
            };
            assert_eq!(binding.alias_symbol, alias);
            assert_eq!(binding.declaration, clause);
            assert_eq!(store_state(&fixture.store), before);
        }
        assert!(fixture.store.alias_symbol_links(alias).is_none());
        assert!(fixture.store.value_symbol_links(alias).is_none());

        let plan = fixture.plan_import(0, 0);
        let read_node = identifier_initializer(&fixture, 0, "test");
        let bound = fixture.bound.get(&fixture.files[0].file).unwrap();
        let read = plan_source_import_identifier_read(
            &fixture.files[0].parsed.arena,
            bound,
            &fixture.store,
            &plan.bindings[0],
            read_node,
            "test",
            alias,
        )
        .unwrap();
        let default = direct_export(&fixture, 1, "default");
        let value = direct_export(&fixture, 1, "value");
        let resolved = resolve_all(&mut fixture, &plan.bindings).unwrap();
        assert_eq!(resolved[0].immediate_target_symbol, default);
        assert_eq!(resolved[0].target_symbol, value);
        assert_eq!(
            fixture
                .store
                .alias_symbol_links(alias)
                .map(|links| (links.immediate_target, links.alias_target)),
            Some((Some(default), AliasTargetState::Resolved(value))),
        );
        assert_eq!(
            fixture.store.symbol(alias).unwrap().export_symbol(),
            Some(export)
        );

        let prepared = prepare_one(&mut fixture, &resolved[0], &read).unwrap();
        assert_eq!(
            prepared.type_,
            fixture.store.intrinsic_bootstrap().unwrap().number_type,
        );
        assert!(fixture.store.value_symbol_links(alias).is_none());
        publish_for_test(&mut fixture.store, std::slice::from_ref(&prepared));
        assert_eq!(
            fixture
                .store
                .value_symbol_links(alias)
                .and_then(|links| links.resolved_type),
            Some(prepared.type_),
        );

        let warm = store_state(&fixture.store);
        assert_eq!(resolve_all(&mut fixture, &plan.bindings).unwrap(), resolved);
        assert_eq!(
            prepare_one(&mut fixture, &resolved[0], &read).unwrap(),
            prepared
        );
        assert_eq!(store_state(&fixture.store), warm);
    }

    #[test]
    fn named_and_namespace_imports_reused_by_exported_types_keep_value_identity() {
        for (source, target, namespace) in [
            (
                concat!(
                    "import { test } from './target'; ",
                    "export type test = string; ",
                    "const copied = test;",
                ),
                "export const test: number = 1;",
                false,
            ),
            (
                concat!(
                    "import * as test from './target'; ",
                    "export type test = string; ",
                    "const copied = test;",
                ),
                "export const value: number = 1;",
                true,
            ),
        ] {
            let mut fixture = fixture(
                &[source, target],
                &[Route {
                    source: 0,
                    specifier: 0,
                    target: Some(1),
                }],
            );
            let plan = fixture.plan_import(0, 0);
            let [binding] = plan.bindings.as_slice() else {
                panic!("expected one merged import binding")
            };
            let alias = binding.alias_symbol;
            let exported_type = direct_export(&fixture, 0, "test");
            assert_eq!(
                fixture.store.symbol(alias).unwrap().export_symbol(),
                Some(exported_type),
            );
            let read_node = identifier_initializer(&fixture, 0, "test");
            let bound = fixture.bound.get(&fixture.files[0].file).unwrap();
            let read = plan_source_import_identifier_read(
                &fixture.files[0].parsed.arena,
                bound,
                &fixture.store,
                binding,
                read_node,
                "test",
                alias,
            )
            .unwrap();
            let expected_target = if namespace {
                let target_bound = fixture.bound.get(&fixture.files[1].file).unwrap();
                target_bound.symbol(target_bound.source_file()).unwrap()
            } else {
                direct_export(&fixture, 1, "test")
            };

            let resolved = resolve_all(&mut fixture, &plan.bindings).unwrap();
            assert_eq!(resolved[0].target_symbol, expected_target);
            let prepared = prepare_one(&mut fixture, &resolved[0], &read).unwrap();
            assert!(fixture.store.value_symbol_links(alias).is_none());
            publish_for_test(&mut fixture.store, std::slice::from_ref(&prepared));
            assert_eq!(
                fixture
                    .store
                    .value_symbol_links(alias)
                    .and_then(|links| links.resolved_type),
                Some(prepared.type_),
            );

            let warm = store_state(&fixture.store);
            assert_eq!(resolve_all(&mut fixture, &plan.bindings).unwrap(), resolved);
            assert_eq!(
                prepare_one(&mut fixture, &resolved[0], &read).unwrap(),
                prepared,
            );
            assert_eq!(store_state(&fixture.store), warm);
        }
    }

    #[test]
    fn merged_default_import_rejects_poisoned_warm_alias_links() {
        let mut fixture = fixture(
            &[
                r#"import test from "./target"; export type test = string;"#,
                "export const value: number = 1; export { value as default };",
            ],
            &[Route {
                source: 0,
                specifier: 0,
                target: Some(1),
            }],
        );
        let plan = fixture.plan_import(0, 0);
        let alias = plan.bindings[0].alias_symbol;
        let resolved = resolve_all(&mut fixture, &plan.bindings).unwrap();
        let valid = fixture.store.alias_symbol_links(alias).unwrap().clone();
        let exported_type = direct_export(&fixture, 0, "test");
        let mut poisoned = valid.clone();
        poisoned.immediate_target = Some(exported_type);
        assert!(fixture.store.set_alias_symbol_links(alias, poisoned));
        let before = store_state(&fixture.store);

        for _ in 0..2 {
            assert_eq!(
                resolve_all(&mut fixture, &plan.bindings),
                Err(SourceImportError::Invariant(
                    SourceImportInvariant::InvalidAliasLinks(alias),
                )),
            );
            assert_eq!(store_state(&fixture.store), before);
        }

        assert!(fixture.store.set_alias_symbol_links(alias, valid));
        assert_eq!(resolve_all(&mut fixture, &plan.bindings).unwrap(), resolved);
    }

    #[test]
    fn forged_default_import_type_exports_remain_invariant_failures() {
        #[derive(Clone, Copy, Debug)]
        enum Forgery {
            ForeignExport,
            WrongExportFlags,
            WrongExportParent,
            WrongAliasFlags,
        }

        for forgery in [
            Forgery::ForeignExport,
            Forgery::WrongExportFlags,
            Forgery::WrongExportParent,
            Forgery::WrongAliasFlags,
        ] {
            let mut fixture = fixture(
                &[
                    r#"import test from "./target"; export type test = string;"#,
                    "export type test = number;",
                ],
                &[Route {
                    source: 0,
                    specifier: 0,
                    target: Some(1),
                }],
            );
            let file = &fixture.files[0];
            let bound = fixture.bound.get(&file.file).unwrap();
            let declaration = file
                .parsed
                .arena
                .iter()
                .find_map(|(node, record)| {
                    (record.kind == SyntaxKind::ImportDeclaration).then_some(NodeRef::new(
                        file.parsed.arena.id(),
                        file.file,
                        node,
                    ))
                })
                .unwrap();
            let NodeData::ImportDeclaration(import) =
                &file.parsed.arena.get(declaration.node).unwrap().data
            else {
                panic!("expected the default import")
            };
            let clause = NodeRef::new(
                file.parsed.arena.id(),
                file.file,
                import.import_clause.unwrap(),
            );
            let alias = bound.symbol(clause).unwrap();
            let export = direct_export(&fixture, 0, "test");
            let foreign = direct_export(&fixture, 1, "test");
            let foreign_bound = fixture.bound.get(&fixture.files[1].file).unwrap();
            let foreign_module = foreign_bound.symbol(foreign_bound.source_file()).unwrap();

            match forgery {
                Forgery::ForeignExport => assert!(fixture.store.set_symbol_relationships(
                    alias,
                    None,
                    None,
                    None,
                    Some(foreign),
                )),
                Forgery::WrongExportFlags => assert!(fixture.store.set_symbol_flags(
                    export,
                    SymbolFlags::INTERFACE,
                    CheckFlags::NONE,
                )),
                Forgery::WrongExportParent => assert!(fixture.store.set_symbol_relationships(
                    export,
                    None,
                    None,
                    Some(foreign_module),
                    None,
                )),
                Forgery::WrongAliasFlags => assert!(fixture.store.set_symbol_flags(
                    alias,
                    SymbolFlags::PROPERTY,
                    CheckFlags::NONE,
                )),
            }

            let before = store_state(&fixture.store);
            for _ in 0..2 {
                assert_eq!(
                    plan_top_level_named_value_import(
                        &file.parsed.arena,
                        bound,
                        &fixture.store,
                        declaration,
                    ),
                    Err(SourceImportError::Invariant(
                        SourceImportInvariant::InvalidAliasSymbol(alias),
                    )),
                    "{forgery:?}",
                );
                assert_eq!(store_state(&fixture.store), before);
            }
        }
    }

    #[test]
    fn unused_namespace_imports_resolve_without_querying_module_values() {
        let mut fixture = fixture(
            &[
                r#"import * as namespace from "./target";"#,
                "export const value: number = 1;",
            ],
            &[Route {
                source: 0,
                specifier: 0,
                target: Some(1),
            }],
        );
        let plan = fixture.plan_import(0, 0);
        assert_eq!(plan.bindings.len(), 1);
        assert_eq!(plan.bindings[0].imported_text, "*");
        assert_eq!(plan.bindings[0].local_text, "namespace");

        let target_bound = fixture.bound.get(&fixture.files[1].file).unwrap();
        let module = target_bound.symbol(target_bound.source_file()).unwrap();
        let resolved = resolve_all(&mut fixture, &plan.bindings).unwrap();
        assert_eq!(resolved.len(), 1);
        assert_eq!(resolved[0].immediate_target_symbol, module);
        assert_eq!(resolved[0].target_symbol, module);
        assert!(
            fixture
                .store
                .value_symbol_links(plan.bindings[0].alias_symbol)
                .is_none()
        );
        assert!(fixture.store.value_symbol_links(module).is_none());
    }

    #[test]
    fn external_and_local_import_equals_preserve_exact_module_aliases() {
        let mut fixture = fixture(
            &[
                r#"
                    import required = require("./target");
                    import forwarded = required;
                "#,
                "export function value(): number { return 1; }",
            ],
            &[Route {
                source: 0,
                specifier: 0,
                target: Some(1),
            }],
        );
        let source = &fixture.files[0];
        let bound = fixture.bound.get(&source.file).unwrap();
        let imports = source
            .parsed
            .arena
            .iter()
            .filter_map(|(node, record)| {
                (record.kind == SyntaxKind::ImportEqualsDeclaration).then_some(NodeRef::new(
                    source.parsed.arena.id(),
                    source.file,
                    node,
                ))
            })
            .map(|declaration| {
                plan_top_level_import_equals(
                    &source.parsed.arena,
                    bound,
                    &fixture.store,
                    declaration,
                )
                .unwrap()
            })
            .collect::<Vec<_>>();
        assert_eq!(imports.len(), 2);
        assert_eq!(imports[0].bindings[0].local_text, "required");
        assert_eq!(imports[1].bindings[0].local_text, "forwarded");

        let required = resolve_all(&mut fixture, &imports[0].bindings).unwrap();
        let forwarded = resolve_all(&mut fixture, &imports[1].bindings).unwrap();
        let target = fixture.bound.get(&fixture.files[1].file).unwrap();
        let module = target.symbol(target.source_file()).unwrap();
        assert_eq!(required[0].target_symbol, module);
        assert_eq!(
            forwarded[0].immediate_target_symbol,
            imports[0].bindings[0].alias_symbol
        );
        assert_eq!(forwarded[0].target_symbol, module);
    }

    #[test]
    fn exported_import_equals_resolves_namespace_types_without_value_publication() {
        let mut fixture = fixture(
            &[
                r#"
                    import * as ns from "./target";
                    export import A = ns.A;
                "#,
                "export interface A { value: number; }",
            ],
            &[Route {
                source: 0,
                specifier: 0,
                target: Some(1),
            }],
        );
        let namespace = fixture.plan_import(0, 0);
        let exported = fixture.try_plan_import_equals(0, 0).unwrap();
        let alias = exported.bindings[0].alias_symbol;
        assert_eq!(direct_export(&fixture, 0, "A"), alias);

        let namespace_resolution = resolve_all(&mut fixture, &namespace.bindings).unwrap();
        let resolved = resolve_all(&mut fixture, &exported.bindings).unwrap();
        let target = direct_export(&fixture, 1, "A");
        assert_eq!(resolved[0].immediate_target_symbol, target);
        assert_eq!(resolved[0].target_symbol, target);
        assert!(fixture.store.value_symbol_links(alias).is_none());
        assert!(
            fixture
                .store
                .value_symbol_links(namespace.bindings[0].alias_symbol)
                .is_none()
        );
        assert!(fixture.store.value_symbol_links(target).is_none());

        let cold = store_state(&fixture.store);
        assert_eq!(
            resolve_all(&mut fixture, &namespace.bindings).unwrap(),
            namespace_resolution,
        );
        assert_eq!(
            resolve_all(&mut fixture, &exported.bindings).unwrap(),
            resolved,
        );
        assert_eq!(store_state(&fixture.store), cold);
    }

    #[test]
    fn exported_import_equals_values_publish_their_authenticated_alias() {
        let mut fixture = fixture(
            &[
                r#"
                    import * as ns from "./target";
                    export import Forwarded = ns;
                    const copied = Forwarded;
                "#,
                "export const value: number = 1;",
            ],
            &[Route {
                source: 0,
                specifier: 0,
                target: Some(1),
            }],
        );
        let namespace = fixture.plan_import(0, 0);
        let exported = fixture.try_plan_import_equals(0, 0).unwrap();
        let node = identifier_initializer(&fixture, 0, "Forwarded");
        let bound = fixture.bound.get(&fixture.files[0].file).unwrap();
        let read = plan_source_import_identifier_read(
            &fixture.files[0].parsed.arena,
            bound,
            &fixture.store,
            &exported.bindings[0],
            node,
            "Forwarded",
            exported.bindings[0].alias_symbol,
        )
        .unwrap();
        resolve_all(&mut fixture, &namespace.bindings).unwrap();
        let resolved = resolve_all(&mut fixture, &exported.bindings).unwrap();
        assert_eq!(
            resolved[0].immediate_target_symbol,
            namespace.bindings[0].alias_symbol,
        );

        let prepared = prepare_one(&mut fixture, &resolved[0], &read).unwrap();
        assert!(
            fixture
                .store
                .value_symbol_links(exported.bindings[0].alias_symbol)
                .is_none()
        );
        publish_for_test(&mut fixture.store, std::slice::from_ref(&prepared));
        assert_eq!(
            fixture
                .store
                .value_symbol_links(exported.bindings[0].alias_symbol)
                .and_then(|links| links.resolved_type),
            Some(prepared.type_),
        );
        assert!(
            fixture
                .store
                .value_symbol_links(namespace.bindings[0].alias_symbol)
                .is_none()
        );

        let published = store_state(&fixture.store);
        assert_eq!(
            prepare_one(&mut fixture, &resolved[0], &read).unwrap(),
            prepared,
        );
        assert_eq!(store_state(&fixture.store), published);
    }

    #[test]
    fn exported_import_equals_rejects_malformed_modifiers_and_foreign_parents() {
        let sources = [
            r#"
                import * as ns from "./target";
                export import A = ns.A;
            "#,
            "export interface A { value: number; }",
        ];
        let routes = [Route {
            source: 0,
            specifier: 0,
            target: Some(1),
        }];
        let malformed = fixture_with_module_states_and_wrapper_flags(
            &sources,
            &routes,
            &[
                CanonicalModuleState::External,
                CanonicalModuleState::External,
            ],
            Some(SyntaxKind::ExportKeyword),
            &[],
        );
        assert!(matches!(
            malformed.try_plan_import_equals(0, 0),
            Err(SourceImportError::Unsupported(
                SourceImportUnsupported::ImportShape(_)
            ))
        ));

        let mut foreign = fixture(&sources, &routes);
        let exported = foreign.try_plan_import_equals(0, 0).unwrap();
        let alias = exported.bindings[0].alias_symbol;
        let target_bound = foreign.bound.get(&foreign.files[1].file).unwrap();
        let foreign_parent = target_bound.symbol(target_bound.source_file()).unwrap();
        assert!(foreign.store.set_symbol_relationships(
            alias,
            None,
            None,
            Some(foreign_parent),
            None
        ));
        assert_eq!(
            foreign.try_plan_import_equals(0, 0),
            Err(SourceImportError::Invariant(
                SourceImportInvariant::InvalidAliasSymbol(alias)
            )),
        );
        assert!(foreign.store.alias_symbol_links(alias).is_none());
        assert!(foreign.store.value_symbol_links(alias).is_none());
    }

    #[test]
    fn namespace_import_wraps_merged_ambient_callable_without_changing_its_value() {
        let mut fixture = fixture_with_declaration_files(
            &[
                r#"import * as foo from "./foo"; const imported = foo;"#,
                concat!(
                    "declare function foo(): void; ",
                    "declare namespace foo {} ",
                    "export = foo;",
                ),
            ],
            &[Route {
                source: 0,
                specifier: 0,
                target: Some(1),
            }],
            &[1],
        );
        let plan = fixture.plan_import(0, 0);
        let node = identifier_initializer(&fixture, 0, "foo");
        let bound = fixture.bound.get(&fixture.files[0].file).unwrap();
        let read = plan_source_import_identifier_read(
            &fixture.files[0].parsed.arena,
            bound,
            &fixture.store,
            &plan.bindings[0],
            node,
            "foo",
            plan.bindings[0].alias_symbol,
        )
        .unwrap();
        let resolved = resolve_all(&mut fixture, &plan.bindings).unwrap();
        let target_bound = fixture.bound.get(&fixture.files[1].file).unwrap();
        let original = fixture
            .store
            .symbol_table(target_bound.locals(target_bound.source_file()).unwrap())
            .unwrap()
            .get_source("foo")
            .unwrap();
        assert_ne!(resolved[0].target_symbol, original);
        assert!(fixture.store.value_symbol_links(original).is_none());
        resolve_namespace_exports(&mut fixture, &resolved[0]).unwrap();

        let prepared = prepare_one(&mut fixture, &resolved[0], &read).unwrap();

        let PreparedSourceImportTarget::ModuleNamespace { properties } = &prepared.target else {
            panic!("expected a synthetic module namespace")
        };
        let [property] = properties.as_slice() else {
            panic!("expected exactly one synthetic default property")
        };
        let callable = fixture
            .store
            .source_callable_type_for_owner(original)
            .unwrap();
        assert_eq!(property.value_symbol, original);
        assert_eq!(property.name.as_ref(), InternalSymbolName::Default.as_ref());
        assert_eq!(property.type_, callable);
        assert_eq!(
            fixture
                .store
                .value_symbol_links(original)
                .and_then(|links| links.resolved_type),
            Some(callable)
        );
        assert!(matches!(
            validate_stored_source_callable(&fixture.store, callable),
            StoredSourceCallableValidation::Valid(_)
        ));
        let namespace = fixture.store.type_payload(prepared.type_).unwrap();
        let structured = namespace.data().structured().unwrap();
        assert!(namespace.symbol().is_none());
        assert_eq!(structured.call_signature_count, 0);
        assert!(structured.signatures.is_none());
        assert_eq!(
            structured.properties.as_deref(),
            Some(&[property.symbol][..])
        );
        let signature = fixture
            .store
            .source_callable_provenance(callable)
            .map(|provenance| provenance.signature)
            .and_then(|signature| fixture.store.signature(signature))
            .unwrap();
        assert!(signature.parameters().is_empty());
        assert_eq!(
            signature.resolved_return_type(),
            Some(fixture.store.intrinsic_bootstrap().unwrap().void_type)
        );
        assert!(
            fixture
                .store
                .value_symbol_links(plan.bindings[0].alias_symbol)
                .is_none()
        );

        publish_for_test(&mut fixture.store, std::slice::from_ref(&prepared));
        let published = store_state(&fixture.store);
        assert_eq!(
            prepare_one(&mut fixture, &resolved[0], &read).unwrap(),
            prepared
        );
        assert_eq!(store_state(&fixture.store), published);
        assert_eq!(
            fixture
                .store
                .value_symbol_links(original)
                .and_then(|links| links.resolved_type),
            Some(callable)
        );
    }

    #[test]
    fn synthetic_namespace_import_rejects_poisoned_target_and_module_links() {
        for poison_target in [true, false] {
            let mut fixture = fixture_with_declaration_files(
                &[
                    r#"import * as foo from "./foo"; const imported = foo;"#,
                    concat!(
                        "declare function foo(): void; ",
                        "declare namespace foo {} ",
                        "export = foo;",
                    ),
                ],
                &[Route {
                    source: 0,
                    specifier: 0,
                    target: Some(1),
                }],
                &[1],
            );
            let plan = fixture.plan_import(0, 0);
            let node = identifier_initializer(&fixture, 0, "foo");
            let bound = fixture.bound.get(&fixture.files[0].file).unwrap();
            let read = plan_source_import_identifier_read(
                &fixture.files[0].parsed.arena,
                bound,
                &fixture.store,
                &plan.bindings[0],
                node,
                "foo",
                plan.bindings[0].alias_symbol,
            )
            .unwrap();
            let resolved = resolve_all(&mut fixture, &plan.bindings).unwrap();
            let synthetic = resolved[0].target_symbol;
            let importer_module = fixture
                .bound
                .get(&fixture.files[0].file)
                .and_then(|bound| bound.symbol(bound.source_file()))
                .unwrap();
            if poison_target {
                let mut links = fixture.store.export_type_links(synthetic).unwrap().clone();
                links.target = Some(importer_module);
                assert!(fixture.store.set_export_type_links(synthetic, links));
            } else {
                let default = fixture
                    .store
                    .symbol(synthetic)
                    .and_then(ts_binder::semantic::Symbol::exports)
                    .and_then(|exports| fixture.store.symbol_table(exports))
                    .and_then(|exports| exports.get(InternalSymbolName::Default.as_ref()))
                    .unwrap();
                assert!(fixture.store.set_symbol_relationships(
                    default,
                    None,
                    None,
                    Some(importer_module),
                    None,
                ));
            }
            let before = store_state(&fixture.store);

            assert!(matches!(
                resolve_namespace_exports(&mut fixture, &resolved[0]),
                Err(SourceImportError::Invariant(
                    SourceImportInvariant::InvalidTargetLinks(target)
                )) if target == synthetic
            ));
            assert!(matches!(
                prepare_one(&mut fixture, &resolved[0], &read),
                Err(SourceImportError::Invariant(
                    SourceImportInvariant::InvalidTargetLinks(target)
                )) if target == synthetic
            ));
            assert_eq!(store_state(&fixture.store), before);
            assert!(fixture.store.value_symbol_links(synthetic).is_none());
            assert!(
                fixture
                    .store
                    .value_symbol_links(plan.bindings[0].alias_symbol)
                    .is_none()
            );
        }
    }

    #[test]
    fn namespace_import_values_expose_exported_callable_properties_cold_and_warm() {
        let mut fixture = fixture(
            &[
                r#"
                    import * as namespace from "./target";
                    const imported = namespace;
                "#,
                r#"
                    export function first(): string { return "first"; }
                    export function second(): number { return 2; }
                "#,
            ],
            &[Route {
                source: 0,
                specifier: 0,
                target: Some(1),
            }],
        );
        let plan = fixture.plan_import(0, 0);
        let read = identifier_initializer(&fixture, 0, "namespace");
        let bound = fixture.bound.get(&fixture.files[0].file).unwrap();
        let planned_read = plan_source_import_identifier_read(
            &fixture.files[0].parsed.arena,
            bound,
            &fixture.store,
            &plan.bindings[0],
            read,
            "namespace",
            plan.bindings[0].alias_symbol,
        )
        .unwrap();
        let resolved = resolve_all(&mut fixture, &plan.bindings).unwrap();
        let prepared = prepare_one(&mut fixture, &resolved[0], &planned_read).unwrap();
        let PreparedSourceImportTarget::ModuleNamespace { properties } = &prepared.target else {
            panic!("expected an imported module namespace")
        };
        assert_eq!(properties.len(), 2);
        let namespace = fixture.store.type_payload(prepared.type_).unwrap();
        assert_eq!(namespace.symbol(), Some(resolved[0].target_symbol));
        let members = namespace
            .data()
            .structured()
            .and_then(|structured| structured.members)
            .and_then(|members| fixture.store.symbol_table(members))
            .unwrap();
        for name in ["first", "second"] {
            let property = members
                .get_source(name)
                .expect("module export must be an own property");
            let target = direct_export(&fixture, 1, name);
            let links = fixture.store.value_symbol_links(property).unwrap();
            assert_eq!(links.target, Some(target));
            assert!(properties.iter().any(|prepared| {
                prepared.symbol == property && prepared.target_symbol == target
            }));
            assert_eq!(
                fixture.store.source_callable_type_for_owner(target),
                links.resolved_type
            );
        }
        assert!(
            fixture
                .store
                .value_symbol_links(plan.bindings[0].alias_symbol)
                .is_none()
        );
        assert_eq!(
            display_type(&fixture, prepared.type_),
            "typeof import(\"701\")"
        );

        publish_for_test(&mut fixture.store, std::slice::from_ref(&prepared));
        let published = store_state(&fixture.store);
        let warm = prepare_one(&mut fixture, &resolved[0], &planned_read).unwrap();
        assert_eq!(warm, prepared);
        assert_eq!(store_state(&fixture.store), published);
        assert_eq!(display_type(&fixture, warm.type_), "typeof import(\"701\")");
    }

    #[test]
    fn namespace_import_materializes_empty_inferred_void_functions_cold_and_warm() {
        let mut fixture = fixture(
            &[
                r#"
                    import * as namespace from "./target";
                    const imported = namespace;
                "#,
                "export function ready() {}",
            ],
            &[Route {
                source: 0,
                specifier: 0,
                target: Some(1),
            }],
        );
        let plan = fixture.plan_import(0, 0);
        let node = identifier_initializer(&fixture, 0, "namespace");
        let bound = fixture.bound.get(&fixture.files[0].file).unwrap();
        let read = plan_source_import_identifier_read(
            &fixture.files[0].parsed.arena,
            bound,
            &fixture.store,
            &plan.bindings[0],
            node,
            "namespace",
            plan.bindings[0].alias_symbol,
        )
        .unwrap();
        let resolved = resolve_all(&mut fixture, &plan.bindings).unwrap();
        let function = direct_export(&fixture, 1, "ready");
        assert!(
            fixture
                .store
                .source_callable_type_for_owner(function)
                .is_none()
        );

        let prepared = prepare_one(&mut fixture, &resolved[0], &read).unwrap();
        let PreparedSourceImportTarget::ModuleNamespace { properties } = &prepared.target else {
            panic!("expected an imported module namespace")
        };
        let [property] = properties.as_slice() else {
            panic!("expected one inferred-void function property")
        };
        assert_eq!(property.target_symbol, function);
        assert_eq!(property.value_symbol, function);
        let callable = fixture
            .store
            .source_callable_type_for_owner(function)
            .unwrap();
        assert_eq!(property.type_, callable);
        assert!(matches!(
            validate_stored_source_callable(&fixture.store, callable),
            StoredSourceCallableValidation::Valid(_)
        ));
        let signature = fixture
            .store
            .source_callable_provenance(callable)
            .unwrap()
            .signature;
        let void = fixture.store.intrinsic_bootstrap().unwrap().void_type;
        assert_eq!(
            fixture
                .store
                .signature(signature)
                .unwrap()
                .resolved_return_type(),
            Some(void)
        );
        assert!(
            fixture
                .store
                .value_symbol_links(resolved[0].target_symbol)
                .is_none()
        );
        assert!(
            fixture
                .store
                .value_symbol_links(plan.bindings[0].alias_symbol)
                .is_none()
        );

        publish_for_test(&mut fixture.store, std::slice::from_ref(&prepared));
        let published = store_state(&fixture.store);
        assert_eq!(
            prepare_one(&mut fixture, &resolved[0], &read).unwrap(),
            prepared
        );
        assert_eq!(store_state(&fixture.store), published);
        assert_eq!(
            fixture
                .store
                .source_callable_provenance(callable)
                .unwrap()
                .signature,
            signature
        );
    }

    #[test]
    fn chained_module_aliases_preserve_nested_namespace_values_cold_and_warm() {
        let mut fixture = fixture(
            &[
                r#"
                    import required = require("./target");
                    import forwarded = required;
                    const imported = forwarded;
                "#,
                "export namespace Values { export function ready() {} }",
            ],
            &[Route {
                source: 0,
                specifier: 0,
                target: Some(1),
            }],
        );
        let required = fixture.try_plan_import_equals(0, 0).unwrap();
        let forwarded = fixture.try_plan_import_equals(0, 1).unwrap();
        let node = identifier_initializer(&fixture, 0, "forwarded");
        let bound = fixture.bound.get(&fixture.files[0].file).unwrap();
        let read = plan_source_import_identifier_read(
            &fixture.files[0].parsed.arena,
            bound,
            &fixture.store,
            &forwarded.bindings[0],
            node,
            "forwarded",
            forwarded.bindings[0].alias_symbol,
        )
        .unwrap();
        resolve_all(&mut fixture, &required.bindings).unwrap();
        let resolved = resolve_all(&mut fixture, &forwarded.bindings).unwrap();
        assert_eq!(
            resolved[0].immediate_target_symbol,
            required.bindings[0].alias_symbol,
        );

        let namespace_symbol = direct_export(&fixture, 1, "Values");
        let function_symbol = fixture
            .store
            .symbol(namespace_symbol)
            .and_then(ts_binder::semantic::Symbol::exports)
            .and_then(|exports| fixture.store.symbol_table(exports))
            .and_then(|exports| exports.get_source("ready"))
            .unwrap();
        let prepared = prepare_one(&mut fixture, &resolved[0], &read).unwrap();
        let PreparedSourceImportTarget::ModuleNamespace { properties } = &prepared.target else {
            panic!("expected an imported module namespace")
        };
        let [property] = properties.as_slice() else {
            panic!("expected one exported nested namespace")
        };
        assert_eq!(property.target_symbol, namespace_symbol);
        assert_eq!(property.value_symbol, namespace_symbol);
        let namespace = property.namespace.as_ref().unwrap();
        assert_eq!(namespace.links.resolved_type, Some(property.type_));
        assert_eq!(
            fixture.store.type_payload(property.type_).unwrap().symbol(),
            None
        );
        let [function] = namespace.properties.as_slice() else {
            panic!("expected one exported namespace function")
        };
        assert_eq!(function.target_symbol, function_symbol);
        assert_eq!(function.value_symbol, function_symbol);
        assert!(function.namespace.is_none());
        let callable = fixture
            .store
            .source_callable_type_for_owner(function_symbol)
            .unwrap();
        assert_eq!(function.type_, callable);
        let signature = fixture
            .store
            .source_callable_provenance(callable)
            .unwrap()
            .signature;
        let void = fixture.store.intrinsic_bootstrap().unwrap().void_type;
        assert_eq!(
            fixture
                .store
                .signature(signature)
                .unwrap()
                .resolved_return_type(),
            Some(void),
        );
        for symbol in [
            namespace_symbol,
            resolved[0].target_symbol,
            required.bindings[0].alias_symbol,
            forwarded.bindings[0].alias_symbol,
        ] {
            assert!(fixture.store.value_symbol_links(symbol).is_none());
        }

        let cold = (store_state(&fixture.store), fixture.store.symbol_len());
        assert_eq!(
            prepare_one(&mut fixture, &resolved[0], &read).unwrap(),
            prepared
        );
        assert_eq!(
            (store_state(&fixture.store), fixture.store.symbol_len()),
            cold,
        );
        let publications = preflight_prepared_source_import_publications(
            &fixture.store,
            std::slice::from_ref(&prepared),
        )
        .unwrap();
        assert_eq!(publications.len(), 3);
        assert_eq!(publications[0].symbol, namespace_symbol);

        publish_for_test(&mut fixture.store, std::slice::from_ref(&prepared));
        assert_eq!(
            fixture
                .store
                .value_symbol_links(namespace_symbol)
                .and_then(|links| links.resolved_type),
            Some(property.type_),
        );
        assert!(
            fixture
                .store
                .value_symbol_links(required.bindings[0].alias_symbol)
                .is_none()
        );
        let warm = (store_state(&fixture.store), fixture.store.symbol_len());
        assert_eq!(
            prepare_one(&mut fixture, &resolved[0], &read).unwrap(),
            prepared
        );
        assert_eq!(
            (store_state(&fixture.store), fixture.store.symbol_len()),
            warm,
        );
        assert_eq!(
            display_type(&fixture, prepared.type_),
            "typeof import(\"701\")"
        );
    }

    #[test]
    fn imported_module_namespaces_materialize_multiple_exported_levels() {
        let mut fixture = fixture(
            &[
                r#"
                    import * as namespace from "./target";
                    const imported = namespace;
                "#,
                "export namespace Outer { export namespace Inner { export function ready() {} } }",
            ],
            &[Route {
                source: 0,
                specifier: 0,
                target: Some(1),
            }],
        );
        let plan = fixture.plan_import(0, 0);
        let node = identifier_initializer(&fixture, 0, "namespace");
        let bound = fixture.bound.get(&fixture.files[0].file).unwrap();
        let read = plan_source_import_identifier_read(
            &fixture.files[0].parsed.arena,
            bound,
            &fixture.store,
            &plan.bindings[0],
            node,
            "namespace",
            plan.bindings[0].alias_symbol,
        )
        .unwrap();
        let resolved = resolve_all(&mut fixture, &plan.bindings).unwrap();
        let prepared = prepare_one(&mut fixture, &resolved[0], &read).unwrap();
        let PreparedSourceImportTarget::ModuleNamespace { properties } = &prepared.target else {
            panic!("expected an imported module namespace")
        };
        let [outer] = properties.as_slice() else {
            panic!("expected the outer namespace")
        };
        let outer_namespace = outer.namespace.as_ref().unwrap();
        let [inner] = outer_namespace.properties.as_slice() else {
            panic!("expected the inner namespace")
        };
        let inner_namespace = inner.namespace.as_ref().unwrap();
        let [function] = inner_namespace.properties.as_slice() else {
            panic!("expected the nested function")
        };
        assert_eq!(function.name.as_utf8(), Some("ready"));
        assert!(
            fixture
                .store
                .value_symbol_links(outer.value_symbol)
                .is_none()
        );
        assert!(
            fixture
                .store
                .value_symbol_links(inner.value_symbol)
                .is_none()
        );

        let publications = preflight_prepared_source_import_publications(
            &fixture.store,
            std::slice::from_ref(&prepared),
        )
        .unwrap();
        assert_eq!(publications.len(), 4);
        assert_eq!(publications[0].symbol, inner.value_symbol);
        assert_eq!(publications[1].symbol, outer.value_symbol);

        publish_for_test(&mut fixture.store, std::slice::from_ref(&prepared));
        assert_eq!(
            fixture
                .store
                .value_symbol_links(outer.value_symbol)
                .and_then(|links| links.resolved_type),
            Some(outer.type_),
        );
        assert_eq!(
            fixture
                .store
                .value_symbol_links(inner.value_symbol)
                .and_then(|links| links.resolved_type),
            Some(inner.type_),
        );
        let warm = (store_state(&fixture.store), fixture.store.symbol_len());
        assert_eq!(
            prepare_one(&mut fixture, &resolved[0], &read).unwrap(),
            prepared
        );
        assert_eq!(
            (store_state(&fixture.store), fixture.store.symbol_len()),
            warm,
        );
    }

    #[test]
    fn namespace_import_rejects_other_cold_inferred_function_shapes() {
        for target in [
            "export function ready() { return 1; }",
            "export function ready(value: number) {}",
            "export function ready<T>() {}",
        ] {
            let mut fixture = fixture(
                &[
                    r#"
                        import * as namespace from "./target";
                        const imported = namespace;
                    "#,
                    target,
                ],
                &[Route {
                    source: 0,
                    specifier: 0,
                    target: Some(1),
                }],
            );
            let plan = fixture.plan_import(0, 0);
            let node = identifier_initializer(&fixture, 0, "namespace");
            let bound = fixture.bound.get(&fixture.files[0].file).unwrap();
            let read = plan_source_import_identifier_read(
                &fixture.files[0].parsed.arena,
                bound,
                &fixture.store,
                &plan.bindings[0],
                node,
                "namespace",
                plan.bindings[0].alias_symbol,
            )
            .unwrap();
            let resolved = resolve_all(&mut fixture, &plan.bindings).unwrap();
            let before = store_state(&fixture.store);
            assert!(
                matches!(
                    prepare_one(&mut fixture, &resolved[0], &read),
                    Err(SourceImportError::Unsupported(
                        SourceImportUnsupported::TargetSymbol { .. }
                    ))
                ),
                "cold inferred function unexpectedly escaped its boundary: {target}"
            );
            assert_eq!(store_state(&fixture.store), before);
        }
    }

    #[test]
    fn repeated_namespace_imports_share_one_deferred_module_identity() {
        let mut fixture = fixture(
            &[
                r#"
                    import * as first from "./target";
                    import * as second from "./target";
                    const firstValue = first;
                    const secondValue = second;
                "#,
                r#"
                    export function zebra(): number { return 1; }
                    export function alpha(): string { return "alpha"; }
                "#,
            ],
            &[
                Route {
                    source: 0,
                    specifier: 0,
                    target: Some(1),
                },
                Route {
                    source: 0,
                    specifier: 1,
                    target: Some(1),
                },
            ],
        );
        let first = fixture.plan_import(0, 0);
        let second = fixture.plan_import(0, 1);
        let first_node = identifier_initializer(&fixture, 0, "first");
        let second_node = identifier_initializer(&fixture, 0, "second");
        let bound = fixture.bound.get(&fixture.files[0].file).unwrap();
        let first_read = plan_source_import_identifier_read(
            &fixture.files[0].parsed.arena,
            bound,
            &fixture.store,
            &first.bindings[0],
            first_node,
            "first",
            first.bindings[0].alias_symbol,
        )
        .unwrap();
        let second_read = plan_source_import_identifier_read(
            &fixture.files[0].parsed.arena,
            bound,
            &fixture.store,
            &second.bindings[0],
            second_node,
            "second",
            second.bindings[0].alias_symbol,
        )
        .unwrap();
        let resolved = resolve_all(
            &mut fixture,
            &[first.bindings[0].clone(), second.bindings[0].clone()],
        )
        .unwrap();
        assert_ne!(
            resolved[0].binding.alias_symbol,
            resolved[1].binding.alias_symbol
        );
        assert_eq!(resolved[0].target_symbol, resolved[1].target_symbol);

        let first_prepared = prepare_one(&mut fixture, &resolved[0], &first_read).unwrap();
        let first_state = (store_state(&fixture.store), fixture.store.symbol_len());
        let second_prepared = prepare_one(&mut fixture, &resolved[1], &second_read).unwrap();
        assert_eq!(first_prepared.type_, second_prepared.type_);
        assert_eq!(
            (store_state(&fixture.store), fixture.store.symbol_len()),
            first_state,
        );
        assert!(
            fixture
                .store
                .value_symbol_links(first_prepared.target_symbol)
                .is_none()
        );
        for prepared in [&first_prepared, &second_prepared] {
            assert!(
                fixture
                    .store
                    .value_symbol_links(prepared.binding.alias_symbol)
                    .is_none()
            );
            let PreparedSourceImportTarget::ModuleNamespace { properties } = &prepared.target
            else {
                panic!("expected an imported module namespace")
            };
            assert_eq!(
                properties
                    .iter()
                    .map(|property| property.name.clone())
                    .collect::<Vec<_>>(),
                vec![EscapedName::source("zebra"), EscapedName::source("alpha")],
            );
        }

        let prepared = [first_prepared, second_prepared];
        let publications =
            preflight_prepared_source_import_publications(&fixture.store, &prepared).unwrap();
        assert_eq!(publications.len(), 3);
        publish_for_test(&mut fixture.store, &prepared);
        let published = (store_state(&fixture.store), fixture.store.symbol_len());

        let first_warm = prepare_one(&mut fixture, &resolved[0], &first_read).unwrap();
        let second_warm = prepare_one(&mut fixture, &resolved[1], &second_read).unwrap();
        assert_eq!(first_warm, prepared[0]);
        assert_eq!(second_warm, prepared[1]);
        assert_eq!(
            (store_state(&fixture.store), fixture.store.symbol_len()),
            published,
        );
    }

    #[test]
    fn pure_namespace_import_values_are_unsupported_without_publication() {
        let mut fixture = fixture(
            &[
                r#"
                    import { Types } from "./target";
                    const imported = Types;
                "#,
                "export namespace Types { export interface Shape {} }",
            ],
            &[Route {
                source: 0,
                specifier: 0,
                target: Some(1),
            }],
        );
        let plan = fixture.plan_import(0, 0);
        let read = identifier_initializer(&fixture, 0, "Types");
        let bound = fixture.bound.get(&fixture.files[0].file).unwrap();
        let planned_read = plan_source_import_identifier_read(
            &fixture.files[0].parsed.arena,
            bound,
            &fixture.store,
            &plan.bindings[0],
            read,
            "Types",
            plan.bindings[0].alias_symbol,
        )
        .unwrap();
        let resolved = resolve_all(&mut fixture, &plan.bindings).unwrap();
        let before = (store_state(&fixture.store), fixture.store.symbol_len());

        assert!(matches!(
            prepare_one(&mut fixture, &resolved[0], &planned_read),
            Err(SourceImportError::Unsupported(
                SourceImportUnsupported::TargetSymbol { target, flags, .. }
            )) if target == resolved[0].target_symbol
                && flags == SymbolFlags::NAMESPACE_MODULE
        ));
        assert_eq!(
            (store_state(&fixture.store), fixture.store.symbol_len()),
            before
        );
    }

    #[test]
    fn exported_namespace_members_never_become_invalid_target_invariants() {
        let mut fixture = fixture(
            &[
                r#"
                    import { Values } from "./target";
                    const imported = Values;
                "#,
                "export namespace Values { export const answer: number = 1; }",
            ],
            &[Route {
                source: 0,
                specifier: 0,
                target: Some(1),
            }],
        );
        let plan = fixture.plan_import(0, 0);
        let read = identifier_initializer(&fixture, 0, "Values");
        let bound = fixture.bound.get(&fixture.files[0].file).unwrap();
        let planned_read = plan_source_import_identifier_read(
            &fixture.files[0].parsed.arena,
            bound,
            &fixture.store,
            &plan.bindings[0],
            read,
            "Values",
            plan.bindings[0].alias_symbol,
        )
        .unwrap();
        let resolved = resolve_all(&mut fixture, &plan.bindings).unwrap();
        let before = (store_state(&fixture.store), fixture.store.symbol_len());

        assert!(matches!(
            prepare_one(&mut fixture, &resolved[0], &planned_read),
            Err(SourceImportError::Unsupported(_))
        ));
        assert_eq!(
            (store_state(&fixture.store), fixture.store.symbol_len()),
            before
        );
    }

    #[test]
    fn poisoned_namespace_alias_links_fail_before_module_allocations() {
        let mut fixture = fixture(
            &[
                r#"
                    import * as namespace from "./target";
                    const imported = namespace;
                "#,
                "export function ready(): number { return 1; }",
            ],
            &[Route {
                source: 0,
                specifier: 0,
                target: Some(1),
            }],
        );
        let plan = fixture.plan_import(0, 0);
        let read = identifier_initializer(&fixture, 0, "namespace");
        let bound = fixture.bound.get(&fixture.files[0].file).unwrap();
        let planned_read = plan_source_import_identifier_read(
            &fixture.files[0].parsed.arena,
            bound,
            &fixture.store,
            &plan.bindings[0],
            read,
            "namespace",
            plan.bindings[0].alias_symbol,
        )
        .unwrap();
        let resolved = resolve_all(&mut fixture, &plan.bindings).unwrap();
        assert!(fixture.store.set_value_symbol_links(
            plan.bindings[0].alias_symbol,
            ValueSymbolLinks {
                target: Some(resolved[0].target_symbol),
                ..ValueSymbolLinks::default()
            },
        ));
        let before = (store_state(&fixture.store), fixture.store.symbol_len());

        assert!(matches!(
            prepare_one(&mut fixture, &resolved[0], &planned_read),
            Err(SourceImportError::Invariant(
                SourceImportInvariant::InvalidAliasValueLinks(alias)
            )) if alias == plan.bindings[0].alias_symbol
        ));
        assert_eq!(
            (store_state(&fixture.store), fixture.store.symbol_len()),
            before
        );
    }

    #[test]
    fn namespace_reexports_preserve_alias_and_final_value_identities() {
        let mut fixture = fixture(
            &[
                r#"
                    import * as namespace from "./barrel";
                    const imported = namespace;
                "#,
                r#"export { ready } from "./target";"#,
                "export function ready(): number { return 1; }",
            ],
            &[
                Route {
                    source: 0,
                    specifier: 0,
                    target: Some(1),
                },
                Route {
                    source: 1,
                    specifier: 0,
                    target: Some(2),
                },
            ],
        );
        let import = fixture.plan_import(0, 0);
        let reexport = fixture.plan_reexport(1, 0);
        let read = identifier_initializer(&fixture, 0, "namespace");
        let bound = fixture.bound.get(&fixture.files[0].file).unwrap();
        let planned_read = plan_source_import_identifier_read(
            &fixture.files[0].parsed.arena,
            bound,
            &fixture.store,
            &import.bindings[0],
            read,
            "namespace",
            import.bindings[0].alias_symbol,
        )
        .unwrap();
        let resolved = resolve_all(&mut fixture, &import.bindings).unwrap();
        let before = (store_state(&fixture.store), fixture.store.symbol_len());

        assert!(matches!(
            prepare_one(&mut fixture, &resolved[0], &planned_read),
            Err(SourceImportError::Unsupported(
                SourceImportUnsupported::TargetDeclaration(_)
            ))
        ));
        assert_eq!(
            (store_state(&fixture.store), fixture.store.symbol_len()),
            before
        );

        resolve_namespace_exports(&mut fixture, &resolved[0]).unwrap();
        let prepared = prepare_one(&mut fixture, &resolved[0], &planned_read).unwrap();
        let PreparedSourceImportTarget::ModuleNamespace { properties } = &prepared.target else {
            panic!("expected one reexported namespace value")
        };
        let [property] = properties.as_slice() else {
            panic!("expected one reexported namespace property")
        };
        assert_eq!(property.target_symbol, reexport.bindings[0].alias_symbol);
        assert_eq!(property.value_symbol, direct_export(&fixture, 2, "ready"));
        assert_eq!(
            fixture
                .store
                .value_symbol_links(property.symbol)
                .and_then(|links| links.target),
            Some(reexport.bindings[0].alias_symbol),
        );
        assert_eq!(
            display_type(&fixture, prepared.type_),
            "typeof import(\"701\")"
        );

        publish_for_test(&mut fixture.store, std::slice::from_ref(&prepared));
        let published = store_state(&fixture.store);
        let warm = prepare_one(&mut fixture, &resolved[0], &planned_read).unwrap();
        assert_eq!(warm, prepared);
        assert_eq!(store_state(&fixture.store), published);
    }

    #[test]
    fn declaration_file_imports_and_default_reexports_preserve_const_enum_identity() {
        let mut fixture = fixture_with_declaration_files(
            &[
                r#"
                    import Selected from "./bridge";
                    const result = Selected.First;
                "#,
                r#"
                    import { Values } from "./enum";
                    export { Values as default } from "./enum";
                "#,
                "export const enum Values { First, Second }",
            ],
            &[
                Route {
                    source: 0,
                    specifier: 0,
                    target: Some(1),
                },
                Route {
                    source: 1,
                    specifier: 0,
                    target: Some(2),
                },
                Route {
                    source: 1,
                    specifier: 1,
                    target: Some(2),
                },
            ],
            &[1, 2],
        );
        let import = fixture.plan_import(0, 0);
        let declaration_import = fixture.plan_import(1, 0);
        let reexport = fixture.plan_reexport(1, 0);
        assert_eq!(reexport.bindings[0].exported_text, "default");
        let target = direct_export(&fixture, 2, "Values");

        let bridge_import = resolve_all(&mut fixture, &declaration_import.bindings).unwrap();
        assert_eq!(bridge_import[0].target_symbol, target);
        let bridge_export = resolve_all_reexports(&mut fixture, &reexport.bindings).unwrap();
        assert_eq!(bridge_export[0].target_symbol, target);
        let resolved = resolve_all(&mut fixture, &import.bindings).unwrap();
        assert_eq!(resolved[0].target_symbol, target);
        assert_eq!(
            resolved[0].immediate_target_symbol,
            reexport.bindings[0].alias_symbol,
        );
        assert!(fixture.store.value_symbol_links(target).is_none());

        let source = &fixture.files[0];
        let read_node = source
            .parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                let NodeData::Identifier(identifier) = &record.data else {
                    return None;
                };
                if identifier.text != "Selected" {
                    return None;
                }
                let parent = record
                    .parent
                    .and_then(|parent| source.parsed.arena.get(parent))?;
                matches!(
                    &parent.data,
                    NodeData::PropertyAccessExpression(access) if access.expression == node
                )
                .then_some(NodeRef::new(
                    source.parsed.arena.id(),
                    source.file,
                    node,
                ))
            })
            .unwrap();
        let bound = fixture.bound.get(&source.file).unwrap();
        let read = plan_source_import_identifier_read(
            &source.parsed.arena,
            bound,
            &fixture.store,
            &import.bindings[0],
            read_node,
            "Selected",
            import.bindings[0].alias_symbol,
        )
        .unwrap();
        let prepared = prepare_one(&mut fixture, &resolved[0], &read).unwrap();
        let PreparedSourceImportTarget::ConstEnum { declared_type } = &prepared.target else {
            panic!("expected a prepared const enum")
        };
        assert_eq!(
            fixture
                .store
                .declared_type_links(target)
                .and_then(|links| links.declared_type),
            Some(*declared_type),
        );
        assert_eq!(
            fixture
                .store
                .value_symbol_links(target)
                .and_then(|links| links.resolved_type),
            Some(prepared.type_),
        );
        assert!(
            fixture
                .store
                .value_symbol_links(import.bindings[0].alias_symbol)
                .is_none()
        );

        publish_for_test(&mut fixture.store, std::slice::from_ref(&prepared));
        let warm = (store_state(&fixture.store), fixture.store.symbol_len());
        assert_eq!(
            prepare_one(&mut fixture, &resolved[0], &read).unwrap(),
            prepared,
        );
        assert_eq!(
            (store_state(&fixture.store), fixture.store.symbol_len()),
            warm,
        );
    }

    #[test]
    fn declaration_file_type_imports_retain_type_only_alias_without_value_links() {
        let mut fixture = fixture_with_declaration_files(
            &[
                r#"import type { Model } from "./target";"#,
                "export interface Model { value: number; }",
            ],
            &[Route {
                source: 0,
                specifier: 0,
                target: Some(1),
            }],
            &[0, 1],
        );
        let plan = fixture.plan_type_import(0, 0);
        let resolved = resolve_all_types(&mut fixture, &plan.bindings).unwrap();
        let alias = plan.bindings[0].alias_symbol;
        assert_eq!(
            resolved[0].target_symbol,
            direct_export(&fixture, 1, "Model"),
        );
        assert_eq!(
            fixture
                .store
                .alias_symbol_links(alias)
                .and_then(|links| links.type_only_declaration),
            Some(plan.bindings[0].declaration),
        );
        assert!(fixture.store.value_symbol_links(alias).is_none());

        let warm = store_state(&fixture.store);
        assert_eq!(
            resolve_all_types(&mut fixture, &plan.bindings).unwrap(),
            resolved
        );
        assert_eq!(store_state(&fixture.store), warm);
    }

    #[test]
    fn declaration_default_assignment_imports_const_enum_through_cold_alias_chain() {
        let mut fixture = fixture_with_declaration_files(
            &[
                r#"
                    import Selected from "./bridge";
                    const result = Selected.First;
                "#,
                r#"
                    import { Values } from "./enum";
                    export default Values;
                "#,
                "export const enum Values { First, Second }",
            ],
            &[
                Route {
                    source: 0,
                    specifier: 0,
                    target: Some(1),
                },
                Route {
                    source: 1,
                    specifier: 0,
                    target: Some(2),
                },
            ],
            &[1, 2],
        );
        let import = fixture.plan_import(0, 0);
        let bridge_import = fixture.plan_import(1, 0);
        let default_alias = direct_export(&fixture, 1, "default");
        let target = direct_export(&fixture, 2, "Values");

        let resolved = resolve_all(&mut fixture, &import.bindings).unwrap();
        assert_eq!(resolved[0].immediate_target_symbol, default_alias);
        assert_eq!(resolved[0].target_symbol, target);
        assert_eq!(
            fixture
                .store
                .alias_symbol_links(default_alias)
                .map(|links| links.alias_target),
            Some(AliasTargetState::Resolved(target)),
        );
        assert_eq!(
            fixture
                .store
                .alias_symbol_links(bridge_import.bindings[0].alias_symbol)
                .map(|links| links.alias_target),
            Some(AliasTargetState::Resolved(target)),
        );
        assert!(fixture.store.value_symbol_links(target).is_none());

        let source = &fixture.files[0];
        let node = source
            .parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                let NodeData::Identifier(identifier) = &record.data else {
                    return None;
                };
                if identifier.text != "Selected" {
                    return None;
                }
                let parent = record
                    .parent
                    .and_then(|parent| source.parsed.arena.get(parent))?;
                matches!(
                    &parent.data,
                    NodeData::PropertyAccessExpression(access) if access.expression == node
                )
                .then_some(NodeRef::new(
                    source.parsed.arena.id(),
                    source.file,
                    node,
                ))
            })
            .unwrap();
        let bound = fixture.bound.get(&source.file).unwrap();
        let read = plan_source_import_identifier_read(
            &source.parsed.arena,
            bound,
            &fixture.store,
            &import.bindings[0],
            node,
            "Selected",
            import.bindings[0].alias_symbol,
        )
        .unwrap();
        let prepared = prepare_one(&mut fixture, &resolved[0], &read).unwrap();
        assert!(matches!(
            &prepared.target,
            PreparedSourceImportTarget::ConstEnum { .. }
        ));
        publish_for_test(&mut fixture.store, std::slice::from_ref(&prepared));

        let warm = store_state(&fixture.store);
        assert_eq!(
            prepare_one(&mut fixture, &resolved[0], &read).unwrap(),
            prepared,
        );
        assert_eq!(store_state(&fixture.store), warm);
    }

    #[test]
    fn value_import_attributes_accept_identifier_and_quoted_string_entries() {
        let mut fixture = fixture(
            &[
                r#"
                    import { value } from "./target"
                        with { a: /* first */ "a", "b": /* second */ "b" };
                    const result = value;
                "#,
                "export const value: number = 1;",
            ],
            &[Route {
                source: 0,
                specifier: 0,
                target: Some(1),
            }],
        );
        let plan = fixture.plan_import(0, 0);
        assert_eq!(plan.bindings[0].local_text, "value");
        let node = identifier_initializer(&fixture, 0, "value");
        let bound = fixture.bound.get(&fixture.files[0].file).unwrap();
        let read = plan_source_import_identifier_read(
            &fixture.files[0].parsed.arena,
            bound,
            &fixture.store,
            &plan.bindings[0],
            node,
            "value",
            plan.bindings[0].alias_symbol,
        )
        .unwrap();
        let resolved = resolve_all(&mut fixture, &plan.bindings).unwrap();
        let prepared = prepare_one(&mut fixture, &resolved[0], &read).unwrap();
        assert_eq!(
            prepared.type_,
            fixture.store.intrinsic_bootstrap().unwrap().number_type,
        );
        publish_for_test(&mut fixture.store, std::slice::from_ref(&prepared));
        let warm = store_state(&fixture.store);
        assert_eq!(
            prepare_one(&mut fixture, &resolved[0], &read).unwrap(),
            prepared,
        );
        assert_eq!(store_state(&fixture.store), warm);
    }

    #[test]
    fn value_import_attributes_reject_duplicate_and_non_string_values() {
        for source in [
            r#"import { value } from "./target" with { a: "first", "a": "second" };"#,
            r#"import { value } from "./target" with { a: runtime };"#,
        ] {
            let fixture = fixture(
                &[source, "export const value: number = 1;"],
                &[Route {
                    source: 0,
                    specifier: 0,
                    target: Some(1),
                }],
            );
            let file = &fixture.files[0];
            let bound = fixture.bound.get(&file.file).unwrap();
            let declaration = file
                .parsed
                .arena
                .iter()
                .find_map(|(node, record)| {
                    (record.kind == SyntaxKind::ImportDeclaration).then_some(NodeRef::new(
                        file.parsed.arena.id(),
                        file.file,
                        node,
                    ))
                })
                .unwrap();
            let before = store_state(&fixture.store);
            assert!(matches!(
                plan_top_level_named_value_import(
                    &file.parsed.arena,
                    bound,
                    &fixture.store,
                    declaration,
                ),
                Err(SourceImportError::Unsupported(
                    SourceImportUnsupported::ImportAttributes(_)
                ))
            ));
            assert_eq!(store_state(&fixture.store), before);
        }
    }

    #[test]
    fn default_object_import_reuses_the_authenticated_published_export_value() {
        let mut fixture = fixture(
            &[
                r#"
                    import selected from "./target"
                        with { a: /* first */ "a", "b": /* second */ "b" };
                    const result = selected;
                "#,
                r#"export default { a: "a", b: "b", 1: "1" };"#,
            ],
            &[Route {
                source: 0,
                specifier: 0,
                target: Some(1),
            }],
        );
        let plan = fixture.plan_import(0, 0);
        let node = identifier_initializer(&fixture, 0, "selected");
        let bound = fixture.bound.get(&fixture.files[0].file).unwrap();
        let read = plan_source_import_identifier_read(
            &fixture.files[0].parsed.arena,
            bound,
            &fixture.store,
            &plan.bindings[0],
            node,
            "selected",
            plan.bindings[0].alias_symbol,
        )
        .unwrap();
        let resolved = resolve_all(&mut fixture, &plan.bindings).unwrap();
        let default = resolved[0].target_symbol;
        assert_eq!(
            fixture.store.symbol(default).unwrap().flags(),
            SymbolFlags::PROPERTY,
        );
        let before = store_state(&fixture.store);
        assert!(matches!(
            prepare_one(&mut fixture, &resolved[0], &read),
            Err(SourceImportError::Unsupported(
                SourceImportUnsupported::TargetDeclaration(_)
            ))
        ));
        assert_eq!(store_state(&fixture.store), before);

        let (object, type_) = {
            let Fixture {
                files,
                bound,
                store,
                ..
            } = &mut fixture;
            let sources = || {
                files.iter().map(|file| {
                    (
                        &file.parsed.arena,
                        bound.get(&file.file).expect("fixture bound every file"),
                    )
                })
            };
            let host = DeclaredTypeHost::new_after_global_merge(
                sources(),
                GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
            )
            .unwrap();
            let file = &files[1];
            let object =
                file.parsed
                    .arena
                    .iter()
                    .find_map(|(node, record)| {
                        (record.kind == SyntaxKind::ObjectLiteralExpression)
                            .then_some(NodeRef::new(file.parsed.arena.id(), file.file, node))
                    })
                    .unwrap();
            let plan =
                super::super::object_members::plan_object_literal(store, &host, object).unwrap();
            let string = store.intrinsic_bootstrap().unwrap().string_type;
            let type_ = super::super::object_members::publish_object_literal(
                store,
                &plan,
                &[string, string, string],
            )
            .unwrap();
            assert!(store.set_value_symbol_links(
                default,
                ValueSymbolLinks {
                    resolved_type: Some(type_),
                    ..ValueSymbolLinks::default()
                },
            ));
            (object, type_)
        };

        let prepared = prepare_one(&mut fixture, &resolved[0], &read).unwrap();
        assert_eq!(prepared.type_, type_);
        assert!(matches!(
            &prepared.target,
            PreparedSourceImportTarget::ExportedObject { expression } if *expression == object
        ));
        assert!(
            fixture
                .store
                .value_symbol_links(plan.bindings[0].alias_symbol)
                .is_none()
        );
        publish_for_test(&mut fixture.store, std::slice::from_ref(&prepared));
        let warm = store_state(&fixture.store);
        assert_eq!(
            prepare_one(&mut fixture, &resolved[0], &read).unwrap(),
            prepared,
        );
        assert_eq!(store_state(&fixture.store), warm);
    }

    #[test]
    fn inferred_exported_object_const_imports_reuse_published_widened_identity() {
        let mut fixture = fixture(
            &[
                "import { value } from './target'; const result = value;",
                "export const value = { name: 'ready' };",
            ],
            &[Route {
                source: 0,
                specifier: 0,
                target: Some(1),
            }],
        );
        let plan = fixture.plan_import(0, 0);
        let read_node = identifier_initializer(&fixture, 0, "value");
        let bound = fixture.bound.get(&fixture.files[0].file).unwrap();
        let read = plan_source_import_identifier_read(
            &fixture.files[0].parsed.arena,
            bound,
            &fixture.store,
            &plan.bindings[0],
            read_node,
            "value",
            plan.bindings[0].alias_symbol,
        )
        .unwrap();
        let resolved = resolve_all(&mut fixture, &plan.bindings).unwrap();
        let target = resolved[0].target_symbol;
        let cold = store_state(&fixture.store);
        assert!(matches!(
            prepare_one(&mut fixture, &resolved[0], &read),
            Err(SourceImportError::Unsupported(
                SourceImportUnsupported::MissingTargetAnnotation(_)
            ))
        ));
        assert_eq!(store_state(&fixture.store), cold);

        let (expression, expression_type, value_type, regular) = {
            let Fixture {
                files,
                bound,
                global_types,
                store,
                ..
            } = &mut fixture;
            let sources = || {
                files.iter().map(|file| {
                    (
                        &file.parsed.arena,
                        bound.get(&file.file).expect("fixture bound every file"),
                    )
                })
            };
            let host = DeclaredTypeHost::new_after_global_merge(
                sources(),
                GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
            )
            .unwrap();
            let provider = &files[1];
            let expression =
                provider
                    .parsed
                    .arena
                    .iter()
                    .find_map(|(node, record)| {
                        (record.kind == SyntaxKind::ObjectLiteralExpression).then_some(
                            NodeRef::new(provider.parsed.arena.id(), provider.file, node),
                        )
                    })
                    .unwrap();
            let object =
                super::super::object_members::plan_object_literal(store, &host, expression)
                    .unwrap();
            let regular = store.regular_string_literal_type("ready".into()).unwrap();
            let fresh = store.fresh_type_of_literal_type(regular).unwrap();
            let expression_type =
                super::super::object_members::publish_object_literal(store, &object, &[fresh])
                    .unwrap();
            let value_type = store
                .get_widened_type_with_global_types(expression_type, global_types)
                .unwrap();
            assert!(store.set_value_symbol_links(
                target,
                ValueSymbolLinks {
                    resolved_type: Some(value_type),
                    ..ValueSymbolLinks::default()
                },
            ));
            (expression, expression_type, value_type, regular)
        };

        let prepared = prepare_one(&mut fixture, &resolved[0], &read).unwrap();
        assert_eq!(prepared.type_, value_type);
        assert!(matches!(
            &prepared.target,
            PreparedSourceImportTarget::PublishedObjectConst {
                expression: actual,
                expression_type: actual_type,
            } if *actual == expression && *actual_type == expression_type
        ));
        assert_eq!(
            fixture
                .store
                .resolved_own_property(value_type, "name")
                .unwrap()
                .unwrap()
                .type_,
            regular,
        );

        publish_for_test(&mut fixture.store, std::slice::from_ref(&prepared));
        let warm = store_state(&fixture.store);
        assert_eq!(
            prepare_one(&mut fixture, &resolved[0], &read).unwrap(),
            prepared,
        );
        assert_eq!(store_state(&fixture.store), warm);
    }

    #[test]
    fn export_equals_object_import_materializes_cold_values_and_preserves_type_exports() {
        let mut fixture = fixture(
            &[
                r#"import selected = require("./target"); const result = selected;"#,
                concat!(
                    "export type Foo = { x: string }; ",
                    "export namespace Bar { export interface Baz { y: number } } ",
                    "export = { a: 1, b: 'hello' };",
                ),
            ],
            &[Route {
                source: 0,
                specifier: 0,
                target: Some(1),
            }],
        );
        let plan = fixture.try_plan_import_equals(0, 0).unwrap();
        let node = identifier_initializer(&fixture, 0, "selected");
        let bound = fixture.bound.get(&fixture.files[0].file).unwrap();
        let read = plan_source_import_identifier_read(
            &fixture.files[0].parsed.arena,
            bound,
            &fixture.store,
            &plan.bindings[0],
            node,
            "selected",
            plan.bindings[0].alias_symbol,
        )
        .unwrap();
        let resolved = resolve_all(&mut fixture, &plan.bindings).unwrap();
        let target = resolved[0].target_symbol;
        assert!(fixture.store.value_symbol_links(target).is_none());

        let target_bound = fixture.bound.get(&fixture.files[1].file).unwrap();
        let module = target_bound.symbol(target_bound.source_file()).unwrap();
        let exports = fixture.store.symbol(module).unwrap().exports().unwrap();
        let foo = fixture
            .store
            .symbol_table(exports)
            .unwrap()
            .get_source("Foo")
            .unwrap();
        let bar = fixture
            .store
            .symbol_table(exports)
            .unwrap()
            .get_source("Bar")
            .unwrap();

        let prepared = prepare_one(&mut fixture, &resolved[0], &read).unwrap();
        let PreparedSourceImportTarget::ExportedObject { expression } = &prepared.target else {
            panic!("expected an export-equals object target")
        };
        assert_eq!(
            fixture
                .store
                .value_symbol_links(target)
                .and_then(|links| links.resolved_type),
            Some(prepared.type_)
        );
        assert_eq!(
            fixture
                .store
                .type_node_links(*expression)
                .and_then(|links| links.resolved_type),
            Some(prepared.type_)
        );
        let object = fixture.store.type_payload(prepared.type_).unwrap();
        let properties = object.data().structured().unwrap().members.unwrap();
        let number = fixture.store.intrinsic_bootstrap().unwrap().number_type;
        let string = fixture.store.intrinsic_bootstrap().unwrap().string_type;
        for (name, expected) in [("a", number), ("b", string)] {
            let property = fixture
                .store
                .symbol_table(properties)
                .unwrap()
                .get_source(name)
                .unwrap();
            assert_eq!(
                fixture
                    .store
                    .value_symbol_links(property)
                    .and_then(|links| links.resolved_type),
                Some(expected)
            );
        }
        assert_eq!(
            fixture
                .store
                .symbol_table(exports)
                .unwrap()
                .get_source("Foo"),
            Some(foo)
        );
        assert_eq!(
            fixture
                .store
                .symbol_table(exports)
                .unwrap()
                .get_source("Bar"),
            Some(bar)
        );
        assert!(
            fixture
                .store
                .value_symbol_links(plan.bindings[0].alias_symbol)
                .is_none()
        );

        let warm = store_state(&fixture.store);
        assert_eq!(
            prepare_one(&mut fixture, &resolved[0], &read).unwrap(),
            prepared
        );
        assert_eq!(store_state(&fixture.store), warm);
    }

    #[test]
    fn named_value_reexport_chain_retains_each_immediate_alias_and_final_target() {
        let mut fixture = fixture(
            &[
                r#"
                    import { publicValue as localValue } from "./barrel-b";
                    const imported = localValue;
                "#,
                r#"export { intermediate as publicValue } from "./barrel-a";"#,
                r#"export { original as intermediate } from "./base";"#,
                r"export const original: number = 1;",
            ],
            &[
                Route {
                    source: 0,
                    specifier: 0,
                    target: Some(1),
                },
                Route {
                    source: 1,
                    specifier: 0,
                    target: Some(2),
                },
                Route {
                    source: 2,
                    specifier: 0,
                    target: Some(3),
                },
            ],
        );
        let import = fixture.plan_import(0, 0);
        let barrel_b = fixture.plan_reexport(1, 0);
        let barrel_a = fixture.plan_reexport(2, 0);
        assert_eq!(barrel_b.bindings[0].imported_text, "intermediate");
        assert_eq!(barrel_b.bindings[0].exported_text, "publicValue");
        assert_eq!(barrel_a.bindings[0].imported_text, "original");
        assert_eq!(barrel_a.bindings[0].exported_text, "intermediate");

        let read = identifier_initializer(&fixture, 0, "localValue");
        let bound = fixture.bound.get(&fixture.files[0].file).unwrap();
        let planned_read = plan_source_import_identifier_read(
            &fixture.files[0].parsed.arena,
            bound,
            &fixture.store,
            &import.bindings[0],
            read,
            "localValue",
            import.bindings[0].alias_symbol,
        )
        .unwrap();
        let mut resolved_imports = resolve_all(&mut fixture, &import.bindings).unwrap();
        assert_eq!(resolved_imports.len(), 1);
        let resolved = resolved_imports.pop().unwrap();
        let public_alias = direct_export(&fixture, 1, "publicValue");
        let intermediate_alias = direct_export(&fixture, 2, "intermediate");
        let base = direct_export(&fixture, 3, "original");
        assert_eq!(resolved.immediate_target_symbol, public_alias);
        assert_eq!(resolved.target_symbol, base);

        let mut resolved_barrel_b =
            resolve_all_reexports(&mut fixture, &barrel_b.bindings).unwrap();
        assert_eq!(resolved_barrel_b.len(), 1);
        let resolved_barrel_b = resolved_barrel_b.pop().unwrap();
        let mut resolved_barrel_a =
            resolve_all_reexports(&mut fixture, &barrel_a.bindings).unwrap();
        assert_eq!(resolved_barrel_a.len(), 1);
        let resolved_barrel_a = resolved_barrel_a.pop().unwrap();
        assert_eq!(
            resolved_barrel_b.immediate_target_symbol,
            intermediate_alias
        );
        assert_eq!(resolved_barrel_b.target_symbol, base);
        assert_eq!(resolved_barrel_a.immediate_target_symbol, base);
        assert_eq!(resolved_barrel_a.target_symbol, base);
        assert_eq!(resolved_barrel_b.type_only_declaration, None);
        assert_eq!(resolved_barrel_a.type_only_declaration, None);

        let prepared = prepare_one(&mut fixture, &resolved, &planned_read).unwrap();
        assert_eq!(
            prepared.type_,
            fixture.store.intrinsic_bootstrap().unwrap().number_type
        );
        assert_eq!(prepared.immediate_target_symbol, public_alias);
        assert_eq!(prepared.target_symbol, base);
        publish_for_test(&mut fixture.store, std::slice::from_ref(&prepared));

        let mut warm_imports = resolve_all(&mut fixture, &import.bindings).unwrap();
        assert_eq!(warm_imports.len(), 1);
        let warm = warm_imports.pop().unwrap();
        assert_eq!(warm, resolved);
        let warm_prepared = prepare_one(&mut fixture, &warm, &planned_read).unwrap();
        assert_eq!(warm_prepared, prepared);
    }

    #[test]
    fn type_only_reexport_marker_propagates_through_a_named_value_barrel() {
        let mut fixture = fixture(
            &[
                r#"
                    import type { PublicModel as LocalModel } from "./barrel-b";
                    const model: LocalModel = { id: 1 };
                "#,
                r#"export { IntermediateModel as PublicModel } from "./barrel-a";"#,
                r#"export type { Model as IntermediateModel } from "./base";"#,
                r"export type Model = { id: number };",
            ],
            &[
                Route {
                    source: 0,
                    specifier: 0,
                    target: Some(1),
                },
                Route {
                    source: 1,
                    specifier: 0,
                    target: Some(2),
                },
                Route {
                    source: 2,
                    specifier: 0,
                    target: Some(3),
                },
            ],
        );
        let import = fixture.plan_type_import(0, 0);
        let barrel_b = fixture.plan_reexport(1, 0);
        let barrel_a = fixture.plan_reexport(2, 0);
        assert!(!barrel_b.bindings[0].syntactic_type_only);
        assert!(barrel_a.bindings[0].syntactic_type_only);

        let public_alias = direct_export(&fixture, 1, "PublicModel");
        let intermediate_alias = direct_export(&fixture, 2, "IntermediateModel");
        let base = direct_export(&fixture, 3, "Model");

        let mut resolved_barrel_a =
            resolve_all_reexports(&mut fixture, &barrel_a.bindings).unwrap();
        assert_eq!(resolved_barrel_a.len(), 1);
        let resolved_barrel_a = resolved_barrel_a.pop().unwrap();
        assert_eq!(resolved_barrel_a.immediate_target_symbol, base);
        assert_eq!(resolved_barrel_a.target_symbol, base);
        assert_eq!(
            resolved_barrel_a.type_only_declaration,
            Some(barrel_a.bindings[0].declaration)
        );
        let mut resolved_barrel_b =
            resolve_all_reexports(&mut fixture, &barrel_b.bindings).unwrap();
        assert_eq!(resolved_barrel_b.len(), 1);
        let resolved_barrel_b = resolved_barrel_b.pop().unwrap();
        assert_eq!(
            resolved_barrel_b.immediate_target_symbol,
            intermediate_alias
        );
        assert_eq!(resolved_barrel_b.target_symbol, base);
        assert_eq!(
            resolved_barrel_b.type_only_declaration,
            Some(barrel_a.bindings[0].declaration)
        );

        let mut resolved_imports = resolve_all_types(&mut fixture, &import.bindings).unwrap();
        assert_eq!(resolved_imports.len(), 1);
        let resolved = resolved_imports.pop().unwrap();
        assert_eq!(resolved.immediate_target_symbol, public_alias);
        assert_eq!(resolved.target_symbol, base);
        assert_eq!(
            fixture
                .store
                .alias_symbol_links(import.bindings[0].alias_symbol)
                .unwrap()
                .type_only_declaration,
            Some(import.bindings[0].declaration)
        );

        let reference = type_reference(&fixture, 0, "LocalModel");
        let capability = plan_type_reference_capability(&fixture, &resolved, reference);
        let imported =
            query_type_with_import_capability(&mut fixture, reference, capability).unwrap();
        assert_eq!(
            fixture
                .store
                .type_alias_links(base)
                .and_then(|links| links.declared_type),
            Some(imported)
        );
        let mut warm_imports = resolve_all_types(&mut fixture, &import.bindings).unwrap();
        assert_eq!(warm_imports.len(), 1);
        let warm = warm_imports.pop().unwrap();
        assert_eq!(warm, resolved);
    }

    #[test]
    fn namespace_reexports_preserve_module_identity_and_type_only_markers_cold_and_warm() {
        let mut fixture = fixture(
            &[
                concat!(
                    "export * as values from './base'; ",
                    "export type * as Types from './base';",
                ),
                "export const value: number = 1; export type Model = number;",
            ],
            &[
                Route {
                    source: 0,
                    specifier: 0,
                    target: Some(1),
                },
                Route {
                    source: 0,
                    specifier: 1,
                    target: Some(1),
                },
            ],
        );
        let before_planning = store_state(&fixture.store);
        let plans = [fixture.plan_reexport(0, 0), fixture.plan_reexport(0, 1)];
        assert_eq!(store_state(&fixture.store), before_planning);

        let target = fixture.bound.get(&fixture.files[1].file).unwrap();
        let module = target.symbol(target.source_file()).unwrap();
        for (plan, (name, type_only)) in plans.into_iter().zip([("values", false), ("Types", true)])
        {
            let [binding] = plan.bindings.as_slice() else {
                panic!("expected one namespace reexport binding")
            };
            assert_eq!(binding.imported_text, "*");
            assert_eq!(binding.exported_text, name);
            assert_eq!(binding.syntactic_type_only, type_only);
            assert_eq!(
                fixture.store.source_node_kind(binding.declaration),
                Some(SyntaxKind::NamespaceExport)
            );
            assert_eq!(direct_export(&fixture, 0, name), binding.alias_symbol);
            assert!(
                fixture
                    .store
                    .alias_symbol_links(binding.alias_symbol)
                    .is_none()
            );
            assert!(
                fixture
                    .store
                    .value_symbol_links(binding.alias_symbol)
                    .is_none()
            );

            let resolved = resolve_all_reexports(&mut fixture, &plan.bindings).unwrap();
            assert_eq!(resolved.len(), 1);
            assert_eq!(resolved[0].immediate_target_symbol, module);
            assert_eq!(resolved[0].target_symbol, module);
            assert_eq!(
                resolved[0].type_only_declaration,
                type_only.then_some(binding.declaration)
            );
            assert!(
                fixture
                    .store
                    .value_symbol_links(binding.alias_symbol)
                    .is_none()
            );
            assert!(fixture.store.value_symbol_links(module).is_none());

            let warm_state = store_state(&fixture.store);
            assert_eq!(
                resolve_all_reexports(&mut fixture, &plan.bindings).unwrap(),
                resolved
            );
            assert_eq!(store_state(&fixture.store), warm_state);
        }
    }

    #[test]
    fn namespace_reexports_reject_malformed_clauses_and_redirected_alias_caches() {
        let sources = [
            r#"export * as values from "./base";"#,
            "export const value: number = 1;",
        ];
        let routes = [Route {
            source: 0,
            specifier: 0,
            target: Some(1),
        }];
        let malformed = fixture_with_module_states_and_wrapper_flags(
            &sources,
            &routes,
            &[
                CanonicalModuleState::External,
                CanonicalModuleState::External,
            ],
            Some(SyntaxKind::NamespaceExport),
            &[],
        );
        assert!(matches!(
            malformed.try_plan_reexport(0, 0),
            Err(SourceImportError::Unsupported(
                SourceImportUnsupported::ExportClause(_)
            ))
        ));

        let mut redirected = fixture(
            &[
                r#"export * as values from "./base";"#,
                "export const value: number = 1;",
                "export const other: number = 2;",
            ],
            &routes,
        );
        let plan = redirected.plan_reexport(0, 0);
        let alias = plan.bindings[0].alias_symbol;
        let wrong = redirected.bound.get(&redirected.files[2].file).unwrap();
        let wrong = wrong.symbol(wrong.source_file()).unwrap();
        assert!(redirected.store.set_alias_symbol_links(
            alias,
            AliasSymbolLinks {
                immediate_target: Some(wrong),
                alias_target: AliasTargetState::Resolved(wrong),
                ..AliasSymbolLinks::default()
            },
        ));
        assert_eq!(
            resolve_all_reexports(&mut redirected, &plan.bindings),
            Err(SourceImportError::Invariant(
                SourceImportInvariant::InvalidAliasLinks(alias)
            ))
        );
        assert!(redirected.store.value_symbol_links(alias).is_none());
    }

    #[test]
    fn star_local_and_commonjs_reexports_remain_boundaries() {
        let star = fixture(
            &[
                r#"export * from "./base";"#,
                r"export const value: number = 1;",
            ],
            &[Route {
                source: 0,
                specifier: 0,
                target: Some(1),
            }],
        );
        assert!(matches!(
            star.try_plan_reexport(0, 0),
            Err(SourceImportError::Unsupported(
                SourceImportUnsupported::ExportClause(_)
            ))
        ));

        let local = fixture(&[r"const value: number = 1; export { value };"], &[]);
        assert!(matches!(
            local.try_plan_reexport(0, 0),
            Err(SourceImportError::Unsupported(
                SourceImportUnsupported::ExportShape(_)
            ))
        ));

        let commonjs = parsed(r#"export { value } from "./base";"#);
        let commonjs_file = FileId::new(740);
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &commonjs.arena,
                commonjs.source_file,
                commonjs_file,
                facts(commonjs_file, CanonicalModuleState::CommonJs),
            )
            .unwrap();
        assert!(matches!(
            binder.bind_typescript_declaration_slice(&commonjs.arena, commonjs_file),
            Err(ts_binder::CanonicalDeclarationError::CommonJsDeclarationsDeferred(file))
                if file == commonjs_file
        ));
    }

    #[test]
    fn value_import_through_a_type_only_reexport_remains_a_typed_boundary() {
        let mut fixture = fixture(
            &[
                r#"import { PublicModel } from "./barrel";"#,
                r#"export type { Model as PublicModel } from "./base";"#,
                r"export type Model = { id: number };",
            ],
            &[
                Route {
                    source: 0,
                    specifier: 0,
                    target: Some(1),
                },
                Route {
                    source: 1,
                    specifier: 0,
                    target: Some(2),
                },
            ],
        );
        let import = fixture.plan_import(0, 0);
        let alias = import.bindings[0].alias_symbol;
        assert_eq!(
            resolve_all(&mut fixture, &import.bindings),
            Err(SourceImportError::Unsupported(
                SourceImportUnsupported::TypeOnlyAlias(alias)
            ))
        );
        let barrel = fixture.plan_reexport(1, 0);
        let mut resolved_barrels = resolve_all_reexports(&mut fixture, &barrel.bindings).unwrap();
        assert_eq!(resolved_barrels.len(), 1);
        let resolved_barrel = resolved_barrels.pop().unwrap();
        assert_eq!(
            resolved_barrel.type_only_declaration,
            Some(barrel.bindings[0].declaration)
        );
        assert_eq!(fixture.store.value_symbol_links(alias), None);
    }

    #[test]
    fn type_import_accepts_parser_owned_reparsed_commonjs_typedefs_cold_and_warm() {
        let mut fixture = javascript_commonjs_fixture(
            r#"import type { Value } from "./target.js"; const selected: Value = 1;"#,
            "/** @typedef {number} Value */\nexports.value = 1;",
            None,
        );
        let plan = fixture.plan_type_import(0, 0);
        let target = direct_export(&fixture, 1, "Value");
        let declaration = fixture
            .store
            .symbol(target)
            .unwrap()
            .declarations()
            .unwrap()[0];
        let record = fixture.files[1].parsed.arena.get(declaration.node).unwrap();
        assert_eq!(record.kind, SyntaxKind::JsTypeAliasDeclaration);
        assert_eq!(record.flags, NodeFlags::REPARSED);

        let resolved = resolve_all_types(&mut fixture, &plan.bindings).unwrap();
        assert_eq!(resolved[0].target_symbol, target);
        assert_eq!(resolved[0].target_declaration, declaration);
        assert!(fixture.store.value_symbol_links(target).is_none());
        assert!(
            fixture
                .store
                .value_symbol_links(plan.bindings[0].alias_symbol)
                .is_none()
        );

        let warm = store_state(&fixture.store);
        assert_eq!(
            resolve_all_types(&mut fixture, &plan.bindings).unwrap(),
            resolved,
        );
        assert_eq!(store_state(&fixture.store), warm);
    }

    #[test]
    fn comment_only_commonjs_jsdoc_typedef_imports_preserve_canonical_identity() {
        for exported_value in ["0", "{}"] {
            let mut fixture = javascript_jsdoc_commonjs_fixture(
                concat!(
                    "/** @typedef {import('./target').C} C */\n",
                    "/** @type {C} */\n",
                    "var c;",
                ),
                &format!(
                    "/** @typedef {{{{ a: 1, m: 1 }}}} C */\nconst value = {exported_value};\nmodule.exports = value;",
                ),
                JsDocImportManifestState::Resolved,
            );
            let before = store_state(&fixture.store);
            let plan = plan_jsdoc_typedef_import(&fixture);
            let resolved = resolve_jsdoc_typedef_import(&fixture, plan).unwrap();
            let target = direct_export(&fixture, 1, "C");
            assert_eq!(resolved.target_symbol, target);
            assert_eq!(store_state(&fixture.store), before);
            assert!(
                fixture
                    .store
                    .alias_symbol_links(plan.local_symbol)
                    .is_none()
            );
            assert!(
                fixture
                    .store
                    .value_symbol_links(plan.local_symbol)
                    .is_none()
            );
            assert!(matches!(
                query_declared_type(&mut fixture, plan.local_symbol),
                Err(DeclaredTypeError::TypeNodeUnavailable(
                    super::super::type_nodes::TypeNodeUnavailable::JsDocImportTypeCapabilityUnsupported(node)
                )) if node == plan.import_type
            ));

            let imported = query_jsdoc_typedef_import(&mut fixture, resolved).unwrap();
            assert_eq!(query_declared_type(&mut fixture, target).unwrap(), imported);
            assert_eq!(
                fixture
                    .store
                    .type_alias_links(plan.local_symbol)
                    .and_then(|links| links.declared_type),
                Some(imported),
            );
            assert_eq!(
                fixture
                    .store
                    .type_node_links(plan.import_type)
                    .and_then(|links| links.resolved_type),
                Some(imported),
            );
            assert_eq!(
                fixture
                    .store
                    .symbol_node_links(plan.imported_name)
                    .and_then(|links| links.resolved_symbol),
                Some(target),
            );
            assert!(
                fixture
                    .store
                    .alias_symbol_links(plan.local_symbol)
                    .is_none()
            );

            let warm = store_state(&fixture.store);
            assert_eq!(
                query_jsdoc_typedef_import(&mut fixture, resolved).unwrap(),
                imported,
            );
            assert_eq!(store_state(&fixture.store), warm);
        }
    }

    #[test]
    fn comment_only_jsdoc_imports_require_the_exact_resolved_manifest_node() {
        for state in [
            JsDocImportManifestState::Absent,
            JsDocImportManifestState::Unresolved,
        ] {
            let fixture = javascript_jsdoc_commonjs_fixture(
                "/** @typedef {import('./target').C} C */\nvar c;",
                "/** @typedef {number} C */\nconst value = 0;\nmodule.exports = value;",
                state,
            );
            let plan = plan_jsdoc_typedef_import(&fixture);
            let before = store_state(&fixture.store);
            let expected = match state {
                JsDocImportManifestState::Absent => {
                    CanonicalAliasTargetUnavailable::ModuleResolutionEntryAbsent(
                        plan.module_specifier,
                    )
                }
                JsDocImportManifestState::Unresolved => {
                    CanonicalAliasTargetUnavailable::ModuleResolutionUnresolved(
                        plan.module_specifier,
                    )
                }
                JsDocImportManifestState::Resolved => unreachable!(),
            };
            assert_eq!(
                resolve_jsdoc_typedef_import(&fixture, plan),
                Err(SourceImportError::Alias(
                    CanonicalAliasResolutionError::TargetUnavailable {
                        alias: plan.local_symbol,
                        reason: expected,
                    }
                )),
            );
            assert_eq!(store_state(&fixture.store), before);
            assert!(
                fixture
                    .store
                    .alias_symbol_links(plan.local_symbol)
                    .is_none()
            );
        }

        let fixture = javascript_jsdoc_commonjs_fixture(
            "/** @typedef {import('./target').C} C */\nvar c;",
            "/** @typedef {number} C */\nconst value = 0;\nmodule.exports = value;",
            JsDocImportManifestState::Resolved,
        );
        let mut plan = plan_jsdoc_typedef_import(&fixture);
        plan.module_specifier = plan.imported_name;
        assert_eq!(
            resolve_jsdoc_typedef_import(&fixture, plan),
            Err(SourceImportError::Alias(
                CanonicalAliasResolutionError::TargetUnavailable {
                    alias: plan.local_symbol,
                    reason: CanonicalAliasTargetUnavailable::MalformedDeclaration(plan.import_type,),
                }
            )),
        );

        let mut unavailable = javascript_jsdoc_commonjs_fixture(
            "/** @typedef {import('./target').C} C */\nvar c;",
            "/** @typedef {number} C */\nconst value = 0;\nmodule.exports = value;",
            JsDocImportManifestState::Resolved,
        );
        let plan = plan_jsdoc_typedef_import(&unavailable);
        unavailable.manifest = CanonicalModuleResolutionManifest::unavailable();
        assert_eq!(
            resolve_jsdoc_typedef_import(&unavailable, plan),
            Err(SourceImportError::Alias(
                CanonicalAliasResolutionError::TargetUnavailable {
                    alias: plan.local_symbol,
                    reason: CanonicalAliasTargetUnavailable::ModuleResolutionCapabilityUnavailable(
                        plan.module_specifier,
                    ),
                }
            )),
        );
    }

    #[test]
    fn comment_only_jsdoc_imports_reject_missing_qualifiers_and_forged_promoted_exports() {
        let missing = javascript_jsdoc_commonjs_fixture(
            "/** @typedef {import('./target').Missing} C */\nvar c;",
            "/** @typedef {number} C */\nconst value = 0;\nmodule.exports = value;",
            JsDocImportManifestState::Resolved,
        );
        let missing_plan = plan_jsdoc_typedef_import(&missing);
        assert_eq!(
            resolve_jsdoc_typedef_import(&missing, missing_plan),
            Err(SourceImportError::Unsupported(
                SourceImportUnsupported::TargetTypeNotExported(missing_plan.import_type)
            )),
        );

        let mut forged = javascript_jsdoc_commonjs_fixture(
            "/** @typedef {import('./target').C} C */\nvar c;",
            "/** @typedef {number} C */\nconst value = 0;\nmodule.exports = value;",
            JsDocImportManifestState::Resolved,
        );
        let plan = plan_jsdoc_typedef_import(&forged);
        let bound = forged.bound.get(&forged.files[1].file).unwrap();
        let module = bound.symbol(bound.source_file()).unwrap();
        let promoted = forged
            .store
            .symbol(module)
            .and_then(ts_binder::semantic::Symbol::exports)
            .and_then(|exports| forged.store.symbol_table(exports))
            .and_then(|exports| exports.get(InternalSymbolName::ExportEquals.as_ref()))
            .unwrap();
        assert!(
            forged
                .store
                .set_symbol_relationships(promoted, None, None, Some(module), None)
        );
        assert_eq!(
            resolve_jsdoc_typedef_import(&forged, plan),
            Err(SourceImportError::Invariant(
                SourceImportInvariant::InvalidTargetSymbol(promoted)
            )),
        );
    }

    #[test]
    fn comment_only_jsdoc_imports_reject_typeof_generic_and_qualified_shapes() {
        for expression in [
            "typeof import('./target').C",
            "import('./target').C<number>",
            "import('./target').Nested.C",
        ] {
            let fixture = javascript_jsdoc_commonjs_fixture(
                &format!("/** @typedef {{{expression}}} C */\nvar c;"),
                "/** @typedef {number} C */\nconst value = 0;\nmodule.exports = value;",
                JsDocImportManifestState::Resolved,
            );
            let file = &fixture.files[0];
            let bound = fixture.bound.get(&file.file).unwrap();
            let jsdoc =
                plan_javascript_source_jsdoc(&file.parsed.arena, bound.source_file()).unwrap();
            let declaration = jsdoc.declarations().first().unwrap();
            let typedef = declaration.typedefs().first().unwrap();
            let JsDocType::Import(imported) = typedef.type_().unwrap().type_() else {
                panic!("the malformed shape still projects as a JSDoc import")
            };

            assert!(matches!(
                plan_source_jsdoc_typedef_import(
                    &file.parsed.arena,
                    bound,
                    &fixture.store,
                    declaration.node(),
                    typedef.source_declaration().unwrap(),
                    imported,
                ),
                Err(SourceImportError::Unsupported(
                    SourceImportUnsupported::TypeReference(_)
                )),
                "unsupported JSDoc import expression: {expression}",
            ));
        }
    }

    #[test]
    fn comment_only_jsdoc_imports_reject_foreign_targets_and_poisoned_caches() {
        for poisoned in 0..4 {
            let mut fixture = javascript_jsdoc_commonjs_fixture(
                "/** @typedef {import('./target').C} C */\nvar c;",
                "/** @typedef {number} C */\nconst value = 0;\nmodule.exports = value;",
                JsDocImportManifestState::Resolved,
            );
            let plan = plan_jsdoc_typedef_import(&fixture);
            let mut resolved = resolve_jsdoc_typedef_import(&fixture, plan).unwrap();
            let wrong = fixture.store.intrinsic_bootstrap().unwrap().string_type;
            match poisoned {
                0 => resolved.target_declaration = plan.local_declaration,
                1 => assert!(fixture.store.set_type_alias_links(
                    plan.local_symbol,
                    TypeAliasLinks {
                        declared_type: Some(wrong),
                        ..TypeAliasLinks::default()
                    },
                )),
                2 => assert!(fixture.store.set_type_node_links(
                    plan.import_type,
                    TypeNodeLinks {
                        resolved_type: Some(wrong),
                        ..TypeNodeLinks::default()
                    },
                )),
                3 => assert!(fixture.store.set_symbol_node_links(
                    plan.imported_name,
                    SymbolNodeLinks {
                        resolved_symbol: Some(plan.local_symbol),
                    },
                )),
                _ => unreachable!(),
            }

            assert!(matches!(
                query_jsdoc_typedef_import(&mut fixture, resolved),
                Err(DeclaredTypeError::TypeNodeUnavailable(
                    super::super::type_nodes::TypeNodeUnavailable::InvalidJsDocImportTypeTarget {
                        node,
                        alias,
                        target,
                    }
                )) if node == plan.import_type
                    && alias == plan.local_symbol
                    && target == resolved.target_symbol,
            ));
            assert!(
                fixture
                    .store
                    .alias_symbol_links(plan.local_symbol)
                    .is_none()
            );
            assert!(
                fixture
                    .store
                    .value_symbol_links(plan.local_symbol)
                    .is_none()
            );
        }
    }

    #[test]
    fn comment_only_jsdoc_imports_recheck_warm_import_node_identity() {
        let mut fixture = javascript_jsdoc_commonjs_fixture(
            "/** @typedef {import('./target').C} C */\nvar c;",
            "/** @typedef {number} C */\nconst value = 0;\nmodule.exports = value;",
            JsDocImportManifestState::Resolved,
        );
        let plan = plan_jsdoc_typedef_import(&fixture);
        let resolved = resolve_jsdoc_typedef_import(&fixture, plan).unwrap();
        let imported = query_jsdoc_typedef_import(&mut fixture, resolved).unwrap();
        let wrong = fixture.store.intrinsic_bootstrap().unwrap().string_type;
        assert_ne!(imported, wrong);
        assert!(fixture.store.set_type_node_links(
            plan.import_type,
            TypeNodeLinks {
                resolved_type: Some(wrong),
                ..TypeNodeLinks::default()
            },
        ));

        assert!(matches!(
            query_jsdoc_typedef_import(&mut fixture, resolved),
            Err(DeclaredTypeError::TypeNodeUnavailable(
                super::super::type_nodes::TypeNodeUnavailable::InvalidJsDocImportTypeTarget {
                    node,
                    alias,
                    target,
                }
            )) if node == plan.import_type
                && alias == plan.local_symbol
                && target == resolved.target_symbol,
        ));
        assert_eq!(
            fixture
                .store
                .type_alias_links(plan.local_symbol)
                .and_then(|links| links.declared_type),
            Some(imported),
        );
    }

    #[test]
    fn commonjs_default_import_authenticates_export_equals_with_promoted_typedefs() {
        let mut fixture = javascript_commonjs_fixture(
            r#"import selected from "./target.js"; const copied = selected;"#,
            concat!(
                "/** @typedef {number} Value */\n",
                "/** @type {number} */\n",
                "const local = 1;\n",
                "module.exports = local;",
            ),
            None,
        );
        let plan = fixture.plan_import(0, 0);
        let target_bound = fixture.bound.get(&fixture.files[1].file).unwrap();
        let module = target_bound.symbol(target_bound.source_file()).unwrap();
        let module_exports = fixture.store.symbol(module).unwrap().exports().unwrap();
        let promoted = fixture
            .store
            .symbol_table(module_exports)
            .and_then(|exports| exports.get(InternalSymbolName::ExportEquals.as_ref()))
            .unwrap();
        let promoted_record = fixture.store.symbol(promoted).unwrap();
        let exported_type = direct_export(&fixture, 1, "Value");
        assert_eq!(
            promoted_record.flags(),
            SymbolFlags::ALIAS | SymbolFlags::NAMESPACE_MODULE,
        );
        assert_eq!(
            promoted_record
                .exports()
                .and_then(|exports| fixture.store.symbol_table(exports))
                .and_then(|exports| exports.get_source("Value")),
            Some(exported_type),
        );
        assert_eq!(
            source_import_target_is_authenticated_alias(&fixture.store, promoted),
            Ok(true),
        );

        let resolved = resolve_all(&mut fixture, &plan.bindings).unwrap();
        let [resolved] = resolved.as_slice() else {
            panic!("expected one CommonJS default import")
        };
        let target_bound = fixture.bound.get(&fixture.files[1].file).unwrap();
        let local = target_bound
            .locals(target_bound.source_file())
            .and_then(|locals| fixture.store.symbol_table(locals))
            .and_then(|locals| locals.get_source("local"))
            .unwrap();
        assert_eq!(resolved.immediate_target_symbol, promoted);
        assert_eq!(resolved.target_symbol, local);
        assert_eq!(
            fixture
                .store
                .symbol(promoted)
                .and_then(ts_binder::semantic::Symbol::exports)
                .and_then(|exports| fixture.store.symbol_table(exports))
                .and_then(|exports| exports.get_source("Value")),
            Some(exported_type),
        );

        let node = identifier_initializer(&fixture, 0, "selected");
        let bound = fixture.bound.get(&fixture.files[0].file).unwrap();
        let read = plan_source_import_identifier_read(
            &fixture.files[0].parsed.arena,
            bound,
            &fixture.store,
            &plan.bindings[0],
            node,
            "selected",
            plan.bindings[0].alias_symbol,
        )
        .unwrap();
        let prepared = prepare_one(&mut fixture, resolved, &read).unwrap();
        assert_eq!(
            prepared.type_,
            fixture.store.intrinsic_bootstrap().unwrap().number_type,
        );
        publish_for_test(&mut fixture.store, std::slice::from_ref(&prepared));

        let warm = store_state(&fixture.store);
        assert_eq!(
            resolve_all(&mut fixture, &plan.bindings).unwrap(),
            vec![resolved.clone()],
        );
        assert_eq!(
            prepare_one(&mut fixture, resolved, &read).unwrap(),
            prepared
        );
        assert_eq!(store_state(&fixture.store), warm);
    }

    #[test]
    fn commonjs_promoted_export_alias_rejects_forged_type_export_tables() {
        let mut fixture = javascript_commonjs_fixture(
            r#"import selected from "./target.js";"#,
            concat!(
                "/** @typedef {number} Value */\n",
                "const local = 1;\n",
                "module.exports = local;",
            ),
            None,
        );
        let plan = fixture.plan_import(0, 0);
        let target_bound = fixture.bound.get(&fixture.files[1].file).unwrap();
        let module = target_bound.symbol(target_bound.source_file()).unwrap();
        let promoted = fixture
            .store
            .symbol(module)
            .and_then(ts_binder::semantic::Symbol::exports)
            .and_then(|exports| fixture.store.symbol_table(exports))
            .and_then(|exports| exports.get(InternalSymbolName::ExportEquals.as_ref()))
            .unwrap();
        assert!(
            fixture
                .store
                .set_symbol_relationships(promoted, None, None, Some(module), None,)
        );

        assert_eq!(
            source_import_target_is_authenticated_alias(&fixture.store, promoted),
            Err(SourceImportError::Invariant(
                SourceImportInvariant::InvalidTargetSymbol(promoted),
            )),
        );
        assert_eq!(
            resolve_all(&mut fixture, &plan.bindings),
            Err(SourceImportError::Invariant(
                SourceImportInvariant::InvalidTargetSymbol(promoted),
            )),
        );
        assert!(
            fixture
                .store
                .value_symbol_links(plan.bindings[0].alias_symbol)
                .is_none()
        );
    }

    #[test]
    fn commonjs_typedef_import_rejects_missing_and_foreign_parser_flags() {
        for flags in [
            NodeFlags(0),
            NodeFlags(NodeFlags::REPARSED.0 | NodeFlags::JAVASCRIPT_FILE.0),
        ] {
            let fixture = javascript_commonjs_fixture(
                r#"import type { Value } from "./target.js";"#,
                "/** @typedef {number} Value */\nexports.value = 1;",
                Some(flags),
            );
            let plan = fixture.plan_type_import(0, 0);
            let target = direct_export(&fixture, 1, "Value");
            let declaration = fixture
                .store
                .symbol(target)
                .unwrap()
                .declarations()
                .unwrap()[0];
            let sources = || {
                fixture
                    .files
                    .iter()
                    .map(|file| (&file.parsed.arena, fixture.bound.get(&file.file).unwrap()))
            };
            let host = DeclaredTypeHost::new_after_global_merge(
                sources(),
                GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
            )
            .unwrap();
            let before = store_state(&fixture.store);

            assert_eq!(
                plan_direct_exported_type_target(
                    &fixture.store,
                    &host,
                    plan.bindings[0].alias_symbol,
                    target,
                ),
                Err(SourceImportError::Unsupported(
                    SourceImportUnsupported::TargetTypeDeclaration(declaration),
                )),
                "flags={flags:?}",
            );
            assert_eq!(store_state(&fixture.store), before);
        }
    }

    #[test]
    fn commonjs_named_import_resolves_annotated_function_scoped_local_cold_and_warm() {
        let mut fixture = javascript_commonjs_fixture(
            r#"import { value } from "./target.js"; const copied = value;"#,
            "/** @type {number} */\nvar local = 1;\nexports.value = local;",
            None,
        );
        let plan = fixture.plan_import(0, 0);
        let node = identifier_initializer(&fixture, 0, "value");
        let bound = fixture.bound.get(&fixture.files[0].file).unwrap();
        let read = plan_source_import_identifier_read(
            &fixture.files[0].parsed.arena,
            bound,
            &fixture.store,
            &plan.bindings[0],
            node,
            "value",
            plan.bindings[0].alias_symbol,
        )
        .unwrap();
        let resolved = resolve_all(&mut fixture, &plan.bindings).unwrap();
        let target = resolved[0].target_symbol;
        assert_eq!(
            fixture.store.symbol(target).unwrap().flags(),
            SymbolFlags::FUNCTION_SCOPED_VARIABLE,
        );

        let prepared = prepare_one(&mut fixture, &resolved[0], &read).unwrap();
        assert_eq!(
            prepared.type_,
            fixture.store.intrinsic_bootstrap().unwrap().number_type,
        );
        assert!(matches!(
            &prepared.target,
            PreparedSourceImportTarget::JavaScriptAnnotatedConst {
                annotation: Some(_)
            }
        ));
        publish_for_test(&mut fixture.store, std::slice::from_ref(&prepared));
        let warm = store_state(&fixture.store);
        assert_eq!(
            prepare_one(&mut fixture, &resolved[0], &read).unwrap(),
            prepared
        );
        assert_eq!(store_state(&fixture.store), warm);
    }

    #[test]
    fn commonjs_named_import_uses_authenticated_assignment_value_caches() {
        let mut fixture = javascript_commonjs_fixture(
            r#"import { value } from "./target.js"; const copied = value;"#,
            "exports.value = 1;",
            None,
        );
        let plan = fixture.plan_import(0, 0);
        let node = identifier_initializer(&fixture, 0, "value");
        let bound = fixture.bound.get(&fixture.files[0].file).unwrap();
        let read = plan_source_import_identifier_read(
            &fixture.files[0].parsed.arena,
            bound,
            &fixture.store,
            &plan.bindings[0],
            node,
            "value",
            plan.bindings[0].alias_symbol,
        )
        .unwrap();
        let resolved = resolve_all(&mut fixture, &plan.bindings).unwrap();
        let target = resolved[0].target_symbol;
        let declaration = fixture
            .store
            .symbol(target)
            .unwrap()
            .value_declaration()
            .unwrap();

        assert_eq!(
            prepare_one(&mut fixture, &resolved[0], &read),
            Err(SourceImportError::Unsupported(
                SourceImportUnsupported::MissingTargetAnnotation(declaration),
            )),
        );
        let NodeData::BinaryExpression(assignment) = &fixture.files[1]
            .parsed
            .arena
            .get(declaration.node)
            .unwrap()
            .data
        else {
            panic!("expected one authenticated CommonJS export assignment")
        };
        let right = NodeRef::new(declaration.arena, declaration.file, assignment.right);
        let left = NodeRef::new(declaration.arena, declaration.file, assignment.left);
        let number = fixture.store.intrinsic_bootstrap().unwrap().number_type;
        for node in [right, left, declaration] {
            assert!(fixture.store.set_type_node_links(
                node,
                TypeNodeLinks {
                    resolved_type: Some(number),
                    ..TypeNodeLinks::default()
                },
            ));
        }

        let prepared = prepare_one(&mut fixture, &resolved[0], &read).unwrap();
        assert_eq!(prepared.type_, number);
        assert!(matches!(
            &prepared.target,
            PreparedSourceImportTarget::CommonJsNamedExport { assignments }
                if assignments.as_slice() == [CommonJsNamedExportAssignment {
                    expression: declaration,
                    left,
                    right,
                }].as_slice()
        ));
        assert!(fixture.store.value_symbol_links(target).is_none());
        publish_for_test(&mut fixture.store, std::slice::from_ref(&prepared));
        let warm = store_state(&fixture.store);
        assert_eq!(
            prepare_one(&mut fixture, &resolved[0], &read).unwrap(),
            prepared
        );
        assert_eq!(store_state(&fixture.store), warm);
    }

    #[test]
    fn repeated_commonjs_exports_reuse_the_published_widened_symbol_type() {
        let mut fixture = javascript_commonjs_fixture(
            r#"import { value } from "./target.js"; const copied = value;"#,
            "exports.value = 1; exports.value = 'updated';",
            None,
        );
        let plan = fixture.plan_import(0, 0);
        let node = identifier_initializer(&fixture, 0, "value");
        let bound = fixture.bound.get(&fixture.files[0].file).unwrap();
        let read = plan_source_import_identifier_read(
            &fixture.files[0].parsed.arena,
            bound,
            &fixture.store,
            &plan.bindings[0],
            node,
            "value",
            plan.bindings[0].alias_symbol,
        )
        .unwrap();
        let resolved = resolve_all(&mut fixture, &plan.bindings).unwrap();
        let target = resolved[0].target_symbol;
        let declarations = fixture
            .store
            .symbol(target)
            .unwrap()
            .declarations()
            .unwrap()
            .to_vec();
        assert_eq!(declarations.len(), 2);
        let regular_number = fixture
            .store
            .regular_number_literal_type(ts_jsnum::Number::new(1.0))
            .unwrap();
        let fresh_number = fixture
            .store
            .fresh_type_of_literal_type(regular_number)
            .unwrap();
        let regular_string = fixture
            .store
            .regular_string_literal_type("updated".to_owned())
            .unwrap();
        let fresh_string = fixture
            .store
            .fresh_type_of_literal_type(regular_string)
            .unwrap();
        for (declaration, type_) in declarations
            .iter()
            .copied()
            .zip([fresh_number, fresh_string])
        {
            let NodeData::BinaryExpression(assignment) = &fixture.files[1]
                .parsed
                .arena
                .get(declaration.node)
                .unwrap()
                .data
            else {
                panic!("expected repeated authenticated CommonJS export assignments")
            };
            for node in [
                NodeRef::new(declaration.arena, declaration.file, assignment.right),
                NodeRef::new(declaration.arena, declaration.file, assignment.left),
                declaration,
            ] {
                assert!(fixture.store.set_type_node_links(
                    node,
                    TypeNodeLinks {
                        resolved_type: Some(type_),
                        ..TypeNodeLinks::default()
                    },
                ));
            }
        }

        assert_eq!(
            prepare_one(&mut fixture, &resolved[0], &read),
            Err(SourceImportError::Unsupported(
                SourceImportUnsupported::MissingTargetAnnotation(declarations[0]),
            )),
        );
        let union = fixture
            .store
            .expression_union_type_with_global_types(
                &fixture.global_types,
                &[regular_number, regular_string],
                UnionReduction::Literal,
            )
            .unwrap();
        assert!(fixture.store.set_value_symbol_links(
            target,
            ValueSymbolLinks {
                resolved_type: Some(union),
                ..ValueSymbolLinks::default()
            },
        ));

        let prepared = prepare_one(&mut fixture, &resolved[0], &read).unwrap();
        assert_eq!(prepared.type_, union);
        publish_for_test(&mut fixture.store, std::slice::from_ref(&prepared));
        let warm = store_state(&fixture.store);
        assert_eq!(
            prepare_one(&mut fixture, &resolved[0], &read).unwrap(),
            prepared
        );
        assert_eq!(store_state(&fixture.store), warm);
    }

    #[test]
    fn repeated_annotated_commonjs_exports_preserve_distinct_assignment_caches() {
        let mut fixture = javascript_commonjs_fixture(
            r#"import { value } from "./target.js"; const copied = value;"#,
            concat!(
                "exports.value = 1;\n",
                "/** @type {string} */\n",
                "exports.value = 'ready';\n",
                "/** @type {boolean} */\n",
                "exports.value = true;",
            ),
            None,
        );
        let plan = fixture.plan_import(0, 0);
        let node = identifier_initializer(&fixture, 0, "value");
        let bound = fixture.bound.get(&fixture.files[0].file).unwrap();
        let read = plan_source_import_identifier_read(
            &fixture.files[0].parsed.arena,
            bound,
            &fixture.store,
            &plan.bindings[0],
            node,
            "value",
            plan.bindings[0].alias_symbol,
        )
        .unwrap();
        let resolved = resolve_all(&mut fixture, &plan.bindings).unwrap();
        let target = resolved[0].target_symbol;
        let declarations = fixture
            .store
            .symbol(target)
            .unwrap()
            .declarations()
            .unwrap()
            .to_vec();
        let (number, string, boolean, regular_true) = {
            let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
            (
                bootstrap.number_type,
                bootstrap.string_type,
                bootstrap.boolean_type,
                bootstrap.regular_true_type,
            )
        };
        let regular_number = fixture
            .store
            .regular_number_literal_type(ts_jsnum::Number::new(1.0))
            .unwrap();
        let regular_string = fixture
            .store
            .regular_string_literal_type("ready".to_owned())
            .unwrap();
        let literal_types = [regular_number, regular_string, regular_true]
            .map(|regular| fixture.store.fresh_type_of_literal_type(regular).unwrap());
        assert!(fixture.store.set_value_symbol_links(
            target,
            ValueSymbolLinks {
                resolved_type: Some(string),
                ..ValueSymbolLinks::default()
            },
        ));
        for ((declaration, literal), assigned) in declarations
            .iter()
            .copied()
            .zip(literal_types)
            .zip([number, string, boolean])
        {
            let NodeData::BinaryExpression(assignment) = &fixture.files[1]
                .parsed
                .arena
                .get(declaration.node)
                .unwrap()
                .data
            else {
                panic!("expected repeated annotated CommonJS export assignments")
            };
            for (node, type_) in [
                (
                    NodeRef::new(declaration.arena, declaration.file, assignment.right),
                    literal,
                ),
                (
                    NodeRef::new(declaration.arena, declaration.file, assignment.left),
                    string,
                ),
                (declaration, assigned),
            ] {
                assert!(fixture.store.set_type_node_links(
                    node,
                    TypeNodeLinks {
                        resolved_type: Some(type_),
                        ..TypeNodeLinks::default()
                    },
                ));
            }
        }

        let prepared = prepare_one(&mut fixture, &resolved[0], &read).unwrap();
        assert_eq!(prepared.type_, string);
        assert!(matches!(
            &prepared.target,
            PreparedSourceImportTarget::CommonJsNamedExport { assignments }
                if assignments.len() == 3
        ));
        publish_for_test(&mut fixture.store, std::slice::from_ref(&prepared));
        let warm = store_state(&fixture.store);
        assert_eq!(
            prepare_one(&mut fixture, &resolved[0], &read).unwrap(),
            prepared
        );
        assert_eq!(store_state(&fixture.store), warm);
    }

    #[test]
    fn commonjs_named_import_rejects_forged_assignment_literal_caches() {
        let mut fixture = javascript_commonjs_fixture(
            r#"import { value } from "./target.js"; const copied = value;"#,
            "exports.value = 1;",
            None,
        );
        let plan = fixture.plan_import(0, 0);
        let node = identifier_initializer(&fixture, 0, "value");
        let bound = fixture.bound.get(&fixture.files[0].file).unwrap();
        let read = plan_source_import_identifier_read(
            &fixture.files[0].parsed.arena,
            bound,
            &fixture.store,
            &plan.bindings[0],
            node,
            "value",
            plan.bindings[0].alias_symbol,
        )
        .unwrap();
        let resolved = resolve_all(&mut fixture, &plan.bindings).unwrap();
        let target = resolved[0].target_symbol;
        let declaration = fixture
            .store
            .symbol(target)
            .unwrap()
            .value_declaration()
            .unwrap();
        let NodeData::BinaryExpression(assignment) = &fixture.files[1]
            .parsed
            .arena
            .get(declaration.node)
            .unwrap()
            .data
        else {
            panic!("expected one CommonJS export assignment")
        };
        let right = NodeRef::new(declaration.arena, declaration.file, assignment.right);
        let left = NodeRef::new(declaration.arena, declaration.file, assignment.left);
        let regular_one = fixture
            .store
            .regular_number_literal_type(ts_jsnum::Number::new(1.0))
            .unwrap();
        let fresh_one = fixture
            .store
            .fresh_type_of_literal_type(regular_one)
            .unwrap();
        let regular_two = fixture
            .store
            .regular_number_literal_type(ts_jsnum::Number::new(2.0))
            .unwrap();
        let fresh_two = fixture
            .store
            .fresh_type_of_literal_type(regular_two)
            .unwrap();
        assert!(fixture.store.set_value_symbol_links(
            target,
            ValueSymbolLinks {
                resolved_type: Some(regular_one),
                ..ValueSymbolLinks::default()
            },
        ));
        for (node, type_) in [
            (right, fresh_one),
            (left, fresh_one),
            (declaration, fresh_two),
        ] {
            assert!(fixture.store.set_type_node_links(
                node,
                TypeNodeLinks {
                    resolved_type: Some(type_),
                    ..TypeNodeLinks::default()
                },
            ));
        }

        assert_eq!(
            prepare_one(&mut fixture, &resolved[0], &read),
            Err(SourceImportError::Invariant(
                SourceImportInvariant::CachedTypeMismatch {
                    symbol: target,
                    cached: fresh_one,
                    expected: fresh_two,
                },
            )),
        );
        assert!(
            fixture
                .store
                .value_symbol_links(plan.bindings[0].alias_symbol)
                .is_none()
        );
    }

    #[test]
    fn commonjs_named_import_rejects_foreign_variable_flags() {
        let mut fixture = javascript_commonjs_fixture(
            r#"import { value } from "./target.js"; const copied = value;"#,
            "exports.value = 1;",
            None,
        );
        let plan = fixture.plan_import(0, 0);
        let node = identifier_initializer(&fixture, 0, "value");
        let bound = fixture.bound.get(&fixture.files[0].file).unwrap();
        let read = plan_source_import_identifier_read(
            &fixture.files[0].parsed.arena,
            bound,
            &fixture.store,
            &plan.bindings[0],
            node,
            "value",
            plan.bindings[0].alias_symbol,
        )
        .unwrap();
        let resolved = resolve_all(&mut fixture, &plan.bindings).unwrap();
        let target = resolved[0].target_symbol;
        let flags = SymbolFlags::FUNCTION_SCOPED_VARIABLE | SymbolFlags::MODULE_EXPORTS;
        assert!(
            fixture
                .store
                .set_symbol_flags(target, flags, CheckFlags::NONE)
        );

        assert_eq!(
            prepare_one(&mut fixture, &resolved[0], &read),
            Err(SourceImportError::Unsupported(
                SourceImportUnsupported::TargetSymbol {
                    alias: plan.bindings[0].alias_symbol,
                    target,
                    flags,
                },
            )),
        );
        assert!(
            fixture
                .store
                .value_symbol_links(plan.bindings[0].alias_symbol)
                .is_none()
        );
    }

    #[test]
    fn type_only_alias_import_is_exact_in_importer_first_cold_and_warm_orders() {
        let mut fixture = fixture(
            &[
                r#"
                    import type { User as LocalUser } from "./target";
                    const user: LocalUser = { id: 1 };
                "#,
                r"export type User = { id: number };",
            ],
            &[Route {
                source: 0,
                specifier: 0,
                target: Some(1),
            }],
        );
        let plan = fixture.plan_type_import(0, 0);
        assert_eq!(plan.bindings.len(), 1);
        assert_eq!(plan.bindings[0].imported_text, "User");
        assert_eq!(plan.bindings[0].local_text, "LocalUser");
        let reference = type_reference(&fixture, 0, "LocalUser");
        let resolved = resolve_all_types(&mut fixture, &plan.bindings).unwrap();
        let capability = plan_type_reference_capability(&fixture, &resolved[0], reference);
        let imported =
            query_type_with_import_capability(&mut fixture, reference, capability).unwrap();
        let target = direct_export(&fixture, 1, "User");
        assert_eq!(
            fixture
                .store
                .type_alias_links(target)
                .and_then(|links| links.declared_type),
            Some(imported)
        );
        assert_eq!(
            fixture
                .store
                .symbol_node_links(reference)
                .and_then(|links| links.resolved_symbol),
            Some(target)
        );
        assert_eq!(
            fixture
                .store
                .value_symbol_links(plan.bindings[0].alias_symbol),
            None
        );

        let warm_resolved = resolve_all_types(&mut fixture, &plan.bindings).unwrap();
        assert_eq!(warm_resolved, resolved);
        let warm_capability =
            plan_type_reference_capability(&fixture, &warm_resolved[0], reference);
        assert_eq!(
            query_type_with_import_capability(&mut fixture, reference, warm_capability).unwrap(),
            imported
        );
    }

    #[test]
    fn warmed_imported_type_still_requires_its_exact_capability() {
        let mut fixture = fixture(
            &[
                r#"
                    import type { User } from "./target";
                    const user: User = { id: 1 };
                "#,
                r"export type User = { id: number };",
            ],
            &[Route {
                source: 0,
                specifier: 0,
                target: Some(1),
            }],
        );
        let plan = fixture.plan_type_import(0, 0);
        let reference = type_reference(&fixture, 0, "User");
        let resolved = resolve_all_types(&mut fixture, &plan.bindings).unwrap();
        let capability = plan_type_reference_capability(&fixture, &resolved[0], reference);
        query_type_with_import_capability(&mut fixture, reference, capability).unwrap();

        let before = store_state(&fixture.store);
        assert!(matches!(
            query_type_without_import_capability(&mut fixture, reference),
            Err(DeclaredTypeError::TypeNodeUnavailable(
                super::super::type_nodes::TypeNodeUnavailable::ImportAliasTypeReference {
                    node,
                    alias,
                }
            )) if node == reference && alias == plan.bindings[0].alias_symbol
        ));
        assert_eq!(store_state(&fixture.store), before);
    }

    fn assert_warmed_composite_root_requires_exact_import_capability(
        fixture: &mut Fixture,
        variable: &str,
    ) {
        let plan = fixture.plan_type_import(0, 0);
        let root = variable_type_node(fixture, 0, variable);
        let reference = type_reference(fixture, 0, "User");
        let resolved = resolve_all_types(fixture, &plan.bindings).unwrap();
        let capability =
            plan_type_reference_capability_for_root(fixture, &resolved[0], root, reference);
        query_type_with_import_capability(fixture, root, capability).unwrap();

        let warm = store_state(&fixture.store);
        assert!(matches!(
            query_type_without_import_capability(fixture, root),
            Err(DeclaredTypeError::TypeNodeUnavailable(
                super::super::type_nodes::TypeNodeUnavailable::ImportAliasTypeReference {
                    node,
                    alias,
                }
            )) if node == reference && alias == plan.bindings[0].alias_symbol
        ));
        assert_eq!(store_state(&fixture.store), warm);
    }

    #[test]
    fn warmed_composite_import_roots_do_not_retain_capabilities() {
        for source in [
            r#"
                import type { User } from "./target";
                const value: User | null = null;
            "#,
            r#"
                import type { User } from "./target";
                const value: (User | null) = null;
            "#,
            r#"
                import type { User } from "./target";
                const value: User[] = [];
            "#,
        ] {
            let mut fixture = fixture(
                &[source, r"export type User = number;"],
                &[Route {
                    source: 0,
                    specifier: 0,
                    target: Some(1),
                }],
            );
            assert_warmed_composite_root_requires_exact_import_capability(&mut fixture, "value");
        }

        let mut initialized_array = fixture_with_module_states(
            &[
                r#"
                    import type { User } from "./target";
                    const value: User[] = [];
                "#,
                r"export type User = number;",
                r"interface Array<T> {} interface ReadonlyArray<T> {}",
            ],
            &[Route {
                source: 0,
                specifier: 0,
                target: Some(1),
            }],
            &[
                CanonicalModuleState::External,
                CanonicalModuleState::External,
                CanonicalModuleState::Script,
            ],
        );
        assert!(
            initialized_array
                .store
                .type_payload(initialized_array.global_types.array_type)
                .unwrap()
                .symbol()
                .is_some(),
            "the initialized-array case must use the global Array<T> interface"
        );
        assert_warmed_composite_root_requires_exact_import_capability(
            &mut initialized_array,
            "value",
        );
    }

    #[test]
    fn composite_import_capability_roots_reject_nonzero_wrapper_flags() {
        for kind in [
            SyntaxKind::UnionType,
            SyntaxKind::ParenthesizedType,
            SyntaxKind::ArrayType,
        ] {
            let mut fixture = fixture_with_module_states_and_wrapper_flags(
                &[
                    r#"
                        import type { User } from "./target";
                        const value: (User | null)[] = [];
                    "#,
                    r"export type User = number;",
                ],
                &[Route {
                    source: 0,
                    specifier: 0,
                    target: Some(1),
                }],
                &[
                    CanonicalModuleState::External,
                    CanonicalModuleState::External,
                ],
                Some(kind),
                &[],
            );
            let plan = fixture.plan_type_import(0, 0);
            let root = variable_type_node(&fixture, 0, "value");
            let reference = type_reference(&fixture, 0, "User");
            let resolved = resolve_all_types(&mut fixture, &plan.bindings).unwrap();
            let capability =
                plan_type_reference_capability_for_root(&fixture, &resolved[0], root, reference);
            let before = store_state(&fixture.store);
            assert!(matches!(
                query_type_with_import_capability(&mut fixture, root, capability),
                Err(DeclaredTypeError::TypeNodeUnavailable(
                    super::super::type_nodes::TypeNodeUnavailable::ImportAliasCapabilityUnsupported(
                        node
                    )
                )) if node == reference
            ));
            assert_eq!(store_state(&fixture.store), before);
        }
    }

    #[test]
    fn type_import_capability_cannot_authorize_an_enclosing_union_query() {
        let mut fixture = fixture(
            &[
                r#"
                    import type { User } from "./target";
                    const user: User | null = null;
                "#,
                r"export type User = { id: number };",
            ],
            &[Route {
                source: 0,
                specifier: 0,
                target: Some(1),
            }],
        );
        let plan = fixture.plan_type_import(0, 0);
        let reference = type_reference(&fixture, 0, "User");
        let resolved = resolve_all_types(&mut fixture, &plan.bindings).unwrap();
        let capability = plan_type_reference_capability(&fixture, &resolved[0], reference);
        let union = {
            let file = &fixture.files[0];
            file.parsed
                .arena
                .iter()
                .find_map(|(node, record)| {
                    (record.kind == SyntaxKind::UnionType).then_some(NodeRef::new(
                        file.parsed.arena.id(),
                        file.file,
                        node,
                    ))
                })
                .expect("fixture contains a union annotation")
        };

        let before = store_state(&fixture.store);
        assert!(matches!(
            query_type_with_import_capability(&mut fixture, union, capability),
            Err(DeclaredTypeError::TypeNodeUnavailable(
                super::super::type_nodes::TypeNodeUnavailable::ImportAliasCapabilityUnsupported(
                    node
                )
            )) if node == reference
        ));
        assert_eq!(store_state(&fixture.store), before);
    }

    #[test]
    fn composite_import_root_revalidates_warm_leaf_capabilities_and_poison() {
        let mut fixture = fixture(
            &[
                r#"
                    import type { User } from "./target";
                    const users: (User | null)[] = [];
                "#,
                r"export type User = number;",
            ],
            &[Route {
                source: 0,
                specifier: 0,
                target: Some(1),
            }],
        );
        let plan = fixture.plan_type_import(0, 0);
        let root = variable_type_node(&fixture, 0, "users");
        let reference = type_reference(&fixture, 0, "User");
        let resolved = resolve_all_types(&mut fixture, &plan.bindings).unwrap();
        let capability =
            plan_type_reference_capability_for_root(&fixture, &resolved[0], root, reference);
        let resolved_root =
            query_type_with_import_capability(&mut fixture, root, capability).unwrap();
        let warm = store_state(&fixture.store);
        let warm_capability =
            plan_type_reference_capability_for_root(&fixture, &resolved[0], root, reference);
        assert_eq!(
            query_type_with_import_capability(&mut fixture, root, warm_capability),
            Ok(resolved_root)
        );
        assert_eq!(store_state(&fixture.store), warm);

        let leaf_only = plan_type_reference_capability(&fixture, &resolved[0], reference);
        assert!(matches!(
            query_type_with_import_capability(&mut fixture, root, leaf_only),
            Err(DeclaredTypeError::TypeNodeUnavailable(
                super::super::type_nodes::TypeNodeUnavailable::ImportAliasCapabilityUnsupported(
                    node
                )
            )) if node == reference
        ));
        assert_eq!(store_state(&fixture.store), warm);

        assert!(fixture.store.set_symbol_node_links(
            reference,
            SymbolNodeLinks {
                resolved_symbol: Some(plan.bindings[0].alias_symbol),
            },
        ));
        let poisoned = store_state(&fixture.store);
        assert!(matches!(
            query_type_with_import_capability(&mut fixture, root, capability),
            Err(DeclaredTypeError::TypeNodeUnavailable(
                super::super::type_nodes::TypeNodeUnavailable::InvalidCachedSymbol {
                    node,
                    symbol,
                }
            )) if node == reference && symbol == plan.bindings[0].alias_symbol
        ));
        assert_eq!(store_state(&fixture.store), poisoned);
    }

    #[test]
    fn composite_import_root_requires_every_type_reference_leaf_capability() {
        let mut fixture = fixture(
            &[
                r#"
                    import type { Count, Text } from "./target";
                    const value: Count | Text = 1;
                "#,
                r"export type Count = number; export type Text = string;",
            ],
            &[Route {
                source: 0,
                specifier: 0,
                target: Some(1),
            }],
        );
        let plan = fixture.plan_type_import(0, 0);
        let root = variable_type_node(&fixture, 0, "value");
        let count = type_reference(&fixture, 0, "Count");
        let text = type_reference(&fixture, 0, "Text");
        let resolved = resolve_all_types(&mut fixture, &plan.bindings).unwrap();
        let count_binding = plan
            .bindings
            .iter()
            .position(|binding| binding.local_text == "Count")
            .unwrap();
        let text_binding = plan
            .bindings
            .iter()
            .position(|binding| binding.local_text == "Text")
            .unwrap();
        let count_capability = plan_type_reference_capability_for_root(
            &fixture,
            &resolved[count_binding],
            root,
            count,
        );
        let text_capability =
            plan_type_reference_capability_for_root(&fixture, &resolved[text_binding], root, text);

        let before = store_state(&fixture.store);
        assert!(matches!(
            query_type_with_import_capability(&mut fixture, root, count_capability),
            Err(DeclaredTypeError::TypeNodeUnavailable(
                super::super::type_nodes::TypeNodeUnavailable::ImportAliasCapabilityUnsupported(
                    node
                )
            )) if node == count
        ));
        assert_eq!(store_state(&fixture.store), before);
        assert!(
            query_type_with_import_capabilities(
                &mut fixture,
                root,
                [count_capability, text_capability],
            )
            .is_ok()
        );
    }

    #[test]
    fn type_import_capability_cannot_warm_its_enclosing_local_alias() {
        let mut fixture = fixture(
            &[
                r#"
                    import type { User } from "./target";
                    type Local = User;
                "#,
                r"export type User = { id: number };",
            ],
            &[Route {
                source: 0,
                specifier: 0,
                target: Some(1),
            }],
        );
        let plan = fixture.plan_type_import(0, 0);
        let reference = type_reference(&fixture, 0, "User");
        let resolved = resolve_all_types(&mut fixture, &plan.bindings).unwrap();
        let capability = plan_type_reference_capability(&fixture, &resolved[0], reference);

        let before = store_state(&fixture.store);
        assert!(matches!(
            query_type_with_import_capability(&mut fixture, reference, capability),
            Err(DeclaredTypeError::TypeNodeUnavailable(
                super::super::type_nodes::TypeNodeUnavailable::ImportAliasCapabilityUnsupported(
                    node
                )
            )) if node == reference
        ));
        assert_eq!(store_state(&fixture.store), before);
    }

    #[test]
    fn type_import_capability_authorizes_exact_callable_parameter_identity() {
        let mut fixture = fixture(
            &[
                r#"
                    import type { User } from "./target";
                    function accept(value: User): void {}
                "#,
                r"export type User = { id: number };",
            ],
            &[Route {
                source: 0,
                specifier: 0,
                target: Some(1),
            }],
        );
        let plan = fixture.plan_type_import(0, 0);
        let reference = type_reference(&fixture, 0, "User");
        let resolved = resolve_all_types(&mut fixture, &plan.bindings).unwrap();
        let capability = plan_type_reference_capability(&fixture, &resolved[0], reference);
        let (declaration, owner_symbol) =
            {
                let file = &fixture.files[0];
                let declaration =
                    file.parsed
                        .arena
                        .iter()
                        .find_map(|(node, record)| {
                            (record.kind == SyntaxKind::FunctionDeclaration)
                                .then_some(NodeRef::new(file.parsed.arena.id(), file.file, node))
                        })
                        .expect("fixture contains a function declaration");
                let owner_symbol = fixture
                    .bound
                    .get(&file.file)
                    .and_then(|bound| bound.symbol(declaration))
                    .and_then(|symbol| fixture.store.get_merged_symbol(symbol))
                    .expect("fixture function has one canonical owner");
                (declaration, owner_symbol)
            };

        let callable = query_source_callable_with_import_capability(
            &mut fixture,
            declaration,
            owner_symbol,
            capability,
        )
        .unwrap();
        let signature = fixture
            .store
            .source_callable_provenance(callable)
            .expect("the callable retains its exact source declaration")
            .signature;
        let expected = fixture
            .store
            .type_alias_links(resolved[0].target_symbol)
            .and_then(|links| links.declared_type)
            .expect("the imported parameter type is materialized");
        assert_eq!(
            fixture.store.callable_signature_parameter_types(signature),
            Some(&[expected][..]),
        );
        assert!(
            fixture
                .store
                .value_symbol_links(plan.bindings[0].alias_symbol)
                .is_none()
        );
    }

    #[test]
    fn minted_type_import_capability_rejects_a_foreign_type_only_marker() {
        let mut fixture = fixture(
            &[
                r#"
                    import type { User } from "./target";
                    const user: User = { id: 1 };
                "#,
                r"export type User = { id: number };",
            ],
            &[Route {
                source: 0,
                specifier: 0,
                target: Some(1),
            }],
        );
        let plan = fixture.plan_type_import(0, 0);
        let reference = type_reference(&fixture, 0, "User");
        let resolved = resolve_all_types(&mut fixture, &plan.bindings).unwrap();
        let capability = plan_type_reference_capability(&fixture, &resolved[0], reference);
        let alias = plan.bindings[0].alias_symbol;
        let mut links = fixture.store.alias_symbol_links(alias).unwrap().clone();
        links.type_only_declaration = Some(resolved[0].target_declaration);
        assert!(fixture.store.set_alias_symbol_links(alias, links));

        let before = store_state(&fixture.store);
        assert!(matches!(
            query_type_with_import_capability(&mut fixture, reference, capability),
            Err(DeclaredTypeError::TypeNodeUnavailable(
                super::super::type_nodes::TypeNodeUnavailable::InvalidImportAliasTarget {
                    node,
                    alias: failed_alias,
                    target,
                }
            )) if node == reference
                && failed_alias == alias
                && target == resolved[0].target_symbol
        ));
        assert_eq!(store_state(&fixture.store), before);
    }

    #[test]
    fn warm_reference_requires_an_equal_preexisting_target_cache_before_query() {
        let mut fixture = fixture(
            &[
                r#"
                    import type { User } from "./target";
                    const user: User = { id: 1 };
                "#,
                r"export type User = { id: number };",
            ],
            &[Route {
                source: 0,
                specifier: 0,
                target: Some(1),
            }],
        );
        let plan = fixture.plan_type_import(0, 0);
        let reference = type_reference(&fixture, 0, "User");
        let resolved = resolve_all_types(&mut fixture, &plan.bindings).unwrap();
        let target = resolved[0].target_symbol;
        let (number_type, string_type) = {
            let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
            (bootstrap.number_type, bootstrap.string_type)
        };
        assert_eq!(
            fixture
                .store
                .type_alias_links(target)
                .and_then(|links| links.declared_type),
            None
        );
        assert!(fixture.store.set_type_node_links(
            reference,
            TypeNodeLinks {
                resolved_type: Some(number_type),
                outer_type_parameters: None,
            },
        ));

        let before = store_state(&fixture.store);
        let alias_links = fixture
            .store
            .alias_symbol_links(plan.bindings[0].alias_symbol)
            .cloned();
        let reference_links = fixture.store.type_node_links(reference).cloned();
        let reference_symbol_links = fixture.store.symbol_node_links(reference).cloned();
        assert_eq!(
            try_plan_type_reference_capability(&fixture, &resolved[0], reference),
            Err(SourceImportError::Invariant(
                SourceImportInvariant::InvalidTypeReferenceCache(reference)
            ))
        );
        assert_eq!(store_state(&fixture.store), before);
        assert_eq!(
            fixture
                .store
                .alias_symbol_links(plan.bindings[0].alias_symbol),
            alias_links.as_ref()
        );
        assert_eq!(
            fixture.store.type_node_links(reference),
            reference_links.as_ref()
        );
        assert_eq!(
            fixture.store.symbol_node_links(reference),
            reference_symbol_links.as_ref()
        );
        assert_eq!(fixture.store.type_alias_links(target), None);

        let mut target_links = fixture
            .store
            .type_alias_links(target)
            .cloned()
            .unwrap_or_default();
        target_links.declared_type = Some(string_type);
        assert!(fixture.store.set_type_alias_links(target, target_links));
        let before_mismatch = store_state(&fixture.store);
        assert_eq!(
            try_plan_type_reference_capability(&fixture, &resolved[0], reference),
            Err(SourceImportError::Invariant(
                SourceImportInvariant::InvalidTypeReferenceCache(reference)
            ))
        );
        assert_eq!(store_state(&fixture.store), before_mismatch);
        assert_eq!(
            fixture
                .store
                .type_alias_links(target)
                .and_then(|links| links.declared_type),
            Some(string_type)
        );
    }

    #[test]
    fn shadowed_same_text_type_reference_is_an_unsupported_import_use() {
        let mut fixture = fixture(
            &[
                r#"
                    import type { User } from "./target";
                    function shadow<User>(value: User): void {}
                "#,
                r"export type User = { id: number };",
            ],
            &[Route {
                source: 0,
                specifier: 0,
                target: Some(1),
            }],
        );
        let plan = fixture.plan_type_import(0, 0);
        let reference = type_reference(&fixture, 0, "User");
        let resolved = resolve_all_types(&mut fixture, &plan.bindings).unwrap();
        assert_eq!(
            try_plan_type_reference_capability(&fixture, &resolved[0], reference),
            Err(SourceImportError::Unsupported(
                SourceImportUnsupported::TypeReference(reference)
            ))
        );
    }

    #[test]
    fn duplicate_local_named_type_import_is_a_typed_unsupported_boundary() {
        let fixture = fixture(
            &[
                r#"import type { User as Local, User as Local } from "./target";"#,
                r"export type User = { id: number };",
            ],
            &[],
        );
        let file = &fixture.files[0];
        let bound = fixture.bound.get(&file.file).unwrap();
        let declaration = file
            .parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::ImportDeclaration).then_some(node)
            })
            .unwrap();
        assert!(matches!(
            plan_top_level_named_type_import(
                &file.parsed.arena,
                bound,
                &fixture.store,
                NodeRef::new(file.parsed.arena.id(), file.file, declaration),
            ),
            Err(SourceImportError::Unsupported(
                SourceImportUnsupported::Binding(_)
            ))
        ));
    }

    #[test]
    fn type_only_interface_import_is_exact_after_target_first_query() {
        let mut fixture = fixture(
            &[
                r#"
                    import type { User } from "./target";
                    const user: User = { id: 1 };
                "#,
                r"export interface User { id: number }",
            ],
            &[Route {
                source: 0,
                specifier: 0,
                target: Some(1),
            }],
        );
        let target = direct_export(&fixture, 1, "User");
        let target_first = query_declared_type(&mut fixture, target).unwrap();
        let plan = fixture.plan_type_import(0, 0);
        let reference = type_reference(&fixture, 0, "User");
        let resolved = resolve_all_types(&mut fixture, &plan.bindings).unwrap();
        let capability = plan_type_reference_capability(&fixture, &resolved[0], reference);
        assert_eq!(
            query_type_with_import_capability(&mut fixture, reference, capability).unwrap(),
            target_first
        );
        let warm_resolved = resolve_all_types(&mut fixture, &plan.bindings).unwrap();
        let warm_capability =
            plan_type_reference_capability(&fixture, &warm_resolved[0], reference);
        assert_eq!(
            query_type_with_import_capability(&mut fixture, reference, warm_capability).unwrap(),
            target_first
        );
    }

    #[test]
    fn exact_type_import_capability_rejects_poisoned_warm_reference_links() {
        let mut fixture = fixture(
            &[
                r#"
                    import type { User } from "./target";
                    const user: User = { id: 1 };
                "#,
                r"export type User = { id: number };",
            ],
            &[Route {
                source: 0,
                specifier: 0,
                target: Some(1),
            }],
        );
        let plan = fixture.plan_type_import(0, 0);
        let reference = type_reference(&fixture, 0, "User");
        let resolved = resolve_all_types(&mut fixture, &plan.bindings).unwrap();
        let capability = plan_type_reference_capability(&fixture, &resolved[0], reference);
        assert!(fixture.store.set_symbol_node_links(
            reference,
            SymbolNodeLinks {
                resolved_symbol: Some(plan.bindings[0].alias_symbol),
            },
        ));
        assert!(matches!(
            query_type_with_import_capability(&mut fixture, reference, capability),
            Err(DeclaredTypeError::TypeNodeUnavailable(
                super::super::type_nodes::TypeNodeUnavailable::InvalidCachedSymbol {
                    node,
                    symbol,
                }
            )) if node == reference && symbol == plan.bindings[0].alias_symbol
        ));
    }

    #[test]
    fn unused_type_import_stays_lazy_and_value_use_is_a_typed_boundary() {
        let mut fixture = fixture(
            &[
                r#"
                    import type { User } from "./target";
                    const runtime = User;
                "#,
                r"export type User = { id: number };",
            ],
            &[Route {
                source: 0,
                specifier: 0,
                target: Some(1),
            }],
        );
        let plan = fixture.plan_type_import(0, 0);
        let resolved = resolve_all_types(&mut fixture, &plan.bindings).unwrap();
        let target = resolved[0].target_symbol;
        assert_eq!(
            fixture
                .store
                .type_alias_links(target)
                .and_then(|links| links.declared_type),
            None,
            "declaration resolution does not eagerly type an unused import"
        );
        assert_eq!(
            fixture
                .store
                .value_symbol_links(plan.bindings[0].alias_symbol),
            None
        );
        let read = identifier_initializer(&fixture, 0, "User");
        let file = &fixture.files[0];
        let bound = fixture.bound.get(&file.file).unwrap();
        assert_eq!(
            reject_source_type_import_value_use(
                &file.parsed.arena,
                bound,
                &fixture.store,
                &resolved[0],
                read,
                "User",
                plan.bindings[0].alias_symbol,
            ),
            Err(SourceImportError::Unsupported(
                SourceImportUnsupported::ValueUseOfTypeOnlyImport(read)
            ))
        );
        assert_eq!(
            fixture
                .store
                .value_symbol_links(plan.bindings[0].alias_symbol),
            None
        );
    }

    #[test]
    fn cold_and_warm_direct_and_renamed_imports_type_only_used_bindings() {
        let mut fixture = fixture(
            &[
                r#"
                    import { numberValue, textValue as localText } from "./target";
                    const result: string = localText;
                "#,
                r#"
                    export const numberValue: number = 1;
                    export const textValue: string = "ok";
                "#,
            ],
            &[Route {
                source: 0,
                specifier: 0,
                target: Some(1),
            }],
        );
        let plan = fixture.plan_import(0, 0);
        assert_eq!(plan.bindings.len(), 2);
        assert_eq!(plan.bindings[1].imported_text, "textValue");
        assert_eq!(plan.bindings[1].local_text, "localText");

        let read = identifier_initializer(&fixture, 0, "localText");
        let bound = fixture.bound.get(&fixture.files[0].file).unwrap();
        let planned_read = plan_source_import_identifier_read(
            &fixture.files[0].parsed.arena,
            bound,
            &fixture.store,
            &plan.bindings[1],
            read,
            "localText",
            plan.bindings[1].alias_symbol,
        )
        .unwrap();
        assert_eq!(planned_read.resolved_symbol, plan.bindings[1].alias_symbol);
        assert_eq!(planned_read.value_symbol, plan.bindings[1].alias_symbol);

        let resolved = resolve_all(&mut fixture, &plan.bindings).unwrap();
        assert_eq!(resolved.len(), 2);
        let prepared = vec![prepare_one(&mut fixture, &resolved[1], &planned_read).unwrap()];
        let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
        assert_eq!(prepared[0].type_, bootstrap.string_type);
        assert_eq!(
            fixture
                .store
                .value_symbol_links(resolved[0].binding.alias_symbol),
            None,
            "an unused binding resolves but is never value-typed"
        );
        assert_eq!(
            fixture.store.value_symbol_links(resolved[0].target_symbol),
            None
        );
        for value in &prepared {
            assert_eq!(fixture.store.value_symbol_links(value.target_symbol), None);
            assert_eq!(
                fixture.store.value_symbol_links(value.binding.alias_symbol),
                None
            );
        }
        let publications =
            preflight_prepared_source_import_publications(&fixture.store, &prepared).unwrap();
        assert_eq!(publications.len(), 2);
        assert_eq!(
            fixture
                .store
                .value_symbol_links(resolved[0].binding.alias_symbol),
            None,
            "preflight itself performs no writes"
        );
        publish_for_test(&mut fixture.store, &prepared);
        for value in &prepared {
            assert_eq!(
                fixture
                    .store
                    .value_symbol_links(value.target_symbol)
                    .and_then(|links| links.resolved_type),
                Some(value.type_)
            );
            assert_eq!(
                fixture
                    .store
                    .value_symbol_links(value.binding.alias_symbol)
                    .and_then(|links| links.resolved_type),
                Some(value.type_)
            );
        }

        assert_eq!(
            fixture
                .store
                .value_symbol_links(resolved[0].binding.alias_symbol),
            None
        );
        assert_eq!(
            fixture.store.value_symbol_links(resolved[0].target_symbol),
            None
        );

        let warm_resolved = resolve_all(&mut fixture, &plan.bindings).unwrap();
        assert_eq!(warm_resolved, resolved);
        let warm = vec![prepare_one(&mut fixture, &warm_resolved[1], &planned_read).unwrap()];
        assert_eq!(warm, prepared);
        publish_for_test(&mut fixture.store, &warm);
    }

    #[test]
    fn exported_generic_function_import_prepares_exact_callable_and_replays_warm() {
        let mut fixture = fixture(
            &[
                r#"
                    import { identity } from "./target";
                    const imported = identity;
                "#,
                r"
                    export function identity<T>(value: T): T { return value; }
                ",
            ],
            &[Route {
                source: 0,
                specifier: 0,
                target: Some(1),
            }],
        );
        let plan = fixture.plan_import(0, 0);
        let read = identifier_initializer(&fixture, 0, "identity");
        let bound = fixture.bound.get(&fixture.files[0].file).unwrap();
        let planned_read = plan_source_import_identifier_read(
            &fixture.files[0].parsed.arena,
            bound,
            &fixture.store,
            &plan.bindings[0],
            read,
            "identity",
            plan.bindings[0].alias_symbol,
        )
        .unwrap();
        let resolved = resolve_all(&mut fixture, &plan.bindings).unwrap();
        let [resolved] = resolved.as_slice() else {
            panic!("expected one import binding")
        };
        let target = direct_export(&fixture, 1, "identity");
        assert_eq!(resolved.target_symbol, target);

        let prepared = prepare_one(&mut fixture, resolved, &planned_read).unwrap();
        let PreparedSourceImportTarget::AnnotatedFunction { signature } = &prepared.target else {
            panic!("expected an annotated function target")
        };
        let signature = *signature;
        let signature_record = fixture.store.signature(signature).unwrap();
        let [type_parameter] = signature_record.type_parameters() else {
            panic!("expected one generic type parameter")
        };
        assert_eq!(
            signature_record.resolved_return_type(),
            Some(*type_parameter)
        );
        assert_eq!(
            fixture.store.source_callable_type_for_owner(target),
            Some(prepared.type_)
        );
        assert_eq!(
            fixture
                .store
                .value_symbol_links(target)
                .and_then(|links| links.resolved_type),
            Some(prepared.type_),
            "the target callable graph is a canonical lazy-query memo"
        );
        assert_eq!(
            fixture
                .store
                .value_symbol_links(plan.bindings[0].alias_symbol),
            None,
            "the importer alias remains deferred until final publication"
        );

        publish_for_test(&mut fixture.store, std::slice::from_ref(&prepared));
        assert_eq!(
            fixture
                .store
                .value_symbol_links(plan.bindings[0].alias_symbol)
                .and_then(|links| links.resolved_type),
            Some(prepared.type_)
        );
        let warm_state = store_state(&fixture.store);

        let warm_resolved = resolve_all(&mut fixture, &plan.bindings).unwrap();
        assert_eq!(warm_resolved.as_slice(), std::slice::from_ref(resolved));
        let warm = prepare_one(&mut fixture, &warm_resolved[0], &planned_read).unwrap();
        assert_eq!(warm, prepared);
        assert_eq!(store_state(&fixture.store), warm_state);
        publish_for_test(&mut fixture.store, std::slice::from_ref(&warm));
    }

    #[test]
    fn inferred_function_import_requires_a_fully_published_callable() {
        let mut fixture = fixture(
            &[
                r#"
                    import { hello } from "./target";
                    const imported = hello;
                "#,
                r#"export function hello() { return "world"; }"#,
            ],
            &[Route {
                source: 0,
                specifier: 0,
                target: Some(1),
            }],
        );
        let plan = fixture.plan_import(0, 0);
        let node = identifier_initializer(&fixture, 0, "hello");
        let bound = fixture.bound.get(&fixture.files[0].file).unwrap();
        let read = plan_source_import_identifier_read(
            &fixture.files[0].parsed.arena,
            bound,
            &fixture.store,
            &plan.bindings[0],
            node,
            "hello",
            plan.bindings[0].alias_symbol,
        )
        .unwrap();
        let resolved = resolve_all(&mut fixture, &plan.bindings).unwrap();
        let target = resolved[0].target_symbol;
        let cold = store_state(&fixture.store);
        assert!(matches!(
            prepare_one(&mut fixture, &resolved[0], &read),
            Err(SourceImportError::Unsupported(
                SourceImportUnsupported::TargetSymbol { target: rejected, .. }
            )) if rejected == target
        ));
        assert_eq!(store_state(&fixture.store), cold);

        let (callable, type_, signature) = {
            let Fixture {
                files,
                bound,
                global_types,
                store,
                ..
            } = &mut fixture;
            let sources = || {
                files.iter().map(|file| {
                    (
                        &file.parsed.arena,
                        bound.get(&file.file).expect("fixture bound every file"),
                    )
                })
            };
            let host = DeclaredTypeHost::new_after_global_merge(
                sources(),
                GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
            )
            .unwrap();
            let declaration = store.symbol(target).unwrap().value_declaration().unwrap();
            let callable = plan_source_callable(
                store,
                &host,
                declaration,
                target,
                Some(CanonicalArrayTargets::from_global_types(global_types)),
            )
            .unwrap();
            let type_ = CanonicalTypeQuery::new_with_global_types(
                store,
                &host,
                global_types,
                CanonicalCheckerOptions::default(),
                &mut CanonicalCheckerDiagnostics::default(),
            )
            .unwrap()
            .get_type_of_source_callable(declaration, target)
            .unwrap();
            let signature = store.source_callable_provenance(type_).unwrap().signature;
            (callable, type_, signature)
        };
        let pending = store_state(&fixture.store);
        assert!(matches!(
            prepare_one(&mut fixture, &resolved[0], &read),
            Err(SourceImportError::Unsupported(
                SourceImportUnsupported::TargetSymbol { target: rejected, .. }
            )) if rejected == target
        ));
        assert_eq!(store_state(&fixture.store), pending);

        let string = fixture.store.intrinsic_bootstrap().unwrap().string_type;
        super::super::source_callables::publish_inferred_source_callable_return(
            &mut fixture.store,
            &callable,
            signature,
            string,
        )
        .unwrap();
        let prepared = prepare_one(&mut fixture, &resolved[0], &read).unwrap();
        assert_eq!(prepared.type_, type_);
        assert!(
            fixture
                .store
                .value_symbol_links(plan.bindings[0].alias_symbol)
                .is_none()
        );

        let target_links = fixture.store.value_symbol_links(target).unwrap().clone();
        assert!(
            fixture
                .store
                .set_value_symbol_links(target, ValueSymbolLinks::default())
        );
        let poisoned = store_state(&fixture.store);
        assert_eq!(
            prepare_one(&mut fixture, &resolved[0], &read),
            Err(SourceImportError::Invariant(
                SourceImportInvariant::InvalidTargetLinks(target),
            )),
        );
        assert_eq!(store_state(&fixture.store), poisoned);
        assert!(fixture.store.set_value_symbol_links(target, target_links));

        publish_for_test(&mut fixture.store, std::slice::from_ref(&prepared));
        let published = store_state(&fixture.store);
        assert_eq!(
            prepare_one(&mut fixture, &resolved[0], &read).unwrap(),
            prepared,
        );
        assert_eq!(store_state(&fixture.store), published);
    }

    #[test]
    fn poisoned_late_binding_blocks_every_prepared_publication() {
        let mut fixture = fixture(
            &[
                r#"
                    import { first, second } from "./target";
                    const one: number = first;
                    const two: string = second;
                "#,
                r#"
                    export const first: number = 1;
                    export const second: string = "two";
                "#,
            ],
            &[Route {
                source: 0,
                specifier: 0,
                target: Some(1),
            }],
        );
        let plan = fixture.plan_import(0, 0);
        let first_read_node = identifier_initializer(&fixture, 0, "first");
        let second_read_node = identifier_initializer(&fixture, 0, "second");
        let bound = fixture.bound.get(&fixture.files[0].file).unwrap();
        let first_read = plan_source_import_identifier_read(
            &fixture.files[0].parsed.arena,
            bound,
            &fixture.store,
            &plan.bindings[0],
            first_read_node,
            "first",
            plan.bindings[0].alias_symbol,
        )
        .unwrap();
        let second_read = plan_source_import_identifier_read(
            &fixture.files[0].parsed.arena,
            bound,
            &fixture.store,
            &plan.bindings[1],
            second_read_node,
            "second",
            plan.bindings[1].alias_symbol,
        )
        .unwrap();
        let resolved = resolve_all(&mut fixture, &plan.bindings).unwrap();
        let prepared = vec![
            prepare_one(&mut fixture, &resolved[0], &first_read).unwrap(),
            prepare_one(&mut fixture, &resolved[1], &second_read).unwrap(),
        ];
        let first_alias = binding_symbol(&plan, "first");
        let second_alias = binding_symbol(&plan, "second");
        assert!(fixture.store.set_value_symbol_links(
            second_alias,
            ValueSymbolLinks {
                function_or_constructor_checked: true,
                ..ValueSymbolLinks::default()
            },
        ));

        assert_eq!(
            preflight_prepared_source_import_publications(&fixture.store, &prepared),
            Err(SourceImportError::Invariant(
                SourceImportInvariant::InvalidAliasValueLinks(second_alias)
            ))
        );
        assert_eq!(fixture.store.value_symbol_links(first_alias), None);
        assert_eq!(
            fixture.store.value_symbol_links(prepared[0].target_symbol),
            None
        );
    }

    #[test]
    fn unresolved_module_resolution_is_retryable_and_publishes_no_value_links() {
        let mut fixture = fixture(
            &[
                r#"import { value } from "./target";"#,
                r"export const value: number = 1;",
            ],
            &[Route {
                source: 0,
                specifier: 0,
                target: None,
            }],
        );
        let plan = fixture.plan_import(0, 0);
        let alias = plan.bindings[0].alias_symbol;
        assert_eq!(fixture.store.alias_symbol_links(alias), None);
        let before = store_state(&fixture.store);
        let error = resolve_all(&mut fixture, &plan.bindings).unwrap_err();
        assert!(matches!(
            error,
            SourceImportError::Alias(CanonicalAliasResolutionError::TargetUnavailable {
                alias: failed,
                reason: super::super::alias::CanonicalAliasTargetUnavailable::ModuleResolutionUnresolved(_),
            }) if failed == alias
        ));
        assert_eq!(fixture.store.alias_symbol_links(alias), None);
        assert_eq!(fixture.store.value_symbol_links(alias), None);
        assert_eq!(store_state(&fixture.store), before);
    }

    #[test]
    fn direct_import_alias_cycle_fails_closed_before_target_typing() {
        let mut fixture = fixture(
            &[
                r#"
                    import { value } from "./b";
                    export { value as loop } from "./b";
                "#,
                r#"export { loop as value } from "./a";"#,
            ],
            &[
                Route {
                    source: 0,
                    specifier: 0,
                    target: Some(1),
                },
                Route {
                    source: 0,
                    specifier: 1,
                    target: Some(1),
                },
                Route {
                    source: 1,
                    specifier: 0,
                    target: Some(0),
                },
            ],
        );
        let plan = fixture.plan_import(0, 0);
        let alias = plan.bindings[0].alias_symbol;
        let first = resolve_all(&mut fixture, &plan.bindings).unwrap_err();
        let SourceImportError::CircularAlias {
            alias: failed,
            events,
        } = first
        else {
            panic!("expected circular alias boundary, got {first:?}");
        };
        assert_eq!(failed, alias);
        assert!(
            !events.is_empty(),
            "cold resolution owns the diagnostic event"
        );

        let warm = resolve_all(&mut fixture, &plan.bindings).unwrap_err();
        let SourceImportError::CircularAlias {
            alias: failed,
            events,
        } = warm
        else {
            panic!("expected cached circular alias boundary, got {warm:?}");
        };
        assert_eq!(failed, alias);
        assert!(
            events.is_empty(),
            "warm resolution does not reissue the event"
        );
        assert_eq!(fixture.store.value_symbol_links(alias), None);
    }

    #[test]
    fn consistent_warm_alias_cache_cannot_redirect_manifest_target() {
        let mut fixture = fixture(
            &[
                r#"import { value } from "./selected";"#,
                r"export const value: number = 1;",
                r#"export const value: string = "wrong";"#,
            ],
            &[Route {
                source: 0,
                specifier: 0,
                target: Some(1),
            }],
        );
        let plan = fixture.plan_import(0, 0);
        let alias = plan.bindings[0].alias_symbol;
        let selected = direct_export(&fixture, 1, "value");
        let wrong = direct_export(&fixture, 2, "value");
        assert_ne!(selected, wrong);
        assert!(fixture.store.set_alias_symbol_links(
            alias,
            AliasSymbolLinks {
                immediate_target: Some(wrong),
                alias_target: AliasTargetState::Resolved(wrong),
                ..AliasSymbolLinks::default()
            },
        ));

        assert_eq!(
            resolve_all(&mut fixture, &plan.bindings),
            Err(SourceImportError::Invariant(
                SourceImportInvariant::InvalidAliasLinks(alias)
            )),
            "the production host and manifest, not self-consistent sparse links, own directness"
        );
        assert_eq!(fixture.store.value_symbol_links(alias), None);
        assert_eq!(fixture.store.value_symbol_links(selected), None);
        assert_eq!(fixture.store.value_symbol_links(wrong), None);
    }

    #[test]
    fn declaration_numeric_const_import_preserves_exact_literal_and_warm_caches() {
        let mut fixture = fixture_with_declaration_files(
            &[
                r#"
                    import { value } from "./target";
                    const result = value;
                "#,
                "export const value = 1;",
            ],
            &[Route {
                source: 0,
                specifier: 0,
                target: Some(1),
            }],
            &[1],
        );
        let plan = fixture.plan_import(0, 0);
        let read_node = identifier_initializer(&fixture, 0, "value");
        let bound = fixture.bound.get(&fixture.files[0].file).unwrap();
        let read = plan_source_import_identifier_read(
            &fixture.files[0].parsed.arena,
            bound,
            &fixture.store,
            &plan.bindings[0],
            read_node,
            "value",
            plan.bindings[0].alias_symbol,
        )
        .unwrap();
        let resolved = resolve_all(&mut fixture, &plan.bindings).unwrap();
        let target = resolved[0].target_symbol;
        let prepared = prepare_one(&mut fixture, &resolved[0], &read).unwrap();
        assert!(matches!(
            &prepared.target,
            PreparedSourceImportTarget::DeclarationNumericConst { literal, .. }
                if literal == "1"
        ));
        assert_eq!(display_type(&fixture, prepared.type_), "1");
        let regular = fixture
            .store
            .intrinsic_bootstrap()
            .unwrap()
            .cached_number_literal_type(ts_jsnum::Number::new(1.0))
            .unwrap();
        assert_eq!(
            fixture.store.fresh_type_of_literal_type(regular).unwrap(),
            prepared.type_
        );
        assert!(fixture.store.value_symbol_links(target).is_none());
        assert!(
            fixture
                .store
                .value_symbol_links(plan.bindings[0].alias_symbol)
                .is_none()
        );

        publish_for_test(&mut fixture.store, std::slice::from_ref(&prepared));
        let published = store_state(&fixture.store);
        assert_eq!(
            fixture
                .store
                .value_symbol_links(target)
                .and_then(|links| links.resolved_type),
            Some(prepared.type_)
        );
        assert_eq!(
            fixture
                .store
                .value_symbol_links(plan.bindings[0].alias_symbol)
                .and_then(|links| links.resolved_type),
            Some(prepared.type_)
        );

        let warm_resolved = resolve_all(&mut fixture, &plan.bindings).unwrap();
        assert_eq!(warm_resolved, resolved);
        assert_eq!(
            prepare_one(&mut fixture, &warm_resolved[0], &read).unwrap(),
            prepared
        );
        assert_eq!(store_state(&fixture.store), published);
    }

    #[test]
    fn declaration_numeric_const_import_rejects_unsupported_initializer_shapes() {
        for target in [
            "export const value: number;",
            "export declare const value: number = 1;",
            "export declare const value;",
            "export const value = \"one\";",
            "export const value = -1;",
            "export const value = 1, another = 2;",
        ] {
            let mut fixture = fixture_with_declaration_files(
                &[
                    r#"
                        import { value } from "./target";
                        const result = value;
                    "#,
                    target,
                ],
                &[Route {
                    source: 0,
                    specifier: 0,
                    target: Some(1),
                }],
                &[1],
            );
            let plan = fixture.plan_import(0, 0);
            let read_node = identifier_initializer(&fixture, 0, "value");
            let bound = fixture.bound.get(&fixture.files[0].file).unwrap();
            let read = plan_source_import_identifier_read(
                &fixture.files[0].parsed.arena,
                bound,
                &fixture.store,
                &plan.bindings[0],
                read_node,
                "value",
                plan.bindings[0].alias_symbol,
            )
            .unwrap();
            let resolved = resolve_all(&mut fixture, &plan.bindings).unwrap();
            let before = store_state(&fixture.store);
            assert!(
                matches!(
                    prepare_one(&mut fixture, &resolved[0], &read),
                    Err(SourceImportError::Unsupported(_))
                ),
                "declaration initializer unexpectedly escaped its boundary: {target}",
            );
            assert_eq!(store_state(&fixture.store), before);
            assert!(
                fixture
                    .store
                    .value_symbol_links(resolved[0].target_symbol)
                    .is_none()
            );
            assert!(
                fixture
                    .store
                    .value_symbol_links(plan.bindings[0].alias_symbol)
                    .is_none()
            );
        }
    }

    #[test]
    fn unannotated_target_and_non_value_import_syntax_remain_explicit_boundaries() {
        let mut unannotated = fixture(
            &[
                r#"
                    import { value } from "./target";
                    const result = value;
                "#,
                r"export const value = 1;",
            ],
            &[Route {
                source: 0,
                specifier: 0,
                target: Some(1),
            }],
        );
        let plan = unannotated.plan_import(0, 0);
        let read_node = identifier_initializer(&unannotated, 0, "value");
        let bound = unannotated.bound.get(&unannotated.files[0].file).unwrap();
        let read = plan_source_import_identifier_read(
            &unannotated.files[0].parsed.arena,
            bound,
            &unannotated.store,
            &plan.bindings[0],
            read_node,
            "value",
            plan.bindings[0].alias_symbol,
        )
        .unwrap();
        let resolved = resolve_all(&mut unannotated, &plan.bindings).unwrap();
        assert!(matches!(
            prepare_one(&mut unannotated, &resolved[0], &read),
            Err(SourceImportError::Unsupported(
                SourceImportUnsupported::MissingTargetAnnotation(_)
            ))
        ));

        let mut unannotated_function = fixture(
            &[
                r#"
                    import { identity } from "./target";
                    const result = identity;
                "#,
                r"export function identity<T>(value: T) { return value; }",
            ],
            &[Route {
                source: 0,
                specifier: 0,
                target: Some(1),
            }],
        );
        let plan = unannotated_function.plan_import(0, 0);
        let read_node = identifier_initializer(&unannotated_function, 0, "identity");
        let bound = unannotated_function
            .bound
            .get(&unannotated_function.files[0].file)
            .unwrap();
        let read = plan_source_import_identifier_read(
            &unannotated_function.files[0].parsed.arena,
            bound,
            &unannotated_function.store,
            &plan.bindings[0],
            read_node,
            "identity",
            plan.bindings[0].alias_symbol,
        )
        .unwrap();
        let resolved = resolve_all(&mut unannotated_function, &plan.bindings).unwrap();
        assert!(matches!(
            prepare_one(&mut unannotated_function, &resolved[0], &read),
            Err(SourceImportError::Callable(
                SourceCallableError::Unsupported(_)
            ))
        ));
        assert_eq!(
            unannotated_function
                .store
                .value_symbol_links(plan.bindings[0].alias_symbol),
            None
        );
        assert_eq!(
            unannotated_function
                .store
                .value_symbol_links(resolved[0].target_symbol),
            None
        );

        for source in [
            r#"import type { value } from "./target";"#,
            r#"import { type value } from "./target";"#,
        ] {
            let fixture = fixture(&[source, r"export const value: number = 1;"], &[]);
            let file = &fixture.files[0];
            let bound = fixture.bound.get(&file.file).unwrap();
            let declaration = file
                .parsed
                .arena
                .iter()
                .find_map(|(node, record)| {
                    (record.kind == SyntaxKind::ImportDeclaration).then_some(node)
                })
                .unwrap();
            assert!(matches!(
                plan_top_level_named_value_import(
                    &file.parsed.arena,
                    bound,
                    &fixture.store,
                    NodeRef::new(file.parsed.arena.id(), file.file, declaration),
                ),
                Err(SourceImportError::Unsupported(_))
            ));
        }
    }
}
