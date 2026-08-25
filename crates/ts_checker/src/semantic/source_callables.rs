//! Exact source callable values owned by source function symbols.
//!
//! This provider deliberately stops before statement/expression dispatch and
//! function-body semantics. It proves one retained `FunctionDeclaration`,
//! anonymous `FunctionExpression`, or `ArrowFunction` and its binder-owned
//! FUNCTION symbol, publishes the callable shell/signature/parameter types,
//! including authenticated identifier and assertion predicates, implicit `any`
//! on ordinary function declarations, and implicit `any[]` rest parameters,
//! and validates the resulting store shape.
//! Source values never borrow `FunctionType` `TypeNode` or `__call` provenance.

use std::collections::HashSet;

use ts_ast::{ModifierList, NodeData, NodeFlags, NodeList, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalNameResolver, CanonicalResolutionLocation, CanonicalSourceFileFacts, CheckFlags,
    InternalSymbolName, SemanticSymbolId, SymbolFlags,
};

use super::{
    CanonicalGlobalTypes, CanonicalTypeMapperStore, DeclaredTypeError, DeclaredTypeHost,
    DeclaredTypeUnavailable, SignatureId, TypeId,
    array_types::CanonicalArrayTargets,
    bootstrap::{LiteralTypeCacheError, PreparedTypeQueryTypes},
    callables::{
        StoredSingleCallableValidation, ValidatedSingleCallParameterDisplay,
        ValidatedSingleCallSignatureDisplay, validate_stored_single_callable,
    },
    declared::{
        cached_ordinary_type_parameter_owner, explicit_type_parameter_symbols, preflight_node,
        type_list_key,
    },
    functions::{StoredFunctionTypeValidation, plan_function_type, validate_stored_function_type},
    jsdoc::{
        JsDocIntrinsicType, JsDocType, PlannedJsDocType, ResolvedJsDocSignature,
        plan_javascript_source_jsdoc,
    },
    links::{
        DeclaredTypeLinks, DecoratorSignatureState, EffectsSignatureState, ResolvedSignatureState,
        SignatureLinks, SymbolNodeLinks, TypeNodeLinks, ValueSymbolLinks,
    },
    reference_types::validate_direct_generic_reference,
    signatures::{Signature, SignatureFlags, TypePredicateKind},
    store::{
        PreparedSourceGenericCallablePublication, ResolvedSourceCallableTypeParameter,
        SemanticStore, SourceCallableProvenance, SourceCallableReturnProvenance,
        SourceCallableTypeParameterProvenance, SourceNodeParent,
    },
    type_records::{
        ConstrainedTypeData, InterfaceTypeData, StructuredTypeData, TypeCacheState, TypeData,
        TypeRecord,
    },
    types::{ObjectFlags, TypeFlags},
};

#[cfg(test)]
use super::declared::execute_type_parameter;

pub(super) use super::store::SourceCallableFamily;

const NODE_FLAG_JSDOC: u32 = 1 << 22;

/// One identifier parameter and its explicit or implicit type identity.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[allow(clippy::struct_excessive_bools)] // Preserve the flat upstream parameter state.
pub(super) struct SourceCallableParameterPlan {
    pub(super) declaration: NodeRef,
    pub(super) symbol: SemanticSymbolId,
    pub(super) type_node: NodeRef,
    identity_node: NodeRef,
    null_literal_identity: bool,
    implicit_any: bool,
    jsdoc_function: bool,
    jsdoc_contextual_type: Option<TypeId>,
    pub(super) optional: bool,
    pub(super) initializer: Option<NodeRef>,
    pub(super) rest: bool,
}

impl SourceCallableParameterPlan {
    pub(super) const fn annotation_identity(self) -> (NodeRef, bool) {
        (self.identity_node, self.null_literal_identity)
    }

    /// Returns the written type node, or `None` for an implicit `any`.
    pub(super) const fn explicit_type_node(self) -> Option<NodeRef> {
        if self.implicit_any {
            None
        } else {
            Some(self.type_node)
        }
    }

    /// Returns the written, contextual `JSDoc`, implicit `any`, or implicit `any[]` type.
    pub(super) fn base_type(self, store: &CanonicalTypeMapperStore) -> Option<TypeId> {
        if let Some(type_) = self.jsdoc_contextual_type {
            return Some(type_);
        }
        match self.explicit_type_node() {
            None if self.rest => implicit_any_array_type(store),
            None => store
                .intrinsic_bootstrap()
                .map(|bootstrap| bootstrap.any_type),
            Some(_) => {
                cached_annotation_identity(store, self.identity_node, self.null_literal_identity)
            }
        }
    }

    pub(super) const fn is_implicit_any(self) -> bool {
        self.implicit_any && self.jsdoc_contextual_type.is_none()
    }

    pub(super) const fn has_jsdoc_function_type(self) -> bool {
        self.jsdoc_function
    }
}

/// Returns the eagerly initialized `Array<any>` identity, including its missing-library fallback.
pub(super) fn implicit_any_array_type(store: &CanonicalTypeMapperStore) -> Option<TypeId> {
    let bootstrap = store.intrinsic_bootstrap()?;
    let globals = store.symbol_table(bootstrap.globals)?;
    let Some(array) = globals.get_source("Array") else {
        return Some(bootstrap.empty_object_type);
    };
    let array = store.get_merged_symbol(array)?;
    let target = store.declared_type_links(array)?.declared_type?;
    if target == bootstrap.empty_generic_type {
        return Some(bootstrap.empty_object_type);
    }
    let TypeData::Interface(interface) = store.type_payload(target)?.data() else {
        return None;
    };
    let TypeCacheState::Allocated(instantiations) = &interface.reference.object.instantiations
    else {
        return None;
    };
    let array_type = *instantiations.get(&type_list_key(&[bootstrap.any_type]))?;
    let reference = validate_direct_generic_reference(store, array_type).ok()?;
    (reference.target == target && reference.type_arguments.as_slice() == [bootstrap.any_type])
        .then_some(array_type)
}

/// One exact declared type-parameter identity owned by a source signature.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct SourceCallableTypeParameterPlan {
    pub(super) declaration: NodeRef,
    pub(super) symbol: SemanticSymbolId,
    pub(super) constraint: Option<NodeRef>,
    pub(super) default_type: Option<NodeRef>,
}

/// Exact syntax and parameter ownership for one identifier type predicate.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct CallableTypePredicatePlan {
    pub(super) node: NodeRef,
    pub(super) owner: NodeRef,
    pub(super) parameter_name: NodeRef,
    pub(super) parameter_symbol: SemanticSymbolId,
    pub(super) parameter_index: i32,
    pub(super) narrowed_type: Option<NodeRef>,
    pub(super) kind: TypePredicateKind,
}

/// Opaque exact-AST capability carried from source planning into the store's
/// atomic generic-callable publication. Sibling semantic modules can inspect
/// it for validation but cannot manufacture or alter its bound AST edges.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct SourceCallableTypeParameterSyntaxRow {
    declaration: NodeRef,
    constraint: Option<NodeRef>,
    default_type: Option<NodeRef>,
}

impl SourceCallableTypeParameterSyntaxRow {
    pub(super) const fn declaration(self) -> NodeRef {
        self.declaration
    }

    pub(super) const fn constraint(self) -> Option<NodeRef> {
        self.constraint
    }

    pub(super) const fn default_type(self) -> Option<NodeRef> {
        self.default_type
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct SourceCallableTypeParameterSyntaxProof {
    declaration: NodeRef,
    rows: Box<[SourceCallableTypeParameterSyntaxRow]>,
    generic_return_type_parameter_declaration: Option<NodeRef>,
    generic_fixed_return_is_exact: bool,
    inferred_empty_body_is_exact: bool,
}

/// Exact return ownership retained by source planning.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum SourceCallableReturnPlan {
    Annotated {
        type_node: NodeRef,
        identity_node: NodeRef,
        null_literal_identity: bool,
    },
    Inferred,
    AmbientImplicitAny,
}

/// Whether a source function owns executable syntax or is an exact ambient
/// declaration. Ambient callables retain their declaration as a diagnostic
/// anchor, but no body consumer may run unless this capability is `Present`.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum SourceCallableBodyMode {
    Present,
    AmbientDeclaration,
}

impl SourceCallableBodyMode {
    pub(super) const fn is_ambient(self) -> bool {
        matches!(self, Self::AmbientDeclaration)
    }
}

impl SourceCallableReturnPlan {
    pub(super) const fn type_node(self) -> Option<NodeRef> {
        match self {
            Self::Annotated { type_node, .. } => Some(type_node),
            Self::Inferred | Self::AmbientImplicitAny => None,
        }
    }

    pub(super) const fn annotation_identity(self) -> Option<(NodeRef, bool)> {
        match self {
            Self::Annotated {
                identity_node,
                null_literal_identity,
                ..
            } => Some((identity_node, null_literal_identity)),
            Self::Inferred | Self::AmbientImplicitAny => None,
        }
    }

    pub(super) const fn provenance(self) -> SourceCallableReturnProvenance {
        match self {
            Self::Annotated { .. } => SourceCallableReturnProvenance::Annotated,
            Self::Inferred | Self::AmbientImplicitAny => SourceCallableReturnProvenance::Inferred,
        }
    }

    pub(super) const fn is_inferred(self) -> bool {
        matches!(self, Self::Inferred)
    }

    pub(super) const fn is_ambient_implicit_any(self) -> bool {
        matches!(self, Self::AmbientImplicitAny)
    }
}

impl SourceCallableTypeParameterSyntaxProof {
    pub(super) const fn declaration(&self) -> NodeRef {
        self.declaration
    }

    pub(super) fn rows(&self) -> &[SourceCallableTypeParameterSyntaxRow] {
        &self.rows
    }

    pub(super) const fn generic_return_type_parameter_declaration(&self) -> Option<NodeRef> {
        self.generic_return_type_parameter_declaration
    }

    pub(super) const fn generic_fixed_return_is_exact(&self) -> bool {
        self.generic_fixed_return_is_exact
    }

    pub(super) const fn inferred_empty_body_is_exact(&self) -> bool {
        self.inferred_empty_body_is_exact
    }
}

/// Binder/syntax proof retained across source-callable publication.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct SourceCallablePlan {
    pub(super) family: SourceCallableFamily,
    pub(super) declaration: NodeRef,
    pub(super) owner_symbol: SemanticSymbolId,
    pub(super) owner_parent: Option<SemanticSymbolId>,
    pub(super) export_local: Option<SemanticSymbolId>,
    javascript_duplicate_owner: bool,
    pub(super) type_parameters: Vec<SourceCallableTypeParameterPlan>,
    pub(super) type_parameter_syntax: Box<SourceCallableTypeParameterSyntaxProof>,
    generic_return_type_parameter_index: Option<usize>,
    pub(super) parameters: Vec<SourceCallableParameterPlan>,
    pub(super) return_type: SourceCallableReturnPlan,
    pub(super) type_predicate: Option<CallableTypePredicatePlan>,
    pub(super) body_mode: SourceCallableBodyMode,
    /// True for an authenticated async arrow, JSX function, or ordinary function.
    pub(super) is_async: bool,
    /// The actual body for `Present`, or the declaration diagnostic anchor for
    /// `AmbientDeclaration`.
    pub(super) body: NodeRef,
    pub(super) flags: SignatureFlags,
    pub(super) min_argument_count: i32,
    pub(super) array_targets: Option<CanonicalArrayTargets>,
}

impl SourceCallablePlan {
    /// Installs a callable `JSDoc` annotation on its authenticated source parameter.
    pub(super) fn set_jsdoc_function_parameter_type(
        &mut self,
        store: &CanonicalTypeMapperStore,
        declaration: NodeRef,
        type_: TypeId,
    ) -> Result<(), SourceCallableError> {
        let invalid = || invariant(SourceCallableInvariant::InvalidParameterCache(declaration));
        let Some(parameter) = self
            .parameters
            .iter_mut()
            .find(|parameter| parameter.declaration == declaration)
        else {
            return Err(invalid());
        };
        if self.family != SourceCallableFamily::FunctionDeclaration
            || self.flags != SignatureFlags::NONE
            || !parameter.implicit_any
            || !parameter.jsdoc_function
            || parameter.optional
            || parameter.rest
            || parameter.initializer.is_some()
            || store.type_payload(type_).and_then(TypeRecord::symbol) != Some(parameter.symbol)
            || store
                .type_node_links(declaration)
                .and_then(|links| links.resolved_type)
                != Some(type_)
            || !matches!(
                validate_stored_function_type(store, type_),
                StoredFunctionTypeValidation::Valid(_)
            )
            || parameter
                .jsdoc_contextual_type
                .is_some_and(|existing| existing != type_)
        {
            return Err(invalid());
        }
        parameter.jsdoc_contextual_type = Some(type_);
        Ok(())
    }
}

/// Source syntax families intentionally deferred beyond the exact first cut.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum SourceCallableUnsupported {
    GenericSignature(NodeRef),
    Async(NodeRef),
    Generator(NodeRef),
    ExpandoProperties(NodeRef),
    Modifiers(NodeRef),
    OverloadDeclaration(NodeRef),
    ThisParameter(NodeRef),
    RestParameterNotLast(NodeRef),
    OptionalRestParameter(NodeRef),
    InitializedRestParameter(NodeRef),
    OptionalInitializedParameter(NodeRef),
    AmbientRestParameter(NodeRef),
    AmbientParameterInitializer(NodeRef),
    DestructuredParameter(NodeRef),
    ParameterModifiers(NodeRef),
    MissingParameterType(NodeRef),
    GenericInferredReturn(NodeRef),
    TypePredicate(NodeRef),
    RequiredAfterOptional(NodeRef),
}

/// Malformed AST, binder provenance, or semantic cache state.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum SourceCallableInvariant {
    InvalidSyntax(NodeRef),
    InvalidOwnerSymbol(NodeRef),
    InvalidExportRoute(NodeRef),
    InvalidParameter(NodeRef),
    InvalidParameterSymbol(NodeRef),
    InvalidTypeCache(NodeRef),
    InvalidSignatureCache(NodeRef),
    InvalidParameterCache(NodeRef),
    Capacity(NodeRef),
    Publication(NodeRef),
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum SourceCallableError {
    Unsupported(SourceCallableUnsupported),
    Invariant(SourceCallableInvariant),
    DeclaredType(DeclaredTypeError),
    LiteralCache(LiteralTypeCacheError),
}

impl SourceCallableError {
    pub(super) const fn node(self) -> Option<NodeRef> {
        match self {
            Self::Unsupported(reason) => Some(match reason {
                SourceCallableUnsupported::GenericSignature(node)
                | SourceCallableUnsupported::Async(node)
                | SourceCallableUnsupported::Generator(node)
                | SourceCallableUnsupported::ExpandoProperties(node)
                | SourceCallableUnsupported::Modifiers(node)
                | SourceCallableUnsupported::OverloadDeclaration(node)
                | SourceCallableUnsupported::ThisParameter(node)
                | SourceCallableUnsupported::RestParameterNotLast(node)
                | SourceCallableUnsupported::OptionalRestParameter(node)
                | SourceCallableUnsupported::InitializedRestParameter(node)
                | SourceCallableUnsupported::OptionalInitializedParameter(node)
                | SourceCallableUnsupported::AmbientRestParameter(node)
                | SourceCallableUnsupported::AmbientParameterInitializer(node)
                | SourceCallableUnsupported::DestructuredParameter(node)
                | SourceCallableUnsupported::ParameterModifiers(node)
                | SourceCallableUnsupported::MissingParameterType(node)
                | SourceCallableUnsupported::GenericInferredReturn(node)
                | SourceCallableUnsupported::TypePredicate(node)
                | SourceCallableUnsupported::RequiredAfterOptional(node) => node,
            }),
            Self::Invariant(reason) => Some(match reason {
                SourceCallableInvariant::InvalidSyntax(node)
                | SourceCallableInvariant::InvalidOwnerSymbol(node)
                | SourceCallableInvariant::InvalidExportRoute(node)
                | SourceCallableInvariant::InvalidParameter(node)
                | SourceCallableInvariant::InvalidParameterSymbol(node)
                | SourceCallableInvariant::InvalidTypeCache(node)
                | SourceCallableInvariant::InvalidSignatureCache(node)
                | SourceCallableInvariant::InvalidParameterCache(node)
                | SourceCallableInvariant::Capacity(node)
                | SourceCallableInvariant::Publication(node) => node,
            }),
            Self::DeclaredType(_) | Self::LiteralCache(_) => None,
        }
    }
}

impl From<DeclaredTypeError> for SourceCallableError {
    fn from(error: DeclaredTypeError) -> Self {
        Self::DeclaredType(error)
    }
}

impl From<LiteralTypeCacheError> for SourceCallableError {
    fn from(error: LiteralTypeCacheError) -> Self {
        Self::LiteralCache(error)
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum SourceCallableState {
    Cold,
    ActiveBarrier {
        type_: TypeId,
        signature: SignatureId,
    },
    ActiveParameters {
        type_: TypeId,
        signature: SignatureId,
    },
    AwaitingInferredReturn {
        type_: TypeId,
        signature: SignatureId,
    },
    Resolved {
        type_: TypeId,
        signature: SignatureId,
    },
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct PendingSourceCallable {
    pub(super) type_: TypeId,
    pub(super) signature: SignatureId,
}

#[derive(Clone, Debug)]
pub(super) struct PendingSourceCallableParameterTypes {
    pub(super) plan: SourceCallablePlan,
    pub(super) base_types: Vec<TypeId>,
}

/// One already-resolved parameter of a contextually typed source arrow.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct ContextualSourceCallableParameter {
    pub(super) declaration: NodeRef,
    pub(super) symbol: SemanticSymbolId,
    pub(super) type_: TypeId,
}

/// Fully prepared semantic values for the bounded inferred contextual arrow.
///
/// Syntax and contextual-origin planning happen before this boundary. Every
/// `TypeId` here is final, so publication never fabricates an annotation node
/// or conflates the variable's contextual target with the arrow expression.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct PreparedContextualSourceCallable {
    pub(super) declaration: NodeRef,
    pub(super) owner_symbol: SemanticSymbolId,
    pub(super) variable_symbol: SemanticSymbolId,
    pub(super) contextual_target: TypeId,
    pub(super) parameters: Vec<ContextualSourceCallableParameter>,
    pub(super) flags: SignatureFlags,
    pub(super) min_argument_count: i32,
    pub(super) return_type: TypeId,
}

/// Fully resolved context for an arrow passed directly to a source call.
///
/// Direct arguments have no binder-owned variable or property anchor. Their
/// exact call-parent proof and contextual target are retained independently.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct PreparedContextualDirectCallSourceCallable {
    pub(super) declaration: NodeRef,
    pub(super) owner_symbol: SemanticSymbolId,
    pub(super) contextual_target: TypeId,
    pub(super) parameters: Vec<ContextualSourceCallableParameter>,
    pub(super) flags: SignatureFlags,
    pub(super) min_argument_count: i32,
    pub(super) return_type: TypeId,
}

#[derive(Clone, Copy)]
struct PreparedContextualSourceCallableView<'a> {
    declaration: NodeRef,
    owner_symbol: SemanticSymbolId,
    variable_symbol: Option<SemanticSymbolId>,
    contextual_target: TypeId,
    parameters: &'a [ContextualSourceCallableParameter],
    flags: SignatureFlags,
    min_argument_count: i32,
    return_type: TypeId,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) enum StoredSourceCallableValidation {
    NotSourceCallable,
    Pending,
    Valid(Vec<TypeId>),
    Malformed,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum SourceCallableDisplayError {
    Unsupported(SourceCallableUnsupported),
    Pending,
    Malformed,
}

struct SourceSyntaxView<'a> {
    family: SourceCallableFamily,
    parameters: &'a NodeList,
    modifiers: Option<&'a ModifierList>,
    type_parameters: Option<&'a NodeList>,
    return_type: Option<ts_ast::NodeId>,
    body: Option<ts_ast::NodeId>,
    asterisk_token: Option<ts_ast::NodeId>,
    name: Option<ts_ast::NodeId>,
    equals_greater_than_token: Option<ts_ast::NodeId>,
    invalid_parser_cache: bool,
}

impl SourceSyntaxView<'_> {
    fn is_async(&self, store: &CanonicalTypeMapperStore, declaration: NodeRef) -> bool {
        self.modifiers.is_some_and(|modifiers| {
            matches!(
                modifiers.list.nodes.as_slice(),
                [modifier] if store.source_node_kind(NodeRef::new(
                    declaration.arena,
                    declaration.file,
                    *modifier,
                )) == Some(SyntaxKind::AsyncKeyword)
            ) || matches!(
                modifiers.list.nodes.as_slice(),
                [export, modifier]
                    if store.source_node_kind(NodeRef::new(
                        declaration.arena,
                        declaration.file,
                        *export,
                    )) == Some(SyntaxKind::ExportKeyword)
                        && store.source_node_kind(NodeRef::new(
                            declaration.arena,
                            declaration.file,
                            *modifier,
                        )) == Some(SyntaxKind::AsyncKeyword)
            )
        })
    }
}

#[derive(Clone, Copy)]
enum SourceCallableOwnerShape<'a> {
    Unique,
    AmbientOverload(&'a [NodeRef]),
    JavaScriptDuplicateImplementation,
}

fn source_function_owner_declarations_are_exact(
    store: &CanonicalTypeMapperStore,
    owner: &ts_binder::semantic::Symbol,
    declaration: NodeRef,
) -> bool {
    if owner.value_declaration() != Some(declaration) {
        return false;
    }
    if owner.flags() == SymbolFlags::FUNCTION {
        return owner.declarations() == Some(&[declaration]);
    }
    let allowed_flags = SymbolFlags::FUNCTION | SymbolFlags::MODULE;
    if !owner.flags().contains(SymbolFlags::FUNCTION)
        || !owner.flags().intersects(SymbolFlags::MODULE)
        || owner.flags().without(allowed_flags) != SymbolFlags::NONE
    {
        return false;
    }
    let Some(declarations) = owner.declarations() else {
        return false;
    };
    declarations.len() >= 2
        && declarations
            .iter()
            .filter(|candidate| **candidate == declaration)
            .count()
            == 1
        && declarations.iter().all(|candidate| {
            *candidate == declaration
                || candidate.is_for(declaration.arena, declaration.file)
                    && store.source_node_kind(*candidate) == Some(SyntaxKind::ModuleDeclaration)
                    && store.source_node_parent(*candidate) == store.source_node_parent(declaration)
        })
}

fn javascript_duplicate_function_owner_structure(
    store: &CanonicalTypeMapperStore,
    owner_symbol: SemanticSymbolId,
    owner: &ts_binder::semantic::Symbol,
    declaration: NodeRef,
) -> bool {
    let Some(declarations) = owner.declarations() else {
        return false;
    };
    let Some(SourceNodeParent::Parent(source)) = store.source_node_parent(declaration) else {
        return false;
    };
    owner.flags() == SymbolFlags::FUNCTION
        && owner.check_flags() == CheckFlags::NONE
        && !owner.name().as_bytes().is_empty()
        && owner.value_declaration() == Some(declaration)
        && owner.members().is_none()
        && owner.exports().is_none()
        && owner.parent().is_none()
        && owner.export_symbol().is_none()
        && store.get_merged_symbol(owner_symbol) == Some(owner_symbol)
        && store.source_node_kind(source) == Some(SyntaxKind::SourceFile)
        && store.source_node_parent(source) == Some(SourceNodeParent::Root)
        && declarations.len() >= 2
        && declarations.first().copied() == Some(declaration)
        && declarations
            .iter()
            .enumerate()
            .all(|(index, implementation)| {
                !declarations[..index].contains(implementation)
                    && implementation.is_for(declaration.arena, declaration.file)
                    && store.source_node_kind(*implementation)
                        == Some(SyntaxKind::FunctionDeclaration)
                    && store.source_node_parent(*implementation)
                        == Some(SourceNodeParent::Parent(source))
            })
}

/// Authenticates the first implementation of one exact JavaScript function group.
pub(super) fn valid_javascript_duplicate_function_owner_shape(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    owner_symbol: SemanticSymbolId,
    declaration: NodeRef,
) -> bool {
    let Some(bound) = host.bound_file(declaration) else {
        return false;
    };
    if bound
        .source_facts()
        .is_none_or(|facts| !facts.is_javascript_file() || facts.is_declaration_file())
    {
        return false;
    }
    let Some(owner) = store.symbol(owner_symbol) else {
        return false;
    };
    if !javascript_duplicate_function_owner_structure(store, owner_symbol, owner, declaration) {
        return false;
    }
    let source = bound.source_file();
    if !source.is_for(declaration.arena, declaration.file)
        || bound
            .locals(source)
            .and_then(|locals| store.symbol_table(locals))
            .and_then(|locals| locals.get(owner.name()))
            != Some(owner_symbol)
    {
        return false;
    }
    let Some(source_record) = host.node(source) else {
        return false;
    };
    let NodeData::SourceFile(source_data) = &source_record.data else {
        return false;
    };
    if source_record.kind != SyntaxKind::SourceFile
        || source_record.parent.is_some()
        || source_record.range.end < source_record.range.start
        || source_data.statements.range.end < source_data.statements.range.start
        || source_data.statements.range.start < source_record.range.start
        || source_data.statements.range.end > source_record.range.end
    {
        return false;
    }

    let declarations = owner
        .declarations()
        .expect("the duplicate owner structure checked its declarations");
    let mut source_declarations = source_data.statements.nodes.iter().filter_map(|statement| {
        let statement = NodeRef::new(source.arena, source.file, *statement);
        (bound.symbol(statement) == Some(owner_symbol)).then_some(statement)
    });
    let mut previous_end = source_record.range.start;
    for implementation in declarations {
        if source_declarations.next() != Some(*implementation)
            || bound.symbol(*implementation) != Some(owner_symbol)
            || bound.local_symbol(*implementation).is_some()
            || bound.container(*implementation) != Some(source)
        {
            return false;
        }
        let Some(record) = host.node(*implementation) else {
            return false;
        };
        let NodeData::FunctionDeclaration(function) = &record.data else {
            return false;
        };
        if record.kind != SyntaxKind::FunctionDeclaration
            || record.parent != Some(source.node)
            || record.flags.0 & NODE_FLAG_JSDOC != 0
            || record.range.start < previous_end
            || record.range.end < record.range.start
            || record.range.end > source_record.range.end
            || function.parameters.range.end < function.parameters.range.start
            || function.parameters.range.start < record.range.start
            || function.parameters.range.end > record.range.end
            || function.full_signature.is_some()
            || function.next_container.is_some()
            || function.symbol.is_some()
            || function.local_symbol.is_some()
            || function.flow_node.is_some()
            || function.end_flow_node.is_some()
            || function.return_flow_node.is_some()
        {
            return false;
        }
        let Some(name) = function
            .name
            .map(|name| NodeRef::new(implementation.arena, implementation.file, name))
        else {
            return false;
        };
        let Some(name_record) = host.node(name) else {
            return false;
        };
        let NodeData::Identifier(identifier) = &name_record.data else {
            return false;
        };
        if name_record.kind != SyntaxKind::Identifier
            || name_record.parent != Some(implementation.node)
            || name_record.range.start < record.range.start
            || name_record.range.end < name_record.range.start
            || name_record.range.end > function.parameters.range.start
            || identifier.text.is_empty()
            || identifier.text.as_bytes() != owner.name().as_bytes()
            || identifier.flow_node.is_some()
        {
            return false;
        }
        let Some(body) = function
            .body
            .map(|body| NodeRef::new(implementation.arena, implementation.file, body))
        else {
            return false;
        };
        let Some(body_record) = host.node(body) else {
            return false;
        };
        let NodeData::Block(block) = &body_record.data else {
            return false;
        };
        if body_record.kind != SyntaxKind::Block
            || body_record.parent != Some(implementation.node)
            || body_record.range.start < function.parameters.range.end
            || body_record.range.end < body_record.range.start
            || body_record.range.end > record.range.end
            || block.statements.range.end < block.statements.range.start
            || block.statements.range.start < body_record.range.start
            || block.statements.range.end > body_record.range.end
            || block.statements.has_trailing_comma
            || block.flow_node.is_some()
            || block.next_container.is_some()
            || block.facts != 0
            || bound.container(body) != Some(*implementation)
        {
            return false;
        }
        previous_end = record.range.end;
    }
    source_declarations.next().is_none()
}

fn published_javascript_duplicate_function_owner_shape(
    store: &CanonicalTypeMapperStore,
    owner_symbol: SemanticSymbolId,
    owner: &ts_binder::semantic::Symbol,
    declaration: NodeRef,
) -> bool {
    if !javascript_duplicate_function_owner_structure(store, owner_symbol, owner, declaration) {
        return false;
    }
    let Some(type_) = store.source_callable_type_for_owner(owner_symbol) else {
        return false;
    };
    let Some(provenance) = store.source_callable_provenance(type_) else {
        return false;
    };
    provenance.family == SourceCallableFamily::FunctionDeclaration
        && provenance.declaration == declaration
        && provenance.owner_symbol == owner_symbol
        && provenance.owner_parent.is_none()
        && provenance.export_local.is_none()
        && provenance.contextual_target.is_none()
        && provenance.contextual_variable.is_none()
        && store.source_callable_type_for_declaration(declaration) == Some(type_)
        && store.source_callable_type_for_signature(provenance.signature) == Some(type_)
}

fn source_function_owner_exports_are_valid(
    store: &CanonicalTypeMapperStore,
    owner_symbol: SemanticSymbolId,
    owner: &ts_binder::semantic::Symbol,
) -> bool {
    let Some(exports) = owner.exports() else {
        return owner.flags() == SymbolFlags::FUNCTION
            || owner.flags() == SymbolFlags::FUNCTION | SymbolFlags::NAMESPACE_MODULE;
    };
    if owner.flags() == SymbolFlags::FUNCTION {
        return owner.value_declaration().is_some_and(|declaration| {
            source_function_owner_expando_exports_are_valid(store, owner_symbol, declaration)
        });
    }
    if owner.flags() == SymbolFlags::FUNCTION | SymbolFlags::NAMESPACE_MODULE {
        return store.symbol_table(exports).is_some_and(|exports| {
            exports.iter().all(|(_, symbol)| {
                store.symbol(symbol).is_some_and(|record| {
                    !record
                        .flags()
                        .intersects(SymbolFlags::VALUE | SymbolFlags::ALIAS)
                        && record.parent() == Some(owner_symbol)
                })
            })
        });
    }
    if owner.flags() != SymbolFlags::FUNCTION | SymbolFlags::VALUE_MODULE {
        return false;
    }
    let Some(declarations) = owner.declarations() else {
        return false;
    };
    let Some(first) = declarations.first() else {
        return false;
    };
    let Some(exports) = store.symbol_table(exports) else {
        return false;
    };
    let mut has_value_export = false;
    for (name, symbol) in exports.iter() {
        let Some(record) = store.symbol(symbol) else {
            return false;
        };
        if record.name() != name
            || !record.flags().intersects(
                SymbolFlags::TYPE
                    | SymbolFlags::VALUE
                    | SymbolFlags::NAMESPACE
                    | SymbolFlags::ALIAS,
            )
            || store.get_merged_symbol(symbol) != Some(symbol)
            || store.get_parent_of_symbol(symbol) != Some(owner_symbol)
            || record.declarations().is_none_or(|members| {
                members.is_empty()
                    || members.iter().any(|member| {
                        !member.is_for(first.arena, first.file)
                            || !source_function_namespace_contains_declaration(
                                store,
                                declarations,
                                *member,
                            )
                    })
            })
        {
            return false;
        }
        has_value_export |= record.flags().intersects(SymbolFlags::VALUE);
    }
    has_value_export
}

/// Validates direct binder-owned expando properties on a source function.
pub(super) fn source_function_owner_expando_exports_are_valid(
    store: &CanonicalTypeMapperStore,
    owner_symbol: SemanticSymbolId,
    declaration: NodeRef,
) -> bool {
    let Some(owner) = store.symbol(owner_symbol) else {
        return false;
    };
    let Some(exports) = owner.exports() else {
        return true;
    };
    let Some(SourceNodeParent::Parent(source)) = store.source_node_parent(declaration) else {
        return false;
    };
    let Some(exports) = store.symbol_table(exports) else {
        return false;
    };
    if exports.is_empty()
        || owner.flags() != SymbolFlags::FUNCTION
        || owner.check_flags() != CheckFlags::NONE
        || owner.declarations() != Some(&[declaration])
        || owner.value_declaration() != Some(declaration)
        || owner.members().is_some()
        || owner.parent().is_some()
        || owner.export_symbol().is_some()
        || store.get_merged_symbol(owner_symbol) != Some(owner_symbol)
        || store.source_node_kind(declaration) != Some(SyntaxKind::FunctionDeclaration)
        || store.source_node_kind(source) != Some(SyntaxKind::SourceFile)
    {
        return false;
    }

    exports.iter().all(|(name, symbol)| {
        let Some(property) = store.symbol(symbol) else {
            return false;
        };
        let Some([assignment]) = property.declarations() else {
            return false;
        };
        let assignment = *assignment;
        let Some(SourceNodeParent::Parent(statement)) = store.source_node_parent(assignment) else {
            return false;
        };
        property.flags() == SymbolFlags::PROPERTY | SymbolFlags::ASSIGNMENT
            && property.check_flags() == CheckFlags::NONE
            && property.name() == name
            && property.value_declaration() == Some(assignment)
            && property.members().is_none()
            && property.exports().is_none()
            && property.parent() == Some(owner_symbol)
            && property.export_symbol().is_none()
            && store.get_merged_symbol(symbol) == Some(symbol)
            && assignment.is_for(declaration.arena, declaration.file)
            && store.source_node_kind(assignment) == Some(SyntaxKind::BinaryExpression)
            && store.source_node_kind(statement) == Some(SyntaxKind::ExpressionStatement)
            && store.source_node_parent(statement) == Some(SourceNodeParent::Parent(source))
    })
}

/// Validates retained arrow expando ownership without borrowing source arenas.
pub(super) fn source_arrow_owner_expando_exports_are_valid(
    store: &CanonicalTypeMapperStore,
    owner_symbol: SemanticSymbolId,
    declaration: NodeRef,
) -> bool {
    let Some(owner) = store.symbol(owner_symbol) else {
        return false;
    };
    let Some(exports) = owner.exports() else {
        return true;
    };
    let Some(SourceNodeParent::Parent(variable)) = store.source_node_parent(declaration) else {
        return false;
    };
    let Some(SourceNodeParent::Parent(list)) = store.source_node_parent(variable) else {
        return false;
    };
    let Some(SourceNodeParent::Parent(variable_statement)) = store.source_node_parent(list) else {
        return false;
    };
    let Some(SourceNodeParent::Parent(source)) = store.source_node_parent(variable_statement)
    else {
        return false;
    };
    let Some(exports) = store.symbol_table(exports) else {
        return false;
    };
    if exports.is_empty()
        || store.source_node_kind(declaration) != Some(SyntaxKind::ArrowFunction)
        || store.source_node_kind(variable) != Some(SyntaxKind::VariableDeclaration)
        || store.source_node_kind(list) != Some(SyntaxKind::VariableDeclarationList)
        || store.source_node_kind(variable_statement) != Some(SyntaxKind::VariableStatement)
        || store.source_node_kind(source) != Some(SyntaxKind::SourceFile)
    {
        return false;
    }

    exports.iter().all(|(name, symbol)| {
        let Some(property) = store.symbol(symbol) else {
            return false;
        };
        let Some([assignment]) = property.declarations() else {
            return false;
        };
        let assignment = *assignment;
        let Some(SourceNodeParent::Parent(statement)) = store.source_node_parent(assignment) else {
            return false;
        };
        property.flags() == SymbolFlags::PROPERTY | SymbolFlags::ASSIGNMENT
            && property.check_flags() == CheckFlags::NONE
            && property.name() == name
            && property.value_declaration() == Some(assignment)
            && property.members().is_none()
            && property.exports().is_none()
            && property.parent() == Some(owner_symbol)
            && property.export_symbol().is_none()
            && store.get_merged_symbol(symbol) == Some(symbol)
            && assignment.is_for(declaration.arena, declaration.file)
            && store.source_node_kind(assignment) == Some(SyntaxKind::BinaryExpression)
            && store.source_node_kind(statement) == Some(SyntaxKind::ExpressionStatement)
            && store.source_node_parent(statement) == Some(SourceNodeParent::Parent(source))
    })
}

fn bound_source_arrow_owner_expando_exports_are_valid(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    declaration: NodeRef,
    owner_symbol: SemanticSymbolId,
) -> bool {
    if !source_arrow_owner_expando_exports_are_valid(store, owner_symbol, declaration) {
        return false;
    }
    let Some(owner) = store.symbol(owner_symbol) else {
        return false;
    };
    let Some(exports) = owner.exports() else {
        return true;
    };
    let Some((arena, bound)) = host.source(declaration) else {
        return false;
    };
    let Some(exports) = store.symbol_table(exports) else {
        return false;
    };

    exports.iter().all(|(_, property)| {
        let Some(assignment) = store
            .symbol(property)
            .and_then(ts_binder::semantic::Symbol::value_declaration)
        else {
            return false;
        };
        let Some(SourceNodeParent::Parent(statement)) = store.source_node_parent(assignment) else {
            return false;
        };
        matches!(
            super::assignment::plan_arrow_expando_assignment(arena, bound, store, statement),
            Ok(Some(plan))
                if plan.owner_symbol == owner_symbol
                    && plan.property_symbol == property
                    && plan.expression == assignment
        )
    })
}

fn bound_source_function_owner_expando_exports_are_valid(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    declaration: NodeRef,
    owner_symbol: SemanticSymbolId,
) -> bool {
    if !source_function_owner_expando_exports_are_valid(store, owner_symbol, declaration) {
        return false;
    }
    let Some(owner) = store.symbol(owner_symbol) else {
        return false;
    };
    let Some(exports) = owner.exports() else {
        return true;
    };
    let Some((arena, bound)) = host.source(declaration) else {
        return false;
    };
    let Some(exports) = store.symbol_table(exports) else {
        return false;
    };

    exports.iter().all(|(_, property)| {
        let Some(assignment) = store
            .symbol(property)
            .and_then(ts_binder::semantic::Symbol::value_declaration)
        else {
            return false;
        };
        let Some(SourceNodeParent::Parent(statement)) = store.source_node_parent(assignment) else {
            return false;
        };
        matches!(
            super::assignment::plan_function_expando_assignment(arena, bound, store, statement),
            Ok(Some(plan))
                if plan.owner_symbol == owner_symbol
                    && plan.property_symbol == property
                    && plan.expression == assignment
        )
    })
}

fn source_function_namespace_contains_declaration(
    store: &CanonicalTypeMapperStore,
    namespaces: &[NodeRef],
    mut declaration: NodeRef,
) -> bool {
    while let Some(SourceNodeParent::Parent(parent)) = store.source_node_parent(declaration) {
        if namespaces.contains(&parent)
            && store.source_node_kind(parent) == Some(SyntaxKind::ModuleDeclaration)
        {
            return true;
        }
        declaration = parent;
    }
    false
}

/// Accepts ordinary functions, namespace merges, and published JavaScript groups.
pub(super) fn valid_source_function_owner_shape(
    store: &CanonicalTypeMapperStore,
    owner_symbol: SemanticSymbolId,
    declaration: NodeRef,
) -> bool {
    let Some(owner) = store.symbol(owner_symbol) else {
        return false;
    };
    source_function_owner_declarations_are_exact(store, owner, declaration)
        && source_function_owner_exports_are_valid(store, owner_symbol, owner)
        || published_javascript_duplicate_function_owner_shape(
            store,
            owner_symbol,
            owner,
            declaration,
        )
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct GlobalWrapperMethodParameter {
    declaration: NodeRef,
    symbol: SemanticSymbolId,
    annotation: NodeRef,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct GlobalWrapperMethodPlan {
    wrapper: TypeId,
    owner: SemanticSymbolId,
    symbol: SemanticSymbolId,
    declaration: NodeRef,
    return_annotation: NodeRef,
    parameter: Option<GlobalWrapperMethodParameter>,
}

/// Lazily publishes one authenticated scalar-wrapper method without resolving
/// unrelated standard-library interface members.
pub(super) fn materialize_global_wrapper_method(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    global_types: &CanonicalGlobalTypes,
    receiver_type: TypeId,
    name: &str,
) -> Result<Option<(SemanticSymbolId, TypeId)>, SourceCallableError> {
    let Some(plan) = plan_global_wrapper_method(store, host, global_types, receiver_type, name)?
    else {
        return Ok(None);
    };

    if let Some(type_) = validated_global_wrapper_method(store, global_types, plan)? {
        return Ok(Some((plan.symbol, type_)));
    }

    let (number, string, undefined, strict_null_checks) = store
        .intrinsic_bootstrap()
        .map(|bootstrap| {
            (
                bootstrap.number_type,
                bootstrap.string_type,
                bootstrap.undefined_type,
                bootstrap.options.strict_null_checks,
            )
        })
        .ok_or_else(|| invariant(SourceCallableInvariant::Publication(plan.declaration)))?;
    let strict_optional = strict_null_checks && plan.parameter.is_some();
    let mut prepared_union = strict_optional
        .then(|| {
            store.prepare_type_query_types_with_global_types(&[], &[], &[], 1, 0, global_types)
        })
        .transpose()?;
    let annotation_count = 1 + usize::from(plan.parameter.is_some());
    let missing_annotations = usize::from(store.type_node_links(plan.return_annotation).is_none())
        + plan.parameter.map_or(0, |parameter| {
            usize::from(store.type_node_links(parameter.annotation).is_none())
        });
    if !store.try_reserve_types(1)
        || !store.try_reserve_signatures(1)
        || !store.try_reserve_signature_links(usize::from(
            store.signature_links(plan.declaration).is_none(),
        ))
        || !store.try_reserve_value_symbol_links(annotation_count)
        || !store.try_reserve_type_node_links(missing_annotations)
        || !store.try_reserve_function_signature_return_annotations(1)
        || !store.try_reserve_callable_signature_parameter_types(1)
    {
        return Err(invariant(SourceCallableInvariant::Capacity(
            plan.declaration,
        )));
    }

    let parameter_type = if let Some(prepared) = prepared_union.as_mut() {
        Some(store.literal_union_type_prepared_with_global_types(
            global_types,
            &[number, undefined],
            None,
            prepared,
        )?)
    } else {
        plan.parameter.map(|_| number)
    };
    let method_type = store
        .alloc_plain_object_type(ObjectFlags::ANONYMOUS, Some(plan.symbol))
        .expect("the authenticated wrapper method reserved its callable type");
    let signature = store
        .alloc_signature(
            SignatureFlags::NONE,
            Some(plan.declaration),
            Vec::new(),
            None,
            plan.parameter
                .map(|parameter| vec![parameter.symbol])
                .unwrap_or_default(),
            Some(string),
            None,
            0,
        )
        .expect("the authenticated wrapper method reserved its signature");
    assert!(store.set_signature_links(
        plan.declaration,
        SignatureLinks {
            resolved_signature: ResolvedSignatureState::Resolved(signature),
            ..SignatureLinks::default()
        },
    ));
    assert!(store.set_value_symbol_links(
        plan.symbol,
        ValueSymbolLinks {
            resolved_type: Some(method_type),
            ..ValueSymbolLinks::default()
        },
    ));
    assert!(store.set_structured_type_members(
        method_type,
        None,
        None,
        Some(vec![signature]),
        None,
        None,
    ));
    assert!(store.set_type_node_links(
        plan.return_annotation,
        TypeNodeLinks {
            resolved_type: Some(string),
            ..TypeNodeLinks::default()
        },
    ));
    assert!(store.set_function_signature_return_annotation(
        signature,
        plan.return_annotation,
        false,
    ));
    if let Some(parameter) = plan.parameter {
        assert!(store.set_type_node_links(
            parameter.annotation,
            TypeNodeLinks {
                resolved_type: Some(number),
                ..TypeNodeLinks::default()
            },
        ));
        assert!(store.set_value_symbol_links(
            parameter.symbol,
            ValueSymbolLinks {
                resolved_type: parameter_type,
                ..ValueSymbolLinks::default()
            },
        ));
    }
    assert!(store.set_callable_signature_parameter_types_batch(vec![(
        signature,
        parameter_type.into_iter().collect(),
    )]));

    debug_assert_eq!(
        validated_global_wrapper_method(store, global_types, plan),
        Ok(Some(method_type)),
    );
    Ok(Some((plan.symbol, method_type)))
}

fn plan_global_wrapper_method(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    global_types: &CanonicalGlobalTypes,
    receiver_type: TypeId,
    name: &str,
) -> Result<Option<GlobalWrapperMethodPlan>, SourceCallableError> {
    let Some(receiver) = store.type_payload(receiver_type) else {
        return Ok(None);
    };
    let (wrapper, owner_name, has_parameter) =
        if receiver.flags().intersects(TypeFlags::NUMBER_LIKE) && name == "toFixed" {
            (global_types.number_type, "Number", true)
        } else if receiver.flags().intersects(TypeFlags::STRING_LIKE) && name == "toLowerCase" {
            (global_types.string_type, "String", false)
        } else {
            return Ok(None);
        };
    let Some(wrapper_record) = store.type_payload(wrapper) else {
        return Ok(None);
    };
    let TypeData::Interface(interface) = wrapper_record.data() else {
        return Ok(None);
    };
    let Some(owner) = wrapper_record
        .symbol()
        .and_then(|owner| store.get_merged_symbol(owner))
    else {
        return Ok(None);
    };
    let Some(owner_record) = store.symbol(owner) else {
        return Ok(None);
    };
    let globals_match = store
        .intrinsic_bootstrap()
        .and_then(|bootstrap| store.symbol_table(bootstrap.globals))
        .and_then(|globals| globals.get_source(owner_name))
        .and_then(|symbol| store.get_merged_symbol(symbol))
        == Some(owner);
    let owner_flags =
        SymbolFlags::INTERFACE | SymbolFlags::FUNCTION_SCOPED_VARIABLE | SymbolFlags::TRANSIENT;
    if wrapper_record.flags() != TypeFlags::OBJECT
        || !wrapper_record
            .object_flags()
            .intersects(ObjectFlags::INTERFACE)
        || wrapper_record
            .object_flags()
            .intersects(ObjectFlags::REFERENCE)
        || wrapper_record.alias().is_some()
        || !owner_record.flags().contains(SymbolFlags::INTERFACE)
        || owner_record.flags().without(owner_flags) != SymbolFlags::NONE
        || owner_record.check_flags() != CheckFlags::NONE
        || owner_record.name().as_utf8() != Some(owner_name)
        || owner_record.parent().is_some()
        || owner_record.exports().is_some()
        || owner_record.export_symbol().is_some()
        || !globals_match
        || store
            .declared_type_links(owner)
            .and_then(|links| links.declared_type)
            != Some(wrapper)
        || interface.outer_type_parameter_count != 0
        || interface.reference.object.target.is_some()
        || interface.reference.node.is_some()
        || interface.reference.resolved_type_arguments.is_some()
    {
        return Ok(None);
    }

    let Some(symbol) = owner_record
        .members()
        .and_then(|members| store.symbol_table(members))
        .and_then(|members| members.get_source(name))
    else {
        return Ok(None);
    };
    let Some(method) = store.symbol(symbol) else {
        return Ok(None);
    };
    let Some([declaration]) = method.declarations() else {
        return Ok(None);
    };
    let declaration = *declaration;
    let invalid_owner = || invariant(SourceCallableInvariant::InvalidOwnerSymbol(declaration));
    if method.flags() != SymbolFlags::METHOD
        || method.check_flags() != CheckFlags::NONE
        || method.name().as_utf8() != Some(name)
        || method.value_declaration() != Some(declaration)
        || method.members().is_some()
        || method.exports().is_some()
        || method.export_symbol().is_some()
        || store.get_merged_symbol(symbol) != Some(symbol)
        || method
            .parent()
            .and_then(|parent| store.get_merged_symbol(parent))
            != Some(owner)
        || !host.symbol_matches(store, declaration, symbol)
    {
        return Err(invalid_owner());
    }

    let bound = host.bound_file(declaration).ok_or_else(invalid_owner)?;
    if bound.source_facts().is_none_or(|facts| {
        !facts.is_declaration_file()
            || !facts.is_default_library()
            || facts.is_javascript_file()
            || facts.is_external_or_common_js_module()
    }) {
        return Err(invalid_owner());
    }
    let record = preflight_node(store, host, declaration)?;
    let NodeData::MethodSignatureDeclaration(method_data) = &record.data else {
        return Err(invariant(SourceCallableInvariant::InvalidSyntax(
            declaration,
        )));
    };
    let Some(SourceNodeParent::Parent(interface_declaration)) =
        store.source_node_parent(declaration)
    else {
        return Err(invalid_owner());
    };
    if record.kind != SyntaxKind::MethodSignature
        || record.flags.0 != 0
        || method_data.full_signature.is_some()
        || method_data.next_container.is_some()
        || method_data.postfix_token.is_some()
        || method_data.symbol.is_some()
        || method_data.type_parameters.is_some()
        || method_data.modifiers.is_some()
        || method_data.parameters.has_trailing_comma
        || method_data.parameters.range.start < record.range.start
        || method_data.parameters.range.end > record.range.end
        || store.source_node_kind(interface_declaration) != Some(SyntaxKind::InterfaceDeclaration)
        || owner_record
            .declarations()
            .is_none_or(|declarations| !declarations.contains(&interface_declaration))
        || !host.symbol_matches(store, interface_declaration, owner)
    {
        return Err(invariant(SourceCallableInvariant::InvalidSyntax(
            declaration,
        )));
    }
    let method_name = NodeRef::new(declaration.arena, declaration.file, method_data.name);
    let method_name_record = preflight_node(store, host, method_name)?;
    let NodeData::Identifier(method_identifier) = &method_name_record.data else {
        return Err(invalid_owner());
    };
    if method_name_record.kind != SyntaxKind::Identifier
        || method_name_record.flags.0 != 0
        || method_name_record.parent != Some(declaration.node)
        || method_identifier.flow_node.is_some()
        || method_identifier.text != name
        || method_name_record.range.start < record.range.start
        || method_name_record.range.end > method_data.parameters.range.start
    {
        return Err(invalid_owner());
    }

    let return_annotation = method_data
        .type_
        .map(|type_| NodeRef::new(declaration.arena, declaration.file, type_))
        .ok_or_else(|| invariant(SourceCallableInvariant::InvalidSyntax(declaration)))?;
    let return_record = preflight_node(store, host, return_annotation)?;
    if return_record.kind != SyntaxKind::StringKeyword
        || return_record.flags.0 != 0
        || return_record.parent != Some(declaration.node)
        || return_record.range.start < method_data.parameters.range.end
        || return_record.range.end > record.range.end
    {
        return Err(invariant(SourceCallableInvariant::InvalidTypeCache(
            return_annotation,
        )));
    }

    let parameter = match (has_parameter, method_data.parameters.nodes.as_slice()) {
        (false, []) => None,
        (true, [parameter]) => Some(plan_global_wrapper_method_parameter(
            store,
            host,
            declaration,
            NodeRef::new(declaration.arena, declaration.file, *parameter),
        )?),
        _ => {
            return Err(invariant(SourceCallableInvariant::InvalidParameter(
                declaration,
            )));
        }
    };
    let locals = bound
        .locals(declaration)
        .and_then(|locals| store.symbol_table(locals));
    match parameter {
        Some(parameter)
            if locals.and_then(|locals| locals.get_source("fractionDigits"))
                != Some(parameter.symbol) =>
        {
            return Err(invariant(SourceCallableInvariant::InvalidParameterSymbol(
                parameter.declaration,
            )));
        }
        None if locals.is_some_and(|locals| !locals.is_empty()) => {
            return Err(invariant(SourceCallableInvariant::InvalidParameter(
                declaration,
            )));
        }
        _ => {}
    }

    Ok(Some(GlobalWrapperMethodPlan {
        wrapper,
        owner,
        symbol,
        declaration,
        return_annotation,
        parameter,
    }))
}

fn plan_global_wrapper_method_parameter(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    method: NodeRef,
    declaration: NodeRef,
) -> Result<GlobalWrapperMethodParameter, SourceCallableError> {
    let invalid = || invariant(SourceCallableInvariant::InvalidParameter(declaration));
    let record = preflight_node(store, host, declaration)?;
    let NodeData::ParameterDeclaration(parameter) = &record.data else {
        return Err(invalid());
    };
    if record.kind != SyntaxKind::Parameter
        || record.flags.0 != 0
        || record.parent != Some(method.node)
        || parameter.dot_dot_dot_token.is_some()
        || parameter.initializer.is_some()
        || parameter.symbol.is_some()
        || parameter.facts != 0
        || parameter.modifiers.is_some()
    {
        return Err(invalid());
    }
    let name = NodeRef::new(declaration.arena, declaration.file, parameter.name);
    let name_record = preflight_node(store, host, name)?;
    let NodeData::Identifier(identifier) = &name_record.data else {
        return Err(invalid());
    };
    if name_record.kind != SyntaxKind::Identifier
        || name_record.flags.0 != 0
        || name_record.parent != Some(declaration.node)
        || identifier.flow_node.is_some()
        || identifier.text != "fractionDigits"
        || name_record.range.start < record.range.start
        || name_record.range.end > record.range.end
    {
        return Err(invalid());
    }
    let annotation = parameter
        .type_
        .map(|type_| NodeRef::new(declaration.arena, declaration.file, type_))
        .ok_or_else(invalid)?;
    let annotation_record = preflight_node(store, host, annotation)?;
    if annotation_record.kind != SyntaxKind::NumberKeyword
        || annotation_record.flags.0 != 0
        || annotation_record.parent != Some(declaration.node)
        || annotation_record.range.start < name_record.range.end
        || annotation_record.range.end > record.range.end
        || !validate_optional_token(
            store,
            host,
            declaration,
            parameter.question_token,
            name_record.range.end,
            annotation_record.range.start,
        )?
    {
        return Err(invalid());
    }
    let symbol = host
        .bound_file(declaration)
        .and_then(|bound| bound.symbol(declaration))
        .ok_or_else(|| invariant(SourceCallableInvariant::InvalidParameterSymbol(declaration)))?;
    let record = store
        .symbol(symbol)
        .ok_or_else(|| invariant(SourceCallableInvariant::InvalidParameterSymbol(declaration)))?;
    if record.flags() != SymbolFlags::FUNCTION_SCOPED_VARIABLE
        || record.check_flags() != CheckFlags::NONE
        || record.name().as_utf8() != Some("fractionDigits")
        || record.declarations() != Some(&[declaration])
        || record.value_declaration() != Some(declaration)
        || record.members().is_some()
        || record.exports().is_some()
        || record.parent().is_some()
        || record.export_symbol().is_some()
        || store.get_merged_symbol(symbol) != Some(symbol)
    {
        return Err(invariant(SourceCallableInvariant::InvalidParameterSymbol(
            declaration,
        )));
    }
    Ok(GlobalWrapperMethodParameter {
        declaration,
        symbol,
        annotation,
    })
}

fn validated_global_wrapper_method(
    store: &CanonicalTypeMapperStore,
    global_types: &CanonicalGlobalTypes,
    plan: GlobalWrapperMethodPlan,
) -> Result<Option<TypeId>, SourceCallableError> {
    if store
        .type_payload(plan.wrapper)
        .and_then(TypeRecord::symbol)
        .and_then(|owner| store.get_merged_symbol(owner))
        != Some(plan.owner)
        || store
            .symbol(plan.owner)
            .and_then(ts_binder::semantic::Symbol::members)
            .and_then(|members| store.symbol_table(members))
            .and_then(|members| {
                store
                    .symbol(plan.symbol)
                    .and_then(|symbol| members.get(symbol.name()))
            })
            != Some(plan.symbol)
    {
        return Err(invariant(SourceCallableInvariant::InvalidOwnerSymbol(
            plan.declaration,
        )));
    }
    let (number, string, strict_null_checks) = store
        .intrinsic_bootstrap()
        .map(|bootstrap| {
            (
                bootstrap.number_type,
                bootstrap.string_type,
                bootstrap.options.strict_null_checks,
            )
        })
        .ok_or_else(|| invariant(SourceCallableInvariant::Publication(plan.declaration)))?;
    validate_global_wrapper_annotation(store, plan.return_annotation, string)?;
    if let Some(parameter) = plan.parameter {
        validate_global_wrapper_annotation(store, parameter.annotation, number)?;
    }

    let method_links = store.value_symbol_links(plan.symbol);
    let signature_links = store.signature_links(plan.declaration);
    let method_cold = method_links.is_none_or(|links| links == &ValueSymbolLinks::default());
    let signature_cold = signature_links.is_none_or(|links| links == &SignatureLinks::default());
    if method_cold && signature_cold {
        if let Some(parameter) = plan.parameter
            && !default_parameter_links(store, parameter.symbol)
        {
            return Err(invariant(SourceCallableInvariant::InvalidParameterCache(
                parameter.declaration,
            )));
        }
        return Ok(None);
    }
    if method_cold || signature_cold {
        return Err(invariant(SourceCallableInvariant::InvalidSignatureCache(
            plan.declaration,
        )));
    }

    let method_type = method_links
        .and_then(|links| links.resolved_type)
        .ok_or_else(|| invariant(SourceCallableInvariant::InvalidTypeCache(plan.declaration)))?;
    if method_links
        != Some(&ValueSymbolLinks {
            resolved_type: Some(method_type),
            ..ValueSymbolLinks::default()
        })
    {
        return Err(invariant(SourceCallableInvariant::InvalidTypeCache(
            plan.declaration,
        )));
    }
    let signature = signature_links
        .and_then(|links| links.resolved_signature.signature())
        .ok_or_else(|| {
            invariant(SourceCallableInvariant::InvalidSignatureCache(
                plan.declaration,
            ))
        })?;
    if signature_links
        != Some(&SignatureLinks {
            resolved_signature: ResolvedSignatureState::Resolved(signature),
            ..SignatureLinks::default()
        })
    {
        return Err(invariant(SourceCallableInvariant::InvalidSignatureCache(
            plan.declaration,
        )));
    }

    let type_record = store
        .type_payload(method_type)
        .ok_or_else(|| invariant(SourceCallableInvariant::InvalidTypeCache(plan.declaration)))?;
    let TypeData::Object(object) = type_record.data() else {
        return Err(invariant(SourceCallableInvariant::InvalidTypeCache(
            plan.declaration,
        )));
    };
    if type_record.flags() != TypeFlags::OBJECT
        || type_record.object_flags() != (ObjectFlags::ANONYMOUS | ObjectFlags::MEMBERS_RESOLVED)
        || type_record.symbol() != Some(plan.symbol)
        || type_record.alias().is_some()
        || object.target.is_some()
        || object.mapper.is_some()
        || object.instantiations != TypeCacheState::Unallocated
        || object.structured.constrained != ConstrainedTypeData::default()
        || object.structured.members.is_some()
        || object.structured.properties.is_some()
        || object.structured.signatures.as_deref() != Some(&[signature])
        || object.structured.call_signature_count != 1
        || object.structured.index_infos.is_some()
        || object
            .structured
            .object_type_without_abstract_construct_signatures
            .is_some()
    {
        return Err(invariant(SourceCallableInvariant::InvalidTypeCache(
            plan.declaration,
        )));
    }
    let record = store.signature(signature).ok_or_else(|| {
        invariant(SourceCallableInvariant::InvalidSignatureCache(
            plan.declaration,
        ))
    })?;
    let expected_parameters = plan
        .parameter
        .map(|parameter| vec![parameter.symbol])
        .unwrap_or_default();
    if record.flags() != SignatureFlags::NONE
        || record.declaration() != Some(plan.declaration)
        || !record.type_parameters().is_empty()
        || record.this_parameter().is_some()
        || record.parameters() != expected_parameters.as_slice()
        || record.resolved_return_type() != Some(string)
        || record.resolved_type_predicate().is_some()
        || record.target().is_some()
        || record.mapper().is_some()
        || record.isolated_signature_type().is_some()
        || record.composite().is_some()
        || record.min_argument_count() != 0
        || record.resolved_min_argument_count() != -1
        || store.function_signature_return_annotation(signature)
            != Some((plan.return_annotation, false))
        || store.signature_has_circular_return_type(signature)
    {
        return Err(invariant(SourceCallableInvariant::InvalidSignatureCache(
            plan.declaration,
        )));
    }

    let parameter_types = store
        .callable_signature_parameter_types(signature)
        .ok_or_else(|| {
            invariant(SourceCallableInvariant::InvalidParameterCache(
                plan.declaration,
            ))
        })?;
    match plan.parameter {
        None if !parameter_types.is_empty() => {
            return Err(invariant(SourceCallableInvariant::InvalidParameterCache(
                plan.declaration,
            )));
        }
        Some(parameter) => {
            let [type_] = parameter_types else {
                return Err(invariant(SourceCallableInvariant::InvalidParameterCache(
                    parameter.declaration,
                )));
            };
            if store.value_symbol_links(parameter.symbol)
                != Some(&ValueSymbolLinks {
                    resolved_type: Some(*type_),
                    ..ValueSymbolLinks::default()
                })
                || if strict_null_checks {
                    !valid_optional_type(
                        store,
                        Some(CanonicalArrayTargets::from_global_types(global_types)),
                        number,
                        *type_,
                    )
                } else {
                    *type_ != number
                }
            {
                return Err(invariant(SourceCallableInvariant::InvalidParameterCache(
                    parameter.declaration,
                )));
            }
        }
        None => {}
    }
    Ok(Some(method_type))
}

fn validate_global_wrapper_annotation(
    store: &CanonicalTypeMapperStore,
    node: NodeRef,
    expected: TypeId,
) -> Result<(), SourceCallableError> {
    let expected_links = TypeNodeLinks {
        resolved_type: Some(expected),
        ..TypeNodeLinks::default()
    };
    if store
        .type_node_links(node)
        .is_some_and(|links| links != &TypeNodeLinks::default() && links != &expected_links)
        || store
            .symbol_node_links(node)
            .is_some_and(|links| links != &SymbolNodeLinks::default())
    {
        return Err(invariant(SourceCallableInvariant::InvalidTypeCache(node)));
    }
    Ok(())
}

/// Validates predicate syntax against its exact function-owned parameter.
pub(super) fn plan_callable_type_predicate(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    node: NodeRef,
) -> Result<CallableTypePredicatePlan, SourceCallableError> {
    let invalid = || invariant(SourceCallableInvariant::InvalidSyntax(node));
    let record = preflight_node(store, host, node)?;
    let NodeData::TypePredicateNode(predicate) = &record.data else {
        return Err(invalid());
    };
    if record.kind != SyntaxKind::TypePredicate || record.flags.0 != 0 {
        return Err(invalid());
    }

    let mut current = node;
    let owner = loop {
        let parent = preflight_node(store, host, current)?
            .parent
            .map(|parent| NodeRef::new(node.arena, node.file, parent))
            .ok_or_else(invalid)?;
        let parent_record = preflight_node(store, host, parent)?;
        if let NodeData::ParenthesizedTypeNode(parenthesized) = &parent_record.data {
            if parent_record.kind != SyntaxKind::ParenthesizedType
                || parenthesized.type_ != current.node
            {
                return Err(invalid());
            }
            current = parent;
            continue;
        }
        break parent;
    };
    let owner_record = preflight_node(store, host, owner)?;
    let (parameters, return_type) = match &owner_record.data {
        NodeData::FunctionDeclaration(function)
            if owner_record.kind == SyntaxKind::FunctionDeclaration =>
        {
            (&function.parameters, function.type_)
        }
        NodeData::ArrowFunction(arrow) if owner_record.kind == SyntaxKind::ArrowFunction => {
            (&arrow.parameters, arrow.type_)
        }
        NodeData::FunctionTypeNode(function) if owner_record.kind == SyntaxKind::FunctionType => {
            (&function.parameters, function.type_)
        }
        _ => return Err(invalid()),
    };
    if return_type != Some(current.node) {
        return Err(invalid());
    }

    let parameter_name = NodeRef::new(node.arena, node.file, predicate.parameter_name);
    let name_record = preflight_node(store, host, parameter_name)?;
    let NodeData::Identifier(identifier) = &name_record.data else {
        return Err(SourceCallableError::Unsupported(
            SourceCallableUnsupported::TypePredicate(node),
        ));
    };
    if name_record.kind != SyntaxKind::Identifier
        || name_record.flags.0 != 0
        || name_record.parent != Some(node.node)
        || identifier.flow_node.is_some()
        || identifier.text.is_empty()
    {
        return Err(invalid());
    }

    let asserts = predicate
        .asserts_modifier
        .map(|modifier| NodeRef::new(node.arena, node.file, modifier));
    if let Some(asserts) = asserts {
        let modifier = preflight_node(store, host, asserts)?;
        if modifier.kind != SyntaxKind::AssertsKeyword
            || modifier.flags.0 != 0
            || modifier.parent != Some(node.node)
            || modifier.range.end > name_record.range.start
        {
            return Err(invalid());
        }
    }
    let narrowed_type = predicate
        .type_
        .map(|narrowed| NodeRef::new(node.arena, node.file, narrowed));
    if asserts.is_none() && narrowed_type.is_none() {
        return Err(invalid());
    }
    if let Some(narrowed_type) = narrowed_type {
        let narrowed = preflight_node(store, host, narrowed_type)?;
        if narrowed.parent != Some(node.node) || narrowed.range.start < name_record.range.end {
            return Err(invalid());
        }
    }

    let bound = host.bound_file(owner).ok_or_else(invalid)?;
    let mut selected = None;
    for (index, parameter) in parameters.nodes.iter().copied().enumerate() {
        let declaration = NodeRef::new(owner.arena, owner.file, parameter);
        let declaration_record = preflight_node(store, host, declaration)?;
        let NodeData::ParameterDeclaration(parameter) = &declaration_record.data else {
            return Err(invalid());
        };
        let name = NodeRef::new(owner.arena, owner.file, parameter.name);
        let name_record = preflight_node(store, host, name)?;
        let NodeData::Identifier(name) = &name_record.data else {
            continue;
        };
        if name.text != identifier.text {
            continue;
        }
        if parameter.dot_dot_dot_token.is_some() {
            return Err(SourceCallableError::Unsupported(
                SourceCallableUnsupported::TypePredicate(node),
            ));
        }
        let symbol = bound.symbol(declaration).ok_or_else(invalid)?;
        let symbol_record = store.symbol(symbol).ok_or_else(invalid)?;
        if store.get_merged_symbol(symbol) != Some(symbol)
            || symbol_record.flags() != SymbolFlags::FUNCTION_SCOPED_VARIABLE
            || symbol_record.check_flags() != CheckFlags::NONE
            || symbol_record.name().as_utf8() != Some(identifier.text.as_str())
            || symbol_record.declarations() != Some(&[declaration])
            || declaration_record.parent != Some(owner.node)
            || selected.replace((index, symbol)).is_some()
        {
            return Err(invalid());
        }
    }
    let Some((index, parameter_symbol)) = selected else {
        return Err(SourceCallableError::Unsupported(
            SourceCallableUnsupported::TypePredicate(node),
        ));
    };
    let parameter_index = i32::try_from(index).map_err(|_| invalid())?;
    let kind = if asserts.is_some() {
        TypePredicateKind::AssertsIdentifier
    } else {
        TypePredicateKind::Identifier
    };
    let expected_symbol = SymbolNodeLinks {
        resolved_symbol: Some(parameter_symbol),
    };
    if store
        .symbol_node_links(parameter_name)
        .is_some_and(|links| links != &SymbolNodeLinks::default() && links != &expected_symbol)
    {
        return Err(invariant(SourceCallableInvariant::InvalidTypeCache(
            parameter_name,
        )));
    }

    Ok(CallableTypePredicatePlan {
        node,
        owner,
        parameter_name,
        parameter_symbol,
        parameter_index,
        narrowed_type,
        kind,
    })
}

/// Checks the exact published predicate metadata without requiring AST access.
pub(super) fn valid_stored_callable_type_predicate(
    store: &CanonicalTypeMapperStore,
    signature: &Signature,
    annotation: Option<NodeRef>,
) -> bool {
    let predicate_annotation =
        annotation.filter(|node| store.source_node_kind(*node) == Some(SyntaxKind::TypePredicate));
    match (predicate_annotation, signature.resolved_type_predicate()) {
        (None, None) => true,
        (None, Some(_)) => false,
        (Some(_), None) => signature.resolved_return_type().is_none(),
        (Some(annotation), Some(predicate)) => {
            let Some(predicate) = store.type_predicate(predicate) else {
                return false;
            };
            let Some(bootstrap) = store.intrinsic_bootstrap() else {
                return false;
            };
            let expected_return = match predicate.kind() {
                TypePredicateKind::Identifier if predicate.type_id().is_some() => {
                    bootstrap.boolean_type
                }
                TypePredicateKind::AssertsIdentifier => bootstrap.void_type,
                _ => return false,
            };
            let Ok(index) = usize::try_from(predicate.parameter_index()) else {
                return false;
            };
            let Some(parameter) = signature.parameters().get(index).copied() else {
                return false;
            };
            let Some(parameter_record) = store.symbol(parameter) else {
                return false;
            };
            parameter_record.name().as_utf8() == Some(predicate.parameter_name())
                && predicate
                    .type_id()
                    .is_none_or(|type_| store.type_payload(type_).is_some())
                && signature
                    .resolved_return_type()
                    .is_none_or(|type_| type_ == expected_return)
                && store.type_node_links(annotation)
                    == Some(&TypeNodeLinks {
                        resolved_type: Some(expected_return),
                        outer_type_parameters: None,
                    })
        }
    }
}

/// Matches published predicate metadata against the complete planned AST.
pub(super) fn valid_planned_callable_type_predicate(
    store: &CanonicalTypeMapperStore,
    signature: &Signature,
    annotation: Option<NodeRef>,
    planned: Option<CallableTypePredicatePlan>,
) -> bool {
    if !valid_stored_callable_type_predicate(store, signature, annotation) {
        return false;
    }
    match (planned, signature.resolved_type_predicate()) {
        (None, None) => true,
        (None, Some(_)) => false,
        (Some(planned), None) => {
            annotation == Some(planned.node)
                && signature.resolved_return_type().is_none()
                && store
                    .type_node_links(planned.node)
                    .is_none_or(|links| links == &TypeNodeLinks::default())
                && store
                    .symbol_node_links(planned.parameter_name)
                    .is_none_or(|links| links == &SymbolNodeLinks::default())
        }
        (Some(planned), Some(predicate)) => {
            let Some(record) = store.type_predicate(predicate) else {
                return false;
            };
            let narrowed = planned
                .narrowed_type
                .map(|node| cached_annotation_identity(store, node, false));
            annotation == Some(planned.node)
                && signature.declaration() == Some(planned.owner)
                && record.kind() == planned.kind
                && record.parameter_index() == planned.parameter_index
                && record.type_id() == narrowed.flatten()
                && narrowed.is_none_or(|narrowed| narrowed.is_some())
                && store.symbol_node_links(planned.parameter_name)
                    == Some(&SymbolNodeLinks {
                        resolved_symbol: Some(planned.parameter_symbol),
                    })
        }
    }
}

/// Plans one exact source callable without publishing semantic records.
pub(super) fn plan_source_callable(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    declaration: NodeRef,
    owner_symbol: SemanticSymbolId,
    array_targets: Option<CanonicalArrayTargets>,
) -> Result<SourceCallablePlan, SourceCallableError> {
    plan_source_callable_with_owner_shape(
        store,
        host,
        declaration,
        owner_symbol,
        array_targets,
        SourceCallableOwnerShape::Unique,
    )
}

/// Plans one declaration belonging to an exact local ambient overload group.
///
/// Publication and warm validation remain owned by `source_overloads`; this
/// entry point only reuses the established declaration/parameter annotation
/// proof without pretending that the declaration owns a singleton callable.
pub(super) fn plan_source_ambient_overload_declaration(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    declaration: NodeRef,
    owner_symbol: SemanticSymbolId,
    declarations: &[NodeRef],
    array_targets: Option<CanonicalArrayTargets>,
) -> Result<SourceCallablePlan, SourceCallableError> {
    plan_source_callable_with_owner_shape(
        store,
        host,
        declaration,
        owner_symbol,
        array_targets,
        SourceCallableOwnerShape::AmbientOverload(declarations),
    )
}

/// Plans a later JavaScript implementation without publishing another callable.
pub(super) fn plan_javascript_duplicate_function_implementation(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    declaration: NodeRef,
    owner_symbol: SemanticSymbolId,
    array_targets: Option<CanonicalArrayTargets>,
) -> Result<SourceCallablePlan, SourceCallableError> {
    plan_source_callable_with_owner_shape(
        store,
        host,
        declaration,
        owner_symbol,
        array_targets,
        SourceCallableOwnerShape::JavaScriptDuplicateImplementation,
    )
}

fn plan_source_callable_with_owner_shape(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    declaration: NodeRef,
    owner_symbol: SemanticSymbolId,
    array_targets: Option<CanonicalArrayTargets>,
    owner_shape: SourceCallableOwnerShape<'_>,
) -> Result<SourceCallablePlan, SourceCallableError> {
    let record = preflight_node(store, host, declaration)?;
    let view = match &record.data {
        NodeData::FunctionDeclaration(function)
            if record.kind == SyntaxKind::FunctionDeclaration =>
        {
            SourceSyntaxView {
                family: SourceCallableFamily::FunctionDeclaration,
                parameters: &function.parameters,
                modifiers: function.modifiers.as_ref(),
                type_parameters: function.type_parameters.as_ref(),
                return_type: function.type_,
                body: function.body,
                asterisk_token: function.asterisk_token,
                name: function.name,
                equals_greater_than_token: None,
                invalid_parser_cache: function.full_signature.is_some()
                    || function.next_container.is_some()
                    || function.symbol.is_some()
                    || function.local_symbol.is_some()
                    || function.flow_node.is_some()
                    || function.end_flow_node.is_some()
                    || function.return_flow_node.is_some(),
            }
        }
        NodeData::ArrowFunction(function) if record.kind == SyntaxKind::ArrowFunction => {
            SourceSyntaxView {
                family: SourceCallableFamily::ArrowFunction,
                parameters: &function.parameters,
                modifiers: function.modifiers.as_ref(),
                type_parameters: function.type_parameters.as_ref(),
                return_type: function.type_,
                body: Some(function.body),
                asterisk_token: function.asterisk_token,
                name: None,
                equals_greater_than_token: Some(function.equals_greater_than_token),
                invalid_parser_cache: function.full_signature.is_some()
                    || function.next_container.is_some()
                    || function.symbol.is_some()
                    || function.flow_node.is_some()
                    || function.end_flow_node.is_some(),
            }
        }
        NodeData::FunctionExpression(function) if record.kind == SyntaxKind::FunctionExpression => {
            if let Some(name) = function.name {
                let name = NodeRef::new(declaration.arena, declaration.file, name);
                preflight_child(store, host, declaration, name)?;
                return Err(SourceCallableError::Unsupported(
                    SourceCallableUnsupported::OverloadDeclaration(name),
                ));
            }
            SourceSyntaxView {
                family: SourceCallableFamily::ArrowFunction,
                parameters: &function.parameters,
                modifiers: function.modifiers.as_ref(),
                type_parameters: function.type_parameters.as_ref(),
                return_type: function.type_,
                body: Some(function.body),
                asterisk_token: function.asterisk_token,
                name: None,
                equals_greater_than_token: None,
                invalid_parser_cache: function.full_signature.is_some()
                    || function.next_container.is_some()
                    || function.symbol.is_some()
                    || function.flow_node.is_some()
                    || function.end_flow_node.is_some()
                    || function.return_flow_node.is_some()
                    || function.facts != 0,
            }
        }
        _ => {
            return Err(invariant(SourceCallableInvariant::InvalidSyntax(
                declaration,
            )));
        }
    };
    if record.flags.0 & NODE_FLAG_JSDOC != 0
        || view.invalid_parser_cache
        || view.parameters.range.start < record.range.start
        || view.parameters.range.end > record.range.end
    {
        return Err(invariant(SourceCallableInvariant::InvalidSyntax(
            declaration,
        )));
    }
    let type_parameters = plan_exact_source_type_parameters(
        store,
        host,
        declaration,
        view.family,
        view.type_parameters,
        view.parameters,
    )?;
    let type_parameter_syntax =
        prove_source_type_parameter_syntax(store, host, declaration, &type_parameters)?;
    if let Some(asterisk) = view.asterisk_token {
        let asterisk = NodeRef::new(declaration.arena, declaration.file, asterisk);
        preflight_child(store, host, declaration, asterisk)?;
        return Err(SourceCallableError::Unsupported(
            SourceCallableUnsupported::Generator(asterisk),
        ));
    }
    let body_mode = validate_modifiers(store, host, declaration, record.range, &view)?;
    let is_async = view.is_async(store, declaration);

    let bound = host
        .bound_file(declaration)
        .ok_or_else(|| invariant(SourceCallableInvariant::InvalidOwnerSymbol(declaration)))?;
    let javascript_jsdoc_generic_arrow = view.family == SourceCallableFamily::ArrowFunction
        && !type_parameters.is_empty()
        && bound
            .source_facts()
            .is_some_and(CanonicalSourceFileFacts::is_javascript_file);
    if body_mode.is_ambient() && bound.source_facts().is_none() {
        return Err(SourceCallableError::Unsupported(
            SourceCallableUnsupported::Modifiers(declaration),
        ));
    }
    if bound.symbol(declaration) != Some(owner_symbol)
        || store.get_merged_symbol(owner_symbol) != Some(owner_symbol)
    {
        return Err(invariant(SourceCallableInvariant::InvalidOwnerSymbol(
            declaration,
        )));
    }
    let owner = store
        .symbol(owner_symbol)
        .ok_or_else(|| invariant(SourceCallableInvariant::InvalidOwnerSymbol(declaration)))?;
    let export_local = bound.local_symbol(declaration);
    let javascript_duplicate_owner = owner
        .declarations()
        .and_then(|declarations| declarations.first())
        .copied()
        .is_some_and(|first| {
            valid_javascript_duplicate_function_owner_shape(store, host, owner_symbol, first)
        });
    let exact_owner_declarations = match owner_shape {
        SourceCallableOwnerShape::Unique => {
            source_function_owner_declarations_are_exact(store, owner, declaration)
                || javascript_duplicate_owner && owner.value_declaration() == Some(declaration)
        }
        SourceCallableOwnerShape::AmbientOverload(declarations) => {
            declarations.len() >= 2
                && declarations.contains(&declaration)
                && owner.declarations() == Some(declarations)
                && owner.value_declaration() == declarations.first().copied()
                && owner.parent().is_none()
                && export_local.is_none()
        }
        SourceCallableOwnerShape::JavaScriptDuplicateImplementation => {
            javascript_duplicate_owner
                && owner.value_declaration() != Some(declaration)
                && owner
                    .declarations()
                    .is_some_and(|declarations| declarations.contains(&declaration))
                && export_local.is_none()
        }
    };
    if !owner.flags().contains(SymbolFlags::FUNCTION)
        || owner.check_flags() != CheckFlags::NONE
        || !exact_owner_declarations
        || owner.members().is_some()
        || owner.export_symbol().is_some()
    {
        return Err(invariant(SourceCallableInvariant::InvalidOwnerSymbol(
            declaration,
        )));
    }
    validate_owner_name_and_export_route(
        store,
        host,
        declaration,
        owner,
        export_local,
        body_mode,
        &view,
    )?;
    let exports_valid = if view.family == SourceCallableFamily::ArrowFunction {
        bound_source_arrow_owner_expando_exports_are_valid(store, host, declaration, owner_symbol)
    } else if owner.flags() == SymbolFlags::FUNCTION && owner.exports().is_some() {
        bound_source_function_owner_expando_exports_are_valid(
            store,
            host,
            declaration,
            owner_symbol,
        )
    } else {
        source_function_owner_exports_are_valid(store, owner_symbol, owner)
    };
    if !exports_valid {
        return Err(SourceCallableError::Unsupported(
            SourceCallableUnsupported::ExpandoProperties(declaration),
        ));
    }
    if !type_parameters.is_empty() && owner.flags() != SymbolFlags::FUNCTION {
        return Err(SourceCallableError::Unsupported(
            SourceCallableUnsupported::GenericSignature(declaration),
        ));
    }
    let array_targets = namespace_source_callable_array_targets(
        store,
        host,
        declaration,
        owner_symbol,
        owner,
        export_local,
        &view,
        body_mode,
        array_targets,
    );
    let implicit_any_arrow_shape = view.family == SourceCallableFamily::ArrowFunction
        && !view.parameters.nodes.is_empty()
        && !view.parameters.has_trailing_comma
        && view.return_type.is_none()
        && type_parameters.is_empty();
    let eligible_implicit_any_arrow = implicit_any_arrow_shape && view.parameters.nodes.len() == 1;
    let javascript_documented_multi_arrow = implicit_any_arrow_shape
        && record.kind == SyntaxKind::ArrowFunction
        && view.parameters.nodes.len() > 1
        && bound
            .source_facts()
            .is_some_and(CanonicalSourceFileFacts::is_javascript_file)
        && is_direct_noncontextual_source_arrow(store, host, declaration)?
        && source_jsdoc_arrow_parameters_are_exact(store, host, declaration, view.parameters)?;
    let direct_implicit_any_arrow = (eligible_implicit_any_arrow
        || javascript_documented_multi_arrow)
        && is_direct_noncontextual_source_arrow(store, host, declaration)?;
    let direct_implicit_any_rest_arrow = implicit_any_arrow_shape
        && view.parameters.nodes.iter().any(|parameter| {
            host.node(NodeRef::new(
                declaration.arena,
                declaration.file,
                *parameter,
            ))
            .is_some_and(|record| {
                matches!(
                    &record.data,
                    NodeData::ParameterDeclaration(parameter)
                        if parameter.dot_dot_dot_token.is_some() && parameter.type_.is_none()
                )
            })
        })
        && is_direct_noncontextual_source_arrow(store, host, declaration)?;
    let array_implicit_any_arrow = eligible_implicit_any_arrow
        && !direct_implicit_any_arrow
        && is_ambiguous_union_array_source_arrow(store, host, declaration)?;
    let object_property_arrow = eligible_implicit_any_arrow
        && !direct_implicit_any_arrow
        && !array_implicit_any_arrow
        && source_object_property_arrow_symbol(store, host, declaration)?.is_some();
    let array_sort_argument_arrow = implicit_any_arrow_shape
        && view.parameters.nodes.len() == 2
        && source_array_sort_argument_arrow_is_exact(store, host, declaration);
    let direct_call_argument_arrow = implicit_any_arrow_shape
        && !direct_implicit_any_arrow
        && !array_implicit_any_arrow
        && !object_property_arrow
        && (source_direct_call_argument_arrow_is_exact(store, host, declaration)?
            || source_promise_constructor_argument_arrow_is_exact(store, host, declaration)?)
        && (eligible_implicit_any_arrow
            || array_sort_argument_arrow
            || source_direct_call_arrow_has_zero_parameter_target(store, host, declaration)?);
    let javascript_object_implicit_any_arrow = eligible_implicit_any_arrow
        && object_property_arrow
        && bound
            .source_facts()
            .is_some_and(CanonicalSourceFileFacts::is_javascript_file);
    let javascript_direct_implicit_any_arrow = direct_implicit_any_arrow
        && bound
            .source_facts()
            .is_some_and(CanonicalSourceFileFacts::is_javascript_file);
    let javascript_jsdoc_function_parameter = if view.family
        == SourceCallableFamily::FunctionDeclaration
        && view.parameters.nodes.len() == 1
        && type_parameters.is_empty()
        && body_mode == SourceCallableBodyMode::Present
        && bound
            .source_facts()
            .is_some_and(CanonicalSourceFileFacts::is_javascript_file)
    {
        source_jsdoc_function_parameter_annotation(store, host, declaration, view.parameters)?
    } else {
        None
    };
    let untyped_javascript_signature = bound
        .source_facts()
        .is_some_and(CanonicalSourceFileFacts::is_javascript_file)
        && (view.parameters.nodes.len() == 1 || javascript_documented_multi_arrow)
        && type_parameters.is_empty()
        && body_mode == SourceCallableBodyMode::Present
        && (view.family == SourceCallableFamily::FunctionDeclaration
            || javascript_object_implicit_any_arrow
            || javascript_direct_implicit_any_arrow)
        && javascript_jsdoc_function_parameter.is_none()
        && view.parameters.nodes.iter().all(|parameter| {
            host.node(NodeRef::new(
                declaration.arena,
                declaration.file,
                *parameter,
            ))
            .is_some_and(|record| {
                matches!(&record.data, NodeData::ParameterDeclaration(parameter)
                        if parameter.type_.is_none())
            })
        });

    let mut parameters = Vec::with_capacity(view.parameters.nodes.len());
    let mut previous_end = view.parameters.range.start;
    let mut optional_seen = false;
    let mut min_argument_count = 0usize;
    let mut flags = if untyped_javascript_signature {
        SignatureFlags::IS_UNTYPED_SIGNATURE_IN_JS_FILE
    } else {
        SignatureFlags::NONE
    };
    for parameter_id in &view.parameters.nodes {
        let parameter = NodeRef::new(declaration.arena, declaration.file, *parameter_id);
        if parameters
            .iter()
            .any(|planned: &SourceCallableParameterPlan| planned.declaration == parameter)
        {
            return Err(invariant(SourceCallableInvariant::InvalidParameter(
                parameter,
            )));
        }
        let parameter_record = preflight_node(store, host, parameter)?;
        let NodeData::ParameterDeclaration(data) = &parameter_record.data else {
            return Err(invariant(SourceCallableInvariant::InvalidParameter(
                parameter,
            )));
        };
        if parameter_record.kind != SyntaxKind::Parameter
            || parameter_record.parent != Some(declaration.node)
            || parameter_record.flags.0 & NODE_FLAG_JSDOC != 0
            || parameter_record.range.start < previous_end
            || parameter_record.range.start < view.parameters.range.start
            || parameter_record.range.end > view.parameters.range.end
            || data.symbol.is_some()
            || data.facts != 0
        {
            return Err(invariant(SourceCallableInvariant::InvalidParameter(
                parameter,
            )));
        }
        previous_end = parameter_record.range.end;
        let name = NodeRef::new(declaration.arena, declaration.file, data.name);
        let name_record = preflight_node(store, host, name)?;
        let parameter_name = match (&name_record.data, name_record.kind) {
            (NodeData::Identifier(identifier), SyntaxKind::Identifier) => identifier.text.clone(),
            (NodeData::BindingPattern(pattern), SyntaxKind::ArrayBindingPattern)
                if array_sort_argument_arrow
                    && host.source(name).is_some_and(|(arena, _)| {
                        super::source_calls::is_authenticated_sort_tuple_binding(
                            arena, name.node, pattern,
                        )
                    }) =>
            {
                format!("__{}", parameters.len())
            }
            _ => {
                return Err(SourceCallableError::Unsupported(
                    SourceCallableUnsupported::DestructuredParameter(parameter),
                ));
            }
        };
        if name_record.parent != Some(parameter.node)
            || name_record.range.start < parameter_record.range.start
            || name_record.range.end > parameter_record.range.end
        {
            return Err(invariant(SourceCallableInvariant::InvalidParameter(
                parameter,
            )));
        }
        if let Some(modifiers) = data.modifiers.as_ref()
            && (data.type_.is_some()
                || data.initializer.is_some()
                || data.question_token.is_some()
                || data.dot_dot_dot_token.is_some()
                || !valid_ordinary_function_public_parameter(
                    store,
                    host,
                    declaration,
                    &view,
                    body_mode,
                    parameter,
                    parameter_record.range,
                    name_record.range.start,
                    modifiers,
                )?)
        {
            return Err(SourceCallableError::Unsupported(
                SourceCallableUnsupported::ParameterModifiers(parameter),
            ));
        }
        if parameter_name == "this"
            && !(view.family == SourceCallableFamily::FunctionDeclaration
                && view.parameters.nodes.len() == 1
                && data.type_.is_none()
                && !body_mode.is_ambient()
                && type_parameters.is_empty()
                && bound
                    .source_facts()
                    .is_some_and(CanonicalSourceFileFacts::is_javascript_file))
        {
            return Err(SourceCallableError::Unsupported(
                SourceCallableUnsupported::ThisParameter(parameter),
            ));
        }
        let rest = if let Some(dot_id) = data.dot_dot_dot_token {
            let dot = NodeRef::new(declaration.arena, declaration.file, dot_id);
            let dot_record = preflight_node(store, host, dot)?;
            if dot_record.kind != SyntaxKind::DotDotDotToken
                || dot_record.parent != Some(parameter.node)
                || dot_record.range.start < parameter_record.range.start
                || dot_record.range.end > name_record.range.start
            {
                return Err(invariant(SourceCallableInvariant::InvalidParameter(
                    parameter,
                )));
            }
            if matches!(owner_shape, SourceCallableOwnerShape::AmbientOverload(_)) {
                return Err(SourceCallableError::Unsupported(
                    SourceCallableUnsupported::AmbientRestParameter(parameter),
                ));
            }
            true
        } else {
            false
        };
        if rest && parameters.len() + 1 != view.parameters.nodes.len() {
            return Err(SourceCallableError::Unsupported(
                SourceCallableUnsupported::RestParameterNotLast(parameter),
            ));
        }
        let initializer = data
            .initializer
            .map(|initializer| NodeRef::new(declaration.arena, declaration.file, initializer));
        let (type_node, type_start, type_end, identity_node, null_literal_identity, implicit_any) =
            if let Some(type_id) = data.type_ {
                let type_node = NodeRef::new(declaration.arena, declaration.file, type_id);
                let type_record = preflight_node(store, host, type_node)?;
                let reparsed_jsdoc =
                    javascript_jsdoc_generic_arrow && type_record.flags == NodeFlags::REPARSED;
                if type_record.parent != Some(parameter.node)
                    || !reparsed_jsdoc
                        && (type_record.range.start < name_record.range.end
                            || type_record.range.end > parameter_record.range.end)
                    || reparsed_jsdoc && type_record.range.end >= record.range.start
                {
                    return Err(invariant(SourceCallableInvariant::InvalidParameter(
                        parameter,
                    )));
                }
                let identity_node = peel_parenthesized_type(store, host, type_node)?;
                if type_record.kind == SyntaxKind::LiteralType {
                    flags |= SignatureFlags::HAS_LITERAL_TYPES;
                }
                (
                    type_node,
                    type_record.range.start,
                    type_record.range.end,
                    identity_node,
                    is_null_literal_type(store, host, identity_node)?,
                    false,
                )
            } else {
                if !(view.family == SourceCallableFamily::FunctionDeclaration
                    || direct_implicit_any_arrow
                        && (view.parameters.range == parameter_record.range
                            || javascript_direct_implicit_any_arrow
                                && view.parameters.range.start < parameter_record.range.start
                                && view.parameters.range.end > parameter_record.range.end)
                    || array_implicit_any_arrow
                        && view.parameters.range.start < parameter_record.range.start
                        && view.parameters.range.end > parameter_record.range.end
                    || object_property_arrow
                        && view.parameters.nodes.as_slice() == [parameter.node]
                    || direct_call_argument_arrow
                    || direct_implicit_any_rest_arrow)
                    || body_mode.is_ambient() && !rest
                    || !type_parameters.is_empty()
                    || initializer.is_some()
                    || rest
                        && implicit_any_array_type(store).is_none_or(|array| {
                            array_targets.is_none()
                                && store
                                    .intrinsic_bootstrap()
                                    .is_none_or(|bootstrap| array != bootstrap.empty_object_type)
                        })
                {
                    return Err(SourceCallableError::Unsupported(
                        SourceCallableUnsupported::MissingParameterType(parameter),
                    ));
                }
                (
                    name,
                    parameter_record.range.end,
                    name_record.range.end,
                    name,
                    false,
                    true,
                )
            };
        let optional = validate_optional_token(
            store,
            host,
            parameter,
            data.question_token,
            name_record.range.end,
            type_start,
        )?;
        if let Some(initializer) = initializer {
            let initializer_record = preflight_node(store, host, initializer)?;
            if initializer_record.parent != Some(parameter.node)
                || initializer_record.range.start < type_end
                || initializer_record.range.end > parameter_record.range.end
            {
                return Err(invariant(SourceCallableInvariant::InvalidParameter(
                    parameter,
                )));
            }
            if body_mode.is_ambient() {
                return Err(SourceCallableError::Unsupported(
                    SourceCallableUnsupported::AmbientParameterInitializer(parameter),
                ));
            }
        }
        if rest && optional {
            return Err(SourceCallableError::Unsupported(
                SourceCallableUnsupported::OptionalRestParameter(parameter),
            ));
        }
        if rest && initializer.is_some() {
            return Err(SourceCallableError::Unsupported(
                SourceCallableUnsupported::InitializedRestParameter(parameter),
            ));
        }
        if optional && initializer.is_some() {
            return Err(SourceCallableError::Unsupported(
                SourceCallableUnsupported::OptionalInitializedParameter(parameter),
            ));
        }
        if rest {
            flags |= SignatureFlags::HAS_REST_PARAMETER;
        } else if optional {
            optional_seen = true;
        } else if optional_seen && initializer.is_none() {
            return Err(SourceCallableError::Unsupported(
                SourceCallableUnsupported::RequiredAfterOptional(parameter),
            ));
        }
        if !optional && initializer.is_none() && !rest {
            min_argument_count = parameters.len() + 1;
        }
        let raw_symbol = bound
            .symbol(parameter)
            .ok_or_else(|| invariant(SourceCallableInvariant::InvalidParameterSymbol(parameter)))?;
        let symbol = store
            .get_merged_symbol(raw_symbol)
            .ok_or_else(|| invariant(SourceCallableInvariant::InvalidParameterSymbol(parameter)))?;
        let symbol_record = store
            .symbol(symbol)
            .ok_or_else(|| invariant(SourceCallableInvariant::InvalidParameterSymbol(parameter)))?;
        if symbol == raw_symbol
            && symbol_record.flags() == SymbolFlags::FUNCTION_SCOPED_VARIABLE
            && symbol_record.check_flags() == CheckFlags::NONE
            && symbol_record.name().as_bytes() == parameter_name.as_bytes()
            && symbol_record.members().is_none()
            && symbol_record.exports().is_none()
            && symbol_record.parent().is_none()
            && symbol_record.export_symbol().is_none()
            && symbol_record.declarations().is_some_and(|declarations| {
                declarations.len() > 1
                    && declarations
                        .iter()
                        .filter(|candidate| **candidate == parameter)
                        .count()
                        == 1
                    && declarations.iter().all(|candidate| {
                        candidate.is_for(declaration.arena, declaration.file)
                            && bound.symbol(*candidate) == Some(symbol)
                            && (*candidate == parameter
                                || store.source_node_kind(*candidate)
                                    == Some(SyntaxKind::VariableDeclaration))
                    })
            })
        {
            return Err(SourceCallableError::Unsupported(
                SourceCallableUnsupported::OverloadDeclaration(parameter),
            ));
        }
        if symbol != raw_symbol
            || symbol_record.flags() != SymbolFlags::FUNCTION_SCOPED_VARIABLE
            || symbol_record.check_flags() != CheckFlags::NONE
            || symbol_record.name().as_bytes() != parameter_name.as_bytes()
            || symbol_record.declarations() != Some(&[parameter])
            || symbol_record.value_declaration() != Some(parameter)
            || symbol_record.members().is_some()
            || symbol_record.exports().is_some()
            || symbol_record.parent().is_some()
            || symbol_record.export_symbol().is_some()
        {
            return Err(invariant(SourceCallableInvariant::InvalidParameterSymbol(
                parameter,
            )));
        }
        parameters.push(SourceCallableParameterPlan {
            declaration: parameter,
            symbol,
            type_node,
            identity_node,
            null_literal_identity,
            implicit_any,
            jsdoc_function: javascript_jsdoc_function_parameter
                .as_ref()
                .is_some_and(|(declaration, _)| *declaration == parameter),
            jsdoc_contextual_type: None,
            optional,
            initializer,
            rest,
        });
    }

    let mut type_predicate = None;
    let (return_type, return_end) = if let Some(return_id) = view.return_type {
        let type_node = NodeRef::new(declaration.arena, declaration.file, return_id);
        let return_record = preflight_node(store, host, type_node)?;
        let reparsed_jsdoc =
            javascript_jsdoc_generic_arrow && return_record.flags == NodeFlags::REPARSED;
        if return_record.parent != Some(declaration.node)
            || !reparsed_jsdoc
                && (return_record.range.start < view.parameters.range.end
                    || return_record.range.end > record.range.end)
            || reparsed_jsdoc && return_record.range.end >= record.range.start
        {
            return Err(invariant(SourceCallableInvariant::InvalidSyntax(
                declaration,
            )));
        }
        let identity_node = peel_parenthesized_type(store, host, type_node)?;
        if preflight_node(store, host, identity_node)?.kind == SyntaxKind::TypePredicate {
            if view.family != SourceCallableFamily::FunctionDeclaration
                || matches!(owner_shape, SourceCallableOwnerShape::AmbientOverload(_))
            {
                return Err(SourceCallableError::Unsupported(
                    SourceCallableUnsupported::TypePredicate(type_node),
                ));
            }
            let predicate = plan_callable_type_predicate(store, host, identity_node)?;
            if predicate.owner != declaration
                || parameters
                    .get(usize::try_from(predicate.parameter_index).unwrap_or(usize::MAX))
                    .is_none_or(|parameter| parameter.symbol != predicate.parameter_symbol)
            {
                return Err(invariant(SourceCallableInvariant::InvalidSyntax(
                    identity_node,
                )));
            }
            type_predicate = Some(predicate);
        }
        (
            SourceCallableReturnPlan::Annotated {
                type_node,
                identity_node,
                null_literal_identity: is_null_literal_type(store, host, identity_node)?,
            },
            return_record.range.end,
        )
    } else if body_mode.is_ambient() {
        if !type_parameters.is_empty()
            || matches!(owner_shape, SourceCallableOwnerShape::AmbientOverload(_))
        {
            return Err(SourceCallableError::Unsupported(
                SourceCallableUnsupported::OverloadDeclaration(declaration),
            ));
        }
        (
            SourceCallableReturnPlan::AmbientImplicitAny,
            view.parameters.range.end,
        )
    } else {
        (
            SourceCallableReturnPlan::Inferred,
            view.parameters.range.end,
        )
    };
    let (body, body_start) = match (body_mode, view.body) {
        (SourceCallableBodyMode::Present, Some(body_id)) => {
            let body = NodeRef::new(declaration.arena, declaration.file, body_id);
            let body_record = preflight_node(store, host, body)?;
            if body_record.parent != Some(declaration.node)
                || body_record.range.start < return_end
                || body_record.range.end > record.range.end
                || view.family == SourceCallableFamily::FunctionDeclaration
                    && body_record.kind != SyntaxKind::Block
            {
                return Err(invariant(SourceCallableInvariant::InvalidSyntax(
                    declaration,
                )));
            }
            (body, body_record.range.start)
        }
        (SourceCallableBodyMode::Present, None) => {
            return Err(SourceCallableError::Unsupported(
                SourceCallableUnsupported::OverloadDeclaration(declaration),
            ));
        }
        (SourceCallableBodyMode::AmbientDeclaration, None) => (declaration, record.range.end),
        (SourceCallableBodyMode::AmbientDeclaration, Some(_)) => {
            return Err(SourceCallableError::Unsupported(
                SourceCallableUnsupported::Modifiers(declaration),
            ));
        }
    };
    let inferred_empty_body_is_exact = !type_parameters.is_empty() && return_type.is_inferred();
    if inferred_empty_body_is_exact {
        let body_record = preflight_node(store, host, body)?;
        let NodeData::Block(block) = &body_record.data else {
            return Err(SourceCallableError::Unsupported(
                SourceCallableUnsupported::GenericInferredReturn(declaration),
            ));
        };
        let supported_parameter_shape = parameters.is_empty() && min_argument_count == 0
            || match (type_parameters.as_slice(), parameters.as_slice()) {
                ([type_parameter], [parameter])
                    if min_argument_count == 1
                        && !parameter.optional
                        && !parameter.rest
                        && parameter.initializer.is_none()
                        && parameter.explicit_type_node().is_some() =>
                {
                    type_parameter.constraint.is_some_and(|constraint| {
                        exact_unresolved_source_type_parameter_constraint(store, host, constraint)
                            .is_ok_and(|valid| valid)
                    }) && is_naked_source_type_parameter_annotation(
                        store,
                        host,
                        parameter.identity_node,
                        type_parameter,
                    )?
                }
                _ => false,
            };
        if view.family != SourceCallableFamily::FunctionDeclaration
            || body_mode != SourceCallableBodyMode::Present
            || !supported_parameter_shape
            || flags != SignatureFlags::NONE
            || body_record.kind != SyntaxKind::Block
            || body_record.parent != Some(declaration.node)
            || body_record.flags.0 != 0
            || block.flow_node.is_some()
            || block.next_container.is_some()
            || !block.statements.nodes.is_empty()
            || block.statements.has_trailing_comma
            || block.facts != 0
        {
            return Err(SourceCallableError::Unsupported(
                SourceCallableUnsupported::GenericInferredReturn(declaration),
            ));
        }
    }
    if let Some(token_id) = view.equals_greater_than_token {
        let token = NodeRef::new(declaration.arena, declaration.file, token_id);
        let token_record = preflight_node(store, host, token)?;
        if token_record.kind != SyntaxKind::EqualsGreaterThanToken
            || token_record.parent != Some(declaration.node)
            || token_record.range.start < return_end
            || token_record.range.end > body_start
        {
            return Err(invariant(SourceCallableInvariant::InvalidSyntax(
                declaration,
            )));
        }
    }
    let min_argument_count = i32::try_from(min_argument_count)
        .map_err(|_| invariant(SourceCallableInvariant::Capacity(declaration)))?;
    let mut plan = SourceCallablePlan {
        family: view.family,
        declaration,
        owner_symbol,
        owner_parent: owner.parent(),
        export_local,
        javascript_duplicate_owner: javascript_duplicate_owner
            && matches!(owner_shape, SourceCallableOwnerShape::Unique),
        type_parameters,
        type_parameter_syntax: Box::new(type_parameter_syntax),
        generic_return_type_parameter_index: None,
        parameters,
        return_type,
        type_predicate,
        body_mode,
        is_async,
        body,
        flags,
        min_argument_count,
        array_targets,
    };
    if javascript_direct_implicit_any_arrow {
        hydrate_warm_jsdoc_contextual_source_callable(store, host, &mut plan)?;
    }
    if let Some((parameter, annotation)) = javascript_jsdoc_function_parameter {
        hydrate_warm_jsdoc_function_parameter(store, &mut plan, parameter, &annotation)?;
    }
    plan.generic_return_type_parameter_index = if plan.return_type.is_inferred() {
        None
    } else {
        validate_exact_generic_annotation_shape(store, host, &plan)?
    };
    plan.type_parameter_syntax
        .generic_return_type_parameter_declaration = plan
        .generic_return_type_parameter_index
        .map(|index| plan.type_parameters[index].declaration);
    plan.type_parameter_syntax.generic_fixed_return_is_exact = !plan.return_type.is_inferred()
        && !plan.type_parameters.is_empty()
        && plan.generic_return_type_parameter_index.is_none();
    plan.type_parameter_syntax.inferred_empty_body_is_exact = inferred_empty_body_is_exact;
    match owner_shape {
        SourceCallableOwnerShape::Unique => {
            let contextual_source_arrow = (object_property_arrow || direct_call_argument_arrow)
                && store
                    .source_callable_type_for_owner(owner_symbol)
                    .and_then(|type_| store.source_callable_provenance(type_))
                    .is_some_and(|provenance| {
                        provenance.declaration == declaration
                            && provenance.owner_symbol == owner_symbol
                            && provenance.contextual_target.is_some()
                            && (direct_call_argument_arrow
                                && provenance.contextual_variable.is_none()
                                || object_property_arrow
                                    && provenance.contextual_variable.is_some_and(|anchor| {
                                        store.source_contextual_callable_anchor_is_exact(
                                            declaration,
                                            owner_symbol,
                                            anchor,
                                        ) && store.symbol(anchor).is_some_and(|symbol| {
                                            symbol.flags() == SymbolFlags::PROPERTY
                                        })
                                    }))
                    });
            if contextual_source_arrow {
                let type_ = store
                    .source_callable_type_for_owner(owner_symbol)
                    .expect("the contextual source arrow already retained its owner");
                if !matches!(
                    validate_stored_source_callable(store, type_),
                    StoredSourceCallableValidation::Valid(_)
                ) {
                    return Err(invariant(SourceCallableInvariant::InvalidTypeCache(
                        declaration,
                    )));
                }
            } else {
                source_callable_state(store, &plan, true)?;
            }
        }
        SourceCallableOwnerShape::AmbientOverload(_) => {
            if plan.family != SourceCallableFamily::FunctionDeclaration
                || plan.body_mode != SourceCallableBodyMode::AmbientDeclaration
                || !plan.type_parameters.is_empty()
                || plan.return_type.is_inferred()
                || plan.export_local.is_some()
                || plan.owner_parent.is_some()
                || plan
                    .parameters
                    .iter()
                    .any(|parameter| parameter.rest || parameter.initializer.is_some())
            {
                return Err(SourceCallableError::Unsupported(
                    SourceCallableUnsupported::OverloadDeclaration(declaration),
                ));
            }
        }
        SourceCallableOwnerShape::JavaScriptDuplicateImplementation => {
            if plan.family != SourceCallableFamily::FunctionDeclaration
                || plan.body_mode != SourceCallableBodyMode::Present
                || !plan.type_parameters.is_empty()
                || plan.export_local.is_some()
                || plan.owner_parent.is_some()
            {
                return Err(SourceCallableError::Unsupported(
                    SourceCallableUnsupported::OverloadDeclaration(declaration),
                ));
            }
        }
    }
    Ok(plan)
}

#[allow(clippy::too_many_arguments)] // Only exact namespace-owned void functions inherit warm targets.
fn namespace_source_callable_array_targets(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    declaration: NodeRef,
    owner_symbol: SemanticSymbolId,
    owner: &ts_binder::semantic::Symbol,
    export_local: Option<SemanticSymbolId>,
    view: &SourceSyntaxView<'_>,
    body_mode: SourceCallableBodyMode,
    array_targets: Option<CanonicalArrayTargets>,
) -> Option<CanonicalArrayTargets> {
    if array_targets.is_some()
        || view.family != SourceCallableFamily::FunctionDeclaration
        || !view.parameters.nodes.is_empty()
        || view.type_parameters.is_some()
        || view.return_type.is_some()
        || body_mode != SourceCallableBodyMode::Present
        || export_local.is_none()
    {
        return array_targets;
    }
    let Some(parent) = owner.parent() else {
        return array_targets;
    };
    if !valid_namespace_export_parent(store, host, declaration, owner, parent) {
        return array_targets;
    }
    let Some(body) = view
        .body
        .map(|body| NodeRef::new(declaration.arena, declaration.file, body))
    else {
        return array_targets;
    };
    let Some(body_record) = host.node(body) else {
        return array_targets;
    };
    let NodeData::Block(block) = &body_record.data else {
        return array_targets;
    };
    if body_record.kind != SyntaxKind::Block
        || body_record.flags.0 != 0
        || body_record.parent != Some(declaration.node)
        || block.flow_node.is_some()
        || block.next_container.is_some()
        || !block.statements.nodes.is_empty()
        || block.statements.has_trailing_comma
        || block.facts != 0
    {
        return array_targets;
    }
    let Some(type_) = store.source_callable_type_for_owner(owner_symbol) else {
        return array_targets;
    };
    let Some(provenance) = store.source_callable_provenance(type_) else {
        return array_targets;
    };
    if provenance.family != SourceCallableFamily::FunctionDeclaration
        || provenance.declaration != declaration
        || provenance.owner_symbol != owner_symbol
        || provenance.owner_parent != Some(parent)
        || provenance.export_local != export_local
        || provenance.return_provenance != SourceCallableReturnProvenance::Inferred
        || provenance.contextual_target.is_some()
        || provenance.contextual_variable.is_some()
        || !matches!(
            validate_stored_source_callable(store, type_),
            StoredSourceCallableValidation::Valid(_)
        )
    {
        return array_targets;
    }
    provenance.array_targets
}

/// Returns the authenticated object-property symbol that directly owns an arrow.
pub(super) fn source_object_property_arrow_symbol(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    declaration: NodeRef,
) -> Result<Option<SemanticSymbolId>, SourceCallableError> {
    if store.source_node_kind(declaration) != Some(SyntaxKind::ArrowFunction) {
        return Ok(None);
    }
    let Some(SourceNodeParent::Parent(property)) = store.source_node_parent(declaration) else {
        return Ok(None);
    };
    let record = preflight_node(store, host, property)?;
    let NodeData::PropertyAssignment(assignment) = &record.data else {
        return Ok(None);
    };
    if record.kind != SyntaxKind::PropertyAssignment
        || record.flags.0 != 0
        || assignment.initializer != declaration.node
        || assignment.postfix_token.is_some()
        || assignment.modifiers.is_some()
        || assignment.type_.is_some()
        || assignment.symbol.is_some()
        || assignment.facts != 0
    {
        return Ok(None);
    }
    let Some(SourceNodeParent::Parent(object)) = store.source_node_parent(property) else {
        return Ok(None);
    };
    if store.source_node_kind(object) != Some(SyntaxKind::ObjectLiteralExpression) {
        return Ok(None);
    }
    let Ok(plan) = super::object_members::plan_object_literal(store, host, object) else {
        return Ok(None);
    };
    let Some(planned) = plan
        .properties
        .iter()
        .find(|planned| planned.declaration == property && planned.type_node == declaration)
    else {
        return Ok(None);
    };
    let Some(record) = store.symbol(planned.symbol) else {
        return Ok(None);
    };
    Ok((record.flags() == SymbolFlags::PROPERTY
        && record.check_flags() == CheckFlags::NONE
        && record.declarations() == Some(&[property])
        && record.value_declaration() == Some(property)
        && record.members().is_none()
        && record.exports().is_none()
        && record.export_symbol().is_none()
        && store.get_parent_of_symbol(planned.symbol) == Some(plan.symbol)
        && store.get_merged_symbol(planned.symbol) == Some(planned.symbol)
        && host.symbol_matches(store, property, planned.symbol))
    .then_some(planned.symbol))
}

/// Authenticates one unparenthesized callback in a direct, array, or global sort call.
#[allow(clippy::too_many_lines)] // Validate the callback, array owner, and top-level container.
pub(super) fn source_direct_call_argument_arrow_is_exact(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    declaration: NodeRef,
) -> Result<bool, SourceCallableError> {
    if store.source_node_kind(declaration) != Some(SyntaxKind::ArrowFunction) {
        return Ok(false);
    }
    if source_array_sort_argument_arrow_is_exact(store, host, declaration) {
        return Ok(true);
    }
    let Some(SourceNodeParent::Parent(call)) = store.source_node_parent(declaration) else {
        return Ok(false);
    };
    let call_record = preflight_node(store, host, call)?;
    let NodeData::CallExpression(call_data) = &call_record.data else {
        return Ok(false);
    };
    if call_record.kind != SyntaxKind::CallExpression
        || call_record.flags.0 != 0
        || call_data.question_dot_token.is_some()
        || call_data.type_arguments.is_some()
        || call_data.symbol.is_some()
        || call_data.facts != 0
        || call_data
            .arguments
            .nodes
            .iter()
            .filter(|argument| **argument == declaration.node)
            .count()
            != 1
    {
        return Ok(false);
    }
    let callee = NodeRef::new(call.arena, call.file, call_data.expression);
    let callee_record = preflight_node(store, host, callee)?;
    if callee_record.parent != Some(call.node) || callee_record.flags.0 != 0 {
        return Ok(false);
    }
    let Some(bound) = host.bound_file(declaration) else {
        return Ok(false);
    };
    let Some(owner) = bound.symbol(declaration) else {
        return Ok(false);
    };
    let callee_valid = match &callee_record.data {
        NodeData::Identifier(identifier) if callee_record.kind == SyntaxKind::Identifier => {
            identifier.flow_node.is_none()
                && !identifier.text.is_empty()
                && bound
                    .locals(bound.source_file())
                    .and_then(|locals| store.symbol_table(locals))
                    .and_then(|locals| locals.get_source(&identifier.text))
                    .and_then(|symbol| store.get_merged_symbol(symbol))
                    .and_then(|symbol| store.symbol(symbol))
                    .is_some_and(|symbol| symbol.flags().contains(SymbolFlags::FUNCTION))
        }
        NodeData::PropertyAccessExpression(property)
            if callee_record.kind == SyntaxKind::PropertyAccessExpression =>
        {
            let Some(name) =
                super::source_calls::source_global_array_callback_method_name(host, callee)
            else {
                return Ok(false);
            };
            let receiver = NodeRef::new(callee.arena, callee.file, property.expression);
            if preflight_node(store, host, receiver)?.parent != Some(callee.node)
                || property.question_dot_token.is_some()
                || property.flow_node.is_some()
                || property.facts != 0
            {
                return Ok(false);
            }
            let Some(globals) = store
                .intrinsic_bootstrap()
                .and_then(|bootstrap| store.symbol_table(bootstrap.globals))
            else {
                return Ok(false);
            };
            ["Array", "ReadonlyArray"].iter().any(|owner| {
                globals
                    .get_source(owner)
                    .and_then(|owner| store.get_merged_symbol(owner))
                    .and_then(|owner| store.symbol(owner))
                    .and_then(ts_binder::semantic::Symbol::members)
                    .and_then(|members| store.symbol_table(members))
                    .and_then(|members| members.get_source(&name))
                    .and_then(|method| store.symbol(method))
                    .is_some_and(|method| method.flags() == SymbolFlags::METHOD)
            })
        }
        _ => false,
    };
    let Some(SourceNodeParent::Parent(container)) = store.source_node_parent(call) else {
        return Ok(false);
    };
    let container_record = preflight_node(store, host, container)?;
    let container_valid = match &container_record.data {
        NodeData::ExpressionStatement(statement) => {
            container_record.kind == SyntaxKind::ExpressionStatement
                && container_record.flags.0 == 0
                && statement.expression == call.node
                && statement.flow_node.is_none()
                && store.source_node_parent(container)
                    == Some(SourceNodeParent::Parent(bound.source_file()))
        }
        NodeData::VariableDeclaration(variable)
            if matches!(&callee_record.data, NodeData::PropertyAccessExpression(_)) =>
        {
            let Some(SourceNodeParent::Parent(list)) = store.source_node_parent(container) else {
                return Ok(false);
            };
            let list_record = preflight_node(store, host, list)?;
            let NodeData::VariableDeclarationList(declarations) = &list_record.data else {
                return Ok(false);
            };
            let Some(SourceNodeParent::Parent(statement)) = store.source_node_parent(list) else {
                return Ok(false);
            };
            let statement_record = preflight_node(store, host, statement)?;
            let NodeData::VariableStatement(statement_data) = &statement_record.data else {
                return Ok(false);
            };
            container_record.kind == SyntaxKind::VariableDeclaration
                && variable.initializer == Some(call.node)
                && list_record.kind == SyntaxKind::VariableDeclarationList
                && declarations
                    .declarations
                    .nodes
                    .iter()
                    .filter(|declaration| **declaration == container.node)
                    .count()
                    == 1
                && statement_record.kind == SyntaxKind::VariableStatement
                && statement_data.declaration_list == list.node
                && store.source_node_parent(statement)
                    == Some(SourceNodeParent::Parent(bound.source_file()))
        }
        _ => false,
    };
    Ok(container_valid
        && bound
            .source_facts()
            .is_some_and(|facts| !facts.is_javascript_file() && !facts.is_declaration_file())
        && host.symbol_matches(store, declaration, owner)
        && store.symbol(owner).is_some_and(|symbol| {
            symbol.flags() == SymbolFlags::FUNCTION
                && symbol.check_flags() == CheckFlags::NONE
                && symbol.declarations() == Some(&[declaration])
                && symbol.value_declaration() == Some(declaration)
                && symbol.members().is_none()
                && symbol.exports().is_none()
                && symbol.parent().is_none()
                && symbol.export_symbol().is_none()
        })
        && callee_valid)
}

/// Authenticates the one-parameter executor of a top-level global Promise construction.
pub(super) fn source_promise_constructor_argument_arrow_is_exact(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    declaration: NodeRef,
) -> Result<bool, SourceCallableError> {
    if store.source_node_kind(declaration) != Some(SyntaxKind::ArrowFunction) {
        return Ok(false);
    }
    let Some(SourceNodeParent::Parent(construction)) = store.source_node_parent(declaration) else {
        return Ok(false);
    };
    let record = preflight_node(store, host, construction)?;
    let NodeData::NewExpression(expression) = &record.data else {
        return Ok(false);
    };
    let Some(arguments) = expression.arguments.as_ref() else {
        return Ok(false);
    };
    if record.kind != SyntaxKind::NewExpression
        || record.flags.0 != 0
        || expression.facts != 0
        || expression.type_arguments.is_some()
        || arguments.has_trailing_comma
        || arguments.nodes.as_slice() != [declaration.node]
    {
        return Ok(false);
    }
    let constructor = NodeRef::new(construction.arena, construction.file, expression.expression);
    let constructor_record = preflight_node(store, host, constructor)?;
    let NodeData::Identifier(identifier) = &constructor_record.data else {
        return Ok(false);
    };
    let Some(SourceNodeParent::Parent(statement)) = store.source_node_parent(construction) else {
        return Ok(false);
    };
    let statement_record = preflight_node(store, host, statement)?;
    let NodeData::ExpressionStatement(statement_data) = &statement_record.data else {
        return Ok(false);
    };
    let Some(bound) = host.bound_file(declaration) else {
        return Ok(false);
    };
    let Some(owner) = bound.symbol(declaration) else {
        return Ok(false);
    };
    let Some(promise) = store
        .intrinsic_bootstrap()
        .and_then(|bootstrap| store.symbol_table(bootstrap.globals))
        .and_then(|globals| globals.get_source("Promise"))
        .and_then(|symbol| store.get_merged_symbol(symbol))
    else {
        return Ok(false);
    };
    Ok(constructor_record.kind == SyntaxKind::Identifier
        && constructor_record.parent == Some(construction.node)
        && constructor_record.flags.0 == 0
        && identifier.flow_node.is_none()
        && identifier.text == "Promise"
        && statement_record.kind == SyntaxKind::ExpressionStatement
        && statement_record.flags.0 == 0
        && statement_data.expression == construction.node
        && statement_data.flow_node.is_none()
        && store.source_node_parent(statement)
            == Some(SourceNodeParent::Parent(bound.source_file()))
        && bound
            .source_facts()
            .is_some_and(|facts| !facts.is_declaration_file())
        && store.symbol(promise).is_some_and(|symbol| {
            symbol.flags().contains(SymbolFlags::INTERFACE)
                && symbol
                    .flags()
                    .contains(SymbolFlags::FUNCTION_SCOPED_VARIABLE)
                && symbol.check_flags() == CheckFlags::NONE
                && symbol.name().as_utf8() == Some("Promise")
                && symbol.parent().is_none()
        })
        && host.symbol_matches(store, declaration, owner)
        && store.symbol(owner).is_some_and(|symbol| {
            symbol.flags() == SymbolFlags::FUNCTION
                && symbol.check_flags() == CheckFlags::NONE
                && symbol.declarations() == Some(&[declaration])
                && symbol.value_declaration() == Some(declaration)
                && symbol.members().is_none()
                && symbol.exports().is_none()
                && symbol.parent().is_none()
                && symbol.export_symbol().is_none()
        }))
}

fn source_array_sort_argument_arrow_is_exact(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    declaration: NodeRef,
) -> bool {
    let Some((arena, bound)) = host.source(declaration) else {
        return false;
    };
    if !super::source_calls::is_authenticated_sort_callback_syntax(arena, declaration)
        || bound
            .source_facts()
            .is_none_or(|facts| facts.is_javascript_file() || facts.is_declaration_file())
    {
        return false;
    }
    let Some(owner) = bound.symbol(declaration) else {
        return false;
    };
    let Some(arrow_owner) = store.symbol(owner) else {
        return false;
    };
    let Some(bootstrap) = store.intrinsic_bootstrap() else {
        return false;
    };
    let Some(array) = store
        .symbol_table(bootstrap.globals)
        .and_then(|globals| globals.get_source("Array"))
        .and_then(|symbol| store.get_merged_symbol(symbol))
    else {
        return false;
    };
    let Some(target) = store
        .declared_type_links(array)
        .and_then(|links| links.declared_type)
    else {
        return false;
    };
    let Some(method) = store
        .symbol(array)
        .and_then(ts_binder::semantic::Symbol::members)
        .and_then(|members| store.symbol_table(members))
        .and_then(|members| members.get_source("sort"))
        .and_then(|symbol| store.get_merged_symbol(symbol))
    else {
        return false;
    };

    arrow_owner.flags() == SymbolFlags::FUNCTION
        && arrow_owner.check_flags() == CheckFlags::NONE
        && arrow_owner.name() == InternalSymbolName::Function.as_ref()
        && arrow_owner.declarations() == Some(&[declaration])
        && arrow_owner.value_declaration() == Some(declaration)
        && arrow_owner.members().is_none()
        && arrow_owner.exports().is_none()
        && arrow_owner.parent().is_none()
        && arrow_owner.export_symbol().is_none()
        && host.symbol_matches(store, declaration, owner)
        && store.get_merged_symbol(owner) == Some(owner)
        && store.authenticated_interface_method_owner(method) == Some((array, target))
}

/// Authenticates ordinary extra callback parameters against a zero-arity target.
#[allow(clippy::too_many_lines)] // Keep the arrow, call, callee, and target proof together.
pub(super) fn source_direct_call_arrow_has_zero_parameter_target(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    declaration: NodeRef,
) -> Result<bool, SourceCallableError> {
    let record = preflight_node(store, host, declaration)?;
    let NodeData::ArrowFunction(arrow) = &record.data else {
        return Ok(false);
    };
    if record.kind != SyntaxKind::ArrowFunction
        || arrow.parameters.nodes.len() < 2
        || arrow.parameters.has_trailing_comma
        || arrow.type_parameters.is_some()
        || arrow.type_.is_some()
        || arrow.modifiers.is_some()
    {
        return Ok(false);
    }
    for parameter_id in &arrow.parameters.nodes {
        let parameter = NodeRef::new(declaration.arena, declaration.file, *parameter_id);
        let parameter_record = preflight_node(store, host, parameter)?;
        let NodeData::ParameterDeclaration(parameter_data) = &parameter_record.data else {
            return Ok(false);
        };
        if parameter_record.kind != SyntaxKind::Parameter
            || parameter_record.parent != Some(declaration.node)
            || parameter_data.type_.is_some()
            || parameter_data.dot_dot_dot_token.is_some()
            || parameter_data.question_token.is_some()
            || parameter_data.initializer.is_some()
            || parameter_data.modifiers.is_some()
        {
            return Ok(false);
        }
    }

    let Some(SourceNodeParent::Parent(call)) = store.source_node_parent(declaration) else {
        return Ok(false);
    };
    let call_record = preflight_node(store, host, call)?;
    let NodeData::CallExpression(call_data) = &call_record.data else {
        return Ok(false);
    };
    let Some(index) = call_data
        .arguments
        .nodes
        .iter()
        .position(|argument| *argument == declaration.node)
    else {
        return Ok(false);
    };
    let callee = NodeRef::new(call.arena, call.file, call_data.expression);
    let callee_record = preflight_node(store, host, callee)?;
    let NodeData::Identifier(callee_name) = &callee_record.data else {
        return Ok(false);
    };
    let Some(bound) = host.bound_file(declaration) else {
        return Ok(false);
    };
    let Some(symbol) = bound
        .locals(bound.source_file())
        .and_then(|locals| store.symbol_table(locals))
        .and_then(|locals| locals.get_source(&callee_name.text))
        .and_then(|symbol| store.get_merged_symbol(symbol))
    else {
        return Ok(false);
    };
    let Some(owner) = store.symbol(symbol) else {
        return Ok(false);
    };
    let Some([function]) = owner.declarations() else {
        return Ok(false);
    };
    if owner.value_declaration() != Some(*function)
        || bound.symbol(*function) != Some(symbol)
        || store.source_node_parent(*function)
            != Some(SourceNodeParent::Parent(bound.source_file()))
    {
        return Ok(false);
    }
    let function_record = preflight_node(store, host, *function)?;
    let NodeData::FunctionDeclaration(function_data) = &function_record.data else {
        return Ok(false);
    };
    if function_record.kind != SyntaxKind::FunctionDeclaration
        || function_data.type_parameters.is_some()
    {
        return Ok(false);
    }
    let Some(parameter_id) = function_data.parameters.nodes.get(index).copied() else {
        return Ok(false);
    };
    let parameter = NodeRef::new(function.arena, function.file, parameter_id);
    let parameter_record = preflight_node(store, host, parameter)?;
    let NodeData::ParameterDeclaration(parameter_data) = &parameter_record.data else {
        return Ok(false);
    };
    let Some(annotation_id) = parameter_data.type_ else {
        return Ok(false);
    };
    if parameter_record.kind != SyntaxKind::Parameter
        || parameter_record.parent != Some(function.node)
        || parameter_data.dot_dot_dot_token.is_some()
    {
        return Ok(false);
    }
    let annotation = NodeRef::new(parameter.arena, parameter.file, annotation_id);
    let annotation_record = preflight_node(store, host, annotation)?;
    let NodeData::FunctionTypeNode(target) = &annotation_record.data else {
        return Ok(false);
    };
    Ok(annotation_record.kind == SyntaxKind::FunctionType
        && annotation_record.parent == Some(parameter.node)
        && annotation_record.flags.0 == 0
        && target.full_signature.is_none()
        && target.next_container.is_none()
        && target.symbol.is_none()
        && target.parameters.nodes.is_empty()
        && !target.parameters.has_trailing_comma
        && target.type_parameters.is_none()
        && target.type_.is_some()
        && target.modifiers.is_none())
}

fn stored_direct_call_argument_arrow_is_exact(
    store: &CanonicalTypeMapperStore,
    declaration: NodeRef,
    owner_symbol: SemanticSymbolId,
) -> bool {
    let Some(owner) = store.symbol(owner_symbol) else {
        return false;
    };
    let Some(SourceNodeParent::Parent(call)) = store.source_node_parent(declaration) else {
        return false;
    };
    if stored_array_sort_argument_arrow_is_exact(store, declaration, owner_symbol, call) {
        return true;
    }
    let Some(SourceNodeParent::Parent(container)) = store.source_node_parent(call) else {
        return false;
    };
    let source = match store.source_node_kind(container) {
        Some(SyntaxKind::ExpressionStatement) => {
            let Some(SourceNodeParent::Parent(source)) = store.source_node_parent(container) else {
                return false;
            };
            source
        }
        Some(SyntaxKind::VariableDeclaration) => {
            let Some(SourceNodeParent::Parent(list)) = store.source_node_parent(container) else {
                return false;
            };
            let Some(SourceNodeParent::Parent(statement)) = store.source_node_parent(list) else {
                return false;
            };
            let Some(SourceNodeParent::Parent(source)) = store.source_node_parent(statement) else {
                return false;
            };
            if store.source_node_kind(list) != Some(SyntaxKind::VariableDeclarationList)
                || store.source_node_kind(statement) != Some(SyntaxKind::VariableStatement)
            {
                return false;
            }
            source
        }
        _ => return false,
    };
    store.source_node_kind(declaration) == Some(SyntaxKind::ArrowFunction)
        && (store.source_node_kind(call) == Some(SyntaxKind::CallExpression)
            || store.source_node_kind(call) == Some(SyntaxKind::NewExpression)
                && store.source_node_kind(container) == Some(SyntaxKind::ExpressionStatement))
        && store.source_node_kind(source) == Some(SyntaxKind::SourceFile)
        && owner.flags() == SymbolFlags::FUNCTION
        && owner.check_flags() == CheckFlags::NONE
        && owner.name() == InternalSymbolName::Function.as_ref()
        && owner.declarations() == Some(&[declaration])
        && owner.value_declaration() == Some(declaration)
        && owner.members().is_none()
        && owner.exports().is_none()
        && owner.parent().is_none()
        && owner.export_symbol().is_none()
        && store.get_merged_symbol(owner_symbol) == Some(owner_symbol)
}

fn stored_array_sort_argument_arrow_is_exact(
    store: &CanonicalTypeMapperStore,
    declaration: NodeRef,
    owner_symbol: SemanticSymbolId,
    call: NodeRef,
) -> bool {
    let Some(owner) = store.symbol(owner_symbol) else {
        return false;
    };
    if store.source_node_kind(declaration) != Some(SyntaxKind::ArrowFunction)
        || store.source_node_kind(call) != Some(SyntaxKind::CallExpression)
        || owner.flags() != SymbolFlags::FUNCTION
        || owner.check_flags() != CheckFlags::NONE
        || owner.name() != InternalSymbolName::Function.as_ref()
        || owner.declarations() != Some(&[declaration])
        || owner.value_declaration() != Some(declaration)
        || owner.members().is_some()
        || owner.exports().is_some()
        || owner.parent().is_some()
        || owner.export_symbol().is_some()
        || store.get_merged_symbol(owner_symbol) != Some(owner_symbol)
    {
        return false;
    }

    let mut property = None;
    for index in 0..declaration.node.index() {
        let Ok(index) = u32::try_from(index) else {
            return false;
        };
        let candidate = NodeRef::new(
            declaration.arena,
            declaration.file,
            ts_ast::NodeId::new(index),
        );
        if store.source_node_kind(candidate) == Some(SyntaxKind::PropertyAccessExpression)
            && store.source_node_parent(candidate) == Some(SourceNodeParent::Parent(call))
            && property.replace(candidate).is_some()
        {
            return false;
        }
    }
    let Some(property) = property else {
        return false;
    };
    let Some(method) = store
        .symbol_node_links(property)
        .and_then(|links| links.resolved_symbol)
    else {
        return false;
    };
    let Some(array) = store
        .intrinsic_bootstrap()
        .and_then(|bootstrap| store.symbol_table(bootstrap.globals))
        .and_then(|globals| globals.get_source("Array"))
        .and_then(|symbol| store.get_merged_symbol(symbol))
    else {
        return false;
    };
    let Some(target) = store
        .declared_type_links(array)
        .and_then(|links| links.declared_type)
    else {
        return false;
    };
    store
        .symbol(method)
        .is_some_and(|symbol| symbol.name().as_utf8() == Some("sort"))
        && store.authenticated_interface_method_owner(method) == Some((array, target))
        && store
            .type_node_links(property)
            .and_then(|links| links.resolved_type)
            .is_some()
}

fn is_direct_noncontextual_source_arrow(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    declaration: NodeRef,
) -> Result<bool, SourceCallableError> {
    let Some(SourceNodeParent::Parent(variable)) = store.source_node_parent(declaration) else {
        return Ok(false);
    };
    let variable_record = preflight_node(store, host, variable)?;
    let NodeData::VariableDeclaration(variable_data) = &variable_record.data else {
        return Ok(false);
    };
    if variable_record.kind != SyntaxKind::VariableDeclaration
        || variable_data.initializer != Some(declaration.node)
        || variable_data.type_.is_some()
    {
        return Ok(false);
    }

    let Some(SourceNodeParent::Parent(list)) = store.source_node_parent(variable) else {
        return Ok(false);
    };
    let list_record = preflight_node(store, host, list)?;
    let NodeData::VariableDeclarationList(list_data) = &list_record.data else {
        return Ok(false);
    };
    if list_record.kind != SyntaxKind::VariableDeclarationList
        || list_data.declarations.nodes.as_slice() != [variable.node]
    {
        return Ok(false);
    }

    let Some(SourceNodeParent::Parent(statement)) = store.source_node_parent(list) else {
        return Ok(false);
    };
    let statement_record = preflight_node(store, host, statement)?;
    let NodeData::VariableStatement(statement_data) = &statement_record.data else {
        return Ok(false);
    };
    if statement_record.kind != SyntaxKind::VariableStatement
        || statement_data.declaration_list != list.node
    {
        return Ok(false);
    }

    let Some(bound) = host.bound_file(declaration) else {
        return Ok(false);
    };
    Ok(store.source_node_parent(statement) == Some(SourceNodeParent::Parent(bound.source_file())))
}

#[allow(clippy::too_many_lines)] // Authenticate the complete ambiguous call and union target.
fn is_ambiguous_union_array_source_arrow(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    declaration: NodeRef,
) -> Result<bool, SourceCallableError> {
    let Some(SourceNodeParent::Parent(array)) = store.source_node_parent(declaration) else {
        return Ok(false);
    };
    let array_record = preflight_node(store, host, array)?;
    let NodeData::ArrayLiteralExpression(array_data) = &array_record.data else {
        return Ok(false);
    };
    if array_record.kind != SyntaxKind::ArrayLiteralExpression
        || array_record.flags.0 != 0
        || array_data.facts != 0
        || array_data.elements.nodes.as_slice() != [declaration.node]
    {
        return Ok(false);
    }

    let Some(SourceNodeParent::Parent(call)) = store.source_node_parent(array) else {
        return Ok(false);
    };
    let call_record = preflight_node(store, host, call)?;
    let NodeData::CallExpression(call_data) = &call_record.data else {
        return Ok(false);
    };
    if call_record.kind != SyntaxKind::CallExpression
        || call_record.flags.0 != 0
        || call_data.facts != 0
        || call_data.symbol.is_some()
        || call_data.question_dot_token.is_some()
        || call_data.type_arguments.is_some()
        || call_data.arguments.nodes.as_slice() != [array.node]
    {
        return Ok(false);
    }

    let Some(SourceNodeParent::Parent(statement)) = store.source_node_parent(call) else {
        return Ok(false);
    };
    let statement_record = preflight_node(store, host, statement)?;
    let NodeData::ExpressionStatement(statement_data) = &statement_record.data else {
        return Ok(false);
    };
    let Some(bound) = host.bound_file(declaration) else {
        return Ok(false);
    };
    if statement_record.kind != SyntaxKind::ExpressionStatement
        || statement_record.flags.0 != 0
        || statement_data.expression != call.node
        || statement_data.flow_node.is_some()
        || store.source_node_parent(statement)
            != Some(SourceNodeParent::Parent(bound.source_file()))
    {
        return Ok(false);
    }

    let callee = NodeRef::new(call.arena, call.file, call_data.expression);
    let callee_record = preflight_node(store, host, callee)?;
    let NodeData::Identifier(callee_name) = &callee_record.data else {
        return Ok(false);
    };
    if callee_record.kind != SyntaxKind::Identifier
        || callee_record.flags.0 != 0
        || callee_record.parent != Some(call.node)
        || callee_name.flow_node.is_some()
    {
        return Ok(false);
    }
    let Some(function_symbol) = bound
        .locals(bound.source_file())
        .and_then(|locals| store.symbol_table(locals))
        .and_then(|locals| locals.get_source(&callee_name.text))
        .and_then(|symbol| store.get_merged_symbol(symbol))
    else {
        return Ok(false);
    };
    let Some(function_owner) = store.symbol(function_symbol) else {
        return Ok(false);
    };
    let Some(function) = function_owner.value_declaration() else {
        return Ok(false);
    };
    if function_owner.flags() != SymbolFlags::FUNCTION
        || function_owner.check_flags() != CheckFlags::NONE
        || function_owner.declarations() != Some(&[function])
        || function_owner.parent().is_some()
        || bound.symbol(function) != Some(function_symbol)
        || store.source_node_parent(function) != Some(SourceNodeParent::Parent(bound.source_file()))
    {
        return Ok(false);
    }
    let function_record = preflight_node(store, host, function)?;
    let NodeData::FunctionDeclaration(function_data) = &function_record.data else {
        return Ok(false);
    };
    if function_record.kind != SyntaxKind::FunctionDeclaration
        || function_data.body.is_some()
        || function_data.type_parameters.is_some()
        || function_data.parameters.nodes.len() != 1
        || function_data.parameters.has_trailing_comma
    {
        return Ok(false);
    }
    let Some(modifiers) = function_data.modifiers.as_ref() else {
        return Ok(false);
    };
    let [modifier_id] = modifiers.list.nodes.as_slice() else {
        return Ok(false);
    };
    let modifier = NodeRef::new(function.arena, function.file, *modifier_id);
    let modifier_record = preflight_node(store, host, modifier)?;
    if modifiers.flags.0 != 0
        || modifiers.list.has_trailing_comma
        || modifier_record.kind != SyntaxKind::DeclareKeyword
        || !matches!(modifier_record.data, NodeData::Token(_))
        || modifier_record.flags.0 != 0
        || modifier_record.parent != Some(function.node)
    {
        return Ok(false);
    }

    let parameter = NodeRef::new(
        function.arena,
        function.file,
        function_data.parameters.nodes[0],
    );
    let parameter_record = preflight_node(store, host, parameter)?;
    let NodeData::ParameterDeclaration(parameter_data) = &parameter_record.data else {
        return Ok(false);
    };
    let Some(union_id) = parameter_data.type_ else {
        return Ok(false);
    };
    if parameter_record.kind != SyntaxKind::Parameter
        || parameter_record.parent != Some(function.node)
        || parameter_data.dot_dot_dot_token.is_some()
        || parameter_data.initializer.is_some()
        || parameter_data.question_token.is_some()
        || parameter_data.modifiers.is_some()
    {
        return Ok(false);
    }
    let union = NodeRef::new(parameter.arena, parameter.file, union_id);
    let union_record = preflight_node(store, host, union)?;
    let NodeData::UnionTypeNode(union_data) = &union_record.data else {
        return Ok(false);
    };
    let [record_id, array_id] = union_data.types.nodes.as_slice() else {
        return Ok(false);
    };
    if union_record.kind != SyntaxKind::UnionType
        || union_record.flags.0 != 0
        || union_record.parent != Some(parameter.node)
        || union_data.types.has_trailing_comma
    {
        return Ok(false);
    }

    let record_reference = NodeRef::new(union.arena, union.file, *record_id);
    let array_reference = NodeRef::new(union.arena, union.file, *array_id);
    Ok(exact_union_callable_reference(
        store,
        host,
        union,
        record_reference,
        "Record",
        SyntaxKind::StringKeyword,
        2,
    )? && exact_union_callable_reference(
        store,
        host,
        union,
        array_reference,
        "Array",
        SyntaxKind::NumberKeyword,
        1,
    )?)
}

fn exact_union_callable_reference(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    union: NodeRef,
    reference: NodeRef,
    expected_name: &str,
    expected_parameter_kind: SyntaxKind,
    expected_argument_count: usize,
) -> Result<bool, SourceCallableError> {
    let record = preflight_node(store, host, reference)?;
    let NodeData::TypeReferenceNode(reference_data) = &record.data else {
        return Ok(false);
    };
    let Some(arguments) = reference_data.type_arguments.as_ref() else {
        return Ok(false);
    };
    if record.kind != SyntaxKind::TypeReference
        || record.flags.0 != 0
        || record.parent != Some(union.node)
        || arguments.nodes.len() != expected_argument_count
        || arguments.has_trailing_comma
    {
        return Ok(false);
    }
    let name = NodeRef::new(reference.arena, reference.file, reference_data.type_name);
    let name_record = preflight_node(store, host, name)?;
    let NodeData::Identifier(identifier) = &name_record.data else {
        return Ok(false);
    };
    if name_record.kind != SyntaxKind::Identifier
        || name_record.parent != Some(reference.node)
        || identifier.text != expected_name
    {
        return Ok(false);
    }
    if expected_argument_count == 2 {
        let key = NodeRef::new(reference.arena, reference.file, arguments.nodes[0]);
        let key_record = preflight_node(store, host, key)?;
        if key_record.kind != SyntaxKind::StringKeyword || key_record.parent != Some(reference.node)
        {
            return Ok(false);
        }
    }
    let function = NodeRef::new(
        reference.arena,
        reference.file,
        arguments.nodes[expected_argument_count - 1],
    );
    exact_union_callable_argument(store, host, reference, function, expected_parameter_kind)
}

fn exact_union_callable_argument(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    reference: NodeRef,
    function: NodeRef,
    expected_parameter_kind: SyntaxKind,
) -> Result<bool, SourceCallableError> {
    let function_record = preflight_node(store, host, function)?;
    let NodeData::FunctionTypeNode(function_data) = &function_record.data else {
        return Ok(false);
    };
    let Some(return_id) = function_data.type_ else {
        return Ok(false);
    };
    if function_record.kind != SyntaxKind::FunctionType
        || function_record.flags.0 != 0
        || function_record.parent != Some(reference.node)
        || function_data.type_parameters.is_some()
        || function_data.modifiers.is_some()
        || function_data.parameters.nodes.len() != 1
        || function_data.parameters.has_trailing_comma
    {
        return Ok(false);
    }
    let return_type = NodeRef::new(function.arena, function.file, return_id);
    let return_record = preflight_node(store, host, return_type)?;
    if return_record.kind != SyntaxKind::VoidKeyword || return_record.parent != Some(function.node)
    {
        return Ok(false);
    }
    let parameter = NodeRef::new(
        function.arena,
        function.file,
        function_data.parameters.nodes[0],
    );
    let parameter_record = preflight_node(store, host, parameter)?;
    let NodeData::ParameterDeclaration(parameter_data) = &parameter_record.data else {
        return Ok(false);
    };
    let Some(annotation_id) = parameter_data.type_ else {
        return Ok(false);
    };
    if parameter_record.kind != SyntaxKind::Parameter
        || parameter_record.parent != Some(function.node)
        || parameter_data.dot_dot_dot_token.is_some()
        || parameter_data.question_token.is_some()
        || parameter_data.initializer.is_some()
        || parameter_data.modifiers.is_some()
    {
        return Ok(false);
    }
    let annotation = NodeRef::new(parameter.arena, parameter.file, annotation_id);
    let annotation_record = preflight_node(store, host, annotation)?;
    Ok(annotation_record.kind == expected_parameter_kind
        && annotation_record.parent == Some(parameter.node))
}

#[allow(clippy::too_many_arguments)] // Preserve exact owner, parameter, and modifier ranges.
fn valid_ordinary_function_public_parameter(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    declaration: NodeRef,
    view: &SourceSyntaxView<'_>,
    body_mode: SourceCallableBodyMode,
    parameter: NodeRef,
    parameter_range: ts_core::TextRange,
    name_start: ts_core::TextPos,
    modifiers: &ModifierList,
) -> Result<bool, SourceCallableError> {
    let Some(bound) = host.bound_file(declaration) else {
        return Ok(false);
    };
    if view.family != SourceCallableFamily::FunctionDeclaration
        || view.parameters.nodes.len() != 1
        || view.modifiers.is_some()
        || view.type_parameters.is_some()
        || view.return_type.is_some()
        || body_mode.is_ambient()
        || bound
            .source_facts()
            .is_none_or(CanonicalSourceFileFacts::is_javascript_file)
        || store.source_node_parent(declaration)
            != Some(SourceNodeParent::Parent(bound.source_file()))
        || modifiers.flags.0 != 0
        || modifiers.list.has_trailing_comma
        || modifiers.list.range.start != parameter_range.start
        || modifiers.list.range.end > name_start
    {
        return Ok(false);
    }
    let [modifier_id] = modifiers.list.nodes.as_slice() else {
        return Ok(false);
    };
    let modifier = NodeRef::new(parameter.arena, parameter.file, *modifier_id);
    let modifier_record = preflight_node(store, host, modifier)?;
    Ok(modifier_record.kind == SyntaxKind::PublicKeyword
        && matches!(modifier_record.data, NodeData::Token(_))
        && modifier_record.flags.0 == 0
        && modifier_record.parent == Some(parameter.node)
        && modifier_record.range.start == parameter_range.start
        && modifier_record.range.end <= modifiers.list.range.end)
}

fn prove_source_type_parameter_syntax(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    declaration: NodeRef,
    type_parameters: &[SourceCallableTypeParameterPlan],
) -> Result<SourceCallableTypeParameterSyntaxProof, SourceCallableError> {
    let declaration_record = preflight_node(store, host, declaration)?;
    let syntax_type_parameters = match &declaration_record.data {
        NodeData::FunctionDeclaration(function)
            if declaration_record.kind == SyntaxKind::FunctionDeclaration =>
        {
            function.type_parameters.as_ref()
        }
        NodeData::ArrowFunction(function)
            if declaration_record.kind == SyntaxKind::ArrowFunction =>
        {
            function.type_parameters.as_ref()
        }
        NodeData::FunctionExpression(function)
            if declaration_record.kind == SyntaxKind::FunctionExpression =>
        {
            function.type_parameters.as_ref()
        }
        _ => {
            return Err(invariant(SourceCallableInvariant::InvalidSyntax(
                declaration,
            )));
        }
    };
    let exact_declarations = syntax_type_parameters.map_or(type_parameters.is_empty(), |list| {
        list.nodes.len() == type_parameters.len()
            && list
                .nodes
                .iter()
                .zip(type_parameters)
                .all(|(node, planned)| {
                    planned.declaration == NodeRef::new(declaration.arena, declaration.file, *node)
                })
    });
    if !exact_declarations {
        return Err(invariant(SourceCallableInvariant::InvalidSyntax(
            declaration,
        )));
    }

    let mut rows = Vec::with_capacity(type_parameters.len());
    for type_parameter in type_parameters {
        let record = preflight_node(store, host, type_parameter.declaration)?;
        let NodeData::TypeParameterDeclaration(data) = &record.data else {
            return Err(invariant(SourceCallableInvariant::InvalidSyntax(
                type_parameter.declaration,
            )));
        };
        let constraint = data
            .constraint
            .map(|node| NodeRef::new(declaration.arena, declaration.file, node));
        let default_type = data
            .default_type
            .map(|node| NodeRef::new(declaration.arena, declaration.file, node));
        let exact_type_child = |node: NodeRef| {
            preflight_node(store, host, node).is_ok_and(|child| {
                child.parent == Some(type_parameter.declaration.node)
                    && child.range.start >= record.range.start
                    && child.range.end <= record.range.end
                    && is_source_type_syntax_kind(child.kind)
            })
        };
        if record.kind != SyntaxKind::TypeParameter
            || record.parent != Some(declaration.node)
            || constraint != type_parameter.constraint
            || default_type != type_parameter.default_type
            || constraint.is_some_and(|constraint| !exact_type_child(constraint))
            || default_type.is_some_and(|default_type| !exact_type_child(default_type))
        {
            return Err(invariant(SourceCallableInvariant::InvalidSyntax(
                type_parameter.declaration,
            )));
        }
        rows.push(SourceCallableTypeParameterSyntaxRow {
            declaration: type_parameter.declaration,
            constraint,
            default_type,
        });
    }
    Ok(SourceCallableTypeParameterSyntaxProof {
        declaration,
        rows: rows.into_boxed_slice(),
        generic_return_type_parameter_declaration: None,
        generic_fixed_return_is_exact: false,
        inferred_empty_body_is_exact: false,
    })
}

const fn is_source_type_syntax_kind(kind: SyntaxKind) -> bool {
    kind.is_keyword_type()
        || (kind as u16) >= (SyntaxKind::FIRST_TYPE_NODE as u16)
            && (kind as u16) <= (SyntaxKind::LAST_TYPE_NODE as u16)
}

fn plan_exact_source_type_parameters(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    declaration: NodeRef,
    family: SourceCallableFamily,
    type_parameters: Option<&NodeList>,
    parameters: &NodeList,
) -> Result<Vec<SourceCallableTypeParameterPlan>, SourceCallableError> {
    let Some(type_parameters) = type_parameters else {
        return Ok(Vec::new());
    };
    let declaration_record = preflight_node(store, host, declaration)?;
    let jsdoc_arrow = family == SourceCallableFamily::ArrowFunction
        && is_reparsed_jsdoc_generic_arrow(store, host, declaration, type_parameters)?;
    if family != SourceCallableFamily::FunctionDeclaration && !jsdoc_arrow
        || type_parameters.nodes.is_empty()
        || !jsdoc_arrow && type_parameters.range.start < declaration_record.range.start
        || jsdoc_arrow && type_parameters.range.end >= declaration_record.range.start
        || type_parameters.range.end > parameters.range.start
        || type_parameters.range.start >= type_parameters.range.end
    {
        return Err(SourceCallableError::Unsupported(
            SourceCallableUnsupported::GenericSignature(declaration),
        ));
    }

    let symbols = explicit_type_parameter_symbols(
        store,
        host,
        declaration,
        Some(type_parameters),
        &mut HashSet::new(),
    )?;
    if symbols.len() != type_parameters.nodes.len() {
        return Err(SourceCallableError::Unsupported(
            SourceCallableUnsupported::GenericSignature(declaration),
        ));
    }

    let mut result = Vec::with_capacity(type_parameters.nodes.len());
    let mut declarations = HashSet::with_capacity(type_parameters.nodes.len());
    let mut names = HashSet::with_capacity(type_parameters.nodes.len());
    let mut previous_end = type_parameters.range.start;
    let mut default_seen = false;
    for (node, symbol) in type_parameters.nodes.iter().zip(symbols) {
        let type_parameter = NodeRef::new(declaration.arena, declaration.file, *node);
        let record = preflight_node(store, host, type_parameter)?;
        let NodeData::TypeParameterDeclaration(data) = &record.data else {
            return Err(invariant(SourceCallableInvariant::InvalidSyntax(
                type_parameter,
            )));
        };
        if record.kind != SyntaxKind::TypeParameter
            || record.parent != Some(declaration.node)
            || record.flags.0 & NODE_FLAG_JSDOC != 0
            || record.range.start < previous_end
            || record.range.start < type_parameters.range.start
            || record.range.end > type_parameters.range.end
            || !declarations.insert(type_parameter)
            || data.expression.is_some()
            || data.modifiers.is_some()
        {
            return Err(SourceCallableError::Unsupported(
                SourceCallableUnsupported::GenericSignature(type_parameter),
            ));
        }
        if data.symbol.is_some() {
            return Err(invariant(SourceCallableInvariant::InvalidSyntax(
                type_parameter,
            )));
        }
        let name = NodeRef::new(type_parameter.arena, type_parameter.file, data.name);
        let name_record = preflight_node(store, host, name)?;
        let NodeData::Identifier(identifier) = &name_record.data else {
            return Err(invariant(SourceCallableInvariant::InvalidSyntax(name)));
        };
        if name_record.kind != SyntaxKind::Identifier
            || name_record.parent != Some(type_parameter.node)
            || name_record.flags.0 != 0
            || name_record.range.start < record.range.start
            || name_record.range.end > record.range.end
            || identifier.text.is_empty()
            || identifier.flow_node.is_some()
        {
            return Err(invariant(SourceCallableInvariant::InvalidSyntax(name)));
        }
        if !names.insert(identifier.text.clone()) {
            return Err(SourceCallableError::Unsupported(
                SourceCallableUnsupported::GenericSignature(name),
            ));
        }

        let constraint = data
            .constraint
            .map(|node| NodeRef::new(declaration.arena, declaration.file, node));
        let default_type = data
            .default_type
            .map(|node| NodeRef::new(declaration.arena, declaration.file, node));
        let mut previous_child_end = name_record.range.end;
        for bound in [constraint, default_type].into_iter().flatten() {
            let bound_record = preflight_node(store, host, bound)?;
            if bound_record.parent != Some(type_parameter.node)
                || bound_record.range.start < previous_child_end
                || bound_record.range.end > record.range.end
                || !is_source_type_syntax_kind(bound_record.kind)
                || !is_exact_source_type_parameter_bound(store, host, declaration, bound, &result)?
            {
                return Err(SourceCallableError::Unsupported(
                    SourceCallableUnsupported::GenericSignature(bound),
                ));
            }
            previous_child_end = bound_record.range.end;
        }
        if let (Some(constraint), Some(default_type)) = (constraint, default_type)
            && !source_type_parameter_bounds_are_compatible(store, host, constraint, default_type)?
        {
            return Err(SourceCallableError::Unsupported(
                SourceCallableUnsupported::GenericSignature(default_type),
            ));
        }
        if default_seen && default_type.is_none() {
            return Err(SourceCallableError::Unsupported(
                SourceCallableUnsupported::GenericSignature(type_parameter),
            ));
        }
        default_seen |= default_type.is_some();

        let symbol_record = store.symbol(symbol).ok_or_else(|| {
            invariant(SourceCallableInvariant::InvalidOwnerSymbol(type_parameter))
        })?;
        if symbol_record.flags() != SymbolFlags::TYPE_PARAMETER
            || symbol_record.check_flags() != CheckFlags::NONE
            || symbol_record.declarations() != Some(&[type_parameter])
            || symbol_record.value_declaration().is_some()
            || symbol_record.members().is_some()
            || symbol_record.exports().is_some()
            || symbol_record.parent().is_some()
            || symbol_record.export_symbol().is_some()
        {
            return Err(invariant(SourceCallableInvariant::InvalidOwnerSymbol(
                type_parameter,
            )));
        }
        result.push(SourceCallableTypeParameterPlan {
            declaration: type_parameter,
            symbol,
            constraint,
            default_type,
        });
        previous_end = record.range.end;
    }
    Ok(result)
}

pub(super) fn is_reparsed_jsdoc_generic_arrow(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    declaration: NodeRef,
    parameters: &NodeList,
) -> Result<bool, SourceCallableError> {
    let (arena, bound) = host
        .source(declaration)
        .ok_or_else(|| invariant(SourceCallableInvariant::InvalidOwnerSymbol(declaration)))?;
    if bound
        .source_facts()
        .is_none_or(|facts| !facts.is_javascript_file())
        || store.source_node_kind(declaration) != Some(SyntaxKind::ArrowFunction)
        || parameters.nodes.is_empty()
    {
        return Ok(false);
    }
    let comments = plan_javascript_source_jsdoc(arena, bound.source_file())
        .map_err(|_| invariant(SourceCallableInvariant::InvalidSyntax(declaration)))?;
    let Some(jsdoc) = comments.callable_declaration(arena, declaration) else {
        return Ok(false);
    };
    let declaration_record = preflight_node(store, host, declaration)?;
    let NodeData::ArrowFunction(function) = &declaration_record.data else {
        return Ok(false);
    };
    let Some(return_type) = jsdoc.return_type() else {
        return Ok(false);
    };
    let Some(return_node) = function
        .type_
        .map(|node| NodeRef::new(declaration.arena, declaration.file, node))
    else {
        return Ok(false);
    };
    let return_record = preflight_node(store, host, return_node)?;
    if jsdoc.template_parameters().len() != parameters.nodes.len()
        || jsdoc.parameters().len() != function.parameters.nodes.len()
        || jsdoc.parameters().is_empty()
        || return_record.flags != NodeFlags::REPARSED
        || return_record.parent != Some(declaration.node)
        || return_record.range != return_type.range()
    {
        return Ok(false);
    }
    for (node, template) in parameters.nodes.iter().zip(jsdoc.template_parameters()) {
        let parameter = NodeRef::new(declaration.arena, declaration.file, *node);
        let record = preflight_node(store, host, parameter)?;
        let NodeData::TypeParameterDeclaration(data) = &record.data else {
            return Ok(false);
        };
        let name = NodeRef::new(parameter.arena, parameter.file, data.name);
        let name_record = preflight_node(store, host, name)?;
        let NodeData::Identifier(identifier) = &name_record.data else {
            return Ok(false);
        };
        if record.kind != SyntaxKind::TypeParameter
            || record.flags != NodeFlags::REPARSED
            || record.parent != Some(declaration.node)
            || record.range != template.range()
            || name_record.range != template.range()
            || identifier.text != template.name()
        {
            return Ok(false);
        }
    }
    for (node, documented) in function.parameters.nodes.iter().zip(jsdoc.parameters()) {
        let parameter = NodeRef::new(declaration.arena, declaration.file, *node);
        let parameter_record = preflight_node(store, host, parameter)?;
        let NodeData::ParameterDeclaration(data) = &parameter_record.data else {
            return Ok(false);
        };
        let name = NodeRef::new(parameter.arena, parameter.file, data.name);
        let name_record = preflight_node(store, host, name)?;
        let NodeData::Identifier(identifier) = &name_record.data else {
            return Ok(false);
        };
        let Some(annotation) = data
            .type_
            .map(|node| NodeRef::new(parameter.arena, parameter.file, node))
        else {
            return Ok(false);
        };
        let annotation_record = preflight_node(store, host, annotation)?;
        if parameter_record.kind != SyntaxKind::Parameter
            || parameter_record.parent != Some(declaration.node)
            || identifier.text != documented.name()
            || annotation_record.flags != NodeFlags::REPARSED
            || annotation_record.parent != Some(parameter.node)
            || documented
                .type_()
                .is_none_or(|documented| annotation_record.range != documented.range())
        {
            return Ok(false);
        }
    }
    Ok(true)
}

fn is_exact_source_type_parameter_bound(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    declaration: NodeRef,
    bound: NodeRef,
    earlier: &[SourceCallableTypeParameterPlan],
) -> Result<bool, SourceCallableError> {
    let kind = preflight_node(store, host, bound)?.kind;
    if matches!(
        kind,
        SyntaxKind::AnyKeyword
            | SyntaxKind::UnknownKeyword
            | SyntaxKind::StringKeyword
            | SyntaxKind::NumberKeyword
            | SyntaxKind::BigIntKeyword
            | SyntaxKind::BooleanKeyword
            | SyntaxKind::SymbolKeyword
            | SyntaxKind::VoidKeyword
            | SyntaxKind::UndefinedKeyword
            | SyntaxKind::NullKeyword
            | SyntaxKind::NeverKeyword
            | SyntaxKind::ObjectKeyword
            | SyntaxKind::IntrinsicKeyword
    ) {
        return Ok(true);
    }
    if source_type_parameter_literal_kind(store, host, bound)?.is_some() {
        return Ok(true);
    }
    if exact_named_interface_keyof_bound(store, host, bound)? {
        return Ok(true);
    }
    if exact_unresolved_source_type_parameter_constraint(store, host, bound)? {
        return Ok(true);
    }
    if exact_ambient_namespace_generic_constraint(store, host, declaration, bound, earlier)? {
        return Ok(true);
    }
    for type_parameter in earlier {
        if is_naked_source_type_parameter_annotation(store, host, bound, type_parameter)? {
            return Ok(true);
        }
    }
    Ok(false)
}

fn exact_ambient_namespace_generic_constraint(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    declaration: NodeRef,
    constraint: NodeRef,
    earlier: &[SourceCallableTypeParameterPlan],
) -> Result<bool, SourceCallableError> {
    let Some(bound) = host.bound_file(declaration) else {
        return Ok(false);
    };
    if bound
        .source_facts()
        .is_none_or(|facts| !facts.is_declaration_file())
    {
        return Ok(false);
    }
    let declaration_record = preflight_node(store, host, declaration)?;
    let NodeData::FunctionDeclaration(function) = &declaration_record.data else {
        return Ok(false);
    };
    if function.body.is_some() {
        return Ok(false);
    }

    let record = preflight_node(store, host, constraint)?;
    let NodeData::TypeReferenceNode(reference) = &record.data else {
        return Ok(false);
    };
    let Some(arguments) = reference.type_arguments.as_ref() else {
        return Ok(false);
    };
    let name = NodeRef::new(constraint.arena, constraint.file, reference.type_name);
    let name_record = preflight_node(store, host, name)?;
    let NodeData::Identifier(identifier) = &name_record.data else {
        return Ok(false);
    };
    if record.kind != SyntaxKind::TypeReference
        || record.flags.0 != 0
        || arguments.nodes.is_empty()
        || arguments.has_trailing_comma
        || name_record.kind != SyntaxKind::Identifier
        || name_record.flags.0 != 0
        || name_record.parent != Some(constraint.node)
        || identifier.flow_node.is_some()
        || identifier.text.is_empty()
    {
        return Ok(false);
    }

    let Some(symbol) = enclosing_namespace_type_symbol(store, host, constraint, &identifier.text)
    else {
        return Ok(false);
    };
    if !namespace_generic_target_arity(store, host, symbol, arguments.nodes.len()) {
        return Ok(false);
    }

    let mut argument_nodes = Vec::with_capacity(arguments.nodes.len());
    for argument in &arguments.nodes {
        let argument = NodeRef::new(constraint.arena, constraint.file, *argument);
        let argument_record = preflight_node(store, host, argument)?;
        if argument_record.parent != Some(constraint.node) {
            return Err(invariant(SourceCallableInvariant::InvalidTypeCache(
                argument,
            )));
        }
        let exact = matches!(
            argument_record.kind,
            SyntaxKind::AnyKeyword
                | SyntaxKind::UnknownKeyword
                | SyntaxKind::StringKeyword
                | SyntaxKind::NumberKeyword
                | SyntaxKind::BooleanKeyword
                | SyntaxKind::NeverKeyword
                | SyntaxKind::ObjectKeyword
        ) || earlier.iter().try_fold(false, |exact, parameter| {
            is_naked_source_type_parameter_annotation(store, host, argument, parameter)
                .map(|matches| exact || matches)
        })?;
        if !exact {
            return Ok(false);
        }
        argument_nodes.push(argument);
    }

    let symbol_links = store.symbol_node_links(constraint);
    let type_links = store.type_node_links(constraint);
    if symbol_links.is_none_or(|links| links == &SymbolNodeLinks::default())
        && type_links.is_none_or(|links| links == &TypeNodeLinks::default())
    {
        return Ok(true);
    }
    let Some(resolved) = type_links.and_then(|links| {
        links.resolved_type.filter(|resolved| {
            links
                == &TypeNodeLinks {
                    resolved_type: Some(*resolved),
                    outer_type_parameters: None,
                }
        })
    }) else {
        return Err(invariant(SourceCallableInvariant::InvalidTypeCache(
            constraint,
        )));
    };
    let expected_arguments = argument_nodes
        .iter()
        .map(|argument| cached_annotation_identity(store, *argument, false))
        .collect::<Option<Vec<_>>>();
    let target = store
        .symbol(symbol)
        .ok_or_else(|| invariant(SourceCallableInvariant::InvalidTypeCache(constraint)))?;
    let valid_target = if target
        .flags()
        .intersects(SymbolFlags::INTERFACE | SymbolFlags::CLASS)
    {
        validate_direct_generic_reference(store, resolved).is_ok_and(|reference| {
            store
                .declared_type_links(symbol)
                .and_then(|links| links.declared_type)
                == Some(reference.target)
                && expected_arguments.as_deref() == Some(reference.type_arguments.as_slice())
        })
    } else {
        store
            .type_payload(resolved)
            .and_then(TypeRecord::alias)
            .and_then(|alias| store.type_alias(alias))
            .is_some_and(|alias| {
                alias.symbol() == Some(symbol)
                    && alias.type_arguments() == expected_arguments.as_deref()
            })
    };
    if symbol_links
        != Some(&SymbolNodeLinks {
            resolved_symbol: Some(symbol),
        })
        || !valid_target
    {
        return Err(invariant(SourceCallableInvariant::InvalidTypeCache(
            constraint,
        )));
    }
    Ok(true)
}

fn enclosing_namespace_type_symbol(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    reference: NodeRef,
    name: &str,
) -> Option<SemanticSymbolId> {
    let bound = host.bound_file(reference)?;
    let mut current = reference;
    while let Some(SourceNodeParent::Parent(parent)) = store.source_node_parent(current) {
        current = parent;
        if store.source_node_kind(current) != Some(SyntaxKind::ModuleDeclaration) {
            continue;
        }
        let namespace = bound
            .symbol(current)
            .and_then(|symbol| store.get_merged_symbol(symbol))?;
        let namespace_record = store.symbol(namespace)?;
        if !namespace_record.flags().intersects(SymbolFlags::MODULE) {
            return None;
        }
        let target = namespace_record
            .exports()
            .and_then(|exports| store.symbol_table(exports))
            .and_then(|exports| exports.get_source(name))
            .and_then(|symbol| store.get_merged_symbol(symbol))?;
        let record = store.symbol(target)?;
        if !record
            .flags()
            .intersects(SymbolFlags::INTERFACE | SymbolFlags::TYPE_ALIAS | SymbolFlags::CLASS)
            || record.check_flags() != CheckFlags::NONE
            || store.get_parent_of_symbol(target) != Some(namespace)
        {
            return None;
        }
        return Some(target);
    }
    None
}

fn namespace_generic_target_arity(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    symbol: SemanticSymbolId,
    expected: usize,
) -> bool {
    let Some(declarations) = store.symbol(symbol).and_then(|owner| owner.declarations()) else {
        return false;
    };
    !declarations.is_empty()
        && declarations.iter().all(|declaration| {
            host.node(*declaration).is_some_and(|record| {
                let parameters = match &record.data {
                    NodeData::InterfaceDeclaration(interface)
                        if record.kind == SyntaxKind::InterfaceDeclaration =>
                    {
                        interface.type_parameters.as_ref()
                    }
                    NodeData::TypeAliasDeclaration(alias)
                        if record.kind == SyntaxKind::TypeAliasDeclaration =>
                    {
                        alias.type_parameters.as_ref()
                    }
                    NodeData::ClassDeclaration(class)
                        if record.kind == SyntaxKind::ClassDeclaration =>
                    {
                        class.type_parameters.as_ref()
                    }
                    _ => None,
                };
                parameters.is_some_and(|parameters| parameters.nodes.len() == expected)
            })
        })
}

/// Proves one missing, unqualified generic constraint without caching a name.
pub(super) fn exact_unresolved_source_type_parameter_constraint(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    constraint: NodeRef,
) -> Result<bool, SourceCallableError> {
    let record = preflight_node(store, host, constraint)?;
    let NodeData::TypeReferenceNode(reference) = &record.data else {
        return Ok(false);
    };
    if record.kind != SyntaxKind::TypeReference || reference.type_arguments.is_some() {
        return Ok(false);
    }
    let Some(SourceNodeParent::Parent(parameter)) = store.source_node_parent(constraint) else {
        return Ok(false);
    };
    let parameter_record = preflight_node(store, host, parameter)?;
    let NodeData::TypeParameterDeclaration(parameter_data) = &parameter_record.data else {
        return Ok(false);
    };
    if parameter_record.kind != SyntaxKind::TypeParameter
        || parameter_data.constraint != Some(constraint.node)
        || parameter_data.default_type.is_some()
    {
        return Ok(false);
    }
    let Some(SourceNodeParent::Parent(function)) = store.source_node_parent(parameter) else {
        return Ok(false);
    };
    let function_record = preflight_node(store, host, function)?;
    let NodeData::FunctionDeclaration(function_data) = &function_record.data else {
        return Ok(false);
    };
    let Some(type_parameters) = function_data.type_parameters.as_ref() else {
        return Ok(false);
    };
    let ([declared_type_parameter], [value_parameter]) = (
        type_parameters.nodes.as_slice(),
        function_data.parameters.nodes.as_slice(),
    ) else {
        return Ok(false);
    };
    let Some(body) = function_data
        .body
        .map(|body| NodeRef::new(function.arena, function.file, body))
    else {
        return Ok(false);
    };
    let body_record = preflight_node(store, host, body)?;
    let NodeData::Block(block) = &body_record.data else {
        return Ok(false);
    };
    if function_record.kind != SyntaxKind::FunctionDeclaration
        || function_record.flags.0 != 0
        || function_data.modifiers.is_some()
        || function_data.asterisk_token.is_some()
        || function_data.type_.is_some()
        || *declared_type_parameter != parameter.node
        || type_parameters.has_trailing_comma
        || function_data.parameters.has_trailing_comma
        || body_record.kind != SyntaxKind::Block
        || body_record.flags.0 != 0
        || body_record.parent != Some(function.node)
        || block.flow_node.is_some()
        || block.next_container.is_some()
        || !block.statements.nodes.is_empty()
        || block.statements.has_trailing_comma
        || block.facts != 0
    {
        return Ok(false);
    }
    let Some(bound) = host.bound_file(function) else {
        return Ok(false);
    };
    let Some(owner) = bound.symbol(function) else {
        return Ok(false);
    };
    let Some(type_parameter_symbol) = bound.symbol(parameter) else {
        return Ok(false);
    };
    if bound
        .source_facts()
        .is_none_or(|facts| facts.is_declaration_file() || facts.is_javascript_file())
        || !host.symbol_matches(store, function, owner)
        || !host.symbol_matches(store, parameter, type_parameter_symbol)
        || store.symbol(owner).is_none_or(|symbol| {
            symbol.flags() != SymbolFlags::FUNCTION
                || symbol.declarations() != Some(&[function])
                || symbol.value_declaration() != Some(function)
        })
        || store.symbol(type_parameter_symbol).is_none_or(|symbol| {
            symbol.flags() != SymbolFlags::TYPE_PARAMETER
                || symbol.declarations() != Some(&[parameter])
        })
    {
        return Ok(false);
    }
    let value_parameter = NodeRef::new(function.arena, function.file, *value_parameter);
    let value_parameter_record = preflight_node(store, host, value_parameter)?;
    let NodeData::ParameterDeclaration(value_parameter_data) = &value_parameter_record.data else {
        return Ok(false);
    };
    let Some(annotation) = value_parameter_data
        .type_
        .map(|annotation| NodeRef::new(value_parameter.arena, value_parameter.file, annotation))
    else {
        return Ok(false);
    };
    if value_parameter_record.kind != SyntaxKind::Parameter
        || value_parameter_record.parent != Some(function.node)
        || value_parameter_data.modifiers.is_some()
        || value_parameter_data.dot_dot_dot_token.is_some()
        || value_parameter_data.question_token.is_some()
        || value_parameter_data.initializer.is_some()
        || !is_naked_source_type_parameter_annotation(
            store,
            host,
            annotation,
            &SourceCallableTypeParameterPlan {
                declaration: parameter,
                symbol: type_parameter_symbol,
                constraint: Some(constraint),
                default_type: None,
            },
        )?
    {
        return Ok(false);
    }
    let name = NodeRef::new(constraint.arena, constraint.file, reference.type_name);
    let name_record = preflight_node(store, host, name)?;
    let NodeData::Identifier(identifier) = &name_record.data else {
        return Ok(false);
    };
    if name_record.kind != SyntaxKind::Identifier
        || name_record.flags.0 != 0
        || name_record.parent != Some(constraint.node)
        || identifier.flow_node.is_some()
        || identifier.text.is_empty()
        || store
            .symbol_node_links(constraint)
            .is_some_and(|links| links != &SymbolNodeLinks::default())
        || store
            .symbol_node_links(name)
            .is_some_and(|links| links != &SymbolNodeLinks::default())
        || bound
            .locals(bound.source_file())
            .and_then(|locals| store.symbol_table(locals))
            .and_then(|locals| locals.get_source(&identifier.text))
            .and_then(|symbol| store.symbol(symbol))
            .is_some_and(|symbol| symbol.flags().intersects(SymbolFlags::TYPE))
    {
        return Ok(false);
    }
    let error_type = store
        .intrinsic_bootstrap()
        .map(|bootstrap| bootstrap.error_type)
        .ok_or_else(|| invariant(SourceCallableInvariant::InvalidTypeCache(constraint)))?;
    if store.type_node_links(constraint).is_some_and(|links| {
        links != &TypeNodeLinks::default()
            && links
                != &TypeNodeLinks {
                    resolved_type: Some(error_type),
                    ..TypeNodeLinks::default()
                }
    }) {
        return Ok(false);
    }
    let Some((arena, bound)) = host.source(constraint) else {
        return Ok(false);
    };
    let mut callback_host = host.name_resolver_host(store)?;
    let resolved =
        CanonicalNameResolver::new(arena, bound, store.symbol_store(), &mut callback_host)
            .map_err(DeclaredTypeError::from)?
            .resolve(
                Some(CanonicalResolutionLocation::Bound(name)),
                &identifier.text,
                SymbolFlags::TYPE,
                None,
                true,
                false,
            )
            .map_err(DeclaredTypeError::from)?;
    Ok(resolved.is_none())
}

fn exact_named_interface_keyof_bound(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    bound: NodeRef,
) -> Result<bool, SourceCallableError> {
    let record = preflight_node(store, host, bound)?;
    let NodeData::TypeOperatorNode(operator) = &record.data else {
        return Ok(false);
    };
    if record.kind != SyntaxKind::TypeOperator || operator.operator != SyntaxKind::KeyOfKeyword {
        return Ok(false);
    }
    let target = NodeRef::new(bound.arena, bound.file, operator.type_);
    let target_record = preflight_node(store, host, target)?;
    let NodeData::TypeReferenceNode(reference) = &target_record.data else {
        return Ok(false);
    };
    if target_record.kind != SyntaxKind::TypeReference
        || target_record.parent != Some(bound.node)
        || reference.type_arguments.is_some()
    {
        return Ok(false);
    }
    let name = NodeRef::new(target.arena, target.file, reference.type_name);
    let name_record = preflight_node(store, host, name)?;
    let NodeData::Identifier(identifier) = &name_record.data else {
        return Ok(false);
    };
    if name_record.kind != SyntaxKind::Identifier
        || name_record.parent != Some(target.node)
        || identifier.text.is_empty()
    {
        return Ok(false);
    }

    let Some(file) = host.bound_file(bound) else {
        return Ok(false);
    };
    let Some(owner) = file
        .locals(file.source_file())
        .and_then(|locals| store.symbol_table(locals))
        .and_then(|locals| locals.get_source(&identifier.text))
        .and_then(|symbol| store.get_merged_symbol(symbol))
    else {
        return Ok(false);
    };
    let Some(interface) = store.symbol(owner) else {
        return Ok(false);
    };
    let Some([declaration]) = interface.declarations() else {
        return Ok(false);
    };
    let declaration = *declaration;
    if interface.flags() != SymbolFlags::INTERFACE
        || store.source_node_parent(declaration)
            != Some(SourceNodeParent::Parent(file.source_file()))
    {
        return Ok(false);
    }
    let Ok(plan) = super::object_members::plan_interface(store, host, owner) else {
        return Ok(false);
    };
    Ok(plan.node == declaration
        && plan.declarations.as_slice() == [declaration]
        && plan.heritage.is_none()
        && plan.indexes.is_empty()
        && plan.call_signatures.is_empty()
        && !plan.properties.is_empty()
        && plan.properties.iter().all(|property| {
            matches!(
                store.source_node_kind(property.declaration),
                Some(SyntaxKind::PropertyDeclaration | SyntaxKind::PropertySignature)
            )
        }))
}

fn source_type_parameter_bounds_are_compatible(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    constraint: NodeRef,
    default_type: NodeRef,
) -> Result<bool, SourceCallableError> {
    let constraint_record = preflight_node(store, host, constraint)?;
    let default_record = preflight_node(store, host, default_type)?;
    if constraint_record.kind.is_keyword_type() || default_record.kind.is_keyword_type() {
        if constraint_record.kind == default_record.kind {
            return Ok(true);
        }
        let literal_kind = source_type_parameter_literal_kind(store, host, default_type)?;
        return Ok(matches!(
            (constraint_record.kind, literal_kind),
            (SyntaxKind::AnyKeyword | SyntaxKind::UnknownKeyword, Some(_))
                | (SyntaxKind::StringKeyword, Some(SyntaxKind::StringLiteral))
                | (SyntaxKind::NumberKeyword, Some(SyntaxKind::NumericLiteral))
                | (SyntaxKind::BigIntKeyword, Some(SyntaxKind::BigIntLiteral))
                | (
                    SyntaxKind::BooleanKeyword,
                    Some(SyntaxKind::TrueKeyword | SyntaxKind::FalseKeyword)
                )
                | (SyntaxKind::NullKeyword, Some(SyntaxKind::NullKeyword))
        ));
    }
    let (
        NodeData::TypeReferenceNode(constraint_reference),
        NodeData::TypeReferenceNode(default_reference),
    ) = (&constraint_record.data, &default_record.data)
    else {
        return Ok(false);
    };
    if constraint_record.kind != SyntaxKind::TypeReference
        || default_record.kind != SyntaxKind::TypeReference
        || constraint_reference.type_arguments.is_some()
        || default_reference.type_arguments.is_some()
    {
        return Ok(false);
    }
    let constraint_name = NodeRef::new(
        constraint.arena,
        constraint.file,
        constraint_reference.type_name,
    );
    let default_name = NodeRef::new(
        default_type.arena,
        default_type.file,
        default_reference.type_name,
    );
    let constraint_name_record = preflight_node(store, host, constraint_name)?;
    let default_name_record = preflight_node(store, host, default_name)?;
    let (NodeData::Identifier(constraint_identifier), NodeData::Identifier(default_identifier)) =
        (&constraint_name_record.data, &default_name_record.data)
    else {
        return Ok(false);
    };
    Ok(constraint_name_record.parent == Some(constraint.node)
        && default_name_record.parent == Some(default_type.node)
        && constraint_identifier.text == default_identifier.text)
}

fn source_type_parameter_literal_kind(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    node: NodeRef,
) -> Result<Option<SyntaxKind>, SourceCallableError> {
    let record = preflight_node(store, host, node)?;
    let NodeData::LiteralTypeNode(literal) = &record.data else {
        return Ok(None);
    };
    if record.kind != SyntaxKind::LiteralType {
        return Err(invariant(SourceCallableInvariant::InvalidSyntax(node)));
    }
    let literal = NodeRef::new(node.arena, node.file, literal.literal);
    let literal_record = preflight_node(store, host, literal)?;
    if literal_record.parent != Some(node.node) || literal_record.range != record.range {
        return Err(invariant(SourceCallableInvariant::InvalidSyntax(node)));
    }
    let literal_kind = if literal_record.kind == SyntaxKind::PrefixUnaryExpression {
        let NodeData::PrefixUnaryExpression(prefix) = &literal_record.data else {
            return Err(invariant(SourceCallableInvariant::InvalidSyntax(literal)));
        };
        if prefix.operator != SyntaxKind::MinusToken {
            return Ok(None);
        }
        let operand = NodeRef::new(node.arena, node.file, prefix.operand);
        let operand_record = preflight_node(store, host, operand)?;
        if operand_record.parent != Some(literal.node)
            || operand_record.range.start <= literal_record.range.start
            || operand_record.range.end != literal_record.range.end
        {
            return Err(invariant(SourceCallableInvariant::InvalidSyntax(literal)));
        }
        if !matches!(
            operand_record.kind,
            SyntaxKind::NumericLiteral | SyntaxKind::BigIntLiteral
        ) {
            return Ok(None);
        }
        operand_record.kind
    } else {
        literal_record.kind
    };
    Ok(matches!(
        literal_kind,
        SyntaxKind::StringLiteral
            | SyntaxKind::NumericLiteral
            | SyntaxKind::BigIntLiteral
            | SyntaxKind::TrueKeyword
            | SyntaxKind::FalseKeyword
            | SyntaxKind::NullKeyword
    )
    .then_some(literal_kind))
}

/// Checks the primitive/literal default relationships admitted by source generics.
pub(super) fn source_type_parameter_default_is_assignable<MapperPayload>(
    store: &SemanticStore<TypeRecord, MapperPayload>,
    constraint: TypeId,
    default_type: TypeId,
) -> bool {
    if constraint == default_type {
        return true;
    }
    let (Some(constraint_record), Some(default_record)) = (
        store.type_payload(constraint),
        store.type_payload(default_type),
    ) else {
        return false;
    };
    let constraint_flags = constraint_record.flags();
    let default_flags = default_record.flags();
    constraint_flags.intersects(TypeFlags::ANY_OR_UNKNOWN)
        || default_flags.intersects(TypeFlags::NEVER)
        || constraint_flags.intersects(TypeFlags::STRING)
            && default_flags.intersects(TypeFlags::STRING_LITERAL)
        || constraint_flags.intersects(TypeFlags::NUMBER)
            && default_flags.intersects(TypeFlags::NUMBER_LITERAL)
        || constraint_flags.intersects(TypeFlags::BIG_INT)
            && default_flags.intersects(TypeFlags::BIG_INT_LITERAL)
        || constraint_flags.intersects(TypeFlags::BOOLEAN)
            && default_flags.intersects(TypeFlags::BOOLEAN_LITERAL)
}

fn validate_exact_generic_annotation_shape(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    plan: &SourceCallablePlan,
) -> Result<Option<usize>, SourceCallableError> {
    if plan.type_parameters.is_empty() {
        return Ok(None);
    }
    let Some((return_identity_node, _)) = plan.return_type.annotation_identity() else {
        return Err(SourceCallableError::Unsupported(
            SourceCallableUnsupported::GenericInferredReturn(plan.declaration),
        ));
    };
    let generic_return_identity = plan
        .type_predicate
        .and_then(|predicate| predicate.narrowed_type)
        .unwrap_or(return_identity_node);
    let ambient_namespace = plan.body_mode.is_ambient()
        && plan.owner_parent.is_some()
        && host
            .bound_file(plan.declaration)
            .and_then(ts_binder::BoundFile::source_facts)
            .is_some_and(CanonicalSourceFileFacts::is_declaration_file);
    for parameter in &plan.parameters {
        let mut exact = false;
        let mut exact_array = false;
        for type_parameter in &plan.type_parameters {
            exact |= is_naked_source_type_parameter_annotation(
                store,
                host,
                parameter.identity_node,
                type_parameter,
            )?;
        }
        if !exact && let Some(array_targets) = plan.array_targets {
            exact_array = is_exact_source_generic_array_annotation(
                store,
                host,
                parameter.identity_node,
                &plan.type_parameters,
                array_targets,
            )?;
            exact = exact_array;
        }
        if !exact && ambient_namespace {
            exact = exact_ambient_generic_constructor_parameter(
                store,
                host,
                parameter.identity_node,
                &plan.type_parameters,
                plan.array_targets,
            )? || exact_cold_ambient_generic_array_parameter(
                store,
                host,
                parameter.identity_node,
                &plan.type_parameters,
            )?;
        }
        if !exact {
            exact = is_exact_source_generic_interface_reference(
                store,
                host,
                parameter.identity_node,
                &plan.type_parameters,
                plan.array_targets,
            )?;
        }
        if !exact && plan.family == SourceCallableFamily::ArrowFunction {
            exact = is_exact_jsdoc_generic_union_annotation(
                store,
                host,
                parameter.identity_node,
                &plan.type_parameters,
            )?;
        }
        if !exact && !parameter.rest {
            exact = is_exact_source_fixed_generic_parameter_annotation(
                store,
                host,
                parameter.identity_node,
                plan.array_targets,
            )?;
        }
        if parameter.is_implicit_any()
            || parameter.initializer.is_some()
            || parameter.rest && !exact_array
            || !exact
        {
            return Err(SourceCallableError::Unsupported(
                SourceCallableUnsupported::GenericSignature(plan.declaration),
            ));
        }
    }
    if plan.type_predicate.is_some_and(|predicate| {
        predicate.kind == TypePredicateKind::AssertsIdentifier && predicate.narrowed_type.is_none()
    }) {
        return Ok(None);
    }
    let mut return_type_parameter = None;
    for (index, type_parameter) in plan.type_parameters.iter().enumerate() {
        if is_naked_source_type_parameter_annotation(
            store,
            host,
            generic_return_identity,
            type_parameter,
        )? {
            return_type_parameter = Some(index);
        }
    }
    if return_type_parameter.is_none() {
        let exact = is_exact_source_generic_mapper_annotation(
            store,
            host,
            generic_return_identity,
            &plan.type_parameters,
        )? || match plan.array_targets {
            Some(targets) => is_exact_source_generic_array_annotation(
                store,
                host,
                return_identity_node,
                &plan.type_parameters,
                targets,
            )?,
            None => false,
        };
        if !exact {
            return Err(SourceCallableError::Unsupported(
                SourceCallableUnsupported::GenericSignature(plan.declaration),
            ));
        }
    }
    Ok(if plan.type_predicate.is_some() {
        None
    } else {
        return_type_parameter
    })
}

fn is_exact_jsdoc_generic_union_annotation(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    annotation: NodeRef,
    parameters: &[SourceCallableTypeParameterPlan],
) -> Result<bool, SourceCallableError> {
    let record = preflight_node(store, host, annotation)?;
    let NodeData::UnionTypeNode(union) = &record.data else {
        return Ok(false);
    };
    if record.kind != SyntaxKind::UnionType
        || record.flags != NodeFlags::REPARSED
        || union.types.nodes.len() != 2
        || union.types.has_trailing_comma
    {
        return Ok(false);
    }
    let mut undefined = false;
    let mut generic = false;
    for node in &union.types.nodes {
        let member = NodeRef::new(annotation.arena, annotation.file, *node);
        let member_record = preflight_node(store, host, member)?;
        if member_record.parent != Some(annotation.node) {
            return Ok(false);
        }
        if member_record.kind == SyntaxKind::UndefinedKeyword {
            if undefined {
                return Ok(false);
            }
            undefined = true;
        } else {
            let mut matched = false;
            for parameter in parameters {
                matched |=
                    is_naked_source_type_parameter_annotation(store, host, member, parameter)?;
            }
            if !matched || generic {
                return Ok(false);
            }
            generic = true;
        }
    }
    Ok(undefined && generic)
}

/// Accepts fixed primitive parameters and fully proven unary primitive callbacks.
fn is_exact_source_fixed_generic_parameter_annotation(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    annotation: NodeRef,
    array_targets: Option<CanonicalArrayTargets>,
) -> Result<bool, SourceCallableError> {
    let record = preflight_node(store, host, annotation)?;
    if fixed_generic_intrinsic_annotation_kind(record.kind)
        || is_null_literal_type(store, host, annotation)?
    {
        return Ok(true);
    }
    if record.kind != SyntaxKind::FunctionType {
        return Ok(false);
    }
    let Ok(callback) = plan_function_type(store, host, annotation, None, false, array_targets)
    else {
        return Ok(false);
    };
    let [parameter] = callback.parameters.as_slice() else {
        return Ok(false);
    };
    if !callback.type_parameters.is_empty()
        || callback.flags != SignatureFlags::NONE
        || callback.min_argument_count != 1
        || parameter.optional
    {
        return Ok(false);
    }
    let parameter_record = preflight_node(store, host, parameter.type_node)?;
    let return_record = preflight_node(store, host, callback.return_type)?;
    Ok(
        (fixed_generic_intrinsic_annotation_kind(parameter_record.kind)
            || is_null_literal_type(store, host, parameter.type_node)?)
            && (fixed_generic_intrinsic_annotation_kind(return_record.kind)
                || is_null_literal_type(store, host, callback.return_type)?),
    )
}

const fn fixed_generic_intrinsic_annotation_kind(kind: SyntaxKind) -> bool {
    matches!(
        kind,
        SyntaxKind::AnyKeyword
            | SyntaxKind::UnknownKeyword
            | SyntaxKind::StringKeyword
            | SyntaxKind::NumberKeyword
            | SyntaxKind::BigIntKeyword
            | SyntaxKind::BooleanKeyword
            | SyntaxKind::SymbolKeyword
            | SyntaxKind::VoidKeyword
            | SyntaxKind::UndefinedKeyword
            | SyntaxKind::NullKeyword
            | SyntaxKind::NeverKeyword
            | SyntaxKind::ObjectKeyword
    )
}

fn exact_ambient_generic_constructor_parameter(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    annotation: NodeRef,
    type_parameters: &[SourceCallableTypeParameterPlan],
    array_targets: Option<CanonicalArrayTargets>,
) -> Result<bool, SourceCallableError> {
    let record = preflight_node(store, host, annotation)?;
    let NodeData::ConstructorTypeNode(constructor) = &record.data else {
        return Ok(false);
    };
    let Some(return_type) = constructor
        .type_
        .map(|node| NodeRef::new(annotation.arena, annotation.file, node))
    else {
        return Ok(false);
    };
    let [parameter] = constructor.parameters.nodes.as_slice() else {
        return Ok(false);
    };
    let parameter = NodeRef::new(annotation.arena, annotation.file, *parameter);
    let parameter_record = preflight_node(store, host, parameter)?;
    let NodeData::ParameterDeclaration(parameter_data) = &parameter_record.data else {
        return Ok(false);
    };
    let Some(dot) = parameter_data
        .dot_dot_dot_token
        .map(|node| NodeRef::new(parameter.arena, parameter.file, node))
    else {
        return Ok(false);
    };
    let Some(array) = parameter_data
        .type_
        .map(|node| NodeRef::new(parameter.arena, parameter.file, node))
    else {
        return Ok(false);
    };
    let name = NodeRef::new(parameter.arena, parameter.file, parameter_data.name);
    let name_record = preflight_node(store, host, name)?;
    let NodeData::Identifier(identifier) = &name_record.data else {
        return Ok(false);
    };
    let dot_record = preflight_node(store, host, dot)?;
    let array_record = preflight_node(store, host, array)?;
    let NodeData::ArrayTypeNode(array_data) = &array_record.data else {
        return Ok(false);
    };
    let element = NodeRef::new(array.arena, array.file, array_data.element_type);
    let element_record = preflight_node(store, host, element)?;
    let return_record = preflight_node(store, host, return_type)?;
    if record.kind != SyntaxKind::ConstructorType
        || record.flags.0 != 0
        || constructor.full_signature.is_some()
        || constructor.next_container.is_some()
        || constructor.symbol.is_some()
        || constructor.type_parameters.is_some()
        || constructor.modifiers.is_some()
        || constructor.parameters.has_trailing_comma
        || parameter_record.kind != SyntaxKind::Parameter
        || parameter_record.flags.0 != 0
        || parameter_record.parent != Some(annotation.node)
        || parameter_data.symbol.is_some()
        || parameter_data.facts != 0
        || parameter_data.initializer.is_some()
        || parameter_data.question_token.is_some()
        || parameter_data.modifiers.is_some()
        || name_record.kind != SyntaxKind::Identifier
        || name_record.flags.0 != 0
        || name_record.parent != Some(parameter.node)
        || identifier.flow_node.is_some()
        || identifier.text.is_empty()
        || dot_record.kind != SyntaxKind::DotDotDotToken
        || dot_record.flags.0 != 0
        || dot_record.parent != Some(parameter.node)
        || array_record.kind != SyntaxKind::ArrayType
        || array_record.flags.0 != 0
        || array_record.parent != Some(parameter.node)
        || element_record.kind != SyntaxKind::AnyKeyword
        || element_record.flags.0 != 0
        || element_record.parent != Some(array.node)
        || return_record.parent != Some(annotation.node)
    {
        return Ok(false);
    }
    if !type_parameters
        .iter()
        .try_fold(false, |exact, type_parameter| {
            is_naked_source_type_parameter_annotation(store, host, return_type, type_parameter)
                .map(|matches| exact || matches)
        })?
    {
        return Ok(false);
    }

    let Some(bound) = host.bound_file(annotation) else {
        return Ok(false);
    };
    let Some(symbol) = bound
        .symbol(annotation)
        .and_then(|symbol| store.get_merged_symbol(symbol))
    else {
        return Ok(false);
    };
    let Some(owner) = store.symbol(symbol) else {
        return Ok(false);
    };
    let Some(members) = owner
        .members()
        .and_then(|members| store.symbol_table(members))
    else {
        return Ok(false);
    };
    let Some(signature) = members.get(InternalSymbolName::New.as_ref()) else {
        return Ok(false);
    };
    let Some(signature_record) = store.symbol(signature) else {
        return Ok(false);
    };
    let Some(parameter_symbol) = bound
        .symbol(parameter)
        .and_then(|symbol| store.get_merged_symbol(symbol))
    else {
        return Ok(false);
    };
    let Some(parameter_owner) = store.symbol(parameter_symbol) else {
        return Ok(false);
    };
    if owner.flags() != SymbolFlags::TYPE_LITERAL
        || owner.check_flags() != CheckFlags::NONE
        || owner.name() != InternalSymbolName::Type.as_ref()
        || owner.declarations() != Some(&[annotation])
        || owner.value_declaration().is_some()
        || owner.exports().is_some()
        || owner.parent().is_some()
        || owner.export_symbol().is_some()
        || members.len() != 1
        || signature_record.flags() != SymbolFlags::SIGNATURE
        || signature_record.check_flags() != CheckFlags::NONE
        || signature_record.name() != InternalSymbolName::New.as_ref()
        || signature_record.declarations() != Some(&[annotation])
        || signature_record.value_declaration().is_some()
        || signature_record.members().is_some()
        || signature_record.exports().is_some()
        || signature_record.parent().is_some()
        || signature_record.export_symbol().is_some()
        || store.get_merged_symbol(signature) != Some(signature)
        || parameter_owner.flags() != SymbolFlags::FUNCTION_SCOPED_VARIABLE
        || parameter_owner.check_flags() != CheckFlags::NONE
        || parameter_owner.name().as_utf8() != Some(identifier.text.as_str())
        || parameter_owner.declarations() != Some(&[parameter])
        || parameter_owner.value_declaration() != Some(parameter)
        || parameter_owner.members().is_some()
        || parameter_owner.exports().is_some()
        || parameter_owner.parent().is_some()
        || parameter_owner.export_symbol().is_some()
    {
        return Ok(false);
    }

    if store
        .symbol_node_links(annotation)
        .is_some_and(|links| links != &SymbolNodeLinks::default())
        || store
            .type_node_links(annotation)
            .is_some_and(|links| links != &TypeNodeLinks::default())
    {
        return Err(invariant(SourceCallableInvariant::InvalidTypeCache(
            annotation,
        )));
    }
    if store
        .symbol_node_links(array)
        .is_some_and(|links| links != &SymbolNodeLinks::default())
    {
        return Err(invariant(SourceCallableInvariant::InvalidTypeCache(array)));
    }
    if let Some(links) = store.type_node_links(array)
        && links != &TypeNodeLinks::default()
    {
        let Some(targets) = array_targets else {
            return Err(invariant(SourceCallableInvariant::InvalidTypeCache(array)));
        };
        let Some(resolved) = links.resolved_type else {
            return Err(invariant(SourceCallableInvariant::InvalidTypeCache(array)));
        };
        let Some(any) = store
            .intrinsic_bootstrap()
            .map(|bootstrap| bootstrap.any_type)
        else {
            return Err(invariant(SourceCallableInvariant::InvalidTypeCache(array)));
        };
        if links.outer_type_parameters.is_some()
            || !store
                .canonical_array_reference_with_targets(targets, resolved)
                .is_ok_and(|reference| {
                    reference.is_some_and(|reference| {
                        !reference.readonly
                            && !reference.array_literal
                            && reference.element_type == any
                    })
                })
        {
            return Err(invariant(SourceCallableInvariant::InvalidTypeCache(array)));
        }
    }
    Ok(true)
}

fn exact_cold_ambient_generic_array_parameter(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    annotation: NodeRef,
    type_parameters: &[SourceCallableTypeParameterPlan],
) -> Result<bool, SourceCallableError> {
    let Some((SourceGenericArraySyntax::ArrayType, element)) =
        exact_source_generic_array_syntax(store, host, annotation)?
    else {
        return Ok(false);
    };
    if store
        .symbol_node_links(annotation)
        .is_some_and(|links| links != &SymbolNodeLinks::default())
        || store
            .type_node_links(annotation)
            .is_some_and(|links| links != &TypeNodeLinks::default())
    {
        return Err(invariant(SourceCallableInvariant::InvalidTypeCache(
            annotation,
        )));
    }
    for type_parameter in type_parameters {
        if is_naked_source_type_parameter_annotation(store, host, element, type_parameter)? {
            return Ok(true);
        }
    }
    exact_cold_ambient_generic_array_parameter(store, host, element, type_parameters)
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum SourceGenericParameterCacheState {
    Cold,
    Warm(TypeId),
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum SourceGenericArraySyntax {
    ArrayType,
    TypeReference,
}

/// Admits an exact, nonempty chain of mutable `T[]` and `Array<T>` wrappers
/// terminating in one declared source type parameter. Planning may encounter a
/// completely cold chain or a previously queried chain. A warm wrapper is
/// trusted only when every child is warm and the complete chain retains the
/// authoritative mutable-array target and exact element identities.
fn is_exact_source_generic_array_annotation(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    annotation: NodeRef,
    type_parameters: &[SourceCallableTypeParameterPlan],
    array_targets: CanonicalArrayTargets,
) -> Result<bool, SourceCallableError> {
    let mut active = HashSet::new();
    let Some((syntax, element)) = exact_source_generic_array_syntax(store, host, annotation)?
    else {
        return Ok(false);
    };
    if !active.insert(annotation) {
        return Err(invariant(SourceCallableInvariant::InvalidParameter(
            annotation,
        )));
    }
    let result = exact_source_generic_parameter_annotation(
        store,
        host,
        element,
        type_parameters,
        array_targets,
        &mut active,
    )?
    .map(|element_state| {
        validate_source_generic_array_annotation_cache(
            store,
            annotation,
            syntax,
            element_state,
            array_targets,
        )
    })
    .transpose();
    active.remove(&annotation);
    Ok(result?.is_some())
}

fn exact_source_generic_parameter_annotation(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    annotation: NodeRef,
    type_parameters: &[SourceCallableTypeParameterPlan],
    array_targets: CanonicalArrayTargets,
    active: &mut HashSet<NodeRef>,
) -> Result<Option<SourceGenericParameterCacheState>, SourceCallableError> {
    for type_parameter in type_parameters {
        if is_naked_source_type_parameter_annotation(store, host, annotation, type_parameter)? {
            return source_type_parameter_annotation_cache_state(store, annotation, type_parameter)
                .map(Some);
        }
    }
    let Some((syntax, element)) = exact_source_generic_array_syntax(store, host, annotation)?
    else {
        return Ok(None);
    };
    if !active.insert(annotation) {
        return Err(invariant(SourceCallableInvariant::InvalidParameter(
            annotation,
        )));
    }
    let result = (|| {
        let Some(element_state) = exact_source_generic_parameter_annotation(
            store,
            host,
            element,
            type_parameters,
            array_targets,
            active,
        )?
        else {
            return Ok(None);
        };
        validate_source_generic_array_annotation_cache(
            store,
            annotation,
            syntax,
            element_state,
            array_targets,
        )
        .map(Some)
    })();
    active.remove(&annotation);
    result
}

fn exact_source_generic_array_syntax(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    annotation: NodeRef,
) -> Result<Option<(SourceGenericArraySyntax, NodeRef)>, SourceCallableError> {
    let record = preflight_node(store, host, annotation)?;
    match &record.data {
        NodeData::ArrayTypeNode(array) if record.kind == SyntaxKind::ArrayType => {
            let element = NodeRef::new(annotation.arena, annotation.file, array.element_type);
            let element_record = preflight_node(store, host, element)?;
            if element_record.parent != Some(annotation.node)
                || element_record.range.start != record.range.start
                || element_record.range.end >= record.range.end
            {
                return Err(invariant(SourceCallableInvariant::InvalidParameter(
                    annotation,
                )));
            }
            Ok(Some((SourceGenericArraySyntax::ArrayType, element)))
        }
        NodeData::TypeReferenceNode(reference) if record.kind == SyntaxKind::TypeReference => {
            let Some(arguments) = &reference.type_arguments else {
                return Ok(None);
            };
            let [argument] = arguments.nodes.as_slice() else {
                return Ok(None);
            };
            let name = NodeRef::new(annotation.arena, annotation.file, reference.type_name);
            let name_record = preflight_node(store, host, name)?;
            let NodeData::Identifier(identifier) = &name_record.data else {
                return Ok(None);
            };
            let argument = NodeRef::new(annotation.arena, annotation.file, *argument);
            let argument_record = preflight_node(store, host, argument)?;
            if identifier.text != "Array"
                || identifier.flow_node.is_some()
                || name_record.kind != SyntaxKind::Identifier
                || name_record.parent != Some(annotation.node)
                || name_record.flags.0 != 0
                || argument_record.parent != Some(annotation.node)
                || arguments.has_trailing_comma
                || arguments.range.start < name_record.range.end
                || arguments.range.end != record.range.end
                || arguments.range.start >= arguments.range.end
                || argument_record.range.start <= arguments.range.start
                || argument_record.range.end >= arguments.range.end
                || argument_record.range.start < record.range.start
                || argument_record.range.end > record.range.end
            {
                return Ok(None);
            }
            Ok(Some((SourceGenericArraySyntax::TypeReference, argument)))
        }
        _ => Ok(None),
    }
}

fn source_type_parameter_annotation_cache_state(
    store: &CanonicalTypeMapperStore,
    annotation: NodeRef,
    type_parameter: &SourceCallableTypeParameterPlan,
) -> Result<SourceGenericParameterCacheState, SourceCallableError> {
    let symbol_links = store.symbol_node_links(annotation);
    let type_links = store.type_node_links(annotation);
    let symbol_cold = symbol_links.is_none_or(|links| links == &SymbolNodeLinks::default());
    let type_cold = type_links.is_none_or(|links| links == &TypeNodeLinks::default());
    if symbol_cold && type_cold {
        return Ok(SourceGenericParameterCacheState::Cold);
    }
    let declared_type = store
        .declared_type_links(type_parameter.symbol)
        .and_then(|links| links.declared_type)
        .filter(|declared_type| {
            cached_ordinary_type_parameter_owner(store, *declared_type)
                == Some(type_parameter.symbol)
        })
        .filter(|declared_type| {
            source_type_parameter_annotation_links_are_fully_warm(
                store,
                annotation,
                type_parameter.symbol,
                *declared_type,
            )
        })
        .ok_or_else(|| invariant(SourceCallableInvariant::InvalidTypeCache(annotation)))?;
    Ok(SourceGenericParameterCacheState::Warm(declared_type))
}

fn validate_source_generic_array_annotation_cache(
    store: &CanonicalTypeMapperStore,
    annotation: NodeRef,
    syntax: SourceGenericArraySyntax,
    element_state: SourceGenericParameterCacheState,
    array_targets: CanonicalArrayTargets,
) -> Result<SourceGenericParameterCacheState, SourceCallableError> {
    let symbol_links = store.symbol_node_links(annotation);
    let type_links = store.type_node_links(annotation);
    let symbol_cold = symbol_links.is_none_or(|links| links == &SymbolNodeLinks::default());
    let type_cold = type_links.is_none_or(|links| links == &TypeNodeLinks::default());
    if symbol_cold && type_cold {
        return Ok(SourceGenericParameterCacheState::Cold);
    }
    let SourceGenericParameterCacheState::Warm(element_type) = element_state else {
        return Err(invariant(SourceCallableInvariant::InvalidTypeCache(
            annotation,
        )));
    };
    let Some(resolved) = type_links.and_then(|links| {
        let resolved = links.resolved_type?;
        (links
            == &TypeNodeLinks {
                resolved_type: Some(resolved),
                outer_type_parameters: None,
            })
            .then_some(resolved)
    }) else {
        return Err(invariant(SourceCallableInvariant::InvalidTypeCache(
            annotation,
        )));
    };
    match syntax {
        SourceGenericArraySyntax::ArrayType if !symbol_cold => {
            return Err(invariant(SourceCallableInvariant::InvalidTypeCache(
                annotation,
            )));
        }
        SourceGenericArraySyntax::TypeReference => {
            let expected_symbol = store
                .type_payload(array_targets.array_type())
                .and_then(TypeRecord::symbol)
                .and_then(|symbol| store.get_merged_symbol(symbol))
                .ok_or_else(|| invariant(SourceCallableInvariant::InvalidTypeCache(annotation)))?;
            if symbol_links
                != Some(&SymbolNodeLinks {
                    resolved_symbol: Some(expected_symbol),
                })
            {
                return Err(invariant(SourceCallableInvariant::InvalidTypeCache(
                    annotation,
                )));
            }
        }
        SourceGenericArraySyntax::ArrayType => {}
    }
    let array = store
        .canonical_array_reference_with_targets(array_targets, resolved)
        .map_err(|_| invariant(SourceCallableInvariant::InvalidTypeCache(annotation)))?
        .filter(|array| {
            !array.readonly && !array.array_literal && array.element_type == element_type
        })
        .ok_or_else(|| invariant(SourceCallableInvariant::InvalidTypeCache(annotation)))?;
    debug_assert_eq!(array.element_type, element_type);
    Ok(SourceGenericParameterCacheState::Warm(resolved))
}

fn is_exact_source_generic_mapper_annotation(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    annotation: NodeRef,
    type_parameters: &[SourceCallableTypeParameterPlan],
) -> Result<bool, SourceCallableError> {
    let record = preflight_node(store, host, annotation)?;
    let valid = if matches!(
        record.kind,
        SyntaxKind::AnyKeyword
            | SyntaxKind::UnknownKeyword
            | SyntaxKind::StringKeyword
            | SyntaxKind::NumberKeyword
            | SyntaxKind::BigIntKeyword
            | SyntaxKind::BooleanKeyword
            | SyntaxKind::SymbolKeyword
            | SyntaxKind::VoidKeyword
            | SyntaxKind::UndefinedKeyword
            | SyntaxKind::NullKeyword
            | SyntaxKind::NeverKeyword
            | SyntaxKind::ObjectKeyword
            | SyntaxKind::IntrinsicKeyword
    ) || is_null_literal_type(store, host, annotation)?
    {
        true
    } else if record.kind == SyntaxKind::TypeReference {
        let mut exact = false;
        for type_parameter in type_parameters {
            exact |=
                is_naked_source_type_parameter_annotation(store, host, annotation, type_parameter)?;
        }
        if !exact {
            exact = is_exact_source_generic_interface_reference(
                store,
                host,
                annotation,
                type_parameters,
                None,
            )?;
        }
        exact
    } else {
        false
    };
    Ok(valid)
}

fn is_exact_source_generic_interface_reference(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    annotation: NodeRef,
    type_parameters: &[SourceCallableTypeParameterPlan],
    array_targets: Option<CanonicalArrayTargets>,
) -> Result<bool, SourceCallableError> {
    let record = preflight_node(store, host, annotation)?;
    let NodeData::TypeReferenceNode(reference) = &record.data else {
        return Ok(false);
    };
    let Some(arguments) = reference.type_arguments.as_ref() else {
        return Ok(false);
    };
    let name = NodeRef::new(annotation.arena, annotation.file, reference.type_name);
    let name_record = preflight_node(store, host, name)?;
    let NodeData::Identifier(identifier) = &name_record.data else {
        return Ok(false);
    };
    if record.kind != SyntaxKind::TypeReference
        || record.flags.0 != 0
        || arguments.nodes.is_empty()
        || arguments.has_trailing_comma
        || name_record.kind != SyntaxKind::Identifier
        || name_record.flags.0 != 0
        || name_record.parent != Some(annotation.node)
        || identifier.flow_node.is_some()
        || identifier.text.is_empty()
    {
        return Ok(false);
    }

    let symbol = match host.name_resolver_host(store) {
        Ok(mut callback_host) => {
            let (arena, bound) = host
                .source(annotation)
                .ok_or_else(|| invariant(SourceCallableInvariant::InvalidTypeCache(annotation)))?;
            CanonicalNameResolver::new(arena, bound, store.symbol_store(), &mut callback_host)
                .map_err(DeclaredTypeError::from)?
                .resolve(
                    Some(CanonicalResolutionLocation::Bound(name)),
                    &identifier.text,
                    SymbolFlags::TYPE,
                    None,
                    true,
                    false,
                )
                .map_err(DeclaredTypeError::from)?
                .and_then(|symbol| store.get_merged_symbol(symbol))
        }
        Err(DeclaredTypeError::Unavailable(
            DeclaredTypeUnavailable::PostGlobalNameResolutionUnavailable,
        )) => enclosing_namespace_type_symbol(store, host, annotation, &identifier.text),
        Err(error) => return Err(error.into()),
    };
    let Some(symbol) = symbol else {
        return Ok(false);
    };
    let Some(owner) = store.symbol(symbol) else {
        return Ok(false);
    };
    let Some(declarations) = owner.declarations() else {
        return Ok(false);
    };
    if !owner.flags().contains(SymbolFlags::INTERFACE)
        || owner
            .flags()
            .without(SymbolFlags::INTERFACE | SymbolFlags::TRANSIENT)
            != SymbolFlags::NONE
        || declarations.is_empty()
        || declarations.iter().any(|declaration| {
            host.node(*declaration).is_none_or(|record| {
                !matches!(
                    &record.data,
                    NodeData::InterfaceDeclaration(interface)
                        if record.kind == SyntaxKind::InterfaceDeclaration
                            && interface
                                .type_parameters
                                .as_ref()
                                .is_some_and(|parameters| {
                                    parameters.nodes.len() == arguments.nodes.len()
                                })
                )
            })
        })
    {
        return Ok(false);
    }

    let mut argument_nodes = Vec::with_capacity(arguments.nodes.len());
    for argument_id in &arguments.nodes {
        let argument = NodeRef::new(annotation.arena, annotation.file, *argument_id);
        let argument_record = preflight_node(store, host, argument)?;
        if argument_record.parent != Some(annotation.node) {
            return Err(invariant(SourceCallableInvariant::InvalidTypeCache(
                argument,
            )));
        }
        let mut exact = false;
        for type_parameter in type_parameters {
            exact |=
                is_naked_source_type_parameter_annotation(store, host, argument, type_parameter)?;
        }
        if !exact && let Some(array_targets) = array_targets {
            exact = is_exact_source_generic_array_annotation(
                store,
                host,
                argument,
                type_parameters,
                array_targets,
            )?;
        }
        if !exact {
            exact = is_exact_source_generic_interface_reference(
                store,
                host,
                argument,
                type_parameters,
                array_targets,
            )?;
        }
        if !exact {
            return Ok(false);
        }
        argument_nodes.push(argument);
    }

    let symbol_links = store.symbol_node_links(annotation);
    let type_links = store.type_node_links(annotation);
    let symbol_cold = symbol_links.is_none_or(|links| links == &SymbolNodeLinks::default());
    let type_cold = type_links.is_none_or(|links| links == &TypeNodeLinks::default());
    if symbol_cold && type_cold {
        return Ok(true);
    }
    let Some(resolved) = type_links.and_then(|links| {
        links.resolved_type.filter(|resolved| {
            links
                == &TypeNodeLinks {
                    resolved_type: Some(*resolved),
                    outer_type_parameters: None,
                }
        })
    }) else {
        return Err(invariant(SourceCallableInvariant::InvalidTypeCache(
            annotation,
        )));
    };
    let Some(target) = store
        .declared_type_links(symbol)
        .and_then(|links| links.declared_type)
    else {
        return Err(invariant(SourceCallableInvariant::InvalidTypeCache(
            annotation,
        )));
    };
    let reference = validate_direct_generic_reference(store, resolved)
        .map_err(|_| invariant(SourceCallableInvariant::InvalidTypeCache(annotation)))?;
    if symbol_links
        != Some(&SymbolNodeLinks {
            resolved_symbol: Some(symbol),
        })
        || reference.target != target
        || reference.type_arguments.len() != argument_nodes.len()
        || reference
            .type_arguments
            .iter()
            .zip(argument_nodes)
            .any(|(expected, node)| {
                store
                    .type_node_links(node)
                    .and_then(|links| links.resolved_type)
                    != Some(*expected)
            })
    {
        return Err(invariant(SourceCallableInvariant::InvalidTypeCache(
            annotation,
        )));
    }
    Ok(true)
}

fn is_naked_source_type_parameter_annotation(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    annotation: NodeRef,
    type_parameter: &SourceCallableTypeParameterPlan,
) -> Result<bool, SourceCallableError> {
    let annotation_record = preflight_node(store, host, annotation)?;
    let NodeData::TypeReferenceNode(reference) = &annotation_record.data else {
        return Ok(false);
    };
    if annotation_record.kind != SyntaxKind::TypeReference || reference.type_arguments.is_some() {
        return Ok(false);
    }
    let name = NodeRef::new(annotation.arena, annotation.file, reference.type_name);
    let name_record = preflight_node(store, host, name)?;
    let NodeData::Identifier(name_identifier) = &name_record.data else {
        return Ok(false);
    };
    let type_parameter_record = preflight_node(store, host, type_parameter.declaration)?;
    let NodeData::TypeParameterDeclaration(type_parameter_data) = &type_parameter_record.data
    else {
        return Err(invariant(SourceCallableInvariant::InvalidSyntax(
            type_parameter.declaration,
        )));
    };
    let declaration_name = NodeRef::new(
        type_parameter.declaration.arena,
        type_parameter.declaration.file,
        type_parameter_data.name,
    );
    let declaration_name_record = preflight_node(store, host, declaration_name)?;
    let NodeData::Identifier(declaration_identifier) = &declaration_name_record.data else {
        return Err(invariant(SourceCallableInvariant::InvalidSyntax(
            declaration_name,
        )));
    };
    let exact_syntax = name_record.kind == SyntaxKind::Identifier
        && name_record.parent == Some(annotation.node)
        && name_record.flags.0 == 0
        && name_identifier.flow_node.is_none()
        && name_identifier.text == declaration_identifier.text;
    if exact_syntax {
        validate_source_type_parameter_annotation_links(store, annotation, type_parameter)?;
    }
    Ok(exact_syntax)
}

/// A naked source `T` annotation is either untouched or has the complete
/// symbol/type pair produced by a canonical type-reference query. Accepting a
/// lone warm side would let the generic callable fast path trust a type cache
/// that was never proven to belong to its declared type parameter.
fn validate_source_type_parameter_annotation_links(
    store: &CanonicalTypeMapperStore,
    annotation: NodeRef,
    type_parameter: &SourceCallableTypeParameterPlan,
) -> Result<(), SourceCallableError> {
    let symbol_links = store.symbol_node_links(annotation);
    let type_links = store.type_node_links(annotation);
    let symbol_cold = symbol_links.is_none_or(|links| links == &SymbolNodeLinks::default());
    let type_cold = type_links.is_none_or(|links| links == &TypeNodeLinks::default());
    if symbol_cold && type_cold {
        return Ok(());
    }

    let declared_type = store
        .declared_type_links(type_parameter.symbol)
        .and_then(|links| links.declared_type)
        .filter(|declared_type| {
            cached_ordinary_type_parameter_owner(store, *declared_type)
                == Some(type_parameter.symbol)
        });
    let fully_warm = declared_type.is_some_and(|declared_type| {
        source_type_parameter_annotation_links_are_fully_warm(
            store,
            annotation,
            type_parameter.symbol,
            declared_type,
        )
    });
    if !fully_warm {
        return Err(invariant(SourceCallableInvariant::InvalidTypeCache(
            annotation,
        )));
    }
    Ok(())
}

fn source_type_parameter_annotation_links_are_fully_warm(
    store: &CanonicalTypeMapperStore,
    annotation: NodeRef,
    symbol: SemanticSymbolId,
    declared_type: TypeId,
) -> bool {
    store.symbol_node_links(annotation)
        == Some(&SymbolNodeLinks {
            resolved_symbol: Some(symbol),
        })
        && store.type_node_links(annotation)
            == Some(&TypeNodeLinks {
                resolved_type: Some(declared_type),
                outer_type_parameters: None,
            })
}

fn source_type_parameter_annotation_links_are_cold_or_fully_warm(
    store: &CanonicalTypeMapperStore,
    annotation: NodeRef,
    symbol: SemanticSymbolId,
    declared_type: TypeId,
) -> bool {
    let symbol_links = store.symbol_node_links(annotation);
    let type_links = store.type_node_links(annotation);
    let cold = symbol_links.is_none_or(|links| links == &SymbolNodeLinks::default())
        && type_links.is_none_or(|links| links == &TypeNodeLinks::default());
    cold || source_type_parameter_annotation_links_are_fully_warm(
        store,
        annotation,
        symbol,
        declared_type,
    )
}

fn validate_modifiers(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    declaration: NodeRef,
    declaration_range: ts_core::TextRange,
    view: &SourceSyntaxView<'_>,
) -> Result<SourceCallableBodyMode, SourceCallableError> {
    let is_declaration_file = host
        .bound_file(declaration)
        .and_then(ts_binder::BoundFile::source_facts)
        .is_some_and(CanonicalSourceFileFacts::is_declaration_file);
    let Some(modifiers) = view.modifiers else {
        return Ok(
            if is_declaration_file
                && view.family == SourceCallableFamily::FunctionDeclaration
                && view.body.is_none()
            {
                SourceCallableBodyMode::AmbientDeclaration
            } else {
                SourceCallableBodyMode::Present
            },
        );
    };
    if modifiers.flags.0 != 0
        || modifiers.list.has_trailing_comma
        || modifiers.list.range.start != declaration_range.start
    {
        return Err(SourceCallableError::Unsupported(
            SourceCallableUnsupported::Modifiers(declaration),
        ));
    }

    let mut modifier_kinds = Vec::with_capacity(modifiers.list.nodes.len());
    let mut previous_end = declaration_range.start;
    for modifier_id in &modifiers.list.nodes {
        let modifier = NodeRef::new(declaration.arena, declaration.file, *modifier_id);
        let record = preflight_node(store, host, modifier)?;
        if !matches!(
            record.kind,
            SyntaxKind::ExportKeyword | SyntaxKind::DeclareKeyword | SyntaxKind::AsyncKeyword
        ) || !matches!(record.data, NodeData::Token(_))
            || record.flags.0 != 0
            || record.parent != Some(declaration.node)
            || record.range.start < previous_end
            || modifier_kinds.is_empty() && record.range.start != declaration_range.start
            || record.range.end > view.parameters.range.start
        {
            return Err(SourceCallableError::Unsupported(
                SourceCallableUnsupported::Modifiers(modifier),
            ));
        }
        previous_end = record.range.end;
        modifier_kinds.push(record.kind);
    }

    match modifier_kinds.as_slice() {
        [SyntaxKind::AsyncKeyword]
            if !is_declaration_file
                && view.family == SourceCallableFamily::ArrowFunction
                && view.parameters.nodes.is_empty()
                && !view.parameters.has_trailing_comma
                && view.type_parameters.is_none()
                && view.return_type.is_none() =>
        {
            Ok(SourceCallableBodyMode::Present)
        }
        [SyntaxKind::AsyncKeyword]
            if !is_declaration_file
                && (valid_async_jsx_source_function(store, host, declaration, view)?
                    || valid_async_source_function(store, host, declaration, view)?) =>
        {
            Ok(SourceCallableBodyMode::Present)
        }
        [SyntaxKind::AsyncKeyword] | [SyntaxKind::ExportKeyword, SyntaxKind::AsyncKeyword]
            if !is_declaration_file
                && valid_async_annotated_source_function(store, host, declaration, view)? =>
        {
            Ok(SourceCallableBodyMode::Present)
        }
        [SyntaxKind::AsyncKeyword] => Err(SourceCallableError::Unsupported(
            SourceCallableUnsupported::Async(NodeRef::new(
                declaration.arena,
                declaration.file,
                modifiers.list.nodes[0],
            )),
        )),
        [SyntaxKind::ExportKeyword, SyntaxKind::AsyncKeyword] => Err(
            SourceCallableError::Unsupported(SourceCallableUnsupported::Async(NodeRef::new(
                declaration.arena,
                declaration.file,
                modifiers.list.nodes[1],
            ))),
        ),
        [SyntaxKind::DeclareKeyword] | [SyntaxKind::ExportKeyword, SyntaxKind::DeclareKeyword]
            if view.family == SourceCallableFamily::FunctionDeclaration =>
        {
            Ok(SourceCallableBodyMode::AmbientDeclaration)
        }
        [SyntaxKind::ExportKeyword]
            if view.family == SourceCallableFamily::FunctionDeclaration
                && is_declaration_file
                && view.body.is_none() =>
        {
            Ok(SourceCallableBodyMode::AmbientDeclaration)
        }
        [SyntaxKind::ExportKeyword] if view.family == SourceCallableFamily::FunctionDeclaration => {
            Ok(SourceCallableBodyMode::Present)
        }
        _ => Err(SourceCallableError::Unsupported(
            SourceCallableUnsupported::Modifiers(declaration),
        )),
    }
}

fn valid_async_source_function(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    declaration: NodeRef,
    view: &SourceSyntaxView<'_>,
) -> Result<bool, SourceCallableError> {
    if view.family != SourceCallableFamily::FunctionDeclaration
        || !view.parameters.nodes.is_empty()
        || view.parameters.has_trailing_comma
        || view.type_parameters.is_some()
        || host.bound_file(declaration).is_none_or(|bound| {
            bound
                .source_facts()
                .is_none_or(|facts| facts.is_declaration_file() || facts.is_javascript_file())
        })
    {
        return Ok(false);
    }

    let Some(body) = view
        .body
        .map(|node| NodeRef::new(declaration.arena, declaration.file, node))
    else {
        return Ok(false);
    };
    let body_record = preflight_node(store, host, body)?;
    let NodeData::Block(block) = &body_record.data else {
        return Ok(false);
    };
    if body_record.kind != SyntaxKind::Block
        || body_record.flags.0 != 0
        || body_record.parent != Some(declaration.node)
        || block.flow_node.is_some()
        || block.next_container.is_some()
        || block.statements.has_trailing_comma
        || block.facts != 0
    {
        return Ok(false);
    }
    for statement in &block.statements.nodes {
        let statement = NodeRef::new(body.arena, body.file, *statement);
        let statement_record = preflight_node(store, host, statement)?;
        if let NodeData::ReturnStatement(returned) = &statement_record.data
            && returned.expression.is_some_and(|expression| {
                matches!(
                    store.source_node_kind(NodeRef::new(body.arena, body.file, expression)),
                    Some(
                        SyntaxKind::JsxElement
                            | SyntaxKind::JsxSelfClosingElement
                            | SyntaxKind::JsxFragment
                    )
                )
            })
        {
            return Ok(false);
        }
    }

    let Some(annotation) = view
        .return_type
        .map(|node| NodeRef::new(declaration.arena, declaration.file, node))
    else {
        return Ok(true);
    };
    let annotation_record = preflight_node(store, host, annotation)?;
    let NodeData::TypeReferenceNode(reference) = &annotation_record.data else {
        return Ok(false);
    };
    let Some(arguments) = &reference.type_arguments else {
        return Ok(false);
    };
    let [argument] = arguments.nodes.as_slice() else {
        return Ok(false);
    };
    let name = NodeRef::new(annotation.arena, annotation.file, reference.type_name);
    let name_record = preflight_node(store, host, name)?;
    let NodeData::Identifier(identifier) = &name_record.data else {
        return Ok(false);
    };
    let argument = NodeRef::new(annotation.arena, annotation.file, *argument);
    let argument_record = preflight_node(store, host, argument)?;

    Ok(annotation_record.kind == SyntaxKind::TypeReference
        && annotation_record.flags.0 == 0
        && annotation_record.parent == Some(declaration.node)
        && !arguments.has_trailing_comma
        && name_record.kind == SyntaxKind::Identifier
        && name_record.flags.0 == 0
        && name_record.parent == Some(annotation.node)
        && identifier.flow_node.is_none()
        && identifier.text == "Promise"
        && argument_record.kind == SyntaxKind::NumberKeyword
        && argument_record.flags.0 == 0
        && argument_record.parent == Some(annotation.node))
}

fn valid_async_annotated_source_function(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    declaration: NodeRef,
    view: &SourceSyntaxView<'_>,
) -> Result<bool, SourceCallableError> {
    if view.family != SourceCallableFamily::FunctionDeclaration
        || view.parameters.has_trailing_comma
        || view.type_parameters.is_some()
        || view.body.is_none()
    {
        return Ok(false);
    }
    let Some(bound) = host.bound_file(declaration) else {
        return Ok(false);
    };
    if bound
        .source_facts()
        .is_none_or(|facts| facts.is_declaration_file() || facts.is_javascript_file())
    {
        return Ok(false);
    }
    let Some(annotation) = view
        .return_type
        .map(|node| NodeRef::new(declaration.arena, declaration.file, node))
    else {
        return Ok(false);
    };
    let annotation_record = preflight_node(store, host, annotation)?;
    let NodeData::TypeReferenceNode(reference) = &annotation_record.data else {
        return Ok(false);
    };
    let Some(arguments) = reference.type_arguments.as_ref() else {
        return Ok(false);
    };
    let [argument] = arguments.nodes.as_slice() else {
        return Ok(false);
    };
    let argument = NodeRef::new(annotation.arena, annotation.file, *argument);
    let argument_record = preflight_node(store, host, argument)?;
    let name = NodeRef::new(annotation.arena, annotation.file, reference.type_name);
    let name_record = preflight_node(store, host, name)?;
    let NodeData::Identifier(identifier) = &name_record.data else {
        return Ok(false);
    };
    if annotation_record.kind != SyntaxKind::TypeReference
        || annotation_record.flags.0 != 0
        || annotation_record.parent != Some(declaration.node)
        || arguments.has_trailing_comma
        || argument_record.parent != Some(annotation.node)
        || name_record.kind != SyntaxKind::Identifier
        || name_record.flags.0 != 0
        || name_record.parent != Some(annotation.node)
        || identifier.text != "Promise"
        || identifier.flow_node.is_some()
    {
        return Ok(false);
    }

    let Some(global_promise) = store
        .intrinsic_bootstrap()
        .and_then(|bootstrap| store.symbol_table(bootstrap.globals))
        .and_then(|globals| globals.get_source("Promise"))
        .and_then(|symbol| store.get_merged_symbol(symbol))
    else {
        return Ok(false);
    };
    let Some(owner) = store.symbol(global_promise) else {
        return Ok(false);
    };
    let allowed_flags =
        SymbolFlags::INTERFACE | SymbolFlags::FUNCTION_SCOPED_VARIABLE | SymbolFlags::TRANSIENT;
    if !owner.flags().contains(SymbolFlags::INTERFACE)
        || owner.flags().without(allowed_flags) != SymbolFlags::NONE
        || owner.parent().is_some()
        || owner.declarations().is_none_or(|declarations| {
            declarations.is_empty()
                || declarations.iter().any(|candidate| {
                    host.bound_file(*candidate)
                        .and_then(ts_binder::BoundFile::source_facts)
                        .is_none_or(|facts| {
                            !facts.is_default_library() || !facts.is_declaration_file()
                        })
                        || !host.symbol_matches(store, *candidate, global_promise)
                        || host
                            .node(*candidate)
                            .is_none_or(|record| match &record.data {
                                NodeData::InterfaceDeclaration(interface) => {
                                    record.kind != SyntaxKind::InterfaceDeclaration
                                        || interface.type_parameters.as_ref().is_none_or(
                                            |parameters| {
                                                parameters.nodes.len() != 1
                                                    || parameters.has_trailing_comma
                                            },
                                        )
                                }
                                NodeData::VariableDeclaration(_) => {
                                    record.kind != SyntaxKind::VariableDeclaration
                                        || !owner
                                            .flags()
                                            .contains(SymbolFlags::FUNCTION_SCOPED_VARIABLE)
                                }
                                _ => true,
                            })
                })
        })
    {
        return Ok(false);
    }

    let (arena, bound) = host
        .source(annotation)
        .ok_or_else(|| invariant(SourceCallableInvariant::InvalidTypeCache(annotation)))?;
    let mut callback_host = host.name_resolver_host(store)?;
    let resolved =
        CanonicalNameResolver::new(arena, bound, store.symbol_store(), &mut callback_host)
            .map_err(DeclaredTypeError::from)?
            .resolve(
                Some(CanonicalResolutionLocation::Bound(name)),
                "Promise",
                SymbolFlags::TYPE,
                None,
                true,
                false,
            )
            .map_err(DeclaredTypeError::from)?
            .and_then(|symbol| store.get_merged_symbol(symbol));
    Ok(resolved == Some(global_promise))
}

fn valid_async_jsx_source_function(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    declaration: NodeRef,
    view: &SourceSyntaxView<'_>,
) -> Result<bool, SourceCallableError> {
    if view.family != SourceCallableFamily::FunctionDeclaration
        || !view.parameters.nodes.is_empty()
        || view.parameters.has_trailing_comma
        || view.type_parameters.is_some()
        || view.return_type.is_some()
    {
        return Ok(false);
    }
    let Some(bound) = host.bound_file(declaration) else {
        return Ok(false);
    };
    if bound
        .source_facts()
        .is_none_or(|facts| facts.is_declaration_file() || facts.is_javascript_file())
    {
        return Ok(false);
    }
    let Some(body) = view
        .body
        .map(|body| NodeRef::new(declaration.arena, declaration.file, body))
    else {
        return Ok(false);
    };
    let body_record = preflight_node(store, host, body)?;
    let NodeData::Block(block) = &body_record.data else {
        return Ok(false);
    };
    let [statement] = block.statements.nodes.as_slice() else {
        return Ok(false);
    };
    let statement = NodeRef::new(body.arena, body.file, *statement);
    let statement_record = preflight_node(store, host, statement)?;
    let NodeData::ReturnStatement(return_statement) = &statement_record.data else {
        return Ok(false);
    };
    let Some(expression) = return_statement
        .expression
        .map(|expression| NodeRef::new(statement.arena, statement.file, expression))
    else {
        return Ok(false);
    };
    let expression_record = preflight_node(store, host, expression)?;
    Ok(body_record.kind == SyntaxKind::Block
        && body_record.flags.0 == 0
        && body_record.parent == Some(declaration.node)
        && !block.statements.has_trailing_comma
        && block.facts == 0
        && statement_record.kind == SyntaxKind::ReturnStatement
        && statement_record.flags.0 == 0
        && statement_record.parent == Some(body.node)
        && return_statement.flow_node.is_none()
        && return_statement.facts == 0
        && expression_record.parent == Some(statement.node)
        && matches!(
            expression_record.kind,
            SyntaxKind::JsxElement | SyntaxKind::JsxSelfClosingElement | SyntaxKind::JsxFragment
        ))
}

fn validate_owner_name_and_export_route(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    declaration: NodeRef,
    owner: &ts_binder::semantic::Symbol,
    local_symbol: Option<SemanticSymbolId>,
    body_mode: SourceCallableBodyMode,
    view: &SourceSyntaxView<'_>,
) -> Result<(), SourceCallableError> {
    match view.family {
        SourceCallableFamily::ArrowFunction => {
            if view.name.is_some()
                || owner.name() != InternalSymbolName::Function.as_ref()
                || owner.parent().is_some()
                || local_symbol.is_some()
            {
                return Err(invariant(SourceCallableInvariant::InvalidOwnerSymbol(
                    declaration,
                )));
            }
        }
        SourceCallableFamily::FunctionDeclaration => {
            let bound = host.bound_file(declaration).ok_or_else(|| {
                invariant(SourceCallableInvariant::InvalidExportRoute(declaration))
            })?;
            let Some(name_id) = view.name else {
                return Err(invariant(SourceCallableInvariant::InvalidOwnerSymbol(
                    declaration,
                )));
            };
            let name = NodeRef::new(declaration.arena, declaration.file, name_id);
            let name_record = preflight_node(store, host, name)?;
            let NodeData::Identifier(identifier) = &name_record.data else {
                return Err(invariant(SourceCallableInvariant::InvalidOwnerSymbol(
                    declaration,
                )));
            };
            if name_record.kind != SyntaxKind::Identifier
                || name_record.parent != Some(declaration.node)
                || owner.name().as_bytes() != identifier.text.as_bytes()
            {
                return Err(invariant(SourceCallableInvariant::InvalidOwnerSymbol(
                    declaration,
                )));
            }
            match local_symbol {
                None if owner.parent().is_none()
                    && (view.modifiers.is_none()
                        || body_mode.is_ambient()
                        || view.is_async(store, declaration)) => {}
                Some(local) if view.modifiers.is_some() || body_mode.is_ambient() => {
                    let parent = owner.parent().ok_or_else(|| {
                        invariant(SourceCallableInvariant::InvalidExportRoute(declaration))
                    })?;
                    let source_parent = bound.symbol(bound.source_file()).is_some_and(|source| {
                        source == parent && store.get_merged_symbol(source) == Some(source)
                    });
                    let namespace_parent = bound.source_facts().is_some_and(|facts| {
                        body_mode.is_ambient() && facts.is_declaration_file()
                            || !body_mode.is_ambient()
                                && !facts.is_declaration_file()
                                && !facts.is_javascript_file()
                    }) && valid_namespace_export_parent(
                        store,
                        host,
                        declaration,
                        owner,
                        parent,
                    );
                    let local_record = store.symbol(local).ok_or_else(|| {
                        invariant(SourceCallableInvariant::InvalidExportRoute(declaration))
                    })?;
                    if !(source_parent || namespace_parent)
                        || store.get_merged_symbol(parent) != Some(parent)
                        || store.get_merged_symbol(local) != Some(local)
                        || local_record.flags() != SymbolFlags::EXPORT_VALUE
                        || local_record.check_flags() != CheckFlags::NONE
                        || local_record.name().as_bytes() != identifier.text.as_bytes()
                        || local_record.declarations() != Some(&[declaration])
                        || local_record.value_declaration().is_some()
                        || local_record.members().is_some()
                        || local_record.exports().is_some()
                        || local_record.parent().is_some()
                        || local_record.export_symbol() != bound.symbol(declaration)
                    {
                        return Err(invariant(SourceCallableInvariant::InvalidExportRoute(
                            declaration,
                        )));
                    }
                }
                _ => {
                    return Err(invariant(SourceCallableInvariant::InvalidExportRoute(
                        declaration,
                    )));
                }
            }
        }
    }
    Ok(())
}

fn valid_namespace_export_parent(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    declaration: NodeRef,
    owner: &ts_binder::semantic::Symbol,
    parent: SemanticSymbolId,
) -> bool {
    let Some(SourceNodeParent::Parent(block)) = store.source_node_parent(declaration) else {
        return false;
    };
    if store.source_node_kind(block) != Some(SyntaxKind::ModuleBlock) {
        return false;
    }
    let Some(SourceNodeParent::Parent(namespace)) = store.source_node_parent(block) else {
        return false;
    };
    if store.source_node_kind(namespace) != Some(SyntaxKind::ModuleDeclaration)
        || !host.symbol_matches(store, namespace, parent)
    {
        return false;
    }
    let Some(namespace_record) = store.symbol(parent) else {
        return false;
    };
    namespace_record.flags().intersects(SymbolFlags::MODULE)
        && namespace_record.check_flags() == CheckFlags::NONE
        && namespace_record
            .declarations()
            .is_some_and(|declarations| declarations.contains(&namespace))
        && namespace_record
            .exports()
            .and_then(|exports| store.symbol_table(exports))
            .and_then(|exports| exports.get(owner.name()))
            == host
                .bound_file(declaration)
                .and_then(|bound| bound.symbol(declaration))
}

fn validate_optional_token(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    parameter: NodeRef,
    question_token: Option<ts_ast::NodeId>,
    name_end: ts_core::TextPos,
    type_start: ts_core::TextPos,
) -> Result<bool, SourceCallableError> {
    let Some(question_id) = question_token else {
        return Ok(false);
    };
    let question = NodeRef::new(parameter.arena, parameter.file, question_id);
    let record = preflight_node(store, host, question)?;
    if record.kind != SyntaxKind::QuestionToken
        || record.parent != Some(parameter.node)
        || record.range.start < name_end
        || record.range.end > type_start
    {
        return Err(invariant(SourceCallableInvariant::InvalidParameter(
            parameter,
        )));
    }
    Ok(true)
}

fn preflight_child(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    parent: NodeRef,
    child: NodeRef,
) -> Result<(), SourceCallableError> {
    if preflight_node(store, host, child)?.parent != Some(parent.node) {
        return Err(invariant(SourceCallableInvariant::InvalidSyntax(parent)));
    }
    Ok(())
}

fn valid_source_callable_plan_owner(
    store: &CanonicalTypeMapperStore,
    plan: &SourceCallablePlan,
) -> bool {
    let Some(owner) = store.symbol(plan.owner_symbol) else {
        return false;
    };
    if store
        .source_node_kind(plan.declaration)
        .is_none_or(|kind| !plan.family.matches_syntax_kind(kind))
        || store.get_merged_symbol(plan.owner_symbol) != Some(plan.owner_symbol)
        || owner.check_flags() != CheckFlags::NONE
        || owner.members().is_some()
        || owner.export_symbol().is_some()
        || owner.parent() != plan.owner_parent
    {
        return false;
    }

    match plan.family {
        SourceCallableFamily::ArrowFunction => {
            owner.flags() == SymbolFlags::FUNCTION
                && owner.name() == InternalSymbolName::Function.as_ref()
                && owner.declarations() == Some(&[plan.declaration])
                && owner.value_declaration() == Some(plan.declaration)
                && source_arrow_owner_expando_exports_are_valid(
                    store,
                    plan.owner_symbol,
                    plan.declaration,
                )
                && plan.owner_parent.is_none()
                && plan.export_local.is_none()
        }
        SourceCallableFamily::FunctionDeclaration => {
            (valid_source_function_owner_shape(store, plan.owner_symbol, plan.declaration)
                || plan.javascript_duplicate_owner
                    && javascript_duplicate_function_owner_structure(
                        store,
                        plan.owner_symbol,
                        owner,
                        plan.declaration,
                    ))
                && match (plan.owner_parent, plan.export_local) {
                    (None, None) => true,
                    (Some(parent), Some(local)) => {
                        store.get_merged_symbol(parent) == Some(parent)
                            && store.get_merged_symbol(local) == Some(local)
                            && store.symbol(local).is_some_and(|local_record| {
                                local_record.flags() == SymbolFlags::EXPORT_VALUE
                                    && local_record.check_flags() == CheckFlags::NONE
                                    && local_record.name() == owner.name()
                                    && local_record.declarations() == Some(&[plan.declaration])
                                    && local_record.value_declaration().is_none()
                                    && local_record.members().is_none()
                                    && local_record.exports().is_none()
                                    && local_record.parent().is_none()
                                    && local_record.export_symbol() == Some(plan.owner_symbol)
                            })
                    }
                    _ => false,
                }
        }
    }
}

fn valid_inferred_generic_source_callable(
    store: &CanonicalTypeMapperStore,
    plan: &SourceCallablePlan,
) -> bool {
    let exact_parameters = plan.parameters.is_empty() && plan.min_argument_count == 0
        || match (plan.type_parameters.as_slice(), plan.parameters.as_slice()) {
            ([type_parameter], [parameter])
                if plan.min_argument_count == 1
                    && !parameter.optional
                    && !parameter.rest
                    && parameter.initializer.is_none()
                    && parameter.explicit_type_node().is_some() =>
            {
                let Some(constraint) = type_parameter.constraint else {
                    return false;
                };
                let Some(error_type) = store
                    .intrinsic_bootstrap()
                    .map(|bootstrap| bootstrap.error_type)
                else {
                    return false;
                };
                let Some(type_) = store
                    .declared_type_links(type_parameter.symbol)
                    .and_then(|links| links.declared_type)
                else {
                    return false;
                };
                store.source_recovered_unresolved_type_reference_is_exact(constraint, error_type)
                    && source_type_parameter_annotation_links_are_cold_or_fully_warm(
                        store,
                        parameter.identity_node,
                        type_parameter.symbol,
                        type_,
                    )
            }
            _ => false,
        };
    !plan.type_parameters.is_empty()
        && plan.family == SourceCallableFamily::FunctionDeclaration
        && plan.return_type.is_inferred()
        && plan.body_mode == SourceCallableBodyMode::Present
        && exact_parameters
        && plan.flags == SignatureFlags::NONE
        && plan.generic_return_type_parameter_index.is_none()
        && plan.type_parameter_syntax.declaration() == plan.declaration
        && plan.type_parameter_syntax.rows().len() == plan.type_parameters.len()
        && plan.type_parameter_syntax.inferred_empty_body_is_exact()
        && !plan.type_parameter_syntax.generic_fixed_return_is_exact()
        && plan
            .type_parameter_syntax
            .generic_return_type_parameter_declaration()
            .is_none()
        && store.source_node_kind(plan.body) == Some(SyntaxKind::Block)
        && store.source_node_parent(plan.body) == Some(SourceNodeParent::Parent(plan.declaration))
}

/// Validates the cold, barrier, parameter, or resolved state for one plan.
pub(super) fn source_callable_state(
    store: &CanonicalTypeMapperStore,
    plan: &SourceCallablePlan,
    allow_active_barrier: bool,
) -> Result<SourceCallableState, SourceCallableError> {
    if !valid_source_callable_plan_owner(store, plan) {
        return Err(invariant(SourceCallableInvariant::InvalidOwnerSymbol(
            plan.declaration,
        )));
    }
    let owner_links = store.value_symbol_links(plan.owner_symbol);
    let Some(type_) = owner_links.and_then(|links| links.resolved_type) else {
        if owner_links.is_some_and(|links| links != &ValueSymbolLinks::default())
            || !default_signature_links(store, plan.declaration)
            || plan
                .parameters
                .iter()
                .any(|parameter| !default_parameter_links(store, parameter.symbol))
            || store
                .source_callable_type_for_owner(plan.owner_symbol)
                .is_some()
            || store
                .source_callable_type_for_declaration(plan.declaration)
                .is_some()
        {
            return Err(invariant(SourceCallableInvariant::InvalidTypeCache(
                plan.declaration,
            )));
        }
        return Ok(SourceCallableState::Cold);
    };
    if owner_links
        != Some(&ValueSymbolLinks {
            resolved_type: Some(type_),
            ..ValueSymbolLinks::default()
        })
    {
        return Err(invariant(SourceCallableInvariant::InvalidTypeCache(
            plan.declaration,
        )));
    }
    let record = store
        .type_payload(type_)
        .ok_or_else(|| invariant(SourceCallableInvariant::InvalidTypeCache(plan.declaration)))?;
    let TypeData::Object(object) = record.data() else {
        return Err(invariant(SourceCallableInvariant::InvalidTypeCache(
            plan.declaration,
        )));
    };
    let signature = exact_signature_link(store, plan.declaration)?;
    let generic_return_type_parameter = match plan.generic_return_type_parameter_index {
        None => None,
        Some(index) => {
            let planned = plan.type_parameters.get(index).ok_or_else(|| {
                invariant(SourceCallableInvariant::InvalidTypeCache(plan.declaration))
            })?;
            let type_parameter = store
                .declared_type_links(planned.symbol)
                .and_then(|links| links.declared_type)
                .filter(|type_| {
                    cached_ordinary_type_parameter_owner(store, *type_) == Some(planned.symbol)
                })
                .ok_or_else(|| {
                    invariant(SourceCallableInvariant::InvalidTypeCache(plan.declaration))
                })?;
            Some(type_parameter)
        }
    };
    let expected_provenance = SourceCallableProvenance {
        family: plan.family,
        declaration: plan.declaration,
        owner_symbol: plan.owner_symbol,
        owner_parent: plan.owner_parent,
        export_local: plan.export_local,
        signature,
        return_provenance: plan.return_type.provenance(),
        array_targets: plan.array_targets,
        generic_return_type_parameter,
        contextual_target: None,
        contextual_variable: None,
    };
    if record.flags() != TypeFlags::OBJECT
        || record.symbol() != Some(plan.owner_symbol)
        || record.alias().is_some()
        || store.source_callable_provenance(type_) != Some(expected_provenance)
        || store.source_callable_type_for_owner(plan.owner_symbol) != Some(type_)
        || store.source_callable_type_for_signature(signature) != Some(type_)
        || store.source_callable_type_for_declaration(plan.declaration) != Some(type_)
        || object.target.is_some()
        || object.mapper.is_some()
        || object.instantiations != TypeCacheState::Unallocated
    {
        return Err(invariant(SourceCallableInvariant::InvalidTypeCache(
            plan.declaration,
        )));
    }
    validate_signature(store, plan, signature)?;
    let resolved_return_type = store
        .signature(signature)
        .expect("the source signature was validated")
        .resolved_return_type();
    let published_parameter_types = store.callable_signature_parameter_types(signature);
    let is_barrier = record.object_flags()
        == ObjectFlags::ANONYMOUS | ObjectFlags::MEMBERS_RESOLVED
        && object.structured == StructuredTypeData::default();
    if is_barrier {
        if !allow_active_barrier
            || resolved_return_type.is_some()
            || published_parameter_types.is_some()
            || plan
                .parameters
                .iter()
                .any(|parameter| !default_parameter_links(store, parameter.symbol))
        {
            return Err(invariant(SourceCallableInvariant::InvalidTypeCache(
                plan.declaration,
            )));
        }
        return Ok(SourceCallableState::ActiveBarrier { type_, signature });
    }
    let structured = &object.structured;
    if record.object_flags() != ObjectFlags::ANONYMOUS | ObjectFlags::MEMBERS_RESOLVED
        || structured.constrained != ConstrainedTypeData::default()
        || structured.members.is_some()
        || structured.properties.is_some()
        || structured.signatures.as_deref() != Some(&[signature])
        || structured.call_signature_count != 1
        || structured.index_infos.is_some()
        || structured
            .object_type_without_abstract_construct_signatures
            .is_some()
    {
        return Err(invariant(SourceCallableInvariant::InvalidTypeCache(
            plan.declaration,
        )));
    }
    if !plan.parameters.is_empty()
        && plan
            .parameters
            .iter()
            .all(|parameter| default_parameter_links(store, parameter.symbol))
    {
        if !allow_active_barrier
            || resolved_return_type.is_some()
            || published_parameter_types.is_some()
        {
            return Err(invariant(SourceCallableInvariant::InvalidTypeCache(
                plan.declaration,
            )));
        }
        return Ok(SourceCallableState::ActiveParameters { type_, signature });
    }
    let Some(published_parameter_types) = published_parameter_types else {
        return Err(invariant(SourceCallableInvariant::InvalidParameterCache(
            plan.declaration,
        )));
    };
    if published_parameter_types.len() != plan.parameters.len() {
        return Err(invariant(SourceCallableInvariant::InvalidParameterCache(
            plan.declaration,
        )));
    }
    for (parameter, expected) in plan.parameters.iter().zip(published_parameter_types) {
        validate_parameter_links(store, plan, parameter, *expected)?;
    }
    validate_cached_return_type(store, plan, signature)?;
    if plan.return_type.is_inferred() && resolved_return_type.is_none() {
        return Ok(SourceCallableState::AwaitingInferredReturn { type_, signature });
    }
    Ok(SourceCallableState::Resolved { type_, signature })
}

/// Reserves every source-callable record before hoisted construction starts.
pub(super) fn reserve_source_callable_capacities(
    store: &mut CanonicalTypeMapperStore,
    plans: &[&SourceCallablePlan],
) -> Result<(usize, usize), SourceCallableError> {
    let Some(first) = plans.first() else {
        return Ok((0, 0));
    };
    let strict = store
        .intrinsic_bootstrap()
        .ok_or_else(|| invariant(SourceCallableInvariant::Capacity(first.declaration)))?
        .options
        .strict_null_checks;
    let mut cold = 0usize;
    let mut cold_type_parameters = HashSet::new();
    let mut optional_parameter_unions = 0usize;
    let mut owners = HashSet::with_capacity(plans.len());
    let mut declarations = HashSet::with_capacity(plans.len());
    for plan in plans {
        if !owners.insert(plan.owner_symbol) || !declarations.insert(plan.declaration) {
            return Err(invariant(SourceCallableInvariant::InvalidOwnerSymbol(
                plan.declaration,
            )));
        }
        let state = source_callable_state(store, plan, true)?;
        if state == SourceCallableState::Cold {
            cold = cold
                .checked_add(1)
                .ok_or_else(|| invariant(SourceCallableInvariant::Capacity(plan.declaration)))?;
            for type_parameter in &plan.type_parameters {
                if store
                    .declared_type_links(type_parameter.symbol)
                    .and_then(|links| links.declared_type)
                    .is_none()
                {
                    cold_type_parameters.insert(type_parameter.symbol);
                }
            }
        }
        if strict
            && matches!(
                state,
                SourceCallableState::Cold
                    | SourceCallableState::ActiveBarrier { .. }
                    | SourceCallableState::ActiveParameters { .. }
            )
        {
            optional_parameter_unions = optional_parameter_unions
                .checked_add(
                    plan.parameters
                        .iter()
                        .filter(|parameter| parameter.optional || parameter.initializer.is_some())
                        .count(),
                )
                .ok_or_else(|| invariant(SourceCallableInvariant::Capacity(plan.declaration)))?;
        }
    }
    if !store.try_reserve_signatures(cold)
        || !store.try_reserve_source_callable_provenance(cold)
        || !store.try_reserve_function_signature_return_annotations(cold)
        || !store.try_reserve_callable_signature_parameter_types(plans.len())
    {
        return Err(invariant(SourceCallableInvariant::Capacity(
            first.declaration,
        )));
    }
    let source_type_allocations = cold
        .checked_add(cold_type_parameters.len())
        .ok_or_else(|| invariant(SourceCallableInvariant::Capacity(first.declaration)))?;
    Ok((source_type_allocations, optional_parameter_unions))
}

fn jsdoc_intrinsic_type(store: &CanonicalTypeMapperStore, type_: &JsDocType) -> Option<TypeId> {
    let JsDocType::Intrinsic(type_) = type_ else {
        return None;
    };
    let bootstrap = store.intrinsic_bootstrap()?;
    Some(match type_ {
        JsDocIntrinsicType::Any => bootstrap.any_type,
        JsDocIntrinsicType::Unknown => bootstrap.unknown_type,
        JsDocIntrinsicType::Never => bootstrap.never_type,
        JsDocIntrinsicType::Void => bootstrap.void_type,
        JsDocIntrinsicType::Undefined => bootstrap.undefined_type,
        JsDocIntrinsicType::Null => bootstrap.null_type,
        JsDocIntrinsicType::Boolean => bootstrap.boolean_type,
        JsDocIntrinsicType::True => bootstrap.regular_true_type,
        JsDocIntrinsicType::False => bootstrap.regular_false_type,
        JsDocIntrinsicType::Number => bootstrap.number_type,
        JsDocIntrinsicType::String => bootstrap.string_type,
        JsDocIntrinsicType::BigInt => bootstrap.bigint_type,
        JsDocIntrinsicType::Symbol => bootstrap.es_symbol_type,
        JsDocIntrinsicType::Object => bootstrap.non_primitive_type,
    })
}

fn source_jsdoc_function_parameter_annotation(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    declaration: NodeRef,
    parameters: &NodeList,
) -> Result<Option<(NodeRef, PlannedJsDocType)>, SourceCallableError> {
    let [parameter] = parameters.nodes.as_slice() else {
        return Ok(None);
    };
    let parameter = NodeRef::new(declaration.arena, declaration.file, *parameter);
    let record = preflight_node(store, host, parameter)?;
    let NodeData::ParameterDeclaration(parameter_data) = &record.data else {
        return Err(invariant(SourceCallableInvariant::InvalidParameter(
            parameter,
        )));
    };
    if parameter_data.type_.is_some() {
        return Ok(None);
    }
    let name = NodeRef::new(parameter.arena, parameter.file, parameter_data.name);
    let name_record = preflight_node(store, host, name)?;
    let NodeData::Identifier(identifier) = &name_record.data else {
        return Ok(None);
    };
    let (arena, bound) = host
        .source(declaration)
        .ok_or_else(|| invariant(SourceCallableInvariant::InvalidOwnerSymbol(declaration)))?;
    if super::jsdoc::leading_jsdoc_comment(arena, declaration)
        .map_err(|_| invariant(SourceCallableInvariant::InvalidSyntax(declaration)))?
        .is_none()
    {
        return Ok(None);
    }
    let comments = plan_javascript_source_jsdoc(arena, bound.source_file())
        .map_err(|_| invariant(SourceCallableInvariant::InvalidSyntax(declaration)))?;
    let Some(annotation) = comments
        .callable_declaration(arena, declaration)
        .and_then(|callable| callable.parameter(&identifier.text))
        .and_then(super::jsdoc::PlannedJsDocParameter::type_)
    else {
        return Ok(None);
    };
    Ok(matches!(annotation.type_(), JsDocType::Function(_))
        .then(|| (parameter, annotation.clone())))
}

fn source_jsdoc_arrow_parameters_are_exact(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    declaration: NodeRef,
    parameters: &NodeList,
) -> Result<bool, SourceCallableError> {
    let invalid = || invariant(SourceCallableInvariant::InvalidSyntax(declaration));
    let (arena, bound) = host.source(declaration).ok_or_else(invalid)?;
    let comments =
        plan_javascript_source_jsdoc(arena, bound.source_file()).map_err(|_| invalid())?;
    let Some(jsdoc) = comments.callable_declaration(arena, declaration) else {
        return Ok(false);
    };
    if jsdoc.parameters().len() != parameters.nodes.len()
        || !jsdoc.template_parameters().is_empty()
        || jsdoc.type_().is_some()
        || jsdoc.this_type().is_some()
        || jsdoc
            .satisfies()
            .is_none_or(|satisfies| !matches!(satisfies.type_().type_(), JsDocType::Function(_)))
    {
        return Ok(false);
    }

    let mut names = HashSet::with_capacity(parameters.nodes.len());
    for (parameter_id, annotation) in parameters.nodes.iter().zip(jsdoc.parameters()) {
        let parameter = NodeRef::new(declaration.arena, declaration.file, *parameter_id);
        let record = preflight_node(store, host, parameter)?;
        let NodeData::ParameterDeclaration(syntax) = &record.data else {
            return Err(invalid());
        };
        let name = NodeRef::new(declaration.arena, declaration.file, syntax.name);
        let name_record = preflight_node(store, host, name)?;
        let NodeData::Identifier(identifier) = &name_record.data else {
            return Ok(false);
        };
        if record.kind != SyntaxKind::Parameter
            || record.parent != Some(declaration.node)
            || name_record.kind != SyntaxKind::Identifier
            || name_record.parent != Some(parameter.node)
            || syntax.type_.is_some()
            || syntax.initializer.is_some()
            || syntax.question_token.is_some()
            || syntax.dot_dot_dot_token.is_some()
            || annotation.name() != identifier.text.as_str()
            || annotation.type_().is_none()
            || annotation.is_optional()
            || !names.insert(identifier.text.as_str())
        {
            return Ok(false);
        }
    }
    Ok(true)
}

fn hydrate_warm_jsdoc_function_parameter(
    store: &CanonicalTypeMapperStore,
    plan: &mut SourceCallablePlan,
    declaration: NodeRef,
    annotation: &PlannedJsDocType,
) -> Result<(), SourceCallableError> {
    let Some(type_) = store
        .type_node_links(declaration)
        .and_then(|links| links.resolved_type)
    else {
        return Ok(());
    };
    let invalid = || invariant(SourceCallableInvariant::InvalidParameterCache(declaration));
    let JsDocType::Function(function) = annotation.type_() else {
        return Err(invalid());
    };
    let signature = store
        .signature_links(declaration)
        .and_then(|links| links.resolved_signature.signature())
        .and_then(|signature| store.signature(signature))
        .ok_or_else(invalid)?;
    if signature.parameters().len() != function.parameters().len()
        || jsdoc_intrinsic_type(store, function.return_type()) != signature.resolved_return_type()
        || signature
            .parameters()
            .iter()
            .zip(function.parameters())
            .any(|(symbol, parameter)| {
                store
                    .symbol(*symbol)
                    .is_none_or(|record| record.name().as_utf8() != Some(parameter.name()))
                    || parameter
                        .type_()
                        .and_then(|type_| jsdoc_intrinsic_type(store, type_))
                        != store
                            .value_symbol_links(*symbol)
                            .and_then(|links| links.resolved_type)
            })
    {
        return Err(invalid());
    }
    plan.set_jsdoc_function_parameter_type(store, declaration, type_)
}

/// Publishes a JavaScript function whose real parameter owns a `JSDoc` callable type.
pub(super) fn publish_jsdoc_parameterized_source_callable(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    plan: &SourceCallablePlan,
) -> Result<(TypeId, SignatureId), SourceCallableError> {
    let invalid = || invariant(SourceCallableInvariant::Publication(plan.declaration));
    let [parameter] = plan.parameters.as_slice() else {
        return Err(invalid());
    };
    let Some(parameter_type) = parameter.jsdoc_contextual_type else {
        return Err(invalid());
    };
    if plan.family != SourceCallableFamily::FunctionDeclaration
        || plan.body_mode != SourceCallableBodyMode::Present
        || !plan.return_type.is_inferred()
        || !plan.type_parameters.is_empty()
        || plan.flags != SignatureFlags::NONE
        || plan.min_argument_count != 1
        || plan_source_callable(
            store,
            host,
            plan.declaration,
            plan.owner_symbol,
            plan.array_targets,
        )? != *plan
        || !matches!(
            validate_stored_function_type(store, parameter_type),
            StoredFunctionTypeValidation::Valid(_)
        )
    {
        return Err(invalid());
    }

    match source_callable_state(store, plan, true)? {
        SourceCallableState::AwaitingInferredReturn { type_, signature }
        | SourceCallableState::Resolved { type_, signature } => return Ok((type_, signature)),
        SourceCallableState::Cold => {}
        SourceCallableState::ActiveBarrier { .. }
        | SourceCallableState::ActiveParameters { .. } => {
            return Err(invalid());
        }
    }

    reserve_source_callable_capacities(store, &[plan])?;
    if !store.try_reserve_types(1)
        || !store.try_reserve_signature_links(1)
        || !store.try_reserve_value_symbol_links(2)
    {
        return Err(invariant(SourceCallableInvariant::Capacity(
            plan.declaration,
        )));
    }
    let pending = begin_source_callable(store, plan, &[])?
        .map_err(|_| invariant(SourceCallableInvariant::InvalidTypeCache(plan.declaration)))?;
    finalize_source_callable_structure(store, plan, pending)?;
    if !store.set_callable_signature_parameter_types_batch(vec![(
        pending.signature,
        vec![parameter_type],
    )]) || !store.set_value_symbol_links(
        parameter.symbol,
        ValueSymbolLinks {
            resolved_type: Some(parameter_type),
            ..ValueSymbolLinks::default()
        },
    ) {
        return Err(invalid());
    }
    if !matches!(
        source_callable_state(store, plan, false)?,
        SourceCallableState::AwaitingInferredReturn { type_, signature }
            if type_ == pending.type_ && signature == pending.signature
    ) {
        return Err(invalid());
    }
    Ok((pending.type_, pending.signature))
}

fn authenticated_jsdoc_contextual_source_signature(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    plan: &SourceCallablePlan,
    resolved: Option<&ResolvedJsDocSignature>,
) -> Result<Option<(Vec<TypeId>, TypeId)>, SourceCallableError> {
    let invalid = || invariant(SourceCallableInvariant::Publication(plan.declaration));
    if plan.family != SourceCallableFamily::ArrowFunction
        || plan.body_mode != SourceCallableBodyMode::Present
        || !plan.return_type.is_inferred()
        || !plan.type_parameters.is_empty()
        || plan.flags != SignatureFlags::IS_UNTYPED_SIGNATURE_IN_JS_FILE
        || plan.parameters.len() != 1
        || plan.min_argument_count != 1
        || plan.owner_parent.is_some()
        || plan.export_local.is_some()
    {
        return Ok(None);
    }
    let Some((arena, bound)) = host.source(plan.declaration) else {
        return Err(invalid());
    };
    if bound
        .source_facts()
        .is_none_or(|facts| !facts.is_javascript_file())
        || !is_direct_noncontextual_source_arrow(store, host, plan.declaration)?
    {
        return Ok(None);
    }
    let Some(SourceNodeParent::Parent(variable)) = store.source_node_parent(plan.declaration)
    else {
        return Err(invalid());
    };
    let Some(variable_symbol) = bound.symbol(variable) else {
        return Err(invalid());
    };
    if !store.source_contextual_callable_anchor_is_exact(
        plan.declaration,
        plan.owner_symbol,
        variable_symbol,
    ) {
        return Err(invalid());
    }

    let comments = plan_javascript_source_jsdoc(arena, bound.source_file())
        .map_err(|_| invariant(SourceCallableInvariant::InvalidSyntax(plan.declaration)))?;
    let Some(callback) = comments
        .callable_declaration(arena, plan.declaration)
        .and_then(|declaration| declaration.type_())
        .and_then(super::jsdoc::PlannedJsDocType::resolved_callback)
    else {
        return Ok(None);
    };
    let Some(return_type) = callback
        .return_type()
        .and_then(|annotation| jsdoc_intrinsic_type(store, annotation.type_()))
    else {
        return Ok(None);
    };
    let Some(void) = store
        .intrinsic_bootstrap()
        .map(|bootstrap| bootstrap.void_type)
    else {
        return Err(invalid());
    };
    if return_type != void
        || callback.this_type().is_some()
        || !callback.template_parameters().is_empty()
        || callback.parameters().len() != plan.parameters.len()
        || resolved.is_some_and(|signature| {
            signature.parameters().len() != callback.parameters().len()
                || signature.return_type() != Some(return_type)
                || signature.this_type().is_some()
        })
    {
        return Err(invalid());
    }

    let mut parameters = Vec::with_capacity(plan.parameters.len());
    for (index, (parameter, callback_parameter)) in plan
        .parameters
        .iter()
        .zip(callback.parameters())
        .enumerate()
    {
        let Some(type_) = callback_parameter
            .type_()
            .and_then(|annotation| jsdoc_intrinsic_type(store, annotation.type_()))
        else {
            return Err(invalid());
        };
        let record = preflight_node(store, host, parameter.declaration)?;
        let NodeData::ParameterDeclaration(syntax) = &record.data else {
            return Err(invalid());
        };
        let name = NodeRef::new(
            parameter.declaration.arena,
            parameter.declaration.file,
            syntax.name,
        );
        let name_record = preflight_node(store, host, name)?;
        let NodeData::Identifier(identifier) = &name_record.data else {
            return Err(invalid());
        };
        if !parameter.implicit_any
            || parameter.optional
            || parameter.rest
            || parameter.initializer.is_some()
            || callback_parameter.is_optional()
            || identifier.text != callback_parameter.name()
            || parameter
                .jsdoc_contextual_type
                .is_some_and(|existing| existing != type_)
            || resolved.is_some_and(|signature| {
                signature.parameters().get(index).is_none_or(|resolved| {
                    resolved.name() != callback_parameter.name()
                        || resolved.range() != callback_parameter.range()
                        || resolved.type_() != Some(type_)
                        || resolved.is_optional() != callback_parameter.is_optional()
                })
            })
        {
            return Err(invalid());
        }
        parameters.push(type_);
    }
    Ok(Some((parameters, return_type)))
}

fn hydrate_warm_jsdoc_contextual_source_callable(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    plan: &mut SourceCallablePlan,
) -> Result<(), SourceCallableError> {
    let Some(callable) = store.source_callable_type_for_owner(plan.owner_symbol) else {
        return Ok(());
    };
    let Some((parameter_types, return_type)) =
        authenticated_jsdoc_contextual_source_signature(store, host, plan, None)?
    else {
        return Ok(());
    };
    let Some(provenance) = store.source_callable_provenance(callable) else {
        return Err(invariant(SourceCallableInvariant::InvalidTypeCache(
            plan.declaration,
        )));
    };
    let Some(signature) = store.signature(provenance.signature) else {
        return Err(invariant(SourceCallableInvariant::InvalidSignatureCache(
            plan.declaration,
        )));
    };
    if provenance.declaration != plan.declaration
        || provenance.owner_symbol != plan.owner_symbol
        || provenance.contextual_target.is_some()
        || provenance.contextual_variable.is_some()
        || signature.flags() != plan.flags
        || signature.resolved_return_type() != Some(return_type)
        || store.callable_signature_parameter_types(provenance.signature)
            != Some(parameter_types.as_slice())
        || plan
            .parameters
            .iter()
            .zip(&parameter_types)
            .any(|(parameter, expected)| {
                store.value_symbol_links(parameter.symbol)
                    != Some(&ValueSymbolLinks {
                        resolved_type: Some(*expected),
                        ..ValueSymbolLinks::default()
                    })
            })
    {
        return Err(invariant(SourceCallableInvariant::InvalidParameterCache(
            plan.declaration,
        )));
    }
    for (parameter, type_) in plan.parameters.iter_mut().zip(parameter_types) {
        parameter.jsdoc_contextual_type = Some(type_);
    }
    Ok(())
}

/// Publishes a JavaScript arrow from its authenticated local `@callback`.
///
/// The callback exists only in source comments, so its resolved parameter and
/// return types belong directly to the arrow instead of a fabricated target.
pub(super) fn publish_jsdoc_contextual_source_callable(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    plan: &SourceCallablePlan,
    callback: &ResolvedJsDocSignature,
) -> Result<(TypeId, SourceCallablePlan), SourceCallableError> {
    let Some((parameter_types, return_type)) =
        authenticated_jsdoc_contextual_source_signature(store, host, plan, Some(callback))?
    else {
        return Err(invariant(SourceCallableInvariant::Publication(
            plan.declaration,
        )));
    };
    let mut contextual = plan.clone();
    for (parameter, type_) in contextual.parameters.iter_mut().zip(&parameter_types) {
        parameter.jsdoc_contextual_type = Some(*type_);
    }

    match source_callable_state(store, &contextual, true)? {
        SourceCallableState::Resolved { type_, signature }
            if store
                .signature(signature)
                .and_then(Signature::resolved_return_type)
                == Some(return_type)
                && matches!(
                    validate_stored_source_callable(store, type_),
                    StoredSourceCallableValidation::Valid(_)
                ) =>
        {
            return Ok((type_, contextual));
        }
        SourceCallableState::Cold => {}
        _ => {
            return Err(invariant(SourceCallableInvariant::InvalidTypeCache(
                plan.declaration,
            )));
        }
    }

    let missing_signature_links = usize::from(store.signature_links(plan.declaration).is_none());
    let missing_value_links = usize::from(store.value_symbol_links(plan.owner_symbol).is_none())
        + plan
            .parameters
            .iter()
            .filter(|parameter| store.value_symbol_links(parameter.symbol).is_none())
            .count();
    if !store.try_reserve_types(1)
        || !store.try_reserve_signatures(1)
        || !store.try_reserve_source_callable_provenance(1)
        || !store.try_reserve_signature_links(missing_signature_links)
        || !store.try_reserve_value_symbol_links(missing_value_links)
        || !store.try_reserve_callable_signature_parameter_types(1)
    {
        return Err(invariant(SourceCallableInvariant::Capacity(
            plan.declaration,
        )));
    }

    let pending = begin_source_callable(store, &contextual, &[])?
        .map_err(|_| invariant(SourceCallableInvariant::InvalidTypeCache(plan.declaration)))?;
    finalize_source_callable_structure(store, &contextual, pending)?;
    if !store.set_callable_signature_parameter_types_batch(vec![(
        pending.signature,
        parameter_types.clone(),
    )]) {
        return Err(invariant(SourceCallableInvariant::InvalidParameterCache(
            plan.declaration,
        )));
    }
    for (parameter, type_) in contextual.parameters.iter().zip(parameter_types) {
        if !store.set_value_symbol_links(
            parameter.symbol,
            ValueSymbolLinks {
                resolved_type: Some(type_),
                ..ValueSymbolLinks::default()
            },
        ) {
            return Err(invariant(SourceCallableInvariant::InvalidParameterCache(
                parameter.declaration,
            )));
        }
    }
    publish_inferred_source_callable_return(store, &contextual, pending.signature, return_type)?;
    if !matches!(
        validate_stored_source_callable(store, pending.type_),
        StoredSourceCallableValidation::Valid(_)
    ) {
        return Err(invariant(SourceCallableInvariant::Publication(
            plan.declaration,
        )));
    }
    Ok((pending.type_, contextual))
}

/// Publishes or validates one fully prepared contextually typed arrow.
///
/// Unlike annotated source callables, this path has no synthetic type-node
/// annotations to resolve lazily. The contextual target, final parameter
/// value types, and inferred return are all known before the first write,
/// and the arrow expression receives an identity distinct from the retained
/// contextual target type.
pub(super) fn publish_contextual_source_callable(
    store: &mut CanonicalTypeMapperStore,
    prepared: &PreparedContextualSourceCallable,
) -> Result<TypeId, SourceCallableError> {
    publish_prepared_contextual_source_callable(
        store,
        &PreparedContextualSourceCallableView {
            declaration: prepared.declaration,
            owner_symbol: prepared.owner_symbol,
            variable_symbol: Some(prepared.variable_symbol),
            contextual_target: prepared.contextual_target,
            parameters: &prepared.parameters,
            flags: prepared.flags,
            min_argument_count: prepared.min_argument_count,
            return_type: prepared.return_type,
        },
    )
}

/// Publishes a contextually typed direct-call arrow without inventing an anchor.
pub(super) fn publish_contextual_direct_call_source_callable(
    store: &mut CanonicalTypeMapperStore,
    prepared: &PreparedContextualDirectCallSourceCallable,
) -> Result<TypeId, SourceCallableError> {
    publish_prepared_contextual_source_callable(
        store,
        &PreparedContextualSourceCallableView {
            declaration: prepared.declaration,
            owner_symbol: prepared.owner_symbol,
            variable_symbol: None,
            contextual_target: prepared.contextual_target,
            parameters: &prepared.parameters,
            flags: prepared.flags,
            min_argument_count: prepared.min_argument_count,
            return_type: prepared.return_type,
        },
    )
}

fn publish_prepared_contextual_source_callable(
    store: &mut CanonicalTypeMapperStore,
    prepared: &PreparedContextualSourceCallableView<'_>,
) -> Result<TypeId, SourceCallableError> {
    if let Some(existing) = store.source_callable_type_for_owner(prepared.owner_symbol) {
        let provenance = store.source_callable_provenance(existing);
        let signature = provenance.and_then(|provenance| store.signature(provenance.signature));
        let parameter_types = provenance
            .and_then(|provenance| store.callable_signature_parameter_types(provenance.signature));
        let expected_symbols = prepared
            .parameters
            .iter()
            .map(|parameter| parameter.symbol)
            .collect::<Vec<_>>();
        let expected_types = prepared
            .parameters
            .iter()
            .map(|parameter| parameter.type_)
            .collect::<Vec<_>>();
        if matches!(
            validate_stored_source_callable(store, existing),
            StoredSourceCallableValidation::Valid(_)
        ) && provenance.is_some_and(|provenance| {
            provenance.family == SourceCallableFamily::ArrowFunction
                && provenance.declaration == prepared.declaration
                && provenance.owner_symbol == prepared.owner_symbol
                && provenance.owner_parent.is_none()
                && provenance.export_local.is_none()
                && provenance.contextual_target == Some(prepared.contextual_target)
                && provenance.contextual_variable == prepared.variable_symbol
        }) && signature.is_some_and(|signature| {
            signature.flags() == prepared.flags
                && signature.parameters() == expected_symbols
                && signature.min_argument_count() == prepared.min_argument_count
                && signature.resolved_return_type() == Some(prepared.return_type)
        }) && parameter_types == Some(expected_types.as_slice())
        {
            return Ok(existing);
        }
        return Err(invariant(SourceCallableInvariant::InvalidTypeCache(
            prepared.declaration,
        )));
    }

    let parameter_count = prepared.parameters.len();
    let minimum = usize::try_from(prepared.min_argument_count).ok();
    let allowed_flags = SignatureFlags::HAS_REST_PARAMETER;
    let direct_call_anchor = prepared.variable_symbol.is_none();
    let owner = store.symbol(prepared.owner_symbol);
    let owner_valid = owner.is_some_and(|owner| {
        store.source_node_kind(prepared.declaration) == Some(SyntaxKind::ArrowFunction)
            && owner.flags() == SymbolFlags::FUNCTION
            && owner.check_flags() == CheckFlags::NONE
            && owner.name() == InternalSymbolName::Function.as_ref()
            && owner.declarations() == Some(&[prepared.declaration])
            && owner.value_declaration() == Some(prepared.declaration)
            && owner.members().is_none()
            && owner.exports().is_none()
            && owner.parent().is_none()
            && owner.export_symbol().is_none()
            && store.get_merged_symbol(prepared.owner_symbol) == Some(prepared.owner_symbol)
            && default_parameter_links(store, prepared.owner_symbol)
    });
    let anchor_valid = prepared.variable_symbol.map_or_else(
        || {
            stored_direct_call_argument_arrow_is_exact(
                store,
                prepared.declaration,
                prepared.owner_symbol,
            )
        },
        |anchor| {
            store.source_contextual_callable_anchor_is_exact(
                prepared.declaration,
                prepared.owner_symbol,
                anchor,
            )
        },
    );
    let property_anchor = anchor_valid
        && prepared.variable_symbol.is_some_and(|anchor| {
            store
                .symbol(anchor)
                .is_some_and(|symbol| symbol.flags() == SymbolFlags::PROPERTY)
        });
    let target_valid = if direct_call_anchor {
        valid_direct_call_contextual_target(store, prepared.contextual_target, prepared.parameters)
            && prepared.flags == SignatureFlags::NONE
            && usize::try_from(prepared.min_argument_count).ok() == Some(parameter_count)
    } else {
        matches!(
            validate_stored_function_type(store, prepared.contextual_target),
            StoredFunctionTypeValidation::Valid(_)
        )
    };
    let parameters_valid = prepared
        .parameters
        .iter()
        .enumerate()
        .all(|(index, parameter)| {
            !prepared.parameters[..index]
                .iter()
                .any(|previous| previous.symbol == parameter.symbol)
                && parameter.symbol != prepared.owner_symbol
                && store.type_payload(parameter.type_).is_some()
                && store.symbol(parameter.symbol).is_some_and(|symbol| {
                    symbol.flags() == SymbolFlags::FUNCTION_SCOPED_VARIABLE
                        && symbol.check_flags() == CheckFlags::NONE
                        && symbol.declarations() == Some(&[parameter.declaration])
                        && symbol.value_declaration() == Some(parameter.declaration)
                        && symbol.members().is_none()
                        && symbol.exports().is_none()
                        && symbol.parent().is_none()
                        && symbol.export_symbol().is_none()
                        && store.get_merged_symbol(parameter.symbol) == Some(parameter.symbol)
                })
                && store.source_node_kind(parameter.declaration) == Some(SyntaxKind::Parameter)
                && store.source_node_parent(parameter.declaration)
                    == Some(SourceNodeParent::Parent(prepared.declaration))
                && (default_parameter_links(store, parameter.symbol)
                    || (property_anchor || direct_call_anchor)
                        && store.value_symbol_links(parameter.symbol)
                            == Some(&ValueSymbolLinks {
                                resolved_type: Some(parameter.type_),
                                ..ValueSymbolLinks::default()
                            }))
        });
    let rest_valid = !prepared.flags.contains(SignatureFlags::HAS_REST_PARAMETER)
        || prepared.parameters.last().is_some_and(|parameter| {
            store
                .validate_canonical_empty_tuple_type(parameter.type_)
                .is_ok()
        });
    let signature_links_cold = store
        .signature_links(prepared.declaration)
        .is_none_or(|links| links == &SignatureLinks::default());
    if !owner_valid
        || !anchor_valid
        || !target_valid
        || !parameters_valid
        || !rest_valid
        || prepared.flags.bits() & !allowed_flags.bits() != 0
        || minimum.is_none_or(|minimum| minimum > parameter_count)
        || store.type_payload(prepared.contextual_target).is_none()
        || store.type_payload(prepared.return_type).is_none()
        || store
            .source_callable_type_for_declaration(prepared.declaration)
            .is_some()
        || !signature_links_cold
    {
        return Err(invariant(SourceCallableInvariant::Publication(
            prepared.declaration,
        )));
    }
    let Some(bootstrap) = store.intrinsic_bootstrap() else {
        return Err(invariant(SourceCallableInvariant::Publication(
            prepared.declaration,
        )));
    };
    if (!property_anchor && !direct_call_anchor && prepared.return_type != bootstrap.void_type)
        || (property_anchor || direct_call_anchor)
            && store
                .validate_cached_array_capability(prepared.return_type)
                .is_err()
        || !store.try_reserve_types(1)
        || !store.try_reserve_signatures(1)
        || !store.try_reserve_source_callable_provenance(1)
        || !store.try_reserve_callable_signature_parameter_types(1)
    {
        return Err(invariant(SourceCallableInvariant::Capacity(
            prepared.declaration,
        )));
    }

    let type_ = store
        .alloc_plain_object_type(ObjectFlags::ANONYMOUS, Some(prepared.owner_symbol))
        .ok_or_else(|| invariant(SourceCallableInvariant::Publication(prepared.declaration)))?;
    let parameter_symbols = prepared
        .parameters
        .iter()
        .map(|parameter| parameter.symbol)
        .collect::<Vec<_>>();
    let parameter_types = prepared
        .parameters
        .iter()
        .map(|parameter| parameter.type_)
        .collect::<Vec<_>>();
    let signature = store
        .alloc_signature(
            prepared.flags,
            Some(prepared.declaration),
            Vec::new(),
            None,
            parameter_symbols,
            Some(prepared.return_type),
            None,
            prepared.min_argument_count,
        )
        .ok_or_else(|| invariant(SourceCallableInvariant::Publication(prepared.declaration)))?;
    assert!(store.set_source_callable_provenance(
        type_,
        SourceCallableProvenance {
            family: SourceCallableFamily::ArrowFunction,
            declaration: prepared.declaration,
            owner_symbol: prepared.owner_symbol,
            owner_parent: None,
            export_local: None,
            signature,
            return_provenance: SourceCallableReturnProvenance::Inferred,
            array_targets: None,
            generic_return_type_parameter: None,
            contextual_target: Some(prepared.contextual_target),
            contextual_variable: prepared.variable_symbol,
        },
    ));
    assert!(store.set_value_symbol_links(
        prepared.owner_symbol,
        ValueSymbolLinks {
            resolved_type: Some(type_),
            ..ValueSymbolLinks::default()
        },
    ));
    assert!(store.set_structured_type_members(
        type_,
        None,
        None,
        Some(vec![signature]),
        None,
        None,
    ));
    assert!(store.set_signature_links(
        prepared.declaration,
        SignatureLinks {
            resolved_signature: ResolvedSignatureState::Resolved(signature),
            ..SignatureLinks::default()
        },
    ));
    assert!(
        store.set_callable_signature_parameter_types_batch(vec![(signature, parameter_types,)])
    );
    for parameter in prepared.parameters {
        assert!(store.set_value_symbol_links(
            parameter.symbol,
            ValueSymbolLinks {
                resolved_type: Some(parameter.type_),
                ..ValueSymbolLinks::default()
            },
        ));
    }
    if !matches!(
        validate_stored_source_callable(store, type_),
        StoredSourceCallableValidation::Valid(_)
    ) {
        return Err(invariant(SourceCallableInvariant::Publication(
            prepared.declaration,
        )));
    }
    Ok(type_)
}

fn valid_direct_call_contextual_target(
    store: &CanonicalTypeMapperStore,
    target: TypeId,
    parameters: &[ContextualSourceCallableParameter],
) -> bool {
    if parameters.is_empty() {
        return false;
    }
    let StoredSingleCallableValidation::Valid { callable, .. } =
        validate_stored_single_callable(store, target)
    else {
        return false;
    };
    let Some(signature) = store.signature(callable.signature) else {
        return false;
    };
    let Some(source_parameter) = callable.parameters.first().copied() else {
        return false;
    };
    signature.type_parameters().is_empty()
        && !signature.has_rest_parameter()
        && callable.rest_parameter.is_none()
        && (callable.min_argument_count == parameters.len()
            && callable.parameters.len() == parameters.len()
            && callable
                .parameters
                .iter()
                .zip(parameters)
                .all(|(expected, parameter)| *expected == parameter.type_)
            || parameters.len() == 1
                && callable.min_argument_count >= 1
                && super::source_calls::authenticated_array_callback_contextual_target(
                    store,
                    target,
                    source_parameter,
                    parameters[0].type_,
                )
            || parameters.len() == 1
                && callable.min_argument_count == 2
                && matches!(
                    callable.parameters.as_slice(),
                    [first, _] if *first == parameters[0].type_
                )
                && stored_promise_executor_contextual_target_is_exact(store, signature))
}

fn stored_promise_executor_contextual_target_is_exact(
    store: &CanonicalTypeMapperStore,
    signature: &Signature,
) -> bool {
    let Some(annotation) = signature.declaration() else {
        return false;
    };
    let Some(SourceNodeParent::Parent(parameter)) = store.source_node_parent(annotation) else {
        return false;
    };
    let Some(SourceNodeParent::Parent(construction)) = store.source_node_parent(parameter) else {
        return false;
    };
    let Some(owner) = store
        .intrinsic_bootstrap()
        .and_then(|bootstrap| store.symbol_table(bootstrap.globals))
        .and_then(|globals| globals.get_source("PromiseConstructor"))
        .and_then(|symbol| store.get_merged_symbol(symbol))
    else {
        return false;
    };
    store.source_node_kind(annotation) == Some(SyntaxKind::FunctionType)
        && store.source_node_kind(parameter) == Some(SyntaxKind::Parameter)
        && store.source_node_kind(construction) == Some(SyntaxKind::ConstructSignature)
        && store
            .symbol(owner)
            .and_then(|owner| owner.members())
            .and_then(|members| store.symbol_table(members))
            .and_then(|members| members.get(InternalSymbolName::New.as_ref()))
            .and_then(|constructor| store.symbol(constructor))
            .and_then(|constructor| constructor.declarations())
            .is_some_and(|declarations| declarations.contains(&construction))
}

/// Publishes the recursive owner cache and structured empty-member barrier.
pub(super) fn begin_source_callable(
    store: &mut CanonicalTypeMapperStore,
    plan: &SourceCallablePlan,
    resolved_type_parameters: &[ResolvedSourceCallableTypeParameter],
) -> Result<Result<PendingSourceCallable, TypeId>, SourceCallableError> {
    match source_callable_state(store, plan, true)? {
        SourceCallableState::AwaitingInferredReturn { type_, .. }
        | SourceCallableState::Resolved { type_, .. } => return Ok(Err(type_)),
        SourceCallableState::Cold => {}
        SourceCallableState::ActiveBarrier { type_, signature }
        | SourceCallableState::ActiveParameters { type_, signature } => {
            return Ok(Ok(PendingSourceCallable { type_, signature }));
        }
    }
    if plan.type_parameters.len() != resolved_type_parameters.len()
        || plan
            .type_parameters
            .iter()
            .zip(resolved_type_parameters)
            .any(|(planned, resolved)| {
                resolved.provenance.declaration != planned.declaration
                    || resolved.provenance.symbol != planned.symbol
                    || resolved.provenance.constraint != planned.constraint
                    || resolved.provenance.default_type != planned.default_type
            })
    {
        return Err(invariant(SourceCallableInvariant::Publication(
            plan.declaration,
        )));
    }
    if !resolved_type_parameters.is_empty() {
        let return_annotation = plan.return_type.annotation_identity();
        if return_annotation.is_none() && !valid_inferred_generic_source_callable(store, plan) {
            return Err(SourceCallableError::Unsupported(
                SourceCallableUnsupported::GenericInferredReturn(plan.declaration),
            ));
        }
        let return_null_literal_identity =
            return_annotation.is_some_and(|(_, null_literal_identity)| null_literal_identity);
        let (type_, signature) = store
            .publish_source_generic_callable(PreparedSourceGenericCallablePublication {
                syntax: &plan.type_parameter_syntax,
                family: plan.family,
                declaration: plan.declaration,
                owner_symbol: plan.owner_symbol,
                owner_parent: plan.owner_parent,
                export_local: plan.export_local,
                type_parameters: resolved_type_parameters.to_vec(),
                parameters: plan
                    .parameters
                    .iter()
                    .map(|parameter| parameter.symbol)
                    .collect(),
                flags: plan.flags,
                min_argument_count: plan.min_argument_count,
                return_annotation: return_annotation.map(|(annotation, _)| annotation),
                return_null_literal_identity,
                generic_return_type_parameter: plan
                    .generic_return_type_parameter_index
                    .map(|index| resolved_type_parameters[index].provenance.type_parameter),
                array_targets: plan.array_targets,
            })
            .ok_or_else(|| invariant(SourceCallableInvariant::Publication(plan.declaration)))?;
        return Ok(Ok(PendingSourceCallable { type_, signature }));
    }
    let type_ = store
        .alloc_plain_object_type(ObjectFlags::ANONYMOUS, Some(plan.owner_symbol))
        .ok_or_else(|| invariant(SourceCallableInvariant::Publication(plan.declaration)))?;
    let signature = store
        .alloc_signature(
            plan.flags,
            Some(plan.declaration),
            Vec::new(),
            None,
            plan.parameters
                .iter()
                .map(|parameter| parameter.symbol)
                .collect(),
            None,
            None,
            plan.min_argument_count,
        )
        .ok_or_else(|| invariant(SourceCallableInvariant::Publication(plan.declaration)))?;
    let provenance = store.set_source_callable_provenance(
        type_,
        SourceCallableProvenance {
            family: plan.family,
            declaration: plan.declaration,
            owner_symbol: plan.owner_symbol,
            owner_parent: plan.owner_parent,
            export_local: plan.export_local,
            signature,
            return_provenance: plan.return_type.provenance(),
            array_targets: plan.array_targets,
            generic_return_type_parameter: None,
            contextual_target: None,
            contextual_variable: None,
        },
    );
    assert!(
        provenance,
        "source callable provenance was prevalidated and reserved"
    );
    if let Some((return_identity_node, return_null_literal_identity)) =
        plan.return_type.annotation_identity()
    {
        let return_annotation = store.set_function_signature_return_annotation(
            signature,
            return_identity_node,
            return_null_literal_identity,
        );
        assert!(
            return_annotation,
            "source callable return annotation was prevalidated and reserved"
        );
    }
    if !store.set_value_symbol_links(
        plan.owner_symbol,
        ValueSymbolLinks {
            resolved_type: Some(type_),
            ..ValueSymbolLinks::default()
        },
    ) || !store.set_structured_type_members(type_, None, None, None, None, None)
        || !store.set_signature_links(
            plan.declaration,
            SignatureLinks {
                resolved_signature: ResolvedSignatureState::Resolved(signature),
                ..SignatureLinks::default()
            },
        )
    {
        return Err(invariant(SourceCallableInvariant::Publication(
            plan.declaration,
        )));
    }
    Ok(Ok(PendingSourceCallable { type_, signature }))
}

/// Installs the exact source-function call surface: nil members/properties and
/// one direct call signature.
pub(super) fn finalize_source_callable_structure(
    store: &mut CanonicalTypeMapperStore,
    plan: &SourceCallablePlan,
    pending: PendingSourceCallable,
) -> Result<(), SourceCallableError> {
    match source_callable_state(store, plan, true)? {
        SourceCallableState::ActiveBarrier { type_, signature }
            if type_ == pending.type_ && signature == pending.signature => {}
        SourceCallableState::ActiveParameters { type_, signature }
            if type_ == pending.type_ && signature == pending.signature =>
        {
            return Ok(());
        }
        _ => {
            return Err(invariant(SourceCallableInvariant::Publication(
                plan.declaration,
            )));
        }
    }
    if !store.set_structured_type_members(
        pending.type_,
        None,
        None,
        Some(vec![pending.signature]),
        None,
        None,
    ) {
        return Err(invariant(SourceCallableInvariant::Publication(
            plan.declaration,
        )));
    }
    if plan.parameters.is_empty() {
        let published = store
            .set_callable_signature_parameter_types_batch(vec![(pending.signature, Vec::new())]);
        assert!(
            published,
            "zero-parameter source callable provenance was prevalidated and reserved"
        );
        if plan.return_type.is_ambient_implicit_any() {
            publish_ambient_implicit_any_return(store, plan, pending.signature)?;
        }
    }
    Ok(())
}

/// Publishes an authenticated zero-parameter anonymous function expression.
pub(super) fn materialize_anonymous_source_function_expression(
    store: &mut CanonicalTypeMapperStore,
    plan: &SourceCallablePlan,
) -> Result<(TypeId, SignatureId), SourceCallableError> {
    if plan.family != SourceCallableFamily::ArrowFunction
        || store.source_node_kind(plan.declaration) != Some(SyntaxKind::FunctionExpression)
        || !plan.parameters.is_empty()
        || !plan.type_parameters.is_empty()
        || !plan.return_type.is_inferred()
        || plan.body_mode != SourceCallableBodyMode::Present
        || plan.is_async
        || plan.flags != SignatureFlags::NONE
        || plan.min_argument_count != 0
        || plan.owner_parent.is_some()
        || plan.export_local.is_some()
        || store
            .symbol(plan.owner_symbol)
            .is_none_or(|owner| owner.exports().is_some())
    {
        return Err(invariant(SourceCallableInvariant::InvalidOwnerSymbol(
            plan.declaration,
        )));
    }

    match source_callable_state(store, plan, true)? {
        SourceCallableState::AwaitingInferredReturn { type_, signature }
        | SourceCallableState::Resolved { type_, signature } => Ok((type_, signature)),
        SourceCallableState::Cold => {
            let (type_count, optional_unions) = reserve_source_callable_capacities(store, &[plan])?;
            if type_count != 1 || optional_unions != 0 || !store.try_reserve_types(type_count) {
                return Err(invariant(SourceCallableInvariant::Capacity(
                    plan.declaration,
                )));
            }
            let Ok(pending) = begin_source_callable(store, plan, &[])? else {
                return Err(invariant(SourceCallableInvariant::Publication(
                    plan.declaration,
                )));
            };
            finalize_source_callable_structure(store, plan, pending)?;
            Ok((pending.type_, pending.signature))
        }
        SourceCallableState::ActiveBarrier { .. }
        | SourceCallableState::ActiveParameters { .. } => Err(invariant(
            SourceCallableInvariant::InvalidTypeCache(plan.declaration),
        )),
    }
}

/// Publishes the canonical `any` return of a bodyless declaration signature.
fn publish_ambient_implicit_any_return(
    store: &mut CanonicalTypeMapperStore,
    plan: &SourceCallablePlan,
    signature: SignatureId,
) -> Result<TypeId, SourceCallableError> {
    let Some(any_type) = store
        .intrinsic_bootstrap()
        .map(|bootstrap| bootstrap.any_type)
    else {
        return Err(invariant(SourceCallableInvariant::InvalidSignatureCache(
            plan.declaration,
        )));
    };
    let Some(record) = store.signature(signature) else {
        return Err(invariant(SourceCallableInvariant::InvalidSignatureCache(
            plan.declaration,
        )));
    };
    if !plan.return_type.is_ambient_implicit_any()
        || !plan.body_mode.is_ambient()
        || !plan.type_parameters.is_empty()
        || record.declaration() != Some(plan.declaration)
        || record
            .resolved_return_type()
            .is_some_and(|existing| existing != any_type)
        || store
            .function_signature_return_annotation(signature)
            .is_some()
        || store.signature_has_circular_return_type(signature)
    {
        return Err(invariant(SourceCallableInvariant::InvalidSignatureCache(
            plan.declaration,
        )));
    }
    if record.resolved_return_type().is_none()
        && !store.set_signature_resolved_return_type(signature, Some(any_type))
    {
        return Err(invariant(SourceCallableInvariant::InvalidSignatureCache(
            plan.declaration,
        )));
    }
    Ok(any_type)
}

/// Atomically publishes all parameter value types for a prevalidated batch.
pub(super) fn publish_source_callable_parameter_types(
    store: &mut CanonicalTypeMapperStore,
    global_types: Option<&CanonicalGlobalTypes>,
    pending: &[PendingSourceCallableParameterTypes],
    prepared: &mut PreparedTypeQueryTypes,
) -> Result<(), SourceCallableError> {
    let Some(first) = pending.first() else {
        return Ok(());
    };
    let strict = store
        .intrinsic_bootstrap()
        .ok_or_else(|| invariant(SourceCallableInvariant::Publication(first.plan.declaration)))?
        .options
        .strict_null_checks;
    let undefined = store
        .intrinsic_bootstrap()
        .expect("bootstrap was checked above")
        .undefined_type;
    let parameter_count = pending.iter().try_fold(0usize, |count, callable| {
        count
            .checked_add(callable.plan.parameters.len())
            .ok_or_else(|| invariant(SourceCallableInvariant::Capacity(callable.plan.declaration)))
    })?;
    let mut owners = HashSet::with_capacity(pending.len());
    let mut declarations = HashSet::with_capacity(pending.len());
    let mut signatures = HashSet::with_capacity(pending.len());
    let mut parameter_symbols = HashSet::with_capacity(parameter_count);
    for callable in pending {
        if callable.base_types.len() != callable.plan.parameters.len() {
            return Err(invariant(SourceCallableInvariant::Publication(
                callable.plan.declaration,
            )));
        }
        let SourceCallableState::ActiveParameters { signature, .. } =
            source_callable_state(store, &callable.plan, true)?
        else {
            return Err(invariant(SourceCallableInvariant::Publication(
                callable.plan.declaration,
            )));
        };
        if !owners.insert(callable.plan.owner_symbol)
            || !declarations.insert(callable.plan.declaration)
            || !signatures.insert(signature)
        {
            return Err(invariant(SourceCallableInvariant::InvalidOwnerSymbol(
                callable.plan.declaration,
            )));
        }
        let generic_type_parameters = if callable.plan.type_parameters.is_empty() {
            None
        } else {
            Some(
                planned_type_parameter_ids(store, &callable.plan).ok_or_else(|| {
                    invariant(SourceCallableInvariant::Publication(
                        callable.plan.declaration,
                    ))
                })?,
            )
        };
        for (parameter, base) in callable.plan.parameters.iter().zip(&callable.base_types) {
            if !parameter_symbols.insert(parameter.symbol) {
                return Err(invariant(SourceCallableInvariant::InvalidParameterSymbol(
                    parameter.declaration,
                )));
            }
            if store.type_payload(*base).is_none()
                || !default_parameter_links(store, parameter.symbol)
            {
                return Err(invariant(SourceCallableInvariant::Publication(
                    parameter.declaration,
                )));
            }
            let cached = parameter.base_type(store).ok_or_else(|| {
                invariant(SourceCallableInvariant::InvalidParameterCache(
                    parameter.declaration,
                ))
            })?;
            let supplied_base = if parameter.is_implicit_any() && parameter.rest {
                store
                    .intrinsic_bootstrap()
                    .map(|bootstrap| bootstrap.any_type)
                    .filter(|any| *base == *any)
                    .map(|_| cached)
                    .ok_or_else(|| {
                        invariant(SourceCallableInvariant::InvalidParameterCache(
                            parameter.declaration,
                        ))
                    })?
            } else {
                *base
            };
            if cached != supplied_base
                || store
                    .validate_cached_array_capability_prepared(
                        supplied_base,
                        global_types,
                        prepared,
                    )
                    .is_err()
                || generic_type_parameters
                    .as_ref()
                    .is_some_and(|type_parameters| {
                        !(valid_generic_source_parameter_type(
                            store,
                            callable.plan.array_targets,
                            supplied_base,
                            type_parameters,
                        ) || !parameter.rest
                            && valid_fixed_generic_source_parameter_type(store, supplied_base)
                            || callable.plan.family == SourceCallableFamily::ArrowFunction
                                && valid_optional_generic_source_parameter_type(
                                    store,
                                    callable.plan.array_targets,
                                    supplied_base,
                                    type_parameters,
                                ))
                    })
            {
                return Err(invariant(SourceCallableInvariant::InvalidParameterCache(
                    parameter.declaration,
                )));
            }
        }
    }
    let mut resolved = Vec::with_capacity(parameter_count);
    let mut expected_parameter_types = Vec::with_capacity(pending.len());
    for callable in pending {
        let signature = exact_signature_link(store, callable.plan.declaration)?;
        let mut callable_parameter_types = Vec::with_capacity(callable.plan.parameters.len());
        for (parameter, base) in callable.plan.parameters.iter().zip(&callable.base_types) {
            let base = if parameter.is_implicit_any() && parameter.rest {
                parameter.base_type(store).ok_or_else(|| {
                    invariant(SourceCallableInvariant::InvalidParameterCache(
                        parameter.declaration,
                    ))
                })?
            } else {
                *base
            };
            let call_type = if strict && (parameter.optional || parameter.initializer.is_some()) {
                let already_contains_undefined = base == undefined
                    || store.type_payload(base).is_some_and(|record| {
                        matches!(
                            record.data(),
                            TypeData::Union(union) if union.union.types.contains(&undefined)
                        )
                    });
                if already_contains_undefined {
                    base
                } else {
                    match global_types {
                        Some(global_types) => store.literal_union_type_prepared_with_global_types(
                            global_types,
                            &[base, undefined],
                            None,
                            prepared,
                        )?,
                        None => {
                            store.literal_union_type_prepared(&[base, undefined], None, prepared)?
                        }
                    }
                }
            } else {
                base
            };
            if store
                .validate_cached_array_capability_prepared(call_type, global_types, prepared)
                .is_err()
            {
                return Err(invariant(SourceCallableInvariant::InvalidParameterCache(
                    parameter.declaration,
                )));
            }
            let value_type = if parameter.initializer.is_some() {
                base
            } else {
                call_type
            };
            resolved.push((parameter.symbol, value_type));
            callable_parameter_types.push(call_type);
        }
        expected_parameter_types.push((signature, callable_parameter_types));
    }
    let provenance = store.set_callable_signature_parameter_types_batch(expected_parameter_types);
    assert!(
        provenance,
        "prevalidated source parameter provenance publication is infallible"
    );
    for (symbol, type_) in resolved {
        let published = store.set_value_symbol_links(
            symbol,
            ValueSymbolLinks {
                resolved_type: Some(type_),
                ..ValueSymbolLinks::default()
            },
        );
        assert!(
            published,
            "prevalidated source callable parameter publication is infallible"
        );
    }
    for callable in pending {
        if callable.plan.return_type.is_ambient_implicit_any() {
            let signature = exact_signature_link(store, callable.plan.declaration)?;
            publish_ambient_implicit_any_return(store, &callable.plan, signature)?;
        }
    }
    for callable in pending {
        let state = source_callable_state(store, &callable.plan, false);
        assert!(
            matches!(
                state,
                Ok(SourceCallableState::AwaitingInferredReturn { .. }
                    | SourceCallableState::Resolved { .. })
            ),
            "prevalidated source callable batch must publish resolved caches"
        );
        let (type_, awaiting_inferred_return) = match state {
            Ok(SourceCallableState::AwaitingInferredReturn { type_, .. }) => (type_, true),
            Ok(SourceCallableState::Resolved { type_, .. }) => (type_, false),
            _ => unreachable!(),
        };
        if awaiting_inferred_return {
            assert_eq!(
                validate_stored_source_callable(store, type_),
                StoredSourceCallableValidation::Pending,
                "inferred source callable must remain explicitly pending until its body is checked"
            );
            continue;
        }
        let capability = match callable.plan.array_targets {
            Some(targets) => {
                store.validate_cached_array_capability_with_array_targets(targets, type_)
            }
            None => store.validate_cached_array_capability(type_),
        };
        assert!(
            capability.is_ok(),
            "source callable edges were prevalidated under the same capability"
        );
    }
    Ok(())
}

pub(super) fn validate_source_callable_signature_identity(
    store: &CanonicalTypeMapperStore,
    plan: &SourceCallablePlan,
    signature: SignatureId,
) -> Result<(), SourceCallableError> {
    let matches = match source_callable_state(store, plan, true)? {
        SourceCallableState::ActiveBarrier {
            signature: cached, ..
        }
        | SourceCallableState::ActiveParameters {
            signature: cached, ..
        }
        | SourceCallableState::AwaitingInferredReturn {
            signature: cached, ..
        }
        | SourceCallableState::Resolved {
            signature: cached, ..
        } => cached == signature,
        SourceCallableState::Cold => false,
    };
    if !matches {
        return Err(invariant(SourceCallableInvariant::InvalidSignatureCache(
            plan.declaration,
        )));
    }
    Ok(())
}

pub(super) fn validate_lazy_source_callable_return(
    store: &CanonicalTypeMapperStore,
    plan: &SourceCallablePlan,
    signature: SignatureId,
) -> Result<Option<TypeId>, SourceCallableError> {
    if plan.return_type.annotation_identity().is_none()
        && !plan.return_type.is_ambient_implicit_any()
    {
        return Err(invariant(SourceCallableInvariant::InvalidSignatureCache(
            plan.declaration,
        )));
    }
    match source_callable_state(store, plan, false)? {
        SourceCallableState::Resolved {
            signature: cached, ..
        } if cached == signature => {}
        _ => {
            return Err(invariant(SourceCallableInvariant::InvalidSignatureCache(
                plan.declaration,
            )));
        }
    }
    let resolved = store
        .signature(signature)
        .expect("the source callable cache was validated")
        .resolved_return_type();
    if plan.return_type.is_ambient_implicit_any()
        && store
            .intrinsic_bootstrap()
            .is_none_or(|bootstrap| resolved != Some(bootstrap.any_type))
    {
        return Err(invariant(SourceCallableInvariant::InvalidSignatureCache(
            plan.declaration,
        )));
    }
    Ok(resolved)
}

pub(super) fn publish_lazy_source_callable_return(
    store: &mut CanonicalTypeMapperStore,
    plan: &SourceCallablePlan,
    signature: SignatureId,
    return_type: TypeId,
) -> Result<TypeId, SourceCallableError> {
    let Some((return_identity_node, return_null_literal_identity)) =
        plan.return_type.annotation_identity()
    else {
        return Err(invariant(SourceCallableInvariant::InvalidSignatureCache(
            plan.declaration,
        )));
    };
    let annotation =
        cached_annotation_identity(store, return_identity_node, return_null_literal_identity);
    if store.type_payload(return_type).is_none()
        || store.signature_has_circular_return_type(signature)
        || validate_lazy_source_callable_return(store, plan, signature)?.is_some()
        || annotation != Some(return_type)
        || !plan.type_parameters.is_empty()
            && !planned_type_parameter_ids(store, plan).is_some_and(|type_parameters| {
                valid_source_generic_mapper_type(
                    store,
                    return_type,
                    &type_parameters,
                    plan.array_targets,
                ) && valid_stored_source_generic_return_annotation(
                    store,
                    return_identity_node,
                    return_null_literal_identity,
                    return_type,
                    plan.generic_return_type_parameter_index
                        .and_then(|index| type_parameters.get(index).copied()),
                    &type_parameters,
                    plan.array_targets,
                )
            })
    {
        return Err(invariant(SourceCallableInvariant::InvalidSignatureCache(
            plan.declaration,
        )));
    }
    let published = store.set_signature_resolved_return_type(signature, Some(return_type));
    assert!(published, "lazy source return publication was prevalidated");
    validate_cached_return_type(store, plan, signature)?;
    Ok(return_type)
}

pub(super) fn publish_circular_lazy_source_callable_return(
    store: &mut CanonicalTypeMapperStore,
    plan: &SourceCallablePlan,
    signature: SignatureId,
    annotation_type: TypeId,
) -> Result<TypeId, SourceCallableError> {
    let Some((return_identity_node, return_null_literal_identity)) =
        plan.return_type.annotation_identity()
    else {
        return Err(invariant(SourceCallableInvariant::InvalidSignatureCache(
            plan.declaration,
        )));
    };
    let Some(bootstrap) = store.intrinsic_bootstrap() else {
        return Err(invariant(SourceCallableInvariant::InvalidSignatureCache(
            plan.declaration,
        )));
    };
    let any_type = bootstrap.any_type;
    let annotation =
        cached_annotation_identity(store, return_identity_node, return_null_literal_identity);
    if store.type_payload(annotation_type).is_none()
        || !plan.type_parameters.is_empty()
        || store.signature_has_circular_return_type(signature)
        || validate_lazy_source_callable_return(store, plan, signature)?.is_some()
        || annotation != Some(annotation_type)
    {
        return Err(invariant(SourceCallableInvariant::InvalidSignatureCache(
            plan.declaration,
        )));
    }
    let published =
        store.set_function_signature_circular_return_type(signature, any_type, annotation_type);
    assert!(
        published,
        "circular lazy source return publication was prevalidated"
    );
    validate_cached_return_type(store, plan, signature)?;
    Ok(any_type)
}

/// Validates the final body-inferred return without consulting annotation
/// syntax. `None` is the exact warmable state after the callable shell and
/// parameter identities have been published.
pub(super) fn validate_inferred_source_callable_return(
    store: &CanonicalTypeMapperStore,
    plan: &SourceCallablePlan,
    signature: SignatureId,
) -> Result<Option<TypeId>, SourceCallableError> {
    if !plan.return_type.is_inferred()
        || !plan.type_parameters.is_empty() && !valid_inferred_generic_source_callable(store, plan)
    {
        return Err(invariant(SourceCallableInvariant::InvalidSignatureCache(
            plan.declaration,
        )));
    }
    match source_callable_state(store, plan, false)? {
        SourceCallableState::AwaitingInferredReturn {
            signature: cached, ..
        }
        | SourceCallableState::Resolved {
            signature: cached, ..
        } if cached == signature => {}
        _ => {
            return Err(invariant(SourceCallableInvariant::InvalidSignatureCache(
                plan.declaration,
            )));
        }
    }
    Ok(store
        .signature(signature)
        .expect("the inferred source callable cache was validated")
        .resolved_return_type())
}

/// Proves the untouched interface shell retained for inherited global JSX.Element.
fn canonical_lazy_global_jsx_element_return(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
) -> bool {
    let Some(bootstrap) = store.intrinsic_bootstrap() else {
        return false;
    };
    let Some(namespace) = store
        .symbol_table(bootstrap.globals)
        .and_then(|globals| globals.get_source("JSX"))
        .and_then(|symbol| store.get_merged_symbol(symbol))
    else {
        return false;
    };
    let Some(namespace_record) = store.symbol(namespace) else {
        return false;
    };
    let Some(namespace_declarations) = namespace_record.declarations() else {
        return false;
    };
    let Some(element) = namespace_record
        .exports()
        .and_then(|exports| store.symbol_table(exports))
        .and_then(|exports| exports.get_source("Element"))
        .and_then(|symbol| store.get_merged_symbol(symbol))
    else {
        return false;
    };
    let Some(element_record) = store.symbol(element) else {
        return false;
    };
    let Some(declarations) = element_record.declarations() else {
        return false;
    };
    let Some(record) = store.type_payload(type_) else {
        return false;
    };
    let TypeData::Interface(interface) = record.data() else {
        return false;
    };
    let namespace_parent_valid = namespace_record.parent().is_none_or(|parent| {
        let Some(parent_record) = store.symbol(parent) else {
            return false;
        };
        let Some(parent_declarations) = parent_record.declarations() else {
            return false;
        };
        parent_record.flags().intersects(SymbolFlags::MODULE)
            && parent_record.check_flags() == CheckFlags::NONE
            && parent_record.name() == InternalSymbolName::Global.as_ref()
            && parent_record.export_symbol().is_none()
            && store.get_merged_symbol(parent) == Some(parent)
            && parent_record
                .exports()
                .and_then(|exports| store.symbol_table(exports))
                .and_then(|exports| exports.get_source("JSX"))
                .and_then(|export| store.get_merged_symbol(export))
                == Some(namespace)
            && !parent_declarations.is_empty()
            && namespace_declarations.iter().all(|declaration| {
                let Some(SourceNodeParent::Parent(block)) = store.source_node_parent(*declaration)
                else {
                    return false;
                };
                let Some(SourceNodeParent::Parent(global)) = store.source_node_parent(block) else {
                    return false;
                };
                store.source_node_kind(block) == Some(SyntaxKind::ModuleBlock)
                    && store.source_node_kind(global) == Some(SyntaxKind::ModuleDeclaration)
                    && parent_declarations.contains(&global)
            })
    });
    namespace_record.flags().intersects(SymbolFlags::NAMESPACE)
        && namespace_record.check_flags() == CheckFlags::NONE
        && namespace_record.name().as_bytes() == b"JSX"
        && namespace_parent_valid
        && namespace_record.export_symbol().is_none()
        && !namespace_declarations.is_empty()
        && namespace_declarations.iter().all(|declaration| {
            store.source_node_kind(*declaration) == Some(SyntaxKind::ModuleDeclaration)
        })
        && element_record.flags() == SymbolFlags::INTERFACE
        && element_record.check_flags() == CheckFlags::NONE
        && element_record.name().as_bytes() == b"Element"
        && element_record.parent() == Some(namespace)
        && element_record.value_declaration().is_none()
        && element_record.members().is_none()
        && element_record.exports().is_none()
        && element_record.export_symbol().is_none()
        && store.get_merged_symbol(element) == Some(element)
        && !declarations.is_empty()
        && declarations.iter().all(|declaration| {
            if store.source_node_kind(*declaration) != Some(SyntaxKind::InterfaceDeclaration) {
                return false;
            }
            let Some(SourceNodeParent::Parent(block)) = store.source_node_parent(*declaration)
            else {
                return false;
            };
            let Some(SourceNodeParent::Parent(module)) = store.source_node_parent(block) else {
                return false;
            };
            store.source_node_kind(block) == Some(SyntaxKind::ModuleBlock)
                && store.source_node_kind(module) == Some(SyntaxKind::ModuleDeclaration)
                && namespace_declarations.contains(&module)
        })
        && record.flags() == TypeFlags::OBJECT
        && record.object_flags() == ObjectFlags::INTERFACE
        && record.symbol() == Some(element)
        && record.alias().is_none()
        && interface == &InterfaceTypeData::default()
        && store.declared_type_links(element)
            == Some(&DeclaredTypeLinks {
                declared_type: Some(type_),
                ..DeclaredTypeLinks::default()
            })
        && store.direct_interface_heritage_provenance(type_).is_none()
}

fn valid_inferred_source_callable_return_capability(
    store: &CanonicalTypeMapperStore,
    array_targets: Option<CanonicalArrayTargets>,
    type_: TypeId,
) -> bool {
    canonical_lazy_global_jsx_element_return(store, type_)
        || super::enums::is_canonical_enum_union(store, type_)
        || match array_targets {
            Some(targets) => store
                .validate_cached_array_capability_with_array_targets(targets, type_)
                .is_ok(),
            None => store.validate_cached_array_capability(type_).is_ok(),
        }
}

/// Atomically publishes a checked and widened inferred return. A warm replay
/// accepts the exact existing identity and rejects every conflicting write.
pub(super) fn publish_inferred_source_callable_return(
    store: &mut CanonicalTypeMapperStore,
    plan: &SourceCallablePlan,
    signature: SignatureId,
    return_type: TypeId,
) -> Result<TypeId, SourceCallableError> {
    if let Some(existing) = validate_inferred_source_callable_return(store, plan, signature)? {
        return if existing == return_type {
            Ok(existing)
        } else {
            Err(invariant(SourceCallableInvariant::InvalidSignatureCache(
                plan.declaration,
            )))
        };
    }
    let capability_valid =
        valid_inferred_source_callable_return_capability(store, plan.array_targets, return_type);
    if !capability_valid
        || !plan.type_parameters.is_empty()
            && store
                .intrinsic_bootstrap()
                .is_none_or(|bootstrap| return_type != bootstrap.void_type)
        || store
            .function_signature_return_annotation(signature)
            .is_some()
        || store.signature_has_circular_return_type(signature)
    {
        return Err(invariant(SourceCallableInvariant::InvalidSignatureCache(
            plan.declaration,
        )));
    }
    let published = store.set_signature_resolved_return_type(signature, Some(return_type));
    assert!(
        published,
        "inferred source return publication was prevalidated"
    );
    match source_callable_state(store, plan, false)? {
        SourceCallableState::Resolved {
            signature: cached, ..
        } if cached == signature => Ok(return_type),
        _ => Err(invariant(SourceCallableInvariant::InvalidSignatureCache(
            plan.declaration,
        ))),
    }
}

pub(super) fn source_callable_display_projection(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    type_: TypeId,
    array_targets: Option<CanonicalArrayTargets>,
) -> Result<ValidatedSingleCallSignatureDisplay, SourceCallableDisplayError> {
    let provenance = store
        .source_callable_provenance(type_)
        .ok_or(SourceCallableDisplayError::Malformed)?;
    if provenance.contextual_target.is_some() {
        if !matches!(
            validate_stored_source_callable(store, type_),
            StoredSourceCallableValidation::Valid(_)
        ) {
            return Err(SourceCallableDisplayError::Malformed);
        }
        let signature = store
            .signature(provenance.signature)
            .ok_or(SourceCallableDisplayError::Malformed)?;
        let expected_types = store
            .callable_signature_parameter_types(provenance.signature)
            .ok_or(SourceCallableDisplayError::Malformed)?;
        if expected_types.len() != signature.parameters().len() {
            return Err(SourceCallableDisplayError::Malformed);
        }
        let mut parameters = Vec::with_capacity(signature.parameters().len());
        for (parameter, value_type) in signature.parameters().iter().zip(expected_types) {
            let declaration = store
                .symbol(*parameter)
                .and_then(ts_binder::semantic::Symbol::value_declaration)
                .ok_or(SourceCallableDisplayError::Malformed)?;
            let parameter_node = host
                .node(declaration)
                .ok_or(SourceCallableDisplayError::Malformed)?;
            let NodeData::ParameterDeclaration(parameter_data) = &parameter_node.data else {
                return Err(SourceCallableDisplayError::Malformed);
            };
            if parameter_data.dot_dot_dot_token.is_some() {
                store
                    .validate_canonical_empty_tuple_type(*value_type)
                    .map_err(|_| SourceCallableDisplayError::Malformed)?;
                continue;
            }
            let name = NodeRef::new(declaration.arena, declaration.file, parameter_data.name);
            let name_node = host
                .node(name)
                .ok_or(SourceCallableDisplayError::Malformed)?;
            let NodeData::Identifier(identifier) = &name_node.data else {
                return Err(SourceCallableDisplayError::Malformed);
            };
            parameters.push(ValidatedSingleCallParameterDisplay {
                name: identifier.text.clone(),
                value_type: *value_type,
                optional: parameter_data.question_token.is_some(),
            });
        }
        return Ok(ValidatedSingleCallSignatureDisplay {
            owner: type_,
            parameters,
            return_type: signature.resolved_return_type(),
        });
    }
    let plan = plan_source_callable(
        store,
        host,
        provenance.declaration,
        provenance.owner_symbol,
        array_targets,
    )
    .map_err(source_callable_display_error)?;
    if !plan.type_parameters.is_empty() {
        return Err(SourceCallableDisplayError::Unsupported(
            SourceCallableUnsupported::GenericSignature(plan.declaration),
        ));
    }
    let signature =
        match source_callable_state(store, &plan, true).map_err(source_callable_display_error)? {
            SourceCallableState::Resolved {
                type_: resolved,
                signature,
            } if resolved == type_ && signature == provenance.signature => signature,
            SourceCallableState::ActiveBarrier { .. }
            | SourceCallableState::ActiveParameters { .. }
            | SourceCallableState::AwaitingInferredReturn { .. } => {
                return Err(SourceCallableDisplayError::Pending);
            }
            SourceCallableState::Cold | SourceCallableState::Resolved { .. } => {
                return Err(SourceCallableDisplayError::Malformed);
            }
        };
    let return_type = store
        .signature(signature)
        .ok_or(SourceCallableDisplayError::Malformed)?
        .resolved_return_type();
    let mut parameters = Vec::with_capacity(plan.parameters.len());
    for parameter in &plan.parameters {
        let value_type = store
            .value_symbol_links(parameter.symbol)
            .and_then(|links| links.resolved_type)
            .ok_or(SourceCallableDisplayError::Malformed)?;
        let parameter_node = host
            .node(parameter.declaration)
            .ok_or(SourceCallableDisplayError::Malformed)?;
        let NodeData::ParameterDeclaration(parameter_data) = &parameter_node.data else {
            return Err(SourceCallableDisplayError::Malformed);
        };
        let name = NodeRef::new(
            parameter.declaration.arena,
            parameter.declaration.file,
            parameter_data.name,
        );
        let name_node = host
            .node(name)
            .ok_or(SourceCallableDisplayError::Malformed)?;
        let NodeData::Identifier(identifier) = &name_node.data else {
            return Err(SourceCallableDisplayError::Malformed);
        };
        parameters.push(ValidatedSingleCallParameterDisplay {
            name: identifier.text.clone(),
            value_type,
            optional: parameter.optional || parameter.initializer.is_some(),
        });
    }
    Ok(ValidatedSingleCallSignatureDisplay {
        owner: type_,
        parameters,
        return_type,
    })
}

const fn source_callable_display_error(error: SourceCallableError) -> SourceCallableDisplayError {
    match error {
        SourceCallableError::Unsupported(reason) => SourceCallableDisplayError::Unsupported(reason),
        SourceCallableError::Invariant(_)
        | SourceCallableError::DeclaredType(_)
        | SourceCallableError::LiteralCache(_) => SourceCallableDisplayError::Malformed,
    }
}

/// Validates a source callable using only retained store state.
pub(super) fn validate_stored_source_callable(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
) -> StoredSourceCallableValidation {
    let provenance = store.source_callable_provenance(type_);
    let not_source = || {
        if provenance.is_some() {
            StoredSourceCallableValidation::Malformed
        } else {
            StoredSourceCallableValidation::NotSourceCallable
        }
    };
    let Some(record) = store.type_payload(type_) else {
        return not_source();
    };
    let Some(owner_symbol) = record.symbol() else {
        return not_source();
    };
    let Some(owner) = store.symbol(owner_symbol) else {
        return not_source();
    };
    let Some(declaration) = owner.value_declaration() else {
        return not_source();
    };
    if owner.declarations() != Some(&[declaration])
        && !valid_source_function_owner_shape(store, owner_symbol, declaration)
    {
        return not_source();
    }
    let Some(family) = source_family_for_kind(store.source_node_kind(declaration)) else {
        return not_source();
    };
    let Some(provenance) = provenance else {
        return StoredSourceCallableValidation::Malformed;
    };
    if provenance
        != (SourceCallableProvenance {
            family,
            declaration,
            owner_symbol,
            owner_parent: provenance.owner_parent,
            export_local: provenance.export_local,
            signature: provenance.signature,
            return_provenance: provenance.return_provenance,
            array_targets: provenance.array_targets,
            generic_return_type_parameter: provenance.generic_return_type_parameter,
            contextual_target: provenance.contextual_target,
            contextual_variable: provenance.contextual_variable,
        })
        || store.source_callable_type_for_owner(owner_symbol) != Some(type_)
        || store.source_callable_type_for_signature(provenance.signature) != Some(type_)
        || store.source_callable_type_for_declaration(declaration) != Some(type_)
    {
        return StoredSourceCallableValidation::Malformed;
    }
    let Some(signature) = store.signature_links(declaration).and_then(|links| {
        (links.effects_signature == EffectsSignatureState::Unresolved
            && links.decorator_signature == DecoratorSignatureState::Unresolved)
            .then_some(links.resolved_signature)
    }) else {
        return StoredSourceCallableValidation::Malformed;
    };
    let ResolvedSignatureState::Resolved(signature) = signature else {
        return StoredSourceCallableValidation::Malformed;
    };
    if signature != provenance.signature {
        return StoredSourceCallableValidation::Malformed;
    }
    let Some(signature_record) = store.signature(signature) else {
        return StoredSourceCallableValidation::Malformed;
    };
    let untyped_javascript = signature_record
        .flags()
        .contains(SignatureFlags::IS_UNTYPED_SIGNATURE_IN_JS_FILE);
    let direct_multi_untyped_arrow = family == SourceCallableFamily::ArrowFunction
        && store.source_node_kind(declaration) == Some(SyntaxKind::ArrowFunction)
        && signature_record.parameters().len() > 1
        && matches!(
            store.source_node_parent(declaration),
            Some(SourceNodeParent::Parent(variable))
                if store.source_node_kind(variable) == Some(SyntaxKind::VariableDeclaration)
        );
    if untyped_javascript
        && (signature_record.flags() != SignatureFlags::IS_UNTYPED_SIGNATURE_IN_JS_FILE
            || signature_record.parameters().len() != 1 && !direct_multi_untyped_arrow
            || !signature_record.type_parameters().is_empty()
            || signature_record.min_argument_count()
                != i32::try_from(signature_record.parameters().len()).unwrap_or(-1)
            || signature_record.parameters().iter().any(|parameter| {
                store
                    .symbol(*parameter)
                    .and_then(|parameter| parameter.declarations())
                    .and_then(|declarations| declarations.first())
                    .is_none_or(|declaration| {
                        store
                            .source_primitive_type_annotation(*declaration)
                            .is_some()
                    })
            }))
    {
        return StoredSourceCallableValidation::Malformed;
    }
    let contextual = match (provenance.contextual_target, provenance.contextual_variable) {
        (None, None) => None,
        (Some(target), Some(variable))
            if family == SourceCallableFamily::ArrowFunction
                && target != type_
                && variable != owner_symbol =>
        {
            Some((target, Some(variable)))
        }
        (Some(target), None)
            if family == SourceCallableFamily::ArrowFunction
                && target != type_
                && stored_direct_call_argument_arrow_is_exact(store, declaration, owner_symbol) =>
        {
            Some((target, None))
        }
        _ => return StoredSourceCallableValidation::Malformed,
    };
    let Some(TypeData::Object(object)) = store.type_payload(type_).map(TypeRecord::data) else {
        return StoredSourceCallableValidation::Malformed;
    };
    let expected_parameter_types = store.callable_signature_parameter_types(signature);
    let Some(type_parameter_edges) = valid_stored_source_type_parameters(
        store,
        declaration,
        family,
        contextual.is_some(),
        signature,
        signature_record.type_parameters(),
    ) else {
        return StoredSourceCallableValidation::Malformed;
    };
    let generic_return_provenance_valid = valid_stored_source_generic_return_provenance(
        store,
        signature,
        provenance.return_provenance,
        provenance.generic_return_type_parameter,
        &type_parameter_edges,
    );
    let return_annotation = store.function_signature_return_annotation(signature);
    let return_provenance_valid = match provenance.return_provenance {
        SourceCallableReturnProvenance::Annotated => {
            contextual.is_none() && return_annotation.is_some()
        }
        SourceCallableReturnProvenance::Inferred => {
            return_annotation.is_none()
                && (type_parameter_edges.is_empty()
                    || family == SourceCallableFamily::FunctionDeclaration
                        && valid_inferred_generic_signature_parameters(
                            store,
                            signature,
                            &type_parameter_edges,
                        ))
                && provenance.generic_return_type_parameter.is_none()
                && !store.signature_has_circular_return_type(signature)
        }
    };
    let mut edges =
        Vec::with_capacity(signature_record.parameters().len() + type_parameter_edges.len() + 2);
    edges.extend(type_parameter_edges.iter().copied());
    let mut default_parameter_count = 0usize;
    let parameters_valid =
        signature_record
            .parameters()
            .iter()
            .enumerate()
            .all(|(index, parameter)| {
                let Some(parameter_record) = store.symbol(*parameter) else {
                    return false;
                };
                let Some(parameter_declaration) = parameter_record
                    .declarations()
                    .and_then(|declarations| (declarations.len() == 1).then_some(declarations[0]))
                else {
                    return false;
                };
                let links_valid = match store.value_symbol_links(*parameter) {
                    None => {
                        default_parameter_count += 1;
                        true
                    }
                    Some(links) if links == &ValueSymbolLinks::default() => {
                        default_parameter_count += 1;
                        true
                    }
                    Some(links) if links.resolved_type.is_some() => {
                        let resolved = links.resolved_type.expect("the branch checked the type");
                        let expected = expected_parameter_types
                            .and_then(|types| types.get(index))
                            .copied();
                        let valid = links
                            == &(ValueSymbolLinks {
                                resolved_type: Some(resolved),
                                ..ValueSymbolLinks::default()
                            })
                            && expected.is_some_and(|expected| {
                                store.type_payload(expected).is_some()
                                    && (expected == resolved
                                        || valid_optional_type(
                                            store,
                                            provenance.array_targets,
                                            resolved,
                                            expected,
                                        ))
                            });
                        if valid {
                            edges.push(resolved);
                            if expected != Some(resolved) {
                                edges.push(expected.expect("the optional call type was validated"));
                            }
                        }
                        valid
                    }
                    Some(_) => false,
                };
                parameter_record.flags() == SymbolFlags::FUNCTION_SCOPED_VARIABLE
                    && parameter_record.check_flags() == CheckFlags::NONE
                    && parameter_record.value_declaration() == Some(parameter_declaration)
                    && parameter_record.members().is_none()
                    && parameter_record.exports().is_none()
                    && parameter_record.parent().is_none()
                    && parameter_record.export_symbol().is_none()
                    && store.get_merged_symbol(*parameter) == Some(*parameter)
                    && store.source_node_kind(parameter_declaration) == Some(SyntaxKind::Parameter)
                    && store.source_node_parent(parameter_declaration)
                        == Some(SourceNodeParent::Parent(declaration))
                    && links_valid
            });
    let parameters_unique = signature_record
        .parameters()
        .iter()
        .enumerate()
        .all(|(index, parameter)| !signature_record.parameters()[..index].contains(parameter));
    let owner_links = ValueSymbolLinks {
        resolved_type: Some(type_),
        ..ValueSymbolLinks::default()
    };
    if record.flags() != TypeFlags::OBJECT
        || record.object_flags() != ObjectFlags::ANONYMOUS | ObjectFlags::MEMBERS_RESOLVED
        || record.alias().is_some()
        || family == SourceCallableFamily::ArrowFunction
            && (owner.flags() != SymbolFlags::FUNCTION
                || owner.declarations() != Some(&[declaration])
                || !source_arrow_owner_expando_exports_are_valid(store, owner_symbol, declaration)
                || contextual.is_some() && owner.exports().is_some())
        || family == SourceCallableFamily::FunctionDeclaration
            && !valid_source_function_owner_shape(store, owner_symbol, declaration)
        || owner.check_flags() != CheckFlags::NONE
        || owner.value_declaration() != Some(declaration)
        || owner.members().is_some()
        || owner.export_symbol().is_some()
        || owner.parent() != provenance.owner_parent
        || family == SourceCallableFamily::ArrowFunction
            && (owner.name() != InternalSymbolName::Function.as_ref()
                || provenance.owner_parent.is_some()
                || provenance.export_local.is_some())
        || family == SourceCallableFamily::FunctionDeclaration
            && !valid_stored_function_export_route(
                store,
                owner_symbol,
                owner,
                declaration,
                provenance,
            )
        || store.get_merged_symbol(owner_symbol) != Some(owner_symbol)
        || store.value_symbol_links(owner_symbol) != Some(&owner_links)
        || signature_record.flags().bits()
            & !(if contextual.is_some() {
                SignatureFlags::HAS_REST_PARAMETER
            } else {
                SignatureFlags::HAS_LITERAL_TYPES
                    | SignatureFlags::HAS_REST_PARAMETER
                    | SignatureFlags::IS_UNTYPED_SIGNATURE_IN_JS_FILE
            })
            .bits()
            != 0
        || signature_record.min_argument_count() < 0
        || usize::try_from(signature_record.min_argument_count()).map_or(true, |minimum| {
            minimum > signature_record.parameters().len()
        })
        || signature_record.resolved_min_argument_count() != -1
        || signature_record.declaration() != Some(declaration)
        || signature_record.this_parameter().is_some()
        || !valid_stored_callable_type_predicate(
            store,
            signature_record,
            return_annotation.map(|(annotation, _)| annotation),
        )
        || signature_record.target().is_some()
        || signature_record.mapper().is_some()
        || signature_record.isolated_signature_type().is_some()
        || signature_record.composite().is_some()
        || !valid_stored_generic_source_signature(
            store,
            signature_record,
            expected_parameter_types,
            provenance.array_targets,
            &type_parameter_edges,
        )
        || !generic_return_provenance_valid
        || !return_provenance_valid
        || !parameters_valid
        || default_parameter_count != 0
            && default_parameter_count != signature_record.parameters().len()
        || !parameters_unique
        || contextual.is_some() && default_parameter_count != 0
        || object.structured.constrained != ConstrainedTypeData::default()
        || object.target.is_some()
        || object.mapper.is_some()
        || object.instantiations != TypeCacheState::Unallocated
    {
        return StoredSourceCallableValidation::Malformed;
    }
    if object.structured == StructuredTypeData::default() {
        return if default_parameter_count == signature_record.parameters().len()
            && expected_parameter_types.is_none()
            && signature_record.resolved_return_type().is_none()
            && !store.signature_has_circular_return_type(signature)
        {
            StoredSourceCallableValidation::Pending
        } else {
            StoredSourceCallableValidation::Malformed
        };
    }
    if object.structured.members.is_some()
        || object.structured.properties.is_some()
        || object.structured.signatures.as_deref() != Some(&[signature])
        || object.structured.call_signature_count != 1
        || object.structured.index_infos.is_some()
        || object
            .structured
            .object_type_without_abstract_construct_signatures
            .is_some()
    {
        return StoredSourceCallableValidation::Malformed;
    }
    if default_parameter_count != 0 {
        if expected_parameter_types.is_some()
            || signature_record.resolved_return_type().is_some()
            || store.signature_has_circular_return_type(signature)
        {
            return StoredSourceCallableValidation::Malformed;
        }
        return StoredSourceCallableValidation::Pending;
    }
    if expected_parameter_types
        .is_none_or(|types| types.len() != signature_record.parameters().len())
    {
        return StoredSourceCallableValidation::Malformed;
    }
    if let Some((target, variable)) = contextual {
        let direct_call_anchor = variable.is_none();
        let anchor_valid = variable.map_or_else(
            || stored_direct_call_argument_arrow_is_exact(store, declaration, owner_symbol),
            |anchor| {
                store.source_contextual_callable_anchor_is_exact(declaration, owner_symbol, anchor)
            },
        );
        let property_anchor = anchor_valid
            && variable.is_some_and(|anchor| {
                store
                    .symbol(anchor)
                    .is_some_and(|symbol| symbol.flags() == SymbolFlags::PROPERTY)
            });
        let return_type = signature_record.resolved_return_type();
        let return_valid = store.intrinsic_bootstrap().is_some_and(|bootstrap| {
            return_type.is_some_and(|return_type| {
                (property_anchor || direct_call_anchor)
                    && store.validate_cached_array_capability(return_type).is_ok()
                    || !property_anchor && !direct_call_anchor && return_type == bootstrap.void_type
            }) && store
                .function_signature_return_annotation(signature)
                .is_none()
                && !store.signature_has_circular_return_type(signature)
        });
        let target_valid = target != type_
            && if direct_call_anchor {
                signature_record.flags() == SignatureFlags::NONE
                    && usize::try_from(signature_record.min_argument_count()).ok()
                        == Some(signature_record.parameters().len())
                    && expected_parameter_types.is_some_and(|types| {
                        let StoredSingleCallableValidation::Valid { callable, .. } =
                            validate_stored_single_callable(store, target)
                        else {
                            return false;
                        };
                        let Some(signature) = store.signature(callable.signature) else {
                            return false;
                        };
                        !types.is_empty()
                            && signature.type_parameters().is_empty()
                            && !signature.has_rest_parameter()
                            && callable.rest_parameter.is_none()
                            && (callable.min_argument_count == types.len()
                                && callable.parameters.as_slice() == types
                                || types.len() == 1
                                    && callable.min_argument_count >= 1
                                    && callable.parameters.first().copied().is_some_and(
                                        |source_parameter| {
                                            super::source_calls::authenticated_array_callback_contextual_target(
                                                store,
                                                target,
                                                source_parameter,
                                                types[0],
                                            )
                                        },
                                    )
                                || types.len() == 1
                                    && callable.min_argument_count == 2
                                    && matches!(
                                        callable.parameters.as_slice(),
                                        [first, _] if *first == types[0]
                                    )
                                    && stored_promise_executor_contextual_target_is_exact(
                                        store, signature,
                                    ))
                    })
            } else {
                matches!(
                    validate_stored_function_type(store, target),
                    StoredFunctionTypeValidation::Valid(_)
                )
            };
        let rest_valid = if signature_record
            .flags()
            .contains(SignatureFlags::HAS_REST_PARAMETER)
        {
            expected_parameter_types
                .and_then(|types| types.last())
                .copied()
                .is_some_and(|rest| store.validate_canonical_empty_tuple_type(rest).is_ok())
        } else {
            true
        };
        if !anchor_valid || !return_valid || !target_valid || !rest_valid {
            return StoredSourceCallableValidation::Malformed;
        }
        edges.push(target);
        edges.push(return_type.expect("the contextual return was validated"));
        return StoredSourceCallableValidation::Valid(edges);
    }
    if provenance.return_provenance == SourceCallableReturnProvenance::Inferred {
        let Some(return_type) = signature_record.resolved_return_type() else {
            return StoredSourceCallableValidation::Pending;
        };
        let valid_return = (type_parameter_edges.is_empty()
            || store
                .intrinsic_bootstrap()
                .is_some_and(|bootstrap| return_type == bootstrap.void_type))
            && valid_inferred_source_callable_return_capability(
                store,
                provenance.array_targets,
                return_type,
            );
        if !valid_return {
            return StoredSourceCallableValidation::Malformed;
        }
        if !canonical_lazy_global_jsx_element_return(store, return_type)
            && !super::enums::is_canonical_enum_union(store, return_type)
        {
            edges.push(return_type);
        }
        return StoredSourceCallableValidation::Valid(edges);
    }
    let Some((return_identity_node, return_null_literal_identity)) = return_annotation else {
        return StoredSourceCallableValidation::Malformed;
    };
    if let Some(return_type) = signature_record.resolved_return_type() {
        let annotation =
            cached_annotation_identity(store, return_identity_node, return_null_literal_identity);
        let valid_return = if !type_parameter_edges.is_empty()
            && (store.circular_return_annotation_type(signature).is_some()
                || !valid_source_generic_mapper_type(
                    store,
                    return_type,
                    &type_parameter_edges,
                    provenance.array_targets,
                )
                || !valid_stored_source_generic_return_annotation(
                    store,
                    return_identity_node,
                    return_null_literal_identity,
                    return_type,
                    provenance.generic_return_type_parameter,
                    &type_parameter_edges,
                    provenance.array_targets,
                )) {
            false
        } else if let Some(circular_annotation) = store.circular_return_annotation_type(signature) {
            let valid = store.intrinsic_bootstrap().is_some_and(|bootstrap| {
                annotation == Some(circular_annotation) && return_type == bootstrap.any_type
            });
            if valid {
                edges.push(circular_annotation);
            }
            valid
        } else {
            annotation == Some(return_type)
        };
        if !valid_return {
            return StoredSourceCallableValidation::Malformed;
        }
        edges.push(return_type);
    } else if store.signature_has_circular_return_type(signature) {
        return StoredSourceCallableValidation::Malformed;
    }
    if let Some(narrowed) = signature_record
        .resolved_type_predicate()
        .and_then(|predicate| store.type_predicate(predicate))
        .and_then(super::signatures::TypePredicate::type_id)
    {
        edges.push(narrowed);
    }
    StoredSourceCallableValidation::Valid(edges)
}

fn valid_stored_generic_source_signature(
    store: &CanonicalTypeMapperStore,
    signature: &Signature,
    parameter_types: Option<&[TypeId]>,
    array_targets: Option<CanonicalArrayTargets>,
    type_parameters: &[TypeId],
) -> bool {
    if type_parameters.is_empty() {
        return true;
    }
    let Ok(minimum_argument_count) = usize::try_from(signature.min_argument_count()) else {
        return false;
    };
    let generic_arrow = signature.declaration().is_some_and(|declaration| {
        store.source_node_kind(declaration) == Some(SyntaxKind::ArrowFunction)
    });
    let has_rest = signature.flags() == SignatureFlags::HAS_REST_PARAMETER;
    let fixed_parameter_count = signature
        .parameters()
        .len()
        .saturating_sub(usize::from(has_rest));
    (signature.flags() == SignatureFlags::NONE || has_rest)
        && minimum_argument_count <= fixed_parameter_count
        && parameter_types.is_none_or(|types| {
            types.len() == signature.parameters().len()
                && types.iter().enumerate().all(|(index, type_)| {
                    valid_generic_source_parameter_type(
                        store,
                        array_targets,
                        *type_,
                        type_parameters,
                    ) || index < fixed_parameter_count
                        && valid_fixed_generic_source_parameter_type(store, *type_)
                        || (index >= minimum_argument_count || generic_arrow)
                            && valid_optional_generic_source_parameter_type(
                                store,
                                array_targets,
                                *type_,
                                type_parameters,
                            )
                })
        })
}

fn valid_optional_generic_source_parameter_type(
    store: &CanonicalTypeMapperStore,
    array_targets: Option<CanonicalArrayTargets>,
    type_: TypeId,
    type_parameters: &[TypeId],
) -> bool {
    let Some(undefined) = store
        .intrinsic_bootstrap()
        .map(|bootstrap| bootstrap.undefined_type)
    else {
        return false;
    };
    let Some(record) = store.type_payload(type_) else {
        return false;
    };
    let TypeData::Union(union) = record.data() else {
        return false;
    };
    if record.alias().is_some()
        || union.origin.is_some()
        || union.union.types.len() != 2
        || !union.union.types.contains(&undefined)
        || store
            .intrinsic_bootstrap()
            .and_then(|bootstrap| bootstrap.cached_union_type(&union.union.types))
            != Some(type_)
    {
        return false;
    }
    union
        .union
        .types
        .iter()
        .copied()
        .filter(|candidate| *candidate != undefined)
        .all(|candidate| {
            valid_generic_source_parameter_type(store, array_targets, candidate, type_parameters)
                || valid_fixed_generic_source_parameter_type(store, candidate)
        })
}

/// Authenticates source-independent primitive or unary callback parameters.
pub(super) fn valid_fixed_generic_source_parameter_type(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
) -> bool {
    if valid_fixed_generic_intrinsic_type(store, type_) {
        return true;
    }
    if !matches!(
        validate_stored_function_type(store, type_),
        StoredFunctionTypeValidation::Valid(_)
    ) {
        return false;
    }
    let StoredSingleCallableValidation::Valid { callable, .. } =
        validate_stored_single_callable(store, type_)
    else {
        return false;
    };
    let Some(signature) = store.signature(callable.signature) else {
        return false;
    };
    let [parameter] = callable.parameters.as_slice() else {
        return false;
    };
    let Some(declaration) = signature.declaration() else {
        return false;
    };
    let Some((return_annotation, null_literal_identity)) =
        store.function_signature_return_annotation(callable.signature)
    else {
        return false;
    };
    let return_annotation_valid = if null_literal_identity {
        store.source_node_kind(return_annotation) == Some(SyntaxKind::LiteralType)
    } else {
        store
            .source_node_kind(return_annotation)
            .is_some_and(fixed_generic_intrinsic_annotation_kind)
    };
    signature.type_parameters().is_empty()
        && signature.flags() == SignatureFlags::NONE
        && callable.min_argument_count == 1
        && callable.rest_parameter.is_none()
        && store.source_node_parent(return_annotation)
            == Some(SourceNodeParent::Parent(declaration))
        && return_annotation_valid
        && valid_fixed_generic_intrinsic_type(store, *parameter)
        && callable
            .return_type
            .is_none_or(|return_type| valid_fixed_generic_intrinsic_type(store, return_type))
}

fn valid_fixed_generic_intrinsic_type(store: &CanonicalTypeMapperStore, type_: TypeId) -> bool {
    let Some(bootstrap) = store.intrinsic_bootstrap() else {
        return false;
    };
    [
        bootstrap.any_type,
        bootstrap.unknown_type,
        bootstrap.undefined_type,
        bootstrap.null_type,
        bootstrap.string_type,
        bootstrap.number_type,
        bootstrap.bigint_type,
        bootstrap.boolean_type,
        bootstrap.es_symbol_type,
        bootstrap.void_type,
        bootstrap.never_type,
        bootstrap.non_primitive_type,
    ]
    .contains(&type_)
}

fn valid_generic_source_parameter_type(
    store: &CanonicalTypeMapperStore,
    array_targets: Option<CanonicalArrayTargets>,
    type_: TypeId,
    type_parameters: &[TypeId],
) -> bool {
    valid_generic_source_parameter_type_worker(
        store,
        array_targets,
        type_,
        type_parameters,
        &mut HashSet::new(),
    )
}

fn valid_generic_source_parameter_type_worker(
    store: &CanonicalTypeMapperStore,
    array_targets: Option<CanonicalArrayTargets>,
    type_: TypeId,
    type_parameters: &[TypeId],
    active: &mut HashSet<TypeId>,
) -> bool {
    if type_parameters.contains(&type_) {
        return true;
    }
    if !active.insert(type_) {
        return false;
    }
    let array = array_targets.and_then(|targets| {
        store
            .canonical_array_reference_with_targets(targets, type_)
            .ok()
            .flatten()
    });
    let valid = if let Some(array) = array {
        !array.readonly
            && !array.array_literal
            && valid_generic_source_parameter_type_worker(
                store,
                array_targets,
                array.element_type,
                type_parameters,
                active,
            )
    } else if let Ok(reference) = validate_direct_generic_reference(store, type_) {
        store
            .type_payload(reference.target)
            .and_then(TypeRecord::symbol)
            .and_then(|symbol| store.symbol(symbol))
            .is_some_and(|owner| {
                owner.flags().contains(SymbolFlags::INTERFACE)
                    && owner
                        .flags()
                        .without(SymbolFlags::INTERFACE | SymbolFlags::TRANSIENT)
                        == SymbolFlags::NONE
                    && (array_targets.is_some()
                        || !matches!(owner.name().as_utf8(), Some("Array" | "ReadonlyArray")))
                    && !reference.type_arguments.is_empty()
                    && reference.type_arguments.iter().all(|argument| {
                        valid_generic_source_parameter_type_worker(
                            store,
                            array_targets,
                            *argument,
                            type_parameters,
                            active,
                        )
                    })
            })
    } else {
        false
    };
    active.remove(&type_);
    valid
}

fn valid_named_source_generic_reference(
    store: &CanonicalTypeMapperStore,
    annotation: NodeRef,
    type_: TypeId,
    type_parameters: &[TypeId],
) -> bool {
    let Some(symbol) = store
        .symbol_node_links(annotation)
        .and_then(|links| links.resolved_symbol)
    else {
        return false;
    };
    let Ok(reference) = validate_direct_generic_reference(store, type_) else {
        return false;
    };
    store.source_node_kind(annotation) == Some(SyntaxKind::TypeReference)
        && store.symbol_node_links(annotation)
            == Some(&SymbolNodeLinks {
                resolved_symbol: Some(symbol),
            })
        && store.type_node_links(annotation)
            == Some(&TypeNodeLinks {
                resolved_type: Some(type_),
                outer_type_parameters: None,
            })
        && store
            .type_payload(reference.target)
            .and_then(TypeRecord::symbol)
            == Some(symbol)
        && valid_generic_source_parameter_type(store, None, type_, type_parameters)
}

fn valid_stored_source_generic_return_provenance(
    store: &CanonicalTypeMapperStore,
    signature: SignatureId,
    return_provenance: SourceCallableReturnProvenance,
    expected: Option<TypeId>,
    type_parameters: &[TypeId],
) -> bool {
    if type_parameters.is_empty() {
        return expected.is_none();
    }
    if return_provenance == SourceCallableReturnProvenance::Inferred {
        return expected.is_none()
            && store
                .function_signature_return_annotation(signature)
                .is_none()
            && valid_inferred_generic_signature_parameters(store, signature, type_parameters);
    }
    let Some((annotation, _)) = store.function_signature_return_annotation(signature) else {
        return false;
    };
    match expected {
        Some(type_parameter) => {
            let Some(symbol) = cached_ordinary_type_parameter_owner(store, type_parameter) else {
                return false;
            };
            type_parameters.contains(&type_parameter)
                && store.source_node_kind(annotation) == Some(SyntaxKind::TypeReference)
                && source_type_parameter_annotation_links_are_cold_or_fully_warm(
                    store,
                    annotation,
                    symbol,
                    type_parameter,
                )
        }
        None if store.source_node_kind(annotation) != Some(SyntaxKind::TypeReference) => true,
        None => {
            let symbol_links = store.symbol_node_links(annotation);
            let type_links = store.type_node_links(annotation);
            let cold = symbol_links.is_none_or(|links| links == &SymbolNodeLinks::default())
                && type_links.is_none_or(|links| links == &TypeNodeLinks::default());
            if cold {
                return store
                    .signature(signature)
                    .and_then(Signature::declaration)
                    .is_some_and(|declaration| {
                        store.source_node_parent(annotation)
                            == Some(SourceNodeParent::Parent(declaration))
                    });
            }
            type_links
                .and_then(|links| links.resolved_type)
                .is_some_and(|type_| {
                    valid_named_source_generic_reference(store, annotation, type_, type_parameters)
                })
        }
    }
}

fn valid_inferred_generic_signature_parameters(
    store: &CanonicalTypeMapperStore,
    signature: SignatureId,
    type_parameters: &[TypeId],
) -> bool {
    let Some(record) = store.signature(signature) else {
        return false;
    };
    if record.flags() != SignatureFlags::NONE {
        return false;
    }
    if record.parameters().is_empty() {
        return record.min_argument_count() == 0;
    }
    let ([type_parameter], [parameter]) = (type_parameters, record.parameters()) else {
        return false;
    };
    if record.min_argument_count() != 1 {
        return false;
    }
    let Some([provenance]) = store.source_callable_type_parameters(signature) else {
        return false;
    };
    let Some(constraint) = provenance.constraint else {
        return false;
    };
    let Some(error_type) = store
        .intrinsic_bootstrap()
        .map(|bootstrap| bootstrap.error_type)
    else {
        return false;
    };
    if provenance.type_parameter != *type_parameter
        || !store.source_recovered_unresolved_type_reference_is_exact(constraint, error_type)
        || store
            .callable_signature_parameter_types(signature)
            .is_some_and(|types| types != [*type_parameter])
    {
        return false;
    }
    let Some([declaration]) = store
        .symbol(*parameter)
        .and_then(|symbol| symbol.declarations())
    else {
        return false;
    };
    store.source_node_kind(*declaration) == Some(SyntaxKind::Parameter)
        && record.declaration().is_some_and(|owner| {
            store.source_node_parent(*declaration) == Some(SourceNodeParent::Parent(owner))
        })
        && store.value_symbol_links(*parameter).is_none_or(|links| {
            links == &ValueSymbolLinks::default()
                || links
                    == &ValueSymbolLinks {
                        resolved_type: Some(*type_parameter),
                        ..ValueSymbolLinks::default()
                    }
        })
}

fn valid_source_generic_mapper_type(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
    type_parameters: &[TypeId],
    array_targets: Option<CanonicalArrayTargets>,
) -> bool {
    if store
        .intrinsic_bootstrap()
        .is_some_and(|bootstrap| type_ == bootstrap.boolean_type || type_ == bootstrap.void_type)
    {
        return true;
    }
    let Some(record) = store.type_payload(type_) else {
        return false;
    };
    match record.data() {
        TypeData::TypeParameter(_) => {
            type_parameters.contains(&type_)
                && cached_ordinary_type_parameter_owner(store, type_).is_some()
        }
        TypeData::Intrinsic(_) | TypeData::Literal(_) | TypeData::UniqueEsSymbol(_) => {
            store.validate_union_constituent(type_).is_ok()
        }
        TypeData::TypeReference(_) => {
            valid_generic_source_parameter_type(store, array_targets, type_, type_parameters)
        }
        _ => false,
    }
}

fn valid_stored_source_generic_return_annotation(
    store: &CanonicalTypeMapperStore,
    annotation: NodeRef,
    null_literal_identity: bool,
    return_type: TypeId,
    expected: Option<TypeId>,
    type_parameters: &[TypeId],
    array_targets: Option<CanonicalArrayTargets>,
) -> bool {
    if let Some(expected) = expected {
        let Some(symbol) = cached_ordinary_type_parameter_owner(store, expected) else {
            return false;
        };
        return return_type == expected
            && type_parameters.contains(&expected)
            && store.source_node_kind(annotation) == Some(SyntaxKind::TypeReference)
            && source_type_parameter_annotation_links_are_fully_warm(
                store, annotation, symbol, expected,
            );
    }
    if null_literal_identity {
        return store
            .intrinsic_bootstrap()
            .is_some_and(|bootstrap| return_type == bootstrap.null_type);
    }
    if store.source_node_kind(annotation) == Some(SyntaxKind::TypePredicate) {
        let Some(bootstrap) = store.intrinsic_bootstrap() else {
            return false;
        };
        return (return_type == bootstrap.boolean_type || return_type == bootstrap.void_type)
            && store.type_node_links(annotation)
                == Some(&TypeNodeLinks {
                    resolved_type: Some(return_type),
                    outer_type_parameters: None,
                });
    }
    if store.source_node_kind(annotation) == Some(SyntaxKind::ArrayType) {
        let Some(targets) = array_targets else {
            return false;
        };
        let Ok(Some(reference)) =
            store.canonical_array_reference_with_targets(targets, return_type)
        else {
            return false;
        };
        return !reference.readonly
            && !reference.array_literal
            && store.type_node_links(annotation)
                == Some(&TypeNodeLinks {
                    resolved_type: Some(return_type),
                    outer_type_parameters: None,
                })
            && valid_generic_source_parameter_type(
                store,
                Some(targets),
                return_type,
                type_parameters,
            );
    }
    if store.source_node_kind(annotation) == Some(SyntaxKind::TypeReference) {
        return valid_named_source_generic_reference(
            store,
            annotation,
            return_type,
            type_parameters,
        );
    }
    store.source_type_node_result_is_exact(annotation, return_type, &[])
}

fn valid_stored_source_type_parameters(
    store: &CanonicalTypeMapperStore,
    declaration: NodeRef,
    family: SourceCallableFamily,
    contextual: bool,
    signature: SignatureId,
    type_parameters: &[TypeId],
) -> Option<Vec<TypeId>> {
    if type_parameters.is_empty() {
        return store
            .source_callable_type_parameters(signature)
            .is_none()
            .then(Vec::new);
    }
    if contextual
        || family != SourceCallableFamily::FunctionDeclaration
            && family != SourceCallableFamily::ArrowFunction
    {
        return None;
    }
    let provenances = store.source_callable_type_parameters(signature)?;
    if provenances.len() != type_parameters.len() {
        return None;
    }
    let no_constraint = store.intrinsic_bootstrap()?.no_constraint_type;
    let mut declarations = HashSet::with_capacity(type_parameters.len());
    let mut symbols = HashSet::with_capacity(type_parameters.len());
    let mut identities = HashSet::with_capacity(type_parameters.len());
    let mut resolved = Vec::with_capacity(type_parameters.len());
    let mut expected_bases = Vec::with_capacity(type_parameters.len());
    let mut default_seen = false;
    for (index, (type_parameter, provenance)) in
        type_parameters.iter().copied().zip(provenances).enumerate()
    {
        if provenance.type_parameter != type_parameter
            || !declarations.insert(provenance.declaration)
            || !symbols.insert(provenance.symbol)
            || !identities.insert(type_parameter)
        {
            return None;
        }
        let symbol = cached_ordinary_type_parameter_owner(store, type_parameter)?;
        if symbol != provenance.symbol {
            return None;
        }
        let symbol_record = store.symbol(symbol)?;
        let [type_parameter_declaration] = symbol_record.declarations()? else {
            return None;
        };
        let TypeData::TypeParameter(type_parameter_data) =
            store.type_payload(type_parameter)?.data()
        else {
            return None;
        };
        let constraint = type_parameter_data.constraint?;
        let default_type = type_parameter_data.resolved_default_type?;
        let constraint_valid = match provenance.constraint {
            Some(node) => {
                constraint != no_constraint
                    && store.source_node_parent(node)
                        == Some(SourceNodeParent::Parent(provenance.declaration))
                    && store.source_type_node_result_is_exact(node, constraint, &resolved)
            }
            None => constraint == no_constraint,
        };
        let default_valid = match provenance.default_type {
            Some(node) => {
                default_type != no_constraint
                    && store.source_node_parent(node)
                        == Some(SourceNodeParent::Parent(provenance.declaration))
                    && store.source_type_node_result_is_exact(node, default_type, &resolved)
            }
            None => default_type == no_constraint,
        };
        let trailing_default_valid = !default_seen || provenance.default_type.is_some();
        default_seen |= provenance.default_type.is_some();
        let compatible_constraint_default_pair = provenance.constraint.is_none()
            || provenance.default_type.is_none()
            || source_type_parameter_default_is_assignable(store, constraint, default_type);
        if symbol_record.flags() != SymbolFlags::TYPE_PARAMETER
            || symbol_record.check_flags() != CheckFlags::NONE
            || symbol_record.value_declaration().is_some()
            || symbol_record.members().is_some()
            || symbol_record.exports().is_some()
            || symbol_record.parent().is_some()
            || symbol_record.export_symbol().is_some()
            || store.get_merged_symbol(symbol) != Some(symbol)
            || *type_parameter_declaration != provenance.declaration
            || store.source_node_kind(provenance.declaration) != Some(SyntaxKind::TypeParameter)
            || store.source_node_parent(provenance.declaration)
                != Some(SourceNodeParent::Parent(declaration))
            || !constraint_valid
            || !default_valid
            || !trailing_default_valid
            || !compatible_constraint_default_pair
        {
            return None;
        }
        let expected_base = if provenance.constraint.is_none() {
            no_constraint
        } else if let Some(earlier) = resolved[..index]
            .iter()
            .position(|candidate| candidate.provenance.type_parameter == constraint)
        {
            expected_bases[earlier]
        } else {
            constraint
        };
        if type_parameter_data
            .constrained
            .resolved_base_constraint
            .is_some_and(|base| base != expected_base)
        {
            return None;
        }
        resolved.push(ResolvedSourceCallableTypeParameter {
            provenance: *provenance,
            constraint,
            default_type,
        });
        expected_bases.push(expected_base);
    }
    Some(type_parameters.to_vec())
}

fn valid_stored_function_export_route(
    store: &CanonicalTypeMapperStore,
    owner_symbol: SemanticSymbolId,
    owner: &ts_binder::semantic::Symbol,
    declaration: NodeRef,
    provenance: SourceCallableProvenance,
) -> bool {
    match (provenance.owner_parent, provenance.export_local) {
        (None, None) => owner.parent().is_none(),
        (Some(parent), Some(local)) if owner.parent() == Some(parent) => {
            store.symbol(local).is_some_and(|local_record| {
                store.get_merged_symbol(local) == Some(local)
                    && local_record.flags() == SymbolFlags::EXPORT_VALUE
                    && local_record.check_flags() == CheckFlags::NONE
                    && local_record.name() == owner.name()
                    && local_record.declarations() == Some(&[declaration])
                    && local_record.value_declaration().is_none()
                    && local_record.members().is_none()
                    && local_record.exports().is_none()
                    && local_record.parent().is_none()
                    && local_record.export_symbol() == Some(owner_symbol)
            })
        }
        _ => false,
    }
}

/// Returns the retained source family for either a branded callable or an
/// otherwise source-callable-shaped record rejected by the store validator.
pub(super) fn stored_source_callable_family(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
) -> Option<SourceCallableFamily> {
    if let Some(provenance) = store.source_callable_provenance(type_) {
        return Some(provenance.family);
    }
    let owner_symbol = store.type_payload(type_)?.symbol()?;
    let owner = store.symbol(owner_symbol)?;
    let declaration = owner.value_declaration()?;
    let family = source_family_for_kind(store.source_node_kind(declaration))?;
    (owner.declarations() == Some(&[declaration])
        || family == SourceCallableFamily::FunctionDeclaration
            && valid_source_function_owner_shape(store, owner_symbol, declaration))
    .then_some(family)
}

const fn source_family_for_kind(kind: Option<SyntaxKind>) -> Option<SourceCallableFamily> {
    match kind {
        Some(SyntaxKind::FunctionDeclaration) => Some(SourceCallableFamily::FunctionDeclaration),
        Some(SyntaxKind::ArrowFunction | SyntaxKind::FunctionExpression) => {
            Some(SourceCallableFamily::ArrowFunction)
        }
        _ => None,
    }
}

fn validate_signature(
    store: &CanonicalTypeMapperStore,
    plan: &SourceCallablePlan,
    signature: SignatureId,
) -> Result<(), SourceCallableError> {
    let record = store.signature(signature).ok_or_else(|| {
        invariant(SourceCallableInvariant::InvalidSignatureCache(
            plan.declaration,
        ))
    })?;
    let expected_parameters = plan
        .parameters
        .iter()
        .map(|parameter| parameter.symbol)
        .collect::<Vec<_>>();
    let expected_type_parameters = planned_type_parameter_ids(store, plan).ok_or_else(|| {
        invariant(SourceCallableInvariant::InvalidSignatureCache(
            plan.declaration,
        ))
    })?;
    let exact_type_parameter_provenance = if plan.type_parameters.is_empty() {
        store.source_callable_type_parameters(signature).is_none()
    } else {
        store
            .source_callable_type_parameters(signature)
            .is_some_and(|rows| {
                rows.len() == plan.type_parameters.len()
                    && rows
                        .iter()
                        .zip(&plan.type_parameters)
                        .zip(&expected_type_parameters)
                        .all(|((row, planned), expected)| {
                            row == &(SourceCallableTypeParameterProvenance {
                                declaration: planned.declaration,
                                symbol: planned.symbol,
                                type_parameter: *expected,
                                constraint: planned.constraint,
                                default_type: planned.default_type,
                            })
                        })
            })
    };
    if record.flags() != plan.flags
        || record.min_argument_count() != plan.min_argument_count
        || record.resolved_min_argument_count() != -1
        || record.declaration() != Some(plan.declaration)
        || record.type_parameters() != expected_type_parameters
        || !exact_type_parameter_provenance
        || valid_stored_source_type_parameters(
            store,
            plan.declaration,
            plan.family,
            false,
            signature,
            record.type_parameters(),
        )
        .as_deref()
            != Some(expected_type_parameters.as_slice())
        || record.parameters() != expected_parameters
        || record.this_parameter().is_some()
        || !valid_planned_callable_type_predicate(
            store,
            record,
            plan.return_type
                .annotation_identity()
                .map(|(annotation, _)| annotation),
            plan.type_predicate,
        )
        || record.target().is_some()
        || record.mapper().is_some()
        || record.isolated_signature_type().is_some()
        || record.composite().is_some()
        || store.function_signature_return_annotation(signature)
            != plan.return_type.annotation_identity()
    {
        return Err(invariant(SourceCallableInvariant::InvalidSignatureCache(
            plan.declaration,
        )));
    }
    Ok(())
}

fn planned_type_parameter_ids(
    store: &CanonicalTypeMapperStore,
    plan: &SourceCallablePlan,
) -> Option<Vec<TypeId>> {
    plan.type_parameters
        .iter()
        .map(|type_parameter| {
            let declared_type = store
                .declared_type_links(type_parameter.symbol)?
                .declared_type?;
            (cached_ordinary_type_parameter_owner(store, declared_type)
                == Some(type_parameter.symbol))
            .then_some(declared_type)
        })
        .collect()
}

fn exact_signature_link(
    store: &CanonicalTypeMapperStore,
    declaration: NodeRef,
) -> Result<SignatureId, SourceCallableError> {
    let Some(links) = store.signature_links(declaration) else {
        return Err(invariant(SourceCallableInvariant::InvalidSignatureCache(
            declaration,
        )));
    };
    let ResolvedSignatureState::Resolved(signature) = links.resolved_signature else {
        return Err(invariant(SourceCallableInvariant::InvalidSignatureCache(
            declaration,
        )));
    };
    if links.effects_signature != EffectsSignatureState::Unresolved
        || links.decorator_signature != DecoratorSignatureState::Unresolved
    {
        return Err(invariant(SourceCallableInvariant::InvalidSignatureCache(
            declaration,
        )));
    }
    Ok(signature)
}

fn default_signature_links(store: &CanonicalTypeMapperStore, declaration: NodeRef) -> bool {
    store
        .signature_links(declaration)
        .is_none_or(|links| links == &SignatureLinks::default())
}

fn default_parameter_links(store: &CanonicalTypeMapperStore, symbol: SemanticSymbolId) -> bool {
    store
        .value_symbol_links(symbol)
        .is_none_or(|links| links == &ValueSymbolLinks::default())
}

fn validate_parameter_links(
    store: &CanonicalTypeMapperStore,
    plan: &SourceCallablePlan,
    parameter: &SourceCallableParameterPlan,
    expected: TypeId,
) -> Result<(), SourceCallableError> {
    let links = store.value_symbol_links(parameter.symbol).ok_or_else(|| {
        invariant(SourceCallableInvariant::InvalidParameterCache(
            parameter.declaration,
        ))
    })?;
    let Some(resolved) = links.resolved_type else {
        return Err(invariant(SourceCallableInvariant::InvalidParameterCache(
            parameter.declaration,
        )));
    };
    if links
        != &(ValueSymbolLinks {
            resolved_type: Some(resolved),
            ..ValueSymbolLinks::default()
        })
    {
        return Err(invariant(SourceCallableInvariant::InvalidParameterCache(
            parameter.declaration,
        )));
    }
    let base = parameter.base_type(store).ok_or_else(|| {
        invariant(SourceCallableInvariant::InvalidParameterCache(
            parameter.declaration,
        ))
    })?;
    let strict = store
        .intrinsic_bootstrap()
        .ok_or_else(|| {
            invariant(SourceCallableInvariant::InvalidParameterCache(
                parameter.declaration,
            ))
        })?
        .options
        .strict_null_checks;
    let call_type_valid = if strict && (parameter.optional || parameter.initializer.is_some()) {
        valid_optional_type(store, plan.array_targets, base, expected)
    } else {
        base == expected
    };
    let value_type_valid = if strict && parameter.optional {
        valid_optional_type(store, plan.array_targets, base, resolved)
    } else {
        base == resolved
    };
    if !call_type_valid || !value_type_valid {
        return Err(invariant(SourceCallableInvariant::InvalidParameterCache(
            parameter.declaration,
        )));
    }
    Ok(())
}

fn validate_cached_return_type(
    store: &CanonicalTypeMapperStore,
    plan: &SourceCallablePlan,
    signature: SignatureId,
) -> Result<(), SourceCallableError> {
    let resolved = store
        .signature(signature)
        .and_then(Signature::resolved_return_type);
    let circular_annotation = store.circular_return_annotation_type(signature);
    let stored_annotation = store.function_signature_return_annotation(signature);
    if plan.return_type.is_ambient_implicit_any() {
        let valid = plan.body_mode.is_ambient()
            && plan.type_parameters.is_empty()
            && stored_annotation.is_none()
            && circular_annotation.is_none()
            && resolved.is_none_or(|type_| {
                store
                    .intrinsic_bootstrap()
                    .is_some_and(|bootstrap| type_ == bootstrap.any_type)
            });
        return if valid {
            Ok(())
        } else {
            Err(invariant(SourceCallableInvariant::InvalidSignatureCache(
                plan.declaration,
            )))
        };
    }
    if plan.return_type.is_inferred() {
        let resolved_valid = resolved.is_none_or(|type_| {
            (plan.type_parameters.is_empty()
                || store
                    .intrinsic_bootstrap()
                    .is_some_and(|bootstrap| type_ == bootstrap.void_type))
                && valid_inferred_source_callable_return_capability(
                    store,
                    plan.array_targets,
                    type_,
                )
        });
        let valid = stored_annotation.is_none()
            && circular_annotation.is_none()
            && (plan.type_parameters.is_empty()
                || valid_inferred_generic_source_callable(store, plan))
            && resolved_valid;
        return if valid {
            Ok(())
        } else {
            Err(invariant(SourceCallableInvariant::InvalidSignatureCache(
                plan.declaration,
            )))
        };
    }
    let Some((return_identity_node, return_null_literal_identity)) =
        plan.return_type.annotation_identity()
    else {
        unreachable!("the inferred return branch returned")
    };
    if resolved.is_none() {
        return if circular_annotation.is_some() {
            Err(invariant(SourceCallableInvariant::InvalidSignatureCache(
                plan.declaration,
            )))
        } else {
            Ok(())
        };
    }
    let resolved = resolved.expect("the unresolved branch returned");
    let annotation =
        cached_annotation_identity(store, return_identity_node, return_null_literal_identity);
    let valid = if !plan.type_parameters.is_empty()
        && (circular_annotation.is_some()
            || !planned_type_parameter_ids(store, plan).is_some_and(|type_parameters| {
                valid_source_generic_mapper_type(
                    store,
                    resolved,
                    &type_parameters,
                    plan.array_targets,
                ) && valid_stored_source_generic_return_annotation(
                    store,
                    return_identity_node,
                    return_null_literal_identity,
                    resolved,
                    plan.generic_return_type_parameter_index
                        .and_then(|index| type_parameters.get(index).copied()),
                    &type_parameters,
                    plan.array_targets,
                )
            })) {
        false
    } else if let Some(circular_annotation) = circular_annotation {
        store.intrinsic_bootstrap().is_some_and(|bootstrap| {
            annotation == Some(circular_annotation) && resolved == bootstrap.any_type
        })
    } else {
        annotation == Some(resolved)
    };
    if !valid {
        return Err(invariant(SourceCallableInvariant::InvalidSignatureCache(
            plan.declaration,
        )));
    }
    Ok(())
}

pub(super) fn cached_annotation_identity(
    store: &CanonicalTypeMapperStore,
    node: NodeRef,
    null_literal_identity: bool,
) -> Option<TypeId> {
    let kind = store.source_node_kind(node)?;
    let bootstrap = store.intrinsic_bootstrap()?;
    if null_literal_identity {
        return Some(bootstrap.null_type);
    }
    let keyword = match kind {
        SyntaxKind::AnyKeyword => Some(bootstrap.any_type),
        SyntaxKind::UnknownKeyword => Some(bootstrap.unknown_type),
        SyntaxKind::StringKeyword => Some(bootstrap.string_type),
        SyntaxKind::NumberKeyword => Some(bootstrap.number_type),
        SyntaxKind::BigIntKeyword => Some(bootstrap.bigint_type),
        SyntaxKind::BooleanKeyword => Some(bootstrap.boolean_type),
        SyntaxKind::SymbolKeyword => Some(bootstrap.es_symbol_type),
        SyntaxKind::VoidKeyword => Some(bootstrap.void_type),
        SyntaxKind::UndefinedKeyword => Some(bootstrap.undefined_type),
        SyntaxKind::NullKeyword => Some(bootstrap.null_type),
        SyntaxKind::NeverKeyword => Some(bootstrap.never_type),
        SyntaxKind::ObjectKeyword => Some(bootstrap.non_primitive_type),
        SyntaxKind::IntrinsicKeyword => Some(bootstrap.intrinsic_marker_type),
        _ => None,
    };
    keyword.or_else(|| {
        store
            .type_node_links(node)
            .and_then(|links| links.resolved_type)
    })
}

fn peel_parenthesized_type(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    mut node: NodeRef,
) -> Result<NodeRef, SourceCallableError> {
    loop {
        let record = preflight_node(store, host, node)?;
        let NodeData::ParenthesizedTypeNode(parenthesized) = &record.data else {
            return Ok(node);
        };
        if record.kind != SyntaxKind::ParenthesizedType {
            return Err(invariant(SourceCallableInvariant::InvalidSyntax(node)));
        }
        let inner = NodeRef::new(node.arena, node.file, parenthesized.type_);
        if preflight_node(store, host, inner)?.parent != Some(node.node) {
            return Err(invariant(SourceCallableInvariant::InvalidSyntax(node)));
        }
        node = inner;
    }
}

fn is_null_literal_type(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    node: NodeRef,
) -> Result<bool, SourceCallableError> {
    let record = preflight_node(store, host, node)?;
    let NodeData::LiteralTypeNode(literal) = &record.data else {
        return Ok(false);
    };
    if record.kind != SyntaxKind::LiteralType {
        return Err(invariant(SourceCallableInvariant::InvalidSyntax(node)));
    }
    let literal = NodeRef::new(node.arena, node.file, literal.literal);
    let literal_record = preflight_node(store, host, literal)?;
    if literal_record.parent != Some(node.node) || literal_record.range != record.range {
        return Err(invariant(SourceCallableInvariant::InvalidSyntax(node)));
    }
    Ok(literal_record.kind == SyntaxKind::NullKeyword
        && matches!(literal_record.data, NodeData::KeywordExpression(_)))
}

pub(super) fn valid_optional_type(
    store: &CanonicalTypeMapperStore,
    array_targets: Option<CanonicalArrayTargets>,
    base: TypeId,
    resolved: TypeId,
) -> bool {
    let Some(undefined) = store
        .intrinsic_bootstrap()
        .map(|bootstrap| bootstrap.undefined_type)
    else {
        return false;
    };
    let Some(base_record) = store.type_payload(base) else {
        return false;
    };
    if base == undefined
        || base_record
            .flags()
            .intersects(TypeFlags::ANY | TypeFlags::UNKNOWN)
    {
        return resolved == base;
    }
    let mut expected = match base_record.data() {
        TypeData::Union(union) if union.union.types.contains(&undefined) => {
            let valid = match array_targets {
                Some(targets) => store.validate_union_constituent_with_array_targets(targets, base),
                None => store.validate_union_constituent(base),
            };
            return resolved == base && valid.is_ok();
        }
        TypeData::Union(_) => {
            return store
                .validate_optional_union_of_union_result(array_targets, base, undefined, resolved)
                .is_ok();
        }
        _ => vec![base],
    };
    expected.retain(|type_| {
        store
            .type_payload(*type_)
            .is_some_and(|record| !record.flags().intersects(TypeFlags::NEVER))
    });
    if !expected.contains(&undefined) {
        expected.push(undefined);
    }
    if expected.len() == 1 {
        return resolved == expected[0];
    }
    let Some(TypeData::Union(union)) = store.type_payload(resolved).map(TypeRecord::data) else {
        return false;
    };
    let valid_union = match array_targets {
        Some(targets) => {
            store.validate_cached_union_result_with_array_targets(targets, resolved, None)
        }
        None => store.validate_cached_union_result(resolved, None),
    };
    expected.len() == union.union.types.len()
        && expected
            .iter()
            .all(|expected| union.union.types.contains(expected))
        && valid_union.is_ok()
}

const fn invariant(error: SourceCallableInvariant) -> SourceCallableError {
    SourceCallableError::Invariant(error)
}

#[cfg(test)]
mod tests {
    use ts_ast::{FileId, NodeData, NodeRef};
    use ts_binder::{
        BoundFile, CanonicalBinder, CanonicalModuleState, CanonicalNameResolverOptions,
        CanonicalSourceFileFacts, CanonicalSourceLanguage, EscapedName,
    };
    use ts_parser::{
        ParseResult, parse_javascript_source_file, parse_jsx_source_file, parse_source_file,
    };

    use super::*;
    use crate::semantic::{
        CanonicalCheckerContext, CanonicalCheckerDiagnostics, CanonicalCheckerOptions,
        DeclaredTypeLinks, IntrinsicBootstrapOptions,
        global_types::initialize_global_library_types,
        jsdoc::resolve_planned_jsdoc_callback_signature,
        production::GlobalMergeCompletion,
        source::{SourceCheckError, UnsupportedSourceSyntax},
        source_functions::SourceFunctionUnsupported,
        type_nodes::{CanonicalTypeQuery, CanonicalTypeQueryOptions, TypeNodeUnavailable},
    };

    struct QueryFixture {
        parsed: ParseResult,
        file: FileId,
        bound: BoundFile,
        store: CanonicalTypeMapperStore,
    }

    impl QueryFixture {
        fn new(source: &str, file: FileId) -> Self {
            Self::with_source_facts(source, file, false, CanonicalModuleState::Script)
        }

        fn with_source_facts(
            source: &str,
            file: FileId,
            declaration_file: bool,
            module_state: CanonicalModuleState,
        ) -> Self {
            Self::with_source_language(
                source,
                file,
                declaration_file,
                module_state,
                CanonicalSourceLanguage::TypeScript,
            )
        }

        fn javascript(source: &str, file: FileId) -> Self {
            Self::with_source_language(
                source,
                file,
                false,
                CanonicalModuleState::Script,
                CanonicalSourceLanguage::JavaScript,
            )
        }

        fn jsx(source: &str, file: FileId) -> Self {
            Self::with_parsed_source(
                parse_jsx_source_file(source),
                file,
                false,
                CanonicalModuleState::Script,
                CanonicalSourceLanguage::TypeScript,
            )
        }

        fn with_source_language(
            source: &str,
            file: FileId,
            declaration_file: bool,
            module_state: CanonicalModuleState,
            language: CanonicalSourceLanguage,
        ) -> Self {
            Self::with_parsed_source(
                parse_source_file(source),
                file,
                declaration_file,
                module_state,
                language,
            )
        }

        fn with_parsed_source(
            parsed: ParseResult,
            file: FileId,
            declaration_file: bool,
            module_state: CanonicalModuleState,
            language: CanonicalSourceLanguage,
        ) -> Self {
            assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
            let mut binder = CanonicalBinder::new();
            binder
                .bind_source_file_with_facts(
                    &parsed.arena,
                    parsed.source_file,
                    file,
                    CanonicalSourceFileFacts::new(
                        EscapedName::source(if declaration_file {
                            "\"/project/source_generic_query.d.ts\""
                        } else {
                            "\"/project/source_generic_query.ts\""
                        }),
                        language,
                        declaration_file,
                        module_state,
                    ),
                )
                .unwrap();
            match language {
                CanonicalSourceLanguage::TypeScript => binder
                    .bind_typescript_declaration_slice(&parsed.arena, file)
                    .unwrap(),
                CanonicalSourceLanguage::JavaScript => binder
                    .bind_javascript_declaration_slice(&parsed.arena, file)
                    .unwrap(),
            };
            let (symbols, mut files) = binder.finish().try_into_parts().unwrap();
            let bound = files.remove(&file).unwrap();
            let mut store = CanonicalTypeMapperStore::from_symbol_store(symbols);
            assert!(
                store
                    .register_source_file(&parsed.arena, parsed.source_file, file)
                    .is_some()
            );
            store
                .initialize_intrinsic_bootstrap(IntrinsicBootstrapOptions::default())
                .unwrap();
            Self {
                parsed,
                file,
                bound,
                store,
            }
        }

        fn generic_parts(&self) -> (NodeRef, NodeRef, NodeRef, NodeRef) {
            generic_function_parts(&self.parsed, self.file)
        }

        fn declaration_and_type_parameter(&self) -> (NodeRef, NodeRef) {
            let (declaration, type_parameter, _, _) = self.generic_parts();
            (declaration, type_parameter)
        }

        fn query_callable(
            &mut self,
            declaration: NodeRef,
            owner: SemanticSymbolId,
            diagnostics: &mut CanonicalCheckerDiagnostics,
        ) -> Result<TypeId, DeclaredTypeError> {
            let host = DeclaredTypeHost::new_after_global_merge(
                [(&self.parsed.arena, &self.bound)],
                GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
            )
            .unwrap();
            CanonicalTypeQuery::new(
                &mut self.store,
                &host,
                CanonicalTypeQueryOptions::default(),
                diagnostics,
            )?
            .get_type_of_source_callable(declaration, owner)
        }

        fn query_return(
            &mut self,
            signature: SignatureId,
            diagnostics: &mut CanonicalCheckerDiagnostics,
        ) -> Result<TypeId, DeclaredTypeError> {
            let host = DeclaredTypeHost::new_after_global_merge(
                [(&self.parsed.arena, &self.bound)],
                GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
            )
            .unwrap();
            CanonicalTypeQuery::new(
                &mut self.store,
                &host,
                CanonicalTypeQueryOptions::default(),
                diagnostics,
            )?
            .get_return_type_of_signature(signature)
        }

        fn query_type_node(
            &mut self,
            node: NodeRef,
            diagnostics: &mut CanonicalCheckerDiagnostics,
        ) -> Result<TypeId, DeclaredTypeError> {
            let host = DeclaredTypeHost::new_after_global_merge(
                [(&self.parsed.arena, &self.bound)],
                GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
            )
            .unwrap();
            CanonicalTypeQuery::new(
                &mut self.store,
                &host,
                CanonicalTypeQueryOptions::default(),
                diagnostics,
            )?
            .get_type_from_type_node(node)
        }

        fn query_type_parameter_result(
            &mut self,
            node: NodeRef,
            diagnostics: &mut CanonicalCheckerDiagnostics,
        ) -> Result<TypeId, DeclaredTypeError> {
            let error = match self.query_type_node(node, diagnostics) {
                Ok(type_) => return Ok(type_),
                Err(error) => error,
            };
            if !matches!(
                error,
                DeclaredTypeError::TypeNodeUnavailable(
                    TypeNodeUnavailable::MissingTypeReference(reference)
                        | TypeNodeUnavailable::InvalidTypeReference(reference)
                ) if reference == node
            ) {
                return Err(error);
            }
            let Some(NodeData::TypeReferenceNode(reference)) =
                self.parsed.arena.get(node.node).map(|record| &record.data)
            else {
                return Err(error);
            };
            let Some(NodeData::Identifier(name)) = self
                .parsed
                .arena
                .get(reference.type_name)
                .map(|record| &record.data)
            else {
                return Err(error);
            };
            let target = self.parsed.arena.iter().find_map(|(_, record)| {
                let NodeData::TypeAliasDeclaration(alias) = &record.data else {
                    return None;
                };
                let NodeData::Identifier(alias_name) = &self.parsed.arena.get(alias.name)?.data
                else {
                    return None;
                };
                (alias_name.text == name.text).then_some(NodeRef::new(
                    node.arena,
                    node.file,
                    alias.type_,
                ))
            });
            match target {
                Some(target) => self.query_type_node(target, diagnostics),
                None => Err(error),
            }
        }
    }

    fn bind_context(parsed: &ParseResult, file: FileId) -> CanonicalCheckerContext<'_> {
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source("\"/project/source_generic.ts\""),
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
            [(file, &parsed.arena)].into_iter().collect(),
            CanonicalCheckerOptions::default(),
        )
        .unwrap()
    }

    const WRAPPER_METHOD_LIBRARY: &str = concat!(
        "interface IArguments {} ",
        "interface Array<T> {} ",
        "interface Object {} ",
        "interface Function {} ",
        "interface String { toLowerCase(): string; } ",
        "interface Number { toFixed(fractionDigits?: number): string; } ",
        "interface Boolean {} ",
        "interface RegExp {} ",
        "interface ReadonlyArray<T> {} ",
        "interface ThisType<T> {} ",
    );

    fn wrapper_method_fixture(
        source: &str,
        strict_null_checks: bool,
        is_default_library: bool,
    ) -> (QueryFixture, CanonicalGlobalTypes) {
        let parsed = parse_source_file(source);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(if strict_null_checks { 1_906 } else { 1_905 });
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new_with_default_library(
                    EscapedName::source("\"/project/lib.wrapper.d.ts\""),
                    CanonicalSourceLanguage::TypeScript,
                    true,
                    is_default_library,
                    CanonicalModuleState::Script,
                ),
            )
            .unwrap();
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
        let (symbols, mut files) = binder.finish().try_into_parts().unwrap();
        let bound = files.remove(&file).unwrap();
        let mut store = CanonicalTypeMapperStore::from_symbol_store(symbols);
        assert!(
            store
                .register_source_file(&parsed.arena, parsed.source_file, file)
                .is_some()
        );
        store
            .initialize_intrinsic_bootstrap(IntrinsicBootstrapOptions {
                strict_null_checks,
                exact_optional_property_types: false,
            })
            .unwrap();
        let globals = store.intrinsic_bootstrap().unwrap().globals;
        let locals = bound.locals(bound.source_file()).unwrap();
        let symbols = store
            .symbol_table(locals)
            .unwrap()
            .iter()
            .map(|(_, symbol)| symbol)
            .collect::<Vec<_>>();
        for symbol in symbols {
            store.merge_global_symbol(globals, symbol).unwrap();
        }
        let global_types = {
            let host = DeclaredTypeHost::new_after_global_merge(
                [(&parsed.arena, &bound)],
                GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
            )
            .unwrap();
            initialize_global_library_types(&mut store, &host, globals, false).unwrap()
        };
        (
            QueryFixture {
                parsed,
                file,
                bound,
                store,
            },
            global_types,
        )
    }

    fn generic_function_parts(
        parsed: &ParseResult,
        file: FileId,
    ) -> (NodeRef, NodeRef, NodeRef, NodeRef) {
        let source = parsed.arena.get(parsed.source_file).unwrap();
        let NodeData::SourceFile(source) = &source.data else {
            panic!("expected source file")
        };
        for statement in &source.statements.nodes {
            let record = parsed.arena.get(*statement).unwrap();
            let NodeData::FunctionDeclaration(function) = &record.data else {
                continue;
            };
            let type_parameters = function
                .type_parameters
                .as_ref()
                .expect("expected generic function");
            let parameter = parsed
                .arena
                .get(function.parameters.nodes[0])
                .expect("expected generic parameter");
            let NodeData::ParameterDeclaration(parameter) = &parameter.data else {
                panic!("expected parameter declaration")
            };
            return (
                NodeRef::new(parsed.arena.id(), file, *statement),
                NodeRef::new(parsed.arena.id(), file, type_parameters.nodes[0]),
                NodeRef::new(
                    parsed.arena.id(),
                    file,
                    parameter.type_.expect("expected parameter annotation"),
                ),
                NodeRef::new(
                    parsed.arena.id(),
                    file,
                    function.type_.expect("expected return annotation"),
                ),
            );
        }
        panic!("expected function declaration")
    }

    fn function_and_type_parameter(parsed: &ParseResult, file: FileId) -> (NodeRef, NodeRef) {
        parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                let NodeData::FunctionDeclaration(function) = &record.data else {
                    return None;
                };
                let type_parameter = *function.type_parameters.as_ref()?.nodes.first()?;
                Some((
                    NodeRef::new(parsed.arena.id(), file, node),
                    NodeRef::new(parsed.arena.id(), file, type_parameter),
                ))
            })
            .expect("expected a generic function declaration")
    }

    fn publication_state(store: &CanonicalTypeMapperStore) -> (usize, usize, [usize; 5], usize) {
        (
            store.types().len(),
            store.signature_len(),
            store.source_callable_provenance_lengths(),
            store.callable_signature_parameter_types_len(),
        )
    }

    #[derive(Debug, Eq, PartialEq)]
    struct GenericTransactionState {
        types: usize,
        signatures: usize,
        symbols: usize,
        mappers: usize,
        cached_signatures: usize,
        source_callable_provenance: [usize; 5],
        callable_parameter_types: usize,
        checker_links: [usize; 26],
    }

    fn generic_transaction_state(store: &CanonicalTypeMapperStore) -> GenericTransactionState {
        GenericTransactionState {
            types: store.type_len(),
            signatures: store.signature_len(),
            symbols: store.symbol_len(),
            mappers: store.mapper_len(),
            cached_signatures: store.cached_signature_len(),
            source_callable_provenance: store.source_callable_provenance_lengths(),
            callable_parameter_types: store.callable_signature_parameter_types_len(),
            checker_links: store.checker_link_allocated_lengths(),
        }
    }

    #[test]
    fn anonymous_function_expressions_preserve_binder_ownership_and_warm_signatures() {
        for (index, javascript) in [false, true].into_iter().enumerate() {
            let file = FileId::new(1_900 + u32::try_from(index).unwrap());
            let mut fixture = if javascript {
                QueryFixture::javascript("const value = function () {};", file)
            } else {
                QueryFixture::new("const value = function () {};", file)
            };
            let declaration = fixture
                .parsed
                .arena
                .iter()
                .find_map(|(node, record)| {
                    (record.kind == SyntaxKind::FunctionExpression).then_some(NodeRef::new(
                        fixture.parsed.arena.id(),
                        file,
                        node,
                    ))
                })
                .unwrap();
            let owner = fixture.bound.symbol(declaration).unwrap();
            let host = DeclaredTypeHost::new_after_global_merge(
                [(&fixture.parsed.arena, &fixture.bound)],
                GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
            )
            .unwrap();
            let before = publication_state(&fixture.store);

            let plan =
                plan_source_callable(&fixture.store, &host, declaration, owner, None).unwrap();
            assert_eq!(plan.family, SourceCallableFamily::ArrowFunction);
            assert_eq!(plan.declaration, declaration);
            assert_eq!(plan.owner_symbol, owner);
            assert_eq!(publication_state(&fixture.store), before);

            let (callable, signature) =
                materialize_anonymous_source_function_expression(&mut fixture.store, &plan)
                    .unwrap();
            let void = fixture.store.intrinsic_bootstrap().unwrap().void_type;
            assert_eq!(
                publish_inferred_source_callable_return(&mut fixture.store, &plan, signature, void,),
                Ok(void),
            );
            assert_eq!(
                fixture.store.source_callable_type_for_owner(owner),
                Some(callable),
            );
            assert_eq!(
                fixture
                    .store
                    .source_callable_type_for_declaration(declaration),
                Some(callable),
            );
            assert_eq!(
                fixture
                    .store
                    .source_callable_provenance(callable)
                    .map(|provenance| provenance.signature),
                Some(signature),
            );
            assert_eq!(
                fixture
                    .store
                    .signature(signature)
                    .unwrap()
                    .resolved_return_type(),
                Some(void),
            );
            assert!(matches!(
                validate_stored_source_callable(&fixture.store, callable),
                StoredSourceCallableValidation::Valid(_)
            ));

            let warm = publication_state(&fixture.store);
            assert_eq!(
                materialize_anonymous_source_function_expression(&mut fixture.store, &plan),
                Ok((callable, signature)),
            );
            assert_eq!(publication_state(&fixture.store), warm);
        }
    }

    #[test]
    fn anonymous_function_expression_plans_reject_names_and_corrupt_owners() {
        let named = QueryFixture::new("const value = function inner() {};", FileId::new(1_902));
        let declaration = named
            .parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::FunctionExpression).then_some(NodeRef::new(
                    named.parsed.arena.id(),
                    named.file,
                    node,
                ))
            })
            .unwrap();
        let owner = named.bound.symbol(declaration).unwrap();
        let host = DeclaredTypeHost::new_after_global_merge(
            [(&named.parsed.arena, &named.bound)],
            GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
        )
        .unwrap();
        assert!(matches!(
            plan_source_callable(&named.store, &host, declaration, owner, None),
            Err(SourceCallableError::Unsupported(
                SourceCallableUnsupported::OverloadDeclaration(_)
            ))
        ));

        let mut invalid = QueryFixture::new("const value = function () {};", FileId::new(1_903));
        let declaration = invalid
            .parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::FunctionExpression).then_some(NodeRef::new(
                    invalid.parsed.arena.id(),
                    invalid.file,
                    node,
                ))
            })
            .unwrap();
        let owner = invalid.bound.symbol(declaration).unwrap();
        assert!(invalid.store.set_symbol_flags(
            owner,
            SymbolFlags::FUNCTION | SymbolFlags::ASSIGNMENT,
            CheckFlags::NONE,
        ));
        let host = DeclaredTypeHost::new_after_global_merge(
            [(&invalid.parsed.arena, &invalid.bound)],
            GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
        )
        .unwrap();
        assert_eq!(
            plan_source_callable(&invalid.store, &host, declaration, owner, None),
            Err(SourceCallableError::Invariant(
                SourceCallableInvariant::InvalidOwnerSymbol(declaration),
            )),
        );
    }

    #[test]
    fn generic_source_predicates_and_assertions_preserve_type_parameter_identity() {
        for (index, (source, expected_kind, minimum_arguments, narrows_type_parameter)) in [
            (
                "declare function select<Value>(value: Value): value is Value;",
                TypePredicateKind::Identifier,
                1,
                true,
            ),
            (
                "declare function assertValue<Value>(value: Value): asserts value is Value;",
                TypePredicateKind::AssertsIdentifier,
                1,
                true,
            ),
            (
                "declare function assertTruthy<Value>(value: Value): asserts value;",
                TypePredicateKind::AssertsIdentifier,
                1,
                false,
            ),
            (
                "declare function selectOptional<Value>(value?: Value): value is Value;",
                TypePredicateKind::Identifier,
                0,
                true,
            ),
        ]
        .into_iter()
        .enumerate()
        {
            let mut fixture =
                QueryFixture::new(source, FileId::new(9_870 + u32::try_from(index).unwrap()));
            let declaration = fixture
                .parsed
                .arena
                .iter()
                .find_map(|(node, record)| {
                    (record.kind == SyntaxKind::FunctionDeclaration).then_some(NodeRef::new(
                        fixture.parsed.arena.id(),
                        fixture.file,
                        node,
                    ))
                })
                .unwrap();
            let owner = fixture.bound.symbol(declaration).unwrap();
            let mut diagnostics = CanonicalCheckerDiagnostics::default();
            let callable = fixture
                .query_callable(declaration, owner, &mut diagnostics)
                .unwrap();
            let signature = fixture
                .store
                .source_callable_provenance(callable)
                .unwrap()
                .signature;
            let expected_return = {
                let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
                if expected_kind == TypePredicateKind::Identifier {
                    bootstrap.boolean_type
                } else {
                    bootstrap.void_type
                }
            };
            assert_eq!(
                fixture.query_return(signature, &mut diagnostics),
                Ok(expected_return),
            );
            let record = fixture.store.signature(signature).unwrap();
            let [type_parameter] = record.type_parameters() else {
                panic!("the generic source predicate must retain one type parameter")
            };
            let predicate = record
                .resolved_type_predicate()
                .and_then(|predicate| fixture.store.type_predicate(predicate))
                .unwrap();
            assert_eq!(record.min_argument_count(), minimum_arguments);
            assert_eq!(predicate.kind(), expected_kind);
            assert_eq!(predicate.parameter_index(), 0);
            assert_eq!(predicate.parameter_name(), "value");
            assert_eq!(
                predicate.type_id(),
                narrows_type_parameter.then_some(*type_parameter),
            );
            assert!(matches!(
                validate_stored_source_callable(&fixture.store, callable),
                StoredSourceCallableValidation::Valid(_),
            ));

            let warm = (
                generic_transaction_state(&fixture.store),
                fixture.store.type_predicate_len(),
            );
            assert_eq!(
                fixture.query_return(signature, &mut diagnostics),
                Ok(expected_return),
            );
            assert_eq!(
                fixture.query_callable(declaration, owner, &mut diagnostics),
                Ok(callable),
            );
            assert_eq!(
                (
                    generic_transaction_state(&fixture.store),
                    fixture.store.type_predicate_len(),
                ),
                warm,
            );
            assert!(diagnostics.is_empty());
        }
    }

    #[test]
    fn source_type_predicates_publish_exact_signature_metadata_cold_and_warm() {
        for (index, (source, expected_kind, expected_parameter, has_narrowed_type)) in [
            (
                "declare function isString(value: unknown): value is string;",
                TypePredicateKind::Identifier,
                0,
                true,
            ),
            (
                "declare function assertString(value: unknown): asserts value is string;",
                TypePredicateKind::AssertsIdentifier,
                0,
                true,
            ),
            (
                "declare function assertTruth(value: unknown): asserts value;",
                TypePredicateKind::AssertsIdentifier,
                0,
                false,
            ),
            (
                "declare function selectString(first: number, value: unknown): value is string;",
                TypePredicateKind::Identifier,
                1,
                true,
            ),
        ]
        .into_iter()
        .enumerate()
        {
            let mut fixture =
                QueryFixture::new(source, FileId::new(9_850 + u32::try_from(index).unwrap()));
            let declaration = fixture
                .parsed
                .arena
                .iter()
                .find_map(|(node, record)| {
                    (record.kind == SyntaxKind::FunctionDeclaration).then_some(NodeRef::new(
                        fixture.parsed.arena.id(),
                        fixture.file,
                        node,
                    ))
                })
                .unwrap();
            let owner = fixture.bound.symbol(declaration).unwrap();
            let mut diagnostics = CanonicalCheckerDiagnostics::default();
            let callable = fixture
                .query_callable(declaration, owner, &mut diagnostics)
                .unwrap();
            let signature = fixture
                .store
                .source_callable_provenance(callable)
                .unwrap()
                .signature;
            assert!(
                fixture
                    .store
                    .signature(signature)
                    .unwrap()
                    .resolved_type_predicate()
                    .is_none()
            );

            let expected_return = {
                let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
                if expected_kind == TypePredicateKind::Identifier {
                    bootstrap.boolean_type
                } else {
                    bootstrap.void_type
                }
            };
            assert_eq!(
                fixture.query_return(signature, &mut diagnostics),
                Ok(expected_return),
            );
            let predicate = fixture
                .store
                .signature(signature)
                .and_then(Signature::resolved_type_predicate)
                .and_then(|predicate| fixture.store.type_predicate(predicate))
                .unwrap();
            assert_eq!(predicate.kind(), expected_kind);
            assert_eq!(predicate.parameter_index(), expected_parameter);
            assert_eq!(predicate.parameter_name(), "value");
            assert_eq!(
                predicate.type_id(),
                has_narrowed_type
                    .then_some(fixture.store.intrinsic_bootstrap().unwrap().string_type),
            );
            assert!(matches!(
                validate_stored_source_callable(&fixture.store, callable),
                StoredSourceCallableValidation::Valid(_)
            ));
            assert!(diagnostics.is_empty());

            let warm = (
                generic_transaction_state(&fixture.store),
                fixture.store.type_predicate_len(),
            );
            assert_eq!(
                fixture.query_return(signature, &mut diagnostics),
                Ok(expected_return),
            );
            assert_eq!(
                fixture.query_callable(declaration, owner, &mut diagnostics),
                Ok(callable),
            );
            assert_eq!(
                (
                    generic_transaction_state(&fixture.store),
                    fixture.store.type_predicate_len(),
                ),
                warm,
            );
        }
    }

    #[test]
    fn source_type_predicates_reject_foreign_parameters_and_forged_narrowing() {
        let mut invalid = QueryFixture::new(
            "declare function isString(value: unknown): other is string;",
            FileId::new(9_854),
        );
        let declaration = invalid
            .parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::FunctionDeclaration).then_some(NodeRef::new(
                    invalid.parsed.arena.id(),
                    invalid.file,
                    node,
                ))
            })
            .unwrap();
        let owner = invalid.bound.symbol(declaration).unwrap();
        let before = generic_transaction_state(&invalid.store);
        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        assert!(
            invalid
                .query_callable(declaration, owner, &mut diagnostics)
                .is_err()
        );
        assert_eq!(generic_transaction_state(&invalid.store), before);

        let mut forged = QueryFixture::new(
            "declare function isString(value: unknown): value is string;",
            FileId::new(9_855),
        );
        let declaration = forged
            .parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::FunctionDeclaration).then_some(NodeRef::new(
                    forged.parsed.arena.id(),
                    forged.file,
                    node,
                ))
            })
            .unwrap();
        let owner = forged.bound.symbol(declaration).unwrap();
        let callable = forged
            .query_callable(declaration, owner, &mut diagnostics)
            .unwrap();
        let signature = forged
            .store
            .source_callable_provenance(callable)
            .unwrap()
            .signature;
        forged.query_return(signature, &mut diagnostics).unwrap();
        let number = forged.store.intrinsic_bootstrap().unwrap().number_type;
        let wrong = forged
            .store
            .alloc_type_predicate(TypePredicateKind::Identifier, 0, "value", Some(number))
            .unwrap();
        assert!(
            forged
                .store
                .set_signature_resolved_type_predicate(signature, Some(wrong))
        );
        let before = (
            generic_transaction_state(&forged.store),
            forged.store.type_predicate_len(),
        );

        assert!(matches!(
            forged.query_return(signature, &mut diagnostics),
            Err(DeclaredTypeError::TypeNodeUnavailable(
                TypeNodeUnavailable::InvalidFunctionSignature(cached),
            )) if cached == signature
        ));
        assert_eq!(
            (
                generic_transaction_state(&forged.store),
                forged.store.type_predicate_len(),
            ),
            before,
        );
    }

    #[test]
    fn default_library_wrapper_methods_publish_exact_signatures_and_replay_warm() {
        for (strict_null_checks, transient_owner) in [(false, false), (true, false), (false, true)]
        {
            let (mut fixture, global_types) =
                wrapper_method_fixture(WRAPPER_METHOD_LIBRARY, strict_null_checks, true);
            if transient_owner {
                for wrapper in [global_types.number_type, global_types.string_type] {
                    let owner = fixture
                        .store
                        .type_payload(wrapper)
                        .unwrap()
                        .symbol()
                        .unwrap();
                    let flags = fixture.store.symbol(owner).unwrap().flags();
                    assert!(fixture.store.set_symbol_flags(
                        owner,
                        flags | SymbolFlags::TRANSIENT,
                        CheckFlags::NONE,
                    ));
                }
            }
            let (number, string) = {
                let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
                (bootstrap.number_type, bootstrap.string_type)
            };
            let host = DeclaredTypeHost::new_after_global_merge(
                [(&fixture.parsed.arena, &fixture.bound)],
                GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
            )
            .unwrap();

            let (fixed_symbol, fixed_type) = materialize_global_wrapper_method(
                &mut fixture.store,
                &host,
                &global_types,
                number,
                "toFixed",
            )
            .unwrap()
            .unwrap();
            let fixed_declaration = fixture
                .store
                .symbol(fixed_symbol)
                .unwrap()
                .value_declaration()
                .unwrap();
            let fixed_signature = fixture
                .store
                .signature_links(fixed_declaration)
                .and_then(|links| links.resolved_signature.signature())
                .unwrap();
            let signature = fixture.store.signature(fixed_signature).unwrap();
            assert_eq!(signature.min_argument_count(), 0);
            assert_eq!(signature.resolved_return_type(), Some(string));
            let [parameter] = signature.parameters() else {
                panic!("Number.toFixed must retain its binder-owned parameter")
            };
            let parameter_type = fixture
                .store
                .value_symbol_links(*parameter)
                .and_then(|links| links.resolved_type)
                .unwrap();
            assert_eq!(
                fixture
                    .store
                    .callable_signature_parameter_types(fixed_signature),
                Some([parameter_type].as_slice())
            );
            if strict_null_checks {
                assert!(valid_optional_type(
                    &fixture.store,
                    Some(CanonicalArrayTargets::from_global_types(&global_types)),
                    number,
                    parameter_type,
                ));
                assert_ne!(parameter_type, number);
            } else {
                assert_eq!(parameter_type, number);
            }

            let (lower_symbol, lower_type) = materialize_global_wrapper_method(
                &mut fixture.store,
                &host,
                &global_types,
                string,
                "toLowerCase",
            )
            .unwrap()
            .unwrap();
            let lower_declaration = fixture
                .store
                .symbol(lower_symbol)
                .unwrap()
                .value_declaration()
                .unwrap();
            let lower_signature = fixture
                .store
                .signature_links(lower_declaration)
                .and_then(|links| links.resolved_signature.signature())
                .unwrap();
            assert!(
                fixture
                    .store
                    .signature(lower_signature)
                    .unwrap()
                    .parameters()
                    .is_empty()
            );
            assert_eq!(
                fixture
                    .store
                    .callable_signature_parameter_types(lower_signature),
                Some([].as_slice())
            );
            assert_eq!(
                fixture
                    .store
                    .signature(lower_signature)
                    .unwrap()
                    .resolved_return_type(),
                Some(string)
            );

            let warm = generic_transaction_state(&fixture.store);
            assert_eq!(
                materialize_global_wrapper_method(
                    &mut fixture.store,
                    &host,
                    &global_types,
                    number,
                    "toFixed",
                ),
                Ok(Some((fixed_symbol, fixed_type)))
            );
            assert_eq!(
                materialize_global_wrapper_method(
                    &mut fixture.store,
                    &host,
                    &global_types,
                    string,
                    "toLowerCase",
                ),
                Ok(Some((lower_symbol, lower_type)))
            );
            assert_eq!(generic_transaction_state(&fixture.store), warm);
        }
    }

    #[test]
    fn wrapper_methods_reject_corrupted_parameter_links_without_publication() {
        let (mut fixture, global_types) =
            wrapper_method_fixture(WRAPPER_METHOD_LIBRARY, true, true);
        let number = fixture.store.intrinsic_bootstrap().unwrap().number_type;
        let host = DeclaredTypeHost::new_after_global_merge(
            [(&fixture.parsed.arena, &fixture.bound)],
            GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
        )
        .unwrap();
        let (method, _) = materialize_global_wrapper_method(
            &mut fixture.store,
            &host,
            &global_types,
            number,
            "toFixed",
        )
        .unwrap()
        .unwrap();
        let declaration = fixture
            .store
            .symbol(method)
            .unwrap()
            .value_declaration()
            .unwrap();
        let signature = fixture
            .store
            .signature_links(declaration)
            .and_then(|links| links.resolved_signature.signature())
            .unwrap();
        let parameter = fixture.store.signature(signature).unwrap().parameters()[0];
        let original = fixture.store.value_symbol_links(parameter).unwrap().clone();
        assert!(fixture.store.set_value_symbol_links(
            parameter,
            ValueSymbolLinks {
                resolved_type: Some(number),
                ..ValueSymbolLinks::default()
            },
        ));
        let poisoned = generic_transaction_state(&fixture.store);

        assert!(matches!(
            materialize_global_wrapper_method(
                &mut fixture.store,
                &host,
                &global_types,
                number,
                "toFixed",
            ),
            Err(SourceCallableError::Invariant(
                SourceCallableInvariant::InvalidParameterCache(_)
            ))
        ));
        assert_eq!(generic_transaction_state(&fixture.store), poisoned);

        assert!(fixture.store.set_value_symbol_links(parameter, original));
        assert!(
            materialize_global_wrapper_method(
                &mut fixture.store,
                &host,
                &global_types,
                number,
                "toFixed",
            )
            .unwrap()
            .is_some()
        );
    }

    #[test]
    fn wrapper_methods_require_default_library_provenance() {
        let (mut fixture, global_types) =
            wrapper_method_fixture(WRAPPER_METHOD_LIBRARY, false, false);
        let number = fixture.store.intrinsic_bootstrap().unwrap().number_type;
        let host = DeclaredTypeHost::new_after_global_merge(
            [(&fixture.parsed.arena, &fixture.bound)],
            GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
        )
        .unwrap();
        let before = generic_transaction_state(&fixture.store);

        assert!(matches!(
            materialize_global_wrapper_method(
                &mut fixture.store,
                &host,
                &global_types,
                number,
                "toFixed",
            ),
            Err(SourceCallableError::Invariant(
                SourceCallableInvariant::InvalidOwnerSymbol(_)
            ))
        ));
        assert_eq!(generic_transaction_state(&fixture.store), before);
        assert_eq!(
            materialize_global_wrapper_method(
                &mut fixture.store,
                &host,
                &global_types,
                number,
                "toLowerCase",
            ),
            Ok(None)
        );
    }

    #[test]
    fn generic_function_accepts_authenticated_named_interface_keyof_constraint() {
        let mut fixture = QueryFixture::new(
            concat!(
                "interface Choices { left: string; right: number } ",
                "function choose<T extends keyof Choices>(value: T): boolean { return true; }",
            ),
            FileId::new(1_907),
        );
        let (declaration, type_parameter) = fixture.declaration_and_type_parameter();
        let owner = fixture.bound.symbol(declaration).unwrap();
        let globals = fixture.store.intrinsic_bootstrap().unwrap().globals;
        let interface = fixture
            .bound
            .locals(fixture.bound.source_file())
            .and_then(|locals| fixture.store.symbol_table(locals))
            .and_then(|locals| locals.get_source("Choices"))
            .unwrap();
        assert_eq!(
            fixture.store.merge_global_symbol(globals, interface),
            Ok(interface)
        );
        let constraint = {
            let NodeData::TypeParameterDeclaration(parameter) =
                &fixture.parsed.arena.get(type_parameter.node).unwrap().data
            else {
                panic!("the fixture must contain a constrained type parameter")
            };
            NodeRef::new(
                type_parameter.arena,
                type_parameter.file,
                parameter.constraint.unwrap(),
            )
        };
        let host = DeclaredTypeHost::new_after_global_merge(
            [(&fixture.parsed.arena, &fixture.bound)],
            GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
        )
        .unwrap();
        let before = generic_transaction_state(&fixture.store);

        assert!(
            exact_named_interface_keyof_bound(&fixture.store, &host, constraint).unwrap(),
            "the cold named-interface keyof proof must accept canonical interface field kinds",
        );
        assert_eq!(generic_transaction_state(&fixture.store), before);
        let plan = plan_source_callable(&fixture.store, &host, declaration, owner, None).unwrap();
        assert_eq!(plan.type_parameters.len(), 1);
        assert_eq!(plan.type_parameters[0].constraint, Some(constraint));
        assert_eq!(generic_transaction_state(&fixture.store), before);

        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        let type_ = fixture
            .query_callable(declaration, owner, &mut diagnostics)
            .unwrap();
        assert!(matches!(
            validate_stored_source_callable(&fixture.store, type_),
            StoredSourceCallableValidation::Valid(_)
        ));
        assert!(diagnostics.is_empty());
        let warm = generic_transaction_state(&fixture.store);
        assert_eq!(
            fixture.query_callable(declaration, owner, &mut diagnostics),
            Ok(type_)
        );
        assert_eq!(generic_transaction_state(&fixture.store), warm);
    }

    #[test]
    fn generic_keyof_constraint_rejects_nonordinary_interface_targets() {
        for (index, source) in [
            concat!(
                "type Choices = { left: string }; ",
                "function choose<T extends keyof Choices>(value: T): boolean { return true; }",
            ),
            concat!(
                "interface Choices<T> { left: T } ",
                "function choose<T extends keyof Choices<string>>(value: T): boolean ",
                "{ return true; }",
            ),
            concat!(
                "interface Choices { left(): string } ",
                "function choose<T extends keyof Choices>(value: T): boolean { return true; }",
            ),
            concat!(
                "interface Choices {} ",
                "function choose<T extends keyof Choices>(value: T): boolean { return true; }",
            ),
        ]
        .into_iter()
        .enumerate()
        {
            let fixture =
                QueryFixture::new(source, FileId::new(1_908 + u32::try_from(index).unwrap()));
            let (declaration, _) = fixture.declaration_and_type_parameter();
            let owner = fixture.bound.symbol(declaration).unwrap();
            let host = DeclaredTypeHost::new_after_global_merge(
                [(&fixture.parsed.arena, &fixture.bound)],
                GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
            )
            .unwrap();
            let before = generic_transaction_state(&fixture.store);

            assert!(
                matches!(
                    plan_source_callable(&fixture.store, &host, declaration, owner, None),
                    Err(SourceCallableError::Unsupported(
                        SourceCallableUnsupported::GenericSignature(_)
                    ))
                ),
                "source: {source}",
            );
            assert_eq!(generic_transaction_state(&fixture.store), before);
        }
    }

    struct StagedGenericPublication {
        fixture: QueryFixture,
        declaration: NodeRef,
        owner: SemanticSymbolId,
        owner_parent: Option<SemanticSymbolId>,
        export_local: Option<SemanticSymbolId>,
        syntax: SourceCallableTypeParameterSyntaxProof,
        resolved: Vec<ResolvedSourceCallableTypeParameter>,
        parameters: Vec<SemanticSymbolId>,
        return_annotation: NodeRef,
        generic_return_type_parameter: Option<TypeId>,
    }

    impl StagedGenericPublication {
        fn publish(&mut self) -> Option<(TypeId, SignatureId)> {
            self.fixture.store.publish_source_generic_callable(
                PreparedSourceGenericCallablePublication {
                    syntax: &self.syntax,
                    family: SourceCallableFamily::FunctionDeclaration,
                    declaration: self.declaration,
                    owner_symbol: self.owner,
                    owner_parent: self.owner_parent,
                    export_local: self.export_local,
                    type_parameters: self.resolved.clone(),
                    parameters: self.parameters.clone(),
                    flags: SignatureFlags::NONE,
                    min_argument_count: i32::try_from(self.parameters.len()).unwrap(),
                    return_annotation: Some(self.return_annotation),
                    return_null_literal_identity: false,
                    generic_return_type_parameter: self.generic_return_type_parameter,
                    array_targets: None,
                },
            )
        }

        fn publish_with(
            &mut self,
            resolved: Vec<ResolvedSourceCallableTypeParameter>,
        ) -> Option<(TypeId, SignatureId)> {
            self.fixture.store.publish_source_generic_callable(
                PreparedSourceGenericCallablePublication {
                    syntax: &self.syntax,
                    family: SourceCallableFamily::FunctionDeclaration,
                    declaration: self.declaration,
                    owner_symbol: self.owner,
                    owner_parent: self.owner_parent,
                    export_local: self.export_local,
                    type_parameters: resolved,
                    parameters: self.parameters.clone(),
                    flags: SignatureFlags::NONE,
                    min_argument_count: i32::try_from(self.parameters.len()).unwrap(),
                    return_annotation: Some(self.return_annotation),
                    return_null_literal_identity: false,
                    generic_return_type_parameter: self.generic_return_type_parameter,
                    array_targets: None,
                },
            )
        }
    }

    fn staged_generic_publication(source: &str, file: FileId) -> StagedGenericPublication {
        let mut fixture = QueryFixture::new(source, file);
        let declaration = fixture
            .parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::FunctionDeclaration).then_some(NodeRef::new(
                    fixture.parsed.arena.id(),
                    file,
                    node,
                ))
            })
            .expect("source has one function declaration");
        let (type_parameter_nodes, parameter_nodes, return_type) = {
            let NodeData::FunctionDeclaration(function) =
                &fixture.parsed.arena.get(declaration.node).unwrap().data
            else {
                unreachable!()
            };
            (
                function
                    .type_parameters
                    .as_ref()
                    .expect("metadata fixture is generic")
                    .nodes
                    .clone(),
                function.parameters.nodes.clone(),
                function
                    .type_
                    .expect("generic fixture has a return annotation"),
            )
        };
        let type_parameter_declarations = type_parameter_nodes
            .iter()
            .map(|node| NodeRef::new(declaration.arena, file, *node))
            .collect::<Vec<_>>();
        let plans = type_parameter_declarations
            .iter()
            .map(|declaration| {
                let NodeData::TypeParameterDeclaration(data) =
                    &fixture.parsed.arena.get(declaration.node).unwrap().data
                else {
                    unreachable!()
                };
                SourceCallableTypeParameterPlan {
                    declaration: *declaration,
                    symbol: fixture.bound.symbol(*declaration).unwrap(),
                    constraint: data
                        .constraint
                        .map(|node| NodeRef::new(declaration.arena, file, node)),
                    default_type: data
                        .default_type
                        .map(|node| NodeRef::new(declaration.arena, file, node)),
                }
            })
            .collect::<Vec<_>>();
        let return_annotation = NodeRef::new(declaration.arena, file, return_type);
        let (mut syntax, generic_return_type_parameter_index, generic_fixed_return_is_exact) = {
            let host = DeclaredTypeHost::new_after_global_merge(
                [(&fixture.parsed.arena, &fixture.bound)],
                GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
            )
            .unwrap();
            let proof =
                prove_source_type_parameter_syntax(&fixture.store, &host, declaration, &plans)
                    .unwrap();
            let index = plans.iter().position(|plan| {
                is_naked_source_type_parameter_annotation(
                    &fixture.store,
                    &host,
                    return_annotation,
                    plan,
                )
                .unwrap()
            });
            let fixed = index.is_none()
                && is_exact_source_generic_mapper_annotation(
                    &fixture.store,
                    &host,
                    return_annotation,
                    &plans,
                )
                .unwrap();
            (proof, index, fixed)
        };
        syntax.generic_return_type_parameter_declaration =
            generic_return_type_parameter_index.map(|index| plans[index].declaration);
        syntax.generic_fixed_return_is_exact = generic_fixed_return_is_exact;
        let type_parameter_symbols = type_parameter_declarations
            .iter()
            .map(|declaration| fixture.bound.symbol(*declaration).unwrap())
            .collect::<Vec<_>>();
        let type_parameters = type_parameter_symbols
            .iter()
            .map(|symbol| execute_type_parameter(&mut fixture.store, *symbol))
            .collect::<Vec<_>>();
        let parameter_symbols = parameter_nodes
            .iter()
            .map(|node| {
                fixture
                    .bound
                    .symbol(NodeRef::new(declaration.arena, file, *node))
                    .unwrap()
            })
            .collect::<Vec<_>>();
        let no_constraint = fixture
            .store
            .intrinsic_bootstrap()
            .unwrap()
            .no_constraint_type;
        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        let resolved = plans
            .iter()
            .zip(type_parameter_symbols)
            .zip(type_parameters.iter().copied())
            .map(
                |((plan, symbol), type_parameter)| ResolvedSourceCallableTypeParameter {
                    provenance: SourceCallableTypeParameterProvenance {
                        declaration: plan.declaration,
                        symbol,
                        type_parameter,
                        constraint: plan.constraint,
                        default_type: plan.default_type,
                    },
                    constraint: plan.constraint.map_or(no_constraint, |node| {
                        fixture
                            .query_type_parameter_result(node, &mut diagnostics)
                            .unwrap()
                    }),
                    default_type: plan.default_type.map_or(no_constraint, |node| {
                        fixture
                            .query_type_parameter_result(node, &mut diagnostics)
                            .unwrap()
                    }),
                },
            )
            .collect::<Vec<_>>();
        assert!(diagnostics.is_empty(), "{diagnostics:?}");
        let owner = fixture.bound.symbol(declaration).unwrap();
        let owner_parent = fixture.store.symbol(owner).unwrap().parent();
        let export_local = fixture.bound.local_symbol(declaration);
        let generic_return_type_parameter =
            generic_return_type_parameter_index.map(|index| type_parameters[index]);
        StagedGenericPublication {
            fixture,
            declaration,
            owner,
            owner_parent,
            export_local,
            syntax,
            resolved,
            parameters: parameter_symbols,
            return_annotation,
            generic_return_type_parameter,
        }
    }

    fn assert_exact_warm_type_parameter_annotation(
        store: &CanonicalTypeMapperStore,
        annotation: NodeRef,
        symbol: SemanticSymbolId,
        type_: TypeId,
    ) {
        assert_eq!(
            store.symbol_node_links(annotation),
            Some(&SymbolNodeLinks {
                resolved_symbol: Some(symbol),
            })
        );
        assert_eq!(
            store.type_node_links(annotation),
            Some(&TypeNodeLinks {
                resolved_type: Some(type_),
                outer_type_parameters: None,
            })
        );
    }

    #[test]
    fn type_parameter_syntax_proof_rejects_a_same_parent_non_field_child() {
        let fixture = QueryFixture::new(
            "function constrained<T extends string>(value: T): T { return value; }",
            FileId::new(951),
        );
        let (declaration, type_parameter) = fixture.declaration_and_type_parameter();
        let NodeData::TypeParameterDeclaration(data) =
            &fixture.parsed.arena.get(type_parameter.node).unwrap().data
        else {
            unreachable!()
        };
        let symbol = fixture.bound.symbol(type_parameter).unwrap();
        let name = NodeRef::new(type_parameter.arena, fixture.file, data.name);
        let constraint = NodeRef::new(
            type_parameter.arena,
            fixture.file,
            data.constraint.expect("fixture has a constraint"),
        );
        let host = DeclaredTypeHost::new_after_global_merge(
            [(&fixture.parsed.arena, &fixture.bound)],
            GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
        )
        .unwrap();
        assert!(matches!(
            prove_source_type_parameter_syntax(
                &fixture.store,
                &host,
                declaration,
                &[SourceCallableTypeParameterPlan {
                    declaration: type_parameter,
                    symbol,
                    constraint: Some(name),
                    default_type: None,
                }],
            ),
            Err(SourceCallableError::Invariant(
                SourceCallableInvariant::InvalidSyntax(_)
            ))
        ));
        let proof = prove_source_type_parameter_syntax(
            &fixture.store,
            &host,
            declaration,
            &[SourceCallableTypeParameterPlan {
                declaration: type_parameter,
                symbol,
                constraint: Some(constraint),
                default_type: None,
            }],
        )
        .unwrap();
        assert_eq!(proof.rows()[0].constraint(), Some(constraint));

        let ordered = staged_generic_publication(
            "function pair<T, U>(left: T, right: U): U { return right; }",
            FileId::new(936),
        );
        let reversed = ordered
            .resolved
            .iter()
            .rev()
            .map(|row| SourceCallableTypeParameterPlan {
                declaration: row.provenance.declaration,
                symbol: row.provenance.symbol,
                constraint: row.provenance.constraint,
                default_type: row.provenance.default_type,
            })
            .collect::<Vec<_>>();
        let host = DeclaredTypeHost::new_after_global_merge(
            [(&ordered.fixture.parsed.arena, &ordered.fixture.bound)],
            GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
        )
        .unwrap();
        assert!(
            prove_source_type_parameter_syntax(
                &ordered.fixture.store,
                &host,
                ordered.declaration,
                &reversed,
            )
            .is_err()
        );
    }

    #[test]
    fn ordered_source_type_parameter_metadata_is_atomic_and_collision_checked() {
        let mut staged = staged_generic_publication(
            "function pair<T, U>(left: T, right: U): U { return right; }",
            FileId::new(950),
        );
        let before = publication_state(&staged.fixture.store);
        let mut swapped = staged.resolved.clone();
        swapped.swap(0, 1);
        assert_eq!(staged.publish_with(swapped), None);
        assert_eq!(publication_state(&staged.fixture.store), before);

        let mut wrong_node = staged.resolved.clone();
        let string = staged
            .fixture
            .store
            .intrinsic_bootstrap()
            .unwrap()
            .string_type;
        wrong_node[0].provenance.constraint = Some(staged.declaration);
        wrong_node[0].constraint = string;
        assert_eq!(staged.publish_with(wrong_node), None);
        assert_eq!(publication_state(&staged.fixture.store), before);

        let foreign = staged_generic_publication(
            "function foreign<T>(value: T): T { return value; }",
            FileId::new(949),
        );
        let mut foreign_type = staged.resolved.clone();
        foreign_type[0].constraint = foreign
            .fixture
            .store
            .intrinsic_bootstrap()
            .unwrap()
            .string_type;
        foreign_type[0].provenance.constraint = Some(foreign_type[0].provenance.declaration);
        assert_eq!(staged.publish_with(foreign_type), None);
        assert_eq!(publication_state(&staged.fixture.store), before);

        let expected_rows = staged
            .resolved
            .iter()
            .map(|row| row.provenance)
            .collect::<Vec<_>>();
        let (callable, signature) = staged.publish().unwrap();
        assert_eq!(
            staged.fixture.store.source_callable_provenance_lengths(),
            [1, 1, 1, 1, 1]
        );
        assert_eq!(
            staged
                .fixture
                .store
                .source_callable_type_parameters(signature),
            Some(expected_rows.as_slice())
        );
        assert_eq!(
            staged
                .fixture
                .store
                .source_callable_type_for_declaration(staged.declaration),
            Some(callable)
        );
    }

    #[test]
    fn keyword_type_parameter_results_reject_poisoned_semantic_links() {
        let source = "function identity<T extends string>(value: T): T { return value; }";

        let mut wrong_result = staged_generic_publication(source, FileId::new(931));
        let constraint = wrong_result.resolved[0]
            .provenance
            .constraint
            .expect("fixture has a constraint");
        let number = wrong_result
            .fixture
            .store
            .intrinsic_bootstrap()
            .unwrap()
            .number_type;
        wrong_result.resolved[0].constraint = number;
        assert!(wrong_result.fixture.store.set_type_node_links(
            constraint,
            TypeNodeLinks {
                resolved_type: Some(number),
                outer_type_parameters: None,
            },
        ));
        let before = generic_transaction_state(&wrong_result.fixture.store);
        assert_eq!(wrong_result.publish(), None);
        assert_eq!(
            generic_transaction_state(&wrong_result.fixture.store),
            before
        );

        let mut wrong_link = staged_generic_publication(source, FileId::new(932));
        let constraint = wrong_link.resolved[0]
            .provenance
            .constraint
            .expect("fixture has a constraint");
        let number = wrong_link
            .fixture
            .store
            .intrinsic_bootstrap()
            .unwrap()
            .number_type;
        assert!(wrong_link.fixture.store.set_type_node_links(
            constraint,
            TypeNodeLinks {
                resolved_type: Some(number),
                outer_type_parameters: None,
            },
        ));
        let before = generic_transaction_state(&wrong_link.fixture.store);
        assert_eq!(wrong_link.publish(), None);
        assert_eq!(generic_transaction_state(&wrong_link.fixture.store), before);

        let mut symbol_poison = staged_generic_publication(source, FileId::new(933));
        let constraint = symbol_poison.resolved[0]
            .provenance
            .constraint
            .expect("fixture has a constraint");
        assert!(symbol_poison.fixture.store.set_symbol_node_links(
            constraint,
            SymbolNodeLinks {
                resolved_symbol: Some(symbol_poison.owner),
            },
        ));
        let before = generic_transaction_state(&symbol_poison.fixture.store);
        assert_eq!(symbol_poison.publish(), None);
        assert_eq!(
            generic_transaction_state(&symbol_poison.fixture.store),
            before
        );

        let mut exact_link = staged_generic_publication(source, FileId::new(934));
        let constraint = exact_link.resolved[0]
            .provenance
            .constraint
            .expect("fixture has a constraint");
        let string = exact_link.resolved[0].constraint;
        assert!(exact_link.fixture.store.set_type_node_links(
            constraint,
            TypeNodeLinks {
                resolved_type: Some(string),
                outer_type_parameters: None,
            },
        ));
        assert!(exact_link.publish().is_some());
    }

    #[test]
    fn dependent_type_parameter_results_require_the_exact_earlier_symbol_link() {
        let source =
            "function pair<T extends string, U extends T>(left: T, right: U): U { return right; }";

        let mut missing = staged_generic_publication(source, FileId::new(935));
        let constraint = missing.resolved[1]
            .provenance
            .constraint
            .expect("second parameter has a dependent constraint");
        assert!(
            missing
                .fixture
                .store
                .set_symbol_node_links(constraint, SymbolNodeLinks::default())
        );
        let before = generic_transaction_state(&missing.fixture.store);
        assert_eq!(missing.publish(), None);
        assert_eq!(generic_transaction_state(&missing.fixture.store), before);

        let mut wrong = staged_generic_publication(source, FileId::new(943));
        let constraint = wrong.resolved[1]
            .provenance
            .constraint
            .expect("second parameter has a dependent constraint");
        let wrong_symbol = wrong.resolved[1].provenance.symbol;
        assert!(wrong.fixture.store.set_symbol_node_links(
            constraint,
            SymbolNodeLinks {
                resolved_symbol: Some(wrong_symbol),
            },
        ));
        let before = generic_transaction_state(&wrong.fixture.store);
        assert_eq!(wrong.publish(), None);
        assert_eq!(generic_transaction_state(&wrong.fixture.store), before);
    }

    #[test]
    fn unproven_alias_and_composite_default_results_fail_closed() {
        for (index, source) in [
            "type Alias = string; function identity<T extends Alias>(value: T): T { return value; }",
            "type Alias = string; function identity<T = Alias>(value: T): T { return value; }",
            "function identity<T = string | number>(value: T): T { return value; }",
        ]
        .into_iter()
        .enumerate()
        {
            let mut staged = staged_generic_publication(
                source,
                FileId::new(976 + u32::try_from(index).unwrap()),
            );
            let before = generic_transaction_state(&staged.fixture.store);
            assert_eq!(staged.publish(), None, "{source}");
            assert_eq!(generic_transaction_state(&staged.fixture.store), before);
        }
    }

    #[test]
    fn existing_type_parameter_symbol_metadata_collision_is_atomic() {
        let mut staged = staged_generic_publication(
            "function identity<T>(value: T): T { return value; }",
            FileId::new(979),
        );
        let prepared = staged.resolved[0].provenance;
        let poison_signature = staged
            .fixture
            .store
            .intrinsic_bootstrap()
            .unwrap()
            .unknown_signature;
        let distinct_type = staged
            .fixture
            .store
            .intrinsic_bootstrap()
            .unwrap()
            .string_type;
        assert_ne!(prepared.declaration, staged.declaration);
        assert_ne!(prepared.type_parameter, distinct_type);
        assert_eq!(
            staged
                .fixture
                .store
                .replace_source_callable_type_parameters_for_test(
                    poison_signature,
                    Some(
                        vec![SourceCallableTypeParameterProvenance {
                            declaration: staged.declaration,
                            symbol: prepared.symbol,
                            type_parameter: distinct_type,
                            constraint: None,
                            default_type: None,
                        }]
                        .into_boxed_slice(),
                    ),
                ),
            None
        );
        let before = generic_transaction_state(&staged.fixture.store);
        assert_eq!(staged.publish(), None);
        assert_eq!(generic_transaction_state(&staged.fixture.store), before);
    }

    #[test]
    fn existing_type_parameter_identity_metadata_collision_is_atomic() {
        let mut staged = staged_generic_publication(
            "function identity<T>(value: T): T { return value; }",
            FileId::new(980),
        );
        let prepared = staged.resolved[0].provenance;
        let poison_signature = staged
            .fixture
            .store
            .intrinsic_bootstrap()
            .unwrap()
            .unknown_signature;
        assert_ne!(prepared.declaration, staged.declaration);
        assert_ne!(prepared.symbol, staged.owner);
        assert_eq!(
            staged
                .fixture
                .store
                .replace_source_callable_type_parameters_for_test(
                    poison_signature,
                    Some(
                        vec![SourceCallableTypeParameterProvenance {
                            declaration: staged.declaration,
                            symbol: staged.owner,
                            type_parameter: prepared.type_parameter,
                            constraint: None,
                            default_type: None,
                        }]
                        .into_boxed_slice(),
                    ),
                ),
            None
        );
        let before = generic_transaction_state(&staged.fixture.store);
        assert_eq!(staged.publish(), None);
        assert_eq!(generic_transaction_state(&staged.fixture.store), before);
    }

    #[test]
    fn partial_primary_and_reverse_poison_are_rejected_before_five_map_publication() {
        let mut staged = staged_generic_publication(
            "function identity<T>(value: T): T { return value; }",
            FileId::new(941),
        );
        let bootstrap = staged.fixture.store.intrinsic_bootstrap().unwrap();
        let poison_type = bootstrap.string_type;
        let poison_signature = bootstrap.unknown_signature;
        assert_eq!(
            staged
                .fixture
                .store
                .replace_source_callable_provenance_for_test(
                    poison_type,
                    Some(SourceCallableProvenance {
                        family: SourceCallableFamily::FunctionDeclaration,
                        declaration: staged.declaration,
                        owner_symbol: staged.owner,
                        owner_parent: staged.owner_parent,
                        export_local: staged.export_local,
                        signature: poison_signature,
                        return_provenance: SourceCallableReturnProvenance::Annotated,
                        array_targets: None,
                        generic_return_type_parameter: staged.generic_return_type_parameter,
                        contextual_target: None,
                        contextual_variable: None,
                    }),
                ),
            None
        );
        assert_eq!(
            staged.fixture.store.source_callable_provenance_lengths(),
            [1, 0, 0, 0, 0]
        );
        let before = publication_state(&staged.fixture.store);
        assert_eq!(staged.publish(), None);
        assert_eq!(publication_state(&staged.fixture.store), before);
        assert!(
            staged
                .fixture
                .store
                .replace_source_callable_provenance_for_test(poison_type, None)
                .is_some()
        );
        assert_eq!(
            staged
                .fixture
                .store
                .replace_source_callable_type_for_declaration_for_test(
                    staged.declaration,
                    Some(poison_type),
                ),
            None
        );
        assert_eq!(
            staged.fixture.store.source_callable_provenance_lengths(),
            [0, 1, 0, 0, 0]
        );
        let before = publication_state(&staged.fixture.store);
        assert_eq!(staged.publish(), None);
        assert_eq!(publication_state(&staged.fixture.store), before);
        assert_eq!(
            staged
                .fixture
                .store
                .replace_source_callable_type_for_declaration_for_test(staged.declaration, None),
            Some(poison_type)
        );
        assert!(staged.publish().is_some());
        assert_eq!(
            staged.fixture.store.source_callable_provenance_lengths(),
            [1, 1, 1, 1, 1]
        );
    }

    #[test]
    fn computed_type_variable_flags_are_cold_but_half_flags_are_poison() {
        let mut computed = staged_generic_publication(
            "function identity<T>(value: T): T { return value; }",
            FileId::new(940),
        );
        let type_parameter = computed.resolved[0].provenance.type_parameter;
        let computed_flags = ObjectFlags::COULD_CONTAIN_TYPE_VARIABLES
            | ObjectFlags::COULD_CONTAIN_TYPE_VARIABLES_COMPUTED;
        assert!(
            computed
                .fixture
                .store
                .set_type_object_flags(type_parameter, computed_flags)
        );
        assert!(computed.publish().is_some());

        let mut half = staged_generic_publication(
            "function identity<T>(value: T): T { return value; }",
            FileId::new(939),
        );
        let type_parameter = half.resolved[0].provenance.type_parameter;
        assert!(
            half.fixture
                .store
                .set_type_object_flags(type_parameter, ObjectFlags::COULD_CONTAIN_TYPE_VARIABLES,)
        );
        let before = publication_state(&half.fixture.store);
        assert_eq!(half.publish(), None);
        assert_eq!(publication_state(&half.fixture.store), before);
    }

    #[test]
    fn partial_source_type_parameter_caches_are_not_promoted_to_provenance() {
        let mut constraint = staged_generic_publication(
            "function identity<T>(value: T): T { return value; }",
            FileId::new(948),
        );
        let type_parameter = constraint.resolved[0].provenance.type_parameter;
        let no_constraint = constraint
            .fixture
            .store
            .intrinsic_bootstrap()
            .unwrap()
            .no_constraint_type;
        assert!(constraint.fixture.store.set_type_parameter_resolution(
            type_parameter,
            Some(no_constraint),
            None,
            None,
            None,
        ));
        let before = publication_state(&constraint.fixture.store);
        assert_eq!(constraint.publish(), None);
        assert_eq!(publication_state(&constraint.fixture.store), before);

        let mut default = staged_generic_publication(
            "function identity<T>(value: T): T { return value; }",
            FileId::new(947),
        );
        let type_parameter = default.resolved[0].provenance.type_parameter;
        let no_constraint = default
            .fixture
            .store
            .intrinsic_bootstrap()
            .unwrap()
            .no_constraint_type;
        assert!(default.fixture.store.set_type_parameter_resolution(
            type_parameter,
            None,
            None,
            None,
            Some(no_constraint),
        ));
        let before = publication_state(&default.fixture.store);
        assert_eq!(default.publish(), None);
        assert_eq!(publication_state(&default.fixture.store), before);

        let mut target = staged_generic_publication(
            "function identity<T>(value: T): T { return value; }",
            FileId::new(946),
        );
        let type_parameter = target.resolved[0].provenance.type_parameter;
        let string = target
            .fixture
            .store
            .intrinsic_bootstrap()
            .unwrap()
            .string_type;
        let mapper = target
            .fixture
            .store
            .new_simple_type_mapper(type_parameter, string)
            .unwrap();
        assert!(target.fixture.store.set_type_parameter_resolution(
            type_parameter,
            None,
            Some(type_parameter),
            Some(mapper),
            None,
        ));
        let before = publication_state(&target.fixture.store);
        assert_eq!(target.publish(), None);
        assert_eq!(publication_state(&target.fixture.store), before);

        let mut base = staged_generic_publication(
            "function identity<T>(value: T): T { return value; }",
            FileId::new(945),
        );
        let type_parameter = base.resolved[0].provenance.type_parameter;
        let string = base
            .fixture
            .store
            .intrinsic_bootstrap()
            .unwrap()
            .string_type;
        assert!(
            base.fixture
                .store
                .set_resolved_base_constraint(type_parameter, Some(string))
        );
        let before = publication_state(&base.fixture.store);
        assert_eq!(base.publish(), None);
        assert_eq!(publication_state(&base.fixture.store), before);
    }

    #[test]
    fn exact_warm_base_constraint_graph_is_accepted_and_poison_is_atomic() {
        let mut wrong_result = staged_generic_publication(
            "function identity<T extends string>(value: T): T { return value; }",
            FileId::new(937),
        );
        wrong_result.resolved[0].constraint = wrong_result
            .fixture
            .store
            .intrinsic_bootstrap()
            .unwrap()
            .number_type;
        let before = publication_state(&wrong_result.fixture.store);
        assert_eq!(wrong_result.publish(), None);
        assert_eq!(publication_state(&wrong_result.fixture.store), before);

        let mut warm = staged_generic_publication(
            "function pair<T extends string, U extends T>(left: T, right: U): U { return right; }",
            FileId::new(944),
        );
        let string = warm
            .fixture
            .store
            .intrinsic_bootstrap()
            .unwrap()
            .string_type;
        for row in &warm.resolved {
            assert!(warm.fixture.store.set_type_parameter_resolution(
                row.provenance.type_parameter,
                Some(row.constraint),
                None,
                None,
                Some(row.default_type),
            ));
            assert!(
                warm.fixture
                    .store
                    .set_resolved_base_constraint(row.provenance.type_parameter, Some(string),)
            );
        }
        assert!(warm.publish().is_some());
        assert_eq!(
            warm.fixture.store.source_callable_provenance_lengths(),
            [1, 1, 1, 1, 1]
        );

        let mut poison = staged_generic_publication(
            "function identity<T extends string>(value: T): T { return value; }",
            FileId::new(942),
        );
        let row = poison.resolved[0];
        let number = poison
            .fixture
            .store
            .intrinsic_bootstrap()
            .unwrap()
            .number_type;
        assert!(poison.fixture.store.set_type_parameter_resolution(
            row.provenance.type_parameter,
            Some(row.constraint),
            None,
            None,
            Some(row.default_type),
        ));
        assert!(
            poison
                .fixture
                .store
                .set_resolved_base_constraint(row.provenance.type_parameter, Some(number),)
        );
        let before = publication_state(&poison.fixture.store);
        assert_eq!(poison.publish(), None);
        assert_eq!(publication_state(&poison.fixture.store), before);
    }

    #[test]
    fn active_generic_shell_survives_parameter_publication_preflight_failure() {
        let mut fixture = QueryFixture::new(
            "function identity<T>(value: T): T { return value; }",
            FileId::new(938),
        );
        let (declaration, _, _, _) = fixture.generic_parts();
        let owner = fixture.bound.symbol(declaration).unwrap();
        let host = DeclaredTypeHost::new_after_global_merge(
            [(&fixture.parsed.arena, &fixture.bound)],
            GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
        )
        .unwrap();
        let plan = plan_source_callable(&fixture.store, &host, declaration, owner, None).unwrap();
        drop(host);
        let type_parameter_plan = plan.type_parameters[0];
        let type_parameter = execute_type_parameter(&mut fixture.store, type_parameter_plan.symbol);
        let no_constraint = fixture
            .store
            .intrinsic_bootstrap()
            .unwrap()
            .no_constraint_type;
        let resolved_type_parameters = [ResolvedSourceCallableTypeParameter {
            provenance: SourceCallableTypeParameterProvenance {
                declaration: type_parameter_plan.declaration,
                symbol: type_parameter_plan.symbol,
                type_parameter,
                constraint: None,
                default_type: None,
            },
            constraint: no_constraint,
            default_type: no_constraint,
        }];
        let pending = begin_source_callable(&mut fixture.store, &plan, &resolved_type_parameters)
            .unwrap()
            .unwrap();
        finalize_source_callable_structure(&mut fixture.store, &plan, pending).unwrap();
        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        let base_type = fixture
            .query_type_node(plan.parameters[0].type_node, &mut diagnostics)
            .unwrap();
        assert!(diagnostics.is_empty(), "{diagnostics:?}");
        let published = publication_state(&fixture.store);
        let link_lengths = fixture.store.checker_link_allocated_lengths();
        assert_eq!(
            fixture.store.source_callable_provenance_lengths(),
            [1, 1, 1, 1, 1]
        );

        let wrong_base = fixture.store.intrinsic_bootstrap().unwrap().string_type;
        let mut prepared = fixture
            .store
            .prepare_type_query_types(&[], &[], &[], 0, 0)
            .unwrap();
        assert!(
            publish_source_callable_parameter_types(
                &mut fixture.store,
                None,
                &[PendingSourceCallableParameterTypes {
                    plan: plan.clone(),
                    base_types: vec![wrong_base],
                }],
                &mut prepared,
            )
            .is_err()
        );
        assert_eq!(publication_state(&fixture.store), published);
        assert_eq!(fixture.store.checker_link_allocated_lengths(), link_lengths);

        let retried = begin_source_callable(&mut fixture.store, &plan, &resolved_type_parameters)
            .unwrap()
            .unwrap();
        assert_eq!(retried, pending);
        assert_eq!(publication_state(&fixture.store), published);
        assert_eq!(fixture.store.checker_link_allocated_lengths(), link_lengths);

        let mut prepared = fixture
            .store
            .prepare_type_query_types(&[], &[], &[], 0, 0)
            .unwrap();
        publish_source_callable_parameter_types(
            &mut fixture.store,
            None,
            &[PendingSourceCallableParameterTypes {
                plan: plan.clone(),
                base_types: vec![base_type],
            }],
            &mut prepared,
        )
        .unwrap();
        assert!(matches!(
            source_callable_state(&fixture.store, &plan, false),
            Ok(SourceCallableState::Resolved { type_, signature })
                if type_ == pending.type_ && signature == pending.signature
        ));
        assert_eq!(fixture.store.types().len(), published.0);
        assert_eq!(fixture.store.signature_len(), published.1);
    }

    #[test]
    fn inferred_return_provenance_publishes_once_and_replays_exactly() {
        let mut fixture = QueryFixture::new("function inferred() { return 1; }", FileId::new(989));
        let declaration = fixture
            .parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::FunctionDeclaration).then_some(NodeRef::new(
                    fixture.parsed.arena.id(),
                    fixture.file,
                    node,
                ))
            })
            .unwrap();
        let owner = fixture.bound.symbol(declaration).unwrap();
        let host = DeclaredTypeHost::new_after_global_merge(
            [(&fixture.parsed.arena, &fixture.bound)],
            GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
        )
        .unwrap();
        let plan = plan_source_callable(&fixture.store, &host, declaration, owner, None).unwrap();
        assert_eq!(plan.return_type, SourceCallableReturnPlan::Inferred);
        drop(host);

        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        let type_ = fixture
            .query_callable(declaration, owner, &mut diagnostics)
            .unwrap();
        assert!(diagnostics.is_empty());
        let provenance = fixture.store.source_callable_provenance(type_).unwrap();
        assert_eq!(
            provenance.return_provenance,
            SourceCallableReturnProvenance::Inferred
        );
        assert!(
            fixture
                .store
                .function_signature_return_annotation(provenance.signature)
                .is_none()
        );
        assert!(matches!(
            source_callable_state(&fixture.store, &plan, false),
            Ok(SourceCallableState::AwaitingInferredReturn {
                type_: cached,
                signature
            }) if cached == type_ && signature == provenance.signature
        ));
        assert_eq!(
            validate_stored_source_callable(&fixture.store, type_),
            StoredSourceCallableValidation::Pending
        );

        let number = fixture.store.intrinsic_bootstrap().unwrap().number_type;
        let string = fixture.store.intrinsic_bootstrap().unwrap().string_type;
        let before = publication_state(&fixture.store);
        assert_eq!(
            publish_inferred_source_callable_return(
                &mut fixture.store,
                &plan,
                provenance.signature,
                number,
            ),
            Ok(number)
        );
        assert_eq!(publication_state(&fixture.store), before);
        assert!(matches!(
            validate_stored_source_callable(&fixture.store, type_),
            StoredSourceCallableValidation::Valid(_)
        ));
        assert_eq!(
            publish_inferred_source_callable_return(
                &mut fixture.store,
                &plan,
                provenance.signature,
                number,
            ),
            Ok(number)
        );
        assert_eq!(publication_state(&fixture.store), before);
        assert!(
            publish_inferred_source_callable_return(
                &mut fixture.store,
                &plan,
                provenance.signature,
                string,
            )
            .is_err()
        );
        assert_eq!(publication_state(&fixture.store), before);
        assert_eq!(
            fixture
                .store
                .signature(provenance.signature)
                .unwrap()
                .resolved_return_type(),
            Some(number)
        );
    }

    #[test]
    fn empty_generic_inferred_return_publishes_only_canonical_void() {
        let mut fixture = QueryFixture::new("function f<T, U>() {}", FileId::new(1_260));
        let (declaration, _) = function_and_type_parameter(&fixture.parsed, fixture.file);
        let owner = fixture.bound.symbol(declaration).unwrap();
        let host = DeclaredTypeHost::new_after_global_merge(
            [(&fixture.parsed.arena, &fixture.bound)],
            GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
        )
        .unwrap();
        let plan = plan_source_callable(&fixture.store, &host, declaration, owner, None).unwrap();
        assert_eq!(plan.type_parameters.len(), 2);
        assert!(plan.parameters.is_empty());
        assert_eq!(plan.return_type, SourceCallableReturnPlan::Inferred);
        assert!(plan.type_parameter_syntax.inferred_empty_body_is_exact());
        assert!(!plan.type_parameter_syntax.generic_fixed_return_is_exact());
        drop(host);

        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        let type_ = fixture
            .query_callable(declaration, owner, &mut diagnostics)
            .unwrap();
        let provenance = fixture.store.source_callable_provenance(type_).unwrap();
        let signature = provenance.signature;
        assert_eq!(
            provenance.return_provenance,
            SourceCallableReturnProvenance::Inferred
        );
        assert!(provenance.generic_return_type_parameter.is_none());
        assert!(
            fixture
                .store
                .function_signature_return_annotation(signature)
                .is_none()
        );
        assert_eq!(
            fixture
                .store
                .source_callable_type_parameters(signature)
                .unwrap()
                .len(),
            2
        );
        assert_eq!(
            fixture
                .store
                .signature(signature)
                .unwrap()
                .type_parameters()
                .len(),
            2
        );
        assert_eq!(
            validate_stored_source_callable(&fixture.store, type_),
            StoredSourceCallableValidation::Pending
        );
        assert!(matches!(
            source_callable_state(&fixture.store, &plan, false),
            Ok(SourceCallableState::AwaitingInferredReturn {
                type_: cached,
                signature: cached_signature,
            }) if cached == type_ && cached_signature == signature
        ));

        let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
        let number = bootstrap.number_type;
        let void = bootstrap.void_type;
        let before = generic_transaction_state(&fixture.store);
        assert!(
            publish_inferred_source_callable_return(&mut fixture.store, &plan, signature, number)
                .is_err()
        );
        assert_eq!(generic_transaction_state(&fixture.store), before);
        assert!(
            fixture
                .store
                .signature(signature)
                .unwrap()
                .resolved_return_type()
                .is_none()
        );

        assert_eq!(
            publish_inferred_source_callable_return(&mut fixture.store, &plan, signature, void),
            Ok(void)
        );
        assert!(matches!(
            validate_stored_source_callable(&fixture.store, type_),
            StoredSourceCallableValidation::Valid(_)
        ));
        assert_eq!(
            fixture.query_callable(declaration, owner, &mut diagnostics),
            Ok(type_)
        );
        assert_eq!(fixture.query_return(signature, &mut diagnostics), Ok(void));
        assert_eq!(generic_transaction_state(&fixture.store), before);
        assert!(diagnostics.is_empty());
    }

    #[test]
    fn unresolved_generic_constraint_keeps_its_typed_parameter_and_recovers_once() {
        let mut fixture = QueryFixture::new(
            "function broken<Item extends Missing>(item: Item) {}",
            FileId::new(1_264),
        );
        let (declaration, type_parameter) =
            function_and_type_parameter(&fixture.parsed, fixture.file);
        let owner = fixture.bound.symbol(declaration).unwrap();
        let NodeData::TypeParameterDeclaration(parameter) =
            &fixture.parsed.arena.get(type_parameter.node).unwrap().data
        else {
            panic!("the function must have one constrained type parameter")
        };
        let constraint = NodeRef::new(
            type_parameter.arena,
            type_parameter.file,
            parameter.constraint.unwrap(),
        );
        let NodeData::TypeReferenceNode(reference) =
            &fixture.parsed.arena.get(constraint.node).unwrap().data
        else {
            panic!("the constraint must name the missing type")
        };
        let missing_name = NodeRef::new(constraint.arena, constraint.file, reference.type_name);
        let host = DeclaredTypeHost::new_after_global_merge(
            [(&fixture.parsed.arena, &fixture.bound)],
            GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
        )
        .unwrap();
        let before = generic_transaction_state(&fixture.store);

        assert!(
            exact_unresolved_source_type_parameter_constraint(&fixture.store, &host, constraint)
                .unwrap()
        );
        let plan = plan_source_callable(&fixture.store, &host, declaration, owner, None).unwrap();
        assert_eq!(plan.type_parameters.len(), 1);
        assert_eq!(plan.type_parameters[0].constraint, Some(constraint));
        assert_eq!(plan.parameters.len(), 1);
        assert_eq!(plan.min_argument_count, 1);
        assert!(!plan.parameters[0].is_implicit_any());
        assert!(plan.type_parameter_syntax.inferred_empty_body_is_exact());
        assert_eq!(generic_transaction_state(&fixture.store), before);
        drop(host);

        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        let callable = fixture
            .query_callable(declaration, owner, &mut diagnostics)
            .unwrap();
        let signature = fixture
            .store
            .source_callable_provenance(callable)
            .unwrap()
            .signature;
        let error_type = fixture.store.intrinsic_bootstrap().unwrap().error_type;
        let type_parameter = fixture
            .store
            .signature(signature)
            .unwrap()
            .type_parameters()[0];
        assert!(
            fixture
                .store
                .source_recovered_unresolved_type_reference_is_exact(constraint, error_type)
        );
        assert_eq!(
            fixture.store.callable_signature_parameter_types(signature),
            Some([type_parameter].as_slice())
        );
        let [diagnostic] = diagnostics.as_slice() else {
            panic!("the missing constraint must report exactly one diagnostic")
        };
        assert_eq!(diagnostic.node, Some(missing_name));
        assert_eq!(diagnostic.diagnostic.code(), 2304);
        assert_eq!(diagnostic.diagnostic.arguments, ["Missing"]);

        let void = fixture.store.intrinsic_bootstrap().unwrap().void_type;
        assert_eq!(
            publish_inferred_source_callable_return(&mut fixture.store, &plan, signature, void,),
            Ok(void)
        );
        assert!(matches!(
            validate_stored_source_callable(&fixture.store, callable),
            StoredSourceCallableValidation::Valid(_)
        ));
        let warm = generic_transaction_state(&fixture.store);
        assert_eq!(
            fixture.query_callable(declaration, owner, &mut diagnostics),
            Ok(callable)
        );
        assert_eq!(fixture.query_return(signature, &mut diagnostics), Ok(void));
        assert_eq!(generic_transaction_state(&fixture.store), warm);
        assert_eq!(diagnostics.len(), 1);
    }

    #[test]
    fn unresolved_generic_constraint_rejects_defaults_arguments_and_other_parameter_types() {
        for (index, source) in [
            "function broken<Item extends Missing = any>(item: Item) {}",
            "function broken<Item extends Missing<string>>(item: Item) {}",
            "function broken<Item extends Missing>(item: string) {}",
            "type Alias = string; function broken<Item extends Alias>(item: Item) {}",
        ]
        .into_iter()
        .enumerate()
        {
            let fixture =
                QueryFixture::new(source, FileId::new(1_265 + u32::try_from(index).unwrap()));
            let (declaration, _) = function_and_type_parameter(&fixture.parsed, fixture.file);
            let owner = fixture.bound.symbol(declaration).unwrap();
            let host = DeclaredTypeHost::new_after_global_merge(
                [(&fixture.parsed.arena, &fixture.bound)],
                GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
            )
            .unwrap();
            let before = generic_transaction_state(&fixture.store);

            assert!(
                matches!(
                    plan_source_callable(&fixture.store, &host, declaration, owner, None),
                    Err(SourceCallableError::Unsupported(
                        SourceCallableUnsupported::GenericSignature(_)
                            | SourceCallableUnsupported::GenericInferredReturn(_)
                    ))
                ),
                "{source}"
            );
            assert_eq!(generic_transaction_state(&fixture.store), before);
        }
    }

    #[test]
    fn inferred_generic_parameters_and_nonempty_bodies_publish_nothing() {
        for (index, source) in [
            "function f<T>(value: T) {}",
            "function f<T>() { return; }",
            "function f<T>() { return 1; }",
        ]
        .into_iter()
        .enumerate()
        {
            let fixture =
                QueryFixture::new(source, FileId::new(1_261 + u32::try_from(index).unwrap()));
            let (declaration, type_parameter) =
                function_and_type_parameter(&fixture.parsed, fixture.file);
            let owner = fixture.bound.symbol(declaration).unwrap();
            let type_parameter_symbol = fixture.bound.symbol(type_parameter).unwrap();
            let before = generic_transaction_state(&fixture.store);
            let host = DeclaredTypeHost::new_after_global_merge(
                [(&fixture.parsed.arena, &fixture.bound)],
                GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
            )
            .unwrap();

            assert!(matches!(
                plan_source_callable(&fixture.store, &host, declaration, owner, None),
                Err(SourceCallableError::Unsupported(
                    SourceCallableUnsupported::GenericInferredReturn(node)
                )) if node == declaration
            ));
            assert_eq!(generic_transaction_state(&fixture.store), before);
            assert!(
                fixture
                    .store
                    .declared_type_links(type_parameter_symbol)
                    .is_none()
            );
            assert!(
                fixture
                    .store
                    .source_callable_type_for_owner(owner)
                    .is_none()
            );
        }
    }

    #[test]
    fn nested_typed_arrows_preserve_owners_and_inferred_returns_on_replay() {
        for (index, source) in [
            "const result = invoke((value: string): string => value);",
            "const result = invoke((outer: number) => invoke((inner: number) => inner));",
            "class Container { run() { invoke((value: number) => value); } }",
        ]
        .into_iter()
        .enumerate()
        {
            let mut fixture =
                QueryFixture::new(source, FileId::new(1_210 + u32::try_from(index).unwrap()));
            let arrows = fixture
                .parsed
                .arena
                .iter()
                .filter_map(|(node, record)| {
                    (record.kind == SyntaxKind::ArrowFunction).then_some(NodeRef::new(
                        fixture.parsed.arena.id(),
                        fixture.file,
                        node,
                    ))
                })
                .collect::<Vec<_>>();
            let method = fixture.parsed.arena.iter().find_map(|(node, record)| {
                (record.kind == SyntaxKind::MethodDeclaration).then_some(NodeRef::new(
                    fixture.parsed.arena.id(),
                    fixture.file,
                    node,
                ))
            });
            let mut owners = HashSet::new();
            let mut diagnostics = CanonicalCheckerDiagnostics::default();

            for declaration in arrows {
                let owner = fixture.bound.symbol(declaration).unwrap();
                assert!(owners.insert(owner));
                let host = DeclaredTypeHost::new_after_global_merge(
                    [(&fixture.parsed.arena, &fixture.bound)],
                    GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
                )
                .unwrap();
                let plan =
                    plan_source_callable(&fixture.store, &host, declaration, owner, None).unwrap();
                drop(host);

                if let Some(method) = method {
                    let method_owner = fixture.bound.symbol(method).unwrap();
                    assert_eq!(
                        fixture.store.symbol(method_owner).unwrap().flags(),
                        SymbolFlags::METHOD
                    );
                    assert_ne!(method_owner, owner);

                    let mut method_plan = plan.clone();
                    method_plan.owner_symbol = method_owner;
                    method_plan.owner_parent = fixture.store.symbol(method_owner).unwrap().parent();
                    let before = publication_state(&fixture.store);
                    let expected = SourceCallableError::Invariant(
                        SourceCallableInvariant::InvalidOwnerSymbol(declaration),
                    );
                    assert_eq!(
                        source_callable_state(&fixture.store, &method_plan, true),
                        Err(expected)
                    );
                    assert_eq!(
                        reserve_source_callable_capacities(&mut fixture.store, &[&method_plan]),
                        Err(expected)
                    );
                    assert_eq!(
                        begin_source_callable(&mut fixture.store, &method_plan, &[]),
                        Err(expected)
                    );
                    assert_eq!(publication_state(&fixture.store), before);
                    assert!(
                        fixture
                            .store
                            .source_callable_type_for_owner(method_owner)
                            .is_none()
                    );
                }

                let callable = fixture
                    .query_callable(declaration, owner, &mut diagnostics)
                    .unwrap();
                let provenance = fixture.store.source_callable_provenance(callable).unwrap();
                assert_eq!(provenance.family, SourceCallableFamily::ArrowFunction);
                assert_eq!(provenance.declaration, declaration);
                assert_eq!(provenance.owner_symbol, owner);

                let expected_return = plan.parameters[0].base_type(&fixture.store).unwrap();
                if plan.return_type.is_inferred() {
                    assert_eq!(
                        fixture.query_return(provenance.signature, &mut diagnostics),
                        Err(DeclaredTypeError::TypeNodeUnavailable(
                            TypeNodeUnavailable::InvalidFunctionSignature(provenance.signature)
                        ))
                    );
                    assert_eq!(
                        publish_inferred_source_callable_return(
                            &mut fixture.store,
                            &plan,
                            provenance.signature,
                            expected_return,
                        ),
                        Ok(expected_return)
                    );
                }
                assert_eq!(
                    fixture.query_return(provenance.signature, &mut diagnostics),
                    Ok(expected_return)
                );

                let warm = publication_state(&fixture.store);
                assert_eq!(
                    fixture.query_callable(declaration, owner, &mut diagnostics),
                    Ok(callable)
                );
                assert_eq!(
                    fixture.query_return(provenance.signature, &mut diagnostics),
                    Ok(expected_return)
                );
                assert_eq!(publication_state(&fixture.store), warm);
                assert!(matches!(
                    validate_stored_source_callable(&fixture.store, callable),
                    StoredSourceCallableValidation::Valid(_)
                ));
            }
            assert!(diagnostics.is_empty());
        }
    }

    #[test]
    fn duplicate_arrow_publication_is_rejected_before_parameter_writes() {
        let mut fixture = QueryFixture::new(
            "const result = invoke((value: string): string => value);",
            FileId::new(1_213),
        );
        let declaration = fixture
            .parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::ArrowFunction).then_some(NodeRef::new(
                    fixture.parsed.arena.id(),
                    fixture.file,
                    node,
                ))
            })
            .unwrap();
        let owner = fixture.bound.symbol(declaration).unwrap();
        let host = DeclaredTypeHost::new_after_global_merge(
            [(&fixture.parsed.arena, &fixture.bound)],
            GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
        )
        .unwrap();
        let plan = plan_source_callable(&fixture.store, &host, declaration, owner, None).unwrap();
        drop(host);

        let before = publication_state(&fixture.store);
        let expected = SourceCallableError::Invariant(SourceCallableInvariant::InvalidOwnerSymbol(
            declaration,
        ));
        assert_eq!(
            reserve_source_callable_capacities(&mut fixture.store, &[&plan, &plan]),
            Err(expected)
        );
        assert_eq!(publication_state(&fixture.store), before);

        reserve_source_callable_capacities(&mut fixture.store, &[&plan]).unwrap();
        let pending = begin_source_callable(&mut fixture.store, &plan, &[])
            .unwrap()
            .unwrap();
        finalize_source_callable_structure(&mut fixture.store, &plan, pending).unwrap();
        let base_type = plan.parameters[0].base_type(&fixture.store).unwrap();
        let entry = PendingSourceCallableParameterTypes {
            plan: plan.clone(),
            base_types: vec![base_type],
        };
        let before = publication_state(&fixture.store);
        let link_lengths = fixture.store.checker_link_allocated_lengths();
        let mut prepared = fixture
            .store
            .prepare_type_query_types(&[], &[], &[], 0, 0)
            .unwrap();

        assert_eq!(
            publish_source_callable_parameter_types(
                &mut fixture.store,
                None,
                &[entry.clone(), entry.clone()],
                &mut prepared,
            ),
            Err(expected)
        );
        assert_eq!(publication_state(&fixture.store), before);
        assert_eq!(fixture.store.checker_link_allocated_lengths(), link_lengths);
        assert!(
            fixture
                .store
                .value_symbol_links(plan.parameters[0].symbol)
                .is_none()
        );

        publish_source_callable_parameter_types(&mut fixture.store, None, &[entry], &mut prepared)
            .unwrap();
        assert_eq!(
            fixture
                .store
                .callable_signature_parameter_types(pending.signature),
            Some([base_type].as_slice())
        );
    }

    #[test]
    fn contextual_object_property_arrow_preserves_nonvoid_return_and_replays_warm() {
        let mut fixture = QueryFixture::new(
            concat!(
                "const target: (value: string) => string = ",
                "(value: string): string => value; ",
                "const object = { run: value => value };",
            ),
            FileId::new(1_216),
        );
        let (property, declaration) = fixture
            .parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                let NodeData::PropertyAssignment(property) = &record.data else {
                    return None;
                };
                Some((
                    NodeRef::new(fixture.parsed.arena.id(), fixture.file, node),
                    NodeRef::new(
                        fixture.parsed.arena.id(),
                        fixture.file,
                        property.initializer,
                    ),
                ))
            })
            .unwrap();
        let NodeData::ArrowFunction(arrow) =
            &fixture.parsed.arena.get(declaration.node).unwrap().data
        else {
            panic!("the object property must contain an arrow")
        };
        let parameter = NodeRef::new(
            declaration.arena,
            declaration.file,
            arrow.parameters.nodes[0],
        );
        let target_node = fixture
            .parsed
            .arena
            .iter()
            .find_map(|(_, record)| {
                let NodeData::VariableDeclaration(variable) = &record.data else {
                    return None;
                };
                variable
                    .type_
                    .map(|type_| NodeRef::new(fixture.parsed.arena.id(), fixture.file, type_))
            })
            .unwrap();
        let owner = fixture.bound.symbol(declaration).unwrap();
        let property_symbol = fixture.bound.symbol(property).unwrap();
        let parameter_symbol = fixture.bound.symbol(parameter).unwrap();
        let host = DeclaredTypeHost::new_after_global_merge(
            [(&fixture.parsed.arena, &fixture.bound)],
            GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
        )
        .unwrap();

        assert_eq!(
            source_object_property_arrow_symbol(&fixture.store, &host, declaration),
            Ok(Some(property_symbol))
        );
        let plan = plan_source_callable(&fixture.store, &host, declaration, owner, None).unwrap();
        assert!(plan.parameters[0].is_implicit_any());
        drop(host);

        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        let target = fixture
            .query_type_node(target_node, &mut diagnostics)
            .unwrap();
        let string = fixture.store.intrinsic_bootstrap().unwrap().string_type;
        let prepared = PreparedContextualSourceCallable {
            declaration,
            owner_symbol: owner,
            variable_symbol: property_symbol,
            contextual_target: target,
            parameters: vec![ContextualSourceCallableParameter {
                declaration: parameter,
                symbol: parameter_symbol,
                type_: string,
            }],
            flags: SignatureFlags::NONE,
            min_argument_count: 1,
            return_type: string,
        };
        let invalid = PreparedContextualSourceCallable {
            variable_symbol: owner,
            ..prepared.clone()
        };
        let before = publication_state(&fixture.store);
        assert_eq!(
            publish_contextual_source_callable(&mut fixture.store, &invalid),
            Err(SourceCallableError::Invariant(
                SourceCallableInvariant::Publication(declaration)
            ))
        );
        assert_eq!(publication_state(&fixture.store), before);

        let callable = publish_contextual_source_callable(&mut fixture.store, &prepared).unwrap();
        let provenance = fixture.store.source_callable_provenance(callable).unwrap();
        assert_eq!(provenance.contextual_variable, Some(property_symbol));
        assert_eq!(provenance.contextual_target, Some(target));
        assert_eq!(
            fixture
                .store
                .signature(provenance.signature)
                .unwrap()
                .resolved_return_type(),
            Some(string)
        );
        assert_eq!(
            fixture
                .store
                .callable_signature_parameter_types(provenance.signature),
            Some([string].as_slice())
        );
        assert!(matches!(
            validate_stored_source_callable(&fixture.store, callable),
            StoredSourceCallableValidation::Valid(_)
        ));
        let warm = publication_state(&fixture.store);
        assert_eq!(
            publish_contextual_source_callable(&mut fixture.store, &prepared),
            Ok(callable)
        );
        let host = DeclaredTypeHost::new_after_global_merge(
            [(&fixture.parsed.arena, &fixture.bound)],
            GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
        )
        .unwrap();
        assert!(plan_source_callable(&fixture.store, &host, declaration, owner, None).is_ok());
        assert_eq!(publication_state(&fixture.store), warm);
        assert!(diagnostics.is_empty());
    }

    #[test]
    fn contextual_direct_call_arrow_keeps_target_parameter_and_independent_return() {
        let mut fixture = QueryFixture::new(
            concat!(
                "declare function consume(callback: (value: number) => number): void; ",
                "consume(value => {});",
            ),
            FileId::new(1_217),
        );
        let declaration = fixture
            .parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::ArrowFunction).then_some(NodeRef::new(
                    fixture.parsed.arena.id(),
                    fixture.file,
                    node,
                ))
            })
            .unwrap();
        let NodeData::ArrowFunction(arrow) =
            &fixture.parsed.arena.get(declaration.node).unwrap().data
        else {
            unreachable!()
        };
        let parameter = NodeRef::new(
            declaration.arena,
            declaration.file,
            arrow.parameters.nodes[0],
        );
        let target_node = fixture
            .parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::FunctionType).then_some(NodeRef::new(
                    fixture.parsed.arena.id(),
                    fixture.file,
                    node,
                ))
            })
            .unwrap();
        let owner = fixture.bound.symbol(declaration).unwrap();
        let parameter_symbol = fixture.bound.symbol(parameter).unwrap();
        let host = DeclaredTypeHost::new_after_global_merge(
            [(&fixture.parsed.arena, &fixture.bound)],
            GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
        )
        .unwrap();

        assert_eq!(
            source_direct_call_argument_arrow_is_exact(&fixture.store, &host, declaration),
            Ok(true)
        );
        let plan = plan_source_callable(&fixture.store, &host, declaration, owner, None).unwrap();
        assert!(plan.parameters[0].is_implicit_any());
        assert_eq!(plan.min_argument_count, 1);
        drop(host);

        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        let target = fixture
            .query_type_node(target_node, &mut diagnostics)
            .unwrap();
        let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
        let number = bootstrap.number_type;
        let string = bootstrap.string_type;
        let void = bootstrap.void_type;
        let prepared = PreparedContextualDirectCallSourceCallable {
            declaration,
            owner_symbol: owner,
            contextual_target: target,
            parameters: vec![ContextualSourceCallableParameter {
                declaration: parameter,
                symbol: parameter_symbol,
                type_: number,
            }],
            flags: SignatureFlags::NONE,
            min_argument_count: 1,
            return_type: void,
        };
        let invalid = PreparedContextualDirectCallSourceCallable {
            parameters: vec![ContextualSourceCallableParameter {
                declaration: parameter,
                symbol: parameter_symbol,
                type_: string,
            }],
            ..prepared.clone()
        };
        let before = publication_state(&fixture.store);
        assert_eq!(
            publish_contextual_direct_call_source_callable(&mut fixture.store, &invalid),
            Err(SourceCallableError::Invariant(
                SourceCallableInvariant::Publication(declaration)
            ))
        );
        assert_eq!(publication_state(&fixture.store), before);

        let callable =
            publish_contextual_direct_call_source_callable(&mut fixture.store, &prepared).unwrap();
        let provenance = fixture.store.source_callable_provenance(callable).unwrap();
        assert_eq!(provenance.contextual_target, Some(target));
        assert_eq!(provenance.contextual_variable, None);
        assert_eq!(
            fixture
                .store
                .callable_signature_parameter_types(provenance.signature),
            Some([number].as_slice())
        );
        assert_eq!(
            fixture
                .store
                .signature(provenance.signature)
                .unwrap()
                .resolved_return_type(),
            Some(void)
        );
        assert!(matches!(
            validate_stored_source_callable(&fixture.store, callable),
            StoredSourceCallableValidation::Valid(_)
        ));
        let warm = publication_state(&fixture.store);
        assert_eq!(
            publish_contextual_direct_call_source_callable(&mut fixture.store, &prepared),
            Ok(callable)
        );
        let host = DeclaredTypeHost::new_after_global_merge(
            [(&fixture.parsed.arena, &fixture.bound)],
            GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
        )
        .unwrap();
        assert!(plan_source_callable(&fixture.store, &host, declaration, owner, None).is_ok());
        assert_eq!(publication_state(&fixture.store), warm);
        drop(host);

        let original_links = fixture
            .store
            .value_symbol_links(parameter_symbol)
            .unwrap()
            .clone();
        assert!(fixture.store.set_value_symbol_links(
            parameter_symbol,
            ValueSymbolLinks {
                resolved_type: Some(string),
                ..ValueSymbolLinks::default()
            },
        ));
        assert_eq!(
            validate_stored_source_callable(&fixture.store, callable),
            StoredSourceCallableValidation::Malformed
        );
        assert_eq!(
            publish_contextual_direct_call_source_callable(&mut fixture.store, &prepared),
            Err(SourceCallableError::Invariant(
                SourceCallableInvariant::InvalidTypeCache(declaration)
            ))
        );
        assert!(
            fixture
                .store
                .set_value_symbol_links(parameter_symbol, original_links)
        );
        assert!(matches!(
            validate_stored_source_callable(&fixture.store, callable),
            StoredSourceCallableValidation::Valid(_)
        ));
        assert!(diagnostics.is_empty());
    }

    #[test]
    fn array_sort_callbacks_retain_bound_tuple_parameter_symbols() {
        let mut fixture = QueryFixture::new(
            concat!(
                "interface Array<T> { sort(compare: (first: T, second: T) => number): this; } ",
                "declare const values: [string, any][]; ",
                "values.sort(([firstKey, firstValue], [secondKey, secondValue]) => 0);",
            ),
            FileId::new(1_250),
        );
        let globals = fixture.store.intrinsic_bootstrap().unwrap().globals;
        let array = fixture
            .bound
            .locals(fixture.bound.source_file())
            .and_then(|locals| fixture.store.symbol_table(locals))
            .and_then(|locals| locals.get_source("Array"))
            .unwrap();
        fixture.store.merge_global_symbol(globals, array).unwrap();
        let declaration = fixture
            .parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::ArrowFunction).then_some(NodeRef::new(
                    fixture.parsed.arena.id(),
                    fixture.file,
                    node,
                ))
            })
            .unwrap();
        let owner = fixture.bound.symbol(declaration).unwrap();
        let host = DeclaredTypeHost::new_after_global_merge(
            [(&fixture.parsed.arena, &fixture.bound)],
            GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
        )
        .unwrap();
        fixture
            .store
            .get_declared_type_of_symbol(&host, array)
            .unwrap();
        let before = publication_state(&fixture.store);

        assert_eq!(
            source_direct_call_argument_arrow_is_exact(&fixture.store, &host, declaration),
            Ok(true),
        );
        let plan = plan_source_callable(&fixture.store, &host, declaration, owner, None).unwrap();
        assert_eq!(plan.parameters.len(), 2);
        assert_eq!(plan.min_argument_count, 2);
        for (index, parameter) in plan.parameters.iter().enumerate() {
            assert!(parameter.is_implicit_any());
            assert_eq!(
                fixture
                    .store
                    .symbol(parameter.symbol)
                    .and_then(|symbol| symbol.name().as_utf8()),
                Some(["__0", "__1"][index]),
            );
        }
        assert_eq!(publication_state(&fixture.store), before);
    }

    #[test]
    fn zero_parameter_callback_targets_accept_multiple_implicit_any_parameters() {
        let mut fixture = QueryFixture::new(
            concat!(
                "function consume(callback: () => number): void {} ",
                "consume((first, second, third, fourth) => {});",
            ),
            FileId::new(1_218),
        );
        let declaration = fixture
            .parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::ArrowFunction).then_some(NodeRef::new(
                    fixture.parsed.arena.id(),
                    fixture.file,
                    node,
                ))
            })
            .unwrap();
        let owner = fixture.bound.symbol(declaration).unwrap();
        let host = DeclaredTypeHost::new_after_global_merge(
            [(&fixture.parsed.arena, &fixture.bound)],
            GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
        )
        .unwrap();
        let before = publication_state(&fixture.store);

        assert_eq!(
            source_direct_call_argument_arrow_is_exact(&fixture.store, &host, declaration),
            Ok(true),
        );
        assert_eq!(
            source_direct_call_arrow_has_zero_parameter_target(&fixture.store, &host, declaration,),
            Ok(true),
        );
        let plan = plan_source_callable(&fixture.store, &host, declaration, owner, None).unwrap();
        let any = fixture.store.intrinsic_bootstrap().unwrap().any_type;
        assert_eq!(plan.parameters.len(), 4);
        assert_eq!(plan.min_argument_count, 4);
        assert!(plan.parameters.iter().all(|parameter| {
            parameter.is_implicit_any() && parameter.base_type(&fixture.store) == Some(any)
        }));
        assert_eq!(publication_state(&fixture.store), before);
        drop(host);

        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        let callable = fixture
            .query_callable(declaration, owner, &mut diagnostics)
            .unwrap();
        let signature = fixture
            .store
            .source_callable_provenance(callable)
            .unwrap()
            .signature;
        let void = fixture.store.intrinsic_bootstrap().unwrap().void_type;
        publish_inferred_source_callable_return(&mut fixture.store, &plan, signature, void)
            .unwrap();
        let provenance = fixture.store.source_callable_provenance(callable).unwrap();
        assert_eq!(provenance.contextual_target, None);
        assert_eq!(provenance.contextual_variable, None);
        assert_eq!(
            fixture
                .store
                .callable_signature_parameter_types(provenance.signature),
            Some([any, any, any, any].as_slice()),
        );
        assert!(matches!(
            validate_stored_source_callable(&fixture.store, callable),
            StoredSourceCallableValidation::Valid(_)
        ));
        let warm = publication_state(&fixture.store);
        assert_eq!(
            fixture.query_callable(declaration, owner, &mut diagnostics),
            Ok(callable),
        );
        let host = DeclaredTypeHost::new_after_global_merge(
            [(&fixture.parsed.arena, &fixture.bound)],
            GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
        )
        .unwrap();
        assert_eq!(
            plan_source_callable(&fixture.store, &host, declaration, owner, None),
            Ok(plan),
        );
        assert_eq!(publication_state(&fixture.store), warm);
        assert!(diagnostics.is_empty());
    }

    #[test]
    fn multiple_implicit_any_callback_parameters_require_zero_arity_targets() {
        for (index, source) in [
            concat!(
                "function consume(callback: (value: number) => number): void {} ",
                "consume((first, second) => {});",
            ),
            concat!(
                "function consume(callback: () => number): void {} ",
                "consume((first: number, second) => {});",
            ),
            concat!(
                "function consume(callback: () => number): void {} ",
                "consume((first, second?) => {});",
            ),
            "const value = (first, second) => {};",
        ]
        .into_iter()
        .enumerate()
        {
            let fixture =
                QueryFixture::new(source, FileId::new(1_219 + u32::try_from(index).unwrap()));
            let declaration = fixture
                .parsed
                .arena
                .iter()
                .find_map(|(node, record)| {
                    (record.kind == SyntaxKind::ArrowFunction).then_some(NodeRef::new(
                        fixture.parsed.arena.id(),
                        fixture.file,
                        node,
                    ))
                })
                .unwrap();
            let owner = fixture.bound.symbol(declaration).unwrap();
            let host = DeclaredTypeHost::new_after_global_merge(
                [(&fixture.parsed.arena, &fixture.bound)],
                GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
            )
            .unwrap();
            let before = publication_state(&fixture.store);

            assert_eq!(
                source_direct_call_arrow_has_zero_parameter_target(
                    &fixture.store,
                    &host,
                    declaration,
                ),
                Ok(false),
                "{source}",
            );
            assert!(
                matches!(
                    plan_source_callable(&fixture.store, &host, declaration, owner, None),
                    Err(SourceCallableError::Unsupported(
                        SourceCallableUnsupported::MissingParameterType(_)
                    ))
                ),
                "{source}",
            );
            assert_eq!(publication_state(&fixture.store), before);
        }
    }

    #[test]
    fn contextual_arrow_rejects_class_method_inputs_before_publication() {
        let mut fixture = QueryFixture::new(
            "class Container { run(): void {} } const callback: () => void = () => {};",
            FileId::new(1_215),
        );
        let declaration = fixture
            .parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::ArrowFunction).then_some(NodeRef::new(
                    fixture.parsed.arena.id(),
                    fixture.file,
                    node,
                ))
            })
            .unwrap();
        let class = fixture
            .parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::ClassDeclaration).then_some(NodeRef::new(
                    fixture.parsed.arena.id(),
                    fixture.file,
                    node,
                ))
            })
            .unwrap();
        let method = fixture
            .parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::MethodDeclaration).then_some(NodeRef::new(
                    fixture.parsed.arena.id(),
                    fixture.file,
                    node,
                ))
            })
            .unwrap();
        let (variable, target_node) = fixture
            .parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                let NodeData::VariableDeclaration(variable) = &record.data else {
                    return None;
                };
                Some((
                    NodeRef::new(fixture.parsed.arena.id(), fixture.file, node),
                    NodeRef::new(fixture.parsed.arena.id(), fixture.file, variable.type_?),
                ))
            })
            .unwrap();
        let owner = fixture.bound.symbol(declaration).unwrap();
        let variable = fixture.bound.symbol(variable).unwrap();
        let class_owner = fixture.bound.symbol(class).unwrap();
        let method_owner = fixture.bound.symbol(method).unwrap();
        let host = DeclaredTypeHost::new_after_global_merge(
            [(&fixture.parsed.arena, &fixture.bound)],
            GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
        )
        .unwrap();
        let class_plan = super::super::classes::plan_nongeneric_class_member_query(
            &fixture.store,
            &host,
            class_owner,
        )
        .unwrap();
        super::super::classes::execute_nongeneric_class_member_query(
            &mut fixture.store,
            &host,
            &class_plan,
        )
        .unwrap();
        drop(host);

        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        let target = fixture
            .query_type_node(target_node, &mut diagnostics)
            .unwrap();
        let method_type = fixture
            .store
            .value_symbol_links(method_owner)
            .and_then(|links| links.resolved_type)
            .unwrap();
        assert_eq!(
            validate_stored_source_callable(&fixture.store, method_type),
            StoredSourceCallableValidation::NotSourceCallable
        );
        let void = fixture.store.intrinsic_bootstrap().unwrap().void_type;
        let valid = PreparedContextualSourceCallable {
            declaration,
            owner_symbol: owner,
            variable_symbol: variable,
            contextual_target: target,
            parameters: Vec::new(),
            flags: SignatureFlags::NONE,
            min_argument_count: 0,
            return_type: void,
        };

        for invalid in [
            PreparedContextualSourceCallable {
                variable_symbol: method_owner,
                ..valid.clone()
            },
            PreparedContextualSourceCallable {
                contextual_target: method_type,
                ..valid.clone()
            },
        ] {
            let before = publication_state(&fixture.store);
            let link_lengths = fixture.store.checker_link_allocated_lengths();
            assert_eq!(
                publish_contextual_source_callable(&mut fixture.store, &invalid),
                Err(SourceCallableError::Invariant(
                    SourceCallableInvariant::Publication(declaration)
                ))
            );
            assert_eq!(publication_state(&fixture.store), before);
            assert_eq!(fixture.store.checker_link_allocated_lengths(), link_lengths);
            assert!(
                fixture
                    .store
                    .source_callable_type_for_owner(owner)
                    .is_none()
            );
            assert!(fixture.store.signature_links(declaration).is_none());
        }

        let callable = publish_contextual_source_callable(&mut fixture.store, &valid).unwrap();
        let warm = publication_state(&fixture.store);
        assert_eq!(
            publish_contextual_source_callable(&mut fixture.store, &valid),
            Ok(callable)
        );
        assert_eq!(publication_state(&fixture.store), warm);
        assert!(diagnostics.is_empty());
    }

    #[test]
    fn incomplete_contextual_provenance_is_rejected_on_warm_replay() {
        let mut fixture = QueryFixture::new(
            "const result = invoke((value: string) => value);",
            FileId::new(1_214),
        );
        let declaration = fixture
            .parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::ArrowFunction).then_some(NodeRef::new(
                    fixture.parsed.arena.id(),
                    fixture.file,
                    node,
                ))
            })
            .unwrap();
        let variable = fixture
            .parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::VariableDeclaration).then_some(NodeRef::new(
                    fixture.parsed.arena.id(),
                    fixture.file,
                    node,
                ))
            })
            .unwrap();
        let owner = fixture.bound.symbol(declaration).unwrap();
        let variable = fixture.bound.symbol(variable).unwrap();
        let host = DeclaredTypeHost::new_after_global_merge(
            [(&fixture.parsed.arena, &fixture.bound)],
            GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
        )
        .unwrap();
        let plan = plan_source_callable(&fixture.store, &host, declaration, owner, None).unwrap();
        drop(host);

        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        let callable = fixture
            .query_callable(declaration, owner, &mut diagnostics)
            .unwrap();
        let provenance = fixture.store.source_callable_provenance(callable).unwrap();
        let string = fixture.store.intrinsic_bootstrap().unwrap().string_type;
        publish_inferred_source_callable_return(
            &mut fixture.store,
            &plan,
            provenance.signature,
            string,
        )
        .unwrap();

        for (contextual_target, contextual_variable) in
            [(Some(string), None), (None, Some(variable))]
        {
            fixture.store.replace_source_callable_provenance_for_test(
                callable,
                Some(SourceCallableProvenance {
                    contextual_target,
                    contextual_variable,
                    ..provenance
                }),
            );
            assert_eq!(
                validate_stored_source_callable(&fixture.store, callable),
                StoredSourceCallableValidation::Malformed
            );
        }
        fixture
            .store
            .replace_source_callable_provenance_for_test(callable, Some(provenance));
        assert!(matches!(
            validate_stored_source_callable(&fixture.store, callable),
            StoredSourceCallableValidation::Valid(_)
        ));
        assert!(diagnostics.is_empty());
    }

    #[test]
    fn ordinary_source_functions_accept_unannotated_identifier_parameters() {
        let mut fixture = QueryFixture::new(
            "function commented(\n/* first */ value,\n/* second */ other,\n) {}",
            FileId::new(1_047),
        );
        let declaration = fixture
            .parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::FunctionDeclaration).then_some(NodeRef::new(
                    fixture.parsed.arena.id(),
                    fixture.file,
                    node,
                ))
            })
            .unwrap();
        let owner = fixture.bound.symbol(declaration).unwrap();
        let host = DeclaredTypeHost::new_after_global_merge(
            [(&fixture.parsed.arena, &fixture.bound)],
            GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
        )
        .unwrap();

        let plan = plan_source_callable(&fixture.store, &host, declaration, owner, None).unwrap();
        assert_eq!(plan.parameters.len(), 2);
        assert_eq!(plan.min_argument_count, 2);
        assert_eq!(plan.return_type, SourceCallableReturnPlan::Inferred);
        let any = fixture.store.intrinsic_bootstrap().unwrap().any_type;
        for parameter in &plan.parameters {
            assert!(parameter.is_implicit_any());
            assert_eq!(parameter.explicit_type_node(), None);
            assert_eq!(parameter.base_type(&fixture.store), Some(any));
            assert_eq!(parameter.type_node, parameter.identity_node);
        }
        drop(host);

        reserve_source_callable_capacities(&mut fixture.store, &[&plan]).unwrap();
        let pending = begin_source_callable(&mut fixture.store, &plan, &[])
            .unwrap()
            .unwrap();
        finalize_source_callable_structure(&mut fixture.store, &plan, pending).unwrap();
        let mut prepared = fixture
            .store
            .prepare_type_query_types(&[], &[], &[], 0, 0)
            .unwrap();
        publish_source_callable_parameter_types(
            &mut fixture.store,
            None,
            &[PendingSourceCallableParameterTypes {
                plan: plan.clone(),
                base_types: vec![any, any],
            }],
            &mut prepared,
        )
        .unwrap();
        assert_eq!(
            fixture
                .store
                .callable_signature_parameter_types(pending.signature),
            Some([any, any].as_slice())
        );
        for parameter in &plan.parameters {
            assert_eq!(
                fixture.store.value_symbol_links(parameter.symbol),
                Some(&ValueSymbolLinks {
                    resolved_type: Some(any),
                    ..ValueSymbolLinks::default()
                })
            );
        }
        let void = fixture.store.intrinsic_bootstrap().unwrap().void_type;
        assert_eq!(
            publish_inferred_source_callable_return(
                &mut fixture.store,
                &plan,
                pending.signature,
                void,
            ),
            Ok(void)
        );
        assert!(matches!(
            validate_stored_source_callable(&fixture.store, pending.type_),
            StoredSourceCallableValidation::Valid(_)
        ));
    }

    #[test]
    fn direct_unparenthesized_source_arrows_accept_one_implicit_any_parameter() {
        let mut fixture = QueryFixture::new("var value = input => <any>{};", FileId::new(1_087));
        let declaration = fixture
            .parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::ArrowFunction).then_some(NodeRef::new(
                    fixture.parsed.arena.id(),
                    fixture.file,
                    node,
                ))
            })
            .unwrap();
        let owner = fixture.bound.symbol(declaration).unwrap();
        let host = DeclaredTypeHost::new_after_global_merge(
            [(&fixture.parsed.arena, &fixture.bound)],
            GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
        )
        .unwrap();
        let plan = plan_source_callable(&fixture.store, &host, declaration, owner, None).unwrap();
        assert_eq!(plan.family, SourceCallableFamily::ArrowFunction);
        assert_eq!(plan.parameters.len(), 1);
        assert_eq!(plan.min_argument_count, 1);
        assert!(plan.parameters[0].is_implicit_any());
        let any = fixture.store.intrinsic_bootstrap().unwrap().any_type;
        assert_eq!(plan.parameters[0].base_type(&fixture.store), Some(any));
        drop(host);

        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        let callable = fixture
            .query_callable(declaration, owner, &mut diagnostics)
            .unwrap();
        let signature = fixture
            .store
            .source_callable_provenance(callable)
            .unwrap()
            .signature;
        assert_eq!(
            fixture.store.callable_signature_parameter_types(signature),
            Some([any].as_slice())
        );
        publish_inferred_source_callable_return(&mut fixture.store, &plan, signature, any).unwrap();
        let warm = publication_state(&fixture.store);
        assert_eq!(
            fixture.query_callable(declaration, owner, &mut diagnostics),
            Ok(callable)
        );
        assert_eq!(publication_state(&fixture.store), warm);
        assert!(matches!(
            validate_stored_source_callable(&fixture.store, callable),
            StoredSourceCallableValidation::Valid(_)
        ));
        assert!(diagnostics.is_empty());
    }

    #[test]
    fn javascript_direct_arrows_accept_parenthesized_untyped_parameters_cold_and_warm() {
        for (index, (source, parenthesized)) in [
            ("const callback = name => {};", false),
            ("const callback = (name) => {};", true),
        ]
        .into_iter()
        .enumerate()
        {
            let mut fixture = QueryFixture::javascript(
                source,
                FileId::new(1_310 + u32::try_from(index).unwrap()),
            );
            let declaration = fixture
                .parsed
                .arena
                .iter()
                .find_map(|(node, record)| {
                    (record.kind == SyntaxKind::ArrowFunction).then_some(NodeRef::new(
                        fixture.parsed.arena.id(),
                        fixture.file,
                        node,
                    ))
                })
                .unwrap();
            let owner = fixture.bound.symbol(declaration).unwrap();
            let host = DeclaredTypeHost::new_after_global_merge(
                [(&fixture.parsed.arena, &fixture.bound)],
                GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
            )
            .unwrap();
            let before = publication_state(&fixture.store);

            let plan = plan_source_callable(&fixture.store, &host, declaration, owner, None)
                .unwrap_or_else(|error| panic!("{source}: {error:?}"));
            let NodeData::ArrowFunction(arrow) =
                &fixture.parsed.arena.get(declaration.node).unwrap().data
            else {
                panic!("the JavaScript fixture must retain its direct arrow")
            };
            let parameter = fixture.parsed.arena.get(arrow.parameters.nodes[0]).unwrap();
            if parenthesized {
                assert!(arrow.parameters.range.start < parameter.range.start);
                assert!(arrow.parameters.range.end > parameter.range.end);
            } else {
                assert_eq!(arrow.parameters.range, parameter.range);
            }
            assert_eq!(plan.flags, SignatureFlags::IS_UNTYPED_SIGNATURE_IN_JS_FILE,);
            assert_eq!(plan.parameters.len(), 1);
            assert!(plan.parameters[0].is_implicit_any());
            assert_eq!(plan.min_argument_count, 1);
            assert_eq!(publication_state(&fixture.store), before);
            drop(host);

            let mut diagnostics = CanonicalCheckerDiagnostics::default();
            let callable = fixture
                .query_callable(declaration, owner, &mut diagnostics)
                .unwrap();
            let signature = fixture
                .store
                .source_callable_provenance(callable)
                .unwrap()
                .signature;
            assert_eq!(
                fixture.store.signature(signature).unwrap().flags(),
                SignatureFlags::IS_UNTYPED_SIGNATURE_IN_JS_FILE,
            );
            let void = fixture.store.intrinsic_bootstrap().unwrap().void_type;
            publish_inferred_source_callable_return(&mut fixture.store, &plan, signature, void)
                .unwrap();
            assert!(matches!(
                validate_stored_source_callable(&fixture.store, callable),
                StoredSourceCallableValidation::Valid(_)
            ));
            let warm = publication_state(&fixture.store);
            assert_eq!(
                fixture.query_callable(declaration, owner, &mut diagnostics),
                Ok(callable),
            );
            assert_eq!(publication_state(&fixture.store), warm);
            assert!(diagnostics.is_empty());
        }
    }

    #[test]
    fn javascript_jsdoc_generic_arrows_publish_required_union_parameters_cold_and_warm() {
        let parsed = parse_javascript_source_file(concat!(
            "/**\n",
            " * @template T\n",
            " * @param {T|undefined} value value or not\n",
            " * @returns {T} result value\n",
            " */\n",
            "const cloneObjectGood = value => /** @type {T} */({ ...value });",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(1_317);
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source("\"/project/jsdoc-generic.js\""),
                    CanonicalSourceLanguage::JavaScript,
                    false,
                    CanonicalModuleState::Script,
                ),
            )
            .unwrap();
        binder
            .bind_javascript_declaration_slice(&parsed.arena, file)
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
        let declaration = parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::ArrowFunction).then_some(NodeRef::new(
                    parsed.arena.id(),
                    file,
                    node,
                ))
            })
            .unwrap();
        let bound = context.file(file).unwrap().1.clone();
        let owner = bound.symbol(declaration).unwrap();
        let host = DeclaredTypeHost::new_after_global_merge(
            [(&parsed.arena, &bound)],
            GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
        )
        .unwrap();
        let global_types = context.global_types().clone();
        let targets = CanonicalArrayTargets::from_global_types(&global_types);
        let cold = generic_transaction_state(context.store());
        let plan = plan_source_callable(context.store(), &host, declaration, owner, Some(targets))
            .unwrap();
        assert_eq!(plan.family, SourceCallableFamily::ArrowFunction);
        assert_eq!(plan.type_parameters.len(), 1);
        assert_eq!(plan.parameters.len(), 1);
        assert_eq!(plan.min_argument_count, 1);
        assert!(!plan.parameters[0].optional);
        assert_eq!(generic_transaction_state(context.store()), cold);

        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        let callable = CanonicalTypeQuery::new_with_global_types(
            context.store_mut_for_test(),
            &host,
            &global_types,
            CanonicalTypeQueryOptions::default(),
            &mut diagnostics,
        )
        .unwrap()
        .get_type_of_source_callable(declaration, owner)
        .unwrap();
        let provenance = context
            .store()
            .source_callable_provenance(callable)
            .unwrap();
        let signature = context.store().signature(provenance.signature).unwrap();
        let [type_parameter] = signature.type_parameters() else {
            panic!("expected the binder-owned JSDoc template identity")
        };
        let type_parameter = *type_parameter;
        let [parameter_type] = context
            .store()
            .callable_signature_parameter_types(provenance.signature)
            .unwrap()
        else {
            panic!("expected the documented required parameter")
        };
        let TypeData::Union(union) = context
            .store()
            .type_payload(*parameter_type)
            .unwrap()
            .data()
        else {
            panic!("the required parameter must retain T | undefined")
        };
        let undefined = context
            .store()
            .intrinsic_bootstrap()
            .unwrap()
            .undefined_type;
        assert_eq!(signature.min_argument_count(), 1);
        assert_eq!(union.union.types.len(), 2);
        assert!(union.union.types.contains(&type_parameter));
        assert!(union.union.types.contains(&undefined));
        assert_eq!(
            provenance.generic_return_type_parameter,
            Some(type_parameter)
        );

        let return_type = CanonicalTypeQuery::new_with_global_types(
            context.store_mut_for_test(),
            &host,
            &global_types,
            CanonicalTypeQueryOptions::default(),
            &mut diagnostics,
        )
        .unwrap()
        .get_return_type_of_signature(provenance.signature)
        .unwrap();
        assert_eq!(return_type, type_parameter);
        assert_eq!(
            context.type_to_string(callable).unwrap(),
            "<T>(value: T | undefined) => T",
        );
        assert!(matches!(
            validate_stored_source_callable(context.store(), callable),
            StoredSourceCallableValidation::Valid(_)
        ));

        let warm = generic_transaction_state(context.store());
        let replay = CanonicalTypeQuery::new_with_global_types(
            context.store_mut_for_test(),
            &host,
            &global_types,
            CanonicalTypeQueryOptions::default(),
            &mut diagnostics,
        )
        .unwrap()
        .get_type_of_source_callable(declaration, owner)
        .unwrap();
        assert_eq!(replay, callable);
        assert_eq!(generic_transaction_state(context.store()), warm);
        assert!(diagnostics.is_empty(), "{diagnostics:?}");
    }

    #[test]
    fn documented_javascript_satisfies_arrows_accept_multiple_parameters_cold_and_warm() {
        let source = concat!(
            "/**\n",
            " * @satisfies {(first: string, ...rest: number[]) => void}\n",
            " * @param {string} first\n",
            " * @param {string | number} second\n",
            " */\n",
            "const callback = (first, second) => {};",
        );
        let mut fixture = QueryFixture::javascript(source, FileId::new(1_318));
        let declaration = fixture
            .parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::ArrowFunction).then_some(NodeRef::new(
                    fixture.parsed.arena.id(),
                    fixture.file,
                    node,
                ))
            })
            .unwrap();
        let owner = fixture.bound.symbol(declaration).unwrap();
        let host = DeclaredTypeHost::new_after_global_merge(
            [(&fixture.parsed.arena, &fixture.bound)],
            GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
        )
        .unwrap();
        let cold = publication_state(&fixture.store);

        let plan = plan_source_callable(&fixture.store, &host, declaration, owner, None).unwrap();
        assert_eq!(plan.parameters.len(), 2);
        assert_eq!(plan.min_argument_count, 2);
        assert_eq!(plan.flags, SignatureFlags::IS_UNTYPED_SIGNATURE_IN_JS_FILE);
        assert!(
            plan.parameters
                .iter()
                .all(|parameter| parameter.is_implicit_any())
        );
        assert_eq!(publication_state(&fixture.store), cold);
        drop(host);

        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        let callable = fixture
            .query_callable(declaration, owner, &mut diagnostics)
            .unwrap();
        let signature = fixture
            .store
            .source_callable_provenance(callable)
            .unwrap()
            .signature;
        let any = fixture.store.intrinsic_bootstrap().unwrap().any_type;
        assert_eq!(
            fixture.store.callable_signature_parameter_types(signature),
            Some([any, any].as_slice()),
        );
        let void = fixture.store.intrinsic_bootstrap().unwrap().void_type;
        publish_inferred_source_callable_return(&mut fixture.store, &plan, signature, void)
            .unwrap();
        assert!(matches!(
            validate_stored_source_callable(&fixture.store, callable),
            StoredSourceCallableValidation::Valid(_)
        ));

        let warm = publication_state(&fixture.store);
        assert_eq!(
            fixture.query_callable(declaration, owner, &mut diagnostics),
            Ok(callable),
        );
        assert_eq!(publication_state(&fixture.store), warm);
        assert!(diagnostics.is_empty());
    }

    #[test]
    fn undocumented_javascript_arrows_do_not_admit_multiple_untyped_parameters() {
        for (index, source) in [
            "const callback = (first, second) => {};",
            concat!(
                "/** @param {string} first */\n",
                "const callback = (first, second) => {};",
            ),
            concat!(
                "/**\n",
                " * @satisfies {(first: string, ...rest: number[]) => void}\n",
                " * @param {string} first\n",
                " * @param {string} unexpected\n",
                " */\n",
                "const callback = (first, second) => {};",
            ),
        ]
        .into_iter()
        .enumerate()
        {
            let fixture = QueryFixture::javascript(
                source,
                FileId::new(1_319 + u32::try_from(index).unwrap()),
            );
            let declaration = fixture
                .parsed
                .arena
                .iter()
                .find_map(|(node, record)| {
                    (record.kind == SyntaxKind::ArrowFunction).then_some(NodeRef::new(
                        fixture.parsed.arena.id(),
                        fixture.file,
                        node,
                    ))
                })
                .unwrap();
            let owner = fixture.bound.symbol(declaration).unwrap();
            let host = DeclaredTypeHost::new_after_global_merge(
                [(&fixture.parsed.arena, &fixture.bound)],
                GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
            )
            .unwrap();
            let cold = publication_state(&fixture.store);

            assert!(matches!(
                plan_source_callable(&fixture.store, &host, declaration, owner, None),
                Err(SourceCallableError::Unsupported(
                    SourceCallableUnsupported::MissingParameterType(_)
                ))
            ));
            assert_eq!(publication_state(&fixture.store), cold);
        }
    }

    #[test]
    fn jsdoc_callback_arrows_publish_typed_parameters_without_inventing_targets() {
        let parsed = parse_javascript_source_file(concat!(
            "/** @callback NS.MyCallback\n",
            " * @param {string} name\n",
            " * @returns {void}\n",
            " */\n",
            "/** @type {NS.MyCallback} */\n",
            "const f = (name) => {};",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(1_314);
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source("\"/project/c.js\""),
                    CanonicalSourceLanguage::JavaScript,
                    false,
                    CanonicalModuleState::Script,
                ),
            )
            .unwrap();
        binder
            .bind_javascript_declaration_slice(&parsed.arena, file)
            .unwrap();
        let options = CanonicalCheckerOptions::default();
        let mut context = CanonicalCheckerContext::new(
            binder.finish(),
            [(file, &parsed.arena)].into_iter().collect(),
            options,
        )
        .unwrap();
        let source = NodeRef::new(parsed.arena.id(), file, parsed.source_file);
        let comments = plan_javascript_source_jsdoc(&parsed.arena, source).unwrap();
        let [declaration] = comments.declarations() else {
            panic!("the fixture must retain one callback-annotated variable")
        };
        let callback = declaration
            .type_()
            .and_then(super::super::jsdoc::PlannedJsDocType::resolved_callback)
            .unwrap();
        let global_types = context.global_types().clone();
        let resolved = resolve_planned_jsdoc_callback_signature(
            context.store_mut_for_test(),
            &global_types,
            options,
            callback,
            &[],
        )
        .unwrap();
        let bound = context.file(file).unwrap().1.clone();
        let arrow = parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::ArrowFunction).then_some(NodeRef::new(
                    parsed.arena.id(),
                    file,
                    node,
                ))
            })
            .unwrap();
        let owner = bound.symbol(arrow).unwrap();
        let host = DeclaredTypeHost::new_after_global_merge(
            [(&parsed.arena, &bound)],
            GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
        )
        .unwrap();
        let targets = CanonicalArrayTargets::from_global_types(&global_types);
        let plan =
            plan_source_callable(context.store(), &host, arrow, owner, Some(targets)).unwrap();
        assert!(plan.parameters[0].is_implicit_any());

        let (callable, contextual) = publish_jsdoc_contextual_source_callable(
            context.store_mut_for_test(),
            &host,
            &plan,
            &resolved,
        )
        .unwrap();
        let (string, void) = {
            let bootstrap = context.store().intrinsic_bootstrap().unwrap();
            (bootstrap.string_type, bootstrap.void_type)
        };
        assert!(!contextual.parameters[0].is_implicit_any());
        assert_eq!(
            contextual.parameters[0].base_type(context.store()),
            Some(string),
        );
        let provenance = context
            .store()
            .source_callable_provenance(callable)
            .unwrap();
        assert!(provenance.contextual_target.is_none());
        assert!(provenance.contextual_variable.is_none());
        assert_eq!(
            context
                .store()
                .signature(provenance.signature)
                .unwrap()
                .flags(),
            SignatureFlags::IS_UNTYPED_SIGNATURE_IN_JS_FILE,
        );
        assert_eq!(
            context
                .store()
                .signature(provenance.signature)
                .and_then(Signature::resolved_return_type),
            Some(void),
        );
        assert_eq!(
            context
                .store()
                .callable_signature_parameter_types(provenance.signature),
            Some([string].as_slice()),
        );
        assert_eq!(
            context
                .store()
                .value_symbol_links(contextual.parameters[0].symbol),
            Some(&ValueSymbolLinks {
                resolved_type: Some(string),
                ..ValueSymbolLinks::default()
            }),
        );
        assert!(matches!(
            validate_stored_source_callable(context.store(), callable),
            StoredSourceCallableValidation::Valid(_)
        ));

        let warm = publication_state(context.store());
        let replay =
            plan_source_callable(context.store(), &host, arrow, owner, Some(targets)).unwrap();
        assert!(!replay.parameters[0].is_implicit_any());
        assert_eq!(
            publish_jsdoc_contextual_source_callable(
                context.store_mut_for_test(),
                &host,
                &replay,
                &resolved,
            )
            .unwrap()
            .0,
            callable,
        );
        assert_eq!(publication_state(context.store()), warm);
    }

    #[test]
    fn ambiguous_union_array_arrows_accept_one_parenthesized_implicit_any_parameter() {
        let mut fixture = QueryFixture::new(
            concat!(
                "declare function test(",
                "arg: Record<string, (arg: string) => void> | ",
                "Array<(arg: number) => void>): void; ",
                "test([(arg) => { arg; }]);"
            ),
            FileId::new(1_120),
        );
        let declaration = fixture
            .parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::ArrowFunction).then_some(NodeRef::new(
                    fixture.parsed.arena.id(),
                    fixture.file,
                    node,
                ))
            })
            .unwrap();
        let owner = fixture.bound.symbol(declaration).unwrap();
        let host = DeclaredTypeHost::new_after_global_merge(
            [(&fixture.parsed.arena, &fixture.bound)],
            GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
        )
        .unwrap();
        let plan = plan_source_callable(&fixture.store, &host, declaration, owner, None).unwrap();
        let any = fixture.store.intrinsic_bootstrap().unwrap().any_type;
        assert_eq!(plan.parameters.len(), 1);
        assert!(plan.parameters[0].is_implicit_any());
        assert_eq!(plan.parameters[0].base_type(&fixture.store), Some(any));
        drop(host);

        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        let callable = fixture
            .query_callable(declaration, owner, &mut diagnostics)
            .unwrap();
        let signature = fixture
            .store
            .source_callable_provenance(callable)
            .unwrap()
            .signature;
        let void = fixture.store.intrinsic_bootstrap().unwrap().void_type;
        publish_inferred_source_callable_return(&mut fixture.store, &plan, signature, void)
            .unwrap();
        let warm = publication_state(&fixture.store);
        assert_eq!(
            fixture.query_callable(declaration, owner, &mut diagnostics),
            Ok(callable)
        );
        assert_eq!(publication_state(&fixture.store), warm);
        assert!(diagnostics.is_empty());
    }

    #[test]
    fn nonambiguous_array_arrows_do_not_receive_implicit_any() {
        for (index, source) in [
            concat!(
                "declare function test(arg: Array<(arg: number) => void>): void; ",
                "test([(arg) => { arg; }]);"
            ),
            concat!(
                "declare function test(",
                "arg: Record<string, (arg: string) => void> | ",
                "Array<(arg: string) => void>): void; ",
                "test([(arg) => { arg; }]);"
            ),
            concat!(
                "declare function test(",
                "arg: Record<string, (arg: string) => void> | ",
                "Array<(arg: number) => void>): void; ",
                "function outer() { test([(arg) => { arg; }]); }"
            ),
        ]
        .into_iter()
        .enumerate()
        {
            let fixture =
                QueryFixture::new(source, FileId::new(1_121 + u32::try_from(index).unwrap()));
            let declaration = fixture
                .parsed
                .arena
                .iter()
                .find_map(|(node, record)| {
                    (record.kind == SyntaxKind::ArrowFunction).then_some(NodeRef::new(
                        fixture.parsed.arena.id(),
                        fixture.file,
                        node,
                    ))
                })
                .unwrap();
            let owner = fixture.bound.symbol(declaration).unwrap();
            let host = DeclaredTypeHost::new_after_global_merge(
                [(&fixture.parsed.arena, &fixture.bound)],
                GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
            )
            .unwrap();

            assert!(
                matches!(
                    plan_source_callable(&fixture.store, &host, declaration, owner, None),
                    Err(SourceCallableError::Unsupported(
                        SourceCallableUnsupported::MissingParameterType(_)
                    ))
                ),
                "{source}"
            );
        }
    }

    #[test]
    fn contextual_nested_and_parenthesized_implicit_any_arrows_remain_unsupported() {
        for (index, source) in [
            "const contextual: (input: string) => string = input => input;",
            "const result = invoke(input => input);",
            "const parenthesized = (input) => input;",
            "const annotated_return = (input): string => input;",
            "function outer() { const nested = input => input; }",
            "const first = input => input, second = 1;",
        ]
        .into_iter()
        .enumerate()
        {
            let fixture =
                QueryFixture::new(source, FileId::new(1_088 + u32::try_from(index).unwrap()));
            let declaration = fixture
                .parsed
                .arena
                .iter()
                .find_map(|(node, record)| {
                    (record.kind == SyntaxKind::ArrowFunction).then_some(NodeRef::new(
                        fixture.parsed.arena.id(),
                        fixture.file,
                        node,
                    ))
                })
                .unwrap();
            let owner = fixture.bound.symbol(declaration).unwrap();
            let host = DeclaredTypeHost::new_after_global_merge(
                [(&fixture.parsed.arena, &fixture.bound)],
                GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
            )
            .unwrap();
            let before = publication_state(&fixture.store);

            assert!(
                matches!(
                    plan_source_callable(&fixture.store, &host, declaration, owner, None),
                    Err(SourceCallableError::Unsupported(
                        SourceCallableUnsupported::MissingParameterType(_)
                    ))
                ),
                "{source}"
            );
            assert_eq!(publication_state(&fixture.store), before);
        }
    }

    #[test]
    fn async_arrows_require_authenticated_zero_parameter_inferred_shapes() {
        for (index, source) in [
            "const value = async () => {};",
            "const value = async () => 1;",
            "const value = { f: async () => { await dependency.f(); } };",
        ]
        .into_iter()
        .enumerate()
        {
            let fixture =
                QueryFixture::new(source, FileId::new(1_280 + u32::try_from(index).unwrap()));
            let declaration = fixture
                .parsed
                .arena
                .iter()
                .find_map(|(node, record)| {
                    (record.kind == SyntaxKind::ArrowFunction).then_some(NodeRef::new(
                        fixture.parsed.arena.id(),
                        fixture.file,
                        node,
                    ))
                })
                .unwrap();
            let owner = fixture.bound.symbol(declaration).unwrap();
            let host = DeclaredTypeHost::new_after_global_merge(
                [(&fixture.parsed.arena, &fixture.bound)],
                GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
            )
            .unwrap();
            let before = publication_state(&fixture.store);

            let plan = plan_source_callable(&fixture.store, &host, declaration, owner, None)
                .unwrap_or_else(|error| panic!("{source}: {error:?}"));
            assert!(plan.is_async);
            assert!(plan.parameters.is_empty());
            assert!(plan.return_type.is_inferred());
            assert_eq!(plan.family, SourceCallableFamily::ArrowFunction);
            assert_eq!(publication_state(&fixture.store), before);
        }

        for (index, source) in [
            "const value = async (input: number) => input;",
            "const value = async (): any => 1;",
        ]
        .into_iter()
        .enumerate()
        {
            let fixture =
                QueryFixture::new(source, FileId::new(1_283 + u32::try_from(index).unwrap()));
            let declaration = fixture
                .parsed
                .arena
                .iter()
                .find_map(|(node, record)| {
                    (record.kind == SyntaxKind::ArrowFunction).then_some(NodeRef::new(
                        fixture.parsed.arena.id(),
                        fixture.file,
                        node,
                    ))
                })
                .unwrap();
            let owner = fixture.bound.symbol(declaration).unwrap();
            let host = DeclaredTypeHost::new_after_global_merge(
                [(&fixture.parsed.arena, &fixture.bound)],
                GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
            )
            .unwrap();
            assert!(
                matches!(
                    plan_source_callable(&fixture.store, &host, declaration, owner, None),
                    Err(SourceCallableError::Unsupported(
                        SourceCallableUnsupported::Async(_)
                    ))
                ),
                "{source}",
            );
        }

        let fixture = QueryFixture::with_source_facts(
            "const value = async () => {};",
            FileId::new(1_285),
            true,
            CanonicalModuleState::Script,
        );
        let declaration = fixture
            .parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::ArrowFunction).then_some(NodeRef::new(
                    fixture.parsed.arena.id(),
                    fixture.file,
                    node,
                ))
            })
            .unwrap();
        let owner = fixture.bound.symbol(declaration).unwrap();
        let host = DeclaredTypeHost::new_after_global_merge(
            [(&fixture.parsed.arena, &fixture.bound)],
            GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
        )
        .unwrap();
        assert!(matches!(
            plan_source_callable(&fixture.store, &host, declaration, owner, None),
            Err(SourceCallableError::Unsupported(
                SourceCallableUnsupported::Async(_)
            ))
        ));
    }

    #[test]
    fn async_jsx_functions_preserve_their_exact_zero_parameter_return_shape() {
        let fixture = QueryFixture::jsx(
            "async function render() { return <view />; }",
            FileId::new(1_271),
        );
        let declaration = fixture
            .parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::FunctionDeclaration).then_some(NodeRef::new(
                    fixture.parsed.arena.id(),
                    fixture.file,
                    node,
                ))
            })
            .unwrap();
        let owner = fixture.bound.symbol(declaration).unwrap();
        let host = DeclaredTypeHost::new_after_global_merge(
            [(&fixture.parsed.arena, &fixture.bound)],
            GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
        )
        .unwrap();
        let before = publication_state(&fixture.store);

        let plan = plan_source_callable(&fixture.store, &host, declaration, owner, None).unwrap();
        assert!(plan.is_async);
        assert_eq!(plan.family, SourceCallableFamily::FunctionDeclaration);
        assert!(plan.parameters.is_empty());
        assert_eq!(plan.return_type, SourceCallableReturnPlan::Inferred);
        assert_eq!(plan.flags, SignatureFlags::NONE);
        assert_eq!(publication_state(&fixture.store), before);

        for (index, source) in [
            "async function render(value: string) { return <view />; }",
            "async function render(): any { return <view />; }",
            "async function render() { return <first />; return <second />; }",
        ]
        .into_iter()
        .enumerate()
        {
            let fixture =
                QueryFixture::jsx(source, FileId::new(1_272 + u32::try_from(index).unwrap()));
            let declaration = fixture
                .parsed
                .arena
                .iter()
                .find_map(|(node, record)| {
                    (record.kind == SyntaxKind::FunctionDeclaration).then_some(NodeRef::new(
                        fixture.parsed.arena.id(),
                        fixture.file,
                        node,
                    ))
                })
                .unwrap();
            let owner = fixture.bound.symbol(declaration).unwrap();
            let host = DeclaredTypeHost::new_after_global_merge(
                [(&fixture.parsed.arena, &fixture.bound)],
                GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
            )
            .unwrap();

            assert!(
                matches!(
                    plan_source_callable(&fixture.store, &host, declaration, owner, None),
                    Err(SourceCallableError::Unsupported(
                        SourceCallableUnsupported::Async(_)
                    ))
                ),
                "{source}"
            );
        }

        let ordinary =
            QueryFixture::jsx("async function render() { return 1; }", FileId::new(1_276));
        let declaration = ordinary
            .parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::FunctionDeclaration).then_some(NodeRef::new(
                    ordinary.parsed.arena.id(),
                    ordinary.file,
                    node,
                ))
            })
            .unwrap();
        let owner = ordinary.bound.symbol(declaration).unwrap();
        let host = DeclaredTypeHost::new_after_global_merge(
            [(&ordinary.parsed.arena, &ordinary.bound)],
            GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
        )
        .unwrap();
        let plan = plan_source_callable(&ordinary.store, &host, declaration, owner, None).unwrap();
        assert!(plan.is_async);
        assert_eq!(plan.family, SourceCallableFamily::FunctionDeclaration);
    }

    #[test]
    fn javascript_duplicate_implementations_publish_only_the_first_signature() {
        let mut fixture = QueryFixture::javascript(
            "function repeated() {} function repeated(arg) {}",
            FileId::new(8_940),
        );
        let source = fixture
            .parsed
            .arena
            .get(fixture.parsed.source_file)
            .unwrap();
        let NodeData::SourceFile(source) = &source.data else {
            panic!("expected the duplicate fixture source file")
        };
        let [first, second] = source.statements.nodes.as_slice() else {
            panic!("expected exactly two duplicate implementations")
        };
        let first = NodeRef::new(fixture.parsed.arena.id(), fixture.file, *first);
        let second = NodeRef::new(fixture.parsed.arena.id(), fixture.file, *second);
        let owner = fixture.bound.symbol(first).unwrap();
        assert_eq!(fixture.bound.symbol(second), Some(owner));

        let host = DeclaredTypeHost::new_after_global_merge(
            [(&fixture.parsed.arena, &fixture.bound)],
            GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
        )
        .unwrap();
        let before = publication_state(&fixture.store);
        assert!(valid_javascript_duplicate_function_owner_shape(
            &fixture.store,
            &host,
            owner,
            first,
        ));
        assert!(!valid_javascript_duplicate_function_owner_shape(
            &fixture.store,
            &host,
            owner,
            second,
        ));
        assert!(!valid_source_function_owner_shape(
            &fixture.store,
            owner,
            first,
        ));

        let canonical = plan_source_callable(&fixture.store, &host, first, owner, None).unwrap();
        assert!(canonical.parameters.is_empty());
        assert_eq!(canonical.min_argument_count, 0);
        assert_eq!(canonical.flags, SignatureFlags::NONE);

        let secondary = plan_javascript_duplicate_function_implementation(
            &fixture.store,
            &host,
            second,
            owner,
            None,
        )
        .unwrap();
        assert_eq!(secondary.declaration, second);
        assert_eq!(secondary.parameters.len(), 1);
        assert!(secondary.parameters[0].is_implicit_any());
        assert_eq!(
            secondary.parameters[0].base_type(&fixture.store),
            Some(fixture.store.intrinsic_bootstrap().unwrap().any_type),
        );
        assert!(
            fixture
                .store
                .value_symbol_links(secondary.parameters[0].symbol)
                .is_none()
        );
        assert!(matches!(
            source_callable_state(&fixture.store, &secondary, false),
            Err(SourceCallableError::Invariant(
                SourceCallableInvariant::InvalidOwnerSymbol(node)
            )) if node == second
        ));
        assert!(matches!(
            plan_source_callable(&fixture.store, &host, second, owner, None),
            Err(SourceCallableError::Invariant(
                SourceCallableInvariant::InvalidOwnerSymbol(node)
            )) if node == second
        ));
        assert_eq!(publication_state(&fixture.store), before);
        drop(host);

        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        let callable = fixture
            .query_callable(first, owner, &mut diagnostics)
            .unwrap();
        let signature = fixture
            .store
            .source_callable_provenance(callable)
            .unwrap()
            .signature;
        assert!(
            fixture
                .store
                .signature(signature)
                .unwrap()
                .parameters()
                .is_empty()
        );
        assert!(valid_source_function_owner_shape(
            &fixture.store,
            owner,
            first,
        ));
        let void = fixture.store.intrinsic_bootstrap().unwrap().void_type;
        publish_inferred_source_callable_return(&mut fixture.store, &canonical, signature, void)
            .unwrap();
        assert!(matches!(
            validate_stored_source_callable(&fixture.store, callable),
            StoredSourceCallableValidation::Valid(_)
        ));

        let warm = publication_state(&fixture.store);
        assert_eq!(
            fixture.query_callable(first, owner, &mut diagnostics),
            Ok(callable)
        );
        assert_eq!(publication_state(&fixture.store), warm);
        assert!(
            fixture
                .store
                .value_symbol_links(secondary.parameters[0].symbol)
                .is_none()
        );
        assert!(diagnostics.is_empty());
    }

    #[test]
    fn typescript_duplicate_implementations_cannot_use_javascript_ownership() {
        let mut fixture = QueryFixture::new(
            "function repeated() {} function repeated(arg) {}",
            FileId::new(8_941),
        );
        let source = fixture
            .parsed
            .arena
            .get(fixture.parsed.source_file)
            .unwrap();
        let NodeData::SourceFile(source) = &source.data else {
            panic!("expected the duplicate fixture source file")
        };
        let [first, second] = source.statements.nodes.as_slice() else {
            panic!("expected exactly two duplicate implementations")
        };
        let first = NodeRef::new(fixture.parsed.arena.id(), fixture.file, *first);
        let second = NodeRef::new(fixture.parsed.arena.id(), fixture.file, *second);
        let owner = fixture.bound.symbol(first).unwrap();
        assert!(fixture.store.set_symbol_declarations(
            owner,
            Some(vec![first, second]),
            Some(first),
        ));
        let host = DeclaredTypeHost::new_after_global_merge(
            [(&fixture.parsed.arena, &fixture.bound)],
            GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
        )
        .unwrap();
        let before = publication_state(&fixture.store);

        assert!(!valid_javascript_duplicate_function_owner_shape(
            &fixture.store,
            &host,
            owner,
            first,
        ));
        assert!(matches!(
            plan_source_callable(&fixture.store, &host, first, owner, None),
            Err(SourceCallableError::Invariant(
                SourceCallableInvariant::InvalidOwnerSymbol(node)
            )) if node == first
        ));
        assert!(
            plan_javascript_duplicate_function_implementation(
                &fixture.store,
                &host,
                second,
                owner,
                None,
            )
            .is_err()
        );
        assert_eq!(publication_state(&fixture.store), before);
    }

    #[test]
    fn javascript_duplicate_implementations_reject_forged_owner_groups() {
        for (index, forged_shape) in ["reversed", "value", "repeated", "unrelated", "parent"]
            .into_iter()
            .enumerate()
        {
            let mut fixture = QueryFixture::javascript(
                "function repeated() {} function repeated(arg) {} function unrelated() {}",
                FileId::new(8_942 + u32::try_from(index).unwrap()),
            );
            let source = fixture
                .parsed
                .arena
                .get(fixture.parsed.source_file)
                .unwrap();
            let NodeData::SourceFile(source) = &source.data else {
                panic!("expected the duplicate fixture source file")
            };
            let [first, second, unrelated] = source.statements.nodes.as_slice() else {
                panic!("expected two duplicate implementations and one unrelated function")
            };
            let first = NodeRef::new(fixture.parsed.arena.id(), fixture.file, *first);
            let second = NodeRef::new(fixture.parsed.arena.id(), fixture.file, *second);
            let unrelated = NodeRef::new(fixture.parsed.arena.id(), fixture.file, *unrelated);
            let owner = fixture.bound.symbol(first).unwrap();
            match forged_shape {
                "reversed" => assert!(fixture.store.set_symbol_declarations(
                    owner,
                    Some(vec![second, first]),
                    Some(first),
                )),
                "value" => assert!(fixture.store.set_symbol_declarations(
                    owner,
                    Some(vec![first, second]),
                    Some(second),
                )),
                "repeated" => assert!(fixture.store.set_symbol_declarations(
                    owner,
                    Some(vec![first, first]),
                    Some(first),
                )),
                "unrelated" => assert!(fixture.store.set_symbol_declarations(
                    owner,
                    Some(vec![first, unrelated]),
                    Some(first),
                )),
                "parent" => {
                    let unrelated_owner = fixture.bound.symbol(unrelated).unwrap();
                    assert!(fixture.store.set_symbol_relationships(
                        owner,
                        None,
                        None,
                        Some(unrelated_owner),
                        None,
                    ));
                }
                _ => unreachable!(),
            }
            let host = DeclaredTypeHost::new_after_global_merge(
                [(&fixture.parsed.arena, &fixture.bound)],
                GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
            )
            .unwrap();
            let before = publication_state(&fixture.store);

            assert!(
                !valid_javascript_duplicate_function_owner_shape(
                    &fixture.store,
                    &host,
                    owner,
                    first,
                ),
                "{forged_shape}",
            );
            assert!(
                plan_source_callable(&fixture.store, &host, first, owner, None).is_err(),
                "{forged_shape}",
            );
            assert_eq!(publication_state(&fixture.store), before, "{forged_shape}");
        }
    }

    #[test]
    fn javascript_untyped_flags_require_one_function_or_object_arrow_parameter() {
        for (index, (source, family, flagged)) in [
            (
                "function accept(value) {}",
                SourceCallableFamily::FunctionDeclaration,
                true,
            ),
            (
                "function accept(first, second) {}",
                SourceCallableFamily::FunctionDeclaration,
                false,
            ),
            (
                "function accept() {}",
                SourceCallableFamily::FunctionDeclaration,
                false,
            ),
            (
                "const object = { arguments: value => value };",
                SourceCallableFamily::ArrowFunction,
                true,
            ),
        ]
        .into_iter()
        .enumerate()
        {
            let mut fixture = QueryFixture::javascript(
                source,
                FileId::new(1_276 + u32::try_from(index).unwrap()),
            );
            let declaration = fixture
                .parsed
                .arena
                .iter()
                .find_map(|(node, record)| {
                    (record.kind == family.syntax_kind()).then_some(NodeRef::new(
                        fixture.parsed.arena.id(),
                        fixture.file,
                        node,
                    ))
                })
                .unwrap();
            let owner = fixture.bound.symbol(declaration).unwrap();
            let host = DeclaredTypeHost::new_after_global_merge(
                [(&fixture.parsed.arena, &fixture.bound)],
                GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
            )
            .unwrap();
            let plan =
                plan_source_callable(&fixture.store, &host, declaration, owner, None).unwrap();
            let expected_flags = if flagged {
                SignatureFlags::IS_UNTYPED_SIGNATURE_IN_JS_FILE
            } else {
                SignatureFlags::NONE
            };
            assert_eq!(plan.flags, expected_flags, "{source}");
            assert_eq!(
                plan.min_argument_count,
                i32::try_from(plan.parameters.len()).unwrap(),
                "{source}"
            );
            if family == SourceCallableFamily::ArrowFunction {
                assert!(
                    source_object_property_arrow_symbol(&fixture.store, &host, declaration)
                        .unwrap()
                        .is_some()
                );
            }
            drop(host);

            let mut diagnostics = CanonicalCheckerDiagnostics::default();
            let callable = fixture
                .query_callable(declaration, owner, &mut diagnostics)
                .unwrap();
            let signature = fixture
                .store
                .source_callable_provenance(callable)
                .unwrap()
                .signature;
            assert_eq!(
                fixture.store.signature(signature).unwrap().flags(),
                expected_flags,
                "{source}"
            );
            let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
            let return_type = if family == SourceCallableFamily::ArrowFunction {
                bootstrap.any_type
            } else {
                bootstrap.void_type
            };
            publish_inferred_source_callable_return(
                &mut fixture.store,
                &plan,
                signature,
                return_type,
            )
            .unwrap();
            assert!(matches!(
                validate_stored_source_callable(&fixture.store, callable),
                StoredSourceCallableValidation::Valid(_)
            ));
            if !flagged {
                assert!(fixture.store.set_signature_flags(
                    signature,
                    SignatureFlags::IS_UNTYPED_SIGNATURE_IN_JS_FILE,
                ));
                assert_eq!(
                    validate_stored_source_callable(&fixture.store, callable),
                    StoredSourceCallableValidation::Malformed
                );
                assert!(fixture.store.set_signature_flags(signature, expected_flags));
            }
            let warm = publication_state(&fixture.store);
            assert_eq!(
                fixture.query_callable(declaration, owner, &mut diagnostics),
                Ok(callable),
                "{source}"
            );
            assert_eq!(publication_state(&fixture.store), warm);
            assert!(diagnostics.is_empty());
        }
    }

    #[test]
    fn javascript_this_parameter_is_an_ordinary_implicit_any_parameter() {
        let fixture = QueryFixture::javascript(
            "/** @this {object} */\nfunction example(this) {}",
            FileId::new(1_094),
        );
        let declaration = fixture
            .parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::FunctionDeclaration).then_some(NodeRef::new(
                    fixture.parsed.arena.id(),
                    fixture.file,
                    node,
                ))
            })
            .unwrap();
        let owner = fixture.bound.symbol(declaration).unwrap();
        let host = DeclaredTypeHost::new_after_global_merge(
            [(&fixture.parsed.arena, &fixture.bound)],
            GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
        )
        .unwrap();

        let plan = plan_source_callable(&fixture.store, &host, declaration, owner, None).unwrap();
        assert_eq!(plan.parameters.len(), 1);
        assert_eq!(plan.min_argument_count, 1);
        assert!(plan.parameters[0].is_implicit_any());
        assert_eq!(
            plan.parameters[0].base_type(&fixture.store),
            Some(fixture.store.intrinsic_bootstrap().unwrap().any_type)
        );
    }

    #[test]
    fn typescript_and_nonisolated_javascript_this_parameters_remain_unsupported() {
        for (index, (source, javascript)) in [
            ("function example(this) {}", false),
            ("function example(this, value) {}", true),
            ("function example(this: object) {}", true),
        ]
        .into_iter()
        .enumerate()
        {
            let file = FileId::new(1_095 + u32::try_from(index).unwrap());
            let fixture = if javascript {
                QueryFixture::javascript(source, file)
            } else {
                QueryFixture::new(source, file)
            };
            let declaration = fixture
                .parsed
                .arena
                .iter()
                .find_map(|(node, record)| {
                    (record.kind == SyntaxKind::FunctionDeclaration).then_some(NodeRef::new(
                        fixture.parsed.arena.id(),
                        fixture.file,
                        node,
                    ))
                })
                .unwrap();
            let owner = fixture.bound.symbol(declaration).unwrap();
            let host = DeclaredTypeHost::new_after_global_merge(
                [(&fixture.parsed.arena, &fixture.bound)],
                GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
            )
            .unwrap();

            assert!(matches!(
                plan_source_callable(&fixture.store, &host, declaration, owner, None),
                Err(SourceCallableError::Unsupported(
                    SourceCallableUnsupported::ThisParameter(_)
                ))
            ));
        }
    }

    #[test]
    fn ordinary_function_public_parameter_retains_its_implicit_any_identity() {
        let fixture = QueryFixture::new("function example(public value) {}", FileId::new(1_098));
        let declaration = fixture
            .parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::FunctionDeclaration).then_some(NodeRef::new(
                    fixture.parsed.arena.id(),
                    fixture.file,
                    node,
                ))
            })
            .unwrap();
        let owner = fixture.bound.symbol(declaration).unwrap();
        let host = DeclaredTypeHost::new_after_global_merge(
            [(&fixture.parsed.arena, &fixture.bound)],
            GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
        )
        .unwrap();

        let plan = plan_source_callable(&fixture.store, &host, declaration, owner, None).unwrap();
        assert_eq!(plan.parameters.len(), 1);
        assert_eq!(plan.min_argument_count, 1);
        assert!(plan.parameters[0].is_implicit_any());
        assert_eq!(
            plan.parameters[0].base_type(&fixture.store),
            Some(fixture.store.intrinsic_bootstrap().unwrap().any_type)
        );
    }

    #[test]
    fn other_function_parameter_modifiers_remain_unsupported() {
        for (index, source) in [
            "function example(private value) {}",
            "function example(protected value) {}",
            "function example(readonly value) {}",
            "function example(public value: string) {}",
            "function example(public value, other) {}",
        ]
        .into_iter()
        .enumerate()
        {
            let fixture =
                QueryFixture::new(source, FileId::new(1_099 + u32::try_from(index).unwrap()));
            let declaration = fixture
                .parsed
                .arena
                .iter()
                .find_map(|(node, record)| {
                    (record.kind == SyntaxKind::FunctionDeclaration).then_some(NodeRef::new(
                        fixture.parsed.arena.id(),
                        fixture.file,
                        node,
                    ))
                })
                .unwrap();
            let owner = fixture.bound.symbol(declaration).unwrap();
            let host = DeclaredTypeHost::new_after_global_merge(
                [(&fixture.parsed.arena, &fixture.bound)],
                GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
            )
            .unwrap();

            assert!(
                matches!(
                    plan_source_callable(&fixture.store, &host, declaration, owner, None),
                    Err(SourceCallableError::Unsupported(
                        SourceCallableUnsupported::ParameterModifiers(_)
                    ))
                ),
                "{source}"
            );
        }
    }

    #[test]
    fn merged_arrow_parameter_and_local_var_are_typed_unsupported() {
        let fixture = QueryFixture::new(
            "const collision = (_i: number, ...rest: number[]): void => { var _i = 10; };",
            FileId::new(1_078),
        );
        let arrow = fixture
            .parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::ArrowFunction).then_some(NodeRef::new(
                    fixture.parsed.arena.id(),
                    fixture.file,
                    node,
                ))
            })
            .unwrap();
        let owner = fixture.bound.symbol(arrow).unwrap();
        let host = DeclaredTypeHost::new_after_global_merge(
            [(&fixture.parsed.arena, &fixture.bound)],
            GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
        )
        .unwrap();
        let before = publication_state(&fixture.store);

        assert!(matches!(
            plan_source_callable(&fixture.store, &host, arrow, owner, None),
            Err(SourceCallableError::Unsupported(
                SourceCallableUnsupported::OverloadDeclaration(_)
            ))
        ));
        assert_eq!(publication_state(&fixture.store), before);
    }

    #[test]
    fn declaration_file_signatures_accept_implicit_and_explicit_ambient_modifiers() {
        for (index, (source, declaration_file, module_state, exported)) in [
            (
                "function plain(value: number): string;",
                true,
                CanonicalModuleState::Script,
                false,
            ),
            (
                "declare function declared(value: number): string;",
                true,
                CanonicalModuleState::Script,
                false,
            ),
            (
                "export function exported(value: number): string;",
                true,
                CanonicalModuleState::External,
                true,
            ),
            (
                "export declare function explicit(value: number): string;",
                true,
                CanonicalModuleState::External,
                true,
            ),
            (
                "export declare function ordinary(value: number): string;",
                false,
                CanonicalModuleState::External,
                true,
            ),
        ]
        .into_iter()
        .enumerate()
        {
            let mut fixture = QueryFixture::with_source_facts(
                source,
                FileId::new(1_060 + u32::try_from(index).unwrap()),
                declaration_file,
                module_state,
            );
            let declaration = fixture
                .parsed
                .arena
                .iter()
                .find_map(|(node, record)| {
                    (record.kind == SyntaxKind::FunctionDeclaration).then_some(NodeRef::new(
                        fixture.parsed.arena.id(),
                        fixture.file,
                        node,
                    ))
                })
                .unwrap();
            let owner = fixture.bound.symbol(declaration).unwrap();
            let host = DeclaredTypeHost::new_after_global_merge(
                [(&fixture.parsed.arena, &fixture.bound)],
                GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
            )
            .unwrap();
            let plan = plan_source_callable(&fixture.store, &host, declaration, owner, None)
                .unwrap_or_else(|error| panic!("{source}: {error:?}"));
            assert_eq!(plan.body_mode, SourceCallableBodyMode::AmbientDeclaration);
            assert_eq!(plan.body, declaration);
            assert_eq!(plan.owner_parent.is_some(), exported);
            assert_eq!(plan.export_local.is_some(), exported);
            drop(host);

            let mut diagnostics = CanonicalCheckerDiagnostics::default();
            let callable = fixture
                .query_callable(declaration, owner, &mut diagnostics)
                .unwrap_or_else(|error| panic!("{source}: {error:?}"));
            let signature = fixture
                .store
                .source_callable_provenance(callable)
                .unwrap()
                .signature;
            let expected_return = fixture.store.intrinsic_bootstrap().unwrap().string_type;
            assert_eq!(
                fixture.query_return(signature, &mut diagnostics),
                Ok(expected_return)
            );
            assert!(diagnostics.is_empty(), "{source}: {diagnostics:?}");
        }
    }

    #[test]
    fn declaration_file_namespace_exports_publish_ambient_callables_cold_and_warm() {
        let mut fixture = QueryFixture::with_source_facts(
            "declare module Foo { export function bar(): void; }",
            FileId::new(1_185),
            true,
            CanonicalModuleState::Script,
        );
        let declaration = fixture
            .parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::FunctionDeclaration).then_some(NodeRef::new(
                    fixture.parsed.arena.id(),
                    fixture.file,
                    node,
                ))
            })
            .unwrap();
        let namespace = fixture
            .parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::ModuleDeclaration).then_some(NodeRef::new(
                    fixture.parsed.arena.id(),
                    fixture.file,
                    node,
                ))
            })
            .and_then(|node| fixture.bound.symbol(node))
            .unwrap();
        let owner = fixture.bound.symbol(declaration).unwrap();
        let export_local = fixture.bound.local_symbol(declaration).unwrap();
        let host = DeclaredTypeHost::new_after_global_merge(
            [(&fixture.parsed.arena, &fixture.bound)],
            GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
        )
        .unwrap();
        let plan = plan_source_callable(&fixture.store, &host, declaration, owner, None).unwrap();
        assert_eq!(plan.body_mode, SourceCallableBodyMode::AmbientDeclaration);
        assert_eq!(plan.owner_parent, Some(namespace));
        assert_eq!(plan.export_local, Some(export_local));
        drop(host);

        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        let callable = fixture
            .query_callable(declaration, owner, &mut diagnostics)
            .unwrap();
        let signature = fixture
            .store
            .source_callable_provenance(callable)
            .unwrap()
            .signature;
        let expected = fixture.store.intrinsic_bootstrap().unwrap().void_type;
        assert_eq!(
            fixture.query_return(signature, &mut diagnostics),
            Ok(expected)
        );
        assert!(matches!(
            validate_stored_source_callable(&fixture.store, callable),
            StoredSourceCallableValidation::Valid(_)
        ));

        let warm = publication_state(&fixture.store);
        assert_eq!(
            fixture.query_callable(declaration, owner, &mut diagnostics),
            Ok(callable),
        );
        assert_eq!(publication_state(&fixture.store), warm);
        assert!(diagnostics.is_empty());
    }

    #[test]
    fn typescript_namespace_exports_publish_ordinary_callables_cold_and_warm() {
        let mut fixture = QueryFixture::with_source_facts(
            "export namespace Example { export function run() {} }",
            FileId::new(1_125),
            false,
            CanonicalModuleState::External,
        );
        let declaration = fixture
            .parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::FunctionDeclaration).then_some(NodeRef::new(
                    fixture.parsed.arena.id(),
                    fixture.file,
                    node,
                ))
            })
            .unwrap();
        let namespace = fixture
            .parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::ModuleDeclaration).then_some(NodeRef::new(
                    fixture.parsed.arena.id(),
                    fixture.file,
                    node,
                ))
            })
            .and_then(|node| fixture.bound.symbol(node))
            .unwrap();
        let owner = fixture.bound.symbol(declaration).unwrap();
        let export_local = fixture.bound.local_symbol(declaration).unwrap();
        let host = DeclaredTypeHost::new_after_global_merge(
            [(&fixture.parsed.arena, &fixture.bound)],
            GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
        )
        .unwrap();
        let plan = plan_source_callable(&fixture.store, &host, declaration, owner, None).unwrap();
        assert_eq!(plan.body_mode, SourceCallableBodyMode::Present);
        assert_eq!(plan.owner_parent, Some(namespace));
        assert_eq!(plan.export_local, Some(export_local));
        drop(host);

        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        let callable = fixture
            .query_callable(declaration, owner, &mut diagnostics)
            .unwrap();
        let signature = fixture
            .store
            .source_callable_provenance(callable)
            .unwrap()
            .signature;
        let void = fixture.store.intrinsic_bootstrap().unwrap().void_type;
        publish_inferred_source_callable_return(&mut fixture.store, &plan, signature, void)
            .unwrap();
        let warm = publication_state(&fixture.store);
        assert_eq!(
            fixture.query_callable(declaration, owner, &mut diagnostics),
            Ok(callable)
        );
        assert_eq!(publication_state(&fixture.store), warm);
        assert!(matches!(
            validate_stored_source_callable(&fixture.store, callable),
            StoredSourceCallableValidation::Valid(_)
        ));
        assert!(diagnostics.is_empty());
    }

    #[test]
    fn importer_warmed_namespace_functions_retain_their_array_targets_during_syntax_planning() {
        let mut fixture = QueryFixture::with_source_facts(
            "export namespace Example { export function run() {} }",
            FileId::new(1_126),
            false,
            CanonicalModuleState::External,
        );
        let declaration = fixture
            .parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::FunctionDeclaration).then_some(NodeRef::new(
                    fixture.parsed.arena.id(),
                    fixture.file,
                    node,
                ))
            })
            .unwrap();
        let owner = fixture.bound.symbol(declaration).unwrap();
        let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
        let targets = CanonicalArrayTargets::for_test(bootstrap.any_type, bootstrap.unknown_type);
        let void = bootstrap.void_type;
        let host = DeclaredTypeHost::new_after_global_merge(
            [(&fixture.parsed.arena, &fixture.bound)],
            GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
        )
        .unwrap();
        let imported =
            plan_source_callable(&fixture.store, &host, declaration, owner, Some(targets)).unwrap();
        drop(host);

        reserve_source_callable_capacities(&mut fixture.store, &[&imported]).unwrap();
        let pending = begin_source_callable(&mut fixture.store, &imported, &[])
            .unwrap()
            .unwrap();
        finalize_source_callable_structure(&mut fixture.store, &imported, pending).unwrap();
        publish_inferred_source_callable_return(
            &mut fixture.store,
            &imported,
            pending.signature,
            void,
        )
        .unwrap();
        let warm = publication_state(&fixture.store);

        let host = DeclaredTypeHost::new_after_global_merge(
            [(&fixture.parsed.arena, &fixture.bound)],
            GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
        )
        .unwrap();
        let replay = plan_source_callable(&fixture.store, &host, declaration, owner, None).unwrap();
        assert_eq!(replay.array_targets, Some(targets));
        assert!(matches!(
            source_callable_state(&fixture.store, &replay, false),
            Ok(SourceCallableState::Resolved { type_, signature })
                if type_ == pending.type_ && signature == pending.signature
        ));
        assert_eq!(publication_state(&fixture.store), warm);
    }

    #[test]
    fn typed_ambient_rest_parameters_preserve_exact_arity_and_signature_flags() {
        for (index, (source, declaration_file, expected_minimum)) in [
            (
                "declare function take(head: string, ...values: number[]): string;",
                false,
                1,
            ),
            ("declare function take(...values: any[]): any;", false, 0),
            ("function take(...values: string[]): void;", true, 0),
        ]
        .into_iter()
        .enumerate()
        {
            let fixture = QueryFixture::with_source_facts(
                source,
                FileId::new(1_160 + u32::try_from(index).unwrap()),
                declaration_file,
                CanonicalModuleState::Script,
            );
            let declaration = fixture
                .parsed
                .arena
                .iter()
                .find_map(|(node, record)| {
                    (record.kind == SyntaxKind::FunctionDeclaration).then_some(NodeRef::new(
                        fixture.parsed.arena.id(),
                        fixture.file,
                        node,
                    ))
                })
                .unwrap();
            let owner = fixture.bound.symbol(declaration).unwrap();
            let host = DeclaredTypeHost::new_after_global_merge(
                [(&fixture.parsed.arena, &fixture.bound)],
                GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
            )
            .unwrap();
            let before = publication_state(&fixture.store);

            let plan = plan_source_callable(&fixture.store, &host, declaration, owner, None)
                .unwrap_or_else(|error| panic!("{source}: {error:?}"));
            assert_eq!(plan.body_mode, SourceCallableBodyMode::AmbientDeclaration);
            assert_eq!(plan.flags, SignatureFlags::HAS_REST_PARAMETER);
            assert_eq!(plan.min_argument_count, expected_minimum);
            assert!(plan.parameters.last().unwrap().rest);
            assert_eq!(publication_state(&fixture.store), before);
        }
    }

    #[test]
    fn generic_and_overloaded_ambient_rest_parameters_remain_typed_boundaries() {
        let generic = QueryFixture::new(
            "declare function generic<T>(...values: T[]): T;",
            FileId::new(1_163),
        );
        let (generic_declaration, _, _, _) = generic.generic_parts();
        let generic_owner = generic.bound.symbol(generic_declaration).unwrap();
        let generic_host = DeclaredTypeHost::new_after_global_merge(
            [(&generic.parsed.arena, &generic.bound)],
            GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
        )
        .unwrap();
        assert!(matches!(
            plan_source_callable(
                &generic.store,
                &generic_host,
                generic_declaration,
                generic_owner,
                None,
            ),
            Err(SourceCallableError::Unsupported(
                SourceCallableUnsupported::GenericSignature(_)
            ))
        ));

        let overload = QueryFixture::new(
            "declare function overloaded(...values: number[]): number; \
             declare function overloaded(value: string): string;",
            FileId::new(1_164),
        );
        let declaration = overload
            .parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::FunctionDeclaration).then_some(NodeRef::new(
                    overload.parsed.arena.id(),
                    overload.file,
                    node,
                ))
            })
            .unwrap();
        let owner = overload.bound.symbol(declaration).unwrap();
        let declarations = overload
            .store
            .symbol(owner)
            .unwrap()
            .declarations()
            .unwrap();
        let host = DeclaredTypeHost::new_after_global_merge(
            [(&overload.parsed.arena, &overload.bound)],
            GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
        )
        .unwrap();
        assert!(matches!(
            plan_source_ambient_overload_declaration(
                &overload.store,
                &host,
                declaration,
                owner,
                declarations,
                None,
            ),
            Err(SourceCallableError::Unsupported(
                SourceCallableUnsupported::AmbientRestParameter(_)
            ))
        ));
    }

    #[test]
    fn type_only_namespace_merges_preserve_callable_identity_cold_and_warm() {
        for (index, (source, declaration_file, module_state, has_exports)) in [
            (
                "declare function callable(): void; \
                 declare namespace callable { export interface Box { value: string; } }",
                false,
                CanonicalModuleState::Script,
                true,
            ),
            (
                "declare function callable(): void; \
                 declare namespace callable { export interface Box { value: string; } }",
                true,
                CanonicalModuleState::Script,
                true,
            ),
            (
                "declare function callable(): void; declare namespace callable {}",
                false,
                CanonicalModuleState::Script,
                false,
            ),
            (
                "declare function callable(): void; \
                 declare namespace callable {} export = callable;",
                true,
                CanonicalModuleState::External,
                false,
            ),
        ]
        .into_iter()
        .enumerate()
        {
            let mut fixture = QueryFixture::with_source_facts(
                source,
                FileId::new(1_180 + u32::try_from(index).unwrap()),
                declaration_file,
                module_state,
            );
            let declaration = fixture
                .parsed
                .arena
                .iter()
                .find_map(|(node, record)| {
                    (record.kind == SyntaxKind::FunctionDeclaration).then_some(NodeRef::new(
                        fixture.parsed.arena.id(),
                        fixture.file,
                        node,
                    ))
                })
                .unwrap();
            let owner = fixture.bound.symbol(declaration).unwrap();
            assert_eq!(
                fixture.store.symbol(owner).unwrap().flags(),
                SymbolFlags::FUNCTION | SymbolFlags::NAMESPACE_MODULE
            );
            assert_eq!(
                fixture.store.symbol(owner).unwrap().exports().is_some(),
                has_exports
            );
            assert!(valid_source_function_owner_shape(
                &fixture.store,
                owner,
                declaration
            ));

            let mut diagnostics = CanonicalCheckerDiagnostics::default();
            let callable = fixture
                .query_callable(declaration, owner, &mut diagnostics)
                .unwrap();
            assert!(matches!(
                validate_stored_source_callable(&fixture.store, callable),
                StoredSourceCallableValidation::Valid(_)
            ));
            let warm = publication_state(&fixture.store);
            assert_eq!(
                fixture.query_callable(declaration, owner, &mut diagnostics),
                Ok(callable)
            );
            assert_eq!(publication_state(&fixture.store), warm);
            assert!(diagnostics.is_empty());
        }
    }

    #[test]
    fn value_namespace_merges_preserve_callable_identity_cold_and_warm() {
        for (index, (source, declaration_file, module_state)) in [
            (
                "declare function callable(): void; \
                 declare namespace callable { export const value: string; }",
                false,
                CanonicalModuleState::Script,
            ),
            (
                "declare function callable(): void; \
                 declare namespace callable { export const value: string; } \
                 export = callable;",
                true,
                CanonicalModuleState::External,
            ),
        ]
        .into_iter()
        .enumerate()
        {
            let mut fixture = QueryFixture::with_source_facts(
                source,
                FileId::new(1_182 + u32::try_from(index).unwrap()),
                declaration_file,
                module_state,
            );
            let declaration = fixture
                .parsed
                .arena
                .iter()
                .find_map(|(node, record)| {
                    (record.kind == SyntaxKind::FunctionDeclaration).then_some(NodeRef::new(
                        fixture.parsed.arena.id(),
                        fixture.file,
                        node,
                    ))
                })
                .unwrap();
            let owner = fixture.bound.symbol(declaration).unwrap();
            assert_eq!(
                fixture.store.symbol(owner).unwrap().flags(),
                SymbolFlags::FUNCTION | SymbolFlags::VALUE_MODULE
            );
            assert!(valid_source_function_owner_shape(
                &fixture.store,
                owner,
                declaration
            ));
            let host = DeclaredTypeHost::new_after_global_merge(
                [(&fixture.parsed.arena, &fixture.bound)],
                GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
            )
            .unwrap();
            let before = publication_state(&fixture.store);

            assert!(plan_source_callable(&fixture.store, &host, declaration, owner, None).is_ok());
            assert_eq!(publication_state(&fixture.store), before);
            drop(host);

            let mut diagnostics = CanonicalCheckerDiagnostics::default();
            let callable = fixture
                .query_callable(declaration, owner, &mut diagnostics)
                .unwrap();
            assert!(matches!(
                validate_stored_source_callable(&fixture.store, callable),
                StoredSourceCallableValidation::Valid(_)
            ));
            let warm = publication_state(&fixture.store);
            assert_eq!(
                fixture.query_callable(declaration, owner, &mut diagnostics),
                Ok(callable)
            );
            assert_eq!(publication_state(&fixture.store), warm);
            assert!(diagnostics.is_empty());
        }
    }

    #[test]
    fn value_namespace_merges_reject_exports_without_namespace_ownership() {
        let mut fixture = QueryFixture::with_source_facts(
            "declare function callable(): void; \
             declare namespace callable { export const value: string; } \
             export = callable;",
            FileId::new(1_184),
            true,
            CanonicalModuleState::External,
        );
        let declaration = fixture
            .parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::FunctionDeclaration).then_some(NodeRef::new(
                    fixture.parsed.arena.id(),
                    fixture.file,
                    node,
                ))
            })
            .unwrap();
        let owner = fixture.bound.symbol(declaration).unwrap();
        let member = fixture
            .store
            .symbol(owner)
            .and_then(ts_binder::semantic::Symbol::exports)
            .and_then(|exports| fixture.store.symbol_table(exports))
            .and_then(|exports| exports.get_source("value"))
            .unwrap();
        let record = fixture.store.symbol(member).unwrap();
        let (members, exports, export_symbol) =
            (record.members(), record.exports(), record.export_symbol());
        assert!(fixture.store.set_symbol_relationships(
            member,
            members,
            exports,
            None,
            export_symbol,
        ));
        let host = DeclaredTypeHost::new_after_global_merge(
            [(&fixture.parsed.arena, &fixture.bound)],
            GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
        )
        .unwrap();
        let before = publication_state(&fixture.store);

        assert!(!valid_source_function_owner_shape(
            &fixture.store,
            owner,
            declaration,
        ));
        assert!(matches!(
            plan_source_callable(&fixture.store, &host, declaration, owner, None),
            Err(SourceCallableError::Unsupported(
                SourceCallableUnsupported::ExpandoProperties(_)
            ))
        ));
        assert_eq!(publication_state(&fixture.store), before);
    }

    #[test]
    fn exported_declaration_file_generic_signatures_keep_exact_owner_provenance() {
        let mut fixture = QueryFixture::with_source_facts(
            "export declare function identity<T>(value: T): T;",
            FileId::new(1_065),
            true,
            CanonicalModuleState::External,
        );
        let (declaration, _, _, _) = fixture.generic_parts();
        let owner = fixture.bound.symbol(declaration).unwrap();
        let mut diagnostics = CanonicalCheckerDiagnostics::default();

        let callable = fixture
            .query_callable(declaration, owner, &mut diagnostics)
            .unwrap();
        let provenance = fixture.store.source_callable_provenance(callable).unwrap();
        assert!(provenance.owner_parent.is_some());
        assert!(provenance.export_local.is_some());
        let signature = fixture.store.signature(provenance.signature).unwrap();
        assert_eq!(signature.type_parameters().len(), 1);
        assert_eq!(signature.parameters().len(), 1);
        assert!(diagnostics.is_empty());
    }

    #[test]
    fn declaration_file_functions_without_return_annotations_publish_canonical_any() {
        for (index, (source, declaration_file, module_state, exported)) in [
            (
                "function plain();",
                true,
                CanonicalModuleState::Script,
                false,
            ),
            (
                "declare function declared(value: number);",
                true,
                CanonicalModuleState::Script,
                false,
            ),
            (
                "export function exported();",
                true,
                CanonicalModuleState::External,
                true,
            ),
            (
                "export declare function explicit(value: number);",
                true,
                CanonicalModuleState::External,
                true,
            ),
            (
                "declare function ordinary(value: number);",
                false,
                CanonicalModuleState::Script,
                false,
            ),
            (
                "export declare function ordinaryExport(value: number);",
                false,
                CanonicalModuleState::External,
                true,
            ),
        ]
        .into_iter()
        .enumerate()
        {
            let mut fixture = QueryFixture::with_source_facts(
                source,
                FileId::new(1_070 + u32::try_from(index).unwrap()),
                declaration_file,
                module_state,
            );
            let declaration = fixture
                .parsed
                .arena
                .iter()
                .find_map(|(node, record)| {
                    (record.kind == SyntaxKind::FunctionDeclaration).then_some(NodeRef::new(
                        fixture.parsed.arena.id(),
                        fixture.file,
                        node,
                    ))
                })
                .unwrap();
            let owner = fixture.bound.symbol(declaration).unwrap();
            let host = DeclaredTypeHost::new_after_global_merge(
                [(&fixture.parsed.arena, &fixture.bound)],
                GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
            )
            .unwrap();
            let plan = plan_source_callable(&fixture.store, &host, declaration, owner, None)
                .unwrap_or_else(|error| panic!("{source}: {error:?}"));
            assert_eq!(plan.body_mode, SourceCallableBodyMode::AmbientDeclaration);
            assert_eq!(
                plan.return_type,
                SourceCallableReturnPlan::AmbientImplicitAny
            );
            assert!(plan.return_type.is_ambient_implicit_any());
            assert!(!plan.return_type.is_inferred());
            assert_eq!(plan.return_type.type_node(), None);
            assert_eq!(plan.owner_parent.is_some(), exported);
            drop(host);

            let any = fixture.store.intrinsic_bootstrap().unwrap().any_type;
            let mut diagnostics = CanonicalCheckerDiagnostics::default();
            let callable = fixture
                .query_callable(declaration, owner, &mut diagnostics)
                .unwrap_or_else(|error| panic!("{source}: {error:?}"));
            let signature = fixture
                .store
                .source_callable_provenance(callable)
                .unwrap()
                .signature;
            assert_eq!(
                fixture
                    .store
                    .signature(signature)
                    .unwrap()
                    .resolved_return_type(),
                Some(any)
            );
            assert!(
                fixture
                    .store
                    .function_signature_return_annotation(signature)
                    .is_none()
            );
            assert!(matches!(
                validate_stored_source_callable(&fixture.store, callable),
                StoredSourceCallableValidation::Valid(_)
            ));
            assert_eq!(fixture.query_return(signature, &mut diagnostics), Ok(any));

            let warm = publication_state(&fixture.store);
            assert_eq!(
                fixture.query_callable(declaration, owner, &mut diagnostics),
                Ok(callable)
            );
            assert_eq!(publication_state(&fixture.store), warm);
            assert!(diagnostics.is_empty(), "{source}: {diagnostics:?}");
        }
    }

    #[test]
    fn ambient_implicit_return_rejects_non_any_cache_values() {
        let mut fixture = QueryFixture::with_source_facts(
            "export function implicit();",
            FileId::new(1_074),
            true,
            CanonicalModuleState::External,
        );
        let declaration = fixture
            .parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::FunctionDeclaration).then_some(NodeRef::new(
                    fixture.parsed.arena.id(),
                    fixture.file,
                    node,
                ))
            })
            .unwrap();
        let owner = fixture.bound.symbol(declaration).unwrap();
        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        let callable = fixture
            .query_callable(declaration, owner, &mut diagnostics)
            .unwrap();
        let signature = fixture
            .store
            .source_callable_provenance(callable)
            .unwrap()
            .signature;
        let string = fixture.store.intrinsic_bootstrap().unwrap().string_type;
        assert!(
            fixture
                .store
                .set_signature_resolved_return_type(signature, Some(string))
        );
        let host = DeclaredTypeHost::new_after_global_merge(
            [(&fixture.parsed.arena, &fixture.bound)],
            GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
        )
        .unwrap();

        assert!(matches!(
            plan_source_callable(&fixture.store, &host, declaration, owner, None),
            Err(SourceCallableError::Invariant(
                SourceCallableInvariant::InvalidSignatureCache(_)
            ))
        ));
        assert!(diagnostics.is_empty());
    }

    #[test]
    fn generic_ambient_missing_returns_remain_typed_boundaries() {
        for (index, (source, declaration_file, module_state)) in [
            (
                "declare function missing<T>(value: T);",
                false,
                CanonicalModuleState::Script,
            ),
            (
                "export declare function generic<T>(value: T);",
                true,
                CanonicalModuleState::External,
            ),
        ]
        .into_iter()
        .enumerate()
        {
            let fixture = QueryFixture::with_source_facts(
                source,
                FileId::new(1_075 + u32::try_from(index).unwrap()),
                declaration_file,
                module_state,
            );
            let declaration = fixture
                .parsed
                .arena
                .iter()
                .find_map(|(node, record)| {
                    (record.kind == SyntaxKind::FunctionDeclaration).then_some(NodeRef::new(
                        fixture.parsed.arena.id(),
                        fixture.file,
                        node,
                    ))
                })
                .unwrap();
            let owner = fixture.bound.symbol(declaration).unwrap();
            let host = DeclaredTypeHost::new_after_global_merge(
                [(&fixture.parsed.arena, &fixture.bound)],
                GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
            )
            .unwrap();

            assert!(matches!(
                plan_source_callable(&fixture.store, &host, declaration, owner, None),
                Err(SourceCallableError::Unsupported(
                    SourceCallableUnsupported::OverloadDeclaration(_)
                ))
            ));
        }
    }

    #[test]
    fn implicit_any_parameters_mix_with_annotated_and_optional_parameters() {
        let fixture = QueryFixture::new(
            "function mixed(first: string, second, third?) {}",
            FileId::new(1_048),
        );
        let declaration = fixture
            .parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::FunctionDeclaration).then_some(NodeRef::new(
                    fixture.parsed.arena.id(),
                    fixture.file,
                    node,
                ))
            })
            .unwrap();
        let owner = fixture.bound.symbol(declaration).unwrap();
        let host = DeclaredTypeHost::new_after_global_merge(
            [(&fixture.parsed.arena, &fixture.bound)],
            GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
        )
        .unwrap();

        let plan = plan_source_callable(&fixture.store, &host, declaration, owner, None).unwrap();
        assert_eq!(plan.min_argument_count, 2);
        assert!(!plan.parameters[0].is_implicit_any());
        assert_eq!(
            plan.parameters[0].explicit_type_node(),
            Some(plan.parameters[0].type_node)
        );
        assert!(plan.parameters[1].is_implicit_any());
        assert!(plan.parameters[2].is_implicit_any());
        assert!(plan.parameters[2].optional);
    }

    #[test]
    fn unannotated_rest_parameters_preserve_array_identity_and_replay_warm() {
        for (index, (source, expected_minimum, ambient)) in [
            ("function rest(...values) {}", 0, false),
            ("function rest(first, ...values) {}", 1, false),
            ("declare function rest(...values): any;", 0, true),
            ("const rest = (...values) => {};", 0, false),
            ("const rest = (first, ...values) => {};", 1, false),
            ("const rest = (first: string, ...values) => {};", 1, false),
        ]
        .into_iter()
        .enumerate()
        {
            let mut fixture =
                QueryFixture::new(source, FileId::new(1_330 + u32::try_from(index).unwrap()));
            let declaration = fixture
                .parsed
                .arena
                .iter()
                .find_map(|(node, record)| {
                    matches!(
                        record.kind,
                        SyntaxKind::FunctionDeclaration | SyntaxKind::ArrowFunction
                    )
                    .then_some(NodeRef::new(
                        fixture.parsed.arena.id(),
                        fixture.file,
                        node,
                    ))
                })
                .unwrap();
            let owner = fixture.bound.symbol(declaration).unwrap();
            let plan = {
                let host = DeclaredTypeHost::new_after_global_merge(
                    [(&fixture.parsed.arena, &fixture.bound)],
                    GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
                )
                .unwrap();
                plan_source_callable(&fixture.store, &host, declaration, owner, None)
                    .unwrap_or_else(|error| panic!("{source}: {error:?}"))
            };
            let rest = plan.parameters.last().unwrap();
            let any_array = fixture
                .store
                .intrinsic_bootstrap()
                .unwrap()
                .empty_object_type;
            assert_eq!(plan.flags, SignatureFlags::HAS_REST_PARAMETER, "{source}");
            assert_eq!(plan.min_argument_count, expected_minimum, "{source}");
            assert_eq!(plan.body_mode.is_ambient(), ambient, "{source}");
            assert!(rest.rest && rest.is_implicit_any(), "{source}");
            assert_eq!(rest.explicit_type_node(), None, "{source}");
            assert_eq!(rest.base_type(&fixture.store), Some(any_array), "{source}");

            let mut diagnostics = CanonicalCheckerDiagnostics::default();
            let callable = fixture
                .query_callable(declaration, owner, &mut diagnostics)
                .unwrap_or_else(|error| panic!("{source}: {error:?}"));
            let signature = fixture
                .store
                .source_callable_provenance(callable)
                .unwrap()
                .signature;
            assert_eq!(
                fixture
                    .store
                    .callable_signature_parameter_types(signature)
                    .and_then(|types| types.last().copied()),
                Some(any_array),
                "{source}"
            );
            assert_eq!(
                fixture
                    .store
                    .value_symbol_links(rest.symbol)
                    .and_then(|links| links.resolved_type),
                Some(any_array),
                "{source}"
            );
            if plan.return_type.is_inferred() {
                let void = fixture.store.intrinsic_bootstrap().unwrap().void_type;
                publish_inferred_source_callable_return(&mut fixture.store, &plan, signature, void)
                    .unwrap();
            }
            assert!(matches!(
                validate_stored_source_callable(&fixture.store, callable),
                StoredSourceCallableValidation::Valid(_)
            ));
            let warm = publication_state(&fixture.store);
            assert_eq!(
                fixture.query_callable(declaration, owner, &mut diagnostics),
                Ok(callable),
                "{source}"
            );
            assert_eq!(publication_state(&fixture.store), warm, "{source}");
            assert!(diagnostics.is_empty(), "{source}: {diagnostics:?}");
        }
    }

    #[test]
    fn unannotated_rest_parameters_reuse_the_authoritative_global_array() {
        let parsed = parse_source_file(
            "interface Array<T> {} interface ReadonlyArray<T> {} \
             function rest(first: string, ...values) {}",
        );
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(1_336);
        let mut context = bind_context(&parsed, file);
        let global_types = context.global_types().clone();
        let bound = context.file(file).unwrap().1.clone();
        let declaration = parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::FunctionDeclaration).then_some(NodeRef::new(
                    parsed.arena.id(),
                    file,
                    node,
                ))
            })
            .unwrap();
        let owner = bound.symbol(declaration).unwrap();
        let host = DeclaredTypeHost::new_after_global_merge(
            [(&parsed.arena, &bound)],
            GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
        )
        .unwrap();
        let cold = publication_state(context.store());
        assert!(matches!(
            plan_source_callable(context.store(), &host, declaration, owner, None),
            Err(SourceCallableError::Unsupported(
                SourceCallableUnsupported::MissingParameterType(_)
            ))
        ));
        assert_eq!(publication_state(context.store()), cold);
        let plan = plan_source_callable(
            context.store(),
            &host,
            declaration,
            owner,
            Some(CanonicalArrayTargets::from_global_types(&global_types)),
        )
        .unwrap();
        let rest = plan.parameters.last().unwrap();
        assert_eq!(
            rest.base_type(context.store()),
            Some(global_types.any_array_type)
        );

        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        let callable = CanonicalTypeQuery::new_with_global_types(
            context.store_mut_for_test(),
            &host,
            &global_types,
            CanonicalTypeQueryOptions::default(),
            &mut diagnostics,
        )
        .unwrap()
        .get_type_of_source_callable(declaration, owner)
        .unwrap();
        let signature = context
            .store()
            .source_callable_provenance(callable)
            .unwrap()
            .signature;
        assert_eq!(
            context
                .store()
                .callable_signature_parameter_types(signature)
                .and_then(|types| types.last().copied()),
            Some(global_types.any_array_type)
        );
        assert_eq!(
            context
                .store()
                .value_symbol_links(rest.symbol)
                .and_then(|links| links.resolved_type),
            Some(global_types.any_array_type)
        );
        let void = context.store().intrinsic_bootstrap().unwrap().void_type;
        publish_inferred_source_callable_return(
            context.store_mut_for_test(),
            &plan,
            signature,
            void,
        )
        .unwrap();
        let warm = publication_state(context.store());
        let replay = CanonicalTypeQuery::new_with_global_types(
            context.store_mut_for_test(),
            &host,
            &global_types,
            CanonicalTypeQueryOptions::default(),
            &mut diagnostics,
        )
        .unwrap()
        .get_type_of_source_callable(declaration, owner)
        .unwrap();
        assert_eq!(replay, callable);
        assert_eq!(publication_state(context.store()), warm);
        assert!(diagnostics.is_empty());
    }

    #[test]
    fn unannotated_generic_ambient_and_initialized_parameters_remain_boundaries() {
        for (index, source) in [
            "function generic<T>(value): T { return value; }",
            "declare function ambient(value): void;",
            "function initialized(value = 1) {}",
        ]
        .into_iter()
        .enumerate()
        {
            let fixture =
                QueryFixture::new(source, FileId::new(1_049 + u32::try_from(index).unwrap()));
            let declaration = fixture
                .parsed
                .arena
                .iter()
                .find_map(|(node, record)| {
                    (record.kind == SyntaxKind::FunctionDeclaration).then_some(NodeRef::new(
                        fixture.parsed.arena.id(),
                        fixture.file,
                        node,
                    ))
                })
                .unwrap();
            let owner = fixture.bound.symbol(declaration).unwrap();
            let host = DeclaredTypeHost::new_after_global_merge(
                [(&fixture.parsed.arena, &fixture.bound)],
                GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
            )
            .unwrap();
            assert!(matches!(
                plan_source_callable(&fixture.store, &host, declaration, owner, None),
                Err(SourceCallableError::Unsupported(
                    SourceCallableUnsupported::MissingParameterType(_)
                ))
            ));
        }
    }

    #[test]
    fn recursive_generic_array_parameter_syntax_requires_an_array_capability() {
        let annotations = [
            "T[]".to_owned(),
            "Array<T>".to_owned(),
            "T[][]".to_owned(),
            "Array<Array<T>>".to_owned(),
            "Array<T[]>[]".to_owned(),
            format!("T{}", "[]".repeat(101)),
        ];
        for (index, annotation) in annotations.into_iter().enumerate() {
            let fixture = QueryFixture::new(
                &format!("function first<T>(values: {annotation}): T {{ return values[0]; }}"),
                FileId::new(990 + u32::try_from(index).unwrap()),
            );
            let (declaration, _, _, _) = fixture.generic_parts();
            let owner = fixture.bound.symbol(declaration).unwrap();
            let host = DeclaredTypeHost::new_after_global_merge(
                [(&fixture.parsed.arena, &fixture.bound)],
                GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
            )
            .unwrap();
            assert!(matches!(
                plan_source_callable(&fixture.store, &host, declaration, owner, None),
                Err(SourceCallableError::Unsupported(
                    SourceCallableUnsupported::GenericSignature(_)
                ))
            ));
            let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
            let targets = CanonicalArrayTargets::for_test(
                bootstrap.empty_generic_type,
                bootstrap.empty_generic_type,
            );
            let plan =
                plan_source_callable(&fixture.store, &host, declaration, owner, Some(targets))
                    .unwrap();
            assert_eq!(plan.parameters.len(), 1);
            assert_eq!(plan.generic_return_type_parameter_index, Some(0));
        }
    }

    #[test]
    fn ambient_namespace_constructor_parameters_preserve_binder_owned_signatures() {
        let fixture = QueryFixture::with_source_facts(
            concat!(
                "declare module 'prop-types' { ",
                "export interface Requireable<T> {} ",
                "export function instanceOf<T>(expectedClass: ",
                "new (...args: any[]) => T): Requireable<T>; ",
                "}",
            ),
            FileId::new(1_241),
            true,
            CanonicalModuleState::Script,
        );
        let declaration = fixture
            .parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::FunctionDeclaration).then_some(NodeRef::new(
                    fixture.parsed.arena.id(),
                    fixture.file,
                    node,
                ))
            })
            .unwrap();
        let owner = fixture.bound.symbol(declaration).unwrap();
        let host = DeclaredTypeHost::new([(&fixture.parsed.arena, &fixture.bound)]).unwrap();
        let before = generic_transaction_state(&fixture.store);

        let plan = plan_source_callable(&fixture.store, &host, declaration, owner, None)
            .expect("ambient constructor parameters must retain their binder-owned signatures");
        assert_eq!(plan.type_parameters.len(), 1);
        assert_eq!(plan.parameters.len(), 1);
        assert_eq!(
            fixture.store.source_node_kind(plan.parameters[0].type_node),
            Some(SyntaxKind::ConstructorType),
        );
        assert_eq!(
            plan.return_type
                .type_node()
                .and_then(|node| fixture.store.source_node_kind(node)),
            Some(SyntaxKind::TypeReference),
        );
        assert_eq!(generic_transaction_state(&fixture.store), before);
    }

    #[test]
    fn ambient_namespace_generic_constraints_and_cold_arrays_require_matching_exports() {
        let fixture = QueryFixture::with_source_facts(
            concat!(
                "declare module 'prop-types' { ",
                "export interface Validator<T> {} ",
                "export interface Requireable<T> {} ",
                "export type ValidationMap<T> = Validator<T>; ",
                "export function oneOfType<T extends Validator<any>>",
                "(value: Validator<T>): Requireable<T>; ",
                "export function shape<P extends ValidationMap<any>>",
                "(value: P): Requireable<P>; ",
                "export function oneOf<T>(values: T[]): Requireable<T>; ",
                "}",
            ),
            FileId::new(1_242),
            true,
            CanonicalModuleState::Script,
        );
        let host = DeclaredTypeHost::new([(&fixture.parsed.arena, &fixture.bound)]).unwrap();
        let before = generic_transaction_state(&fixture.store);
        let declarations = fixture
            .parsed
            .arena
            .iter()
            .filter_map(|(node, record)| {
                (record.kind == SyntaxKind::FunctionDeclaration).then_some(NodeRef::new(
                    fixture.parsed.arena.id(),
                    fixture.file,
                    node,
                ))
            })
            .collect::<Vec<_>>();
        assert_eq!(declarations.len(), 3);

        for declaration in declarations {
            let owner = fixture.bound.symbol(declaration).unwrap();
            let plan = plan_source_callable(&fixture.store, &host, declaration, owner, None)
                .expect("matching ambient namespace exports must authenticate generic types");
            assert_eq!(plan.type_parameters.len(), 1);
            assert_eq!(plan.parameters.len(), 1);
        }
        assert_eq!(generic_transaction_state(&fixture.store), before);
    }

    #[test]
    fn ambient_namespace_constructor_parameters_reject_other_signature_shapes() {
        for (index, constructor) in [
            "new (args: any[]) => T",
            "new (...args: string[]) => T",
            "new <U>(...args: any[]) => T",
            "new (...args: any[]) => string",
        ]
        .into_iter()
        .enumerate()
        {
            let source = format!(
                "declare module 'prop-types' {{ \
                 export interface Requireable<T> {{}} \
                 export function instanceOf<T>(expectedClass: {constructor}): Requireable<T>; \
                 }}",
            );
            let fixture = QueryFixture::with_source_facts(
                &source,
                FileId::new(1_243 + u32::try_from(index).unwrap()),
                true,
                CanonicalModuleState::Script,
            );
            let declaration = fixture
                .parsed
                .arena
                .iter()
                .find_map(|(node, record)| {
                    (record.kind == SyntaxKind::FunctionDeclaration).then_some(NodeRef::new(
                        fixture.parsed.arena.id(),
                        fixture.file,
                        node,
                    ))
                })
                .unwrap();
            let owner = fixture.bound.symbol(declaration).unwrap();
            let host = DeclaredTypeHost::new([(&fixture.parsed.arena, &fixture.bound)]).unwrap();
            let before = generic_transaction_state(&fixture.store);

            assert!(matches!(
                plan_source_callable(&fixture.store, &host, declaration, owner, None),
                Err(SourceCallableError::Unsupported(
                    SourceCallableUnsupported::GenericSignature(_)
                ))
            ));
            assert_eq!(generic_transaction_state(&fixture.store), before);
        }
    }

    #[test]
    fn generic_interface_parameter_and_return_types_preserve_wrapped_type_parameters() {
        let mut fixture = QueryFixture::new(
            concat!(
                "interface Box<T> {} ",
                "declare function wrap<T>(value: Box<T>): Box<T>;",
            ),
            FileId::new(1_238),
        );
        let globals = fixture.store.intrinsic_bootstrap().unwrap().globals;
        let interface = fixture
            .bound
            .locals(fixture.bound.source_file())
            .and_then(|locals| fixture.store.symbol_table(locals))
            .and_then(|locals| locals.get_source("Box"))
            .unwrap();
        assert_eq!(
            fixture.store.merge_global_symbol(globals, interface),
            Ok(interface)
        );
        let (declaration, type_parameter, parameter_type, return_type) = fixture.generic_parts();
        let owner = fixture.bound.symbol(declaration).unwrap();
        let parameter = SourceCallableTypeParameterPlan {
            declaration: type_parameter,
            symbol: fixture.bound.symbol(type_parameter).unwrap(),
            constraint: None,
            default_type: None,
        };
        let host = DeclaredTypeHost::new_after_global_merge(
            [(&fixture.parsed.arena, &fixture.bound)],
            GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
        )
        .unwrap();
        let before = generic_transaction_state(&fixture.store);

        assert!(
            is_exact_source_generic_interface_reference(
                &fixture.store,
                &host,
                parameter_type,
                &[parameter],
                None,
            )
            .unwrap(),
            "the wrapped parameter annotation must resolve to the local generic interface"
        );
        assert!(
            is_exact_source_generic_interface_reference(
                &fixture.store,
                &host,
                return_type,
                &[parameter],
                None,
            )
            .unwrap(),
            "the wrapped return annotation must resolve to the local generic interface"
        );
        let plan = plan_source_callable(&fixture.store, &host, declaration, owner, None)
            .expect("wrapped source type parameters must remain valid generic annotations");

        assert_eq!(plan.parameters[0].type_node, parameter_type);
        assert_eq!(plan.return_type.type_node(), Some(return_type));
        assert_eq!(generic_transaction_state(&fixture.store), before);
        drop(host);

        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        let callable = fixture
            .query_callable(declaration, owner, &mut diagnostics)
            .expect("the canonical generic interface references must resolve");
        assert!(matches!(
            validate_stored_source_callable(&fixture.store, callable),
            StoredSourceCallableValidation::Valid(_)
        ));
        assert!(diagnostics.is_empty());

        let warm = generic_transaction_state(&fixture.store);
        assert_eq!(
            fixture.query_callable(declaration, owner, &mut diagnostics),
            Ok(callable)
        );
        assert_eq!(generic_transaction_state(&fixture.store), warm);
    }

    #[test]
    fn optional_generic_signatures_preserve_reduced_arity_cold_and_warm() {
        for (index, (source, expected_minimum, expected_parameters)) in [
            ("declare function optional<T>(value?: T): T;", 0, 1),
            (
                "declare function fallback<T, U = T>(value: T, next?: U): U;",
                1,
                2,
            ),
            ("function direct<T>(value?: T): T { return value; }", 0, 1),
        ]
        .into_iter()
        .enumerate()
        {
            let mut fixture =
                QueryFixture::new(source, FileId::new(1_110 + u32::try_from(index).unwrap()));
            let (declaration, _, _, _) = fixture.generic_parts();
            let owner = fixture.bound.symbol(declaration).unwrap();
            let host = DeclaredTypeHost::new_after_global_merge(
                [(&fixture.parsed.arena, &fixture.bound)],
                GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
            )
            .unwrap();
            let plan = plan_source_callable(&fixture.store, &host, declaration, owner, None)
                .unwrap_or_else(|error| panic!("{source}: {error:?}"));
            assert_eq!(plan.min_argument_count, expected_minimum);
            assert_eq!(plan.parameters.len(), expected_parameters);
            assert!(plan.parameters.last().unwrap().optional);
            drop(host);

            let mut diagnostics = CanonicalCheckerDiagnostics::default();
            let callable = fixture
                .query_callable(declaration, owner, &mut diagnostics)
                .unwrap_or_else(|error| panic!("{source}: {error:?}"));
            let signature = fixture
                .store
                .source_callable_provenance(callable)
                .unwrap()
                .signature;
            assert_eq!(
                fixture
                    .store
                    .signature(signature)
                    .unwrap()
                    .min_argument_count(),
                expected_minimum
            );
            assert!(matches!(
                validate_stored_source_callable(&fixture.store, callable),
                StoredSourceCallableValidation::Valid(_)
            ));
            let warm = generic_transaction_state(&fixture.store);
            assert_eq!(
                fixture.query_callable(declaration, owner, &mut diagnostics),
                Ok(callable)
            );
            assert_eq!(generic_transaction_state(&fixture.store), warm);
            assert!(diagnostics.is_empty());
        }
    }

    #[test]
    fn primitive_constraints_accept_compatible_literal_default_syntax() {
        for (index, source) in [
            "declare function numeric<T extends number = 1>(value: T): T;",
            "declare function negative<T extends number = -1>(value: T): T;",
            "declare function bigint<T extends bigint = 1n>(value: T): T;",
            "declare function negativeBigint<T extends bigint = -1n>(value: T): T;",
            "declare function negativeZero<T extends number = -0>(value: T): T;",
            "declare function negativeZeroBigint<T extends bigint = -0n>(value: T): T;",
            "declare function text<T extends string = 'ready'>(value: T): T;",
            "declare function truth<T extends boolean = true>(value: T): T;",
        ]
        .into_iter()
        .enumerate()
        {
            let fixture =
                QueryFixture::new(source, FileId::new(1_120 + u32::try_from(index).unwrap()));
            let (declaration, _, _, _) = fixture.generic_parts();
            let owner = fixture.bound.symbol(declaration).unwrap();
            let host = DeclaredTypeHost::new_after_global_merge(
                [(&fixture.parsed.arena, &fixture.bound)],
                GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
            )
            .unwrap();
            let before = generic_transaction_state(&fixture.store);

            let plan = plan_source_callable(&fixture.store, &host, declaration, owner, None)
                .unwrap_or_else(|error| panic!("{source}: {error:?}"));
            assert!(plan.type_parameters[0].constraint.is_some());
            assert!(plan.type_parameters[0].default_type.is_some());
            assert_eq!(generic_transaction_state(&fixture.store), before);
        }
    }

    #[test]
    fn negative_numeric_generic_defaults_publish_and_replay_canonical_literals() {
        for (index, (source, expected_flags)) in [
            (
                "declare function numeric<T extends number = -1>(value: T): T;",
                TypeFlags::NUMBER_LITERAL,
            ),
            (
                "declare function bigint<T extends bigint = -1n>(value: T): T;",
                TypeFlags::BIG_INT_LITERAL,
            ),
            (
                "declare function numericZero<T extends number = -0>(value: T): T;",
                TypeFlags::NUMBER_LITERAL,
            ),
            (
                "declare function bigintZero<T extends bigint = -0n>(value: T): T;",
                TypeFlags::BIG_INT_LITERAL,
            ),
        ]
        .into_iter()
        .enumerate()
        {
            let mut fixture =
                QueryFixture::new(source, FileId::new(1_170 + u32::try_from(index).unwrap()));
            let (declaration, _, _, _) = fixture.generic_parts();
            let owner = fixture.bound.symbol(declaration).unwrap();
            let mut diagnostics = CanonicalCheckerDiagnostics::default();

            let callable = fixture
                .query_callable(declaration, owner, &mut diagnostics)
                .unwrap_or_else(|error| panic!("{source}: {error:?}"));
            let signature = fixture
                .store
                .source_callable_provenance(callable)
                .unwrap()
                .signature;
            let [type_parameter] = fixture
                .store
                .signature(signature)
                .unwrap()
                .type_parameters()
            else {
                panic!("{source}: expected one type parameter")
            };
            let TypeData::TypeParameter(parameter) =
                fixture.store.type_payload(*type_parameter).unwrap().data()
            else {
                panic!("{source}: expected a canonical type parameter")
            };
            let default_type = parameter.resolved_default_type.unwrap();
            assert_eq!(
                fixture.store.type_payload(default_type).unwrap().flags(),
                expected_flags
            );
            assert!(matches!(
                validate_stored_source_callable(&fixture.store, callable),
                StoredSourceCallableValidation::Valid(_)
            ));
            let warm = generic_transaction_state(&fixture.store);
            assert_eq!(
                fixture.query_callable(declaration, owner, &mut diagnostics),
                Ok(callable)
            );
            assert_eq!(generic_transaction_state(&fixture.store), warm);
            assert!(diagnostics.is_empty(), "{source}: {diagnostics:?}");
        }
    }

    #[test]
    fn incompatible_literal_defaults_are_rejected_before_publication() {
        for (index, source) in [
            "declare function text<T extends string = 1>(value: T): T;",
            "declare function numeric<T extends number = 'wrong'>(value: T): T;",
            "declare function truth<T extends boolean = 1>(value: T): T;",
        ]
        .into_iter()
        .enumerate()
        {
            let fixture =
                QueryFixture::new(source, FileId::new(1_130 + u32::try_from(index).unwrap()));
            let (declaration, _, _, _) = fixture.generic_parts();
            let owner = fixture.bound.symbol(declaration).unwrap();
            let host = DeclaredTypeHost::new_after_global_merge(
                [(&fixture.parsed.arena, &fixture.bound)],
                GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
            )
            .unwrap();
            let before = generic_transaction_state(&fixture.store);

            assert!(matches!(
                plan_source_callable(&fixture.store, &host, declaration, owner, None),
                Err(SourceCallableError::Unsupported(
                    SourceCallableUnsupported::GenericSignature(_)
                ))
            ));
            assert_eq!(generic_transaction_state(&fixture.store), before);
        }
    }

    #[test]
    fn recursive_generic_array_parameter_warm_cache_is_exact_at_every_wrapper() {
        let parsed = parse_source_file(
            "interface Array<T> {} interface ReadonlyArray<T> {} \
             function deep<T>(values: Array<T[]>[]): T { return values[0][0][0]; }",
        );
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(996);
        let mut context = bind_context(&parsed, file);
        let (declaration, _, parameter_type, _) = generic_function_parts(&parsed, file);
        let resolved = context.get_type_from_type_node(parameter_type).unwrap();
        let array_targets = CanonicalArrayTargets::from_global_types(context.global_types());
        let owner = context.file(file).unwrap().1.symbol(declaration).unwrap();
        {
            let (_, bound) = context.file(file).unwrap();
            let host = DeclaredTypeHost::new_after_global_merge(
                [(&parsed.arena, bound)],
                GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
            )
            .unwrap();
            let plan = plan_source_callable(
                context.store(),
                &host,
                declaration,
                owner,
                Some(array_targets),
            )
            .unwrap();
            assert_eq!(plan.parameters.len(), 1);
            assert_eq!(
                context.store().type_node_links(parameter_type),
                Some(&TypeNodeLinks {
                    resolved_type: Some(resolved),
                    outer_type_parameters: None,
                })
            );
        }

        let NodeData::ArrayTypeNode(outer) = &parsed.arena.get(parameter_type.node).unwrap().data
        else {
            panic!("the mixed fixture has an outer array type")
        };
        let inner_reference = NodeRef::new(parameter_type.arena, file, outer.element_type);
        assert_eq!(
            parsed.arena.get(inner_reference.node).unwrap().kind,
            SyntaxKind::TypeReference
        );
        let number = context.store().intrinsic_bootstrap().unwrap().number_type;
        assert!(context.store_mut_for_test().set_type_node_links(
            inner_reference,
            TypeNodeLinks {
                resolved_type: Some(number),
                outer_type_parameters: None,
            },
        ));
        let before = generic_transaction_state(context.store());
        let (_, bound) = context.file(file).unwrap();
        let host = DeclaredTypeHost::new_after_global_merge(
            [(&parsed.arena, bound)],
            GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
        )
        .unwrap();
        assert!(
            plan_source_callable(
                context.store(),
                &host,
                declaration,
                owner,
                Some(array_targets),
            )
            .is_err()
        );
        assert_eq!(generic_transaction_state(context.store()), before);
    }

    #[test]
    fn recursive_generic_array_semantic_shape_uses_authoritative_mutable_targets() {
        let parsed = parse_source_file(
            "interface Array<T> {} interface ReadonlyArray<T> {} \
             function identity<T>(value: T): T { return value; }",
        );
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(997);
        let mut context = bind_context(&parsed, file);
        let (_, _, parameter_type, _) = generic_function_parts(&parsed, file);
        let type_parameter = context.get_type_from_type_node(parameter_type).unwrap();
        let global_types = context.global_types().clone();
        let array_targets = CanonicalArrayTargets::from_global_types(&global_types);
        let store = context.store_mut_for_test();
        let inner = store
            .create_canonical_array_type_with_targets(array_targets, type_parameter, false)
            .unwrap();
        let outer = store
            .create_canonical_array_type_with_targets(array_targets, inner, false)
            .unwrap();
        let readonly = store
            .create_canonical_array_type_with_targets(array_targets, outer, true)
            .unwrap();

        assert!(valid_generic_source_parameter_type(
            store,
            Some(array_targets),
            outer,
            &[type_parameter],
        ));
        assert!(!valid_generic_source_parameter_type(
            store,
            None,
            outer,
            &[type_parameter],
        ));
        assert!(!valid_generic_source_parameter_type(
            store,
            Some(array_targets),
            readonly,
            &[type_parameter],
        ));
        let number = store.intrinsic_bootstrap().unwrap().number_type;
        assert!(!valid_generic_source_parameter_type(
            store,
            Some(array_targets),
            outer,
            &[number],
        ));
    }

    #[test]
    fn non_generic_source_callable_rejects_forged_type_parameter_provenance() {
        let mut fixture = QueryFixture::new(
            "function plain(value: string): string { return value; }",
            FileId::new(943),
        );
        let declaration = fixture
            .parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::FunctionDeclaration).then_some(NodeRef::new(
                    fixture.parsed.arena.id(),
                    fixture.file,
                    node,
                ))
            })
            .unwrap();
        let NodeData::FunctionDeclaration(function) =
            &fixture.parsed.arena.get(declaration.node).unwrap().data
        else {
            unreachable!()
        };
        let owner = fixture.bound.symbol(declaration).unwrap();
        let parameter = fixture
            .bound
            .symbol(NodeRef::new(
                declaration.arena,
                declaration.file,
                function.parameters.nodes[0],
            ))
            .unwrap();
        let signature = fixture
            .store
            .alloc_signature(
                SignatureFlags::NONE,
                Some(declaration),
                Vec::new(),
                None,
                vec![parameter],
                None,
                None,
                1,
            )
            .unwrap();
        let string = fixture.store.intrinsic_bootstrap().unwrap().string_type;
        assert!(
            fixture
                .store
                .replace_source_callable_type_parameters_for_test(
                    signature,
                    Some(
                        vec![SourceCallableTypeParameterProvenance {
                            declaration,
                            symbol: owner,
                            type_parameter: string,
                            constraint: None,
                            default_type: None,
                        }]
                        .into_boxed_slice(),
                    ),
                )
                .is_none()
        );
        let callable = fixture
            .store
            .alloc_plain_object_type(ObjectFlags::ANONYMOUS, Some(owner))
            .unwrap();
        assert!(!fixture.store.set_source_callable_provenance(
            callable,
            SourceCallableProvenance {
                family: SourceCallableFamily::FunctionDeclaration,
                declaration,
                owner_symbol: owner,
                owner_parent: None,
                export_local: None,
                signature,
                return_provenance: SourceCallableReturnProvenance::Annotated,
                array_targets: None,
                generic_return_type_parameter: None,
                contextual_target: None,
                contextual_variable: None,
            },
        ));
        assert_eq!(
            fixture.store.source_callable_provenance_lengths(),
            [0, 0, 0, 0, 1]
        );
    }

    #[test]
    fn exact_generic_identity_query_publishes_and_reuses_one_declared_identity() {
        let mut fixture = QueryFixture::new(
            "function identity<T>(value: T): T { return value; }",
            FileId::new(951),
        );
        let (declaration, type_parameter_declaration) = fixture.declaration_and_type_parameter();
        let owner = fixture.bound.symbol(declaration).unwrap();
        let type_parameter_symbol = fixture.bound.symbol(type_parameter_declaration).unwrap();
        assert!(
            fixture
                .store
                .declared_type_links(type_parameter_symbol)
                .is_none()
        );
        assert!(
            fixture
                .store
                .source_callable_type_for_owner(owner)
                .is_none()
        );

        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        let callable = fixture
            .query_callable(declaration, owner, &mut diagnostics)
            .unwrap();
        let provenance = fixture.store.source_callable_provenance(callable).unwrap();
        let signature = provenance.signature;
        let type_parameter = fixture
            .store
            .signature(signature)
            .unwrap()
            .type_parameters()[0];
        assert_eq!(
            fixture.store.source_callable_type_parameters(signature),
            Some(
                &[SourceCallableTypeParameterProvenance {
                    declaration: type_parameter_declaration,
                    symbol: type_parameter_symbol,
                    type_parameter,
                    constraint: None,
                    default_type: None,
                }][..]
            )
        );
        assert_eq!(
            fixture
                .store
                .declared_type_links(type_parameter_symbol)
                .and_then(|links| links.declared_type),
            Some(type_parameter)
        );
        let [parameter] = fixture.store.signature(signature).unwrap().parameters() else {
            panic!("expected identity parameter")
        };
        assert_eq!(
            fixture
                .store
                .value_symbol_links(*parameter)
                .and_then(|links| links.resolved_type),
            Some(type_parameter)
        );
        assert_eq!(
            fixture.query_return(signature, &mut diagnostics),
            Ok(type_parameter)
        );
        assert!(matches!(
            validate_stored_source_callable(&fixture.store, callable),
            StoredSourceCallableValidation::Valid(edges) if edges.contains(&type_parameter)
        ));

        let warm = publication_state(&fixture.store);
        assert_eq!(
            fixture.query_callable(declaration, owner, &mut diagnostics),
            Ok(callable)
        );
        assert_eq!(
            fixture.query_return(signature, &mut diagnostics),
            Ok(type_parameter)
        );
        assert_eq!(publication_state(&fixture.store), warm);
        assert_eq!(
            fixture
                .store
                .signature(signature)
                .unwrap()
                .type_parameters(),
            [type_parameter]
        );
        assert!(diagnostics.is_empty());
    }

    #[test]
    fn generic_annotation_warm_orders_reuse_the_declared_identity() {
        for (index, warm_return_first) in [false, true].into_iter().enumerate() {
            let mut fixture = QueryFixture::new(
                "function identity<T>(value: T): T { return value; }",
                FileId::new(953 + u32::try_from(index).unwrap()),
            );
            let (declaration, type_parameter_declaration, parameter_type, return_type) =
                fixture.generic_parts();
            let owner = fixture.bound.symbol(declaration).unwrap();
            let type_parameter_symbol = fixture.bound.symbol(type_parameter_declaration).unwrap();
            let first = if warm_return_first {
                return_type
            } else {
                parameter_type
            };
            let second = if warm_return_first {
                parameter_type
            } else {
                return_type
            };
            let mut diagnostics = CanonicalCheckerDiagnostics::default();

            let type_parameter = fixture.query_type_node(first, &mut diagnostics).unwrap();
            assert_eq!(
                fixture
                    .store
                    .declared_type_links(type_parameter_symbol)
                    .and_then(|links| links.declared_type),
                Some(type_parameter)
            );
            assert_exact_warm_type_parameter_annotation(
                &fixture.store,
                first,
                type_parameter_symbol,
                type_parameter,
            );
            assert!(
                fixture
                    .store
                    .symbol_node_links(second)
                    .is_none_or(|links| links == &SymbolNodeLinks::default())
            );
            assert!(
                fixture
                    .store
                    .type_node_links(second)
                    .is_none_or(|links| links == &TypeNodeLinks::default())
            );

            let callable = fixture
                .query_callable(declaration, owner, &mut diagnostics)
                .unwrap();
            let signature = fixture
                .store
                .source_callable_provenance(callable)
                .unwrap()
                .signature;
            assert_exact_warm_type_parameter_annotation(
                &fixture.store,
                parameter_type,
                type_parameter_symbol,
                type_parameter,
            );
            assert_eq!(
                fixture.query_return(signature, &mut diagnostics),
                Ok(type_parameter)
            );
            assert_exact_warm_type_parameter_annotation(
                &fixture.store,
                return_type,
                type_parameter_symbol,
                type_parameter,
            );
            assert!(matches!(
                validate_stored_source_callable(&fixture.store, callable),
                StoredSourceCallableValidation::Valid(edges)
                    if edges.iter().filter(|edge| **edge == type_parameter).count() >= 3
            ));
            assert!(diagnostics.is_empty());
        }
    }

    #[test]
    fn partial_and_poisoned_cold_generic_annotation_links_publish_nothing() {
        let source = "function identity<T>(value: T): T { return value; }";

        let mut symbol_only = QueryFixture::new(source, FileId::new(955));
        let (declaration, type_parameter_declaration, parameter_type, _) =
            symbol_only.generic_parts();
        let owner = symbol_only.bound.symbol(declaration).unwrap();
        let type_parameter_symbol = symbol_only
            .bound
            .symbol(type_parameter_declaration)
            .unwrap();
        assert!(symbol_only.store.set_symbol_node_links(
            parameter_type,
            SymbolNodeLinks {
                resolved_symbol: Some(type_parameter_symbol),
            },
        ));
        let before = publication_state(&symbol_only.store);
        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        assert!(
            symbol_only
                .query_callable(declaration, owner, &mut diagnostics)
                .is_err()
        );
        assert_eq!(publication_state(&symbol_only.store), before);
        assert!(
            symbol_only
                .store
                .source_callable_type_for_owner(owner)
                .is_none()
        );

        let mut type_only = QueryFixture::new(source, FileId::new(956));
        let (declaration, _, parameter_type, return_type) = type_only.generic_parts();
        let owner = type_only.bound.symbol(declaration).unwrap();
        let type_parameter = type_only
            .query_type_node(return_type, &mut diagnostics)
            .unwrap();
        assert!(type_only.store.set_type_node_links(
            parameter_type,
            TypeNodeLinks {
                resolved_type: Some(type_parameter),
                outer_type_parameters: None,
            },
        ));
        let before = publication_state(&type_only.store);
        assert!(
            type_only
                .query_callable(declaration, owner, &mut diagnostics)
                .is_err()
        );
        assert_eq!(publication_state(&type_only.store), before);
        assert!(
            type_only
                .store
                .source_callable_type_for_owner(owner)
                .is_none()
        );

        let mut outer_poison = QueryFixture::new(source, FileId::new(957));
        let (declaration, type_parameter_declaration, parameter_type, return_type) =
            outer_poison.generic_parts();
        let owner = outer_poison.bound.symbol(declaration).unwrap();
        let type_parameter_symbol = outer_poison
            .bound
            .symbol(type_parameter_declaration)
            .unwrap();
        let type_parameter = outer_poison
            .query_type_node(return_type, &mut diagnostics)
            .unwrap();
        assert!(outer_poison.store.set_symbol_node_links(
            parameter_type,
            SymbolNodeLinks {
                resolved_symbol: Some(type_parameter_symbol),
            },
        ));
        assert!(outer_poison.store.set_type_node_links(
            parameter_type,
            TypeNodeLinks {
                resolved_type: Some(type_parameter),
                outer_type_parameters: Some(vec![type_parameter]),
            },
        ));
        let before = publication_state(&outer_poison.store);
        assert!(
            outer_poison
                .query_callable(declaration, owner, &mut diagnostics)
                .is_err()
        );
        assert_eq!(publication_state(&outer_poison.store), before);
        assert!(
            outer_poison
                .store
                .source_callable_type_for_owner(owner)
                .is_none()
        );

        let mut wrong_pair = QueryFixture::new(source, FileId::new(958));
        let (declaration, _, parameter_type, _) = wrong_pair.generic_parts();
        let owner = wrong_pair.bound.symbol(declaration).unwrap();
        let number = wrong_pair.store.intrinsic_bootstrap().unwrap().number_type;
        assert!(wrong_pair.store.set_symbol_node_links(
            parameter_type,
            SymbolNodeLinks {
                resolved_symbol: Some(owner),
            },
        ));
        assert!(wrong_pair.store.set_type_node_links(
            parameter_type,
            TypeNodeLinks {
                resolved_type: Some(number),
                outer_type_parameters: None,
            },
        ));
        let before = publication_state(&wrong_pair.store);
        assert!(
            wrong_pair
                .query_callable(declaration, owner, &mut diagnostics)
                .is_err()
        );
        assert_eq!(publication_state(&wrong_pair.store), before);
        assert!(
            wrong_pair
                .store
                .source_callable_type_for_owner(owner)
                .is_none()
        );
        assert!(diagnostics.is_empty());
    }

    #[test]
    fn unsupported_generic_signature_shapes_publish_nothing() {
        for (index, source) in [
            "function f<T extends U, U>(value: T): T { return value; }",
            "function f<T extends T>(value: T): T { return value; }",
            "function f<T extends string | number>(value: T): T { return value; }",
            "function f<T extends string = number>(): string { return ''; }",
            "function f<T>(value: (item: T) => T): T { return value as any; }",
            "function f<T>(value: T): { value: T } { return { value }; }",
        ]
        .into_iter()
        .enumerate()
        {
            let parsed = parse_source_file(source);
            assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
            let file = FileId::new(960 + u32::try_from(index).unwrap());
            let (declaration, type_parameter_declaration) =
                function_and_type_parameter(&parsed, file);
            let mut context = bind_context(&parsed, file);
            let (owner, type_parameter_symbol) = {
                let (_, bound) = context.file(file).unwrap();
                (
                    bound.symbol(declaration).unwrap(),
                    bound.symbol(type_parameter_declaration).unwrap(),
                )
            };
            let before = publication_state(context.store());
            assert!(matches!(
                context.check_source_file(file),
                Err(SourceCheckError::Unsupported(
                    UnsupportedSourceSyntax::Function(SourceFunctionUnsupported::Callable(_))
                ))
            ));
            assert_eq!(publication_state(context.store()), before);
            assert!(
                context
                    .store()
                    .declared_type_links(type_parameter_symbol)
                    .is_none()
            );
            assert!(
                context
                    .store()
                    .source_callable_type_for_owner(owner)
                    .is_none()
            );
            assert!(context.diagnostics().is_empty());
        }
    }

    #[test]
    fn const_type_parameter_fails_before_generic_identity_publication() {
        let mut fixture = QueryFixture::new(
            "function identity<const T>(value: T): T { return value; }",
            FileId::new(970),
        );
        let (declaration, type_parameter_declaration, _, _) = fixture.generic_parts();
        let owner = fixture.bound.symbol(declaration).unwrap();
        let type_parameter_symbol = fixture.bound.symbol(type_parameter_declaration).unwrap();
        let before = generic_transaction_state(&fixture.store);
        let mut diagnostics = CanonicalCheckerDiagnostics::default();

        assert!(
            fixture
                .query_callable(declaration, owner, &mut diagnostics)
                .is_err()
        );
        assert_eq!(generic_transaction_state(&fixture.store), before);
        assert!(
            fixture
                .store
                .declared_type_links(type_parameter_symbol)
                .is_none()
        );
        assert!(
            fixture
                .store
                .source_callable_type_for_owner(owner)
                .is_none()
        );
        assert!(diagnostics.is_empty());
    }

    #[test]
    fn swapped_ordered_return_type_parameter_fails_atomically() {
        let mut staged = staged_generic_publication(
            "function pair<T, U>(left: T, right: U): U { return right; }",
            FileId::new(981),
        );
        let expected_return = staged.resolved[1].provenance.type_parameter;
        assert_eq!(staged.generic_return_type_parameter, Some(expected_return));
        staged.generic_return_type_parameter = Some(staged.resolved[0].provenance.type_parameter);
        let before = generic_transaction_state(&staged.fixture.store);

        assert_eq!(staged.publish(), None);
        assert_eq!(generic_transaction_state(&staged.fixture.store), before);
        assert!(
            staged
                .fixture
                .store
                .source_callable_type_for_owner(staged.owner)
                .is_none()
        );
    }

    #[test]
    fn poisoned_declared_or_signature_type_parameter_fails_without_new_publication() {
        let mut cold = QueryFixture::new(
            "function identity<T>(value: T): T { return value; }",
            FileId::new(971),
        );
        let (declaration, type_parameter_declaration) = cold.declaration_and_type_parameter();
        let owner = cold.bound.symbol(declaration).unwrap();
        let type_parameter_symbol = cold.bound.symbol(type_parameter_declaration).unwrap();
        let forged = cold.store.alloc_type_parameter(None).unwrap();
        assert!(cold.store.set_declared_type_links(
            type_parameter_symbol,
            DeclaredTypeLinks {
                declared_type: Some(forged),
                ..DeclaredTypeLinks::default()
            }
        ));
        let poisoned_cold = publication_state(&cold.store);
        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        assert!(
            cold.query_callable(declaration, owner, &mut diagnostics)
                .is_err()
        );
        assert_eq!(publication_state(&cold.store), poisoned_cold);
        assert!(cold.store.source_callable_type_for_owner(owner).is_none());

        let mut warm = QueryFixture::new(
            "function identity<T>(value: T): T { return value; }",
            FileId::new(972),
        );
        let (declaration, _) = warm.declaration_and_type_parameter();
        let owner = warm.bound.symbol(declaration).unwrap();
        let callable = warm
            .query_callable(declaration, owner, &mut diagnostics)
            .unwrap();
        let signature = warm
            .store
            .source_callable_provenance(callable)
            .unwrap()
            .signature;
        let number = warm.store.intrinsic_bootstrap().unwrap().number_type;
        assert!(
            warm.store
                .set_signature_type_parameters(signature, vec![number])
        );
        assert_eq!(
            validate_stored_source_callable(&warm.store, callable),
            StoredSourceCallableValidation::Malformed
        );
        let poisoned_warm = publication_state(&warm.store);
        assert!(warm.query_return(signature, &mut diagnostics).is_err());
        assert_eq!(publication_state(&warm.store), poisoned_warm);
        assert!(diagnostics.is_empty());
    }

    #[test]
    fn poisoned_warm_generic_annotation_links_and_signature_shape_fail_closed() {
        let source = "function identity<T>(value: T): T { return value; }";
        let mut diagnostics = CanonicalCheckerDiagnostics::default();

        let mut parameter_poison = QueryFixture::new(source, FileId::new(973));
        let (declaration, _, parameter_type, _) = parameter_poison.generic_parts();
        let owner = parameter_poison.bound.symbol(declaration).unwrap();
        let callable = parameter_poison
            .query_callable(declaration, owner, &mut diagnostics)
            .unwrap();
        let number = parameter_poison
            .store
            .intrinsic_bootstrap()
            .unwrap()
            .number_type;
        assert!(parameter_poison.store.set_type_node_links(
            parameter_type,
            TypeNodeLinks {
                resolved_type: Some(number),
                outer_type_parameters: None,
            },
        ));
        let before = publication_state(&parameter_poison.store);
        assert!(
            parameter_poison
                .query_callable(declaration, owner, &mut diagnostics)
                .is_err()
        );
        assert_eq!(publication_state(&parameter_poison.store), before);
        assert_eq!(
            parameter_poison.store.source_callable_type_for_owner(owner),
            Some(callable)
        );

        let mut return_poison = QueryFixture::new(source, FileId::new(974));
        let (declaration, _, _, return_type) = return_poison.generic_parts();
        let owner = return_poison.bound.symbol(declaration).unwrap();
        let callable = return_poison
            .query_callable(declaration, owner, &mut diagnostics)
            .unwrap();
        let signature = return_poison
            .store
            .source_callable_provenance(callable)
            .unwrap()
            .signature;
        let type_parameter = return_poison
            .query_return(signature, &mut diagnostics)
            .unwrap();
        assert_eq!(
            return_poison
                .store
                .signature(signature)
                .unwrap()
                .resolved_return_type(),
            Some(type_parameter)
        );
        assert!(return_poison.store.set_symbol_node_links(
            return_type,
            SymbolNodeLinks {
                resolved_symbol: Some(owner),
            },
        ));
        assert_eq!(
            validate_stored_source_callable(&return_poison.store, callable),
            StoredSourceCallableValidation::Malformed
        );
        let before = publication_state(&return_poison.store);
        assert!(
            return_poison
                .query_return(signature, &mut diagnostics)
                .is_err()
        );
        assert_eq!(publication_state(&return_poison.store), before);

        let mut shape_poison = QueryFixture::new(source, FileId::new(975));
        let (declaration, _, _, _) = shape_poison.generic_parts();
        let owner = shape_poison.bound.symbol(declaration).unwrap();
        let callable = shape_poison
            .query_callable(declaration, owner, &mut diagnostics)
            .unwrap();
        let signature = shape_poison
            .store
            .source_callable_provenance(callable)
            .unwrap()
            .signature;
        assert!(
            shape_poison
                .store
                .set_signature_flags(signature, SignatureFlags::HAS_LITERAL_TYPES)
        );
        assert_eq!(
            validate_stored_source_callable(&shape_poison.store, callable),
            StoredSourceCallableValidation::Malformed
        );
        let before = publication_state(&shape_poison.store);
        assert!(
            shape_poison
                .query_callable(declaration, owner, &mut diagnostics)
                .is_err()
        );
        assert_eq!(publication_state(&shape_poison.store), before);
        assert!(diagnostics.is_empty());
    }
}
