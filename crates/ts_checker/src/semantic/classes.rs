//! Exact local class shells and primitive annotated members for S11a.
//!
//! Pinned `getDeclaredTypeOfClassOrInterface` already lives in
//! [`super::declared`]. This module composes that canonical instance identity
//! with the distinct class value identity created by
//! `getTypeOfFuncClassEnumModuleWorker`. The admitted declaration plan also
//! retains the exact split between annotated instance properties
//! (`symbol.members`) and annotated static properties (`symbol.exports`).
//!
//! The member transaction adds direct primitive property annotations,
//! retained readonly state, final instance/static structured caches, and one
//! default or explicit zero-argument construct signature. The public query
//! additionally admits one direct local nongeneric base whose own completed
//! graph is in the same supported family; the whole-source adapter consumes
//! that graph only after seeing the exact direct base plan earlier in source.
//! Empty zero-argument methods retain their canonical callable identities.
//! Direct classes can also retain one string-to-number index signature.
//! Definite annotated fields admit one authenticated ambient-function decorator.
//! Nonempty executable bodies, general heritage, and non-primitive annotations
//! remain later class stages.

use std::collections::HashSet;

use ts_ast::{NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalNameResolver, CanonicalResolutionLocation, CheckFlags, EscapedName,
    InternalSymbolName, SemanticSymbolId, SymbolFlags, SymbolTableId,
    semantic::{PreparedSymbolTable, Symbol},
};

use super::{
    CanonicalTypeMapperStore, DeclaredTypeError, DeclaredTypeHost, IndexInfoId,
    ResolvedSignatureState, SignatureId, SignatureLinks, TypeId,
    declared::{preflight_class_or_interface_reference, preflight_node, type_list_key},
    links::{TypeNodeLinks, ValueSymbolLinks},
    signatures::SignatureFlags,
    source_callables::{StoredSourceCallableValidation, validate_stored_source_callable},
    store::{DirectClassHeritageProvenance, SourceNodeParent},
    type_records::{
        ConstrainedTypeData, ObjectTypeData, StructuredTypeData, TypeCacheState, TypeData,
        TypeParameterData,
    },
    types::{ObjectFlags, TypeFlags},
};

const NODE_FLAG_JSDOC: u32 = 1 << 22;
const NODE_FLAG_HAS_ERROR: u32 = 1 << 15;
const PROTOTYPE_NAME: &str = "prototype";

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum ClassPropertySide {
    Instance,
    Static,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum ClassConstructorVisibility {
    Public,
    Protected,
    Private,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct ClassConstructorPlan {
    declaration: NodeRef,
    symbol: SemanticSymbolId,
    visibility: ClassConstructorVisibility,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct ClassMethodPlan {
    declaration: NodeRef,
    symbol: SemanticSymbolId,
    name_node: NodeRef,
    name: String,
    side: ClassPropertySide,
    return_type_node: Option<NodeRef>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct ClassIndexSignaturePlan {
    declaration: NodeRef,
    symbol: SemanticSymbolId,
    key_type_node: NodeRef,
    value_type_node: NodeRef,
}

/// One source property whose annotation can be executed by the root query
/// adapter without rediscovering its binder ownership or class side.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct ClassPropertyPlan {
    declaration: NodeRef,
    symbol: SemanticSymbolId,
    name_node: NodeRef,
    type_node: NodeRef,
    name: String,
    side: ClassPropertySide,
    optional: bool,
    definite: bool,
    readonly: bool,
}

impl ClassPropertyPlan {
    pub(super) const fn declaration(&self) -> NodeRef {
        self.declaration
    }

    pub(super) const fn symbol(&self) -> SemanticSymbolId {
        self.symbol
    }

    pub(super) const fn name_node(&self) -> NodeRef {
        self.name_node
    }

    pub(super) const fn type_node(&self) -> NodeRef {
        self.type_node
    }

    pub(super) fn name(&self) -> &str {
        &self.name
    }

    pub(super) const fn side(&self) -> ClassPropertySide {
        self.side
    }

    pub(super) const fn optional(&self) -> bool {
        self.optional
    }

    pub(super) const fn definite(&self) -> bool {
        self.definite
    }

    pub(super) const fn readonly(&self) -> bool {
        self.readonly
    }
}

/// Opaque, read-only syntax and binder proof for one admitted class.
///
/// Bound properties may be cold or carry the exact retained readonly bit
/// published by this module's member transaction.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct ClassDeclarationPlan {
    declaration: NodeRef,
    symbol: SemanticSymbolId,
    base: Option<DirectClassBasePlan>,
    implementations: Vec<DirectClassImplementationPlan>,
    constructor: Option<ClassConstructorPlan>,
    index: Option<ClassIndexSignaturePlan>,
    instance_members: Option<SymbolTableId>,
    static_members: SymbolTableId,
    properties: Vec<ClassPropertyPlan>,
    instance_properties: Vec<ClassPropertyPlan>,
    static_properties: Vec<ClassPropertyPlan>,
    methods: Vec<ClassMethodPlan>,
    instance_methods: Vec<ClassMethodPlan>,
    static_methods: Vec<ClassMethodPlan>,
}

impl ClassDeclarationPlan {
    pub(super) const fn declaration(&self) -> NodeRef {
        self.declaration
    }

    pub(super) const fn symbol(&self) -> SemanticSymbolId {
        self.symbol
    }

    pub(super) const fn base(&self) -> Option<&DirectClassBasePlan> {
        self.base.as_ref()
    }

    pub(super) const fn instance_members(&self) -> Option<SymbolTableId> {
        self.instance_members
    }

    pub(super) const fn static_members(&self) -> SymbolTableId {
        self.static_members
    }

    /// Every admitted property in source declaration order.
    pub(super) fn properties(&self) -> &[ClassPropertyPlan] {
        &self.properties
    }

    pub(super) fn instance_properties(&self) -> &[ClassPropertyPlan] {
        &self.instance_properties
    }

    pub(super) fn static_properties(&self) -> &[ClassPropertyPlan] {
        &self.static_properties
    }

    pub(super) fn property_type_nodes(&self) -> impl ExactSizeIterator<Item = NodeRef> + '_ {
        self.properties.iter().map(ClassPropertyPlan::type_node)
    }
}

/// Exact direct-identifier edge retained by the class query and source plan.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct DirectClassBasePlan {
    clause: NodeRef,
    node: NodeRef,
    expression: NodeRef,
    symbol: SemanticSymbolId,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct DirectClassImplementationPlan {
    clause: NodeRef,
    node: NodeRef,
    expression: NodeRef,
    symbol: SemanticSymbolId,
}

/// The two identities installed by the class shell query.
///
/// `instance_type` is the canonical `CLASS | REFERENCE` origin from
/// `declared.rs`; `value_type` is the independent anonymous static side.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ClassShells {
    declaration: NodeRef,
    symbol: SemanticSymbolId,
    instance_type: TypeId,
    value_type: TypeId,
}

impl ClassShells {
    #[must_use]
    pub const fn declaration(self) -> NodeRef {
        self.declaration
    }

    #[must_use]
    pub const fn symbol(self) -> SemanticSymbolId {
        self.symbol
    }

    #[must_use]
    pub const fn instance_type(self) -> TypeId {
        self.instance_type
    }

    #[must_use]
    pub const fn value_type(self) -> TypeId {
        self.value_type
    }
}

/// The distinct value and instance identities retained for one direct base.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ClassBaseIdentities {
    symbol: SemanticSymbolId,
    instance_type: TypeId,
    value_type: TypeId,
}

impl ClassBaseIdentities {
    #[must_use]
    pub const fn symbol(self) -> SemanticSymbolId {
        self.symbol
    }

    #[must_use]
    pub const fn instance_type(self) -> TypeId {
        self.instance_type
    }

    #[must_use]
    pub const fn value_type(self) -> TypeId {
        self.value_type
    }
}

/// Exact member identities installed for one admitted class declaration.
///
/// `instance_members` is the maps-`this` table used by the class instance
/// reference. It is distinct from the binder's declared-member table whenever
/// the resolved instance surface is nonempty; the pinned clone of a nil table
/// remains nil. `static_members` is the resolved static table and therefore
/// also contains the class's own `prototype`; it aliases the binder export
/// table only for a class without a base. Resolved property vectors are
/// own-first and omit shadowed inherited symbols.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ClassMembers {
    shells: ClassShells,
    base: Option<ClassBaseIdentities>,
    instance_members: Option<SymbolTableId>,
    static_members: SymbolTableId,
    instance_properties: Vec<SemanticSymbolId>,
    declared_instance_property_count: usize,
    static_properties: Vec<SemanticSymbolId>,
    declared_static_property_count: usize,
    prototype: SemanticSymbolId,
    default_construct_signature: SignatureId,
}

impl ClassMembers {
    #[must_use]
    pub const fn shells(&self) -> ClassShells {
        self.shells
    }

    #[must_use]
    pub const fn base(&self) -> Option<ClassBaseIdentities> {
        self.base
    }

    #[must_use]
    pub const fn instance_members(&self) -> Option<SymbolTableId> {
        self.instance_members
    }

    #[must_use]
    pub const fn static_members(&self) -> SymbolTableId {
        self.static_members
    }

    #[must_use]
    pub fn instance_properties(&self) -> &[SemanticSymbolId] {
        &self.instance_properties
    }

    #[must_use]
    pub fn declared_instance_properties(&self) -> &[SemanticSymbolId] {
        &self.instance_properties[..self.declared_instance_property_count]
    }

    #[must_use]
    pub fn static_properties(&self) -> &[SemanticSymbolId] {
        &self.static_properties
    }

    #[must_use]
    pub fn declared_static_properties(&self) -> &[SemanticSymbolId] {
        &self.static_properties[..self.declared_static_property_count]
    }

    #[must_use]
    pub const fn prototype(&self) -> SemanticSymbolId {
        self.prototype
    }

    #[must_use]
    pub const fn default_construct_signature(&self) -> SignatureId {
        self.default_construct_signature
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ClassInvariant {
    SymbolNotOwned(SemanticSymbolId),
    InvalidOwnerSymbol(SemanticSymbolId),
    InvalidDeclaration(NodeRef),
    InvalidName(NodeRef),
    InvalidHeritage(NodeRef),
    InvalidProperty(NodeRef),
    InvalidPropertySymbol(NodeRef),
    InvalidPrototype(SemanticSymbolId),
    InvalidPlan(NodeRef),
    InvalidInstanceCache(SemanticSymbolId),
    InvalidValueCache(SemanticSymbolId),
    InvalidPropertyTypeCache(NodeRef),
    InvalidPropertyValueCache(SemanticSymbolId),
    InvalidInstanceMembers(SemanticSymbolId),
    InvalidStaticMembers(SemanticSymbolId),
    InvalidConstructSignature(SemanticSymbolId),
    InvalidHeritageCache(SemanticSymbolId),
    BootstrapUnavailable(NodeRef),
    Capacity(NodeRef),
    Publication(NodeRef),
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ClassUnsupported {
    MergedDeclarations(SemanticSymbolId),
    NestedDeclaration(NodeRef),
    DeclarationModifiers(NodeRef),
    Generic(NodeRef),
    Heritage(NodeRef),
    ClassExpression(NodeRef),
    Member { node: NodeRef, kind: SyntaxKind },
    PropertyInitializer(NodeRef),
    MissingPropertyType(NodeRef),
    PropertyType { node: NodeRef, kind: SyntaxKind },
    PropertyName { node: NodeRef, kind: SyntaxKind },
    PropertyModifiers(NodeRef),
    StaticDefiniteAssignment(NodeRef),
    ReservedStaticProperty(NodeRef),
    DuplicateProperty(NodeRef),
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ClassError {
    Unsupported(ClassUnsupported),
    Invariant(ClassInvariant),
    DeclaredType(DeclaredTypeError),
}

impl From<DeclaredTypeError> for ClassError {
    fn from(error: DeclaredTypeError) -> Self {
        Self::DeclaredType(error)
    }
}

impl std::fmt::Display for ClassError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Unsupported(error) => write!(formatter, "class shell is unsupported: {error:?}"),
            Self::Invariant(error) => write!(formatter, "class shell invariant failed: {error:?}"),
            Self::DeclaredType(error) => write!(formatter, "{error}"),
        }
    }
}

impl std::error::Error for ClassError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::DeclaredType(error) => Some(error),
            Self::Unsupported(_) | Self::Invariant(_) => None,
        }
    }
}

impl ClassError {
    #[must_use]
    pub const fn node(self) -> Option<NodeRef> {
        match self {
            Self::Unsupported(unsupported) => Some(match unsupported {
                ClassUnsupported::MergedDeclarations(_) => return None,
                ClassUnsupported::NestedDeclaration(node)
                | ClassUnsupported::DeclarationModifiers(node)
                | ClassUnsupported::Generic(node)
                | ClassUnsupported::Heritage(node)
                | ClassUnsupported::ClassExpression(node)
                | ClassUnsupported::PropertyInitializer(node)
                | ClassUnsupported::MissingPropertyType(node)
                | ClassUnsupported::PropertyType { node, .. }
                | ClassUnsupported::PropertyModifiers(node)
                | ClassUnsupported::StaticDefiniteAssignment(node)
                | ClassUnsupported::ReservedStaticProperty(node)
                | ClassUnsupported::DuplicateProperty(node)
                | ClassUnsupported::Member { node, .. }
                | ClassUnsupported::PropertyName { node, .. } => node,
            }),
            Self::Invariant(invariant) => Some(match invariant {
                ClassInvariant::SymbolNotOwned(_)
                | ClassInvariant::InvalidOwnerSymbol(_)
                | ClassInvariant::InvalidPrototype(_)
                | ClassInvariant::InvalidInstanceCache(_)
                | ClassInvariant::InvalidValueCache(_)
                | ClassInvariant::InvalidPropertyValueCache(_)
                | ClassInvariant::InvalidInstanceMembers(_)
                | ClassInvariant::InvalidStaticMembers(_)
                | ClassInvariant::InvalidConstructSignature(_)
                | ClassInvariant::InvalidHeritageCache(_) => return None,
                ClassInvariant::InvalidDeclaration(node)
                | ClassInvariant::InvalidName(node)
                | ClassInvariant::InvalidHeritage(node)
                | ClassInvariant::InvalidProperty(node)
                | ClassInvariant::InvalidPropertySymbol(node)
                | ClassInvariant::InvalidPropertyTypeCache(node)
                | ClassInvariant::InvalidPlan(node)
                | ClassInvariant::BootstrapUnavailable(node)
                | ClassInvariant::Capacity(node)
                | ClassInvariant::Publication(node) => node,
            }),
            Self::DeclaredType(_) => None,
        }
    }
}

const fn invariant(invariant: ClassInvariant) -> ClassError {
    ClassError::Invariant(invariant)
}

const fn unsupported(unsupported: ClassUnsupported) -> ClassError {
    ClassError::Unsupported(unsupported)
}

fn bound_symbol(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    node: NodeRef,
) -> Option<SemanticSymbolId> {
    let raw = host.bound_file(node)?.symbol(node)?;
    let symbol = store.get_merged_symbol(raw)?;
    host.symbol_matches(store, node, symbol).then_some(symbol)
}

fn validate_decorator_function_value(
    store: &CanonicalTypeMapperStore,
    symbol: SemanticSymbolId,
    declaration: NodeRef,
) -> Result<(), ClassError> {
    let value = match store.value_symbol_links(symbol) {
        None => None,
        Some(links) if links == &ValueSymbolLinks::default() => None,
        Some(links) => {
            let Some(value) = links.resolved_type else {
                return Err(invariant(ClassInvariant::InvalidPropertyValueCache(symbol)));
            };
            if links
                != &(ValueSymbolLinks {
                    resolved_type: Some(value),
                    ..ValueSymbolLinks::default()
                })
            {
                return Err(invariant(ClassInvariant::InvalidPropertyValueCache(symbol)));
            }
            Some(value)
        }
    };
    if value != store.source_callable_type_for_owner(symbol) {
        return Err(invariant(ClassInvariant::InvalidPropertyValueCache(symbol)));
    }
    let Some(value) = value else {
        return Ok(());
    };
    if !matches!(
        validate_stored_source_callable(store, value),
        StoredSourceCallableValidation::Valid(_)
    ) {
        return Err(invariant(ClassInvariant::InvalidPropertyValueCache(symbol)));
    }
    let Some(provenance) = store.source_callable_provenance(value) else {
        return Err(invariant(ClassInvariant::InvalidPropertyValueCache(symbol)));
    };
    let Some(signature) = store.signature(provenance.signature) else {
        return Err(invariant(ClassInvariant::InvalidPropertyValueCache(symbol)));
    };
    let Some(any) = store
        .intrinsic_bootstrap()
        .map(|bootstrap| bootstrap.any_type)
    else {
        return Err(invariant(ClassInvariant::BootstrapUnavailable(declaration)));
    };
    if provenance.owner_symbol != symbol
        || provenance.declaration != declaration
        || signature.flags() != SignatureFlags::HAS_REST_PARAMETER
        || signature.parameters().len() != 1
        || signature.min_argument_count() != 0
        || signature.resolved_return_type() != Some(any)
    {
        return Err(invariant(ClassInvariant::InvalidPropertyValueCache(symbol)));
    }
    Ok(())
}

fn validate_decorator_function_signature(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    field: NodeRef,
    declaration: NodeRef,
) -> Result<(), ClassError> {
    let reject = || unsupported(ClassUnsupported::PropertyModifiers(field));
    let record = preflight_node(store, host, declaration)?;
    let NodeData::FunctionDeclaration(function) = &record.data else {
        return Err(reject());
    };
    let Some(modifiers) = function.modifiers.as_ref() else {
        return Err(reject());
    };
    let [modifier] = modifiers.list.nodes.as_slice() else {
        return Err(reject());
    };
    let modifier = NodeRef::new(declaration.arena, declaration.file, *modifier);
    let modifier_record = preflight_node(store, host, modifier)?;
    if record.kind != SyntaxKind::FunctionDeclaration
        || record.flags.0 != 0
        || function.body.is_some()
        || function.type_parameters.is_some()
        || function.facts != 0
        || modifiers.flags.0 != 0
        || modifiers.list.has_trailing_comma
        || modifier_record.kind != SyntaxKind::DeclareKeyword
        || modifier_record.flags.0 != 0
        || modifier_record.parent != Some(declaration.node)
        || !matches!(modifier_record.data, NodeData::Token(_))
        || function.parameters.has_trailing_comma
        || function.parameters.nodes.len() != 1
    {
        return Err(reject());
    }
    let Some(return_type) = function.type_ else {
        return Err(reject());
    };
    let return_type = NodeRef::new(declaration.arena, declaration.file, return_type);
    let return_record = preflight_node(store, host, return_type)?;
    if return_record.kind != SyntaxKind::AnyKeyword
        || return_record.flags.0 != 0
        || return_record.parent != Some(declaration.node)
        || !matches!(return_record.data, NodeData::KeywordTypeNode(_))
    {
        return Err(reject());
    }

    let parameter = NodeRef::new(
        declaration.arena,
        declaration.file,
        function.parameters.nodes[0],
    );
    let parameter_record = preflight_node(store, host, parameter)?;
    let NodeData::ParameterDeclaration(parameter_data) = &parameter_record.data else {
        return Err(reject());
    };
    let Some(rest) = parameter_data.dot_dot_dot_token else {
        return Err(reject());
    };
    let rest = NodeRef::new(parameter.arena, parameter.file, rest);
    let rest_record = preflight_node(store, host, rest)?;
    if parameter_record.kind != SyntaxKind::Parameter
        || parameter_record.flags.0 != 0
        || parameter_record.parent != Some(declaration.node)
        || parameter_data.initializer.is_some()
        || parameter_data.question_token.is_some()
        || parameter_data.modifiers.is_some()
        || parameter_data.facts != 0
        || rest_record.kind != SyntaxKind::DotDotDotToken
        || rest_record.flags.0 != 0
        || rest_record.parent != Some(parameter.node)
        || !matches!(rest_record.data, NodeData::Token(_))
    {
        return Err(reject());
    }
    let Some(type_node) = parameter_data.type_ else {
        return Err(reject());
    };
    let type_node = NodeRef::new(parameter.arena, parameter.file, type_node);
    let type_record = preflight_node(store, host, type_node)?;
    let NodeData::ArrayTypeNode(array) = &type_record.data else {
        return Err(reject());
    };
    let element = NodeRef::new(type_node.arena, type_node.file, array.element_type);
    let element_record = preflight_node(store, host, element)?;
    if type_record.kind != SyntaxKind::ArrayType
        || type_record.flags.0 != 0
        || type_record.parent != Some(parameter.node)
        || element_record.kind != SyntaxKind::AnyKeyword
        || element_record.flags.0 != 0
        || element_record.parent != Some(type_node.node)
        || !matches!(element_record.data, NodeData::KeywordTypeNode(_))
    {
        return Err(reject());
    }
    Ok(())
}

fn authenticate_class_property_decorator(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    field: NodeRef,
    name: NodeRef,
    decorator: NodeRef,
) -> Result<(), ClassError> {
    let reject = || unsupported(ClassUnsupported::PropertyModifiers(field));
    let field_record = preflight_node(store, host, field)?;
    let NodeData::PropertyDeclaration(property) = &field_record.data else {
        return Err(reject());
    };
    let Some(postfix) = property.postfix_token else {
        return Err(reject());
    };
    let postfix = NodeRef::new(field.arena, field.file, postfix);
    let postfix_record = preflight_node(store, host, postfix)?;
    if property.type_.is_none()
        || property.initializer.is_some()
        || postfix_record.kind != SyntaxKind::ExclamationToken
        || postfix_record.parent != Some(field.node)
    {
        return Err(reject());
    }

    let record = preflight_node(store, host, decorator)?;
    let NodeData::Decorator(data) = &record.data else {
        return Err(reject());
    };
    let name_record = preflight_node(store, host, name)?;
    let expression = NodeRef::new(decorator.arena, decorator.file, data.expression);
    let expression_record = preflight_node(store, host, expression)?;
    let NodeData::Identifier(identifier) = &expression_record.data else {
        return Err(reject());
    };
    if record.kind != SyntaxKind::Decorator
        || record.flags.0 != 0
        || record.parent != Some(field.node)
        || record.range.start < field_record.range.start
        || record.range.end > name_record.range.start
        || data.facts != 0
        || expression_record.kind != SyntaxKind::Identifier
        || expression_record.flags.0 != 0
        || expression_record.parent != Some(decorator.node)
        || expression_record.range.start <= record.range.start
        || expression_record.range.end != record.range.end
        || identifier.flow_node.is_some()
        || identifier.text.is_empty()
    {
        return Err(reject());
    }

    let (arena, bound) = host
        .source(expression)
        .ok_or_else(|| invariant(ClassInvariant::InvalidProperty(field)))?;
    let mut callback_host = host.name_resolver_host(store)?;
    let raw = CanonicalNameResolver::new(arena, bound, store.symbol_store(), &mut callback_host)
        .map_err(|_| invariant(ClassInvariant::InvalidProperty(field)))?
        .resolve(
            Some(CanonicalResolutionLocation::Bound(expression)),
            &identifier.text,
            SymbolFlags::VALUE | SymbolFlags::EXPORT_VALUE,
            None,
            false,
            false,
        )
        .map_err(|_| reject())?
        .ok_or_else(reject)?;
    let symbol = store.get_merged_symbol(raw).ok_or_else(reject)?;
    let symbol_record = store.symbol(symbol).ok_or_else(reject)?;
    let Some([declaration]) = symbol_record.declarations() else {
        return Err(reject());
    };
    let declaration = *declaration;
    let function_record = preflight_node(store, host, declaration)?;
    if raw != symbol
        || symbol_record.flags() != SymbolFlags::FUNCTION
        || symbol_record.check_flags() != CheckFlags::NONE
        || symbol_record.name().as_utf8() != Some(identifier.text.as_str())
        || symbol_record.value_declaration() != Some(declaration)
        || symbol_record.members().is_some()
        || symbol_record.exports().is_some()
        || symbol_record.parent().is_some()
        || symbol_record.export_symbol().is_some()
        || !declaration.is_for(field.arena, field.file)
        || function_record.range.end > record.range.start
        || !host.symbol_matches(store, declaration, symbol)
    {
        return Err(reject());
    }
    if store
        .symbol_node_links(expression)
        .is_some_and(|links| links.resolved_symbol.is_some_and(|cached| cached != symbol))
    {
        return Err(invariant(ClassInvariant::InvalidProperty(field)));
    }
    validate_decorator_function_signature(store, host, field, declaration)?;
    validate_decorator_function_value(store, symbol, declaration)
}

fn class_property_modifiers(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    declaration: NodeRef,
    name: NodeRef,
    modifiers: Option<&ts_ast::ModifierList>,
) -> Result<(ClassPropertySide, bool), ClassError> {
    let Some(modifiers) = modifiers else {
        return Ok((ClassPropertySide::Instance, false));
    };
    let kinds = modifiers
        .list
        .nodes
        .iter()
        .map(|node| {
            let node = NodeRef::new(declaration.arena, declaration.file, *node);
            preflight_node(store, host, node).map(|record| (node, record))
        })
        .collect::<Result<Vec<_>, _>>()?;
    let supported = match kinds
        .iter()
        .map(|(_, record)| record.kind)
        .collect::<Vec<_>>()
        .as_slice()
    {
        [SyntaxKind::Decorator] => {
            authenticate_class_property_decorator(store, host, declaration, name, kinds[0].0)?;
            (ClassPropertySide::Instance, false)
        }
        [SyntaxKind::PublicKeyword] => (ClassPropertySide::Instance, false),
        [SyntaxKind::ReadonlyKeyword] => (ClassPropertySide::Instance, true),
        [SyntaxKind::PublicKeyword, SyntaxKind::ReadonlyKeyword] => {
            (ClassPropertySide::Instance, true)
        }
        [SyntaxKind::StaticKeyword] => (ClassPropertySide::Static, false),
        [SyntaxKind::PublicKeyword, SyntaxKind::StaticKeyword] => {
            (ClassPropertySide::Static, false)
        }
        [SyntaxKind::StaticKeyword, SyntaxKind::ReadonlyKeyword] => {
            (ClassPropertySide::Static, true)
        }
        [
            SyntaxKind::PublicKeyword,
            SyntaxKind::StaticKeyword,
            SyntaxKind::ReadonlyKeyword,
        ] => (ClassPropertySide::Static, true),
        _ => {
            return Err(unsupported(ClassUnsupported::PropertyModifiers(
                declaration,
            )));
        }
    };
    let declaration_record = preflight_node(store, host, declaration)?;
    let name_record = preflight_node(store, host, name)?;
    let mut previous_end = modifiers.list.range.start;
    if modifiers.flags.0 != 0
        || modifiers.list.has_trailing_comma
        || modifiers.list.range.start != declaration_record.range.start
        || modifiers.list.range.end > name_record.range.start
        || kinds.iter().any(|(node, record)| {
            let invalid = record.parent != Some(declaration.node)
                || record.flags.0 != 0
                || !matches!(record.data, NodeData::Token(_) | NodeData::Decorator(_))
                || record.range.start < previous_end
                || record.range.start < modifiers.list.range.start
                || record.range.end > modifiers.list.range.end;
            previous_end = record.range.end;
            !node.is_for(declaration.arena, declaration.file) || invalid
        })
    {
        return Err(invariant(ClassInvariant::InvalidProperty(declaration)));
    }
    Ok(supported)
}

fn class_constructor_visibility(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    declaration: NodeRef,
    parameter_start: ts_core::TextPos,
    modifiers: Option<&ts_ast::ModifierList>,
) -> Result<ClassConstructorVisibility, ClassError> {
    let Some(modifiers) = modifiers else {
        return Ok(ClassConstructorVisibility::Public);
    };
    let [modifier] = modifiers.list.nodes.as_slice() else {
        return Err(unsupported(ClassUnsupported::Member {
            node: declaration,
            kind: SyntaxKind::Constructor,
        }));
    };
    let modifier = NodeRef::new(declaration.arena, declaration.file, *modifier);
    let record = preflight_node(store, host, modifier)?;
    let visibility = match record.kind {
        SyntaxKind::PublicKeyword => ClassConstructorVisibility::Public,
        SyntaxKind::ProtectedKeyword => ClassConstructorVisibility::Protected,
        SyntaxKind::PrivateKeyword => ClassConstructorVisibility::Private,
        _ => {
            return Err(unsupported(ClassUnsupported::Member {
                node: declaration,
                kind: SyntaxKind::Constructor,
            }));
        }
    };
    let declaration_record = preflight_node(store, host, declaration)?;
    if modifiers.flags.0 != 0
        || modifiers.list.has_trailing_comma
        || modifiers.list.range.start != declaration_record.range.start
        || modifiers.list.range.end > parameter_start
        || record.parent != Some(declaration.node)
        || record.flags.0 != 0
        || !matches!(record.data, NodeData::Token(_))
        || record.range.start < modifiers.list.range.start
        || record.range.end > modifiers.list.range.end
    {
        return Err(invariant(ClassInvariant::InvalidProperty(declaration)));
    }
    Ok(visibility)
}

fn plan_constructor(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    owner: SemanticSymbolId,
    declaration: NodeRef,
    instance_members: Option<SymbolTableId>,
) -> Result<ClassConstructorPlan, ClassError> {
    let record = preflight_node(store, host, declaration)?;
    let NodeData::ConstructorDeclaration(constructor) = &record.data else {
        return Err(invariant(ClassInvariant::InvalidProperty(declaration)));
    };
    if record.kind != SyntaxKind::Constructor
        || record.flags.0 != 0
        || constructor.asterisk_token.is_some()
        || constructor.end_flow_node.is_some()
        || constructor.full_signature.is_some()
        || constructor.next_container.is_some()
        || constructor.return_flow_node.is_some()
        || constructor.symbol.is_some()
        || constructor.type_.is_some()
        || constructor.type_parameters.is_some()
        || constructor.facts != 0
    {
        return Err(invariant(ClassInvariant::InvalidProperty(declaration)));
    }
    if !constructor.parameters.nodes.is_empty() || constructor.parameters.has_trailing_comma {
        return Err(unsupported(ClassUnsupported::Member {
            node: declaration,
            kind: SyntaxKind::Constructor,
        }));
    }
    let body = constructor
        .body
        .map(|body| NodeRef::new(declaration.arena, declaration.file, body))
        .ok_or_else(|| {
            unsupported(ClassUnsupported::Member {
                node: declaration,
                kind: SyntaxKind::Constructor,
            })
        })?;
    let body_record = preflight_node(store, host, body)?;
    let NodeData::Block(block) = &body_record.data else {
        return Err(invariant(ClassInvariant::InvalidProperty(declaration)));
    };
    if body_record.kind != SyntaxKind::Block
        || body_record.parent != Some(declaration.node)
        || body_record.flags.0 != 0
        || body_record.range.start < constructor.parameters.range.end
        || body_record.range.end != record.range.end
        || block.facts != 0
        || block.statements.has_trailing_comma
    {
        return Err(invariant(ClassInvariant::InvalidProperty(declaration)));
    }
    if !block.statements.nodes.is_empty() {
        return Err(unsupported(ClassUnsupported::Member {
            node: declaration,
            kind: SyntaxKind::Constructor,
        }));
    }

    let visibility = class_constructor_visibility(
        store,
        host,
        declaration,
        constructor.parameters.range.start,
        constructor.modifiers.as_ref(),
    )?;
    let symbol = bound_symbol(store, host, declaration)
        .ok_or_else(|| invariant(ClassInvariant::InvalidConstructSignature(owner)))?;
    let symbol_record = store
        .symbol(symbol)
        .ok_or_else(|| invariant(ClassInvariant::InvalidConstructSignature(owner)))?;
    let table = instance_members.and_then(|members| store.symbol_table(members));
    if symbol_record.flags() != SymbolFlags::CONSTRUCTOR
        || symbol_record.check_flags() != CheckFlags::NONE
        || symbol_record.name() != InternalSymbolName::Constructor.as_ref()
        || symbol_record.declarations() != Some(&[declaration])
        || symbol_record.value_declaration().is_some()
        || symbol_record.members().is_some()
        || symbol_record.exports().is_some()
        || symbol_record.parent() != Some(owner)
        || symbol_record.export_symbol().is_some()
        || store.get_merged_symbol(symbol) != Some(symbol)
        || table.and_then(|table| table.get(InternalSymbolName::Constructor.as_ref()))
            != Some(symbol)
    {
        return Err(invariant(ClassInvariant::InvalidConstructSignature(owner)));
    }
    if let Some(links) = store.signature_links(declaration)
        && links != &SignatureLinks::default()
    {
        let ResolvedSignatureState::Resolved(signature) = links.resolved_signature else {
            return Err(invariant(ClassInvariant::InvalidConstructSignature(owner)));
        };
        let Some(instance_type) = store
            .declared_type_links(owner)
            .and_then(|links| links.declared_type)
        else {
            return Err(invariant(ClassInvariant::InvalidConstructSignature(owner)));
        };
        if links
            != &(SignatureLinks {
                resolved_signature: ResolvedSignatureState::Resolved(signature),
                ..SignatureLinks::default()
            })
            || !exact_construct_signature(store, signature, instance_type, Some(declaration))
        {
            return Err(invariant(ClassInvariant::InvalidConstructSignature(owner)));
        }
    }

    Ok(ClassConstructorPlan {
        declaration,
        symbol,
        visibility,
    })
}

fn plan_method(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    owner: SemanticSymbolId,
    declaration: NodeRef,
    instance_members: Option<SymbolTableId>,
    static_members: SymbolTableId,
) -> Result<ClassMethodPlan, ClassError> {
    let record = preflight_node(store, host, declaration)?;
    let NodeData::MethodDeclaration(method) = &record.data else {
        return Err(invariant(ClassInvariant::InvalidProperty(declaration)));
    };
    if record.kind != SyntaxKind::MethodDeclaration
        || record.flags.0 != 0
        || method.asterisk_token.is_some()
        || method.end_flow_node.is_some()
        || method.flow_node.is_some()
        || method.full_signature.is_some()
        || method.next_container.is_some()
        || method.postfix_token.is_some()
        || method.symbol.is_some()
        || method.type_parameters.is_some()
        || method.facts != 0
    {
        return Err(unsupported(ClassUnsupported::Member {
            node: declaration,
            kind: SyntaxKind::MethodDeclaration,
        }));
    }
    if !method.parameters.nodes.is_empty() || method.parameters.has_trailing_comma {
        return Err(unsupported(ClassUnsupported::Member {
            node: declaration,
            kind: SyntaxKind::MethodDeclaration,
        }));
    }
    let name_node = NodeRef::new(declaration.arena, declaration.file, method.name);
    let name_record = preflight_node(store, host, name_node)?;
    let NodeData::Identifier(identifier) = &name_record.data else {
        return Err(unsupported(ClassUnsupported::PropertyName {
            node: name_node,
            kind: name_record.kind,
        }));
    };
    if name_record.kind != SyntaxKind::Identifier
        || name_record.parent != Some(declaration.node)
        || name_record.range.start < record.range.start
        || name_record.range.end > method.parameters.range.start
    {
        return Err(invariant(ClassInvariant::InvalidName(name_node)));
    }
    let (side, readonly) = class_property_modifiers(
        store,
        host,
        declaration,
        name_node,
        method.modifiers.as_ref(),
    )?;
    if readonly
        || side == ClassPropertySide::Static
            && matches!(
                identifier.text.as_str(),
                "prototype" | "name" | "length" | "caller" | "arguments"
            )
    {
        return Err(unsupported(ClassUnsupported::Member {
            node: declaration,
            kind: SyntaxKind::MethodDeclaration,
        }));
    }

    let return_type_node = method
        .type_
        .map(|node| NodeRef::new(declaration.arena, declaration.file, node));
    let mut body_start = method.parameters.range.end;
    if let Some(type_node) = return_type_node {
        let type_record = preflight_node(store, host, type_node)?;
        if type_record.parent != Some(declaration.node)
            || type_record.range.start < method.parameters.range.end
            || type_record.range.end > record.range.end
        {
            return Err(invariant(ClassInvariant::InvalidProperty(declaration)));
        }
        body_start = type_record.range.end;
    }
    let body = method
        .body
        .map(|node| NodeRef::new(declaration.arena, declaration.file, node))
        .ok_or_else(|| {
            unsupported(ClassUnsupported::Member {
                node: declaration,
                kind: SyntaxKind::MethodDeclaration,
            })
        })?;
    let body_record = preflight_node(store, host, body)?;
    let NodeData::Block(block) = &body_record.data else {
        return Err(invariant(ClassInvariant::InvalidProperty(declaration)));
    };
    if body_record.kind != SyntaxKind::Block
        || body_record.parent != Some(declaration.node)
        || body_record.flags.0 != 0
        || body_record.range.start < body_start
        || body_record.range.end != record.range.end
        || block.facts != 0
        || block.statements.has_trailing_comma
    {
        return Err(invariant(ClassInvariant::InvalidProperty(declaration)));
    }
    if !block.statements.nodes.is_empty() {
        return Err(unsupported(ClassUnsupported::Member {
            node: declaration,
            kind: SyntaxKind::MethodDeclaration,
        }));
    }

    let symbol = bound_symbol(store, host, declaration)
        .ok_or_else(|| invariant(ClassInvariant::InvalidPropertySymbol(declaration)))?;
    let symbol_record = store
        .symbol(symbol)
        .ok_or_else(|| invariant(ClassInvariant::InvalidPropertySymbol(declaration)))?;
    let table = match side {
        ClassPropertySide::Instance => instance_members,
        ClassPropertySide::Static => Some(static_members),
    }
    .and_then(|table| store.symbol_table(table));
    if symbol_record.flags() != SymbolFlags::METHOD
        || symbol_record.check_flags() != CheckFlags::NONE
        || symbol_record.name().as_utf8() != Some(identifier.text.as_str())
        || symbol_record.declarations() != Some(&[declaration])
        || symbol_record.value_declaration() != Some(declaration)
        || symbol_record.members().is_some()
        || symbol_record.exports().is_some()
        || symbol_record.parent() != Some(owner)
        || symbol_record.export_symbol().is_some()
        || store.get_merged_symbol(symbol) != Some(symbol)
        || table.and_then(|table| table.get_source(&identifier.text)) != Some(symbol)
    {
        return Err(invariant(ClassInvariant::InvalidPropertySymbol(
            declaration,
        )));
    }

    Ok(ClassMethodPlan {
        declaration,
        symbol,
        name_node,
        name: identifier.text.clone(),
        side,
        return_type_node,
    })
}

fn plan_class_index_signature(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    owner: SemanticSymbolId,
    owner_declaration: NodeRef,
    declaration: NodeRef,
    instance_members: Option<SymbolTableId>,
) -> Result<ClassIndexSignaturePlan, ClassError> {
    let unsupported_index = || {
        unsupported(ClassUnsupported::Member {
            node: declaration,
            kind: SyntaxKind::IndexSignature,
        })
    };
    let record = preflight_node(store, host, declaration)?;
    let NodeData::IndexSignatureDeclaration(index) = &record.data else {
        return Err(unsupported_index());
    };
    if record.kind != SyntaxKind::IndexSignature
        || record.parent != Some(owner_declaration.node)
        || record.flags.0 != 0
        || index.full_signature.is_some()
        || index.next_container.is_some()
        || index.symbol.is_some()
        || index.type_parameters.is_some()
        || index.modifiers.is_some()
        || index.parameters.has_trailing_comma
        || index.parameters.nodes.len() != 1
        || index.parameters.range.start < record.range.start
        || index.parameters.range.end > record.range.end
    {
        return Err(unsupported_index());
    }

    let parameter = NodeRef::new(
        declaration.arena,
        declaration.file,
        index.parameters.nodes[0],
    );
    let parameter_record = preflight_node(store, host, parameter)?;
    let NodeData::ParameterDeclaration(parameter_data) = &parameter_record.data else {
        return Err(unsupported_index());
    };
    if parameter_record.kind != SyntaxKind::Parameter
        || parameter_record.parent != Some(declaration.node)
        || parameter_record.flags.0 != 0
        || parameter_record.range.start < index.parameters.range.start
        || parameter_record.range.end > index.parameters.range.end
        || parameter_data.dot_dot_dot_token.is_some()
        || parameter_data.initializer.is_some()
        || parameter_data.question_token.is_some()
        || parameter_data.symbol.is_some()
        || parameter_data.facts != 0
        || parameter_data.modifiers.is_some()
    {
        return Err(unsupported_index());
    }
    let name = NodeRef::new(parameter.arena, parameter.file, parameter_data.name);
    let name_record = preflight_node(store, host, name)?;
    let NodeData::Identifier(identifier) = &name_record.data else {
        return Err(unsupported_index());
    };
    if name_record.kind != SyntaxKind::Identifier
        || name_record.parent != Some(parameter.node)
        || name_record.range.start < parameter_record.range.start
        || name_record.range.end > parameter_record.range.end
        || identifier.text.is_empty()
        || identifier.text == "this"
    {
        return Err(unsupported_index());
    }

    let Some(key_type) = parameter_data.type_ else {
        return Err(unsupported_index());
    };
    let key_type_node = NodeRef::new(parameter.arena, parameter.file, key_type);
    let key_record = preflight_node(store, host, key_type_node)?;
    if key_record.kind != SyntaxKind::StringKeyword
        || !matches!(key_record.data, NodeData::KeywordTypeNode(_))
        || key_record.flags.0 != 0
        || key_record.parent != Some(parameter.node)
        || key_record.range.start < name_record.range.end
        || key_record.range.end > parameter_record.range.end
    {
        return Err(unsupported_index());
    }

    let value_type_node = NodeRef::new(declaration.arena, declaration.file, index.type_);
    let value_record = preflight_node(store, host, value_type_node)?;
    if value_record.kind != SyntaxKind::NumberKeyword
        || !matches!(value_record.data, NodeData::KeywordTypeNode(_))
        || value_record.flags.0 != 0
        || value_record.parent != Some(declaration.node)
        || value_record.range.start < index.parameters.range.end
        || value_record.range.end > record.range.end
    {
        return Err(unsupported_index());
    }

    let Some(bound) = host.bound_file(declaration) else {
        return Err(invariant(ClassInvariant::InvalidPropertySymbol(
            declaration,
        )));
    };
    let symbol = bound_symbol(store, host, declaration)
        .ok_or_else(|| invariant(ClassInvariant::InvalidPropertySymbol(declaration)))?;
    let symbol_record = store
        .symbol(symbol)
        .ok_or_else(|| invariant(ClassInvariant::InvalidPropertySymbol(declaration)))?;
    let member_table = instance_members.and_then(|table| store.symbol_table(table));
    if symbol_record.flags() != SymbolFlags::SIGNATURE
        || symbol_record.check_flags() != CheckFlags::NONE
        || symbol_record.name() != InternalSymbolName::Index.as_ref()
        || symbol_record.declarations() != Some(&[declaration])
        || symbol_record.value_declaration().is_some()
        || symbol_record.members().is_some()
        || symbol_record.exports().is_some()
        || symbol_record.parent() != Some(owner)
        || symbol_record.export_symbol().is_some()
        || member_table.and_then(|table| table.get(InternalSymbolName::Index.as_ref()))
            != Some(symbol)
    {
        return Err(invariant(ClassInvariant::InvalidPropertySymbol(
            declaration,
        )));
    }

    let parameter_symbol = bound_symbol(store, host, parameter)
        .ok_or_else(|| invariant(ClassInvariant::InvalidPropertySymbol(parameter)))?;
    let parameter_symbol_record = store
        .symbol(parameter_symbol)
        .ok_or_else(|| invariant(ClassInvariant::InvalidPropertySymbol(parameter)))?;
    let locals = bound
        .locals(declaration)
        .and_then(|locals| store.symbol_table(locals));
    if parameter_symbol_record.flags() != SymbolFlags::FUNCTION_SCOPED_VARIABLE
        || parameter_symbol_record.check_flags() != CheckFlags::NONE
        || parameter_symbol_record.name().as_utf8() != Some(identifier.text.as_str())
        || parameter_symbol_record.declarations() != Some(&[parameter])
        || parameter_symbol_record.value_declaration() != Some(parameter)
        || parameter_symbol_record.members().is_some()
        || parameter_symbol_record.exports().is_some()
        || parameter_symbol_record.parent().is_some()
        || parameter_symbol_record.export_symbol().is_some()
        || locals.is_none_or(|locals| {
            locals.len() != 1 || locals.get_source(&identifier.text) != Some(parameter_symbol)
        })
    {
        return Err(invariant(ClassInvariant::InvalidPropertySymbol(parameter)));
    }

    Ok(ClassIndexSignaturePlan {
        declaration,
        symbol,
        key_type_node,
        value_type_node,
    })
}

fn plan_property(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    owner: SemanticSymbolId,
    member: NodeRef,
    instance_members: Option<SymbolTableId>,
    static_members: SymbolTableId,
) -> Result<ClassPropertyPlan, ClassError> {
    let record = preflight_node(store, host, member)?;
    let NodeData::PropertyDeclaration(property) = &record.data else {
        return Err(unsupported(ClassUnsupported::Member {
            node: member,
            kind: record.kind,
        }));
    };
    if property.initializer.is_some() {
        return Err(unsupported(ClassUnsupported::PropertyInitializer(member)));
    }
    let Some(type_node) = property.type_ else {
        return Err(unsupported(ClassUnsupported::MissingPropertyType(member)));
    };
    if property.symbol.is_some()
        || property.facts != 0
        || record.flags.0 & (NODE_FLAG_JSDOC | NODE_FLAG_HAS_ERROR) != 0
    {
        return Err(invariant(ClassInvariant::InvalidProperty(member)));
    }

    let name = NodeRef::new(member.arena, member.file, property.name);
    let name_record = preflight_node(store, host, name)?;
    let NodeData::Identifier(identifier) = &name_record.data else {
        return Err(unsupported(ClassUnsupported::PropertyName {
            node: name,
            kind: name_record.kind,
        }));
    };
    if name_record.kind != SyntaxKind::Identifier
        || name_record.parent != Some(member.node)
        || name_record.range.start < record.range.start
        || name_record.range.end > record.range.end
    {
        return Err(invariant(ClassInvariant::InvalidName(name)));
    }
    let (side, readonly) =
        class_property_modifiers(store, host, member, name, property.modifiers.as_ref())?;

    let type_node = NodeRef::new(member.arena, member.file, type_node);
    let type_record = preflight_node(store, host, type_node)?;
    if type_record.parent != Some(member.node)
        || type_record.range.start < name_record.range.end
        || type_record.range.end > record.range.end
    {
        return Err(invariant(ClassInvariant::InvalidProperty(member)));
    }

    let (optional, definite) = match property.postfix_token {
        None => (false, false),
        Some(token) => {
            let token = NodeRef::new(member.arena, member.file, token);
            let token_record = preflight_node(store, host, token)?;
            if token_record.parent != Some(member.node)
                || token_record.flags.0 != 0
                || !matches!(token_record.data, NodeData::Token(_))
                || token_record.range.start < name_record.range.end
                || token_record.range.end > type_record.range.start
            {
                return Err(invariant(ClassInvariant::InvalidProperty(member)));
            }
            match token_record.kind {
                SyntaxKind::QuestionToken => (true, false),
                SyntaxKind::ExclamationToken => (false, true),
                _ => return Err(invariant(ClassInvariant::InvalidProperty(member))),
            }
        }
    };
    if side == ClassPropertySide::Static && definite {
        return Err(unsupported(ClassUnsupported::StaticDefiniteAssignment(
            member,
        )));
    }
    if side == ClassPropertySide::Static
        && matches!(
            identifier.text.as_str(),
            "prototype" | "name" | "length" | "caller" | "arguments"
        )
    {
        return Err(unsupported(ClassUnsupported::ReservedStaticProperty(
            member,
        )));
    }

    let symbol = bound_symbol(store, host, member)
        .ok_or_else(|| invariant(ClassInvariant::InvalidPropertySymbol(member)))?;
    let symbol_record = store
        .symbol(symbol)
        .ok_or_else(|| invariant(ClassInvariant::InvalidPropertySymbol(member)))?;
    let expected_flags = SymbolFlags::PROPERTY
        | if optional {
            SymbolFlags::OPTIONAL
        } else {
            SymbolFlags::NONE
        };
    let expected_check_flags = if readonly {
        CheckFlags::READONLY
    } else {
        CheckFlags::NONE
    };
    let table = match side {
        ClassPropertySide::Instance => instance_members,
        ClassPropertySide::Static => Some(static_members),
    }
    .and_then(|table| store.symbol_table(table));
    if symbol_record.flags() != expected_flags
        || (symbol_record.check_flags() != CheckFlags::NONE
            && symbol_record.check_flags() != expected_check_flags)
        || symbol_record.name().as_utf8() != Some(identifier.text.as_str())
        || symbol_record.declarations() != Some(&[member])
        || symbol_record.value_declaration() != Some(member)
        || symbol_record.members().is_some()
        || symbol_record.exports().is_some()
        || symbol_record.parent() != Some(owner)
        || symbol_record.export_symbol().is_some()
        || store.get_merged_symbol(symbol) != Some(symbol)
        || table.and_then(|table| table.get_source(&identifier.text)) != Some(symbol)
    {
        return Err(invariant(ClassInvariant::InvalidPropertySymbol(member)));
    }

    Ok(ClassPropertyPlan {
        declaration: member,
        symbol,
        name_node: name,
        type_node,
        name: identifier.text.clone(),
        side,
        optional,
        definite,
        readonly,
    })
}

fn validate_prototype(
    store: &CanonicalTypeMapperStore,
    owner: SemanticSymbolId,
    exports: SymbolTableId,
) -> Result<(), ClassError> {
    let table = store
        .symbol_table(exports)
        .ok_or_else(|| invariant(ClassInvariant::InvalidPrototype(owner)))?;
    let prototype = table
        .get_source(PROTOTYPE_NAME)
        .ok_or_else(|| invariant(ClassInvariant::InvalidPrototype(owner)))?;
    let record = store
        .symbol(prototype)
        .ok_or_else(|| invariant(ClassInvariant::InvalidPrototype(owner)))?;
    if record.flags() != SymbolFlags::PROPERTY | SymbolFlags::PROTOTYPE
        || record.check_flags() != CheckFlags::NONE
        || record.name().as_utf8() != Some(PROTOTYPE_NAME)
        || record.declarations().is_some()
        || record.value_declaration().is_some()
        || record.members().is_some()
        || record.exports().is_some()
        || record.parent() != Some(owner)
        || record.export_symbol().is_some()
        || store.get_merged_symbol(prototype) != Some(prototype)
    {
        return Err(invariant(ClassInvariant::InvalidPrototype(owner)));
    }
    Ok(())
}

fn reject_reserved_static_prototype(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    declaration: NodeRef,
    members: &ts_ast::NodeList,
) -> Result<(), ClassError> {
    for member in &members.nodes {
        let member = NodeRef::new(declaration.arena, declaration.file, *member);
        let record = preflight_node(store, host, member)?;
        let NodeData::PropertyDeclaration(property) = &record.data else {
            continue;
        };
        let name = NodeRef::new(member.arena, member.file, property.name);
        let name_record = preflight_node(store, host, name)?;
        let NodeData::Identifier(identifier) = &name_record.data else {
            continue;
        };
        if identifier.text != PROTOTYPE_NAME {
            continue;
        }
        if record.parent != Some(declaration.node) || name_record.parent != Some(member.node) {
            return Err(invariant(ClassInvariant::InvalidProperty(member)));
        }
        let (side, _) =
            class_property_modifiers(store, host, member, name, property.modifiers.as_ref())?;
        if side == ClassPropertySide::Static {
            return Err(unsupported(ClassUnsupported::ReservedStaticProperty(
                member,
            )));
        }
    }
    Ok(())
}

fn plan_direct_class_base(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    declaration: NodeRef,
    owner: SemanticSymbolId,
    clauses: &ts_ast::NodeList,
) -> Result<DirectClassBasePlan, ClassError> {
    let [clause_id] = clauses.nodes.as_slice() else {
        return Err(unsupported(ClassUnsupported::Heritage(declaration)));
    };
    let clause = NodeRef::new(declaration.arena, declaration.file, *clause_id);
    let clause_record = preflight_node(store, host, clause)?;
    let NodeData::HeritageClause(clause_data) = &clause_record.data else {
        return Err(invariant(ClassInvariant::InvalidHeritage(clause)));
    };
    if clauses.has_trailing_comma
        || clause_record.kind != SyntaxKind::HeritageClause
        || clause_record.parent != Some(declaration.node)
        || clause_record.flags.0 != 0
        || clause_data.facts != 0
        || clause_data.types.has_trailing_comma
    {
        return Err(invariant(ClassInvariant::InvalidHeritage(clause)));
    }
    if clause_data.token != SyntaxKind::ExtendsKeyword {
        return Err(unsupported(ClassUnsupported::Heritage(clause)));
    }
    let [base_id] = clause_data.types.nodes.as_slice() else {
        return Err(unsupported(ClassUnsupported::Heritage(clause)));
    };
    let node = NodeRef::new(declaration.arena, declaration.file, *base_id);
    let node_record = preflight_node(store, host, node)?;
    let NodeData::ExpressionWithTypeArguments(base) = &node_record.data else {
        return Err(unsupported(ClassUnsupported::Heritage(node)));
    };
    if node_record.kind != SyntaxKind::ExpressionWithTypeArguments
        || node_record.parent != Some(clause.node)
        || node_record.flags.0 != 0
        || node_record.range.start < clause_data.types.range.start
        || node_record.range.end > clause_data.types.range.end
        || base.facts != 0
    {
        return Err(invariant(ClassInvariant::InvalidHeritage(node)));
    }
    if base.type_arguments.is_some() {
        return Err(unsupported(ClassUnsupported::Heritage(node)));
    }

    let expression = NodeRef::new(declaration.arena, declaration.file, base.expression);
    let expression_record = preflight_node(store, host, expression)?;
    let NodeData::Identifier(identifier) = &expression_record.data else {
        return Err(unsupported(ClassUnsupported::Heritage(expression)));
    };
    if expression_record.kind != SyntaxKind::Identifier
        || expression_record.parent != Some(node.node)
        || expression_record.flags.0 != 0
        || identifier.flow_node.is_some()
        || expression_record.range.start < node_record.range.start
        || expression_record.range.end > node_record.range.end
    {
        return Err(invariant(ClassInvariant::InvalidHeritage(expression)));
    }

    let (arena, bound) = host
        .source(expression)
        .ok_or_else(|| invariant(ClassInvariant::InvalidHeritage(expression)))?;
    let mut callback_host = host.name_resolver_host(store)?;
    let raw = CanonicalNameResolver::new(arena, bound, store.symbol_store(), &mut callback_host)
        .map_err(|_| invariant(ClassInvariant::InvalidHeritage(expression)))?
        .resolve(
            Some(CanonicalResolutionLocation::Bound(expression)),
            &identifier.text,
            SymbolFlags::VALUE | SymbolFlags::EXPORT_VALUE,
            None,
            false,
            false,
        )
        .map_err(|_| unsupported(ClassUnsupported::Heritage(expression)))?
        .ok_or_else(|| unsupported(ClassUnsupported::Heritage(expression)))?;
    let symbol = store
        .get_merged_symbol(raw)
        .ok_or_else(|| invariant(ClassInvariant::InvalidHeritage(expression)))?;
    if symbol == owner
        || store
            .symbol(symbol)
            .is_none_or(|record| record.flags() != SymbolFlags::CLASS)
    {
        return Err(unsupported(ClassUnsupported::Heritage(expression)));
    }
    Ok(DirectClassBasePlan {
        clause,
        node,
        expression,
        symbol,
    })
}

fn plan_empty_class_implementations(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    declaration: NodeRef,
    owner: SemanticSymbolId,
    clauses: &ts_ast::NodeList,
) -> Result<Vec<DirectClassImplementationPlan>, ClassError> {
    let [clause_id] = clauses.nodes.as_slice() else {
        return Err(unsupported(ClassUnsupported::Heritage(declaration)));
    };
    let clause = NodeRef::new(declaration.arena, declaration.file, *clause_id);
    let clause_record = preflight_node(store, host, clause)?;
    let NodeData::HeritageClause(data) = &clause_record.data else {
        return Err(invariant(ClassInvariant::InvalidHeritage(clause)));
    };
    if clauses.has_trailing_comma
        || clause_record.kind != SyntaxKind::HeritageClause
        || clause_record.parent != Some(declaration.node)
        || clause_record.flags.0 != 0
        || data.facts != 0
        || data.token != SyntaxKind::ImplementsKeyword
        || data.types.has_trailing_comma
        || data.types.nodes.is_empty()
    {
        return Err(unsupported(ClassUnsupported::Heritage(clause)));
    }

    let declaration_record = preflight_node(store, host, declaration)?;
    let mut implementations = Vec::new();
    implementations
        .try_reserve_exact(data.types.nodes.len())
        .map_err(|_| invariant(ClassInvariant::Capacity(declaration)))?;
    let mut previous_end = data.types.range.start;
    for implementation in &data.types.nodes {
        let node = NodeRef::new(declaration.arena, declaration.file, *implementation);
        let record = preflight_node(store, host, node)?;
        let NodeData::ExpressionWithTypeArguments(target) = &record.data else {
            return Err(unsupported(ClassUnsupported::Heritage(node)));
        };
        if record.kind != SyntaxKind::ExpressionWithTypeArguments
            || record.parent != Some(clause.node)
            || record.flags.0 != 0
            || record.range.start < previous_end
            || record.range.end > data.types.range.end
            || target.facts != 0
            || target.type_arguments.is_some()
        {
            return Err(unsupported(ClassUnsupported::Heritage(node)));
        }
        previous_end = record.range.end;

        let expression = NodeRef::new(declaration.arena, declaration.file, target.expression);
        let expression_record = preflight_node(store, host, expression)?;
        let NodeData::Identifier(identifier) = &expression_record.data else {
            return Err(unsupported(ClassUnsupported::Heritage(expression)));
        };
        if expression_record.kind != SyntaxKind::Identifier
            || expression_record.parent != Some(node.node)
            || expression_record.flags.0 != 0
            || identifier.flow_node.is_some()
            || expression_record.range.start < record.range.start
            || expression_record.range.end > record.range.end
        {
            return Err(invariant(ClassInvariant::InvalidHeritage(expression)));
        }

        let (arena, bound) = host
            .source(expression)
            .ok_or_else(|| invariant(ClassInvariant::InvalidHeritage(expression)))?;
        let mut callback_host = host.name_resolver_host(store)?;
        let raw =
            CanonicalNameResolver::new(arena, bound, store.symbol_store(), &mut callback_host)
                .map_err(|_| invariant(ClassInvariant::InvalidHeritage(expression)))?
                .resolve(
                    Some(CanonicalResolutionLocation::Bound(expression)),
                    &identifier.text,
                    SymbolFlags::TYPE,
                    None,
                    false,
                    false,
                )
                .map_err(|_| unsupported(ClassUnsupported::Heritage(expression)))?
                .ok_or_else(|| unsupported(ClassUnsupported::Heritage(expression)))?;
        let symbol = store
            .get_merged_symbol(raw)
            .ok_or_else(|| invariant(ClassInvariant::InvalidHeritage(expression)))?;
        let target_record = store
            .symbol(symbol)
            .ok_or_else(|| invariant(ClassInvariant::InvalidHeritage(expression)))?;
        let Some([target_declaration]) = target_record.declarations() else {
            return Err(unsupported(ClassUnsupported::Heritage(expression)));
        };
        let target_declaration = *target_declaration;
        let target_syntax = preflight_node(store, host, target_declaration)?;
        let valid_target = match &target_syntax.data {
            NodeData::ClassDeclaration(class) => {
                target_record.flags() == SymbolFlags::CLASS
                    && class.type_parameters.is_none()
                    && class.heritage_clauses.is_none()
            }
            NodeData::InterfaceDeclaration(interface) => {
                target_record.flags() == SymbolFlags::INTERFACE
                    && interface.type_parameters.is_none()
                    && interface.heritage_clauses.is_none()
            }
            _ => false,
        };
        let no_instance_members = target_record.members().is_none_or(|members| {
            store.symbol_table(members).is_some_and(|table| {
                table
                    .iter()
                    .all(|(name, _)| name == InternalSymbolName::Constructor.as_ref())
            })
        });
        if symbol == owner
            || !target_declaration.is_for(declaration.arena, declaration.file)
            || target_syntax.range.end > declaration_record.range.start
            || !valid_target
            || !no_instance_members
            || implementations
                .iter()
                .any(|current: &DirectClassImplementationPlan| current.symbol == symbol)
        {
            return Err(unsupported(ClassUnsupported::Heritage(expression)));
        }
        implementations.push(DirectClassImplementationPlan {
            clause,
            node,
            expression,
            symbol,
        });
    }
    Ok(implementations)
}

/// Produces the opaque syntax/binder proof consumed by the class shell
/// executor and the root annotation adapter.
fn plan_class_declaration(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    symbol: SemanticSymbolId,
    allow_direct_base: bool,
) -> Result<ClassDeclarationPlan, ClassError> {
    let merged = store
        .get_merged_symbol(symbol)
        .ok_or_else(|| invariant(ClassInvariant::SymbolNotOwned(symbol)))?;
    if merged != symbol {
        return Err(unsupported(ClassUnsupported::MergedDeclarations(symbol)));
    }
    let symbol_record = store
        .symbol(symbol)
        .ok_or_else(|| invariant(ClassInvariant::SymbolNotOwned(symbol)))?;
    if symbol_record.flags() != SymbolFlags::CLASS {
        return if symbol_record.flags().contains(SymbolFlags::CLASS) {
            Err(unsupported(ClassUnsupported::MergedDeclarations(symbol)))
        } else {
            Err(invariant(ClassInvariant::InvalidOwnerSymbol(symbol)))
        };
    }
    let Some([declaration]) = symbol_record.declarations() else {
        return Err(unsupported(ClassUnsupported::MergedDeclarations(symbol)));
    };
    let declaration = *declaration;
    if symbol_record.check_flags() != CheckFlags::NONE
        || symbol_record.value_declaration() != Some(declaration)
        || symbol_record.parent().is_some()
        || symbol_record.export_symbol().is_some()
    {
        return Err(invariant(ClassInvariant::InvalidOwnerSymbol(symbol)));
    }

    let declaration_record = preflight_node(store, host, declaration)?;
    let class = match &declaration_record.data {
        NodeData::ClassDeclaration(class) => class,
        NodeData::ClassExpression(_) => {
            return Err(unsupported(ClassUnsupported::ClassExpression(declaration)));
        }
        _ => return Err(invariant(ClassInvariant::InvalidDeclaration(declaration))),
    };
    if declaration_record.kind != SyntaxKind::ClassDeclaration
        || declaration_record.flags.0 & (NODE_FLAG_JSDOC | NODE_FLAG_HAS_ERROR) != 0
        || !host.symbol_matches(store, declaration, symbol)
        || class.flow_node.is_some()
        || class.local_symbol.is_some()
        || class.symbol.is_some()
        || class.next_container.is_some()
        || class.facts != 0
        || class.members.has_trailing_comma
        || class.members.range.start < declaration_record.range.start
        || class.members.range.end != declaration_record.range.end
    {
        return Err(invariant(ClassInvariant::InvalidDeclaration(declaration)));
    }
    if class.modifiers.is_some() {
        return Err(unsupported(ClassUnsupported::DeclarationModifiers(
            declaration,
        )));
    }
    if class.type_parameters.is_some() {
        return Err(unsupported(ClassUnsupported::Generic(declaration)));
    }
    let (base, implementations) = match class.heritage_clauses.as_ref() {
        None => (None, Vec::new()),
        Some(clauses) => {
            let implements = clauses.nodes.first().is_some_and(|clause| {
                let clause = NodeRef::new(declaration.arena, declaration.file, *clause);
                host.node(clause).is_some_and(|record| {
                    matches!(
                        &record.data,
                        NodeData::HeritageClause(data) if data.token == SyntaxKind::ImplementsKeyword
                    )
                })
            });
            if implements {
                (
                    None,
                    plan_empty_class_implementations(store, host, declaration, symbol, clauses)?,
                )
            } else if allow_direct_base {
                (
                    Some(plan_direct_class_base(
                        store,
                        host,
                        declaration,
                        symbol,
                        clauses,
                    )?),
                    Vec::new(),
                )
            } else {
                return Err(unsupported(ClassUnsupported::Heritage(declaration)));
            }
        }
    };
    let Some(name) = class.name else {
        return Err(invariant(ClassInvariant::InvalidDeclaration(declaration)));
    };
    let name = NodeRef::new(declaration.arena, declaration.file, name);
    let name_record = preflight_node(store, host, name)?;
    let NodeData::Identifier(identifier) = &name_record.data else {
        return Err(invariant(ClassInvariant::InvalidName(name)));
    };
    if name_record.kind != SyntaxKind::Identifier
        || name_record.parent != Some(declaration.node)
        || name_record.flags.0 != 0
        || name_record.range.start < declaration_record.range.start
        || name_record.range.end > declaration_record.range.end
        || symbol_record.name().as_utf8() != Some(identifier.text.as_str())
    {
        return Err(invariant(ClassInvariant::InvalidName(name)));
    }

    let Some(parent) = declaration_record.parent else {
        return Err(unsupported(ClassUnsupported::NestedDeclaration(
            declaration,
        )));
    };
    let parent = NodeRef::new(declaration.arena, declaration.file, parent);
    let parent_record = preflight_node(store, host, parent)?;
    let NodeData::SourceFile(source) = &parent_record.data else {
        return Err(unsupported(ClassUnsupported::NestedDeclaration(
            declaration,
        )));
    };
    if parent_record.kind != SyntaxKind::SourceFile
        || parent_record.parent.is_some()
        || source
            .statements
            .nodes
            .iter()
            .filter(|node| **node == declaration.node)
            .count()
            != 1
    {
        return Err(invariant(ClassInvariant::InvalidDeclaration(declaration)));
    }

    let instance_members = symbol_record.members();
    let static_members = symbol_record
        .exports()
        .ok_or_else(|| invariant(ClassInvariant::InvalidPrototype(symbol)))?;
    if instance_members.is_some_and(|members| store.symbol_table(members).is_none())
        || store.symbol_table(static_members).is_none()
    {
        return Err(invariant(ClassInvariant::InvalidOwnerSymbol(symbol)));
    }
    reject_reserved_static_prototype(store, host, declaration, &class.members)?;
    validate_prototype(store, symbol, static_members)?;

    let mut instance_properties = Vec::new();
    let mut static_properties = Vec::new();
    let mut properties = Vec::with_capacity(class.members.nodes.len());
    let mut methods = Vec::new();
    let mut instance_methods = Vec::new();
    let mut static_methods = Vec::new();
    let mut instance_names = HashSet::new();
    let mut static_names = HashSet::new();
    let mut constructor = None;
    let mut index = None;
    let mut previous_end = class.members.range.start;
    for member in &class.members.nodes {
        let member = NodeRef::new(declaration.arena, declaration.file, *member);
        let member_record = preflight_node(store, host, member)?;
        if member_record.parent != Some(declaration.node)
            || member_record.range.start < previous_end
            || member_record.range.start < class.members.range.start
            || member_record.range.end > class.members.range.end
        {
            return Err(invariant(ClassInvariant::InvalidProperty(member)));
        }
        previous_end = member_record.range.end;
        if member_record.kind == SyntaxKind::Constructor {
            if base.is_some() || constructor.is_some() {
                return Err(unsupported(ClassUnsupported::Member {
                    node: member,
                    kind: SyntaxKind::Constructor,
                }));
            }
            constructor = Some(plan_constructor(
                store,
                host,
                symbol,
                member,
                instance_members,
            )?);
            continue;
        }
        if member_record.kind == SyntaxKind::IndexSignature {
            if base.is_some() || index.is_some() {
                return Err(unsupported(ClassUnsupported::Member {
                    node: member,
                    kind: SyntaxKind::IndexSignature,
                }));
            }
            index = Some(plan_class_index_signature(
                store,
                host,
                symbol,
                declaration,
                member,
                instance_members,
            )?);
            continue;
        }
        if member_record.kind == SyntaxKind::MethodDeclaration {
            let method = plan_method(
                store,
                host,
                symbol,
                member,
                instance_members,
                static_members,
            )?;
            let names = match method.side {
                ClassPropertySide::Instance => &mut instance_names,
                ClassPropertySide::Static => &mut static_names,
            };
            if !names.insert(method.name.clone()) {
                return Err(unsupported(ClassUnsupported::DuplicateProperty(member)));
            }
            methods.push(method.clone());
            match method.side {
                ClassPropertySide::Instance => instance_methods.push(method),
                ClassPropertySide::Static => static_methods.push(method),
            }
            continue;
        }
        if member_record.kind != SyntaxKind::PropertyDeclaration {
            return Err(unsupported(ClassUnsupported::Member {
                node: member,
                kind: member_record.kind,
            }));
        }
        let property = plan_property(
            store,
            host,
            symbol,
            member,
            instance_members,
            static_members,
        )?;
        let names = match property.side {
            ClassPropertySide::Instance => &mut instance_names,
            ClassPropertySide::Static => &mut static_names,
        };
        if !names.insert(property.name.clone()) {
            return Err(unsupported(ClassUnsupported::DuplicateProperty(member)));
        }
        properties.push(property.clone());
        match property.side {
            ClassPropertySide::Instance => instance_properties.push(property),
            ClassPropertySide::Static => static_properties.push(property),
        }
    }
    if let Some(index) = index
        && (!instance_properties.is_empty() || !instance_methods.is_empty())
    {
        return Err(unsupported(ClassUnsupported::Member {
            node: index.declaration,
            kind: SyntaxKind::IndexSignature,
        }));
    }

    let instance_table = instance_members.and_then(|table| store.symbol_table(table));
    let expected_instance_members = instance_properties
        .len()
        .checked_add(instance_methods.len())
        .and_then(|count| count.checked_add(usize::from(constructor.is_some())))
        .and_then(|count| count.checked_add(usize::from(index.is_some())))
        .ok_or_else(|| invariant(ClassInvariant::Capacity(declaration)))?;
    if instance_members.is_some() == (expected_instance_members == 0)
        || instance_table.is_some_and(|table| table.len() != expected_instance_members)
    {
        return Err(invariant(ClassInvariant::InvalidOwnerSymbol(symbol)));
    }
    let static_table = store
        .symbol_table(static_members)
        .expect("the class export table was validated above");
    let expected_static_members = static_properties
        .len()
        .checked_add(static_methods.len())
        .and_then(|count| count.checked_add(1))
        .ok_or_else(|| invariant(ClassInvariant::Capacity(declaration)))?;
    if static_table.len() != expected_static_members {
        return Err(invariant(ClassInvariant::InvalidOwnerSymbol(symbol)));
    }

    let local_arity =
        preflight_class_or_interface_reference(store, host, symbol, SymbolFlags::CLASS)?;
    if local_arity != 0 {
        return Err(unsupported(ClassUnsupported::Generic(declaration)));
    }
    Ok(ClassDeclarationPlan {
        declaration,
        symbol,
        base,
        implementations,
        constructor,
        index,
        instance_members,
        static_members,
        properties,
        instance_properties,
        static_properties,
        methods,
        instance_methods,
        static_methods,
    })
}

/// Produces the exact no-heritage syntax/binder proof used by source checking
/// and the standalone shell query.
pub(super) fn plan_nongeneric_class(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    symbol: SemanticSymbolId,
) -> Result<ClassDeclarationPlan, ClassError> {
    plan_class_declaration(store, host, symbol, false)
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct ClassMemberPlan {
    class: ClassDeclarationPlan,
    property_types: Vec<TypeId>,
    method_return_types: Vec<TypeId>,
    index_types: Option<(TypeId, TypeId)>,
    uninitialized_instance_properties: Vec<NodeRef>,
}

impl ClassMemberPlan {
    pub(super) const fn declaration(&self) -> NodeRef {
        self.class.declaration
    }

    pub(super) const fn symbol(&self) -> SemanticSymbolId {
        self.class.symbol
    }

    /// Instance field names that require strict-property-initialization errors.
    pub(super) fn uninitialized_instance_properties(&self) -> &[NodeRef] {
        &self.uninitialized_instance_properties
    }

    const fn constructor_declaration(&self) -> Option<NodeRef> {
        match self.class.constructor {
            Some(constructor) => Some(constructor.declaration),
            None => None,
        }
    }

    const fn constructor_visibility(&self) -> ClassConstructorVisibility {
        match self.class.constructor {
            Some(constructor) => constructor.visibility,
            None => ClassConstructorVisibility::Public,
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) enum ClassMemberQueryPlan {
    Direct(ClassMemberPlan),
    Derived {
        class: ClassMemberPlan,
        base: Box<ClassMemberPlan>,
    },
}

impl ClassMemberQueryPlan {
    pub(super) const fn declaration(&self) -> NodeRef {
        match self {
            Self::Direct(plan) | Self::Derived { class: plan, .. } => plan.declaration(),
        }
    }

    pub(super) const fn symbol(&self) -> SemanticSymbolId {
        match self {
            Self::Direct(plan) | Self::Derived { class: plan, .. } => plan.symbol(),
        }
    }

    pub(super) fn uninitialized_instance_properties(&self) -> &[NodeRef] {
        match self {
            Self::Direct(plan) | Self::Derived { class: plan, .. } => {
                plan.uninitialized_instance_properties()
            }
        }
    }

    pub(super) fn constructor_declaration(&self) -> Option<NodeRef> {
        match self {
            Self::Direct(plan) => plan.constructor_declaration(),
            Self::Derived { class, base } => match class.constructor_declaration() {
                Some(declaration) => Some(declaration),
                None => base.constructor_declaration(),
            },
        }
    }

    pub(super) fn constructor_visibility(&self) -> ClassConstructorVisibility {
        match self {
            Self::Direct(plan) => plan.constructor_visibility(),
            Self::Derived { class, base } => {
                if class.class.constructor.is_some() {
                    class.constructor_visibility()
                } else {
                    base.constructor_visibility()
                }
            }
        }
    }

    pub(super) const fn direct_plan(&self) -> Option<&ClassMemberPlan> {
        match self {
            Self::Direct(plan) => Some(plan),
            Self::Derived { .. } => None,
        }
    }

    pub(super) fn base_plan(&self) -> Option<&ClassMemberPlan> {
        match self {
            Self::Direct(_) => None,
            Self::Derived { base, .. } => Some(base.as_ref()),
        }
    }
}

fn primitive_keyword_type(
    store: &CanonicalTypeMapperStore,
    node: NodeRef,
    kind: SyntaxKind,
) -> Result<TypeId, ClassError> {
    let bootstrap = store
        .intrinsic_bootstrap()
        .ok_or_else(|| invariant(ClassInvariant::BootstrapUnavailable(node)))?;
    match kind {
        SyntaxKind::AnyKeyword => Ok(bootstrap.any_type),
        SyntaxKind::UnknownKeyword => Ok(bootstrap.unknown_type),
        SyntaxKind::StringKeyword => Ok(bootstrap.string_type),
        SyntaxKind::NumberKeyword => Ok(bootstrap.number_type),
        SyntaxKind::BigIntKeyword => Ok(bootstrap.bigint_type),
        SyntaxKind::BooleanKeyword => Ok(bootstrap.boolean_type),
        SyntaxKind::SymbolKeyword => Ok(bootstrap.es_symbol_type),
        SyntaxKind::VoidKeyword => Ok(bootstrap.void_type),
        SyntaxKind::UndefinedKeyword => Ok(bootstrap.undefined_type),
        SyntaxKind::NeverKeyword => Ok(bootstrap.never_type),
        SyntaxKind::ObjectKeyword => Ok(bootstrap.non_primitive_type),
        _ => Err(unsupported(ClassUnsupported::PropertyType { node, kind })),
    }
}

fn expected_property_check_flags(property: &ClassPropertyPlan) -> CheckFlags {
    if property.readonly {
        CheckFlags::READONLY
    } else {
        CheckFlags::NONE
    }
}

fn method_return_type(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    method: &ClassMethodPlan,
) -> Result<TypeId, ClassError> {
    let bootstrap = store
        .intrinsic_bootstrap()
        .ok_or_else(|| invariant(ClassInvariant::BootstrapUnavailable(method.declaration)))?;
    let Some(type_node) = method.return_type_node else {
        return Ok(bootstrap.void_type);
    };
    let record = preflight_node(store, host, type_node)?;
    if record.flags.0 != 0
        || record.parent != Some(method.declaration.node)
        || !matches!(record.data, NodeData::KeywordTypeNode(_))
        || !matches!(
            record.kind,
            SyntaxKind::VoidKeyword | SyntaxKind::AnyKeyword | SyntaxKind::UndefinedKeyword
        )
    {
        return Err(unsupported(ClassUnsupported::Member {
            node: method.declaration,
            kind: SyntaxKind::MethodDeclaration,
        }));
    }
    primitive_keyword_type(store, type_node, record.kind)
}

fn exact_method_callable(
    store: &CanonicalTypeMapperStore,
    method: &ClassMethodPlan,
    return_type: TypeId,
) -> Option<(TypeId, SignatureId)> {
    exact_method_value(store, method.symbol, method.declaration, return_type)
}

fn exact_method_value(
    store: &CanonicalTypeMapperStore,
    symbol: SemanticSymbolId,
    declaration: NodeRef,
    return_type: TypeId,
) -> Option<(TypeId, SignatureId)> {
    let links = store.value_symbol_links(symbol)?;
    let type_ = links.resolved_type?;
    if links
        != &(ValueSymbolLinks {
            resolved_type: Some(type_),
            ..ValueSymbolLinks::default()
        })
    {
        return None;
    }
    let record = store.type_payload(type_)?;
    let TypeData::Object(object) = record.data() else {
        return None;
    };
    let [signature] = object.structured.signatures.as_deref()? else {
        return None;
    };
    let signature_record = store.signature(*signature)?;
    if record.flags() != TypeFlags::OBJECT
        || record.object_flags() != (ObjectFlags::ANONYMOUS | ObjectFlags::MEMBERS_RESOLVED)
        || record.symbol() != Some(symbol)
        || record.alias().is_some()
        || object.target.is_some()
        || object.mapper.is_some()
        || object.instantiations != TypeCacheState::Unallocated
        || object.structured.constrained != ConstrainedTypeData::default()
        || object.structured.members.is_some()
        || object.structured.properties.is_some()
        || object.structured.call_signature_count != 1
        || object.structured.index_infos.is_some()
        || object
            .structured
            .object_type_without_abstract_construct_signatures
            .is_some()
        || signature_record.flags() != SignatureFlags::NONE
        || signature_record.declaration() != Some(declaration)
        || !signature_record.type_parameters().is_empty()
        || !signature_record.parameters().is_empty()
        || signature_record.this_parameter().is_some()
        || signature_record.min_argument_count() != 0
        || signature_record.resolved_min_argument_count() != -1
        || signature_record.resolved_return_type() != Some(return_type)
        || signature_record.resolved_type_predicate().is_some()
        || signature_record.target().is_some()
        || signature_record.mapper().is_some()
        || signature_record.isolated_signature_type().is_some()
        || signature_record.composite().is_some()
        || store.signature_links(declaration)
            != Some(&SignatureLinks {
                resolved_signature: ResolvedSignatureState::Resolved(*signature),
                ..SignatureLinks::default()
            })
    {
        return None;
    }
    Some((type_, *signature))
}

fn validate_method_cache_state(
    store: &CanonicalTypeMapperStore,
    method: &ClassMethodPlan,
    return_type: TypeId,
) -> Result<(), ClassError> {
    if let Some(type_node) = method.return_type_node
        && store.type_node_links(type_node).is_some_and(|links| {
            links != &TypeNodeLinks::default()
                && links
                    != &(TypeNodeLinks {
                        resolved_type: Some(return_type),
                        ..TypeNodeLinks::default()
                    })
        })
    {
        return Err(invariant(ClassInvariant::InvalidPropertyTypeCache(
            type_node,
        )));
    }
    let value_links = store.value_symbol_links(method.symbol);
    let signature_links = store.signature_links(method.declaration);
    let value_cold = value_links.is_none_or(|links| links == &ValueSymbolLinks::default());
    let signature_cold = signature_links.is_none_or(|links| links == &SignatureLinks::default());
    if value_cold && signature_cold {
        return Ok(());
    }
    if !value_cold && !signature_cold && exact_method_callable(store, method, return_type).is_some()
    {
        return Ok(());
    }
    Err(invariant(ClassInvariant::InvalidPropertyValueCache(
        method.symbol,
    )))
}

fn uninitialized_instance_properties(
    store: &CanonicalTypeMapperStore,
    class: &ClassDeclarationPlan,
    property_types: &[TypeId],
) -> Result<Vec<NodeRef>, ClassError> {
    let mut uninitialized = Vec::new();
    uninitialized
        .try_reserve(class.instance_properties.len())
        .map_err(|_| invariant(ClassInvariant::Capacity(class.declaration)))?;

    for (property, property_type) in class.properties.iter().zip(property_types) {
        if property.side != ClassPropertySide::Instance || property.optional || property.definite {
            continue;
        }
        let record = store
            .type_payload(*property_type)
            .ok_or_else(|| invariant(ClassInvariant::InvalidPropertyValueCache(property.symbol)))?;
        let permits_uninitialized = record
            .flags()
            .intersects(TypeFlags::ANY_OR_UNKNOWN | TypeFlags::UNDEFINED)
            || matches!(
                record.data(),
                TypeData::Union(union)
                    if union.union.types.first().and_then(|type_| store.type_payload(*type_))
                        .is_some_and(|first| first.flags().intersects(TypeFlags::UNDEFINED))
            );
        if !permits_uninitialized {
            uninitialized.push(property.name_node);
        }
    }
    Ok(uninitialized)
}

fn exact_property_value_links(
    store: &CanonicalTypeMapperStore,
    property: &ClassPropertyPlan,
    property_type: TypeId,
) -> bool {
    store.value_symbol_links(property.symbol)
        == Some(&ValueSymbolLinks {
            resolved_type: Some(property_type),
            ..ValueSymbolLinks::default()
        })
}

fn validate_property_cache_state(
    store: &CanonicalTypeMapperStore,
    property: &ClassPropertyPlan,
    property_type: TypeId,
) -> Result<(), ClassError> {
    match store.type_node_links(property.type_node) {
        None => {}
        Some(links) if links == &TypeNodeLinks::default() => {}
        Some(links)
            if links
                == &(TypeNodeLinks {
                    resolved_type: Some(property_type),
                    ..TypeNodeLinks::default()
                }) => {}
        Some(_) => {
            return Err(invariant(ClassInvariant::InvalidPropertyTypeCache(
                property.type_node,
            )));
        }
    }

    let expected_check_flags = expected_property_check_flags(property);
    let check_flags = store
        .symbol(property.symbol)
        .ok_or_else(|| invariant(ClassInvariant::InvalidPropertySymbol(property.declaration)))?
        .check_flags();
    match store.value_symbol_links(property.symbol) {
        None => {
            if check_flags != CheckFlags::NONE {
                return Err(invariant(ClassInvariant::InvalidPropertyValueCache(
                    property.symbol,
                )));
            }
        }
        Some(links) if links == &ValueSymbolLinks::default() => {
            if check_flags != CheckFlags::NONE {
                return Err(invariant(ClassInvariant::InvalidPropertyValueCache(
                    property.symbol,
                )));
            }
        }
        Some(links)
            if links
                == &(ValueSymbolLinks {
                    resolved_type: Some(property_type),
                    ..ValueSymbolLinks::default()
                })
                && check_flags == expected_check_flags => {}
        Some(_) => {
            return Err(invariant(ClassInvariant::InvalidPropertyValueCache(
                property.symbol,
            )));
        }
    }
    Ok(())
}

fn validate_index_type_cache(
    store: &CanonicalTypeMapperStore,
    node: NodeRef,
    expected: TypeId,
) -> Result<(), ClassError> {
    if store.type_node_links(node).is_some_and(|links| {
        links != &TypeNodeLinks::default()
            && links
                != &(TypeNodeLinks {
                    resolved_type: Some(expected),
                    ..TypeNodeLinks::default()
                })
    }) {
        return Err(invariant(ClassInvariant::InvalidPropertyTypeCache(node)));
    }
    Ok(())
}

fn plan_index_types(
    store: &CanonicalTypeMapperStore,
    index: Option<&ClassIndexSignaturePlan>,
) -> Result<Option<(TypeId, TypeId)>, ClassError> {
    let Some(index) = index else {
        return Ok(None);
    };
    let bootstrap = store
        .intrinsic_bootstrap()
        .ok_or_else(|| invariant(ClassInvariant::BootstrapUnavailable(index.declaration)))?;
    let key_type = bootstrap.string_type;
    let value_type = bootstrap.number_type;
    validate_index_type_cache(store, index.key_type_node, key_type)?;
    validate_index_type_cache(store, index.value_type_node, value_type)?;
    Ok(Some((key_type, value_type)))
}

/// Preflights the first exact class-member cut.
///
/// Every property must have one direct primitive keyword annotation. This
/// keeps the class transaction dependency-closed without executing several
/// independent type-node queries whose later failure could expose an earlier
/// property publication.
fn plan_class_members(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    class: ClassDeclarationPlan,
) -> Result<ClassMemberPlan, ClassError> {
    let mut property_types = Vec::new();
    property_types
        .try_reserve_exact(class.properties.len())
        .map_err(|_| invariant(ClassInvariant::Capacity(class.declaration)))?;
    for property in &class.properties {
        let record = preflight_node(store, host, property.type_node)?;
        if record.flags.0 != 0
            || !matches!(record.data, NodeData::KeywordTypeNode(_))
            || record.parent != Some(property.declaration.node)
        {
            return Err(unsupported(ClassUnsupported::PropertyType {
                node: property.type_node,
                kind: record.kind,
            }));
        }
        let property_type = primitive_keyword_type(store, property.type_node, record.kind)?;
        validate_property_cache_state(store, property, property_type)?;
        property_types.push(property_type);
    }
    let mut method_return_types = Vec::new();
    method_return_types
        .try_reserve_exact(class.methods.len())
        .map_err(|_| invariant(ClassInvariant::Capacity(class.declaration)))?;
    for method in &class.methods {
        let return_type = method_return_type(store, host, method)?;
        validate_method_cache_state(store, method, return_type)?;
        method_return_types.push(return_type);
    }
    let index_types = plan_index_types(store, class.index.as_ref())?;
    let uninitialized_instance_properties =
        uninitialized_instance_properties(store, &class, &property_types)?;
    Ok(ClassMemberPlan {
        class,
        property_types,
        method_return_types,
        index_types,
        uninitialized_instance_properties,
    })
}

pub(super) fn plan_nongeneric_class_members(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    symbol: SemanticSymbolId,
) -> Result<ClassMemberPlan, ClassError> {
    let class = plan_nongeneric_class(store, host, symbol)?;
    plan_class_members(store, host, class)
}

/// Plans either the existing no-base class cut or one exact direct local base.
///
/// Both the public query and whole-source adapter retain this exact aggregate
/// plan so the base dependency is proven before either class can publish.
pub(super) fn plan_nongeneric_class_member_query(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    symbol: SemanticSymbolId,
) -> Result<ClassMemberQueryPlan, ClassError> {
    let class = plan_class_declaration(store, host, symbol, true)?;
    let Some(base) = class.base.as_ref() else {
        return plan_class_members(store, host, class).map(ClassMemberQueryPlan::Direct);
    };
    let base_plan = plan_nongeneric_class_members(store, host, base.symbol)?;
    if base_plan.constructor_visibility() == ClassConstructorVisibility::Private
        || base_plan.class.index.is_some()
    {
        return Err(unsupported(ClassUnsupported::Heritage(base.expression)));
    }
    let class = plan_class_members(store, host, class)?;
    Ok(ClassMemberQueryPlan::Derived {
        class,
        base: Box::new(base_plan),
    })
}

fn prototype_symbol(
    store: &CanonicalTypeMapperStore,
    plan: &ClassDeclarationPlan,
) -> Option<SemanticSymbolId> {
    store
        .symbol_table(plan.static_members)
        .and_then(|members| members.get_source(PROTOTYPE_NAME))
}

fn planned_class_member_entries(
    properties: &[ClassPropertyPlan],
    methods: &[ClassMethodPlan],
) -> Vec<(EscapedName, SemanticSymbolId)> {
    let mut entries = properties
        .iter()
        .map(|property| {
            (
                property.declaration,
                EscapedName::source(property.name.as_str()),
                property.symbol,
            )
        })
        .chain(methods.iter().map(|method| {
            (
                method.declaration,
                EscapedName::source(method.name.as_str()),
                method.symbol,
            )
        }))
        .collect::<Vec<_>>();
    entries.sort_unstable_by_key(|(declaration, _, _)| *declaration);
    entries
        .into_iter()
        .map(|(_, name, symbol)| (name, symbol))
        .collect()
}

fn exact_member_table(
    store: &CanonicalTypeMapperStore,
    table: Option<SymbolTableId>,
    properties: &[ClassPropertyPlan],
    methods: &[ClassMethodPlan],
) -> bool {
    let entries = planned_class_member_entries(properties, methods);
    match (table, entries.is_empty()) {
        (None, true) => true,
        (Some(table), false) => store.symbol_table(table).is_some_and(|table| {
            table.len() == entries.len()
                && entries
                    .iter()
                    .all(|(name, symbol)| table.get(name.as_ref()) == Some(*symbol))
        }),
        _ => false,
    }
}

fn exact_class_instance_identity(
    store: &CanonicalTypeMapperStore,
    symbol: SemanticSymbolId,
    instance_type: TypeId,
) -> Option<&super::type_records::InterfaceTypeData> {
    let record = store.type_payload(instance_type)?;
    let TypeData::Interface(instance) = record.data() else {
        return None;
    };
    let [this_type] = instance.all_type_parameters.as_deref()? else {
        return None;
    };
    let this_record = store.type_payload(*this_type)?;
    let TypeData::TypeParameter(this) = this_record.data() else {
        return None;
    };
    let TypeCacheState::Allocated(instantiations) = &instance.reference.object.instantiations
    else {
        return None;
    };
    (record.flags() == TypeFlags::OBJECT
        && record.symbol() == Some(symbol)
        && record.alias().is_none()
        && instance.outer_type_parameter_count == 0
        && instance.this_type == Some(*this_type)
        && instance.reference.object.target == Some(instance_type)
        && instance.reference.object.mapper.is_none()
        && instantiations.len() == 1
        && instantiations.get(&type_list_key(&[])) == Some(&instance_type)
        && instance.reference.node.is_none()
        && instance.reference.resolved_type_arguments.as_deref() == Some(&[][..])
        && this_record.flags() == TypeFlags::TYPE_PARAMETER
        && this_record.object_flags() == ObjectFlags::NONE
        && this_record.symbol() == Some(symbol)
        && this_record.alias().is_none()
        && this
            == &(TypeParameterData {
                constraint: Some(instance_type),
                is_this_type: true,
                ..TypeParameterData::default()
            }))
        .then_some(instance)
}

fn exact_instance_identity<'a>(
    store: &'a CanonicalTypeMapperStore,
    plan: &ClassDeclarationPlan,
    instance_type: TypeId,
) -> Option<&'a super::type_records::InterfaceTypeData> {
    exact_class_instance_identity(store, plan.symbol, instance_type)
}

fn exact_construct_signature(
    store: &CanonicalTypeMapperStore,
    signature: SignatureId,
    instance_type: TypeId,
    declaration: Option<NodeRef>,
) -> bool {
    store.signature(signature).is_some_and(|signature| {
        signature.flags() == SignatureFlags::CONSTRUCT
            && signature.min_argument_count() == 0
            && signature.resolved_min_argument_count() == -1
            && signature.declaration() == declaration
            && signature.type_parameters().is_empty()
            && signature.parameters().is_empty()
            && signature.this_parameter().is_none()
            && signature.resolved_return_type() == Some(instance_type)
            && signature.resolved_type_predicate().is_none()
            && signature.target().is_none()
            && signature.mapper().is_none()
            && signature.isolated_signature_type().is_none()
            && signature.composite().is_none()
    })
}

fn exact_class_index_infos(
    store: &CanonicalTypeMapperStore,
    plan: &ClassMemberPlan,
    indexes: Option<&[IndexInfoId]>,
) -> bool {
    match (plan.class.index, plan.index_types, indexes) {
        (None, None, None) => true,
        (Some(index), Some((key_type, value_type)), Some([info])) => {
            store.index_info(*info).is_some_and(|info| {
                info.key_type() == key_type
                    && info.value_type() == value_type
                    && !info.is_readonly()
                    && info.declaration() == Some(index.declaration)
                    && info.index_symbol().is_none()
                    && info.components().is_empty()
                    && plan
                        .class
                        .instance_members
                        .and_then(|members| store.symbol_table(members))
                        .and_then(|members| members.get(InternalSymbolName::Index.as_ref()))
                        == Some(index.symbol)
                    && store.type_node_links(index.key_type_node)
                        == Some(&TypeNodeLinks {
                            resolved_type: Some(key_type),
                            ..TypeNodeLinks::default()
                        })
                    && store.type_node_links(index.value_type_node)
                        == Some(&TypeNodeLinks {
                            resolved_type: Some(value_type),
                            ..TypeNodeLinks::default()
                        })
            })
        }
        _ => false,
    }
}

fn completed_class_members(
    store: &CanonicalTypeMapperStore,
    plan: &ClassMemberPlan,
    instance_type: TypeId,
    value_type: TypeId,
) -> Option<ClassMembers> {
    if plan.class.base.is_some()
        || store
            .direct_class_heritage_provenance(instance_type)
            .is_some()
    {
        return None;
    }
    let undefined_type = store.intrinsic_bootstrap()?.undefined_type;
    let instance = exact_instance_identity(store, &plan.class, instance_type)?;
    if store
        .declared_type_links(plan.class.symbol)
        .and_then(|links| links.declared_type)
        != Some(instance_type)
        || !instance.base_types_resolved
        || instance.resolved_base_constructor_type != Some(undefined_type)
        || instance.resolved_base_types.is_some()
        || !instance.declared_members_resolved
        || instance.declared_members != plan.class.instance_members
        || instance.declared_call_signatures.is_some()
        || instance.declared_construct_signatures.is_some()
        || !exact_class_index_infos(store, plan, instance.declared_index_infos.as_deref())
    {
        return None;
    }

    let instance_structured = &instance.reference.object.structured;
    let instance_properties = planned_class_member_entries(
        &plan.class.instance_properties,
        &plan.class.instance_methods,
    )
    .into_iter()
    .map(|(_, symbol)| symbol)
    .collect::<Vec<_>>();
    if store.type_payload(instance_type).is_none_or(|record| {
        record.object_flags()
            != (ObjectFlags::CLASS | ObjectFlags::REFERENCE | ObjectFlags::MEMBERS_RESOLVED)
    }) || instance_structured.constrained != ConstrainedTypeData::default()
        || instance_structured.properties.as_deref()
            != (!instance_properties.is_empty()).then_some(instance_properties.as_slice())
        || instance_structured.signatures.is_some()
        || instance_structured.call_signature_count != 0
        || instance_structured.index_infos.as_deref() != instance.declared_index_infos.as_deref()
        || instance_structured
            .object_type_without_abstract_construct_signatures
            .is_some()
        || instance_structured.members == plan.class.instance_members
            && instance_structured.members.is_some()
        || !exact_member_table(
            store,
            instance_structured.members,
            &plan.class.instance_properties,
            &plan.class.instance_methods,
        )
    {
        return None;
    }

    let value_record = store.type_payload(value_type)?;
    let TypeData::Object(value) = value_record.data() else {
        return None;
    };
    let prototype = prototype_symbol(store, &plan.class)?;
    let static_properties =
        planned_class_member_entries(&plan.class.static_properties, &plan.class.static_methods)
            .into_iter()
            .map(|(_, symbol)| symbol)
            .collect::<Vec<_>>();
    let mut all_static_properties = static_properties.clone();
    all_static_properties.push(prototype);
    let [default_construct_signature] = value.structured.signatures.as_deref()? else {
        return None;
    };
    if value_record.flags() != TypeFlags::OBJECT
        || value_record.object_flags() != (ObjectFlags::ANONYMOUS | ObjectFlags::MEMBERS_RESOLVED)
        || value_record.symbol() != Some(plan.class.symbol)
        || value_record.alias().is_some()
        || value.target.is_some()
        || value.mapper.is_some()
        || value.instantiations != TypeCacheState::Unallocated
        || value.structured.constrained != ConstrainedTypeData::default()
        || value.structured.members != Some(plan.class.static_members)
        || value.structured.properties.as_deref() != Some(all_static_properties.as_slice())
        || value.structured.call_signature_count != 0
        || value.structured.index_infos.is_some()
        || value
            .structured
            .object_type_without_abstract_construct_signatures
            .is_some()
        || !exact_construct_signature(
            store,
            *default_construct_signature,
            instance_type,
            plan.constructor_declaration(),
        )
        || plan.class.constructor.is_some_and(|constructor| {
            store.signature_links(constructor.declaration)
                != Some(&SignatureLinks {
                    resolved_signature: ResolvedSignatureState::Resolved(
                        *default_construct_signature,
                    ),
                    ..SignatureLinks::default()
                })
        })
    {
        return None;
    }

    if plan
        .class
        .properties
        .iter()
        .zip(&plan.property_types)
        .any(|(property, property_type)| {
            store
                .type_node_links(property.type_node)
                .is_none_or(|links| {
                    links
                        != &(TypeNodeLinks {
                            resolved_type: Some(*property_type),
                            ..TypeNodeLinks::default()
                        })
                })
                || store.symbol(property.symbol).is_none_or(|symbol| {
                    symbol.check_flags() != expected_property_check_flags(property)
                })
                || !exact_property_value_links(store, property, *property_type)
        })
    {
        return None;
    }
    if plan
        .class
        .methods
        .iter()
        .zip(&plan.method_return_types)
        .any(|(method, return_type)| {
            exact_method_callable(store, method, *return_type).is_none()
                || method.return_type_node.is_some_and(|type_node| {
                    store.type_node_links(type_node)
                        != Some(&TypeNodeLinks {
                            resolved_type: Some(*return_type),
                            ..TypeNodeLinks::default()
                        })
                })
        })
    {
        return None;
    }

    Some(ClassMembers {
        shells: ClassShells {
            declaration: plan.class.declaration,
            symbol: plan.class.symbol,
            instance_type,
            value_type,
        },
        base: None,
        instance_members: instance_structured.members,
        static_members: plan.class.static_members,
        declared_instance_property_count: instance_properties.len(),
        instance_properties,
        declared_static_property_count: static_properties.len(),
        static_properties,
        prototype,
        default_construct_signature: *default_construct_signature,
    })
}

#[derive(Clone)]
struct DerivedMemberSurfaces {
    instance_entries: Vec<(EscapedName, SemanticSymbolId)>,
    instance_properties: Vec<SemanticSymbolId>,
    static_entries: Vec<(EscapedName, SemanticSymbolId)>,
    static_properties: Vec<SemanticSymbolId>,
}

fn prepare_derived_member_surfaces(
    store: &CanonicalTypeMapperStore,
    plan: &ClassMemberPlan,
    base_plan: &ClassMemberPlan,
) -> Result<DerivedMemberSurfaces, ClassError> {
    let capacity = || invariant(ClassInvariant::Capacity(plan.class.declaration));
    let own_instance_entries = planned_class_member_entries(
        &plan.class.instance_properties,
        &plan.class.instance_methods,
    );
    let inherited_instance_entries = planned_class_member_entries(
        &base_plan.class.instance_properties,
        &base_plan.class.instance_methods,
    );
    let own_static_entries =
        planned_class_member_entries(&plan.class.static_properties, &plan.class.static_methods);
    let inherited_static_entries = planned_class_member_entries(
        &base_plan.class.static_properties,
        &base_plan.class.static_methods,
    );
    let instance_capacity = own_instance_entries
        .len()
        .checked_add(inherited_instance_entries.len())
        .ok_or_else(capacity)?;
    let static_capacity = own_static_entries
        .len()
        .checked_add(inherited_static_entries.len())
        .and_then(|capacity| capacity.checked_add(1))
        .ok_or_else(capacity)?;
    let mut instance_entries = Vec::new();
    let mut instance_properties = Vec::new();
    let mut static_entries = Vec::new();
    let mut static_properties = Vec::new();
    let mut instance_names = HashSet::new();
    let mut static_names = HashSet::new();
    instance_entries
        .try_reserve_exact(instance_capacity)
        .map_err(|_| capacity())?;
    instance_properties
        .try_reserve_exact(instance_capacity)
        .map_err(|_| capacity())?;
    static_entries
        .try_reserve_exact(static_capacity)
        .map_err(|_| capacity())?;
    static_properties
        .try_reserve_exact(static_capacity.saturating_sub(1))
        .map_err(|_| capacity())?;
    instance_names
        .try_reserve(instance_capacity)
        .map_err(|_| capacity())?;
    static_names
        .try_reserve(static_capacity)
        .map_err(|_| capacity())?;

    for (name, symbol) in own_instance_entries {
        if !instance_names.insert(name.clone()) {
            return Err(invariant(ClassInvariant::InvalidOwnerSymbol(
                plan.class.symbol,
            )));
        }
        instance_entries.push((name, symbol));
        instance_properties.push(symbol);
    }
    for (name, symbol) in inherited_instance_entries {
        if instance_names.insert(name.clone()) {
            instance_entries.push((name, symbol));
            instance_properties.push(symbol);
        }
    }

    for (name, symbol) in own_static_entries {
        if !static_names.insert(name.clone()) {
            return Err(invariant(ClassInvariant::InvalidOwnerSymbol(
                plan.class.symbol,
            )));
        }
        static_entries.push((name, symbol));
        static_properties.push(symbol);
    }
    let prototype = prototype_symbol(store, &plan.class)
        .ok_or_else(|| invariant(ClassInvariant::InvalidPrototype(plan.class.symbol)))?;
    let prototype_name = EscapedName::source(PROTOTYPE_NAME);
    if !static_names.insert(prototype_name.clone()) {
        return Err(invariant(ClassInvariant::InvalidPrototype(
            plan.class.symbol,
        )));
    }
    static_entries.push((prototype_name, prototype));
    for (name, symbol) in inherited_static_entries {
        if static_names.insert(name.clone()) {
            static_entries.push((name, symbol));
            static_properties.push(symbol);
        }
    }
    Ok(DerivedMemberSurfaces {
        instance_entries,
        instance_properties,
        static_entries,
        static_properties,
    })
}

fn exact_symbol_table_entries(
    store: &CanonicalTypeMapperStore,
    table: Option<SymbolTableId>,
    entries: &[(EscapedName, SemanticSymbolId)],
) -> bool {
    match (table, entries.is_empty()) {
        (None, true) => true,
        (Some(table), false) => store.symbol_table(table).is_some_and(|table| {
            table.len() == entries.len()
                && entries
                    .iter()
                    .all(|(name, symbol)| table.get(name.as_ref()) == Some(*symbol))
        }),
        _ => false,
    }
}

fn completed_derived_class_members(
    store: &CanonicalTypeMapperStore,
    plan: &ClassMemberPlan,
    base: &ClassMembers,
    instance_type: TypeId,
    value_type: TypeId,
    surfaces: &DerivedMemberSurfaces,
) -> Option<ClassMembers> {
    let base_plan = plan.class.base.as_ref()?;
    let instance = exact_instance_identity(store, &plan.class, instance_type)?;
    if store
        .declared_type_links(plan.class.symbol)
        .and_then(|links| links.declared_type)
        != Some(instance_type)
        || !instance.base_types_resolved
        || instance.resolved_base_constructor_type != Some(base.shells.value_type)
        || instance.resolved_base_types.as_deref() != Some(&[base.shells.instance_type][..])
        || !instance.declared_members_resolved
        || instance.declared_members != plan.class.instance_members
        || instance.declared_call_signatures.is_some()
        || instance.declared_construct_signatures.is_some()
        || instance.declared_index_infos.is_some()
    {
        return None;
    }
    let provenance = DirectClassHeritageProvenance {
        owner_symbol: plan.class.symbol,
        owner_value_type: value_type,
        base_symbol: base_plan.symbol,
        base_instance_type: base.shells.instance_type,
        base_value_type: base.shells.value_type,
    };
    if store.direct_class_heritage_provenance(instance_type) != Some(provenance) {
        return None;
    }

    let instance_record = store.type_payload(instance_type)?;
    let instance_structured = &instance.reference.object.structured;
    if instance_record.object_flags()
        != (ObjectFlags::CLASS | ObjectFlags::REFERENCE | ObjectFlags::MEMBERS_RESOLVED)
        || instance_structured.constrained != ConstrainedTypeData::default()
        || instance_structured.properties.as_deref()
            != (!surfaces.instance_properties.is_empty())
                .then_some(surfaces.instance_properties.as_slice())
        || instance_structured.signatures.is_some()
        || instance_structured.call_signature_count != 0
        || instance_structured.index_infos.is_some()
        || instance_structured
            .object_type_without_abstract_construct_signatures
            .is_some()
        || instance_structured.members == plan.class.instance_members
            && instance_structured.members.is_some()
        || !exact_symbol_table_entries(
            store,
            instance_structured.members,
            &surfaces.instance_entries,
        )
    {
        return None;
    }

    let value_record = store.type_payload(value_type)?;
    let TypeData::Object(value) = value_record.data() else {
        return None;
    };
    let prototype = prototype_symbol(store, &plan.class)?;
    let mut all_static_properties = surfaces.static_properties.clone();
    all_static_properties.push(prototype);
    let [default_construct_signature] = value.structured.signatures.as_deref()? else {
        return None;
    };
    if value_record.flags() != TypeFlags::OBJECT
        || value_record.object_flags() != (ObjectFlags::ANONYMOUS | ObjectFlags::MEMBERS_RESOLVED)
        || value_record.symbol() != Some(plan.class.symbol)
        || value_record.alias().is_some()
        || value.target.is_some()
        || value.mapper.is_some()
        || value.instantiations != TypeCacheState::Unallocated
        || value.structured.constrained != ConstrainedTypeData::default()
        || value.structured.properties.as_deref() != Some(all_static_properties.as_slice())
        || value.structured.call_signature_count != 0
        || value.structured.index_infos.is_some()
        || value
            .structured
            .object_type_without_abstract_construct_signatures
            .is_some()
        || value.structured.members == Some(plan.class.static_members)
        || !exact_symbol_table_entries(store, value.structured.members, &surfaces.static_entries)
        || !exact_construct_signature(
            store,
            *default_construct_signature,
            instance_type,
            store
                .signature(base.default_construct_signature)
                .and_then(super::signatures::Signature::declaration),
        )
    {
        return None;
    }
    if plan
        .class
        .properties
        .iter()
        .zip(&plan.property_types)
        .any(|(property, property_type)| {
            store
                .type_node_links(property.type_node)
                .is_none_or(|links| {
                    links
                        != &(TypeNodeLinks {
                            resolved_type: Some(*property_type),
                            ..TypeNodeLinks::default()
                        })
                })
                || store.symbol(property.symbol).is_none_or(|symbol| {
                    symbol.check_flags() != expected_property_check_flags(property)
                })
                || !exact_property_value_links(store, property, *property_type)
        })
    {
        return None;
    }
    if plan
        .class
        .methods
        .iter()
        .zip(&plan.method_return_types)
        .any(|(method, return_type)| {
            exact_method_callable(store, method, *return_type).is_none()
                || method.return_type_node.is_some_and(|type_node| {
                    store.type_node_links(type_node)
                        != Some(&TypeNodeLinks {
                            resolved_type: Some(*return_type),
                            ..TypeNodeLinks::default()
                        })
                })
        })
    {
        return None;
    }
    Some(ClassMembers {
        shells: ClassShells {
            declaration: plan.class.declaration,
            symbol: plan.class.symbol,
            instance_type,
            value_type,
        },
        base: Some(ClassBaseIdentities {
            symbol: base_plan.symbol,
            instance_type: base.shells.instance_type,
            value_type: base.shells.value_type,
        }),
        instance_members: instance_structured.members,
        static_members: value.structured.members?,
        instance_properties: surfaces.instance_properties.clone(),
        declared_instance_property_count: plan.class.instance_properties.len()
            + plan.class.instance_methods.len(),
        static_properties: surfaces.static_properties.clone(),
        declared_static_property_count: plan.class.static_properties.len()
            + plan.class.static_methods.len(),
        prototype,
        default_construct_signature: *default_construct_signature,
    })
}

fn has_instance_member_publication(
    store: &CanonicalTypeMapperStore,
    instance_type: TypeId,
) -> bool {
    store.type_payload(instance_type).is_some_and(|record| {
        record
            .object_flags()
            .contains(ObjectFlags::MEMBERS_RESOLVED)
            || matches!(record.data(), TypeData::Interface(interface) if
                interface.base_types_resolved
                || interface.declared_members_resolved
                || interface.declared_members.is_some()
                || interface.declared_call_signatures.is_some()
                || interface.declared_construct_signatures.is_some()
                || interface.declared_index_infos.is_some()
                || interface.reference.object.structured != StructuredTypeData::default())
    })
}

fn has_static_member_publication(store: &CanonicalTypeMapperStore, value_type: TypeId) -> bool {
    store.type_payload(value_type).is_some_and(|record| {
        record
            .object_flags()
            .contains(ObjectFlags::MEMBERS_RESOLVED)
            || record
                .data()
                .structured()
                .is_some_and(|structured| structured != &StructuredTypeData::default())
    })
}

fn cached_primitive_member_plan(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    class: &ClassDeclarationPlan,
) -> Option<ClassMemberPlan> {
    let mut property_types = Vec::with_capacity(class.properties.len());
    for property in &class.properties {
        let record = preflight_node(store, host, property.type_node).ok()?;
        if record.flags.0 != 0
            || !matches!(record.data, NodeData::KeywordTypeNode(_))
            || record.parent != Some(property.declaration.node)
        {
            return None;
        }
        let property_type = primitive_keyword_type(store, property.type_node, record.kind).ok()?;
        validate_property_cache_state(store, property, property_type).ok()?;
        property_types.push(property_type);
    }
    let mut method_return_types = Vec::with_capacity(class.methods.len());
    for method in &class.methods {
        let return_type = method_return_type(store, host, method).ok()?;
        validate_method_cache_state(store, method, return_type).ok()?;
        method_return_types.push(return_type);
    }
    let index_types = plan_index_types(store, class.index.as_ref()).ok()?;
    let uninitialized_instance_properties =
        uninitialized_instance_properties(store, class, &property_types).ok()?;
    Some(ClassMemberPlan {
        class: class.clone(),
        property_types,
        method_return_types,
        index_types,
        uninitialized_instance_properties,
    })
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum StaticShellState {
    Cold,
    WarmShell(TypeId),
    WarmMembers(TypeId),
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct ClassShellState {
    instance: Option<TypeId>,
    value: StaticShellState,
}

fn exact_static_shell(
    store: &CanonicalTypeMapperStore,
    symbol: SemanticSymbolId,
    type_: TypeId,
) -> bool {
    let Some(record) = store.type_payload(type_) else {
        return false;
    };
    record.flags() == TypeFlags::OBJECT
        && record.object_flags() == ObjectFlags::ANONYMOUS
        && record.symbol() == Some(symbol)
        && record.alias().is_none()
        && matches!(record.data(), TypeData::Object(object) if object == &ObjectTypeData::default())
}

fn shell_state(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    plan: &ClassDeclarationPlan,
) -> Result<ClassShellState, ClassError> {
    let instance = store
        .declared_type_links(plan.symbol)
        .and_then(|links| links.declared_type);
    let value = match store.value_symbol_links(plan.symbol) {
        None => StaticShellState::Cold,
        Some(links) if links == &ValueSymbolLinks::default() => StaticShellState::Cold,
        Some(links) if links.resolved_type.is_some() => {
            let type_ = links
                .resolved_type
                .expect("the branch checked the resolved identity");
            if links
                != &(ValueSymbolLinks {
                    resolved_type: Some(type_),
                    ..ValueSymbolLinks::default()
                })
            {
                return Err(invariant(ClassInvariant::InvalidValueCache(plan.symbol)));
            }
            if exact_static_shell(store, plan.symbol, type_) {
                StaticShellState::WarmShell(type_)
            } else if instance.is_some_and(|instance| {
                cached_primitive_member_plan(store, host, plan).is_some_and(|members| {
                    completed_class_members(store, &members, instance, type_).is_some()
                })
            }) {
                StaticShellState::WarmMembers(type_)
            } else {
                return Err(invariant(ClassInvariant::InvalidValueCache(plan.symbol)));
            }
        }
        Some(_) => {
            return Err(invariant(ClassInvariant::InvalidValueCache(plan.symbol)));
        }
    };
    let Some(undefined_type) = store
        .intrinsic_bootstrap()
        .map(|bootstrap| bootstrap.undefined_type)
    else {
        return Err(invariant(ClassInvariant::BootstrapUnavailable(
            plan.declaration,
        )));
    };
    if let Some(instance) = instance {
        let Some(interface) = exact_instance_identity(store, plan, instance) else {
            return Err(invariant(ClassInvariant::InvalidInstanceCache(plan.symbol)));
        };
        if store.direct_class_heritage_provenance(instance).is_some()
            || !matches!(value, StaticShellState::WarmMembers(_))
                && (store.type_payload(instance).is_none_or(|record| {
                    record.object_flags() != (ObjectFlags::CLASS | ObjectFlags::REFERENCE)
                }) || interface.base_types_resolved
                    || interface.resolved_base_types.is_some()
                    || interface
                        .resolved_base_constructor_type
                        .is_some_and(|type_| type_ != undefined_type)
                    || matches!(value, StaticShellState::WarmShell(_))
                        && interface.resolved_base_constructor_type != Some(undefined_type)
                    || interface.declared_members_resolved
                    || interface.declared_members.is_some()
                    || interface.declared_call_signatures.is_some()
                    || interface.declared_construct_signatures.is_some()
                    || interface.declared_index_infos.is_some()
                    || interface.reference.object.structured != StructuredTypeData::default())
        {
            return Err(invariant(ClassInvariant::InvalidInstanceCache(plan.symbol)));
        }
    } else if !matches!(value, StaticShellState::Cold) {
        return Err(invariant(ClassInvariant::InvalidValueCache(plan.symbol)));
    }
    Ok(ClassShellState { instance, value })
}

/// Installs or validates the two exact class identities from a previously
/// produced plan.
///
/// Cold execution allocates exactly the instance origin, its synthetic `this`
/// type, and the anonymous static shell. It then forces the no-heritage base
/// constructor cache to canonical `undefined` before publishing the class
/// value link, matching pinned `getTypeOfFuncClassEnumModuleWorker`.
pub(super) fn execute_nongeneric_class_shells(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    plan: &ClassDeclarationPlan,
) -> Result<ClassShells, ClassError> {
    let current = plan_nongeneric_class(store, host, plan.symbol)?;
    if current != *plan {
        return Err(invariant(ClassInvariant::InvalidPlan(plan.declaration)));
    }
    let state = shell_state(store, host, plan)?;
    if let StaticShellState::WarmShell(value_type) | StaticShellState::WarmMembers(value_type) =
        state.value
    {
        let instance_type = state
            .instance
            .expect("a validated warm static shell requires its instance");
        return Ok(ClassShells {
            declaration: plan.declaration,
            symbol: plan.symbol,
            instance_type,
            value_type,
        });
    }

    let cold_instance = state.instance.is_none();
    let additional = 1usize
        .checked_add(usize::from(cold_instance) * 2)
        .ok_or_else(|| invariant(ClassInvariant::Capacity(plan.declaration)))?;
    if !store.try_reserve_types(additional) {
        return Err(invariant(ClassInvariant::Capacity(plan.declaration)));
    }

    // `checkClassLikeDeclaration` asks for the declared instance first.
    let instance_type = store.get_declared_type_of_symbol(host, plan.symbol)?;
    if state.instance.is_some_and(|type_| type_ != instance_type) {
        return Err(invariant(ClassInvariant::InvalidInstanceCache(plan.symbol)));
    }
    // `getTypeOfFuncClassEnumModuleWorker` allocates the value object before
    // forcing the base-constructor cache.
    let value_type = store
        .alloc_plain_object_type(ObjectFlags::ANONYMOUS, Some(plan.symbol))
        .ok_or_else(|| invariant(ClassInvariant::Publication(plan.declaration)))?;

    let undefined_type = store
        .intrinsic_bootstrap()
        .expect("the shell state validated bootstrap")
        .undefined_type;
    let (base_types_resolved, base_constructor, base_types) = {
        let Some(TypeData::Interface(interface)) = store
            .type_payload(instance_type)
            .map(super::type_records::TypeRecord::data)
        else {
            return Err(invariant(ClassInvariant::InvalidInstanceCache(plan.symbol)));
        };
        (
            interface.base_types_resolved,
            interface.resolved_base_constructor_type,
            interface.resolved_base_types.clone(),
        )
    };
    if base_types_resolved
        || base_types.is_some()
        || base_constructor.is_some_and(|type_| type_ != undefined_type)
    {
        return Err(invariant(ClassInvariant::InvalidInstanceCache(plan.symbol)));
    }
    if base_constructor.is_none() {
        assert!(store.set_interface_base_resolution(
            instance_type,
            base_types_resolved,
            Some(undefined_type),
            base_types,
        ));
    }
    assert!(store.set_value_symbol_links(
        plan.symbol,
        ValueSymbolLinks {
            resolved_type: Some(value_type),
            ..ValueSymbolLinks::default()
        },
    ));

    let resolved = shell_state(store, host, plan)?;
    if resolved.instance != Some(instance_type)
        || resolved.value != StaticShellState::WarmShell(value_type)
    {
        return Err(invariant(ClassInvariant::Publication(plan.declaration)));
    }
    Ok(ClassShells {
        declaration: plan.declaration,
        symbol: plan.symbol,
        instance_type,
        value_type,
    })
}

fn resolved_class_value_type(
    store: &CanonicalTypeMapperStore,
    symbol: SemanticSymbolId,
) -> Option<TypeId> {
    let links = store.value_symbol_links(symbol)?;
    let type_ = links.resolved_type?;
    (links
        == &(ValueSymbolLinks {
            resolved_type: Some(type_),
            ..ValueSymbolLinks::default()
        }))
        .then_some(type_)
}

fn class_member_state(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    plan: &ClassMemberPlan,
) -> Result<Option<ClassMembers>, ClassError> {
    let instance = store
        .declared_type_links(plan.class.symbol)
        .and_then(|links| links.declared_type);
    let value = resolved_class_value_type(store, plan.class.symbol);
    if let (Some(instance), Some(value)) = (instance, value)
        && let Some(members) = completed_class_members(store, plan, instance, value)
    {
        return Ok(Some(members));
    }
    if instance.is_some_and(|instance| has_instance_member_publication(store, instance)) {
        return Err(invariant(ClassInvariant::InvalidInstanceMembers(
            plan.class.symbol,
        )));
    }
    if value.is_some_and(|value| has_static_member_publication(store, value)) {
        return Err(invariant(ClassInvariant::InvalidStaticMembers(
            plan.class.symbol,
        )));
    }
    shell_state(store, host, &plan.class)?;
    Ok(None)
}

fn validated_nongeneric_class_member_state(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    plan: &ClassMemberPlan,
) -> Result<Option<ClassMembers>, ClassError> {
    let current = plan_nongeneric_class_members(store, host, plan.class.symbol)?;
    if current != *plan {
        return Err(invariant(ClassInvariant::InvalidPlan(
            plan.class.declaration,
        )));
    }
    class_member_state(store, host, plan)
}

/// Revalidates one exact member plan and every observable warm class cache
/// without publishing a cold shell or member graph.
pub(super) fn preflight_nongeneric_class_members(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    plan: &ClassMemberPlan,
) -> Result<(), ClassError> {
    validated_nongeneric_class_member_state(store, host, plan).map(drop)
}

fn prepare_class_method_signatures(
    plan: &ClassMemberPlan,
) -> Result<Vec<Vec<SignatureId>>, ClassError> {
    let mut signature_lists = Vec::new();
    signature_lists
        .try_reserve_exact(plan.class.methods.len())
        .map_err(|_| invariant(ClassInvariant::Capacity(plan.class.declaration)))?;
    for _ in &plan.class.methods {
        let mut signatures = Vec::new();
        signatures
            .try_reserve_exact(1)
            .map_err(|_| invariant(ClassInvariant::Capacity(plan.class.declaration)))?;
        signature_lists.push(signatures);
    }
    Ok(signature_lists)
}

fn publish_class_methods(
    store: &mut CanonicalTypeMapperStore,
    plan: &ClassMemberPlan,
    signature_lists: Vec<Vec<SignatureId>>,
) {
    for ((method, return_type), mut signatures) in plan
        .class
        .methods
        .iter()
        .zip(&plan.method_return_types)
        .zip(signature_lists)
    {
        if exact_method_callable(store, method, *return_type).is_some() {
            if let Some(type_node) = method.return_type_node {
                assert!(store.set_type_node_links(
                    type_node,
                    TypeNodeLinks {
                        resolved_type: Some(*return_type),
                        ..TypeNodeLinks::default()
                    },
                ));
            }
            continue;
        }

        let method_type = store
            .alloc_plain_object_type(ObjectFlags::ANONYMOUS, Some(method.symbol))
            .expect("the class transaction reserved the method value identity");
        let signature = store
            .alloc_signature(
                SignatureFlags::NONE,
                Some(method.declaration),
                Vec::new(),
                None,
                Vec::new(),
                Some(*return_type),
                None,
                0,
            )
            .expect("the class transaction reserved the method signature");
        signatures.push(signature);
        if let Some(type_node) = method.return_type_node {
            assert!(store.set_type_node_links(
                type_node,
                TypeNodeLinks {
                    resolved_type: Some(*return_type),
                    ..TypeNodeLinks::default()
                },
            ));
        }
        assert!(store.set_signature_links(
            method.declaration,
            SignatureLinks {
                resolved_signature: ResolvedSignatureState::Resolved(signature),
                ..SignatureLinks::default()
            },
        ));
        assert!(store.set_value_symbol_links(
            method.symbol,
            ValueSymbolLinks {
                resolved_type: Some(method_type),
                ..ValueSymbolLinks::default()
            },
        ));
        assert!(store.set_structured_type_members(
            method_type,
            None,
            None,
            Some(signatures),
            None,
            None,
        ));
    }
}

/// Installs the exact primitive-property member graph and default constructor
/// for a previously preflighted class.
///
/// All typed checks, owned allocations, sparse-link capacity, and member-table
/// entry capacity are staged before the shell executor can publish the first
/// class identity. Static structured members are the final commit point.
pub(super) fn execute_nongeneric_class_members(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    plan: &ClassMemberPlan,
) -> Result<ClassMembers, ClassError> {
    if let Some(members) = validated_nongeneric_class_member_state(store, host, plan)? {
        return Ok(members);
    }
    let shell = shell_state(store, host, &plan.class)?;
    let cold_instance = shell.instance.is_none();
    let cold_value = matches!(shell.value, StaticShellState::Cold);
    let additional_types = usize::from(cold_value)
        .checked_add(usize::from(cold_instance) * 2)
        .and_then(|count| count.checked_add(plan.class.methods.len()))
        .ok_or_else(|| invariant(ClassInvariant::Capacity(plan.class.declaration)))?;

    let prototype = prototype_symbol(store, &plan.class)
        .ok_or_else(|| invariant(ClassInvariant::InvalidPrototype(plan.class.symbol)))?;
    let planned_instance_entries = planned_class_member_entries(
        &plan.class.instance_properties,
        &plan.class.instance_methods,
    );
    let planned_static_entries =
        planned_class_member_entries(&plan.class.static_properties, &plan.class.static_methods);
    let prepared_instance_members = if planned_instance_entries.is_empty() {
        None
    } else {
        Some(
            PreparedSymbolTable::new(planned_instance_entries.len())
                .ok_or_else(|| invariant(ClassInvariant::Capacity(plan.class.declaration)))?,
        )
    };

    let mut instance_properties = Vec::new();
    let mut instance_member_entries = Vec::new();
    let mut static_properties = Vec::new();
    let mut all_static_properties = Vec::new();
    let mut construct_signatures = Vec::new();
    let mut declared_index_infos = Vec::new();
    let mut resolved_index_infos = Vec::new();
    let method_signature_lists = prepare_class_method_signatures(plan)?;
    instance_properties
        .try_reserve_exact(planned_instance_entries.len())
        .map_err(|_| invariant(ClassInvariant::Capacity(plan.class.declaration)))?;
    instance_member_entries
        .try_reserve_exact(planned_instance_entries.len())
        .map_err(|_| invariant(ClassInvariant::Capacity(plan.class.declaration)))?;
    static_properties
        .try_reserve_exact(planned_static_entries.len())
        .map_err(|_| invariant(ClassInvariant::Capacity(plan.class.declaration)))?;
    all_static_properties
        .try_reserve_exact(
            planned_static_entries
                .len()
                .checked_add(1)
                .ok_or_else(|| invariant(ClassInvariant::Capacity(plan.class.declaration)))?,
        )
        .map_err(|_| invariant(ClassInvariant::Capacity(plan.class.declaration)))?;
    construct_signatures
        .try_reserve_exact(1)
        .map_err(|_| invariant(ClassInvariant::Capacity(plan.class.declaration)))?;
    declared_index_infos
        .try_reserve_exact(usize::from(plan.class.index.is_some()))
        .map_err(|_| invariant(ClassInvariant::Capacity(plan.class.declaration)))?;
    resolved_index_infos
        .try_reserve_exact(usize::from(plan.class.index.is_some()))
        .map_err(|_| invariant(ClassInvariant::Capacity(plan.class.declaration)))?;
    instance_properties.extend(planned_instance_entries.iter().map(|(_, symbol)| *symbol));
    instance_member_entries.extend(planned_instance_entries);
    static_properties.extend(planned_static_entries.iter().map(|(_, symbol)| *symbol));
    all_static_properties.extend_from_slice(&static_properties);
    all_static_properties.push(prototype);

    let missing_property_type_node_links = plan
        .class
        .properties
        .iter()
        .filter(|property| store.type_node_links(property.type_node).is_none())
        .count();
    let missing_method_type_node_links = plan
        .class
        .methods
        .iter()
        .filter_map(|method| method.return_type_node)
        .filter(|type_node| store.type_node_links(*type_node).is_none())
        .count();
    let missing_index_type_node_links = plan.class.index.map_or(0, |index| {
        [index.key_type_node, index.value_type_node]
            .into_iter()
            .filter(|type_node| store.type_node_links(*type_node).is_none())
            .count()
    });
    let missing_type_node_links = missing_property_type_node_links
        .checked_add(missing_method_type_node_links)
        .and_then(|count| count.checked_add(missing_index_type_node_links))
        .ok_or_else(|| invariant(ClassInvariant::Capacity(plan.class.declaration)))?;
    let missing_property_value_links = plan
        .class
        .properties
        .iter()
        .filter(|property| store.value_symbol_links(property.symbol).is_none())
        .count();
    let missing_owner_value_link =
        usize::from(store.value_symbol_links(plan.class.symbol).is_none());
    let missing_method_value_links = plan
        .class
        .methods
        .iter()
        .filter(|method| store.value_symbol_links(method.symbol).is_none())
        .count();
    let missing_constructor_signature_links = usize::from(
        plan.class
            .constructor
            .is_some_and(|constructor| store.signature_links(constructor.declaration).is_none()),
    );
    let missing_method_signature_links = plan
        .class
        .methods
        .iter()
        .filter(|method| store.signature_links(method.declaration).is_none())
        .count();
    let missing_signature_links = missing_constructor_signature_links
        .checked_add(missing_method_signature_links)
        .ok_or_else(|| invariant(ClassInvariant::Capacity(plan.class.declaration)))?;
    let missing_value_links = missing_property_value_links
        .checked_add(missing_owner_value_link)
        .and_then(|count| count.checked_add(missing_method_value_links))
        .ok_or_else(|| invariant(ClassInvariant::Capacity(plan.class.declaration)))?;
    let signature_count = plan
        .class
        .methods
        .len()
        .checked_add(1)
        .ok_or_else(|| invariant(ClassInvariant::Capacity(plan.class.declaration)))?;
    if !store.try_reserve_types(additional_types)
        || !store.try_reserve_signatures(signature_count)
        || !store.try_reserve_index_infos(usize::from(plan.class.index.is_some()))
        || !store.try_reserve_checker_symbol_allocations(
            0,
            usize::from(prepared_instance_members.is_some()),
        )
        || !store.try_reserve_type_node_links(missing_type_node_links)
        || !store.try_reserve_value_symbol_links(missing_value_links)
        || !store.try_reserve_signature_links(missing_signature_links)
    {
        return Err(invariant(ClassInvariant::Capacity(plan.class.declaration)));
    }

    let shells = execute_nongeneric_class_shells(store, host, &plan.class)?;
    let instance_members = prepared_instance_members.map(|prepared| {
        let table = store.alloc_prepared_symbol_table(prepared);
        for (name, symbol) in instance_member_entries {
            assert_eq!(store.insert_symbol(table, name, symbol), Some(None),);
        }
        table
    });
    let default_construct_signature = plan
        .class
        .constructor
        .and_then(|constructor| store.signature_links(constructor.declaration))
        .and_then(|links| links.resolved_signature.signature())
        .unwrap_or_else(|| {
            store
                .alloc_signature(
                    SignatureFlags::CONSTRUCT,
                    plan.constructor_declaration(),
                    Vec::new(),
                    None,
                    Vec::new(),
                    Some(shells.instance_type),
                    None,
                    0,
                )
                .expect("the class-member transaction reserved one exact default signature")
        });
    construct_signatures.push(default_construct_signature);
    if let Some(constructor) = plan.class.constructor {
        assert!(store.set_signature_links(
            constructor.declaration,
            SignatureLinks {
                resolved_signature: ResolvedSignatureState::Resolved(default_construct_signature),
                ..SignatureLinks::default()
            },
        ));
    }

    for (property, property_type) in plan.class.properties.iter().zip(&plan.property_types) {
        assert!(store.set_type_node_links(
            property.type_node,
            TypeNodeLinks {
                resolved_type: Some(*property_type),
                ..TypeNodeLinks::default()
            },
        ));
        assert!(store.set_source_property_readonly(property.symbol, property.readonly,));
        assert!(store.set_value_symbol_links(
            property.symbol,
            ValueSymbolLinks {
                resolved_type: Some(*property_type),
                ..ValueSymbolLinks::default()
            },
        ));
    }
    if let Some(index) = plan.class.index {
        let (key_type, value_type) = plan
            .index_types
            .expect("an admitted class index retains both resolved keyword types");
        assert!(store.set_type_node_links(
            index.key_type_node,
            TypeNodeLinks {
                resolved_type: Some(key_type),
                ..TypeNodeLinks::default()
            },
        ));
        assert!(store.set_type_node_links(
            index.value_type_node,
            TypeNodeLinks {
                resolved_type: Some(value_type),
                ..TypeNodeLinks::default()
            },
        ));
        let info = store
            .alloc_index_info(
                key_type,
                value_type,
                false,
                Some(index.declaration),
                Vec::new(),
            )
            .expect("the class transaction reserved its validated index information");
        declared_index_infos.push(info);
        resolved_index_infos.push(info);
    }
    publish_class_methods(store, plan, method_signature_lists);
    assert!(store.set_interface_declared_members(
        shells.instance_type,
        true,
        plan.class.instance_members,
        None,
        None,
        (!declared_index_infos.is_empty()).then_some(declared_index_infos),
    ));
    let undefined_type = store
        .intrinsic_bootstrap()
        .expect("the member plan validated intrinsic bootstrap")
        .undefined_type;
    assert!(store.set_interface_base_resolution(
        shells.instance_type,
        true,
        Some(undefined_type),
        None,
    ));
    assert!(store.set_structured_type_members(
        shells.instance_type,
        instance_members,
        (!instance_properties.is_empty()).then_some(instance_properties),
        None,
        None,
        (!resolved_index_infos.is_empty()).then_some(resolved_index_infos),
    ));
    assert!(store.set_structured_type_members(
        shells.value_type,
        Some(plan.class.static_members),
        Some(all_static_properties),
        None,
        Some(construct_signatures),
        None,
    ));

    Ok(completed_class_members(
        store,
        plan,
        shells.instance_type,
        shells.value_type,
    )
    .unwrap_or_else(|| {
        panic!(
            "the fully preflighted class-member transaction published an invalid final graph"
        )
    }))
}

fn exact_cold_derived_instance(
    store: &CanonicalTypeMapperStore,
    plan: &ClassMemberPlan,
    instance_type: TypeId,
) -> bool {
    let Some(instance) = exact_instance_identity(store, &plan.class, instance_type) else {
        return false;
    };
    store.type_payload(instance_type).is_some_and(|record| {
        record.object_flags() == (ObjectFlags::CLASS | ObjectFlags::REFERENCE)
    }) && !instance.base_types_resolved
        && instance.resolved_base_constructor_type.is_none()
        && instance.resolved_base_types.is_none()
        && !instance.declared_members_resolved
        && instance.declared_members.is_none()
        && instance.declared_call_signatures.is_none()
        && instance.declared_construct_signatures.is_none()
        && instance.declared_index_infos.is_none()
        && instance.reference.object.structured == StructuredTypeData::default()
}

fn exact_optional_class_value(
    store: &CanonicalTypeMapperStore,
    symbol: SemanticSymbolId,
) -> Result<Option<TypeId>, ClassError> {
    match store.value_symbol_links(symbol) {
        None => Ok(None),
        Some(links) if links == &ValueSymbolLinks::default() => Ok(None),
        Some(links) => {
            let Some(type_) = links.resolved_type else {
                return Err(invariant(ClassInvariant::InvalidValueCache(symbol)));
            };
            if links
                != &(ValueSymbolLinks {
                    resolved_type: Some(type_),
                    ..ValueSymbolLinks::default()
                })
            {
                return Err(invariant(ClassInvariant::InvalidValueCache(symbol)));
            }
            Ok(Some(type_))
        }
    }
}

fn derived_class_member_state(
    store: &CanonicalTypeMapperStore,
    plan: &ClassMemberPlan,
    base: Option<&ClassMembers>,
    surfaces: &DerivedMemberSurfaces,
) -> Result<Option<ClassMembers>, ClassError> {
    let instance = store
        .declared_type_links(plan.class.symbol)
        .and_then(|links| links.declared_type);
    let value = exact_optional_class_value(store, plan.class.symbol)?;
    if let (Some(instance), Some(value), Some(base)) = (instance, value, base)
        && let Some(members) =
            completed_derived_class_members(store, plan, base, instance, value, surfaces)
    {
        return Ok(Some(members));
    }
    if instance.is_some_and(|instance| store.direct_class_heritage_provenance(instance).is_some())
        || value.is_some()
        || instance.is_some_and(|instance| !exact_cold_derived_instance(store, plan, instance))
    {
        return Err(invariant(ClassInvariant::InvalidHeritageCache(
            plan.class.symbol,
        )));
    }
    Ok(None)
}

fn execute_direct_derived_class_members(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    plan: &ClassMemberPlan,
    base_plan: &ClassMemberPlan,
) -> Result<ClassMembers, ClassError> {
    let surfaces = prepare_derived_member_surfaces(store, plan, base_plan)?;
    let base_state = validated_nongeneric_class_member_state(store, host, base_plan)?;
    if let Some(members) = derived_class_member_state(store, plan, base_state.as_ref(), &surfaces)?
    {
        return Ok(members);
    }
    let DerivedMemberSurfaces {
        instance_entries: insertion_instance_entries,
        instance_properties: insertion_instance_properties,
        static_entries: insertion_static_entries,
        static_properties: _,
    } = surfaces.clone();

    let prototype = prototype_symbol(store, &plan.class)
        .ok_or_else(|| invariant(ClassInvariant::InvalidPrototype(plan.class.symbol)))?;
    let prepared_instance_members = if surfaces.instance_entries.is_empty() {
        None
    } else {
        Some(
            PreparedSymbolTable::new(surfaces.instance_entries.len())
                .ok_or_else(|| invariant(ClassInvariant::Capacity(plan.class.declaration)))?,
        )
    };
    let prepared_static_members = PreparedSymbolTable::new(surfaces.static_entries.len())
        .ok_or_else(|| invariant(ClassInvariant::Capacity(plan.class.declaration)))?;
    let mut all_static_properties = Vec::new();
    all_static_properties
        .try_reserve_exact(
            surfaces
                .static_properties
                .len()
                .checked_add(1)
                .ok_or_else(|| invariant(ClassInvariant::Capacity(plan.class.declaration)))?,
        )
        .map_err(|_| invariant(ClassInvariant::Capacity(plan.class.declaration)))?;
    all_static_properties.extend_from_slice(&surfaces.static_properties);
    all_static_properties.push(prototype);
    let mut resolved_base_types = Vec::new();
    resolved_base_types
        .try_reserve_exact(1)
        .map_err(|_| invariant(ClassInvariant::Capacity(plan.class.declaration)))?;
    let mut construct_signatures = Vec::new();
    construct_signatures
        .try_reserve_exact(1)
        .map_err(|_| invariant(ClassInvariant::Capacity(plan.class.declaration)))?;
    let method_signature_lists = prepare_class_method_signatures(plan)?;

    let missing_declared_links = [plan, base_plan]
        .into_iter()
        .filter(|plan| store.declared_type_links(plan.class.symbol).is_none())
        .count();
    let missing_property_type_node_links = plan
        .class
        .properties
        .iter()
        .chain(&base_plan.class.properties)
        .filter(|property| store.type_node_links(property.type_node).is_none())
        .count();
    let missing_method_type_node_links = plan
        .class
        .methods
        .iter()
        .chain(&base_plan.class.methods)
        .filter_map(|method| method.return_type_node)
        .filter(|node| store.type_node_links(*node).is_none())
        .count();
    let missing_type_node_links = missing_property_type_node_links
        .checked_add(missing_method_type_node_links)
        .ok_or_else(|| invariant(ClassInvariant::Capacity(plan.class.declaration)))?;
    let missing_property_value_links = plan
        .class
        .properties
        .iter()
        .chain(&base_plan.class.properties)
        .map(|property| property.symbol)
        .chain([plan.class.symbol, base_plan.class.symbol])
        .filter(|symbol| store.value_symbol_links(*symbol).is_none())
        .count();
    let missing_method_value_links = plan
        .class
        .methods
        .iter()
        .chain(&base_plan.class.methods)
        .filter(|method| store.value_symbol_links(method.symbol).is_none())
        .count();
    let missing_value_links = missing_property_value_links
        .checked_add(missing_method_value_links)
        .ok_or_else(|| invariant(ClassInvariant::Capacity(plan.class.declaration)))?;
    let missing_constructor_signature_links = [plan.class.constructor, base_plan.class.constructor]
        .into_iter()
        .flatten()
        .filter(|constructor| store.signature_links(constructor.declaration).is_none())
        .count();
    let missing_method_signature_links = plan
        .class
        .methods
        .iter()
        .chain(&base_plan.class.methods)
        .filter(|method| store.signature_links(method.declaration).is_none())
        .count();
    let missing_signature_links = missing_constructor_signature_links
        .checked_add(missing_method_signature_links)
        .ok_or_else(|| invariant(ClassInvariant::Capacity(plan.class.declaration)))?;
    let method_count = plan
        .class
        .methods
        .len()
        .checked_add(base_plan.class.methods.len())
        .ok_or_else(|| invariant(ClassInvariant::Capacity(plan.class.declaration)))?;
    let type_count = method_count
        .checked_add(6)
        .ok_or_else(|| invariant(ClassInvariant::Capacity(plan.class.declaration)))?;
    let signature_count = method_count
        .checked_add(2)
        .ok_or_else(|| invariant(ClassInvariant::Capacity(plan.class.declaration)))?;
    if !store.try_reserve_types(type_count)
        || !store.try_reserve_signatures(signature_count)
        || !store.try_reserve_checker_symbol_allocations(
            0,
            2 + usize::from(
                !base_plan.class.instance_properties.is_empty()
                    || !base_plan.class.instance_methods.is_empty(),
            ),
        )
        || !store.try_reserve_declared_type_links(missing_declared_links)
        || !store.try_reserve_type_node_links(missing_type_node_links)
        || !store.try_reserve_value_symbol_links(missing_value_links)
        || !store.try_reserve_signature_links(missing_signature_links)
        || !store.try_reserve_direct_class_heritage_provenance(1)
    {
        return Err(invariant(ClassInvariant::Capacity(plan.class.declaration)));
    }

    // The dependency completes first, but every derived allocation, sparse
    // link, table entry, and retained edge has already been staged. No
    // fallible work remains after this call.
    let base = execute_nongeneric_class_members(store, host, base_plan)
        .expect("the aggregate class preflight made base execution infallible");
    let instance_type = store
        .get_declared_type_of_symbol(host, plan.class.symbol)
        .expect("the aggregate class preflight made derived identity publication infallible");
    let value_type = store
        .alloc_plain_object_type(ObjectFlags::ANONYMOUS, Some(plan.class.symbol))
        .expect("the aggregate class transaction reserved the derived value type");
    let instance_members = prepared_instance_members.map(|prepared| {
        let table = store.alloc_prepared_symbol_table(prepared);
        for (name, symbol) in insertion_instance_entries {
            assert_eq!(store.insert_symbol(table, name, symbol), Some(None),);
        }
        table
    });
    let static_members = store.alloc_prepared_symbol_table(prepared_static_members);
    for (name, symbol) in insertion_static_entries {
        assert_eq!(
            store.insert_symbol(static_members, name, symbol),
            Some(None),
        );
    }
    let inherited_constructor_declaration = store
        .signature(base.default_construct_signature)
        .and_then(super::signatures::Signature::declaration);
    let default_construct_signature = store
        .alloc_signature(
            SignatureFlags::CONSTRUCT,
            inherited_constructor_declaration,
            Vec::new(),
            None,
            Vec::new(),
            Some(instance_type),
            None,
            0,
        )
        .expect("the aggregate class transaction reserved the derived signature");
    construct_signatures.push(default_construct_signature);
    resolved_base_types.push(base.shells.instance_type);

    // Pinned `getTypeOfFuncClassEnumModuleWorker` allocates the value shell
    // before forcing the base-constructor cache.
    assert!(store.set_interface_base_resolution(
        instance_type,
        false,
        Some(base.shells.value_type),
        None,
    ));
    assert!(store.set_value_symbol_links(
        plan.class.symbol,
        ValueSymbolLinks {
            resolved_type: Some(value_type),
            ..ValueSymbolLinks::default()
        },
    ));
    for (property, property_type) in plan.class.properties.iter().zip(&plan.property_types) {
        assert!(store.set_type_node_links(
            property.type_node,
            TypeNodeLinks {
                resolved_type: Some(*property_type),
                ..TypeNodeLinks::default()
            },
        ));
        assert!(store.set_source_property_readonly(property.symbol, property.readonly,));
        assert!(store.set_value_symbol_links(
            property.symbol,
            ValueSymbolLinks {
                resolved_type: Some(*property_type),
                ..ValueSymbolLinks::default()
            },
        ));
    }
    publish_class_methods(store, plan, method_signature_lists);
    assert!(store.set_interface_declared_members(
        instance_type,
        true,
        plan.class.instance_members,
        None,
        None,
        None,
    ));
    assert!(store.set_interface_base_resolution(
        instance_type,
        true,
        Some(base.shells.value_type),
        Some(resolved_base_types),
    ));
    assert!(store.set_structured_type_members(
        instance_type,
        instance_members,
        (!insertion_instance_properties.is_empty()).then_some(insertion_instance_properties),
        None,
        None,
        None,
    ));
    assert!(store.publish_direct_class_heritage_provenance(
        instance_type,
        DirectClassHeritageProvenance {
            owner_symbol: plan.class.symbol,
            owner_value_type: value_type,
            base_symbol: base.shells.symbol,
            base_instance_type: base.shells.instance_type,
            base_value_type: base.shells.value_type,
        },
    ));
    assert!(store.set_structured_type_members(
        value_type,
        Some(static_members),
        Some(all_static_properties),
        None,
        Some(construct_signatures),
        None,
    ));
    completed_derived_class_members(store, plan, &base, instance_type, value_type, &surfaces)
        .ok_or_else(|| invariant(ClassInvariant::Publication(plan.class.declaration)))
}

/// Executes the shared public-query and whole-source member domain.
pub(super) fn execute_nongeneric_class_member_query(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    plan: &ClassMemberQueryPlan,
) -> Result<ClassMembers, ClassError> {
    let current = plan_nongeneric_class_member_query(
        store,
        host,
        match plan {
            ClassMemberQueryPlan::Direct(plan)
            | ClassMemberQueryPlan::Derived { class: plan, .. } => plan.class.symbol,
        },
    )?;
    if current != *plan {
        return Err(invariant(ClassInvariant::InvalidPlan(match plan {
            ClassMemberQueryPlan::Direct(plan)
            | ClassMemberQueryPlan::Derived { class: plan, .. } => plan.class.declaration,
        })));
    }
    match plan {
        ClassMemberQueryPlan::Direct(plan) => execute_nongeneric_class_members(store, host, plan),
        ClassMemberQueryPlan::Derived { class, base } => {
            execute_direct_derived_class_members(store, host, class, base)
        }
    }
}

/// Revalidates one exact direct-base or no-base class member query without
/// publishing either class identity or any inherited member surface.
pub(super) fn preflight_nongeneric_class_member_query(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    plan: &ClassMemberQueryPlan,
) -> Result<(), ClassError> {
    let current = plan_nongeneric_class_member_query(store, host, plan.symbol())?;
    if current != *plan {
        return Err(invariant(ClassInvariant::InvalidPlan(plan.declaration())));
    }
    match plan {
        ClassMemberQueryPlan::Direct(plan) => {
            validated_nongeneric_class_member_state(store, host, plan).map(drop)
        }
        ClassMemberQueryPlan::Derived { class, base } => {
            let surfaces = prepare_derived_member_surfaces(store, class, base)?;
            let base_state = validated_nongeneric_class_member_state(store, host, base)?;
            derived_class_member_state(store, class, base_state.as_ref(), &surfaces).map(drop)
        }
    }
}

/// Store-only proof used before any relation-cache read involving a class.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum ClassHeritageMembersValidation {
    NotClass,
    Valid,
    Malformed,
}

struct StoredClassParts {
    symbol: SemanticSymbolId,
    instance: super::type_records::InterfaceTypeData,
    value_type: TypeId,
    value: ObjectTypeData,
    index: Option<StoredClassIndex>,
    declared_instance_properties: Vec<SemanticSymbolId>,
    declared_static_properties: Vec<SemanticSymbolId>,
    prototype: SemanticSymbolId,
}

struct StoredClassSurface {
    parts: StoredClassParts,
    instance_properties: Vec<SemanticSymbolId>,
    static_properties: Vec<SemanticSymbolId>,
}

#[derive(Clone, Copy)]
struct StoredClassIndex {
    symbol: SemanticSymbolId,
    info: IndexInfoId,
}

#[derive(Clone, Copy)]
enum StoredClassIndexState {
    Absent,
    Present(StoredClassIndex),
}

fn exact_stored_property(
    store: &CanonicalTypeMapperStore,
    owner: SemanticSymbolId,
    owner_declaration: NodeRef,
    property: SemanticSymbolId,
) -> Option<NodeRef> {
    let record = store.symbol(property)?;
    let [declaration] = record.declarations()? else {
        return None;
    };
    let flags = record.flags();
    let check_flags = record.check_flags();
    let links = store.value_symbol_links(property)?;
    let property_type = links.resolved_type?;
    let bootstrap = store.intrinsic_bootstrap()?;
    let primitive = [
        bootstrap.any_type,
        bootstrap.unknown_type,
        bootstrap.string_type,
        bootstrap.number_type,
        bootstrap.bigint_type,
        bootstrap.boolean_type,
        bootstrap.es_symbol_type,
        bootstrap.void_type,
        bootstrap.undefined_type,
        bootstrap.never_type,
        bootstrap.non_primitive_type,
    ]
    .contains(&property_type);
    ((flags == SymbolFlags::PROPERTY || flags == (SymbolFlags::PROPERTY | SymbolFlags::OPTIONAL))
        && matches!(check_flags, CheckFlags::NONE | CheckFlags::READONLY)
        && record.value_declaration() == Some(*declaration)
        && record.members().is_none()
        && record.exports().is_none()
        && record.parent() == Some(owner)
        && record.export_symbol().is_none()
        && store.get_merged_symbol(property) == Some(property)
        && store.source_node_kind(*declaration) == Some(SyntaxKind::PropertyDeclaration)
        && store.source_node_parent(*declaration)
            == Some(SourceNodeParent::Parent(owner_declaration))
        && store
            .source_primitive_type_annotation(*declaration)
            .is_some_and(|annotation| {
                store.source_type_node_result_is_exact(annotation, property_type, &[])
            })
        && links
            == &(ValueSymbolLinks {
                resolved_type: Some(property_type),
                ..ValueSymbolLinks::default()
            })
        && primitive)
        .then_some(*declaration)
}

fn exact_stored_method_return_type(
    store: &CanonicalTypeMapperStore,
    declaration: NodeRef,
    return_type: TypeId,
) -> bool {
    // Empty class method bodies follow the optional return annotation in the arena.
    let Some(body_index) = declaration
        .node
        .index()
        .checked_sub(1)
        .and_then(|index| u32::try_from(index).ok())
    else {
        return false;
    };
    let body = NodeRef::new(
        declaration.arena,
        declaration.file,
        ts_ast::NodeId::new(body_index),
    );
    if store.source_node_kind(body) != Some(SyntaxKind::Block)
        || store.source_node_parent(body) != Some(SourceNodeParent::Parent(declaration))
    {
        return false;
    }
    let Some(previous_index) = body
        .node
        .index()
        .checked_sub(1)
        .and_then(|index| u32::try_from(index).ok())
    else {
        return false;
    };
    let previous = NodeRef::new(
        declaration.arena,
        declaration.file,
        ts_ast::NodeId::new(previous_index),
    );
    if store.source_node_parent(previous) != Some(SourceNodeParent::Parent(declaration)) {
        return false;
    }
    match store.source_node_kind(previous) {
        Some(SyntaxKind::Identifier) => store
            .intrinsic_bootstrap()
            .is_some_and(|bootstrap| return_type == bootstrap.void_type),
        Some(SyntaxKind::VoidKeyword | SyntaxKind::AnyKeyword | SyntaxKind::UndefinedKeyword) => {
            store.type_node_links(previous)
                == Some(&TypeNodeLinks {
                    resolved_type: Some(return_type),
                    ..TypeNodeLinks::default()
                })
                && store.source_type_node_result_is_exact(previous, return_type, &[])
        }
        _ => false,
    }
}

fn exact_stored_method(
    store: &CanonicalTypeMapperStore,
    owner: SemanticSymbolId,
    owner_declaration: NodeRef,
    method: SemanticSymbolId,
) -> Option<NodeRef> {
    let record = store.symbol(method)?;
    let [declaration] = record.declarations()? else {
        return None;
    };
    let links = store.value_symbol_links(method)?;
    let method_type = links.resolved_type?;
    let structured = store.type_payload(method_type)?.data().structured()?;
    let [signature] = structured.signatures.as_deref()? else {
        return None;
    };
    let return_type = store.signature(*signature)?.resolved_return_type()?;
    (record.flags() == SymbolFlags::METHOD
        && record.check_flags() == CheckFlags::NONE
        && record.value_declaration() == Some(*declaration)
        && record.members().is_none()
        && record.exports().is_none()
        && record.parent() == Some(owner)
        && record.export_symbol().is_none()
        && store.get_merged_symbol(method) == Some(method)
        && store.source_node_kind(*declaration) == Some(SyntaxKind::MethodDeclaration)
        && store.source_node_parent(*declaration)
            == Some(SourceNodeParent::Parent(owner_declaration))
        && exact_stored_method_return_type(store, *declaration, return_type)
        && exact_method_value(store, method, *declaration, return_type)
            == Some((method_type, *signature)))
    .then_some(*declaration)
}

fn exact_stored_class_member(
    store: &CanonicalTypeMapperStore,
    owner: SemanticSymbolId,
    owner_declaration: NodeRef,
    member: SemanticSymbolId,
) -> Option<NodeRef> {
    if store.symbol(member)?.flags() == SymbolFlags::METHOD {
        exact_stored_method(store, owner, owner_declaration, member)
    } else {
        exact_stored_property(store, owner, owner_declaration, member)
    }
}

#[derive(Clone, Copy)]
enum StoredClassConstructor {
    Absent,
    Present {
        symbol: SemanticSymbolId,
        declaration: NodeRef,
    },
}

impl StoredClassConstructor {
    const fn symbol(self) -> Option<SemanticSymbolId> {
        match self {
            Self::Absent => None,
            Self::Present { symbol, .. } => Some(symbol),
        }
    }

    const fn declaration(self) -> Option<NodeRef> {
        match self {
            Self::Absent => None,
            Self::Present { declaration, .. } => Some(declaration),
        }
    }
}

fn stored_class_constructor(
    store: &CanonicalTypeMapperStore,
    owner: SemanticSymbolId,
    owner_declaration: NodeRef,
    table: Option<SymbolTableId>,
) -> Option<StoredClassConstructor> {
    let Some(table) = table else {
        return Some(StoredClassConstructor::Absent);
    };
    let table = store.symbol_table(table)?;
    let Some(symbol) = table.get(InternalSymbolName::Constructor.as_ref()) else {
        return Some(StoredClassConstructor::Absent);
    };
    let record = store.symbol(symbol)?;
    let [declaration] = record.declarations()? else {
        return None;
    };
    (record.flags() == SymbolFlags::CONSTRUCTOR
        && record.check_flags() == CheckFlags::NONE
        && record.name() == InternalSymbolName::Constructor.as_ref()
        && record.value_declaration().is_none()
        && record.members().is_none()
        && record.exports().is_none()
        && record.parent() == Some(owner)
        && record.export_symbol().is_none()
        && store.get_merged_symbol(symbol) == Some(symbol)
        && store.source_node_kind(*declaration) == Some(SyntaxKind::Constructor)
        && store.source_node_parent(*declaration)
            == Some(SourceNodeParent::Parent(owner_declaration)))
    .then_some(StoredClassConstructor::Present {
        symbol,
        declaration: *declaration,
    })
}

fn stored_class_index(
    store: &CanonicalTypeMapperStore,
    owner: SemanticSymbolId,
    owner_declaration: NodeRef,
    members: Option<SymbolTableId>,
    indexes: Option<&[IndexInfoId]>,
) -> Option<StoredClassIndexState> {
    let Some(members) = members else {
        return indexes.is_none().then_some(StoredClassIndexState::Absent);
    };
    let table = store.symbol_table(members)?;
    let symbol = table.get(InternalSymbolName::Index.as_ref());
    match (symbol, indexes) {
        (None, None) => Some(StoredClassIndexState::Absent),
        (Some(symbol), Some([info])) => {
            let symbol_record = store.symbol(symbol)?;
            let [declaration] = symbol_record.declarations()? else {
                return None;
            };
            let index = store.index_info(*info)?;
            let bootstrap = store.intrinsic_bootstrap()?;
            (symbol_record.flags() == SymbolFlags::SIGNATURE
                && symbol_record.check_flags() == CheckFlags::NONE
                && symbol_record.name() == InternalSymbolName::Index.as_ref()
                && symbol_record.value_declaration().is_none()
                && symbol_record.members().is_none()
                && symbol_record.exports().is_none()
                && symbol_record.parent() == Some(owner)
                && symbol_record.export_symbol().is_none()
                && store.get_merged_symbol(symbol) == Some(symbol)
                && store.source_node_kind(*declaration) == Some(SyntaxKind::IndexSignature)
                && store.source_node_parent(*declaration)
                    == Some(SourceNodeParent::Parent(owner_declaration))
                && index.key_type() == bootstrap.string_type
                && index.value_type() == bootstrap.number_type
                && !index.is_readonly()
                && index.declaration() == Some(*declaration)
                && index.index_symbol().is_none()
                && index.components().is_empty())
            .then_some(StoredClassIndexState::Present(StoredClassIndex {
                symbol,
                info: *info,
            }))
        }
        _ => None,
    }
}

fn stored_declared_properties(
    store: &CanonicalTypeMapperStore,
    owner: SemanticSymbolId,
    owner_declaration: NodeRef,
    table: Option<SymbolTableId>,
    prototype: Option<SemanticSymbolId>,
    constructor: Option<SemanticSymbolId>,
    index: Option<SemanticSymbolId>,
) -> Option<Vec<SemanticSymbolId>> {
    let Some(table) = table else {
        return (prototype.is_none() && constructor.is_none() && index.is_none()).then(Vec::new);
    };
    let table = store.symbol_table(table)?;
    if table.is_empty() && prototype.is_none() {
        return None;
    }
    let mut properties = Vec::new();
    properties.try_reserve_exact(table.len()).ok()?;
    for (name, property) in table.iter() {
        if store.symbol(property)?.name() != name {
            return None;
        }
        if Some(property) == prototype || Some(property) == constructor || Some(property) == index {
            continue;
        }
        exact_stored_class_member(store, owner, owner_declaration, property)?;
        properties.push(property);
    }
    properties.sort_unstable_by_key(|property| {
        exact_stored_class_member(store, owner, owner_declaration, *property)
            .expect("validated class member retains one declaration")
    });
    if properties.windows(2).any(|pair| {
        exact_stored_class_member(store, owner, owner_declaration, pair[0])
            >= exact_stored_class_member(store, owner, owner_declaration, pair[1])
    }) {
        return None;
    }
    let expected_len = properties
        .len()
        .checked_add(usize::from(prototype.is_some()))?
        .checked_add(usize::from(constructor.is_some()))?
        .checked_add(usize::from(index.is_some()))?;
    (table.len() == expected_len).then_some(properties)
}

fn stored_class_parts(
    store: &CanonicalTypeMapperStore,
    instance_type: TypeId,
) -> Option<StoredClassParts> {
    let record = store.type_payload(instance_type)?;
    let symbol = record.symbol()?;
    let instance = exact_class_instance_identity(store, symbol, instance_type)?.clone();
    let owner = store.symbol(symbol)?;
    let [declaration] = owner.declarations()? else {
        return None;
    };
    let declaration = *declaration;
    if record.object_flags()
        != (ObjectFlags::CLASS | ObjectFlags::REFERENCE | ObjectFlags::MEMBERS_RESOLVED)
        || owner.flags() != SymbolFlags::CLASS
        || owner.check_flags() != CheckFlags::NONE
        || owner.value_declaration() != Some(declaration)
        || owner.parent().is_some()
        || owner.export_symbol().is_some()
        || store.get_merged_symbol(symbol) != Some(symbol)
        || store.source_node_kind(declaration) != Some(SyntaxKind::ClassDeclaration)
        || store
            .declared_type_links(symbol)
            .is_none_or(|links| links.declared_type != Some(instance_type))
        || !instance.declared_members_resolved
        || instance.declared_members != owner.members()
        || instance.declared_call_signatures.is_some()
        || instance.declared_construct_signatures.is_some()
    {
        return None;
    }
    let exports = owner.exports()?;
    validate_prototype(store, symbol, exports).ok()?;
    let prototype = store.symbol_table(exports)?.get_source(PROTOTYPE_NAME)?;
    let constructor = stored_class_constructor(store, symbol, declaration, owner.members())?;
    let index = match stored_class_index(
        store,
        symbol,
        declaration,
        owner.members(),
        instance.declared_index_infos.as_deref(),
    )? {
        StoredClassIndexState::Absent => None,
        StoredClassIndexState::Present(index) => Some(index),
    };
    let declared_instance_properties = stored_declared_properties(
        store,
        symbol,
        declaration,
        owner.members(),
        None,
        constructor.symbol(),
        index.map(|index| index.symbol),
    )?;
    let declared_static_properties = stored_declared_properties(
        store,
        symbol,
        declaration,
        Some(exports),
        Some(prototype),
        None,
        None,
    )?;

    let links = store.value_symbol_links(symbol)?;
    let value_type = links.resolved_type?;
    if links
        != &(ValueSymbolLinks {
            resolved_type: Some(value_type),
            ..ValueSymbolLinks::default()
        })
    {
        return None;
    }
    let value_record = store.type_payload(value_type)?;
    let TypeData::Object(value) = value_record.data() else {
        return None;
    };
    let [signature] = value.structured.signatures.as_deref()? else {
        return None;
    };
    let expected_constructor_declaration = if let Some(declaration) = constructor.declaration() {
        Some(declaration)
    } else if let Some(provenance) = store.direct_class_heritage_provenance(instance_type) {
        let base = store.type_payload(provenance.base_value_type)?;
        let [signature] = base.data().structured()?.signatures.as_deref()? else {
            return None;
        };
        store.signature(*signature)?.declaration()
    } else {
        None
    };
    if value_record.flags() != TypeFlags::OBJECT
        || value_record.object_flags() != (ObjectFlags::ANONYMOUS | ObjectFlags::MEMBERS_RESOLVED)
        || value_record.symbol() != Some(symbol)
        || value_record.alias().is_some()
        || value.target.is_some()
        || value.mapper.is_some()
        || value.instantiations != TypeCacheState::Unallocated
        || value.structured.constrained != ConstrainedTypeData::default()
        || value.structured.call_signature_count != 0
        || value.structured.index_infos.is_some()
        || value
            .structured
            .object_type_without_abstract_construct_signatures
            .is_some()
        || !exact_construct_signature(
            store,
            *signature,
            instance_type,
            expected_constructor_declaration,
        )
        || constructor.declaration().is_some_and(|declaration| {
            store.signature_links(declaration)
                != Some(&SignatureLinks {
                    resolved_signature: ResolvedSignatureState::Resolved(*signature),
                    ..SignatureLinks::default()
                })
        })
    {
        return None;
    }
    Some(StoredClassParts {
        symbol,
        instance,
        value_type,
        value: value.clone(),
        index,
        declared_instance_properties,
        declared_static_properties,
        prototype,
    })
}

fn property_entries(
    store: &CanonicalTypeMapperStore,
    properties: &[SemanticSymbolId],
) -> Option<Vec<(EscapedName, SemanticSymbolId)>> {
    properties
        .iter()
        .map(|property| {
            store
                .symbol(*property)
                .map(|record| (record.name().to_owned(), *property))
        })
        .collect()
}

fn validate_stored_no_base_class(
    store: &CanonicalTypeMapperStore,
    instance_type: TypeId,
) -> Option<StoredClassSurface> {
    if store
        .direct_class_heritage_provenance(instance_type)
        .is_some()
    {
        return None;
    }
    let parts = stored_class_parts(store, instance_type)?;
    let undefined_type = store.intrinsic_bootstrap()?.undefined_type;
    let structured = &parts.instance.reference.object.structured;
    let instance_entries = property_entries(store, &parts.declared_instance_properties)?;
    let static_entries = property_entries(store, &parts.declared_static_properties)?;
    let mut all_static_properties = parts.declared_static_properties.clone();
    all_static_properties.push(parts.prototype);
    if !parts.instance.base_types_resolved
        || parts.instance.resolved_base_constructor_type != Some(undefined_type)
        || parts.instance.resolved_base_types.is_some()
        || structured.constrained != ConstrainedTypeData::default()
        || structured.properties.as_deref()
            != (!parts.declared_instance_properties.is_empty())
                .then_some(parts.declared_instance_properties.as_slice())
        || structured.signatures.is_some()
        || structured.call_signature_count != 0
        || match (parts.index, structured.index_infos.as_deref()) {
            (None, None) => false,
            (Some(index), Some([info])) => index.info != *info,
            _ => true,
        }
        || structured
            .object_type_without_abstract_construct_signatures
            .is_some()
        || structured.members == parts.instance.declared_members && structured.members.is_some()
        || !exact_symbol_table_entries(store, structured.members, &instance_entries)
        || parts.value.structured.members != store.symbol(parts.symbol).and_then(Symbol::exports)
        || parts.value.structured.properties.as_deref() != Some(all_static_properties.as_slice())
        || !exact_symbol_table_entries(
            store,
            parts.value.structured.members,
            &static_entries
                .into_iter()
                .chain([(EscapedName::source(PROTOTYPE_NAME), parts.prototype)])
                .collect::<Vec<_>>(),
        )
    {
        return None;
    }
    Some(StoredClassSurface {
        instance_properties: parts.declared_instance_properties.clone(),
        static_properties: parts.declared_static_properties.clone(),
        parts,
    })
}

type StoredPropertyEntries = Vec<(EscapedName, SemanticSymbolId)>;

fn compose_stored_properties(
    store: &CanonicalTypeMapperStore,
    own: &[SemanticSymbolId],
    inherited: &[SemanticSymbolId],
) -> Option<(StoredPropertyEntries, Vec<SemanticSymbolId>)> {
    let capacity = own.len().checked_add(inherited.len())?;
    let mut entries = Vec::with_capacity(capacity);
    let mut properties = Vec::with_capacity(capacity);
    let mut names = HashSet::with_capacity(capacity);
    for property in own.iter().chain(inherited) {
        let name = store.symbol(*property)?.name().to_owned();
        if names.insert(name.clone()) {
            entries.push((name, *property));
            properties.push(*property);
        }
    }
    Some((entries, properties))
}

fn validate_stored_derived_class(
    store: &CanonicalTypeMapperStore,
    instance_type: TypeId,
    provenance: DirectClassHeritageProvenance,
) -> Option<StoredClassSurface> {
    let parts = stored_class_parts(store, instance_type)?;
    if provenance.owner_symbol != parts.symbol
        || provenance.owner_value_type != parts.value_type
        || provenance.base_symbol == parts.symbol
        || parts.index.is_some()
    {
        return None;
    }
    let base = validate_stored_no_base_class(store, provenance.base_instance_type)?;
    if base.parts.symbol != provenance.base_symbol
        || base.parts.value_type != provenance.base_value_type
        || base.parts.index.is_some()
        || !parts.instance.base_types_resolved
        || parts.instance.resolved_base_constructor_type != Some(provenance.base_value_type)
        || parts.instance.resolved_base_types.as_deref()
            != Some(&[provenance.base_instance_type][..])
    {
        return None;
    }
    let (instance_entries, instance_properties) = compose_stored_properties(
        store,
        &parts.declared_instance_properties,
        &base.instance_properties,
    )?;
    let (mut static_entries, static_properties) = compose_stored_properties(
        store,
        &parts.declared_static_properties,
        &base.static_properties,
    )?;
    static_entries.push((EscapedName::source(PROTOTYPE_NAME), parts.prototype));
    let structured = &parts.instance.reference.object.structured;
    let mut all_static_properties = static_properties.clone();
    all_static_properties.push(parts.prototype);
    if structured.constrained != ConstrainedTypeData::default()
        || structured.properties.as_deref()
            != (!instance_properties.is_empty()).then_some(instance_properties.as_slice())
        || structured.signatures.is_some()
        || structured.call_signature_count != 0
        || structured.index_infos.is_some()
        || structured
            .object_type_without_abstract_construct_signatures
            .is_some()
        || structured.members == parts.instance.declared_members && structured.members.is_some()
        || !exact_symbol_table_entries(store, structured.members, &instance_entries)
        || parts.value.structured.members == store.symbol(parts.symbol).and_then(Symbol::exports)
        || parts.value.structured.properties.as_deref() != Some(all_static_properties.as_slice())
        || !exact_symbol_table_entries(store, parts.value.structured.members, &static_entries)
    {
        return None;
    }
    Some(StoredClassSurface {
        parts,
        instance_properties,
        static_properties,
    })
}

/// Validates either an exact completed no-base class or the direct-base graph
/// branded by [`DirectClassHeritageProvenance`].
pub(super) fn validate_class_heritage_members(
    store: &CanonicalTypeMapperStore,
    instance_type: TypeId,
) -> ClassHeritageMembersValidation {
    let Some(record) = store.type_payload(instance_type) else {
        return ClassHeritageMembersValidation::NotClass;
    };
    if record.object_flags() & (ObjectFlags::CLASS | ObjectFlags::REFERENCE)
        != (ObjectFlags::CLASS | ObjectFlags::REFERENCE)
    {
        return ClassHeritageMembersValidation::NotClass;
    }
    let valid = match store.direct_class_heritage_provenance(instance_type) {
        Some(provenance) => {
            validate_stored_derived_class(store, instance_type, provenance).is_some()
        }
        None => validate_stored_no_base_class(store, instance_type).is_some(),
    };
    if valid {
        ClassHeritageMembersValidation::Valid
    } else {
        ClassHeritageMembersValidation::Malformed
    }
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;

    use ts_ast::{FileId, NodeArena, NodeData};
    use ts_binder::{
        BoundFile, CanonicalBinder, CanonicalModuleState, CanonicalNameResolverOptions,
        CanonicalSourceFileFacts, CanonicalSourceLanguage, EscapedName,
    };
    use ts_parser::{ParseResult, parse_source_file};

    use super::*;
    use crate::semantic::{
        CanonicalCheckerContext, CanonicalCheckerOptions, IntrinsicBootstrapOptions, SemanticStore,
        declared::type_list_key,
        mapper::TypeMapper,
        production::GlobalMergeCompletion,
        type_records::{TypeCacheState, TypeParameterData, TypeRecord},
    };

    type TestStore = SemanticStore<TypeRecord, TypeMapper>;

    struct Fixture {
        parsed: ParseResult,
        file: FileId,
        files: BTreeMap<FileId, BoundFile>,
        store: TestStore,
    }

    fn fixture(source: &str) -> Fixture {
        let parsed = parse_source_file(source);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(91);
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source("\"/classes.ts\""),
                    CanonicalSourceLanguage::TypeScript,
                    false,
                    CanonicalModuleState::Script,
                ),
            )
            .unwrap();
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
        let (symbols, files) = binder.finish().try_into_parts().unwrap();
        let mut store = TestStore::from_symbol_store(symbols);
        assert!(
            store
                .register_source_file(&parsed.arena, parsed.source_file, file)
                .is_some()
        );
        store
            .initialize_intrinsic_bootstrap(IntrinsicBootstrapOptions::default())
            .unwrap();
        let bound = files.get(&file).expect("bound source remains available");
        let source_locals = bound
            .locals(bound.source_file())
            .expect("class declarations allocate source locals");
        let mut global_symbols = store
            .symbol_table(source_locals)
            .expect("bound source locals remain store-owned")
            .iter()
            .map(|(name, symbol)| (name.as_bytes().to_vec(), symbol))
            .collect::<Vec<_>>();
        global_symbols.sort_unstable_by(|left, right| left.0.cmp(&right.0));
        let globals = store.intrinsic_bootstrap().unwrap().globals;
        for (_, symbol) in global_symbols {
            store.merge_global_symbol(globals, symbol).unwrap();
        }
        Fixture {
            parsed,
            file,
            files,
            store,
        }
    }

    fn host<'a>(arena: &'a NodeArena, bound: &'a BoundFile) -> DeclaredTypeHost<'a> {
        DeclaredTypeHost::new_after_global_merge(
            [(arena, bound)],
            GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
        )
        .unwrap()
    }

    fn class_node(fixture: &Fixture, name: &str) -> NodeRef {
        let node = fixture
            .parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                let NodeData::ClassDeclaration(class) = &record.data else {
                    return None;
                };
                let name_node = class.name.and_then(|name| fixture.parsed.arena.get(name))?;
                let NodeData::Identifier(identifier) = &name_node.data else {
                    return None;
                };
                (identifier.text == name).then_some(node)
            })
            .unwrap();
        NodeRef::new(fixture.parsed.arena.id(), fixture.file, node)
    }

    fn class_symbol(fixture: &Fixture, name: &str) -> SemanticSymbolId {
        fixture.files[&fixture.file]
            .symbol(class_node(fixture, name))
            .unwrap()
    }

    fn warm_class_method(
        store: &mut TestStore,
        method: &ClassMethodPlan,
        return_type: TypeId,
    ) -> (TypeId, SignatureId) {
        let type_ = store
            .alloc_plain_object_type(ObjectFlags::ANONYMOUS, Some(method.symbol))
            .unwrap();
        let signature = store
            .alloc_signature(
                SignatureFlags::NONE,
                Some(method.declaration),
                Vec::new(),
                None,
                Vec::new(),
                Some(return_type),
                None,
                0,
            )
            .unwrap();
        assert!(store.set_signature_links(
            method.declaration,
            SignatureLinks {
                resolved_signature: ResolvedSignatureState::Resolved(signature),
                ..SignatureLinks::default()
            },
        ));
        assert!(store.set_value_symbol_links(
            method.symbol,
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
        (type_, signature)
    }

    #[test]
    fn authenticated_field_decorator_preserves_property_identity_and_replays_warm() {
        let mut fixture = fixture(concat!(
            "declare function decorate(...args: any[]): any; ",
            "class Model { @decorate value!: bigint; }",
        ));
        let owner = class_symbol(&fixture, "Model");
        let bound = &fixture.files[&fixture.file];
        let host = host(&fixture.parsed.arena, bound);
        let plan = plan_nongeneric_class_member_query(&fixture.store, &host, owner).unwrap();
        assert!(plan.uninitialized_instance_properties().is_empty());

        let members =
            execute_nongeneric_class_member_query(&mut fixture.store, &host, &plan).unwrap();

        let [property] = members.declared_instance_properties() else {
            panic!("the decorated field retains one canonical class property")
        };
        let bigint = fixture.store.intrinsic_bootstrap().unwrap().bigint_type;
        assert_eq!(
            fixture
                .store
                .value_symbol_links(*property)
                .and_then(|links| links.resolved_type),
            Some(bigint)
        );
        assert_eq!(
            fixture.store.symbol(*property).unwrap().check_flags(),
            CheckFlags::NONE
        );
        assert_eq!(
            validate_class_heritage_members(&fixture.store, members.shells().instance_type()),
            ClassHeritageMembersValidation::Valid
        );
        let warm = (
            fixture.store.type_len(),
            fixture.store.signature_len(),
            fixture.store.symbol_store().symbol_table_len(),
            fixture.store.checker_link_allocated_lengths(),
        );

        assert_eq!(
            execute_nongeneric_class_member_query(&mut fixture.store, &host, &plan),
            Ok(members)
        );
        assert_eq!(
            (
                fixture.store.type_len(),
                fixture.store.signature_len(),
                fixture.store.symbol_store().symbol_table_len(),
                fixture.store.checker_link_allocated_lengths(),
            ),
            warm
        );
    }

    #[test]
    fn authenticated_definite_bigint_field_decorator_checks_from_source() {
        let parsed = parse_source_file(concat!(
            "declare function dec(...args: any[]): any; ",
            "class C { @dec prop!: bigint; }",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(303);
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source("\"/decorated-field.ts\""),
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
            [(file, &parsed.arena)].into_iter().collect(),
            CanonicalCheckerOptions::default(),
        )
        .unwrap();

        context.check_source_file(file).unwrap();

        assert!(context.diagnostics().is_empty());
    }

    #[test]
    fn unsupported_field_decorators_reject_before_class_publication() {
        for source in [
            "class Model { @missing value!: bigint; }",
            "declare const dec: any; class Model { @dec value!: bigint; }",
            "declare function dec(value: any): any; class Model { @dec value!: bigint; }",
            "declare function dec(...args: any[]): number; class Model { @dec value!: bigint; }",
            "declare function dec(...args: any[]): any; class Model { @dec value: bigint; }",
            "declare function dec(...args: any[]): any; class Model { @dec() value!: bigint; }",
            "declare function dec(...args: any[]): any; class Model { @dec @dec value!: bigint; }",
        ] {
            let fixture = fixture(source);
            let owner = class_symbol(&fixture, "Model");
            let bound = &fixture.files[&fixture.file];
            let host = host(&fixture.parsed.arena, bound);
            let cold = (
                fixture.store.type_len(),
                fixture.store.signature_len(),
                fixture.store.checker_link_allocated_lengths(),
            );

            assert!(matches!(
                plan_nongeneric_class_member_query(&fixture.store, &host, owner),
                Err(ClassError::Unsupported(
                    ClassUnsupported::PropertyModifiers(_)
                ))
            ));
            assert_eq!(
                (
                    fixture.store.type_len(),
                    fixture.store.signature_len(),
                    fixture.store.checker_link_allocated_lengths(),
                ),
                cold
            );
            assert!(fixture.store.declared_type_links(owner).is_none());
            assert!(fixture.store.value_symbol_links(owner).is_none());
        }
    }

    #[test]
    fn malformed_decorator_function_value_rejects_before_class_publication() {
        let mut fixture = fixture(concat!(
            "declare function dec(...args: any[]): any; ",
            "class Model { @dec value!: bigint; }",
        ));
        let owner = class_symbol(&fixture, "Model");
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
        let decorator = fixture.files[&fixture.file].symbol(declaration).unwrap();
        let wrong = fixture.store.intrinsic_bootstrap().unwrap().number_type;
        assert!(fixture.store.set_value_symbol_links(
            decorator,
            ValueSymbolLinks {
                resolved_type: Some(wrong),
                ..ValueSymbolLinks::default()
            },
        ));
        let bound = &fixture.files[&fixture.file];
        let host = host(&fixture.parsed.arena, bound);
        let poisoned = (
            fixture.store.type_len(),
            fixture.store.signature_len(),
            fixture.store.checker_link_allocated_lengths(),
        );

        assert_eq!(
            plan_nongeneric_class_member_query(&fixture.store, &host, owner),
            Err(invariant(ClassInvariant::InvalidPropertyValueCache(
                decorator
            )))
        );
        assert_eq!(
            (
                fixture.store.type_len(),
                fixture.store.signature_len(),
                fixture.store.checker_link_allocated_lengths(),
            ),
            poisoned
        );
        assert!(fixture.store.declared_type_links(owner).is_none());
        assert!(fixture.store.value_symbol_links(owner).is_none());
    }

    #[test]
    fn class_string_index_publishes_one_shared_index_and_replays_warm() {
        let mut fixture = fixture("class Indexed { [key: string]: number; constructor() {} }");
        let owner = class_symbol(&fixture, "Indexed");
        let bound = &fixture.files[&fixture.file];
        let host = host(&fixture.parsed.arena, bound);
        let plan = plan_nongeneric_class_member_query(&fixture.store, &host, owner).unwrap();
        let ClassMemberQueryPlan::Direct(class) = &plan else {
            panic!("an indexed class without heritage retains one direct class plan")
        };
        let index = class.class.index.unwrap();
        let declared_table = fixture
            .store
            .symbol_table(class.class.instance_members.unwrap())
            .unwrap();
        assert_eq!(
            declared_table.get(InternalSymbolName::Index.as_ref()),
            Some(index.symbol)
        );
        assert!(
            declared_table
                .get(InternalSymbolName::Constructor.as_ref())
                .is_some()
        );
        let initial_index_count = fixture.store.index_info_len();

        let members =
            execute_nongeneric_class_member_query(&mut fixture.store, &host, &plan).unwrap();

        assert_eq!(fixture.store.index_info_len(), initial_index_count + 1);
        assert!(members.instance_properties().is_empty());
        assert_eq!(members.instance_members(), None);
        let TypeData::Interface(instance) = fixture
            .store
            .type_payload(members.shells().instance_type())
            .unwrap()
            .data()
        else {
            panic!("the indexed class retains its canonical instance type")
        };
        let [info] = instance.declared_index_infos.as_deref().unwrap() else {
            panic!("the indexed class publishes exactly one declared index")
        };
        assert_eq!(
            instance.reference.object.structured.index_infos.as_deref(),
            Some(&[*info][..])
        );
        let index_info = fixture.store.index_info(*info).unwrap();
        let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
        assert_eq!(index_info.key_type(), bootstrap.string_type);
        assert_eq!(index_info.value_type(), bootstrap.number_type);
        assert_eq!(index_info.declaration(), Some(index.declaration));
        assert!(!index_info.is_readonly());
        assert_eq!(index_info.index_symbol(), None);
        assert_eq!(
            fixture.store.type_node_links(index.key_type_node),
            Some(&TypeNodeLinks {
                resolved_type: Some(bootstrap.string_type),
                ..TypeNodeLinks::default()
            })
        );
        assert_eq!(
            fixture.store.type_node_links(index.value_type_node),
            Some(&TypeNodeLinks {
                resolved_type: Some(bootstrap.number_type),
                ..TypeNodeLinks::default()
            })
        );
        assert_eq!(
            validate_class_heritage_members(&fixture.store, members.shells().instance_type()),
            ClassHeritageMembersValidation::Valid
        );
        let warm = (
            fixture.store.type_len(),
            fixture.store.signature_len(),
            fixture.store.index_info_len(),
            fixture.store.symbol_store().symbol_table_len(),
            fixture.store.checker_link_allocated_lengths(),
        );

        assert_eq!(
            execute_nongeneric_class_member_query(&mut fixture.store, &host, &plan),
            Ok(members)
        );
        assert_eq!(
            (
                fixture.store.type_len(),
                fixture.store.signature_len(),
                fixture.store.index_info_len(),
                fixture.store.symbol_store().symbol_table_len(),
                fixture.store.checker_link_allocated_lengths(),
            ),
            warm
        );
    }

    #[test]
    fn class_string_index_with_empty_constructor_checks_from_source() {
        let parsed = parse_source_file("class C123 { [s: string]: number; constructor() {} }");
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(302);
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source("\"/classIndexer.ts\""),
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
            [(file, &parsed.arena)].into_iter().collect(),
            CanonicalCheckerOptions::default(),
        )
        .unwrap();

        context.check_source_file(file).unwrap();

        assert!(context.diagnostics().is_empty());
    }

    #[test]
    fn poisoned_class_index_cache_rejects_warm_replay_without_publication() {
        let mut fixture = fixture("class Indexed { [key: string]: number; constructor() {} }");
        let owner = class_symbol(&fixture, "Indexed");
        let bound = &fixture.files[&fixture.file];
        let host = host(&fixture.parsed.arena, bound);
        let plan = plan_nongeneric_class_member_query(&fixture.store, &host, owner).unwrap();
        let ClassMemberQueryPlan::Direct(class) = &plan else {
            panic!("an indexed class without heritage retains one direct class plan")
        };
        let index_symbol = class.class.index.unwrap().symbol;
        let members =
            execute_nongeneric_class_member_query(&mut fixture.store, &host, &plan).unwrap();
        let TypeData::Interface(instance) = fixture
            .store
            .type_payload(members.shells().instance_type())
            .unwrap()
            .data()
        else {
            panic!("the indexed class retains its canonical instance type")
        };
        let info = instance.declared_index_infos.as_deref().unwrap()[0];
        assert!(
            fixture
                .store
                .set_index_info_symbol(info, Some(index_symbol))
        );
        let poisoned = (
            fixture.store.type_len(),
            fixture.store.signature_len(),
            fixture.store.index_info_len(),
            fixture.store.symbol_store().symbol_table_len(),
            fixture.store.checker_link_allocated_lengths(),
        );

        assert_eq!(
            validate_class_heritage_members(&fixture.store, members.shells().instance_type()),
            ClassHeritageMembersValidation::Malformed
        );
        assert_eq!(
            execute_nongeneric_class_member_query(&mut fixture.store, &host, &plan),
            Err(invariant(ClassInvariant::InvalidInstanceMembers(owner)))
        );
        assert_eq!(
            (
                fixture.store.type_len(),
                fixture.store.signature_len(),
                fixture.store.index_info_len(),
                fixture.store.symbol_store().symbol_table_len(),
                fixture.store.checker_link_allocated_lengths(),
            ),
            poisoned
        );
    }

    #[test]
    fn empty_local_class_implements_clause_has_no_runtime_base() {
        let mut fixture = fixture("class A {} class C implements A { static make() {} }");
        let target = class_symbol(&fixture, "A");
        let owner = class_symbol(&fixture, "C");
        let bound = &fixture.files[&fixture.file];
        let host = host(&fixture.parsed.arena, bound);
        let plan = plan_nongeneric_class_member_query(&fixture.store, &host, owner).unwrap();
        let ClassMemberQueryPlan::Direct(class) = &plan else {
            panic!("implements does not install a runtime base")
        };
        assert_eq!(class.class.implementations.len(), 1);
        assert_eq!(class.class.implementations[0].symbol, target);

        let members =
            execute_nongeneric_class_member_query(&mut fixture.store, &host, &plan).unwrap();

        assert_eq!(members.base(), None);
        assert_eq!(
            validate_class_heritage_members(&fixture.store, members.shells().instance_type()),
            ClassHeritageMembersValidation::Valid
        );
        assert!(fixture.store.declared_type_links(target).is_none());
    }

    #[test]
    fn empty_local_class_and_interface_implements_clauses_check_from_source() {
        for (index, source) in [
            "class A {} class C implements A {}",
            "interface Empty {} class C implements Empty {}",
        ]
        .into_iter()
        .enumerate()
        {
            let parsed = parse_source_file(source);
            assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
            let file = FileId::new(300 + u32::try_from(index).unwrap());
            let mut binder = CanonicalBinder::new();
            binder
                .bind_source_file_with_facts(
                    &parsed.arena,
                    parsed.source_file,
                    file,
                    CanonicalSourceFileFacts::new(
                        EscapedName::source("\"/implements.ts\""),
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
                [(file, &parsed.arena)].into_iter().collect(),
                CanonicalCheckerOptions::default(),
            )
            .unwrap();

            context.check_source_file(file).unwrap();

            assert!(context.diagnostics().is_empty(), "{source}");
        }
    }

    #[test]
    fn empty_class_installs_exact_instance_and_value_shells_then_replays_warm() {
        let mut fixture = fixture("class Plain {}");
        let symbol = class_symbol(&fixture, "Plain");
        let bound = &fixture.files[&fixture.file];
        let host = host(&fixture.parsed.arena, bound);
        let plan = plan_nongeneric_class(&fixture.store, &host, symbol).unwrap();
        let type_count = fixture.store.type_len();
        let link_counts = fixture.store.checker_link_allocated_lengths();

        let shells = execute_nongeneric_class_shells(&mut fixture.store, &host, &plan).unwrap();
        assert_eq!(fixture.store.type_len(), type_count + 3);
        assert_eq!(shells.declaration(), class_node(&fixture, "Plain"));
        assert_eq!(shells.symbol(), symbol);
        assert_ne!(shells.instance_type(), shells.value_type());
        assert_eq!(
            fixture
                .store
                .declared_type_links(symbol)
                .and_then(|links| links.declared_type),
            Some(shells.instance_type())
        );
        assert_eq!(
            fixture.store.value_symbol_links(symbol),
            Some(&ValueSymbolLinks {
                resolved_type: Some(shells.value_type()),
                ..ValueSymbolLinks::default()
            })
        );

        let instance_record = fixture.store.type_payload(shells.instance_type()).unwrap();
        assert_eq!(instance_record.flags(), TypeFlags::OBJECT);
        assert_eq!(
            instance_record.object_flags(),
            ObjectFlags::CLASS | ObjectFlags::REFERENCE
        );
        assert_eq!(instance_record.symbol(), Some(symbol));
        let TypeData::Interface(instance) = instance_record.data() else {
            panic!("class instance must use InterfaceTypeData")
        };
        assert_eq!(
            instance.resolved_base_constructor_type,
            Some(fixture.store.intrinsic_bootstrap().unwrap().undefined_type)
        );
        assert!(!instance.base_types_resolved);
        assert_eq!(instance.resolved_base_types, None);
        assert_eq!(
            instance.reference.object.target,
            Some(shells.instance_type())
        );
        assert_eq!(instance.reference.resolved_type_arguments, Some(Vec::new()));
        let all = instance.all_type_parameters.as_deref().unwrap();
        assert_eq!(all.len(), 1);
        assert_eq!(instance.this_type, Some(all[0]));
        let TypeCacheState::Allocated(instantiations) = &instance.reference.object.instantiations
        else {
            panic!("class origin owns its self-instantiation cache")
        };
        assert_eq!(
            instantiations.get(&type_list_key(&[])),
            Some(&shells.instance_type())
        );
        let TypeData::TypeParameter(TypeParameterData {
            constraint,
            is_this_type,
            ..
        }) = fixture.store.type_payload(all[0]).unwrap().data()
        else {
            panic!("class owns a synthetic this parameter")
        };
        assert!(*is_this_type);
        assert_eq!(*constraint, Some(shells.instance_type()));

        let value_record = fixture.store.type_payload(shells.value_type()).unwrap();
        assert_eq!(value_record.flags(), TypeFlags::OBJECT);
        assert_eq!(value_record.object_flags(), ObjectFlags::ANONYMOUS);
        assert_eq!(value_record.symbol(), Some(symbol));
        assert!(matches!(
            value_record.data(),
            TypeData::Object(object) if object == &ObjectTypeData::default()
        ));

        let warm_state = (
            fixture.store.type_len(),
            fixture.store.checker_link_allocated_lengths(),
        );
        assert_eq!(
            execute_nongeneric_class_shells(&mut fixture.store, &host, &plan),
            Ok(shells)
        );
        assert_eq!(
            (
                fixture.store.type_len(),
                fixture.store.checker_link_allocated_lengths(),
            ),
            warm_state
        );
        assert_ne!(fixture.store.checker_link_allocated_lengths(), link_counts);
    }

    #[test]
    fn annotated_property_plan_preserves_instance_static_and_postfix_split() {
        let fixture = fixture(
            "class Model { readonly value?: string; definite!: number; static readonly count: number; }",
        );
        let symbol = class_symbol(&fixture, "Model");
        let bound = &fixture.files[&fixture.file];
        let host = host(&fixture.parsed.arena, bound);
        let plan = plan_nongeneric_class(&fixture.store, &host, symbol).unwrap();

        assert_eq!(plan.declaration(), class_node(&fixture, "Model"));
        assert_eq!(plan.symbol(), symbol);
        assert!(plan.instance_members().is_some());
        assert_eq!(plan.instance_properties().len(), 2);
        assert_eq!(plan.static_properties().len(), 1);
        assert_eq!(plan.property_type_nodes().len(), 3);
        assert_eq!(
            plan.properties()
                .iter()
                .map(ClassPropertyPlan::name)
                .collect::<Vec<_>>(),
            vec!["value", "definite", "count"]
        );

        let value = &plan.instance_properties()[0];
        assert_eq!(value.name(), "value");
        assert_eq!(value.side(), ClassPropertySide::Instance);
        assert!(value.optional());
        assert!(!value.definite());
        assert!(value.readonly());

        let definite = &plan.instance_properties()[1];
        assert_eq!(definite.name(), "definite");
        assert!(!definite.optional());
        assert!(definite.definite());
        assert!(!definite.readonly());

        let count = &plan.static_properties()[0];
        assert_eq!(count.name(), "count");
        assert_eq!(count.side(), ClassPropertySide::Static);
        assert!(!count.optional());
        assert!(!count.definite());
        assert!(count.readonly());
        let static_table = fixture.store.symbol_table(plan.static_members()).unwrap();
        assert_eq!(static_table.len(), 2);
        assert!(static_table.get_source(PROTOTYPE_NAME).is_some());
    }

    #[test]
    fn static_zero_argument_methods_publish_canonical_callables_and_replay_warm() {
        let mut fixture = fixture(concat!(
            "class Greeter { ",
            "static try() {} ",
            "public static named(): any {} ",
            "static count: number; ",
            "}",
        ));
        let owner = class_symbol(&fixture, "Greeter");
        let bound = &fixture.files[&fixture.file];
        let host = host(&fixture.parsed.arena, bound);
        let plan = plan_nongeneric_class_member_query(&fixture.store, &host, owner).unwrap();

        let members =
            execute_nongeneric_class_member_query(&mut fixture.store, &host, &plan).unwrap();

        let names = members
            .static_properties()
            .iter()
            .map(|symbol| {
                fixture
                    .store
                    .symbol(*symbol)
                    .unwrap()
                    .name()
                    .as_utf8()
                    .unwrap()
            })
            .collect::<Vec<_>>();
        assert_eq!(names, ["try", "named", "count"]);
        assert_eq!(members.instance_members(), None);
        let methods = match &plan {
            ClassMemberQueryPlan::Direct(plan) => &plan.class.methods,
            ClassMemberQueryPlan::Derived { .. } => unreachable!("Greeter has no base"),
        };
        let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
        for (method, expected) in methods
            .iter()
            .zip([bootstrap.void_type, bootstrap.any_type])
        {
            let (type_, signature) =
                exact_method_callable(&fixture.store, method, expected).unwrap();
            assert_eq!(
                fixture.store.type_payload(type_).unwrap().symbol(),
                Some(method.symbol)
            );
            assert_eq!(
                fixture.store.signature_links(method.declaration),
                Some(&SignatureLinks {
                    resolved_signature: ResolvedSignatureState::Resolved(signature),
                    ..SignatureLinks::default()
                })
            );
        }
        assert_eq!(
            validate_class_heritage_members(&fixture.store, members.shells().instance_type()),
            ClassHeritageMembersValidation::Valid
        );
        let warm = (
            fixture.store.type_len(),
            fixture.store.signature_len(),
            fixture.store.symbol_store().symbol_table_len(),
            fixture.store.checker_link_allocated_lengths(),
        );
        assert_eq!(
            execute_nongeneric_class_member_query(&mut fixture.store, &host, &plan),
            Ok(members)
        );
        assert_eq!(
            (
                fixture.store.type_len(),
                fixture.store.signature_len(),
                fixture.store.symbol_store().symbol_table_len(),
                fixture.store.checker_link_allocated_lengths(),
            ),
            warm
        );
    }

    #[test]
    fn prewarmed_class_methods_keep_their_callable_and_signature_identities() {
        let mut fixture = fixture("class Model { instance(): void {} static run(): any {} }");
        let owner = class_symbol(&fixture, "Model");
        let bound = &fixture.files[&fixture.file];
        let host = host(&fixture.parsed.arena, bound);
        let plan = plan_nongeneric_class_members(&fixture.store, &host, owner).unwrap();
        let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
        let return_types = [bootstrap.void_type, bootstrap.any_type];
        let expected = plan
            .class
            .methods
            .iter()
            .zip(return_types)
            .map(|(method, return_type)| warm_class_method(&mut fixture.store, method, return_type))
            .collect::<Vec<_>>();
        let type_count = fixture.store.type_len();
        let signature_count = fixture.store.signature_len();

        let members = execute_nongeneric_class_members(&mut fixture.store, &host, &plan).unwrap();

        assert_eq!(fixture.store.type_len(), type_count + 3);
        assert_eq!(fixture.store.signature_len(), signature_count + 1);
        for ((method, return_type), identity) in
            plan.class.methods.iter().zip(return_types).zip(expected)
        {
            assert_eq!(
                exact_method_callable(&fixture.store, method, return_type),
                Some(identity)
            );
            assert_eq!(
                fixture
                    .store
                    .type_node_links(method.return_type_node.unwrap()),
                Some(&TypeNodeLinks {
                    resolved_type: Some(return_type),
                    ..TypeNodeLinks::default()
                })
            );
        }
        assert_eq!(members.declared_instance_properties().len(), 1);
        assert_eq!(members.declared_static_properties().len(), 1);
        assert_eq!(
            validate_class_heritage_members(&fixture.store, members.shells().instance_type()),
            ClassHeritageMembersValidation::Valid
        );
    }

    #[test]
    fn instance_zero_argument_methods_share_the_ordered_class_member_table() {
        let mut fixture = fixture("class Model { public run(): void {} value: string; }");
        let owner = class_symbol(&fixture, "Model");
        let bound = &fixture.files[&fixture.file];
        let host = host(&fixture.parsed.arena, bound);
        let plan = plan_nongeneric_class_member_query(&fixture.store, &host, owner).unwrap();

        let members =
            execute_nongeneric_class_member_query(&mut fixture.store, &host, &plan).unwrap();

        let names = members
            .instance_properties()
            .iter()
            .map(|symbol| {
                fixture
                    .store
                    .symbol(*symbol)
                    .unwrap()
                    .name()
                    .as_utf8()
                    .unwrap()
            })
            .collect::<Vec<_>>();
        assert_eq!(names, ["run", "value"]);
        let declared = fixture.store.symbol(owner).unwrap().members().unwrap();
        assert_ne!(members.instance_members(), Some(declared));
        assert_eq!(
            validate_class_heritage_members(&fixture.store, members.shells().instance_type()),
            ClassHeritageMembersValidation::Valid
        );
    }

    #[test]
    fn derived_static_properties_reuse_prewarmed_base_method_signatures() {
        let mut fixture = fixture(concat!(
            "class Base { static inherited(): any {} } ",
            "class Derived extends Base { static own(): void {} }",
        ));
        let owner = class_symbol(&fixture, "Derived");
        let bound = &fixture.files[&fixture.file];
        let host = host(&fixture.parsed.arena, bound);
        let plan = plan_nongeneric_class_member_query(&fixture.store, &host, owner).unwrap();
        let ClassMemberQueryPlan::Derived { class, base } = &plan else {
            panic!("Derived retains its direct base")
        };
        let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
        let own_return_type = bootstrap.void_type;
        let inherited_return_type = bootstrap.any_type;
        let own = warm_class_method(&mut fixture.store, &class.class.methods[0], own_return_type);
        let inherited = warm_class_method(
            &mut fixture.store,
            &base.class.methods[0],
            inherited_return_type,
        );
        let type_count = fixture.store.type_len();
        let signature_count = fixture.store.signature_len();

        let members =
            execute_nongeneric_class_member_query(&mut fixture.store, &host, &plan).unwrap();

        assert_eq!(fixture.store.type_len(), type_count + 6);
        assert_eq!(fixture.store.signature_len(), signature_count + 2);
        assert_eq!(
            exact_method_callable(&fixture.store, &class.class.methods[0], own_return_type),
            Some(own)
        );
        assert_eq!(
            exact_method_callable(
                &fixture.store,
                &base.class.methods[0],
                inherited_return_type,
            ),
            Some(inherited)
        );
        assert_eq!(
            members.static_properties(),
            &[class.class.methods[0].symbol, base.class.methods[0].symbol]
        );
        assert_eq!(
            fixture
                .store
                .symbol_table(members.static_members())
                .and_then(|table| table.get_source("inherited")),
            Some(base.class.methods[0].symbol)
        );
        assert_eq!(
            validate_class_heritage_members(&fixture.store, members.shells().instance_type()),
            ClassHeritageMembersValidation::Valid
        );
    }

    #[test]
    fn derived_classes_reuse_inherited_instance_and_static_method_symbols() {
        let mut fixture = fixture(concat!(
            "class Base { ",
            "instance(): void {} ",
            "base: string; ",
            "static shared(): any {} ",
            "static count: number; ",
            "} ",
            "class Derived extends Base { ",
            "own(): void {} ",
            "derived: number; ",
            "static local(): void {} ",
            "static total: number; ",
            "}",
        ));
        let base_symbol = class_symbol(&fixture, "Base");
        let derived_symbol = class_symbol(&fixture, "Derived");
        let bound = &fixture.files[&fixture.file];
        let host = host(&fixture.parsed.arena, bound);
        let plan =
            plan_nongeneric_class_member_query(&fixture.store, &host, derived_symbol).unwrap();

        let derived =
            execute_nongeneric_class_member_query(&mut fixture.store, &host, &plan).unwrap();
        let base_plan =
            plan_nongeneric_class_member_query(&fixture.store, &host, base_symbol).unwrap();
        let base =
            execute_nongeneric_class_member_query(&mut fixture.store, &host, &base_plan).unwrap();

        let names = |symbols: &[SemanticSymbolId]| {
            symbols
                .iter()
                .map(|symbol| {
                    fixture
                        .store
                        .symbol(*symbol)
                        .unwrap()
                        .name()
                        .as_utf8()
                        .unwrap()
                })
                .collect::<Vec<_>>()
        };
        assert_eq!(
            names(derived.instance_properties()),
            ["own", "derived", "instance", "base"]
        );
        assert_eq!(
            names(derived.static_properties()),
            ["local", "total", "shared", "count"]
        );
        assert_eq!(
            derived.instance_properties()[2],
            base.instance_properties()[0]
        );
        assert_eq!(derived.static_properties()[2], base.static_properties()[0]);
        assert_eq!(
            validate_class_heritage_members(&fixture.store, derived.shells().instance_type()),
            ClassHeritageMembersValidation::Valid
        );

        let warm = (
            fixture.store.type_len(),
            fixture.store.signature_len(),
            fixture.store.symbol_store().symbol_table_len(),
            fixture.store.checker_link_allocated_lengths(),
        );
        assert_eq!(
            execute_nongeneric_class_member_query(&mut fixture.store, &host, &plan),
            Ok(derived)
        );
        assert_eq!(
            (
                fixture.store.type_len(),
                fixture.store.signature_len(),
                fixture.store.symbol_store().symbol_table_len(),
                fixture.store.checker_link_allocated_lengths(),
            ),
            warm
        );
    }

    #[test]
    fn overriding_methods_replace_base_symbols_without_hiding_other_methods() {
        let mut fixture = fixture(concat!(
            "class Base { same(): void {} other(): void {} static shared(): void {} } ",
            "class Derived extends Base { same(): void {} static shared(): void {} }",
        ));
        let base_symbol = class_symbol(&fixture, "Base");
        let derived_symbol = class_symbol(&fixture, "Derived");
        let bound = &fixture.files[&fixture.file];
        let host = host(&fixture.parsed.arena, bound);
        let plan =
            plan_nongeneric_class_member_query(&fixture.store, &host, derived_symbol).unwrap();

        let derived =
            execute_nongeneric_class_member_query(&mut fixture.store, &host, &plan).unwrap();
        let base_plan =
            plan_nongeneric_class_member_query(&fixture.store, &host, base_symbol).unwrap();
        let base =
            execute_nongeneric_class_member_query(&mut fixture.store, &host, &base_plan).unwrap();

        assert_eq!(derived.instance_properties().len(), 2);
        assert_ne!(
            derived.instance_properties()[0],
            base.instance_properties()[0]
        );
        assert_eq!(
            derived.instance_properties()[1],
            base.instance_properties()[1]
        );
        assert_eq!(derived.static_properties().len(), 1);
        assert_ne!(derived.static_properties()[0], base.static_properties()[0]);
        assert_eq!(
            validate_class_heritage_members(&fixture.store, derived.shells().instance_type()),
            ClassHeritageMembersValidation::Valid
        );
    }

    #[test]
    fn forged_inherited_static_property_type_invalidates_the_derived_graph() {
        let mut fixture = fixture(concat!(
            "class Base { static inherited: number; } ",
            "class Derived extends Base {}",
        ));
        let owner = class_symbol(&fixture, "Derived");
        let bound = &fixture.files[&fixture.file];
        let host = host(&fixture.parsed.arena, bound);
        let plan = plan_nongeneric_class_member_query(&fixture.store, &host, owner).unwrap();
        let ClassMemberQueryPlan::Derived { base, .. } = &plan else {
            panic!("Derived retains its direct base")
        };
        let inherited = &base.class.static_properties[0];
        let members =
            execute_nongeneric_class_member_query(&mut fixture.store, &host, &plan).unwrap();
        let instance = members.shells().instance_type();
        let base_instance = members.base().unwrap().instance_type();
        assert_eq!(
            fixture.store.is_type_assignable_to(instance, base_instance),
            Ok(true)
        );

        let wrong = fixture.store.intrinsic_bootstrap().unwrap().string_type;
        assert!(fixture.store.set_type_node_links(
            inherited.type_node,
            TypeNodeLinks {
                resolved_type: Some(wrong),
                ..TypeNodeLinks::default()
            },
        ));
        assert!(fixture.store.set_value_symbol_links(
            inherited.symbol,
            ValueSymbolLinks {
                resolved_type: Some(wrong),
                ..ValueSymbolLinks::default()
            },
        ));
        let poisoned = (
            fixture.store.type_len(),
            fixture.store.signature_len(),
            fixture.store.symbol_store().symbol_table_len(),
            fixture.store.checker_link_allocated_lengths(),
            fixture.store.relation_state_snapshot(),
        );

        assert_eq!(
            validate_class_heritage_members(&fixture.store, instance),
            ClassHeritageMembersValidation::Malformed
        );
        assert_eq!(
            fixture.store.is_type_assignable_to(instance, base_instance),
            Err(super::super::relater::RelationUnavailable::InvalidStructuredMembers(instance,))
        );
        assert_eq!(
            execute_nongeneric_class_member_query(&mut fixture.store, &host, &plan),
            Err(invariant(ClassInvariant::InvalidPropertyTypeCache(
                inherited.type_node,
            )))
        );
        assert_eq!(
            (
                fixture.store.type_len(),
                fixture.store.signature_len(),
                fixture.store.symbol_store().symbol_table_len(),
                fixture.store.checker_link_allocated_lengths(),
                fixture.store.relation_state_snapshot(),
            ),
            poisoned
        );
    }

    #[test]
    fn forged_inherited_method_return_type_invalidates_the_derived_graph() {
        let mut fixture = fixture(concat!(
            "class Base { static inherited(): void {} } ",
            "class Derived extends Base {}",
        ));
        let owner = class_symbol(&fixture, "Derived");
        let bound = &fixture.files[&fixture.file];
        let host = host(&fixture.parsed.arena, bound);
        let plan = plan_nongeneric_class_member_query(&fixture.store, &host, owner).unwrap();
        let ClassMemberQueryPlan::Derived { base, .. } = &plan else {
            panic!("Derived retains its direct base")
        };
        let inherited = &base.class.methods[0];
        let annotation = inherited.return_type_node.unwrap();
        let members =
            execute_nongeneric_class_member_query(&mut fixture.store, &host, &plan).unwrap();
        let instance = members.shells().instance_type();
        let base_instance = members.base().unwrap().instance_type();
        assert_eq!(
            fixture.store.is_type_assignable_to(instance, base_instance),
            Ok(true)
        );
        let void = fixture.store.intrinsic_bootstrap().unwrap().void_type;
        let (_, signature) = exact_method_callable(&fixture.store, inherited, void).unwrap();
        let wrong = fixture.store.intrinsic_bootstrap().unwrap().any_type;
        assert!(
            fixture
                .store
                .set_signature_resolved_return_type(signature, Some(wrong))
        );
        assert!(fixture.store.set_type_node_links(
            annotation,
            TypeNodeLinks {
                resolved_type: Some(wrong),
                ..TypeNodeLinks::default()
            },
        ));
        let poisoned = (
            fixture.store.type_len(),
            fixture.store.signature_len(),
            fixture.store.symbol_store().symbol_table_len(),
            fixture.store.checker_link_allocated_lengths(),
            fixture.store.relation_state_snapshot(),
        );

        assert_eq!(
            validate_class_heritage_members(&fixture.store, instance),
            ClassHeritageMembersValidation::Malformed
        );
        assert_eq!(
            fixture.store.is_type_assignable_to(instance, base_instance),
            Err(super::super::relater::RelationUnavailable::InvalidStructuredMembers(instance,))
        );
        assert_eq!(
            execute_nongeneric_class_member_query(&mut fixture.store, &host, &plan),
            Err(invariant(ClassInvariant::InvalidPropertyTypeCache(
                annotation,
            )))
        );
        assert_eq!(
            (
                fixture.store.type_len(),
                fixture.store.signature_len(),
                fixture.store.symbol_store().symbol_table_len(),
                fixture.store.checker_link_allocated_lengths(),
                fixture.store.relation_state_snapshot(),
            ),
            poisoned
        );
    }

    #[test]
    fn poisoned_inherited_method_signature_invalidates_the_complete_derived_graph() {
        let mut fixture = fixture(concat!(
            "class Base { method(): void {} } ",
            "class Derived extends Base { own(): void {} }",
        ));
        let derived_symbol = class_symbol(&fixture, "Derived");
        let bound = &fixture.files[&fixture.file];
        let host = host(&fixture.parsed.arena, bound);
        let plan =
            plan_nongeneric_class_member_query(&fixture.store, &host, derived_symbol).unwrap();
        let derived =
            execute_nongeneric_class_member_query(&mut fixture.store, &host, &plan).unwrap();
        let inherited = derived.instance_properties()[1];
        let method_type = fixture
            .store
            .value_symbol_links(inherited)
            .and_then(|links| links.resolved_type)
            .unwrap();
        let signature = fixture
            .store
            .type_payload(method_type)
            .and_then(|record| record.data().structured())
            .and_then(|structured| structured.signatures.as_deref())
            .and_then(|signatures| signatures.first().copied())
            .unwrap();
        let wrong = fixture.store.intrinsic_bootstrap().unwrap().number_type;
        assert!(
            fixture
                .store
                .set_signature_resolved_return_type(signature, Some(wrong))
        );
        let poisoned = (
            fixture.store.type_len(),
            fixture.store.signature_len(),
            fixture.store.symbol_store().symbol_table_len(),
            fixture.store.checker_link_allocated_lengths(),
        );

        assert_eq!(
            validate_class_heritage_members(&fixture.store, derived.shells().instance_type()),
            ClassHeritageMembersValidation::Malformed
        );
        assert_eq!(
            execute_nongeneric_class_member_query(&mut fixture.store, &host, &plan),
            Err(invariant(ClassInvariant::InvalidPropertyValueCache(
                inherited
            )))
        );
        assert_eq!(
            (
                fixture.store.type_len(),
                fixture.store.signature_len(),
                fixture.store.symbol_store().symbol_table_len(),
                fixture.store.checker_link_allocated_lengths(),
            ),
            poisoned
        );
    }

    #[test]
    fn unsupported_method_return_or_body_keeps_all_class_members_cold() {
        for source in [
            "class Model { static first() {} static second(): number {} }",
            "class Model { static first() {} static second() { return; } }",
            "class Model { static first() {} static second(value: string) {} }",
        ] {
            let fixture = fixture(source);
            let owner = class_symbol(&fixture, "Model");
            let bound = &fixture.files[&fixture.file];
            let host = host(&fixture.parsed.arena, bound);
            let cold = (
                fixture.store.type_len(),
                fixture.store.signature_len(),
                fixture.store.checker_link_allocated_lengths(),
            );

            assert!(matches!(
                plan_nongeneric_class_member_query(&fixture.store, &host, owner),
                Err(ClassError::Unsupported(ClassUnsupported::Member {
                    kind: SyntaxKind::MethodDeclaration,
                    ..
                }))
            ));
            assert_eq!(
                (
                    fixture.store.type_len(),
                    fixture.store.signature_len(),
                    fixture.store.checker_link_allocated_lengths(),
                ),
                cold
            );
            assert!(fixture.store.declared_type_links(owner).is_none());
            assert!(fixture.store.value_symbol_links(owner).is_none());
        }
    }

    #[test]
    fn uninitialized_property_plan_matches_strict_checker_type_exemptions() {
        let fixture = fixture(concat!(
            "class Model { ",
            "safeAny: any; ",
            "requiredString: string; ",
            "safeUnknown: unknown; ",
            "requiredVoid: void; ",
            "safeUndefined: undefined; ",
            "optional?: number; ",
            "definite!: boolean; ",
            "static ignored: string; ",
            "}",
        ));
        let symbol = class_symbol(&fixture, "Model");
        let bound = &fixture.files[&fixture.file];
        let host = host(&fixture.parsed.arena, bound);

        let plan = plan_nongeneric_class_members(&fixture.store, &host, symbol).unwrap();

        let names = plan
            .uninitialized_instance_properties()
            .iter()
            .map(|property| {
                let NodeData::Identifier(name) = &fixture
                    .parsed
                    .arena
                    .get(property.node)
                    .expect("class property name remains in its source arena")
                    .data
                else {
                    panic!("class property diagnostics must target their names")
                };
                name.text.as_str()
            })
            .collect::<Vec<_>>();
        assert_eq!(names, ["requiredString", "requiredVoid"]);
        assert!(!plan.uninitialized_instance_properties().is_empty());
    }

    #[test]
    fn existing_instance_shell_stays_canonical_when_the_static_side_is_cold() {
        let mut fixture = fixture("class Staged {}");
        let symbol = class_symbol(&fixture, "Staged");
        let bound = &fixture.files[&fixture.file];
        let host = host(&fixture.parsed.arena, bound);
        let instance = fixture
            .store
            .get_declared_type_of_symbol(&host, symbol)
            .unwrap();
        let TypeData::Interface(data) = fixture.store.type_payload(instance).unwrap().data() else {
            panic!("declared class identity is an interface record")
        };
        assert_eq!(data.resolved_base_constructor_type, None);
        let plan = plan_nongeneric_class(&fixture.store, &host, symbol).unwrap();
        let type_count = fixture.store.type_len();

        let shells = execute_nongeneric_class_shells(&mut fixture.store, &host, &plan).unwrap();
        assert_eq!(shells.instance_type(), instance);
        assert_eq!(fixture.store.type_len(), type_count + 1);
        let TypeData::Interface(data) = fixture.store.type_payload(instance).unwrap().data() else {
            panic!("declared class identity remains an interface record")
        };
        assert_eq!(
            data.resolved_base_constructor_type,
            Some(fixture.store.intrinsic_bootstrap().unwrap().undefined_type)
        );
        assert!(!data.base_types_resolved);
    }

    #[test]
    fn prewarmed_constructor_signature_is_reused_by_class_members() {
        let mut fixture = fixture("class Model { constructor() {} }");
        let owner = class_symbol(&fixture, "Model");
        let bound = &fixture.files[&fixture.file];
        let host = host(&fixture.parsed.arena, bound);
        let plan = plan_nongeneric_class_members(&fixture.store, &host, owner).unwrap();
        let constructor = plan.class.constructor.unwrap();
        let instance = fixture
            .store
            .get_declared_type_of_symbol(&host, owner)
            .unwrap();
        let signature = fixture
            .store
            .alloc_signature(
                SignatureFlags::CONSTRUCT,
                Some(constructor.declaration),
                Vec::new(),
                None,
                Vec::new(),
                Some(instance),
                None,
                0,
            )
            .unwrap();
        assert!(fixture.store.set_signature_links(
            constructor.declaration,
            SignatureLinks {
                resolved_signature: ResolvedSignatureState::Resolved(signature),
                ..SignatureLinks::default()
            },
        ));
        let type_count = fixture.store.type_len();
        let signature_count = fixture.store.signature_len();

        let members = execute_nongeneric_class_members(&mut fixture.store, &host, &plan).unwrap();

        assert_eq!(members.shells().instance_type(), instance);
        assert_eq!(members.default_construct_signature(), signature);
        assert_eq!(fixture.store.type_len(), type_count + 1);
        assert_eq!(fixture.store.signature_len(), signature_count);
        assert_eq!(
            fixture.store.signature_links(constructor.declaration),
            Some(&SignatureLinks {
                resolved_signature: ResolvedSignatureState::Resolved(signature),
                ..SignatureLinks::default()
            })
        );
        assert_eq!(
            validate_class_heritage_members(&fixture.store, instance),
            ClassHeritageMembersValidation::Valid
        );
    }

    #[test]
    fn warm_value_without_instance_and_poisoned_value_reject_atomically() {
        let mut fixture = fixture("class Poisoned {}");
        let symbol = class_symbol(&fixture, "Poisoned");
        let bound = &fixture.files[&fixture.file];
        let host = host(&fixture.parsed.arena, bound);
        let plan = plan_nongeneric_class(&fixture.store, &host, symbol).unwrap();
        let value = fixture
            .store
            .alloc_plain_object_type(ObjectFlags::ANONYMOUS, Some(symbol))
            .unwrap();
        assert!(fixture.store.set_value_symbol_links(
            symbol,
            ValueSymbolLinks {
                resolved_type: Some(value),
                ..ValueSymbolLinks::default()
            }
        ));
        let state = (
            fixture.store.type_len(),
            fixture.store.checker_link_allocated_lengths(),
        );
        assert_eq!(
            execute_nongeneric_class_shells(&mut fixture.store, &host, &plan),
            Err(invariant(ClassInvariant::InvalidValueCache(symbol)))
        );
        assert_eq!(
            (
                fixture.store.type_len(),
                fixture.store.checker_link_allocated_lengths(),
            ),
            state
        );
        assert!(
            fixture
                .store
                .declared_type_links(symbol)
                .and_then(|links| links.declared_type)
                .is_none()
        );

        let wrong = fixture.store.intrinsic_bootstrap().unwrap().string_type;
        assert!(fixture.store.set_value_symbol_links(
            symbol,
            ValueSymbolLinks {
                resolved_type: Some(wrong),
                ..ValueSymbolLinks::default()
            }
        ));
        let poisoned = (
            fixture.store.type_len(),
            fixture.store.checker_link_allocated_lengths(),
        );
        assert_eq!(
            execute_nongeneric_class_shells(&mut fixture.store, &host, &plan),
            Err(invariant(ClassInvariant::InvalidValueCache(symbol)))
        );
        assert_eq!(
            (
                fixture.store.type_len(),
                fixture.store.checker_link_allocated_lengths(),
            ),
            poisoned
        );
    }

    #[test]
    fn pre_resolved_base_bit_is_not_an_exact_shell_state() {
        let mut fixture = fixture("class BasePoison {}");
        let symbol = class_symbol(&fixture, "BasePoison");
        let bound = &fixture.files[&fixture.file];
        let host = host(&fixture.parsed.arena, bound);
        let instance = fixture
            .store
            .get_declared_type_of_symbol(&host, symbol)
            .unwrap();
        assert!(
            fixture
                .store
                .set_interface_base_resolution(instance, true, None, None)
        );
        let plan = plan_nongeneric_class(&fixture.store, &host, symbol).unwrap();
        let state = (
            fixture.store.type_len(),
            fixture.store.checker_link_allocated_lengths(),
        );

        assert_eq!(
            execute_nongeneric_class_shells(&mut fixture.store, &host, &plan),
            Err(invariant(ClassInvariant::InvalidInstanceCache(symbol)))
        );
        assert_eq!(
            (
                fixture.store.type_len(),
                fixture.store.checker_link_allocated_lengths(),
            ),
            state
        );
        assert!(
            fixture
                .store
                .value_symbol_links(symbol)
                .is_none_or(|links| links == &ValueSymbolLinks::default())
        );
    }

    #[test]
    fn published_instance_members_cannot_be_reused_as_a_cold_class_shell() {
        let mut fixture = fixture("class Model {}");
        let owner = class_symbol(&fixture, "Model");
        let bound = &fixture.files[&fixture.file];
        let host = host(&fixture.parsed.arena, bound);
        let instance = fixture
            .store
            .get_declared_type_of_symbol(&host, owner)
            .unwrap();
        assert!(
            fixture
                .store
                .set_interface_declared_members(instance, true, None, None, None, None,)
        );
        let plan = plan_nongeneric_class(&fixture.store, &host, owner).unwrap();
        let state = (
            fixture.store.type_len(),
            fixture.store.signature_len(),
            fixture.store.checker_link_allocated_lengths(),
        );

        assert_eq!(
            execute_nongeneric_class_shells(&mut fixture.store, &host, &plan),
            Err(invariant(ClassInvariant::InvalidInstanceCache(owner)))
        );
        assert_eq!(
            (
                fixture.store.type_len(),
                fixture.store.signature_len(),
                fixture.store.checker_link_allocated_lengths(),
            ),
            state
        );
        assert!(fixture.store.value_symbol_links(owner).is_none());
    }

    #[test]
    fn no_base_class_shell_rejects_forged_direct_heritage_provenance() {
        let mut fixture = fixture("class Base {} class Model {}");
        let base_owner = class_symbol(&fixture, "Base");
        let owner = class_symbol(&fixture, "Model");
        let bound = &fixture.files[&fixture.file];
        let host = host(&fixture.parsed.arena, bound);
        let base_plan = plan_nongeneric_class_members(&fixture.store, &host, base_owner).unwrap();
        let base = execute_nongeneric_class_members(&mut fixture.store, &host, &base_plan).unwrap();
        let plan = plan_nongeneric_class(&fixture.store, &host, owner).unwrap();
        let shells = execute_nongeneric_class_shells(&mut fixture.store, &host, &plan).unwrap();
        assert!(fixture.store.publish_direct_class_heritage_provenance(
            shells.instance_type(),
            DirectClassHeritageProvenance {
                owner_symbol: owner,
                owner_value_type: shells.value_type(),
                base_symbol: base_owner,
                base_instance_type: base.shells().instance_type(),
                base_value_type: base.shells().value_type(),
            },
        ));
        let state = (
            fixture.store.type_len(),
            fixture.store.signature_len(),
            fixture.store.symbol_store().symbol_table_len(),
            fixture.store.checker_link_allocated_lengths(),
        );

        assert_eq!(
            execute_nongeneric_class_shells(&mut fixture.store, &host, &plan),
            Err(invariant(ClassInvariant::InvalidInstanceCache(owner)))
        );
        assert_eq!(
            (
                fixture.store.type_len(),
                fixture.store.signature_len(),
                fixture.store.symbol_store().symbol_table_len(),
                fixture.store.checker_link_allocated_lengths(),
            ),
            state
        );
    }

    #[test]
    fn unsupported_class_families_are_typed_and_do_not_publish_shells() {
        let cases = [
            ("class Generic<T> {}", "Generic"),
            ("class Base {} class Derived extends Base {}", "Derived"),
            ("class Method { method(): void { return; } }", "Method"),
            ("class Initialized { value = 1; }", "Initialized"),
            ("class Reserved { static prototype: number; }", "Reserved"),
            (
                "class StaticDefinite { static value!: number; }",
                "StaticDefinite",
            ),
        ];
        for (source, name) in cases {
            let fixture = fixture(source);
            let symbol = class_symbol(&fixture, name);
            let bound = &fixture.files[&fixture.file];
            let host = host(&fixture.parsed.arena, bound);
            let state = (
                fixture.store.type_len(),
                fixture.store.checker_link_allocated_lengths(),
            );
            let result = plan_nongeneric_class(&fixture.store, &host, symbol);
            assert!(
                matches!(result, Err(ClassError::Unsupported(_))),
                "{source}: {result:?}"
            );
            assert_eq!(
                (
                    fixture.store.type_len(),
                    fixture.store.checker_link_allocated_lengths(),
                ),
                state
            );
            assert!(
                fixture
                    .store
                    .declared_type_links(symbol)
                    .and_then(|links| links.declared_type)
                    .is_none()
            );
            assert!(
                fixture
                    .store
                    .value_symbol_links(symbol)
                    .is_none_or(|links| links == &ValueSymbolLinks::default())
            );
        }
    }

    #[test]
    fn unsupported_later_annotation_is_rejected_before_any_class_publication() {
        let fixture = fixture("class Missing {} class Model { first: string; second: Missing; }");
        let symbol = class_symbol(&fixture, "Model");
        let bound = &fixture.files[&fixture.file];
        let host = host(&fixture.parsed.arena, bound);
        let state = (
            fixture.store.type_len(),
            fixture.store.signature_len(),
            fixture.store.symbol_store().symbol_table_len(),
            fixture.store.checker_link_allocated_lengths(),
            fixture.store.relation_state_snapshot(),
        );

        assert!(matches!(
            plan_nongeneric_class_members(&fixture.store, &host, symbol),
            Err(ClassError::Unsupported(ClassUnsupported::PropertyType {
                kind: SyntaxKind::TypeReference,
                ..
            }))
        ));
        assert_eq!(
            (
                fixture.store.type_len(),
                fixture.store.signature_len(),
                fixture.store.symbol_store().symbol_table_len(),
                fixture.store.checker_link_allocated_lengths(),
                fixture.store.relation_state_snapshot(),
            ),
            state
        );
        assert!(
            fixture
                .store
                .declared_type_links(symbol)
                .and_then(|links| links.declared_type)
                .is_none()
        );
        assert!(
            fixture
                .store
                .value_symbol_links(symbol)
                .is_none_or(|links| links == &ValueSymbolLinks::default())
        );
    }

    #[test]
    fn wrong_later_annotation_cache_rejects_before_an_earlier_property_or_shell_is_written() {
        let mut fixture = fixture("class Model { first: string; second: number; }");
        let symbol = class_symbol(&fixture, "Model");
        let bound = &fixture.files[&fixture.file];
        let host = host(&fixture.parsed.arena, bound);
        let shell_plan = plan_nongeneric_class(&fixture.store, &host, symbol).unwrap();
        let second = shell_plan.properties()[1].type_node();
        let wrong = fixture.store.intrinsic_bootstrap().unwrap().string_type;
        assert!(fixture.store.set_type_node_links(
            second,
            TypeNodeLinks {
                resolved_type: Some(wrong),
                ..TypeNodeLinks::default()
            },
        ));
        let state = (
            fixture.store.type_len(),
            fixture.store.signature_len(),
            fixture.store.symbol_store().symbol_table_len(),
            fixture.store.checker_link_allocated_lengths(),
            fixture.store.relation_state_snapshot(),
        );

        assert_eq!(
            plan_nongeneric_class_members(&fixture.store, &host, symbol),
            Err(invariant(ClassInvariant::InvalidPropertyTypeCache(second)))
        );
        assert_eq!(
            (
                fixture.store.type_len(),
                fixture.store.signature_len(),
                fixture.store.symbol_store().symbol_table_len(),
                fixture.store.checker_link_allocated_lengths(),
                fixture.store.relation_state_snapshot(),
            ),
            state
        );
        assert!(shell_plan.properties().iter().all(|property| {
            fixture
                .store
                .value_symbol_links(property.symbol())
                .is_none_or(|links| links == &ValueSymbolLinks::default())
        }));
        assert!(
            fixture
                .store
                .declared_type_links(symbol)
                .and_then(|links| links.declared_type)
                .is_none()
        );
    }

    #[test]
    fn poisoned_completed_constructor_is_rejected_without_further_mutation() {
        let mut fixture = fixture("class Model { value: string; static count: number; }");
        let symbol = class_symbol(&fixture, "Model");
        let bound = &fixture.files[&fixture.file];
        let host = host(&fixture.parsed.arena, bound);
        let plan = plan_nongeneric_class_members(&fixture.store, &host, symbol).unwrap();
        let members = execute_nongeneric_class_members(&mut fixture.store, &host, &plan).unwrap();
        let wrong = fixture.store.intrinsic_bootstrap().unwrap().number_type;
        assert!(fixture.store.set_signature_resolved_return_type(
            members.default_construct_signature(),
            Some(wrong),
        ));
        let state = (
            fixture.store.type_len(),
            fixture.store.signature_len(),
            fixture.store.symbol_store().symbol_table_len(),
            fixture.store.checker_link_allocated_lengths(),
            fixture.store.relation_state_snapshot(),
        );

        let retry_plan = plan_nongeneric_class_members(&fixture.store, &host, symbol).unwrap();
        assert!(matches!(
            execute_nongeneric_class_members(&mut fixture.store, &host, &retry_plan),
            Err(ClassError::Invariant(
                ClassInvariant::InvalidInstanceMembers(_) | ClassInvariant::InvalidStaticMembers(_)
            ))
        ));
        assert_eq!(
            (
                fixture.store.type_len(),
                fixture.store.signature_len(),
                fixture.store.symbol_store().symbol_table_len(),
                fixture.store.checker_link_allocated_lengths(),
                fixture.store.relation_state_snapshot(),
            ),
            state
        );
        assert_eq!(
            fixture
                .store
                .signature(members.default_construct_signature())
                .and_then(super::super::signatures::Signature::resolved_return_type),
            Some(wrong)
        );
    }

    #[test]
    fn poisoned_later_derived_annotation_rejects_before_base_or_derived_publication() {
        let mut fixture = fixture(
            "class Base { base: string; } \
             class Derived extends Base { first: string; second: number; }",
        );
        let base_symbol = class_symbol(&fixture, "Base");
        let derived_symbol = class_symbol(&fixture, "Derived");
        let bound = &fixture.files[&fixture.file];
        let host = host(&fixture.parsed.arena, bound);
        let plan =
            plan_nongeneric_class_member_query(&fixture.store, &host, derived_symbol).unwrap();
        let ClassMemberQueryPlan::Derived { class, base } = &plan else {
            panic!("Derived retains one exact direct base")
        };
        let second = class.class.properties()[1].type_node();
        let wrong = fixture.store.intrinsic_bootstrap().unwrap().string_type;
        assert!(fixture.store.set_type_node_links(
            second,
            TypeNodeLinks {
                resolved_type: Some(wrong),
                ..TypeNodeLinks::default()
            },
        ));
        let state = (
            fixture.store.type_len(),
            fixture.store.signature_len(),
            fixture.store.symbol_store().symbol_table_len(),
            fixture.store.checker_link_allocated_lengths(),
            fixture.store.relation_state_snapshot(),
        );

        assert_eq!(
            execute_nongeneric_class_member_query(&mut fixture.store, &host, &plan),
            Err(invariant(ClassInvariant::InvalidPropertyTypeCache(second)))
        );
        assert_eq!(
            (
                fixture.store.type_len(),
                fixture.store.signature_len(),
                fixture.store.symbol_store().symbol_table_len(),
                fixture.store.checker_link_allocated_lengths(),
                fixture.store.relation_state_snapshot(),
            ),
            state
        );
        for symbol in [base_symbol, derived_symbol] {
            assert!(
                fixture
                    .store
                    .declared_type_links(symbol)
                    .and_then(|links| links.declared_type)
                    .is_none()
            );
            assert!(
                fixture
                    .store
                    .value_symbol_links(symbol)
                    .is_none_or(|links| links == &ValueSymbolLinks::default())
            );
        }
        assert!(base.class.properties().iter().all(|property| {
            fixture
                .store
                .value_symbol_links(property.symbol())
                .is_none_or(|links| links == &ValueSymbolLinks::default())
        }));
    }

    #[test]
    fn poisoned_direct_base_cache_cannot_hide_behind_a_warm_relation() {
        let mut fixture = fixture(
            "class Base { base?: string; } \
             class Derived extends Base { own: number; }",
        );
        let derived_symbol = class_symbol(&fixture, "Derived");
        let bound = &fixture.files[&fixture.file];
        let host = host(&fixture.parsed.arena, bound);
        let plan =
            plan_nongeneric_class_member_query(&fixture.store, &host, derived_symbol).unwrap();
        let members =
            execute_nongeneric_class_member_query(&mut fixture.store, &host, &plan).unwrap();
        let derived_type = members.shells().instance_type();
        let base = members.base().expect("Derived retains its direct base");
        assert_eq!(
            fixture
                .store
                .is_type_assignable_to(derived_type, base.instance_type()),
            Ok(true)
        );
        assert_eq!(
            validate_class_heritage_members(&fixture.store, derived_type),
            ClassHeritageMembersValidation::Valid
        );
        assert!(fixture.store.set_interface_base_resolution(
            derived_type,
            true,
            Some(base.value_type()),
            Some(vec![derived_type]),
        ));
        let poisoned = (
            fixture.store.type_len(),
            fixture.store.signature_len(),
            fixture.store.symbol_store().symbol_table_len(),
            fixture.store.checker_link_allocated_lengths(),
            fixture.store.relation_state_snapshot(),
        );

        assert_eq!(
            validate_class_heritage_members(&fixture.store, derived_type),
            ClassHeritageMembersValidation::Malformed
        );
        assert_eq!(
            fixture
                .store
                .is_type_assignable_to(derived_type, base.instance_type()),
            Err(
                super::super::relater::RelationUnavailable::InvalidStructuredMembers(derived_type,)
            )
        );
        assert_eq!(
            execute_nongeneric_class_member_query(&mut fixture.store, &host, &plan),
            Err(invariant(ClassInvariant::InvalidHeritageCache(
                derived_symbol,
            )))
        );
        assert_eq!(
            (
                fixture.store.type_len(),
                fixture.store.signature_len(),
                fixture.store.symbol_store().symbol_table_len(),
                fixture.store.checker_link_allocated_lengths(),
                fixture.store.relation_state_snapshot(),
            ),
            poisoned
        );
    }

    #[test]
    fn poisoned_derived_constructor_signature_is_rejected_before_cached_identity() {
        let mut fixture = fixture(
            "class Base { base: string; } \
             class Derived extends Base { own: number; }",
        );
        let derived_symbol = class_symbol(&fixture, "Derived");
        let bound = &fixture.files[&fixture.file];
        let host = host(&fixture.parsed.arena, bound);
        let plan =
            plan_nongeneric_class_member_query(&fixture.store, &host, derived_symbol).unwrap();
        let members =
            execute_nongeneric_class_member_query(&mut fixture.store, &host, &plan).unwrap();
        let derived_type = members.shells().instance_type();
        let base_type = members
            .base()
            .expect("Derived retains its direct base")
            .instance_type();
        assert_eq!(
            fixture.store.is_type_assignable_to(derived_type, base_type),
            Ok(true)
        );
        let wrong = fixture.store.intrinsic_bootstrap().unwrap().number_type;
        assert!(fixture.store.set_signature_resolved_return_type(
            members.default_construct_signature(),
            Some(wrong),
        ));
        let poisoned = (
            fixture.store.type_len(),
            fixture.store.signature_len(),
            fixture.store.symbol_store().symbol_table_len(),
            fixture.store.checker_link_allocated_lengths(),
            fixture.store.relation_state_snapshot(),
        );

        assert_eq!(
            validate_class_heritage_members(&fixture.store, derived_type),
            ClassHeritageMembersValidation::Malformed
        );
        assert_eq!(
            fixture.store.is_type_assignable_to(derived_type, base_type),
            Err(
                super::super::relater::RelationUnavailable::InvalidStructuredMembers(derived_type,)
            )
        );
        assert_eq!(
            execute_nongeneric_class_member_query(&mut fixture.store, &host, &plan),
            Err(invariant(ClassInvariant::InvalidHeritageCache(
                derived_symbol,
            )))
        );
        assert_eq!(
            (
                fixture.store.type_len(),
                fixture.store.signature_len(),
                fixture.store.symbol_store().symbol_table_len(),
                fixture.store.checker_link_allocated_lengths(),
                fixture.store.relation_state_snapshot(),
            ),
            poisoned
        );
    }

    #[derive(Clone, Copy)]
    enum ShadowTablePoison {
        Instance,
        Static,
    }

    fn assert_shadow_table_poison_rejected(poison: ShadowTablePoison) {
        let mut fixture = fixture(
            "class Base { same: string; static shared: number; } \
             class Derived extends Base { same: string; static shared: string; }",
        );
        let derived_symbol = class_symbol(&fixture, "Derived");
        let bound = &fixture.files[&fixture.file];
        let host = host(&fixture.parsed.arena, bound);
        let plan =
            plan_nongeneric_class_member_query(&fixture.store, &host, derived_symbol).unwrap();
        let members =
            execute_nongeneric_class_member_query(&mut fixture.store, &host, &plan).unwrap();
        let derived_type = members.shells().instance_type();
        let base_type = members
            .base()
            .expect("Derived retains its direct base")
            .instance_type();
        let relation_cold = fixture.store.relation_state_snapshot();
        assert_eq!(
            fixture.store.is_type_assignable_to(derived_type, base_type),
            Ok(true)
        );
        assert_ne!(fixture.store.relation_state_snapshot(), relation_cold);

        match poison {
            ShadowTablePoison::Instance => {
                let declared = fixture
                    .store
                    .symbol(derived_symbol)
                    .and_then(Symbol::members)
                    .expect("Derived retains its declared instance table");
                assert_ne!(members.instance_members(), Some(declared));
                assert!(fixture.store.set_structured_type_members(
                    derived_type,
                    Some(declared),
                    Some(members.instance_properties().to_vec()),
                    None,
                    None,
                    None,
                ));
            }
            ShadowTablePoison::Static => {
                let declared = fixture
                    .store
                    .symbol(derived_symbol)
                    .and_then(Symbol::exports)
                    .expect("Derived retains its declared static table");
                assert_ne!(members.static_members(), declared);
                let mut properties = members.static_properties().to_vec();
                properties.push(members.prototype());
                assert!(fixture.store.set_structured_type_members(
                    members.shells().value_type(),
                    Some(declared),
                    Some(properties),
                    None,
                    Some(vec![members.default_construct_signature()]),
                    None,
                ));
            }
        }
        let poisoned = (
            fixture.store.type_len(),
            fixture.store.signature_len(),
            fixture.store.symbol_store().symbol_table_len(),
            fixture.store.checker_link_allocated_lengths(),
            fixture.store.relation_state_snapshot(),
        );

        assert_eq!(
            validate_class_heritage_members(&fixture.store, derived_type),
            ClassHeritageMembersValidation::Malformed
        );
        assert_eq!(
            fixture.store.is_type_assignable_to(derived_type, base_type),
            Err(
                super::super::relater::RelationUnavailable::InvalidStructuredMembers(derived_type,)
            )
        );
        assert_eq!(
            execute_nongeneric_class_member_query(&mut fixture.store, &host, &plan),
            Err(invariant(ClassInvariant::InvalidHeritageCache(
                derived_symbol,
            )))
        );
        assert_eq!(
            (
                fixture.store.type_len(),
                fixture.store.signature_len(),
                fixture.store.symbol_store().symbol_table_len(),
                fixture.store.checker_link_allocated_lengths(),
                fixture.store.relation_state_snapshot(),
            ),
            poisoned
        );
    }

    #[test]
    fn shadowed_surfaces_reject_binder_table_substitution_after_a_warm_relation() {
        for poison in [ShadowTablePoison::Instance, ShadowTablePoison::Static] {
            assert_shadow_table_poison_rejected(poison);
        }
    }

    #[test]
    fn relation_rejects_a_declared_class_table_with_a_source_wrong_key() {
        let mut fixture = fixture("class Model { value: string; } class Shape { value: string; }");
        let model_symbol = class_symbol(&fixture, "Model");
        let shape_symbol = class_symbol(&fixture, "Shape");
        let bound = &fixture.files[&fixture.file];
        let host = host(&fixture.parsed.arena, bound);
        let model_plan =
            plan_nongeneric_class_member_query(&fixture.store, &host, model_symbol).unwrap();
        let shape_plan =
            plan_nongeneric_class_member_query(&fixture.store, &host, shape_symbol).unwrap();
        let model =
            execute_nongeneric_class_member_query(&mut fixture.store, &host, &model_plan).unwrap();
        let shape =
            execute_nongeneric_class_member_query(&mut fixture.store, &host, &shape_plan).unwrap();
        let model_type = model.shells().instance_type();
        let shape_type = shape.shells().instance_type();
        assert_eq!(
            fixture.store.is_type_assignable_to(model_type, shape_type),
            Ok(true)
        );
        let [property] = model.declared_instance_properties() else {
            panic!("Model retains one declared property")
        };
        let exports = fixture
            .store
            .symbol(model_symbol)
            .and_then(Symbol::exports)
            .expect("Model retains its static table");
        let wrong_members = fixture.store.alloc_symbol_table();
        assert_eq!(
            fixture.store.insert_symbol(
                wrong_members,
                EscapedName::source("sourceWrong"),
                *property,
            ),
            Some(None)
        );
        assert!(fixture.store.set_symbol_relationships(
            model_symbol,
            Some(wrong_members),
            Some(exports),
            None,
            None,
        ));
        assert!(fixture.store.set_interface_declared_members(
            model_type,
            true,
            Some(wrong_members),
            None,
            None,
            None,
        ));
        let poisoned = fixture.store.relation_state_snapshot();

        assert_eq!(
            validate_class_heritage_members(&fixture.store, model_type),
            ClassHeritageMembersValidation::Malformed
        );
        assert_eq!(
            fixture.store.is_type_assignable_to(model_type, shape_type),
            Err(super::super::relater::RelationUnavailable::InvalidStructuredMembers(model_type,))
        );
        assert_eq!(fixture.store.relation_state_snapshot(), poisoned);
    }

    #[test]
    fn forged_provenance_on_a_no_base_dependency_rejects_the_derived_transaction() {
        let mut fixture = fixture(
            "class Other { other: string; } \
             class Base { base: string; } \
             class Derived extends Base { own: string; }",
        );
        let other_symbol = class_symbol(&fixture, "Other");
        let base_symbol = class_symbol(&fixture, "Base");
        let derived_symbol = class_symbol(&fixture, "Derived");
        let bound = &fixture.files[&fixture.file];
        let host = host(&fixture.parsed.arena, bound);
        let other_plan =
            plan_nongeneric_class_member_query(&fixture.store, &host, other_symbol).unwrap();
        let base_plan =
            plan_nongeneric_class_member_query(&fixture.store, &host, base_symbol).unwrap();
        let derived_plan =
            plan_nongeneric_class_member_query(&fixture.store, &host, derived_symbol).unwrap();
        let other =
            execute_nongeneric_class_member_query(&mut fixture.store, &host, &other_plan).unwrap();
        let base =
            execute_nongeneric_class_member_query(&mut fixture.store, &host, &base_plan).unwrap();
        assert!(fixture.store.publish_direct_class_heritage_provenance(
            base.shells().instance_type(),
            DirectClassHeritageProvenance {
                owner_symbol: base_symbol,
                owner_value_type: base.shells().value_type(),
                base_symbol: other_symbol,
                base_instance_type: other.shells().instance_type(),
                base_value_type: other.shells().value_type(),
            },
        ));
        let poisoned = (
            fixture.store.type_len(),
            fixture.store.signature_len(),
            fixture.store.symbol_store().symbol_table_len(),
            fixture.store.checker_link_allocated_lengths(),
            fixture.store.relation_state_snapshot(),
        );

        assert_eq!(
            validate_class_heritage_members(&fixture.store, base.shells().instance_type()),
            ClassHeritageMembersValidation::Malformed
        );
        assert_eq!(
            execute_nongeneric_class_member_query(&mut fixture.store, &host, &derived_plan),
            Err(invariant(ClassInvariant::InvalidInstanceMembers(
                base_symbol,
            )))
        );
        assert_eq!(
            (
                fixture.store.type_len(),
                fixture.store.signature_len(),
                fixture.store.symbol_store().symbol_table_len(),
                fixture.store.checker_link_allocated_lengths(),
                fixture.store.relation_state_snapshot(),
            ),
            poisoned
        );
        assert!(
            fixture
                .store
                .declared_type_links(derived_symbol)
                .and_then(|links| links.declared_type)
                .is_none()
        );
        assert!(
            fixture
                .store
                .value_symbol_links(derived_symbol)
                .and_then(|links| links.resolved_type)
                .is_none()
        );
    }
}
