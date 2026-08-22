//! Declared object-member construction for the canonical checker.
//!
//! This module owns the exact syntax-to-member-table boundary.  It deliberately
//! does not recurse through property annotations: [`super::type_nodes`] plans
//! and executes property, index, and call-signature annotations so one query
//! retains a single dependency graph and resolution stack. Declared call sets
//! are limited to pure nongeneric, fixed-arity call-signature members; mixed
//! and optional/rest/construct forms remain explicit boundaries.

use std::collections::HashSet;

use ts_ast::{NodeData, NodeList, NodeRef, SyntaxKind};
use ts_binder::{
    CheckFlags, EscapedName, InternalSymbolName, SemanticSymbolId, SymbolData, SymbolFlags,
    SymbolTableId, semantic::PreparedSymbolTable,
};

use super::{
    CanonicalTypeMapperStore, DeclaredTypeHost, SignatureId, TypeId,
    declared::{cached_ordinary_type_parameter_owner, preflight_node},
    interface_heritage::{
        DirectInterfaceHeritageError, DirectInterfaceHeritagePlan, plan_direct_interface_heritage,
    },
    links::{ResolvedSignatureState, SignatureLinks, ValueSymbolLinks},
    reference_types::validate_direct_generic_reference,
    signatures::SignatureFlags,
    store::SourceNodeParent,
    type_records::{
        ConstrainedTypeData, InterfaceTypeData, ObjectTypeData, StructuredTypeData, TypeCacheState,
        TypeData, TypeRecord,
    },
    types::{ObjectFlags, TypeFlags},
};

const NODE_FLAG_JSDOC: u32 = 1 << 22;
const NODE_FLAG_HAS_ERROR: u32 = 1 << 15;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum PropertyObjectKind {
    TypeLiteral,
    Interface,
    ObjectLiteral,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum TypeLiteralMemberPolicy {
    General,
    ConcreteIndexedAccess,
    GenericInterface,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct PlannedProperty {
    pub declaration: NodeRef,
    pub symbol: SemanticSymbolId,
    #[allow(dead_code)] // Retained for the next property-diagnostic range slice.
    pub name_node: NodeRef,
    pub type_node: NodeRef,
    pub optional: bool,
    pub readonly: bool,
    pub name: String,
}

const fn source_property_check_flags(readonly: bool) -> CheckFlags {
    if readonly {
        CheckFlags::READONLY
    } else {
        CheckFlags::NONE
    }
}

/// One exact source-declared index signature admitted by the first A11 cut.
///
/// The bound `__index` symbol is a signature-container member. It is not the
/// synthetic property cached later in [`super::signatures::IndexInfo`], so
/// publication deliberately leaves `IndexInfo::index_symbol` empty.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct PlannedIndexSignature {
    pub declaration: NodeRef,
    pub symbol: SemanticSymbolId,
    pub key_type_node: NodeRef,
    pub value_type_node: NodeRef,
    pub readonly: bool,
}

/// One required identifier parameter in an admitted declared call signature.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct PlannedCallParameter {
    pub symbol: SemanticSymbolId,
    pub type_node: NodeRef,
    identity_node: NodeRef,
    null_literal_identity: bool,
}

/// One nongeneric, fixed-arity call signature in source declaration order.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct PlannedCallSignature {
    pub declaration: NodeRef,
    pub symbol: SemanticSymbolId,
    pub parameters: Vec<PlannedCallParameter>,
    pub return_type: NodeRef,
    return_identity_node: NodeRef,
    return_null_literal_identity: bool,
    flags: SignatureFlags,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct ResolvedCallSignatureTypes {
    pub parameter_types: Vec<TypeId>,
    pub return_type: TypeId,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct PropertyObjectPlan {
    pub kind: PropertyObjectKind,
    pub node: NodeRef,
    pub symbol: SemanticSymbolId,
    pub members: Option<SymbolTableId>,
    pub properties: Vec<PlannedProperty>,
    pub indexes: Vec<PlannedIndexSignature>,
    pub call_signatures: Vec<PlannedCallSignature>,
    pub alias_symbol: Option<SemanticSymbolId>,
    pub heritage: Option<DirectInterfaceHeritagePlan>,
}

impl PropertyObjectPlan {
    pub(super) fn property_type_nodes(&self) -> impl ExactSizeIterator<Item = NodeRef> + '_ {
        self.properties.iter().map(|property| property.type_node)
    }

    pub(super) fn index_type_nodes(
        &self,
    ) -> impl ExactSizeIterator<Item = (NodeRef, NodeRef)> + '_ {
        self.indexes
            .iter()
            .map(|index| (index.key_type_node, index.value_type_node))
    }

    pub(super) fn call_type_nodes(&self) -> impl Iterator<Item = NodeRef> + '_ {
        self.call_signatures.iter().flat_map(|signature| {
            signature
                .parameters
                .iter()
                .map(|parameter| parameter.type_node)
                .chain(std::iter::once(signature.return_type))
        })
    }

    pub(super) fn heritage_base_symbols(
        &self,
    ) -> impl ExactSizeIterator<Item = SemanticSymbolId> + '_ {
        let bases = self
            .heritage
            .as_ref()
            .map_or(&[][..], |heritage| heritage.bases.as_slice());
        bases.iter().map(|base| base.symbol)
    }

    fn property_symbols(&self) -> Vec<SemanticSymbolId> {
        self.properties
            .iter()
            .map(|property| property.symbol)
            .collect()
    }

    fn expected_properties(&self) -> Option<Vec<SemanticSymbolId>> {
        (!self.properties.is_empty()).then(|| self.property_symbols())
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum PropertyObjectState {
    EmptyBootstrap(TypeId),
    Shell(TypeId),
    Resolved(TypeId),
}

/// Read-only evidence that a resolved object belongs to the installed,
/// nongeneric declared-property prefix.
///
/// This is intentionally distinct from expression object literals. Declared
/// properties may refer back to their owner (for example `Node.next: Node`),
/// so callers validate each property type as a store-owned identity without
/// recursively requiring it to belong to a narrower construction domain.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum DeclaredPropertyObjectProof {
    Interface,
    TypeLiteral,
}

/// Distinguishes a supported proof from an intentional coverage boundary and
/// a corrupt cache that claimed to be a supported declared property object.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum DeclaredPropertyObjectValidation {
    Valid(DeclaredPropertyObjectProof),
    NotDeclared,
    Malformed,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) enum StoredDeclaredCallSetValidation {
    NotDeclaredCallSet,
    Valid(Vec<TypeId>),
    Malformed,
}

/// Validates the source-owned interface/type-literal provider without an AST
/// host. The publication brand distinguishes this narrow provider from
/// arbitrary object types that happen to carry structured signatures.
pub(super) fn validate_stored_declared_call_set(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
) -> StoredDeclaredCallSetValidation {
    if !store.type_has_declared_call_set_provenance(type_) {
        return StoredDeclaredCallSetValidation::NotDeclaredCallSet;
    }
    let Some(record) = store.type_payload(type_) else {
        return StoredDeclaredCallSetValidation::Malformed;
    };
    let Some(owner) = record.symbol() else {
        return StoredDeclaredCallSetValidation::Malformed;
    };
    let Some(owner_record) = store.symbol(owner) else {
        return StoredDeclaredCallSetValidation::Malformed;
    };
    let (owner_declaration, structured, members, exact_owner) = match record.data() {
        TypeData::Object(object) => {
            let Some([declaration]) = owner_record.declarations() else {
                return StoredDeclaredCallSetValidation::Malformed;
            };
            let alias_valid = match record.alias() {
                None => true,
                Some(alias) => store.type_alias(alias).is_some_and(|alias| {
                    alias.type_arguments().is_none()
                        && alias.symbol().is_some_and(|symbol| {
                            store.type_alias_links(symbol).is_some_and(|links| {
                                links.declared_type == Some(type_)
                                    && links.type_parameters.is_none()
                                    && links.instantiations.is_none()
                            })
                        })
                }),
            };
            let exact = record.flags() == TypeFlags::OBJECT
                && record.object_flags() == ObjectFlags::ANONYMOUS | ObjectFlags::MEMBERS_RESOLVED
                && owner_record.flags() == SymbolFlags::TYPE_LITERAL
                && owner_record.check_flags() == CheckFlags::NONE
                && owner_record.name() == InternalSymbolName::Type.as_ref()
                && owner_record.value_declaration().is_none()
                && owner_record.exports().is_none()
                && owner_record.parent().is_none()
                && owner_record.export_symbol().is_none()
                && store.get_merged_symbol(owner) == Some(owner)
                && store.source_node_kind(*declaration) == Some(SyntaxKind::TypeLiteral)
                && store.type_node_links(*declaration).is_some_and(|links| {
                    links.resolved_type == Some(type_) && links.outer_type_parameters.is_none()
                })
                && alias_valid
                && valid_object_tail(object);
            (
                *declaration,
                &object.structured,
                owner_record.members(),
                exact,
            )
        }
        TypeData::Interface(interface) => {
            let Some([declaration]) = owner_record.declarations() else {
                return StoredDeclaredCallSetValidation::Malformed;
            };
            let exact = record.flags() == TypeFlags::OBJECT
                && record.object_flags() == ObjectFlags::INTERFACE | ObjectFlags::MEMBERS_RESOLVED
                && record.alias().is_none()
                && owner_record.flags() == SymbolFlags::INTERFACE
                && owner_record.check_flags() == CheckFlags::NONE
                && owner_record.name().as_utf8().is_some()
                && owner_record.value_declaration().is_none()
                && owner_record.members() == interface.declared_members
                && owner_record.exports().is_none()
                && owner_record.export_symbol().is_none()
                && store.get_merged_symbol(owner) == Some(owner)
                && store.source_node_kind(*declaration) == Some(SyntaxKind::InterfaceDeclaration)
                && store
                    .declared_type_links(owner)
                    .is_some_and(|links| links.declared_type == Some(type_))
                && valid_thisless_interface_identity(interface)
                && interface.base_types_resolved
                && interface.resolved_base_constructor_type.is_none()
                && interface.resolved_base_types.is_none()
                && interface.declared_members_resolved
                && interface.declared_construct_signatures.is_none()
                && interface.declared_index_infos.is_none()
                && interface.declared_call_signatures.as_deref()
                    == interface.reference.object.structured.signatures.as_deref();
            (
                *declaration,
                &interface.reference.object.structured,
                owner_record.members(),
                exact,
            )
        }
        _ => return StoredDeclaredCallSetValidation::Malformed,
    };
    let Some(signatures) = structured.signatures.as_deref() else {
        return StoredDeclaredCallSetValidation::Malformed;
    };
    if !exact_owner
        || signatures.is_empty()
        || structured.constrained != ConstrainedTypeData::default()
        || structured.members != members
        || structured.properties.is_some()
        || structured.call_signature_count != signatures.len()
        || structured.index_infos.is_some()
        || structured
            .object_type_without_abstract_construct_signatures
            .is_some()
    {
        return StoredDeclaredCallSetValidation::Malformed;
    }
    let Some(members) = members.and_then(|members| store.symbol_table(members)) else {
        return StoredDeclaredCallSetValidation::Malformed;
    };
    let Some(call_symbol) = members
        .get(InternalSymbolName::Call.as_ref())
        .filter(|_| members.len() == 1)
    else {
        return StoredDeclaredCallSetValidation::Malformed;
    };
    let Some(call_record) = store.symbol(call_symbol) else {
        return StoredDeclaredCallSetValidation::Malformed;
    };
    let declarations = signatures
        .iter()
        .filter_map(|signature| store.signature(*signature)?.declaration())
        .collect::<Vec<_>>();
    if declarations.len() != signatures.len()
        || call_record.flags() != SymbolFlags::SIGNATURE
        || call_record.check_flags() != CheckFlags::NONE
        || call_record.name() != InternalSymbolName::Call.as_ref()
        || call_record.declarations() != Some(declarations.as_slice())
        || call_record.value_declaration().is_some()
        || call_record.members().is_some()
        || call_record.exports().is_some()
        || call_record.parent() != Some(owner)
        || call_record.export_symbol().is_some()
        || store.get_merged_symbol(call_symbol) != Some(call_symbol)
    {
        return StoredDeclaredCallSetValidation::Malformed;
    }

    let mut edges = Vec::new();
    let mut seen_signatures = HashSet::with_capacity(signatures.len());
    for (signature, declaration) in signatures.iter().copied().zip(declarations) {
        let Some(signature_record) = store.signature(signature) else {
            return StoredDeclaredCallSetValidation::Malformed;
        };
        let Some(parameter_types) = store.callable_signature_parameter_types(signature) else {
            return StoredDeclaredCallSetValidation::Malformed;
        };
        let Some(return_type) = signature_record.resolved_return_type() else {
            return StoredDeclaredCallSetValidation::Malformed;
        };
        let Some((return_annotation, null_literal_identity)) =
            store.function_signature_return_annotation(signature)
        else {
            return StoredDeclaredCallSetValidation::Malformed;
        };
        let minimum = usize::try_from(signature_record.min_argument_count()).ok();
        if !seen_signatures.insert(signature)
            || store.declared_call_set_type_for_signature(signature) != Some(type_)
            || store.source_node_kind(declaration) != Some(SyntaxKind::CallSignature)
            || store.source_node_parent(declaration)
                != Some(SourceNodeParent::Parent(owner_declaration))
            || store.signature_links(declaration)
                != Some(&SignatureLinks {
                    resolved_signature: ResolvedSignatureState::Resolved(signature),
                    ..SignatureLinks::default()
                })
            || signature_record.flags().bits() & !SignatureFlags::HAS_LITERAL_TYPES.bits() != 0
            || signature_record.resolved_min_argument_count() != -1
            || minimum != Some(signature_record.parameters().len())
            || !signature_record.type_parameters().is_empty()
            || signature_record.this_parameter().is_some()
            || signature_record.resolved_type_predicate().is_some()
            || signature_record.target().is_some()
            || signature_record.mapper().is_some()
            || signature_record.isolated_signature_type().is_some()
            || signature_record.composite().is_some()
            || store.signature_has_circular_return_type(signature)
            || cached_annotation_identity(store, return_annotation, null_literal_identity)
                != Some(return_type)
            || parameter_types.len() != signature_record.parameters().len()
        {
            return StoredDeclaredCallSetValidation::Malformed;
        }
        let mut seen_parameters = HashSet::with_capacity(parameter_types.len());
        for (parameter, type_) in signature_record
            .parameters()
            .iter()
            .copied()
            .zip(parameter_types)
        {
            let Some(parameter_record) = store.symbol(parameter) else {
                return StoredDeclaredCallSetValidation::Malformed;
            };
            let Some([parameter_declaration]) = parameter_record.declarations() else {
                return StoredDeclaredCallSetValidation::Malformed;
            };
            if !seen_parameters.insert(parameter)
                || parameter_record.flags() != SymbolFlags::FUNCTION_SCOPED_VARIABLE
                || parameter_record.check_flags() != CheckFlags::NONE
                || parameter_record.value_declaration() != Some(*parameter_declaration)
                || parameter_record.members().is_some()
                || parameter_record.exports().is_some()
                || parameter_record.parent().is_some()
                || parameter_record.export_symbol().is_some()
                || store.get_merged_symbol(parameter) != Some(parameter)
                || store.source_node_kind(*parameter_declaration) != Some(SyntaxKind::Parameter)
                || store.source_node_parent(*parameter_declaration)
                    != Some(SourceNodeParent::Parent(declaration))
                || store.value_symbol_links(parameter)
                    != Some(&ValueSymbolLinks {
                        resolved_type: Some(*type_),
                        ..ValueSymbolLinks::default()
                    })
            {
                return StoredDeclaredCallSetValidation::Malformed;
            }
            edges.push(*type_);
        }
        edges.push(return_type);
    }
    StoredDeclaredCallSetValidation::Valid(edges)
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum DetailedDeclaredPropertyObjectValidation {
    Valid(DeclaredPropertyObjectProof),
    TraversableBoundary(DeclaredPropertyObjectProof),
    NotDeclared,
    Malformed,
}

pub(super) enum DeclaredPropertyTypeGraphValidation {
    Traversable(Vec<TypeId>),
    Opaque,
    Malformed,
}

impl PropertyObjectState {
    pub(super) const fn type_id(self) -> TypeId {
        match self {
            Self::EmptyBootstrap(type_) | Self::Shell(type_) | Self::Resolved(type_) => type_,
        }
    }

    pub(super) const fn is_resolved(self) -> bool {
        matches!(self, Self::EmptyBootstrap(_) | Self::Resolved(_))
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum PropertyObjectError {
    InvalidTypeLiteral(NodeRef),
    InvalidInterface {
        declaration: NodeRef,
        symbol: SemanticSymbolId,
    },
    InvalidInterfaceSymbol(SemanticSymbolId),
    InvalidObjectLiteral(NodeRef),
    UnsupportedMember {
        node: NodeRef,
        kind: SyntaxKind,
    },
    InvalidCachedTypeLiteral {
        node: NodeRef,
        type_: TypeId,
    },
    InvalidCachedInterface {
        symbol: SemanticSymbolId,
        type_: TypeId,
    },
    Capacity(NodeRef),
}

fn invalid_plan(plan: &PropertyObjectPlan) -> PropertyObjectError {
    match plan.kind {
        PropertyObjectKind::TypeLiteral => PropertyObjectError::InvalidTypeLiteral(plan.node),
        PropertyObjectKind::Interface => PropertyObjectError::InvalidInterface {
            declaration: plan.node,
            symbol: plan.symbol,
        },
        PropertyObjectKind::ObjectLiteral => PropertyObjectError::InvalidObjectLiteral(plan.node),
    }
}

fn invalid_cache(plan: &PropertyObjectPlan, type_: TypeId) -> PropertyObjectError {
    match plan.kind {
        PropertyObjectKind::TypeLiteral | PropertyObjectKind::ObjectLiteral => {
            PropertyObjectError::InvalidCachedTypeLiteral {
                node: plan.node,
                type_,
            }
        }
        PropertyObjectKind::Interface => PropertyObjectError::InvalidCachedInterface {
            symbol: plan.symbol,
            type_,
        },
    }
}

pub(super) fn plan_object_literal(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    node: NodeRef,
) -> Result<PropertyObjectPlan, PropertyObjectError> {
    let record = preflight_node(store, host, node)
        .map_err(|_| PropertyObjectError::InvalidObjectLiteral(node))?;
    let NodeData::ObjectLiteralExpression(object) = &record.data else {
        return Err(PropertyObjectError::InvalidObjectLiteral(node));
    };
    if record.kind != SyntaxKind::ObjectLiteralExpression
        || record.flags.0 & NODE_FLAG_JSDOC != 0
        || object.symbol.is_some()
        || object.facts != 0
        || object.properties.range != record.range
    {
        return Err(PropertyObjectError::InvalidObjectLiteral(node));
    }
    let symbol =
        bound_symbol(store, host, node).ok_or(PropertyObjectError::InvalidObjectLiteral(node))?;
    let symbol_record = store
        .symbol(symbol)
        .ok_or(PropertyObjectError::InvalidObjectLiteral(node))?;
    if symbol_record.flags() != SymbolFlags::OBJECT_LITERAL
        || symbol_record.check_flags() != CheckFlags::NONE
        || symbol_record.name() != InternalSymbolName::Object.as_ref()
        || symbol_record.declarations() != Some(&[node])
        || symbol_record.value_declaration() != Some(node)
        || symbol_record.parent().is_some()
        || symbol_record.exports().is_some()
        || symbol_record.export_symbol().is_some()
    {
        return Err(PropertyObjectError::InvalidObjectLiteral(node));
    }
    for member in &object.properties.nodes {
        let member = NodeRef::new(node.arena, node.file, *member);
        let member_record = preflight_node(store, host, member)
            .map_err(|_| PropertyObjectError::InvalidObjectLiteral(node))?;
        let NodeData::PropertyAssignment(property) = &member_record.data else {
            continue;
        };
        let name = NodeRef::new(member.arena, member.file, property.name);
        let name_record = preflight_node(store, host, name)
            .map_err(|_| PropertyObjectError::InvalidObjectLiteral(node))?;
        let NodeData::ComputedPropertyName(computed) = &name_record.data else {
            continue;
        };
        let expression = NodeRef::new(name.arena, name.file, computed.expression);
        let expression_record = preflight_node(store, host, expression)
            .map_err(|_| PropertyObjectError::InvalidObjectLiteral(node))?;
        if !matches!(
            (&expression_record.data, expression_record.kind),
            (NodeData::StringLiteral(_), SyntaxKind::StringLiteral)
                | (NodeData::NumericLiteral(_), SyntaxKind::NumericLiteral)
                | (
                    NodeData::NoSubstitutionTemplateLiteral(_),
                    SyntaxKind::NoSubstitutionTemplateLiteral
                )
        ) {
            return Err(PropertyObjectError::UnsupportedMember {
                node: name,
                kind: SyntaxKind::ComputedPropertyName,
            });
        }
    }
    plan_members(
        store,
        host,
        PropertyObjectKind::ObjectLiteral,
        node,
        symbol,
        symbol_record.members(),
        &object.properties,
        None,
        TypeLiteralMemberPolicy::General,
    )
}

pub(super) fn plan_type_literal(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    node: NodeRef,
    alias_symbol: Option<SemanticSymbolId>,
) -> Result<PropertyObjectPlan, PropertyObjectError> {
    plan_type_literal_with_policy(
        store,
        host,
        node,
        alias_symbol,
        TypeLiteralMemberPolicy::General,
    )
}

pub(super) fn plan_nongeneric_keyof_type_literal(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    node: NodeRef,
) -> Result<PropertyObjectPlan, PropertyObjectError> {
    plan_type_literal_with_policy(
        store,
        host,
        node,
        None,
        TypeLiteralMemberPolicy::ConcreteIndexedAccess,
    )
}

pub(super) fn plan_concrete_indexed_access_type_literal(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    node: NodeRef,
) -> Result<PropertyObjectPlan, PropertyObjectError> {
    plan_type_literal_with_policy(
        store,
        host,
        node,
        None,
        TypeLiteralMemberPolicy::ConcreteIndexedAccess,
    )
}

fn plan_type_literal_with_policy(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    node: NodeRef,
    alias_symbol: Option<SemanticSymbolId>,
    policy: TypeLiteralMemberPolicy,
) -> Result<PropertyObjectPlan, PropertyObjectError> {
    let record = preflight_node(store, host, node)
        .map_err(|_| PropertyObjectError::InvalidTypeLiteral(node))?;
    let NodeData::TypeLiteralNode(literal) = &record.data else {
        return Err(PropertyObjectError::InvalidTypeLiteral(node));
    };
    if record.kind != SyntaxKind::TypeLiteral
        || record.flags.0 & NODE_FLAG_JSDOC != 0
        || literal.members.range != record.range
    {
        return Err(PropertyObjectError::InvalidTypeLiteral(node));
    }
    let symbol =
        bound_symbol(store, host, node).ok_or(PropertyObjectError::InvalidTypeLiteral(node))?;
    let symbol_record = store
        .symbol(symbol)
        .ok_or(PropertyObjectError::InvalidTypeLiteral(node))?;
    if symbol_record.flags() != SymbolFlags::TYPE_LITERAL
        || symbol_record.check_flags() != CheckFlags::NONE
        || symbol_record.name() != InternalSymbolName::Type.as_ref()
        || symbol_record.declarations() != Some(&[node])
        || symbol_record.value_declaration().is_some()
        || symbol_record.parent().is_some()
        || symbol_record.exports().is_some()
        || symbol_record.export_symbol().is_some()
    {
        return Err(PropertyObjectError::InvalidTypeLiteral(node));
    }
    if let Some(alias) = alias_symbol {
        let Some(alias_record) = store.symbol(alias) else {
            return Err(PropertyObjectError::InvalidTypeLiteral(node));
        };
        if store.get_merged_symbol(alias) != Some(alias)
            || alias_record.flags() != SymbolFlags::TYPE_ALIAS
            || alias_record.check_flags() != CheckFlags::NONE
        {
            return Err(PropertyObjectError::InvalidTypeLiteral(node));
        }
    }
    plan_members(
        store,
        host,
        PropertyObjectKind::TypeLiteral,
        node,
        symbol,
        symbol_record.members(),
        &literal.members,
        alias_symbol,
        policy,
    )
}

pub(super) fn plan_interface(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    symbol: SemanticSymbolId,
) -> Result<PropertyObjectPlan, PropertyObjectError> {
    let symbol = store
        .get_merged_symbol(symbol)
        .ok_or(PropertyObjectError::InvalidInterfaceSymbol(symbol))?;
    let Some(symbol_record) = store.symbol(symbol) else {
        unreachable!("get_merged_symbol returned a store-owned symbol")
    };
    let Some(declarations) = symbol_record
        .declarations()
        .filter(|declarations| !declarations.is_empty())
    else {
        return Err(PropertyObjectError::InvalidInterfaceSymbol(symbol));
    };
    // `resolveDeclaredMembers` reads the merged symbol's member table
    // independently of its value side. A function-scoped value declaration
    // such as the standard library's `declare var Object` is therefore inert
    // for this property-only interface plan.
    let mut declaration = None;
    let mut value_declarations = Vec::new();
    let mut seen_declarations = HashSet::new();
    for candidate in declarations {
        if !seen_declarations.insert(*candidate) {
            return Err(PropertyObjectError::InvalidInterface {
                declaration: *candidate,
                symbol,
            });
        }
        let record = preflight_node(store, host, *candidate).map_err(|_| {
            PropertyObjectError::InvalidInterface {
                declaration: *candidate,
                symbol,
            }
        })?;
        if !host.symbol_matches(store, *candidate, symbol) {
            return Err(PropertyObjectError::InvalidInterface {
                declaration: *candidate,
                symbol,
            });
        }
        match (record.kind, &record.data) {
            (SyntaxKind::InterfaceDeclaration, NodeData::InterfaceDeclaration(_))
                if declaration.is_none() =>
            {
                declaration = Some(*candidate);
            }
            (SyntaxKind::InterfaceDeclaration, NodeData::InterfaceDeclaration(_)) => {
                return Err(PropertyObjectError::UnsupportedMember {
                    node: *candidate,
                    kind: SyntaxKind::InterfaceDeclaration,
                });
            }
            (SyntaxKind::VariableDeclaration, NodeData::VariableDeclaration(_)) => {
                value_declarations.push(*candidate);
            }
            _ => {
                return Err(PropertyObjectError::InvalidInterface {
                    declaration: *candidate,
                    symbol,
                });
            }
        }
    }
    let Some(declaration) = declaration else {
        return Err(PropertyObjectError::InvalidInterfaceSymbol(symbol));
    };
    let record = preflight_node(store, host, declaration).map_err(|_| {
        PropertyObjectError::InvalidInterface {
            declaration,
            symbol,
        }
    })?;
    let NodeData::InterfaceDeclaration(interface) = &record.data else {
        return Err(PropertyObjectError::InvalidInterface {
            declaration,
            symbol,
        });
    };
    let name = NodeRef::new(declaration.arena, declaration.file, interface.name);
    let name_record =
        preflight_node(store, host, name).map_err(|_| PropertyObjectError::InvalidInterface {
            declaration,
            symbol,
        })?;
    let NodeData::Identifier(identifier) = &name_record.data else {
        return Err(PropertyObjectError::InvalidInterface {
            declaration,
            symbol,
        });
    };
    let expected_parent = declared_type_declaration_parent(
        store,
        host,
        declaration,
        symbol,
        name,
        interface.modifiers.as_ref(),
    )
    .map_err(|()| PropertyObjectError::InvalidInterface {
        declaration,
        symbol,
    })?;
    let expected_symbol_flags = SymbolFlags::INTERFACE
        | if value_declarations.is_empty() {
            SymbolFlags::NONE
        } else {
            SymbolFlags::FUNCTION_SCOPED_VARIABLE
        };
    let valid_value_declaration = match symbol_record.value_declaration() {
        None => value_declarations.is_empty(),
        Some(value) => value_declarations.contains(&value),
    };
    if record.kind != SyntaxKind::InterfaceDeclaration
        || record.flags.0 != 0
        || !host.symbol_matches(store, declaration, symbol)
        || symbol_record.flags() != expected_symbol_flags
        || symbol_record.check_flags() != CheckFlags::NONE
        || symbol_record.name().as_utf8() != Some(identifier.text.as_str())
        || !valid_value_declaration
        || symbol_record.parent().is_some() != expected_parent.is_some()
        || store.get_parent_of_symbol(symbol) != expected_parent
        || symbol_record.exports().is_some()
        || symbol_record.export_symbol().is_some()
        || name_record.kind != SyntaxKind::Identifier
        || name_record.parent != Some(declaration.node)
        || interface.flow_node.is_some()
        || interface.local_symbol.is_some()
        || interface.symbol.is_some()
        || interface.type_parameters.is_some()
        || interface.members.has_trailing_comma
        || interface.members.range.start < record.range.start
        || interface.members.range.end != record.range.end
    {
        return Err(PropertyObjectError::InvalidInterface {
            declaration,
            symbol,
        });
    }
    let heritage = interface
        .heritage_clauses
        .as_ref()
        .map(|clauses| {
            plan_direct_interface_heritage(store, host, declaration, symbol, clauses).map_err(
                |error| match error {
                    DirectInterfaceHeritageError::Invalid => {
                        PropertyObjectError::InvalidInterface {
                            declaration,
                            symbol,
                        }
                    }
                    DirectInterfaceHeritageError::Unsupported { node, kind } => {
                        PropertyObjectError::UnsupportedMember { node, kind }
                    }
                },
            )
        })
        .transpose()?;
    let mut plan = plan_members(
        store,
        host,
        PropertyObjectKind::Interface,
        declaration,
        symbol,
        symbol_record.members(),
        &interface.members,
        None,
        TypeLiteralMemberPolicy::General,
    )?;
    plan.heritage = heritage;
    if let Some(heritage) = plan.heritage.as_ref() {
        if let Some(index) = plan.indexes.first() {
            return Err(PropertyObjectError::UnsupportedMember {
                node: index.declaration,
                kind: SyntaxKind::IndexSignature,
            });
        }
        let [base] = heritage.bases.as_slice() else {
            return Err(PropertyObjectError::UnsupportedMember {
                node: heritage.clause,
                kind: SyntaxKind::HeritageClause,
            });
        };
        let base_plan = plan_interface(store, host, base.symbol)?;
        if let Some(index) = base_plan.indexes.first() {
            return Err(PropertyObjectError::UnsupportedMember {
                node: index.declaration,
                kind: SyntaxKind::IndexSignature,
            });
        }
        if base_plan.heritage.is_some() {
            return Err(PropertyObjectError::UnsupportedMember {
                node: base.node,
                kind: SyntaxKind::ExpressionWithTypeArguments,
            });
        }
        if let Some(call) = base_plan.call_signatures.first() {
            return Err(PropertyObjectError::UnsupportedMember {
                node: call.declaration,
                kind: SyntaxKind::CallSignature,
            });
        }
        if let Some(call) = plan.call_signatures.first() {
            return Err(PropertyObjectError::UnsupportedMember {
                node: call.declaration,
                kind: SyntaxKind::CallSignature,
            });
        }
        if !value_declarations.is_empty() {
            return Err(PropertyObjectError::UnsupportedMember {
                node: heritage.clause,
                kind: SyntaxKind::HeritageClause,
            });
        }
        for property in &plan.properties {
            let Some(base_property) = base_plan
                .properties
                .iter()
                .find(|base| base.name == property.name)
            else {
                continue;
            };
            let own_kind = store.source_node_kind(property.type_node);
            let base_kind = store.source_node_kind(base_property.type_node);
            let same_primitive = own_kind == base_kind
                && matches!(
                    own_kind,
                    Some(
                        SyntaxKind::AnyKeyword
                            | SyntaxKind::UnknownKeyword
                            | SyntaxKind::StringKeyword
                            | SyntaxKind::NumberKeyword
                            | SyntaxKind::BooleanKeyword
                            | SyntaxKind::BigIntKeyword
                            | SyntaxKind::SymbolKeyword
                            | SyntaxKind::VoidKeyword
                            | SyntaxKind::NeverKeyword
                    )
                );
            let compatible = same_primitive
                || own_kind == Some(SyntaxKind::AnyKeyword)
                    && base_kind != Some(SyntaxKind::NeverKeyword);
            if !compatible || property.optional && !base_property.optional {
                return Err(PropertyObjectError::UnsupportedMember {
                    node: property.declaration,
                    kind: store
                        .source_node_kind(property.declaration)
                        .unwrap_or(SyntaxKind::PropertySignature),
                });
            }
        }
    }
    if !value_declarations.is_empty() && !plan.call_signatures.is_empty() {
        return Err(PropertyObjectError::InvalidInterface {
            declaration,
            symbol,
        });
    }
    Ok(plan)
}

/// Plans the property declarations of one direct, local generic interface.
///
/// The bound member table also contains the interface's type parameters. The
/// publication step creates a separate declared-property table instead of
/// replacing that binder-owned table.
pub(super) fn plan_generic_interface(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    symbol: SemanticSymbolId,
) -> Result<PropertyObjectPlan, PropertyObjectError> {
    let symbol = store
        .get_merged_symbol(symbol)
        .ok_or(PropertyObjectError::InvalidInterfaceSymbol(symbol))?;
    let symbol_record = store
        .symbol(symbol)
        .ok_or(PropertyObjectError::InvalidInterfaceSymbol(symbol))?;
    let [declaration] = symbol_record.declarations().unwrap_or_default() else {
        return Err(PropertyObjectError::InvalidInterfaceSymbol(symbol));
    };
    let declaration = *declaration;
    let invalid = || PropertyObjectError::InvalidInterface {
        declaration,
        symbol,
    };
    let record = preflight_node(store, host, declaration).map_err(|_| invalid())?;
    let NodeData::InterfaceDeclaration(interface) = &record.data else {
        return Err(invalid());
    };
    let Some(parameters) = interface.type_parameters.as_ref() else {
        return Err(invalid());
    };
    let raw_members = symbol_record.members().ok_or_else(invalid)?;
    let raw_table = store.symbol_table(raw_members).ok_or_else(invalid)?;
    let name = NodeRef::new(declaration.arena, declaration.file, interface.name);
    let name_record = preflight_node(store, host, name).map_err(|_| invalid())?;
    let NodeData::Identifier(identifier) = &name_record.data else {
        return Err(invalid());
    };
    if record.kind != SyntaxKind::InterfaceDeclaration
        || record.flags.0 != 0
        || parameters.nodes.is_empty()
        || !host.symbol_matches(store, declaration, symbol)
        || symbol_record.flags() != SymbolFlags::INTERFACE
        || symbol_record.check_flags() != CheckFlags::NONE
        || symbol_record.name().as_utf8() != Some(identifier.text.as_str())
        || symbol_record.value_declaration().is_some()
        || symbol_record.parent().is_some()
        || symbol_record.exports().is_some()
        || symbol_record.export_symbol().is_some()
        || name_record.kind != SyntaxKind::Identifier
        || name_record.parent != Some(declaration.node)
        || interface.modifiers.is_some()
        || interface.flow_node.is_some()
        || interface.local_symbol.is_some()
        || interface.symbol.is_some()
        || interface.heritage_clauses.is_some()
        || interface.members.has_trailing_comma
        || interface.members.range.start < record.range.start
        || interface.members.range.end != record.range.end
    {
        return Err(invalid());
    }

    let mut parameter_symbols = HashSet::with_capacity(parameters.nodes.len());
    for parameter in &parameters.nodes {
        let parameter = NodeRef::new(declaration.arena, declaration.file, *parameter);
        let parameter_record = preflight_node(store, host, parameter).map_err(|_| invalid())?;
        if parameter_record.kind != SyntaxKind::TypeParameter
            || parameter_record.parent != Some(declaration.node)
        {
            return Err(invalid());
        }
        let parameter_symbol = bound_symbol(store, host, parameter).ok_or_else(invalid)?;
        let parameter_symbol_record = store.symbol(parameter_symbol).ok_or_else(invalid)?;
        if parameter_symbol_record.flags() != SymbolFlags::TYPE_PARAMETER
            || parameter_symbol_record.parent() != Some(symbol)
            || raw_table.get(parameter_symbol_record.name()) != Some(parameter_symbol)
            || !parameter_symbols.insert(parameter_symbol)
        {
            return Err(invalid());
        }
    }

    let plan = plan_members(
        store,
        host,
        PropertyObjectKind::Interface,
        declaration,
        symbol,
        Some(raw_members),
        &interface.members,
        None,
        TypeLiteralMemberPolicy::GenericInterface,
    )?;
    if let Some(index) = plan.indexes.first() {
        return Err(PropertyObjectError::UnsupportedMember {
            node: index.declaration,
            kind: SyntaxKind::IndexSignature,
        });
    }
    if let Some(call) = plan.call_signatures.first() {
        return Err(PropertyObjectError::UnsupportedMember {
            node: call.declaration,
            kind: SyntaxKind::CallSignature,
        });
    }
    if raw_table.len() != parameter_symbols.len() + plan.properties.len() {
        return Err(invalid());
    }
    Ok(plan)
}

/// Proves a named declared type's local, namespace-exported, or top-level ESM
/// owner. Exported forms validate their containing declaration, binder local
/// placeholder when present, and canonical export-table edge.
pub(super) fn declared_type_declaration_parent(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    declaration: NodeRef,
    symbol: SemanticSymbolId,
    name: NodeRef,
    modifiers: Option<&ts_ast::ModifierList>,
) -> Result<Option<SemanticSymbolId>, ()> {
    let invalid = || ();
    let (_, bound) = host.source(declaration).ok_or_else(invalid)?;
    let declaration_record = preflight_node(store, host, declaration).map_err(|_| invalid())?;
    let name_record = preflight_node(store, host, name).map_err(|_| invalid())?;
    let NodeData::Identifier(identifier) = &name_record.data else {
        return Err(());
    };
    let Some(parent_id) = declaration_record.parent else {
        return Err(());
    };
    let parent = NodeRef::new(declaration.arena, declaration.file, parent_id);
    let parent_record = preflight_node(store, host, parent).map_err(|_| invalid())?;
    if parent_record.kind == SyntaxKind::ModuleBlock {
        return declared_namespace_type_parent(
            store,
            host,
            declaration,
            symbol,
            identifier.text.as_str(),
            parent,
            modifiers,
        );
    }
    let Some(modifiers) = modifiers else {
        return Ok(None);
    };
    let source = bound.source_file();
    let source_record = preflight_node(store, host, source).map_err(|_| invalid())?;
    let NodeData::SourceFile(source_data) = &source_record.data else {
        return Err(());
    };
    if declaration_record.parent != Some(source.node)
        || source_data
            .statements
            .nodes
            .iter()
            .filter(|node| **node == declaration.node)
            .count()
            != 1
        || bound
            .symbol(declaration)
            .and_then(|symbol| store.get_merged_symbol(symbol))
            != Some(symbol)
    {
        return Err(());
    }
    if !is_exact_export_modifier(
        store,
        host,
        declaration,
        declaration_record,
        name_record,
        modifiers,
    ) {
        return Err(());
    }
    let facts = bound.source_facts().ok_or_else(invalid)?;
    if facts.is_javascript_file() || !facts.is_external_module() || facts.is_common_js_module() {
        return Err(());
    }
    let source_symbol = bound.symbol(source).ok_or_else(invalid)?;
    let source_symbol_record = store.symbol(source_symbol).ok_or_else(invalid)?;
    let exported_symbol_record = store.symbol(symbol).ok_or_else(invalid)?;
    let local = bound.local_symbol(declaration).ok_or_else(invalid)?;
    let local_record = store.symbol(local).ok_or_else(invalid)?;
    if store.get_merged_symbol(source_symbol) != Some(source_symbol)
        || source_symbol_record.flags() != SymbolFlags::VALUE_MODULE
        || source_symbol_record.check_flags() != CheckFlags::NONE
        || source_symbol_record.name() != facts.source_file_symbol_name()
        || source_symbol_record.declarations() != Some(&[source])
        || source_symbol_record.value_declaration() != Some(source)
        || source_symbol_record.members().is_some()
        || source_symbol_record.exports().is_none()
        || source_symbol_record.parent().is_some()
        || source_symbol_record.export_symbol().is_some()
        || exported_symbol_record.name().as_utf8() != Some(identifier.text.as_str())
        || local == symbol
        || store.get_merged_symbol(local) != Some(local)
        || local_record.flags() != SymbolFlags::NONE
        || local_record.check_flags() != CheckFlags::NONE
        || local_record.name().as_utf8() != Some(identifier.text.as_str())
        || local_record.declarations() != Some(&[declaration])
        || local_record.value_declaration().is_some()
        || local_record.members().is_some()
        || local_record.exports().is_some()
        || local_record.parent().is_some()
        || local_record.export_symbol() != Some(symbol)
        || source_symbol_record
            .exports()
            .and_then(|exports| store.symbol_table(exports))
            .and_then(|exports| exports.get_source(&identifier.text))
            != Some(symbol)
    {
        return Err(());
    }
    Ok(Some(source_symbol))
}

fn declared_namespace_type_parent(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    declaration: NodeRef,
    symbol: SemanticSymbolId,
    name: &str,
    block: NodeRef,
    modifiers: Option<&ts_ast::ModifierList>,
) -> Result<Option<SemanticSymbolId>, ()> {
    let invalid = || ();
    let (_, bound) = host.source(declaration).ok_or_else(invalid)?;
    let block_record = preflight_node(store, host, block).map_err(|_| invalid())?;
    let NodeData::ModuleBlock(block_data) = &block_record.data else {
        return Err(());
    };
    let module = block_record
        .parent
        .map(|node| NodeRef::new(block.arena, block.file, node))
        .ok_or_else(invalid)?;
    let module_record = preflight_node(store, host, module).map_err(|_| invalid())?;
    let NodeData::ModuleDeclaration(module_data) = &module_record.data else {
        return Err(());
    };
    if block_record.kind != SyntaxKind::ModuleBlock
        || module_record.kind != SyntaxKind::ModuleDeclaration
        || module_data.body != Some(block.node)
        || block_data
            .statements
            .nodes
            .iter()
            .filter(|node| **node == declaration.node)
            .count()
            != 1
        || bound
            .symbol(declaration)
            .and_then(|candidate| store.get_merged_symbol(candidate))
            != Some(symbol)
    {
        return Err(());
    }

    let owner = store.symbol(symbol).ok_or_else(invalid)?;
    if owner.parent().is_none() && modifiers.is_none() {
        return Ok(None);
    }
    let namespace = bound
        .symbol(module)
        .and_then(|namespace| store.get_merged_symbol(namespace))
        .ok_or_else(invalid)?;
    let namespace_record = store.symbol(namespace).ok_or_else(invalid)?;
    if !namespace_record.flags().intersects(SymbolFlags::MODULE)
        || store.get_parent_of_symbol(symbol) != Some(namespace)
        || namespace_record
            .exports()
            .and_then(|exports| store.symbol_table(exports))
            .and_then(|exports| exports.get_source(name))
            .and_then(|export| store.get_merged_symbol(export))
            != Some(symbol)
    {
        return Err(());
    }
    if let Some(modifiers) = modifiers {
        let declaration_record = preflight_node(store, host, declaration).map_err(|_| invalid())?;
        let name = match &declaration_record.data {
            NodeData::InterfaceDeclaration(interface) => interface.name,
            NodeData::TypeAliasDeclaration(alias) => alias.name,
            NodeData::ClassDeclaration(class) => class.name.ok_or_else(invalid)?,
            _ => return Err(()),
        };
        let name = NodeRef::new(declaration.arena, declaration.file, name);
        let name_record = preflight_node(store, host, name).map_err(|_| invalid())?;
        if !is_exact_export_modifier(
            store,
            host,
            declaration,
            declaration_record,
            name_record,
            modifiers,
        ) {
            return Err(());
        }
    }
    if let Some(local) = bound.local_symbol(declaration) {
        let record = store.symbol(local).ok_or_else(invalid)?;
        if local == symbol
            || store.get_merged_symbol(local) != Some(local)
            || record.flags() != SymbolFlags::NONE
            || record.check_flags() != CheckFlags::NONE
            || record.name().as_utf8() != Some(name)
            || record.declarations() != Some(&[declaration])
            || record.value_declaration().is_some()
            || record.members().is_some()
            || record.exports().is_some()
            || record.parent().is_some()
            || record.export_symbol() != Some(symbol)
        {
            return Err(());
        }
    }
    Ok(Some(namespace))
}

fn is_exact_export_modifier(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    declaration: NodeRef,
    declaration_record: &ts_ast::Node,
    name_record: &ts_ast::Node,
    modifiers: &ts_ast::ModifierList,
) -> bool {
    let [modifier] = modifiers.list.nodes.as_slice() else {
        return false;
    };
    let modifier = NodeRef::new(declaration.arena, declaration.file, *modifier);
    let Ok(modifier_record) = preflight_node(store, host, modifier) else {
        return false;
    };
    modifiers.flags.0 == 0
        && !modifiers.list.has_trailing_comma
        && modifiers.list.range.start == declaration_record.range.start
        && modifiers.list.range.end <= name_record.range.start
        && modifier_record.kind == SyntaxKind::ExportKeyword
        && matches!(modifier_record.data, NodeData::Token(_))
        && modifier_record.flags.0 == 0
        && modifier_record.parent == Some(declaration.node)
        && modifier_record.range.start == declaration_record.range.start
        && modifier_record.range.end <= modifiers.list.range.end
        && host.source(modifier).is_some_and(|(arena, _)| {
            arena.source_text().is_none_or(|source| {
                source.get(
                    modifier_record.range.start.get() as usize
                        ..modifier_record.range.end.get() as usize,
                ) == Some("export")
            })
        })
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

#[allow(clippy::too_many_arguments)]
fn plan_members(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    kind: PropertyObjectKind,
    node: NodeRef,
    symbol: SemanticSymbolId,
    members: Option<SymbolTableId>,
    member_nodes: &NodeList,
    alias_symbol: Option<SemanticSymbolId>,
    policy: TypeLiteralMemberPolicy,
) -> Result<PropertyObjectPlan, PropertyObjectError> {
    let provisional = PropertyObjectPlan {
        kind,
        node,
        symbol,
        members,
        properties: Vec::new(),
        indexes: Vec::new(),
        call_signatures: Vec::new(),
        alias_symbol,
        heritage: None,
    };
    if kind != PropertyObjectKind::ObjectLiteral && member_nodes.has_trailing_comma
        || policy != TypeLiteralMemberPolicy::GenericInterface
            && members.is_some() == member_nodes.nodes.is_empty()
        || policy == TypeLiteralMemberPolicy::GenericInterface && members.is_none()
    {
        return Err(invalid_plan(&provisional));
    }
    let table = members.and_then(|members| store.symbol_table(members));
    if members.is_some() != table.is_some() {
        return Err(invalid_plan(&provisional));
    }

    let owner_record = preflight_node(store, host, node).map_err(|_| invalid_plan(&provisional))?;
    let mut previous_end = member_nodes.range.start;
    let mut seen_nodes = HashSet::new();
    let mut seen_symbols = HashSet::new();
    let mut seen_names = HashSet::new();
    let mut properties = Vec::with_capacity(member_nodes.nodes.len());
    let mut indexes = Vec::with_capacity(1);
    let mut call_signatures = Vec::with_capacity(member_nodes.nodes.len());
    for member in &member_nodes.nodes {
        let member = NodeRef::new(node.arena, node.file, *member);
        let member_record =
            preflight_node(store, host, member).map_err(|_| invalid_plan(&provisional))?;
        let admitted_kind = match kind {
            PropertyObjectKind::ObjectLiteral => matches!(
                member_record.kind,
                SyntaxKind::PropertyAssignment | SyntaxKind::ShorthandPropertyAssignment
            ),
            PropertyObjectKind::TypeLiteral => matches!(
                member_record.kind,
                SyntaxKind::PropertyDeclaration
                    | SyntaxKind::PropertySignature
                    | SyntaxKind::IndexSignature
                    | SyntaxKind::CallSignature
            ),
            PropertyObjectKind::Interface => matches!(
                member_record.kind,
                SyntaxKind::PropertyDeclaration
                    | SyntaxKind::PropertySignature
                    | SyntaxKind::IndexSignature
                    | SyntaxKind::CallSignature
            ),
        };
        if !admitted_kind {
            return Err(PropertyObjectError::UnsupportedMember {
                node: member,
                kind: member_record.kind,
            });
        }
        if member_record.parent != Some(node.node)
            || member_record.flags.0 & NODE_FLAG_JSDOC != 0
            || member_record.range.start < previous_end
            || member_record.range.start < member_nodes.range.start
            || member_record.range.end > member_nodes.range.end
            || member_record.range.start < owner_record.range.start
            || member_record.range.end > owner_record.range.end
            || !seen_nodes.insert(member)
        {
            return Err(invalid_plan(&provisional));
        }
        previous_end = member_record.range.end;

        if member_record.kind == SyntaxKind::CallSignature {
            call_signatures.push(plan_call_signature(store, host, node, symbol, member)?);
            continue;
        }

        if member_record.kind == SyntaxKind::IndexSignature {
            let index = plan_index_signature(store, host, node, symbol, member)?;
            if policy == TypeLiteralMemberPolicy::General && !indexes.is_empty() {
                return Err(PropertyObjectError::UnsupportedMember {
                    node: member,
                    kind: SyntaxKind::IndexSignature,
                });
            }
            indexes.push(index);
            continue;
        }

        let (name_id, value_id, postfix_token, modifiers, signature_initializer, valid_payload) =
            match &member_record.data {
                NodeData::PropertyDeclaration(property)
                    if kind != PropertyObjectKind::ObjectLiteral =>
                {
                    (
                        property.name,
                        property.type_,
                        property.postfix_token,
                        property.modifiers.as_ref(),
                        None,
                        property.initializer.is_none()
                            && property.type_.is_some()
                            && property.symbol.is_none()
                            && property.facts == 0,
                    )
                }
                NodeData::PropertySignatureDeclaration(property)
                    if kind != PropertyObjectKind::ObjectLiteral =>
                {
                    (
                        property.name,
                        Some(property.type_),
                        property.postfix_token,
                        property.modifiers.as_ref(),
                        Some(property.initializer),
                        property.symbol.is_none(),
                    )
                }
                NodeData::PropertyAssignment(property)
                    if kind == PropertyObjectKind::ObjectLiteral =>
                {
                    (
                        property.name,
                        Some(property.initializer),
                        property.postfix_token,
                        property.modifiers.as_ref(),
                        None,
                        property.type_.is_none()
                            && property.postfix_token.is_none()
                            && property.modifiers.is_none()
                            && property.symbol.is_none()
                            && property.facts == 0,
                    )
                }
                NodeData::ShorthandPropertyAssignment(property)
                    if kind == PropertyObjectKind::ObjectLiteral =>
                {
                    (
                        property.name,
                        Some(property.name),
                        property.postfix_token,
                        property.modifiers.as_ref(),
                        None,
                        property.equals_token.is_none()
                            && property.object_assignment_initializer.is_none()
                            && property.type_.is_none()
                            && property.postfix_token.is_none()
                            && property.modifiers.is_none()
                            && property.symbol.is_none()
                            && property.facts == 0,
                    )
                }
                _ => return Err(invalid_plan(&provisional)),
            };
        if !valid_payload {
            return Err(invalid_plan(&provisional));
        }
        if let Some(initializer) = signature_initializer
            && !missing_signature_initializer(store, host, member, initializer)
        {
            return Err(invalid_plan(&provisional));
        }
        let name = NodeRef::new(member.arena, member.file, name_id);
        let name_record =
            preflight_node(store, host, name).map_err(|_| invalid_plan(&provisional))?;
        let property_name = match &name_record.data {
            NodeData::Identifier(identifier) if name_record.kind == SyntaxKind::Identifier => {
                identifier.text.clone()
            }
            NodeData::ComputedPropertyName(computed)
                if kind == PropertyObjectKind::ObjectLiteral
                    && name_record.kind == SyntaxKind::ComputedPropertyName =>
            {
                let expression = NodeRef::new(name.arena, name.file, computed.expression);
                let expression_record = preflight_node(store, host, expression)
                    .map_err(|_| invalid_plan(&provisional))?;
                if computed.facts != 0
                    || expression_record.parent != Some(name.node)
                    || expression_record.range.start < name_record.range.start
                    || expression_record.range.end > name_record.range.end
                {
                    return Err(invalid_plan(&provisional));
                }
                match &expression_record.data {
                    NodeData::StringLiteral(literal)
                        if expression_record.kind == SyntaxKind::StringLiteral =>
                    {
                        literal.text.clone()
                    }
                    NodeData::NumericLiteral(literal)
                        if expression_record.kind == SyntaxKind::NumericLiteral =>
                    {
                        literal.text.clone()
                    }
                    NodeData::NoSubstitutionTemplateLiteral(literal)
                        if expression_record.kind == SyntaxKind::NoSubstitutionTemplateLiteral =>
                    {
                        literal.text.clone()
                    }
                    _ => {
                        return Err(PropertyObjectError::UnsupportedMember {
                            node: name,
                            kind: name_record.kind,
                        });
                    }
                }
            }
            _ => {
                return Err(PropertyObjectError::UnsupportedMember {
                    node: name,
                    kind: name_record.kind,
                });
            }
        };
        if name_record.parent != Some(member.node)
            || name_record.range.start < member_record.range.start
            || name_record.range.end > member_record.range.end
            || !seen_names.insert(property_name.clone())
        {
            return Err(invalid_plan(&provisional));
        }

        let type_node = NodeRef::new(member.arena, member.file, value_id.expect("checked above"));
        let type_record =
            preflight_node(store, host, type_node).map_err(|_| invalid_plan(&provisional))?;
        let valid_value_range = if member_record.kind == SyntaxKind::ShorthandPropertyAssignment {
            type_node == name && type_record.range == name_record.range
        } else {
            type_record.range.start >= name_record.range.end
        };
        if type_record.parent != Some(member.node)
            || !valid_value_range
            || type_record.range.end > member_record.range.end
        {
            return Err(invalid_plan(&provisional));
        }

        let optional = if let Some(token) = postfix_token {
            let token = NodeRef::new(member.arena, member.file, token);
            let token_record =
                preflight_node(store, host, token).map_err(|_| invalid_plan(&provisional))?;
            if token_record.kind != SyntaxKind::QuestionToken
                || token_record.parent != Some(member.node)
                || token_record.range.start < name_record.range.end
                || token_record.range.end > type_record.range.start
            {
                return Err(invalid_plan(&provisional));
            }
            true
        } else {
            false
        };
        let readonly = if kind == PropertyObjectKind::ObjectLiteral {
            false
        } else {
            preflight_readonly_modifier(store, host, member, modifiers)
                .ok_or_else(|| invalid_plan(&provisional))?
        };

        let property_symbol =
            bound_symbol(store, host, member).ok_or_else(|| invalid_plan(&provisional))?;
        let property_record = store
            .symbol(property_symbol)
            .ok_or_else(|| invalid_plan(&provisional))?;
        let expected_flags = SymbolFlags::PROPERTY
            | if optional {
                SymbolFlags::OPTIONAL
            } else {
                SymbolFlags::NONE
            };
        let expected_check_flags = source_property_check_flags(readonly);
        if property_record.flags() != expected_flags
            || (property_record.check_flags() != CheckFlags::NONE
                && property_record.check_flags() != expected_check_flags)
            || property_record.name().as_utf8() != Some(property_name.as_str())
            || property_record.declarations() != Some(&[member])
            || property_record.value_declaration() != Some(member)
            || property_record.members().is_some()
            || property_record.exports().is_some()
            || property_record.export_symbol().is_some()
            || property_record
                .parent()
                .and_then(|parent| store.get_merged_symbol(parent))
                != Some(symbol)
            || !seen_symbols.insert(property_symbol)
            || table.and_then(|table| table.get_source(&property_name)) != Some(property_symbol)
        {
            return Err(invalid_plan(&provisional));
        }
        properties.push(PlannedProperty {
            declaration: member,
            symbol: property_symbol,
            name_node: name,
            type_node,
            optional,
            readonly,
            name: property_name,
        });
    }

    let mut seen_index_kinds = HashSet::with_capacity(indexes.len());
    for index in &indexes {
        let Some(kind @ (SyntaxKind::StringKeyword | SyntaxKind::NumberKeyword)) =
            store.source_node_kind(index.key_type_node)
        else {
            return Err(invalid_plan(&provisional));
        };
        if !seen_index_kinds.insert(kind) {
            return Err(PropertyObjectError::UnsupportedMember {
                node: index.declaration,
                kind: SyntaxKind::IndexSignature,
            });
        }
    }

    let reserved_index_count = usize::from(!indexes.is_empty());
    let reserved_call_count = usize::from(!call_signatures.is_empty());
    if table.is_some_and(|table| {
        let parameter_count = if policy == TypeLiteralMemberPolicy::GenericInterface {
            table
                .iter()
                .filter(|(_, member)| {
                    store
                        .symbol(*member)
                        .is_some_and(|record| record.flags() == SymbolFlags::TYPE_PARAMETER)
                })
                .count()
        } else {
            0
        };
        table.len()
            != properties
                .len()
                .saturating_add(reserved_index_count)
                .saturating_add(reserved_call_count)
                .saturating_add(parameter_count)
            || match indexes.first() {
                Some(index) => table.get(InternalSymbolName::Index.as_ref()) != Some(index.symbol),
                None => table.get(InternalSymbolName::Index.as_ref()).is_some(),
            }
            || match call_signatures.first() {
                Some(signature) => {
                    table.get(InternalSymbolName::Call.as_ref()) != Some(signature.symbol)
                }
                None => table.get(InternalSymbolName::Call.as_ref()).is_some(),
            }
    }) {
        return Err(invalid_plan(&provisional));
    }
    if let Some(index) = indexes.first() {
        let declarations = indexes
            .iter()
            .map(|index| index.declaration)
            .collect::<Vec<_>>();
        let Some(record) = store.symbol(index.symbol) else {
            return Err(invalid_plan(&provisional));
        };
        if indexes
            .iter()
            .any(|candidate| candidate.symbol != index.symbol)
            || record.declarations() != Some(declarations.as_slice())
        {
            return Err(invalid_plan(&provisional));
        }
    }
    if policy == TypeLiteralMemberPolicy::General && !indexes.is_empty() && !properties.is_empty() {
        return Err(PropertyObjectError::UnsupportedMember {
            node: indexes[0].declaration,
            kind: SyntaxKind::IndexSignature,
        });
    }
    if !call_signatures.is_empty() && (!properties.is_empty() || !indexes.is_empty()) {
        return Err(PropertyObjectError::UnsupportedMember {
            node: call_signatures[0].declaration,
            kind: SyntaxKind::CallSignature,
        });
    }
    if let Some(call) = call_signatures.first() {
        let declarations = call_signatures
            .iter()
            .map(|signature| signature.declaration)
            .collect::<Vec<_>>();
        let Some(record) = store.symbol(call.symbol) else {
            return Err(invalid_plan(&provisional));
        };
        if call_signatures
            .iter()
            .any(|signature| signature.symbol != call.symbol)
            || record.declarations() != Some(declarations.as_slice())
        {
            return Err(invalid_plan(&provisional));
        }
    }

    Ok(PropertyObjectPlan {
        properties,
        indexes,
        call_signatures,
        ..provisional
    })
}

fn plan_call_signature(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    owner: NodeRef,
    owner_symbol: SemanticSymbolId,
    declaration: NodeRef,
) -> Result<PlannedCallSignature, PropertyObjectError> {
    let unsupported = || PropertyObjectError::UnsupportedMember {
        node: declaration,
        kind: SyntaxKind::CallSignature,
    };
    let record = preflight_node(store, host, declaration).map_err(|_| unsupported())?;
    let NodeData::CallSignatureDeclaration(call) = &record.data else {
        return Err(unsupported());
    };
    if record.kind != SyntaxKind::CallSignature
        || record.parent != Some(owner.node)
        || record.flags.0 != 0
        || call.full_signature.is_some()
        || call.next_container.is_some()
        || call.symbol.is_some()
        || call.type_parameters.is_some()
        || call.parameters.has_trailing_comma
        || call.parameters.range.start < record.range.start
        || call.parameters.range.end > record.range.end
    {
        return Err(unsupported());
    }
    let Some(return_id) = call.type_ else {
        return Err(unsupported());
    };
    let return_type = NodeRef::new(declaration.arena, declaration.file, return_id);
    let return_record = preflight_node(store, host, return_type).map_err(|_| unsupported())?;
    if return_record.parent != Some(declaration.node)
        || return_record.range.start < call.parameters.range.end
        || return_record.range.end > record.range.end
    {
        return Err(unsupported());
    }

    let bound = host.bound_file(declaration).ok_or_else(unsupported)?;
    let raw_call_symbol = bound.symbol(declaration).ok_or_else(unsupported)?;
    let call_symbol = store
        .get_merged_symbol(raw_call_symbol)
        .ok_or_else(unsupported)?;
    let call_record = store.symbol(call_symbol).ok_or_else(unsupported)?;
    if call_symbol != raw_call_symbol
        || call_record.flags() != SymbolFlags::SIGNATURE
        || call_record.check_flags() != CheckFlags::NONE
        || call_record.name() != InternalSymbolName::Call.as_ref()
        || call_record
            .declarations()
            .is_none_or(|declarations| !declarations.contains(&declaration))
        || call_record.value_declaration().is_some()
        || call_record.members().is_some()
        || call_record.exports().is_some()
        || call_record.parent() != Some(owner_symbol)
        || call_record.export_symbol().is_some()
    {
        return Err(unsupported());
    }

    let locals = bound
        .locals(declaration)
        .and_then(|locals| store.symbol_table(locals));
    if call.parameters.nodes.is_empty() {
        if locals.is_some_and(|locals| !locals.is_empty()) {
            return Err(unsupported());
        }
    } else if locals.is_none() {
        return Err(unsupported());
    }

    let mut parameters = Vec::with_capacity(call.parameters.nodes.len());
    let mut previous_end = call.parameters.range.start;
    let mut flags = SignatureFlags::NONE;
    for parameter_id in &call.parameters.nodes {
        let parameter = NodeRef::new(declaration.arena, declaration.file, *parameter_id);
        let parameter_record = preflight_node(store, host, parameter).map_err(|_| unsupported())?;
        let NodeData::ParameterDeclaration(data) = &parameter_record.data else {
            return Err(unsupported());
        };
        if parameter_record.kind != SyntaxKind::Parameter
            || parameter_record.parent != Some(declaration.node)
            || parameter_record.flags.0 != 0
            || parameter_record.range.start < previous_end
            || parameter_record.range.start < call.parameters.range.start
            || parameter_record.range.end > call.parameters.range.end
            || data.dot_dot_dot_token.is_some()
            || data.initializer.is_some()
            || data.question_token.is_some()
            || data.symbol.is_some()
            || data.facts != 0
            || data.modifiers.is_some()
        {
            return Err(unsupported());
        }
        previous_end = parameter_record.range.end;
        let name = NodeRef::new(parameter.arena, parameter.file, data.name);
        let name_record = preflight_node(store, host, name).map_err(|_| unsupported())?;
        let NodeData::Identifier(identifier) = &name_record.data else {
            return Err(unsupported());
        };
        if name_record.kind != SyntaxKind::Identifier
            || name_record.parent != Some(parameter.node)
            || name_record.range.start < parameter_record.range.start
            || name_record.range.end > parameter_record.range.end
            || identifier.text.is_empty()
            || identifier.text == "this"
        {
            return Err(unsupported());
        }
        let Some(type_id) = data.type_ else {
            return Err(unsupported());
        };
        let type_node = NodeRef::new(parameter.arena, parameter.file, type_id);
        let type_record = preflight_node(store, host, type_node).map_err(|_| unsupported())?;
        if type_record.parent != Some(parameter.node)
            || type_record.range.start < name_record.range.end
            || type_record.range.end > parameter_record.range.end
        {
            return Err(unsupported());
        }
        if type_record.kind == SyntaxKind::LiteralType {
            flags |= SignatureFlags::HAS_LITERAL_TYPES;
        }

        let raw_parameter_symbol = bound.symbol(parameter).ok_or_else(unsupported)?;
        let parameter_symbol = store
            .get_merged_symbol(raw_parameter_symbol)
            .ok_or_else(unsupported)?;
        let symbol_record = store.symbol(parameter_symbol).ok_or_else(unsupported)?;
        if parameter_symbol != raw_parameter_symbol
            || symbol_record.flags() != SymbolFlags::FUNCTION_SCOPED_VARIABLE
            || symbol_record.check_flags() != CheckFlags::NONE
            || symbol_record.name().as_utf8() != Some(identifier.text.as_str())
            || symbol_record.declarations() != Some(&[parameter])
            || symbol_record.value_declaration() != Some(parameter)
            || symbol_record.members().is_some()
            || symbol_record.exports().is_some()
            || symbol_record.parent().is_some()
            || symbol_record.export_symbol().is_some()
            || locals.and_then(|locals| locals.get_source(&identifier.text))
                != Some(parameter_symbol)
            || parameters
                .iter()
                .any(|planned: &PlannedCallParameter| planned.symbol == parameter_symbol)
        {
            return Err(unsupported());
        }
        let identity_node = peel_parenthesized_type(store, host, type_node)?;
        parameters.push(PlannedCallParameter {
            symbol: parameter_symbol,
            type_node,
            identity_node,
            null_literal_identity: is_null_literal_type(store, host, identity_node)?,
        });
    }
    if locals.is_some_and(|locals| locals.len() != parameters.len()) {
        return Err(unsupported());
    }
    if i32::try_from(parameters.len()).is_err() {
        return Err(unsupported());
    }
    let return_identity_node = peel_parenthesized_type(store, host, return_type)?;
    Ok(PlannedCallSignature {
        declaration,
        symbol: call_symbol,
        parameters,
        return_type,
        return_identity_node,
        return_null_literal_identity: is_null_literal_type(store, host, return_identity_node)?,
        flags,
    })
}

fn plan_index_signature(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    owner: NodeRef,
    owner_symbol: SemanticSymbolId,
    declaration: NodeRef,
) -> Result<PlannedIndexSignature, PropertyObjectError> {
    let unsupported = || PropertyObjectError::UnsupportedMember {
        node: declaration,
        kind: SyntaxKind::IndexSignature,
    };
    let record = preflight_node(store, host, declaration).map_err(|_| unsupported())?;
    let NodeData::IndexSignatureDeclaration(index) = &record.data else {
        return Err(unsupported());
    };
    if record.kind != SyntaxKind::IndexSignature
        || record.parent != Some(owner.node)
        || record.flags.0 != 0
        || index.full_signature.is_some()
        || index.next_container.is_some()
        || index.symbol.is_some()
        || index.type_parameters.is_some()
        || index.parameters.has_trailing_comma
        || index.parameters.nodes.len() != 1
        || index.parameters.range.start < record.range.start
        || index.parameters.range.end > record.range.end
    {
        return Err(unsupported());
    }
    let readonly = preflight_readonly_modifier(store, host, declaration, index.modifiers.as_ref())
        .ok_or_else(unsupported)?;

    let parameter = NodeRef::new(
        declaration.arena,
        declaration.file,
        index.parameters.nodes[0],
    );
    let parameter_record = preflight_node(store, host, parameter).map_err(|_| unsupported())?;
    let NodeData::ParameterDeclaration(parameter_data) = &parameter_record.data else {
        return Err(unsupported());
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
        return Err(unsupported());
    }
    let name = NodeRef::new(parameter.arena, parameter.file, parameter_data.name);
    let name_record = preflight_node(store, host, name).map_err(|_| unsupported())?;
    let NodeData::Identifier(identifier) = &name_record.data else {
        return Err(unsupported());
    };
    if name_record.kind != SyntaxKind::Identifier
        || name_record.parent != Some(parameter.node)
        || name_record.range.start < parameter_record.range.start
        || name_record.range.end > parameter_record.range.end
        || identifier.text.is_empty()
        || identifier.text == "this"
    {
        return Err(unsupported());
    }
    let Some(key_type_id) = parameter_data.type_ else {
        return Err(unsupported());
    };
    let key_type_node = NodeRef::new(parameter.arena, parameter.file, key_type_id);
    let key_record = preflight_node(store, host, key_type_node).map_err(|_| unsupported())?;
    if !matches!(
        key_record.kind,
        SyntaxKind::StringKeyword | SyntaxKind::NumberKeyword
    ) || key_record.parent != Some(parameter.node)
        || key_record.range.start < name_record.range.end
        || key_record.range.end > parameter_record.range.end
    {
        return Err(unsupported());
    }

    let value_type_node = NodeRef::new(declaration.arena, declaration.file, index.type_);
    let value_record = preflight_node(store, host, value_type_node).map_err(|_| unsupported())?;
    if value_record.parent != Some(declaration.node)
        || value_record.range.start < index.parameters.range.end
        || value_record.range.end > record.range.end
    {
        return Err(unsupported());
    }

    let Some(bound) = host.bound_file(declaration) else {
        return Err(unsupported());
    };
    let raw_index_symbol = bound.symbol(declaration).ok_or_else(unsupported)?;
    let index_symbol = store
        .get_merged_symbol(raw_index_symbol)
        .ok_or_else(unsupported)?;
    let index_record = store.symbol(index_symbol).ok_or_else(unsupported)?;
    if index_symbol != raw_index_symbol
        || index_record.flags() != SymbolFlags::SIGNATURE
        || index_record.check_flags() != CheckFlags::NONE
        || index_record.name() != InternalSymbolName::Index.as_ref()
        || index_record
            .declarations()
            .is_none_or(|declarations| !declarations.contains(&declaration))
        || index_record.value_declaration().is_some()
        || index_record.members().is_some()
        || index_record.exports().is_some()
        || index_record.parent() != Some(owner_symbol)
        || index_record.export_symbol().is_some()
    {
        return Err(unsupported());
    }

    let raw_parameter_symbol = bound.symbol(parameter).ok_or_else(unsupported)?;
    let parameter_symbol = store
        .get_merged_symbol(raw_parameter_symbol)
        .ok_or_else(unsupported)?;
    let parameter_symbol_record = store.symbol(parameter_symbol).ok_or_else(unsupported)?;
    let locals = bound.locals(declaration).ok_or_else(unsupported)?;
    let locals = store.symbol_table(locals).ok_or_else(unsupported)?;
    if parameter_symbol != raw_parameter_symbol
        || parameter_symbol_record.flags() != SymbolFlags::FUNCTION_SCOPED_VARIABLE
        || parameter_symbol_record.check_flags() != CheckFlags::NONE
        || parameter_symbol_record.name().as_utf8() != Some(identifier.text.as_str())
        || parameter_symbol_record.declarations() != Some(&[parameter])
        || parameter_symbol_record.value_declaration() != Some(parameter)
        || parameter_symbol_record.members().is_some()
        || parameter_symbol_record.exports().is_some()
        || parameter_symbol_record.parent().is_some()
        || parameter_symbol_record.export_symbol().is_some()
        || locals.len() != 1
        || locals.get_source(&identifier.text) != Some(parameter_symbol)
    {
        return Err(unsupported());
    }

    Ok(PlannedIndexSignature {
        declaration,
        symbol: index_symbol,
        key_type_node,
        value_type_node,
        readonly,
    })
}

fn missing_signature_initializer(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    member: NodeRef,
    initializer: ts_ast::NodeId,
) -> bool {
    let initializer = NodeRef::new(member.arena, member.file, initializer);
    let Ok(record) = preflight_node(store, host, initializer) else {
        return false;
    };
    matches!(
        &record.data,
        NodeData::Identifier(identifier)
            if record.kind == SyntaxKind::Identifier
                && record.flags.0 == NODE_FLAG_HAS_ERROR
                && record.parent == Some(member.node)
                && record.range.start == record.range.end
                && identifier.flow_node.is_none()
                && identifier.text.is_empty()
    )
}

fn preflight_readonly_modifier(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    member: NodeRef,
    modifiers: Option<&ts_ast::ModifierList>,
) -> Option<bool> {
    let Some(modifiers) = modifiers else {
        return Some(false);
    };
    if modifiers.flags.0 != 0
        || modifiers.list.nodes.len() != 1
        || modifiers.list.has_trailing_comma
    {
        return None;
    }
    let modifier = NodeRef::new(member.arena, member.file, modifiers.list.nodes[0]);
    let modifier_record = preflight_node(store, host, modifier).ok()?;
    let member_record = preflight_node(store, host, member).ok()?;
    (modifier_record.kind == SyntaxKind::ReadonlyKeyword
        && modifier_record.parent == Some(member.node)
        && modifiers.list.range.start == member_record.range.start
        && modifiers.list.range.end <= member_record.range.end
        && modifier_record.range.start >= modifiers.list.range.start
        && modifier_record.range.end <= modifiers.list.range.end)
        .then_some(true)
}

pub(super) fn type_literal_state(
    store: &CanonicalTypeMapperStore,
    plan: &PropertyObjectPlan,
) -> Result<Option<PropertyObjectState>, PropertyObjectError> {
    debug_assert_eq!(plan.kind, PropertyObjectKind::TypeLiteral);
    let Some(links) = store.type_node_links(plan.node) else {
        return Ok(None);
    };
    if links.outer_type_parameters.is_some() {
        let type_ = links.resolved_type.unwrap_or_else(|| {
            store
                .intrinsic_bootstrap()
                .expect("type queries require bootstrap")
                .error_type
        });
        return Err(invalid_cache(plan, type_));
    }
    let Some(type_) = links.resolved_type else {
        return Ok(None);
    };
    if plan.properties.is_empty()
        && plan.indexes.is_empty()
        && plan.call_signatures.is_empty()
        && plan.alias_symbol.is_none()
    {
        let expected = store
            .intrinsic_bootstrap()
            .ok_or(PropertyObjectError::InvalidCachedTypeLiteral {
                node: plan.node,
                type_,
            })?
            .empty_type_literal_type;
        return if type_ == expected {
            Ok(Some(PropertyObjectState::EmptyBootstrap(type_)))
        } else {
            Err(invalid_cache(plan, type_))
        };
    }
    validate_object_record(store, plan, type_)
        .map(Some)
        .ok_or_else(|| invalid_cache(plan, type_))
}

pub(super) fn object_literal_state(
    store: &CanonicalTypeMapperStore,
    plan: &PropertyObjectPlan,
) -> Result<Option<PropertyObjectState>, PropertyObjectError> {
    debug_assert_eq!(plan.kind, PropertyObjectKind::ObjectLiteral);
    let Some(links) = store.type_node_links(plan.node) else {
        if unresolved_property_links(store, plan) {
            return Ok(None);
        }
        let type_ = store
            .intrinsic_bootstrap()
            .ok_or(PropertyObjectError::InvalidObjectLiteral(plan.node))?
            .error_type;
        return Err(invalid_cache(plan, type_));
    };
    let type_ = links.resolved_type.unwrap_or_else(|| {
        store
            .intrinsic_bootstrap()
            .expect("source checking requires bootstrap")
            .error_type
    });
    if links.outer_type_parameters.is_some() || links.resolved_type.is_none() {
        return Err(invalid_cache(plan, type_));
    }
    match validate_object_record(store, plan, type_) {
        Some(state @ PropertyObjectState::Resolved(_)) => Ok(Some(state)),
        _ => Err(invalid_cache(plan, type_)),
    }
}

pub(super) fn ensure_type_literal_shell(
    store: &mut CanonicalTypeMapperStore,
    plan: &PropertyObjectPlan,
) -> Result<PropertyObjectState, PropertyObjectError> {
    if let Some(state) = type_literal_state(store, plan)? {
        return Ok(state);
    }
    if plan.properties.is_empty()
        && plan.indexes.is_empty()
        && plan.call_signatures.is_empty()
        && plan.alias_symbol.is_none()
    {
        let type_ = store
            .intrinsic_bootstrap()
            .ok_or(PropertyObjectError::InvalidTypeLiteral(plan.node))?
            .empty_type_literal_type;
        let mut links = store
            .type_node_links(plan.node)
            .cloned()
            .unwrap_or_default();
        links.resolved_type = Some(type_);
        assert!(store.set_type_node_links(plan.node, links));
        return Ok(PropertyObjectState::EmptyBootstrap(type_));
    }

    if !store.try_reserve_types(1)
        || plan.alias_symbol.is_some() && !store.try_reserve_type_aliases(1)
    {
        return Err(PropertyObjectError::Capacity(plan.node));
    }
    let type_ = store
        .alloc_plain_object_type(ObjectFlags::ANONYMOUS, Some(plan.symbol))
        .expect("the property-object plan validated its symbol");
    if let Some(alias_symbol) = plan.alias_symbol {
        let alias = store
            .alloc_type_alias(Some(alias_symbol))
            .expect("the property-object plan validated its alias symbol");
        assert!(store.set_type_alias(type_, Some(alias)));
    }
    let mut links = store
        .type_node_links(plan.node)
        .cloned()
        .unwrap_or_default();
    links.resolved_type = Some(type_);
    assert!(store.set_type_node_links(plan.node, links));
    Ok(PropertyObjectState::Shell(type_))
}

pub(super) fn interface_state(
    store: &CanonicalTypeMapperStore,
    plan: &PropertyObjectPlan,
    type_: TypeId,
) -> Result<PropertyObjectState, PropertyObjectError> {
    debug_assert_eq!(plan.kind, PropertyObjectKind::Interface);
    validate_interface_record(store, plan, type_).ok_or_else(|| invalid_cache(plan, type_))
}

/// Read-only proof for the declared-own half of a direct heritage result.
///
/// The final structured cache is owned by [`super::structured_members`]. This
/// proof deliberately validates only the interface shell, its declared table,
/// and the exact property-type links so inherited publication can remain one
/// atomic transaction.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum DirectInterfaceDeclaredState {
    Unresolved,
    Resolved,
}

pub(super) fn prepare_direct_interface_declared_properties(
    store: &CanonicalTypeMapperStore,
    plan: &PropertyObjectPlan,
    type_: TypeId,
    property_types: &[TypeId],
) -> Result<DirectInterfaceDeclaredState, PropertyObjectError> {
    if plan.kind != PropertyObjectKind::Interface
        || plan.heritage.is_none()
        || !plan.indexes.is_empty()
        || !plan.call_signatures.is_empty()
        || property_types.len() != plan.properties.len()
        || property_types
            .iter()
            .any(|type_| store.type_payload(*type_).is_none())
    {
        return Err(invalid_cache(plan, type_));
    }
    let Some(record) = store.type_payload(type_) else {
        return Err(invalid_cache(plan, type_));
    };
    let TypeData::Interface(interface) = record.data() else {
        return Err(invalid_cache(plan, type_));
    };
    if record.flags() != TypeFlags::OBJECT
        || record.symbol() != Some(plan.symbol)
        || record.alias().is_some()
        || store.get_merged_symbol(plan.symbol) != Some(plan.symbol)
        || store
            .declared_type_links(plan.symbol)
            .is_none_or(|links| links.declared_type != Some(type_))
        || !valid_thisless_interface_identity(interface)
    {
        return Err(invalid_cache(plan, type_));
    }
    if record.object_flags() == ObjectFlags::INTERFACE
        && !interface.base_types_resolved
        && store.direct_interface_heritage_provenance(type_).is_none()
        && valid_unresolved_interface_members(interface)
        && unresolved_property_links(store, plan)
    {
        return Ok(DirectInterfaceDeclaredState::Unresolved);
    }
    let exact_property_types =
        plan.properties
            .iter()
            .zip(property_types)
            .all(|(property, type_)| {
                store.symbol(property.symbol).is_some_and(|record| {
                    record.check_flags() == source_property_check_flags(property.readonly)
                }) && store.value_symbol_links(property.symbol)
                    == Some(&ValueSymbolLinks {
                        resolved_type: Some(*type_),
                        ..ValueSymbolLinks::default()
                    })
            });
    if record.object_flags() == ObjectFlags::INTERFACE | ObjectFlags::MEMBERS_RESOLVED
        && interface.declared_members_resolved
        && interface.declared_members == plan.members
        && interface.declared_call_signatures.is_none()
        && interface.declared_construct_signatures.is_none()
        && interface.declared_index_infos.is_none()
        && exact_property_types
    {
        return Ok(DirectInterfaceDeclaredState::Resolved);
    }
    Err(invalid_cache(plan, type_))
}

/// Publishes a previously validated declared-own property result.
///
/// Every identity and cache precondition was checked by
/// [`prepare_direct_interface_declared_properties`]; these setters can now
/// reject only a programming error in this module's caller.
pub(super) fn publish_prepared_direct_interface_declared_properties(
    store: &mut CanonicalTypeMapperStore,
    plan: &PropertyObjectPlan,
    type_: TypeId,
    property_types: &[TypeId],
    state: DirectInterfaceDeclaredState,
) {
    if state == DirectInterfaceDeclaredState::Resolved {
        return;
    }
    for (property, property_type) in plan.properties.iter().zip(property_types) {
        assert!(
            store.set_source_property_readonly(property.symbol, property.readonly),
            "the direct-interface plan validated a bound source property"
        );
        assert!(store.set_value_symbol_links(
            property.symbol,
            ValueSymbolLinks {
                resolved_type: Some(*property_type),
                ..ValueSymbolLinks::default()
            },
        ));
    }
    assert!(store.set_interface_declared_members(type_, true, plan.members, None, None, None));
}

fn validate_object_record(
    store: &CanonicalTypeMapperStore,
    plan: &PropertyObjectPlan,
    type_: TypeId,
) -> Option<PropertyObjectState> {
    let record = store.type_payload(type_)?;
    let TypeData::Object(object) = record.data() else {
        return None;
    };
    if record.flags() != TypeFlags::OBJECT
        || record.symbol() != Some(plan.symbol)
        || !valid_alias(store, record, plan.alias_symbol)
        || !valid_object_tail(object)
    {
        return None;
    }
    match plan.kind {
        PropertyObjectKind::TypeLiteral => {
            if record.object_flags() == ObjectFlags::ANONYMOUS
                && object.structured == StructuredTypeData::default()
                && unresolved_property_links(store, plan)
            {
                return Some(PropertyObjectState::Shell(type_));
            }
            if record.object_flags() == ObjectFlags::ANONYMOUS | ObjectFlags::MEMBERS_RESOLVED
                && valid_declared_structured_members(store, object, plan)
                && resolved_property_links(store, plan)
            {
                return Some(PropertyObjectState::Resolved(type_));
            }
        }
        PropertyObjectKind::ObjectLiteral => {
            let property_types = object_literal_property_types(store, object, plan)?;
            let expected_flags = expected_object_literal_flags(store, &property_types)?;
            if record.object_flags() == expected_flags | ObjectFlags::MEMBERS_RESOLVED {
                return Some(PropertyObjectState::Resolved(type_));
            }
        }
        PropertyObjectKind::Interface => return None,
    }
    None
}

fn expected_object_literal_flags(
    store: &CanonicalTypeMapperStore,
    property_types: &[TypeId],
) -> Option<ObjectFlags> {
    let mut flags = ObjectFlags::ANONYMOUS
        | ObjectFlags::OBJECT_LITERAL
        | ObjectFlags::FRESH_LITERAL
        | ObjectFlags::CONTAINS_OBJECT_OR_ARRAY_LITERAL;
    for property_type in property_types {
        flags |=
            store.type_payload(*property_type)?.object_flags() & ObjectFlags::PROPAGATING_FLAGS;
    }
    Some(flags)
}

fn validate_interface_record(
    store: &CanonicalTypeMapperStore,
    plan: &PropertyObjectPlan,
    type_: TypeId,
) -> Option<PropertyObjectState> {
    let record = store.type_payload(type_)?;
    let TypeData::Interface(interface) = record.data() else {
        return None;
    };
    if record.flags() != TypeFlags::OBJECT
        || record.symbol() != Some(plan.symbol)
        || record.alias().is_some()
        || !valid_thisless_interface_identity(interface)
    {
        return None;
    }
    if record.object_flags() == ObjectFlags::INTERFACE
        && valid_unresolved_interface_members(interface)
        && unresolved_property_links(store, plan)
    {
        return Some(PropertyObjectState::Shell(type_));
    }
    if record.object_flags() == ObjectFlags::INTERFACE | ObjectFlags::MEMBERS_RESOLVED
        && interface.base_types_resolved
        && interface.resolved_base_constructor_type.is_none()
        && interface.resolved_base_types.is_none()
        && interface.declared_members_resolved
        && interface.declared_members == plan.members
        && interface.declared_call_signatures.as_deref()
            == resolved_call_signature_ids(store, plan).as_deref()
        && interface.declared_construct_signatures.is_none()
        && interface.declared_index_infos.as_deref()
            == interface.reference.object.structured.index_infos.as_deref()
        && valid_declared_structured_members(store, &interface.reference.object, plan)
        && resolved_property_links(store, plan)
    {
        return Some(PropertyObjectState::Resolved(type_));
    }
    None
}

/// Proves that `type_` is a fully resolved, nongeneric interface or declared
/// type literal whose only members are ordered properties.
///
/// The proof is semantic-only so cache validators can use it without retaining
/// an AST host. Source provenance is still checked through registered node
/// facts and the exact owner/property symbol edges published by the binder.
pub(super) fn validate_resolved_declared_property_object(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
) -> DeclaredPropertyObjectValidation {
    match validate_resolved_declared_property_object_detailed(store, type_) {
        DetailedDeclaredPropertyObjectValidation::Valid(proof) => {
            DeclaredPropertyObjectValidation::Valid(proof)
        }
        DetailedDeclaredPropertyObjectValidation::TraversableBoundary(_)
        | DetailedDeclaredPropertyObjectValidation::NotDeclared => {
            DeclaredPropertyObjectValidation::NotDeclared
        }
        DetailedDeclaredPropertyObjectValidation::Malformed => {
            DeclaredPropertyObjectValidation::Malformed
        }
    }
}

fn validate_resolved_declared_property_object_detailed(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
) -> DetailedDeclaredPropertyObjectValidation {
    use DetailedDeclaredPropertyObjectValidation::{Malformed, NotDeclared, Valid};

    let Some(record) = store.type_payload(type_) else {
        return NotDeclared;
    };
    if record.flags() != TypeFlags::OBJECT {
        return if matches!(record.data(), TypeData::Interface(_) | TypeData::Object(_)) {
            Malformed
        } else {
            NotDeclared
        };
    }
    if store
        .intrinsic_bootstrap()
        .is_some_and(|bootstrap| type_ == bootstrap.empty_type_literal_type)
    {
        return if validate_empty_type_literal_identity(store, type_, record) {
            Valid(DeclaredPropertyObjectProof::TypeLiteral)
        } else {
            Malformed
        };
    }
    match record.data() {
        TypeData::Interface(interface) => {
            let Some(owner) = record.symbol() else {
                return Malformed;
            };
            let Some(owner_record) = store.symbol(owner) else {
                return Malformed;
            };
            if owner_record.flags() != SymbolFlags::INTERFACE {
                return NotDeclared;
            }
            if interface.all_type_parameters.is_some()
                || interface.outer_type_parameter_count != 0
                || interface.this_type.is_some()
                || interface.reference.object.target.is_some()
                || interface.reference.object.mapper.is_some()
                || interface.reference.object.instantiations != TypeCacheState::Unallocated
                || interface.reference.node.is_some()
                || interface.reference.resolved_type_arguments.is_some()
                || record.object_flags().intersects(ObjectFlags::REFERENCE)
            {
                return NotDeclared;
            }
            match classify_declared_owner_members(store, owner) {
                DeclaredOwnerMemberDomain::PropertyOnly => {}
                DeclaredOwnerMemberDomain::Unsupported => return NotDeclared,
                DeclaredOwnerMemberDomain::Malformed => return Malformed,
            }
            if interface.resolved_base_constructor_type.is_some()
                || interface.resolved_base_types.is_some()
                || interface.declared_call_signatures.is_some()
                || interface.declared_construct_signatures.is_some()
                || interface.declared_index_infos.is_some()
                || interface.reference.object.structured.signatures.is_some()
                || interface.reference.object.structured.call_signature_count != 0
                || interface.reference.object.structured.index_infos.is_some()
            {
                return NotDeclared;
            }
            validate_resolved_property_interface(store, type_, record, interface)
        }
        TypeData::Object(object) => {
            let Some(owner) = record.symbol() else {
                return NotDeclared;
            };
            let Some(owner_record) = store.symbol(owner) else {
                return Malformed;
            };
            if owner_record.flags() != SymbolFlags::TYPE_LITERAL {
                return NotDeclared;
            }
            match classify_declared_owner_members(store, owner) {
                DeclaredOwnerMemberDomain::PropertyOnly => {}
                DeclaredOwnerMemberDomain::Unsupported => return NotDeclared,
                DeclaredOwnerMemberDomain::Malformed => return Malformed,
            }
            if record
                .alias()
                .is_some_and(|alias| declared_property_alias_is_generic(store, alias))
                || store
                    .symbol(owner)
                    .and_then(|owner| owner.declarations())
                    .filter(|declarations| declarations.len() == 1)
                    .and_then(|declarations| store.type_node_links(declarations[0]))
                    .is_some_and(|links| links.outer_type_parameters.is_some())
            {
                return NotDeclared;
            }
            if object.structured.signatures.is_some()
                || object.structured.call_signature_count != 0
                || object.structured.index_infos.is_some()
            {
                return NotDeclared;
            }
            validate_resolved_property_type_literal(store, type_, record, object)
        }
        _ => NotDeclared,
    }
}

/// Validates the narrower property graph needed by cache-capability scans.
/// Legal nested/exported owner forms remain outside the admitted union domain,
/// but their exact member/value-link shell is safe to traverse for hidden
/// canonical-array references.
pub(super) fn validate_resolved_declared_property_type_graph(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
) -> DeclaredPropertyTypeGraphValidation {
    match validate_resolved_declared_property_object_detailed(store, type_) {
        DetailedDeclaredPropertyObjectValidation::Valid(_)
        | DetailedDeclaredPropertyObjectValidation::TraversableBoundary(_) => {
            resolved_declared_property_types(store, type_).map_or(
                DeclaredPropertyTypeGraphValidation::Malformed,
                DeclaredPropertyTypeGraphValidation::Traversable,
            )
        }
        DetailedDeclaredPropertyObjectValidation::NotDeclared => {
            DeclaredPropertyTypeGraphValidation::Opaque
        }
        DetailedDeclaredPropertyObjectValidation::Malformed => {
            DeclaredPropertyTypeGraphValidation::Malformed
        }
    }
}

/// Returns the store-owned property types behind an already validated
/// declared-property object. Callers use this after
/// [`validate_resolved_declared_property_object`] has proved the complete
/// owner/member/link shell, so recursive property identities can be walked
/// without retaining an AST host.
pub(super) fn resolved_declared_property_types(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
) -> Option<Vec<TypeId>> {
    let structured = match store.type_payload(type_)?.data() {
        TypeData::Interface(interface) => &interface.reference.object.structured,
        TypeData::Object(object) => &object.structured,
        _ => return None,
    };
    structured
        .properties
        .as_deref()
        .unwrap_or_default()
        .iter()
        .map(|property| store.value_symbol_links(*property)?.resolved_type)
        .collect()
}

fn validate_empty_type_literal_identity(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
    record: &TypeRecord,
) -> bool {
    let Some(bootstrap) = store.intrinsic_bootstrap() else {
        return false;
    };
    let TypeData::Object(object) = record.data() else {
        return false;
    };
    let Some(symbol) = store.symbol(bootstrap.empty_type_literal_symbol) else {
        return false;
    };
    type_ == bootstrap.empty_type_literal_type
        && record.object_flags() == ObjectFlags::ANONYMOUS | ObjectFlags::MEMBERS_RESOLVED
        && record.symbol() == Some(bootstrap.empty_type_literal_symbol)
        && record.alias().is_none()
        && valid_resolved_declared_structured_shell(object)
        && object.structured.members.is_none()
        && object.structured.properties.is_none()
        && store.get_merged_symbol(bootstrap.empty_type_literal_symbol)
            == Some(bootstrap.empty_type_literal_symbol)
        && symbol.flags() == SymbolFlags::TYPE_LITERAL | SymbolFlags::TRANSIENT
        && symbol.check_flags() == CheckFlags::NONE
        && symbol.name() == InternalSymbolName::Type.as_ref()
        && symbol.declarations().is_none()
        && symbol.value_declaration().is_none()
        && symbol.members().is_none()
        && symbol.exports().is_none()
        && symbol.parent().is_none()
        && symbol.export_symbol().is_none()
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum DeclaredOwnerMemberDomain {
    PropertyOnly,
    Unsupported,
    Malformed,
}

fn classify_declared_owner_members(
    store: &CanonicalTypeMapperStore,
    owner: SemanticSymbolId,
) -> DeclaredOwnerMemberDomain {
    let Some(owner) = store.symbol(owner) else {
        return DeclaredOwnerMemberDomain::Malformed;
    };
    let Some(members) = owner.members() else {
        return DeclaredOwnerMemberDomain::PropertyOnly;
    };
    let Some(table) = store.symbol_table(members) else {
        return DeclaredOwnerMemberDomain::Malformed;
    };
    let allowed_flags = SymbolFlags::PROPERTY | SymbolFlags::OPTIONAL;
    let unsupported_flags = SymbolFlags::METHOD
        | SymbolFlags::SIGNATURE
        | SymbolFlags::ACCESSOR
        | SymbolFlags::CONSTRUCTOR;
    let mut domain = DeclaredOwnerMemberDomain::PropertyOnly;
    for (_, property) in table.iter() {
        let Some(property) = store.symbol(property) else {
            return DeclaredOwnerMemberDomain::Malformed;
        };
        if property.flags().contains(SymbolFlags::PROPERTY)
            && property.flags().without(allowed_flags) == SymbolFlags::NONE
        {
            let declarations = property.declarations().unwrap_or_default();
            match declarations {
                [declaration]
                    if matches!(
                        store.source_node_kind(*declaration),
                        Some(SyntaxKind::PropertyDeclaration | SyntaxKind::PropertySignature)
                    ) => {}
                [] => return DeclaredOwnerMemberDomain::Malformed,
                _ => {
                    let mut unique = HashSet::with_capacity(declarations.len());
                    if declarations.iter().all(|declaration| {
                        unique.insert(*declaration)
                            && matches!(
                                store.source_node_kind(*declaration),
                                Some(
                                    SyntaxKind::PropertyDeclaration | SyntaxKind::PropertySignature
                                )
                            )
                    }) {
                        domain = DeclaredOwnerMemberDomain::Unsupported;
                    } else {
                        return DeclaredOwnerMemberDomain::Malformed;
                    }
                }
            }
        } else if property.flags().intersects(unsupported_flags) {
            domain = DeclaredOwnerMemberDomain::Unsupported;
        } else {
            return DeclaredOwnerMemberDomain::Malformed;
        }
    }
    domain
}

fn declared_property_alias_is_generic(
    store: &CanonicalTypeMapperStore,
    alias: super::TypeAliasId,
) -> bool {
    store
        .type_alias(alias)
        .and_then(super::type_records::TypeAlias::symbol)
        .and_then(|symbol| store.type_alias_links(symbol))
        .is_some_and(|links| links.type_parameters.is_some() || links.instantiations.is_some())
}

fn validate_resolved_property_interface(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
    record: &TypeRecord,
    interface: &InterfaceTypeData,
) -> DetailedDeclaredPropertyObjectValidation {
    use DetailedDeclaredPropertyObjectValidation::{
        Malformed, NotDeclared, TraversableBoundary, Valid,
    };

    let structured = &interface.reference.object.structured;
    if record.object_flags() != ObjectFlags::INTERFACE | ObjectFlags::MEMBERS_RESOLVED
        || record.alias().is_some()
        || !valid_thisless_interface_identity(interface)
        || !interface.base_types_resolved
        || interface.resolved_base_constructor_type.is_some()
        || interface.resolved_base_types.is_some()
        || !interface.declared_members_resolved
        || interface.declared_members != structured.members
        || interface.declared_call_signatures.is_some()
        || interface.declared_construct_signatures.is_some()
        || interface.declared_index_infos.is_some()
        || !valid_resolved_declared_structured_shell(&interface.reference.object)
    {
        return Malformed;
    }
    let Some(owner) = record.symbol() else {
        return Malformed;
    };
    let (declaration, boundary) = match validate_declared_property_owner(
        store,
        type_,
        owner,
        structured.members,
        DeclaredPropertyObjectProof::Interface,
    ) {
        DeclaredPropertyOwnerValidation::Valid(declaration) => (declaration, false),
        DeclaredPropertyOwnerValidation::TraversableBoundary(declaration) => (declaration, true),
        DeclaredPropertyOwnerValidation::Unsupported => return NotDeclared,
        DeclaredPropertyOwnerValidation::Malformed => return Malformed,
    };
    if validate_declared_property_members(store, owner, declaration, structured) {
        if boundary {
            TraversableBoundary(DeclaredPropertyObjectProof::Interface)
        } else {
            Valid(DeclaredPropertyObjectProof::Interface)
        }
    } else {
        Malformed
    }
}

fn validate_resolved_property_type_literal(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
    record: &TypeRecord,
    object: &ObjectTypeData,
) -> DetailedDeclaredPropertyObjectValidation {
    use DetailedDeclaredPropertyObjectValidation::{Malformed, TraversableBoundary, Valid};

    let alias_boundary = match validate_declared_property_alias_provenance(store, type_, record) {
        DeclaredPropertyAliasValidation::Valid => false,
        DeclaredPropertyAliasValidation::Unsupported => true,
        DeclaredPropertyAliasValidation::Malformed => return Malformed,
    };
    if record.object_flags() != ObjectFlags::ANONYMOUS | ObjectFlags::MEMBERS_RESOLVED
        || !valid_resolved_declared_structured_shell(object)
    {
        return Malformed;
    }
    let Some(owner) = record.symbol() else {
        return Malformed;
    };
    let (declaration, owner_boundary) = match validate_declared_property_owner(
        store,
        type_,
        owner,
        object.structured.members,
        DeclaredPropertyObjectProof::TypeLiteral,
    ) {
        DeclaredPropertyOwnerValidation::Valid(declaration) => (declaration, false),
        DeclaredPropertyOwnerValidation::TraversableBoundary(declaration) => (declaration, true),
        DeclaredPropertyOwnerValidation::Unsupported => {
            return DetailedDeclaredPropertyObjectValidation::NotDeclared;
        }
        DeclaredPropertyOwnerValidation::Malformed => return Malformed,
    };
    if validate_declared_property_members(store, owner, declaration, &object.structured) {
        if alias_boundary || owner_boundary {
            TraversableBoundary(DeclaredPropertyObjectProof::TypeLiteral)
        } else {
            Valid(DeclaredPropertyObjectProof::TypeLiteral)
        }
    } else {
        Malformed
    }
}

fn valid_resolved_declared_structured_shell(object: &ObjectTypeData) -> bool {
    valid_object_tail(object)
        && object.structured.constrained == ConstrainedTypeData::default()
        && object.structured.signatures.is_none()
        && object.structured.call_signature_count == 0
        && object.structured.index_infos.is_none()
        && object
            .structured
            .object_type_without_abstract_construct_signatures
            .is_none()
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum DeclaredPropertyOwnerValidation {
    Valid(NodeRef),
    TraversableBoundary(NodeRef),
    Unsupported,
    Malformed,
}

fn validate_declared_property_owner(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
    owner: SemanticSymbolId,
    members: Option<SymbolTableId>,
    proof: DeclaredPropertyObjectProof,
) -> DeclaredPropertyOwnerValidation {
    use DeclaredPropertyOwnerValidation::{Malformed, TraversableBoundary, Unsupported, Valid};

    let Some(owner_record) = store.symbol(owner) else {
        return Malformed;
    };
    let (expected_flags, expected_kind, valid_name) = match proof {
        DeclaredPropertyObjectProof::Interface => (
            SymbolFlags::INTERFACE,
            SyntaxKind::InterfaceDeclaration,
            owner_record.name().as_utf8().is_some(),
        ),
        DeclaredPropertyObjectProof::TypeLiteral => (
            SymbolFlags::TYPE_LITERAL,
            SyntaxKind::TypeLiteral,
            owner_record.name() == InternalSymbolName::Type.as_ref(),
        ),
    };
    let declarations = owner_record.declarations().unwrap_or_default();
    if declarations.len() != 1 {
        let mut unique = HashSet::with_capacity(declarations.len());
        return if declarations.len() > 1
            && declarations.iter().all(|declaration| {
                unique.insert(*declaration)
                    && store.source_node_kind(*declaration) == Some(expected_kind)
            }) {
            Unsupported
        } else {
            Malformed
        };
    }
    let declaration = declarations[0];
    if store.get_merged_symbol(owner) != Some(owner)
        || owner_record.flags() != expected_flags
        || owner_record.check_flags() != CheckFlags::NONE
        || !valid_name
        || owner_record.value_declaration().is_some()
        || owner_record.members() != members
        || store.source_node_kind(declaration) != Some(expected_kind)
    {
        return Malformed;
    }
    let valid_identity_cache = match proof {
        DeclaredPropertyObjectProof::Interface => store
            .declared_type_links(owner)
            .is_some_and(|links| links.declared_type == Some(type_)),
        DeclaredPropertyObjectProof::TypeLiteral => {
            store.type_node_links(declaration).is_some_and(|links| {
                links.resolved_type == Some(type_) && links.outer_type_parameters.is_none()
            })
        }
    };
    if !valid_identity_cache {
        return Malformed;
    }
    let has_owner_relationship = owner_record.parent().is_some()
        || owner_record.exports().is_some()
        || owner_record.export_symbol().is_some();
    if proof == DeclaredPropertyObjectProof::Interface
        && declaration_has_external_owner_shape(store, declaration)
    {
        TraversableBoundary(declaration)
    } else if has_owner_relationship {
        Malformed
    } else {
        Valid(declaration)
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum DeclaredPropertyAliasValidation {
    Valid,
    Unsupported,
    Malformed,
}

fn validate_declared_property_alias_provenance(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
    record: &TypeRecord,
) -> DeclaredPropertyAliasValidation {
    use DeclaredPropertyAliasValidation::{Malformed, Unsupported, Valid};

    let Ok(expected_owner) = direct_type_literal_alias_owner(store, type_, record) else {
        return Malformed;
    };
    let (alias, expected_owner) = match (record.alias(), expected_owner) {
        (None, None) => return Valid,
        (Some(alias), Some(expected_owner)) => (alias, expected_owner),
        (None, Some(_)) | (Some(_), None) => return Malformed,
    };
    let Some(alias_record) = store.type_alias(alias) else {
        return Malformed;
    };
    let Some(symbol) = alias_record.symbol() else {
        return Malformed;
    };
    let Some(symbol_record) = store.symbol(symbol) else {
        return Malformed;
    };
    let [declaration] = symbol_record.declarations().unwrap_or_default() else {
        return Malformed;
    };
    let valid_core = symbol == expected_owner
        && alias_record.type_arguments().is_none()
        && store.get_merged_symbol(symbol) == Some(symbol)
        && symbol_record.flags() == SymbolFlags::TYPE_ALIAS
        && symbol_record.check_flags() == CheckFlags::NONE
        && symbol_record.value_declaration().is_none()
        && store.source_node_kind(*declaration) == Some(SyntaxKind::TypeAliasDeclaration)
        && store.type_alias_links(symbol).is_some_and(|links| {
            links.declared_type == Some(type_)
                && links.type_parameters.is_none()
                && links.instantiations.is_none()
                && !links.is_constructor_declared_property
        });
    if !valid_core {
        return Malformed;
    }
    let has_owner_relationship = symbol_record.parent().is_some()
        || symbol_record.exports().is_some()
        || symbol_record.export_symbol().is_some();
    if declaration_has_external_owner_shape(store, *declaration) {
        Unsupported
    } else if has_owner_relationship {
        Malformed
    } else {
        Valid
    }
}

fn declaration_has_external_owner_shape(
    store: &CanonicalTypeMapperStore,
    declaration: NodeRef,
) -> bool {
    if store.source_node_is_exported(declaration) == Some(true) {
        return true;
    }
    match store.source_node_parent(declaration) {
        Some(SourceNodeParent::Parent(parent)) => store
            .source_node_kind(parent)
            .is_some_and(|kind| kind != SyntaxKind::SourceFile),
        Some(SourceNodeParent::Root) | None => false,
    }
}

/// Returns the expected owner for a direct type-alias RHS or `None` for an
/// inline type literal. The reverse declared-type index is essential here:
/// AST parentage alone cannot prove which alias semantically owns `type_`.
fn direct_type_literal_alias_owner(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
    record: &TypeRecord,
) -> Result<Option<SemanticSymbolId>, ()> {
    let mut node = record
        .symbol()
        .and_then(|owner| store.symbol(owner))
        .and_then(|owner| owner.declarations())
        .and_then(|declarations| declarations.first())
        .copied()
        .ok_or(())?;
    let alias_declaration = loop {
        let SourceNodeParent::Parent(parent) = store.source_node_parent(node).ok_or(())? else {
            return Err(());
        };
        match store.source_node_kind(parent).ok_or(())? {
            SyntaxKind::ParenthesizedType => node = parent,
            SyntaxKind::TypeAliasDeclaration => break Some(parent),
            _ => break None,
        }
    };
    let Some(alias_declaration) = alias_declaration else {
        return Ok(None);
    };
    let owners = store.type_alias_declared_type_owners(type_).ok_or(())?;
    let mut matches = owners.iter().copied().filter(|owner| {
        store.symbol(*owner).is_some_and(|symbol| {
            symbol.declarations() == Some(&[alias_declaration][..])
                && symbol.flags() == SymbolFlags::TYPE_ALIAS
        })
    });
    let owner = matches.next().ok_or(())?;
    if matches.next().is_some() {
        return Err(());
    }
    Ok(Some(owner))
}

fn validate_declared_property_members(
    store: &CanonicalTypeMapperStore,
    owner: SemanticSymbolId,
    owner_declaration: NodeRef,
    structured: &StructuredTypeData,
) -> bool {
    let properties = match structured.properties.as_deref() {
        None => &[][..],
        Some(properties) if !properties.is_empty() => properties,
        Some(_) => return false,
    };
    let table = match (structured.members, properties.is_empty()) {
        (None, true) => None,
        (Some(members), false) => match store.symbol_table(members) {
            Some(table) if table.len() == properties.len() => Some(table),
            _ => return false,
        },
        _ => return false,
    };
    let mut seen_properties = HashSet::with_capacity(properties.len());
    let mut seen_declarations = HashSet::with_capacity(properties.len());
    let mut previous_declaration = None;
    for property in properties {
        if !seen_properties.insert(*property) {
            return false;
        }
        let Some(property_record) = store.symbol(*property) else {
            return false;
        };
        let [declaration] = property_record.declarations().unwrap_or_default() else {
            return false;
        };
        let allowed_flags = SymbolFlags::PROPERTY | SymbolFlags::OPTIONAL;
        if !property_record.flags().contains(SymbolFlags::PROPERTY)
            || property_record.flags().without(allowed_flags) != SymbolFlags::NONE
            || property_record.check_flags().bits() & !CheckFlags::READONLY.bits() != 0
            || property_record.name().is_reserved_member_name()
            || property_record.name().is_private_identifier()
            || property_record.name().is_late_bound()
            || property_record.name().as_utf8().is_none()
            || property_record.value_declaration() != Some(*declaration)
            || property_record.parent() != Some(owner)
            || property_record.members().is_some()
            || property_record.exports().is_some()
            || property_record.export_symbol().is_some()
            || store.get_merged_symbol(*property) != Some(*property)
            || !matches!(
                store.source_node_kind(*declaration),
                Some(SyntaxKind::PropertyDeclaration | SyntaxKind::PropertySignature)
            )
            || !declaration.is_for(owner_declaration.arena, owner_declaration.file)
            || *declaration >= owner_declaration
            || previous_declaration.is_some_and(|previous| previous >= *declaration)
            || !seen_declarations.insert(*declaration)
            || table.and_then(|table| table.get(property_record.name())) != Some(*property)
        {
            return false;
        }
        let Some(links) = store.value_symbol_links(*property) else {
            return false;
        };
        let Some(property_type) = links.resolved_type else {
            return false;
        };
        if links
            != &(ValueSymbolLinks {
                resolved_type: Some(property_type),
                ..ValueSymbolLinks::default()
            })
            || store.type_payload(property_type).is_none()
        {
            return false;
        }
        previous_declaration = Some(*declaration);
    }
    table.is_none_or(|table| {
        table.iter().all(|(name, property)| {
            seen_properties.contains(&property)
                && store
                    .symbol(property)
                    .is_some_and(|record| record.name() == name)
        })
    })
}

fn valid_alias(
    store: &CanonicalTypeMapperStore,
    record: &TypeRecord,
    alias_symbol: Option<SemanticSymbolId>,
) -> bool {
    match (record.alias(), alias_symbol) {
        (None, None) => true,
        (Some(alias), Some(symbol)) => store.type_alias(alias).is_some_and(|alias| {
            alias.symbol() == Some(symbol) && alias.type_arguments().is_none()
        }),
        _ => false,
    }
}

fn valid_object_tail(object: &ObjectTypeData) -> bool {
    object.target.is_none()
        && object.mapper.is_none()
        && object.instantiations == TypeCacheState::Unallocated
}

fn valid_thisless_interface_identity(interface: &InterfaceTypeData) -> bool {
    interface.all_type_parameters.is_none()
        && interface.outer_type_parameter_count == 0
        && interface.this_type.is_none()
        && interface.reference.object.target.is_none()
        && interface.reference.object.mapper.is_none()
        && interface.reference.object.instantiations == TypeCacheState::Unallocated
        && interface.reference.node.is_none()
        && interface.reference.resolved_type_arguments.is_none()
}

fn valid_unresolved_interface_members(interface: &InterfaceTypeData) -> bool {
    // Pinned `getBaseTypes` and `resolveDeclaredMembers` have independent
    // caches. Resolving an empty base list before declared members is a valid
    // shell state, not a corrupt partially initialized interface.
    valid_thisless_interface_identity(interface)
        && interface.reference.object.structured == StructuredTypeData::default()
        && interface.resolved_base_constructor_type.is_none()
        && interface.resolved_base_types.is_none()
        && !interface.declared_members_resolved
        && interface.declared_members.is_none()
        && interface.declared_call_signatures.is_none()
        && interface.declared_construct_signatures.is_none()
        && interface.declared_index_infos.is_none()
}

fn valid_declared_structured_members(
    store: &CanonicalTypeMapperStore,
    object: &ObjectTypeData,
    plan: &PropertyObjectPlan,
) -> bool {
    let call_signatures = resolved_call_signature_ids(store, plan);
    (plan.call_signatures.is_empty()
        || store.type_has_declared_call_set_provenance(
            match plan.kind {
                PropertyObjectKind::TypeLiteral => store
                    .type_node_links(plan.node)
                    .and_then(|links| links.resolved_type),
                PropertyObjectKind::Interface => store
                    .declared_type_links(plan.symbol)
                    .and_then(|links| links.declared_type),
                PropertyObjectKind::ObjectLiteral => None,
            }
            .unwrap_or_else(|| {
                store
                    .intrinsic_bootstrap()
                    .expect("declared object validation requires bootstrap")
                    .error_type
            }),
        ))
        && valid_object_tail(object)
        && object.structured.constrained == ConstrainedTypeData::default()
        && object.structured.members == plan.members
        && object.structured.properties == plan.expected_properties()
        && object.structured.signatures.as_deref() == call_signatures.as_deref()
        && object.structured.call_signature_count == call_signatures.as_ref().map_or(0, Vec::len)
        && valid_declared_index_infos(store, object.structured.index_infos.as_deref(), plan)
        && object
            .structured
            .object_type_without_abstract_construct_signatures
            .is_none()
}

fn valid_declared_index_infos(
    store: &CanonicalTypeMapperStore,
    index_infos: Option<&[super::IndexInfoId]>,
    plan: &PropertyObjectPlan,
) -> bool {
    let indexes = index_infos.unwrap_or_default();
    if indexes.len() != plan.indexes.len() || plan.indexes.is_empty() != index_infos.is_none() {
        return false;
    }
    let Some(bootstrap) = store.intrinsic_bootstrap() else {
        return false;
    };
    let mut seen = HashSet::with_capacity(indexes.len());
    indexes.iter().zip(&plan.indexes).all(|(id, planned)| {
        if !seen.insert(*id) {
            return false;
        }
        let expected_key = match store.source_node_kind(planned.key_type_node) {
            Some(SyntaxKind::StringKeyword) => bootstrap.string_type,
            Some(SyntaxKind::NumberKeyword) => bootstrap.number_type,
            _ => return false,
        };
        store.index_info(*id).is_some_and(|info| {
            info.key_type() == expected_key
                && store.type_payload(info.key_type()).is_some()
                && store.type_payload(info.value_type()).is_some()
                && cached_planned_type_identity(store, planned.value_type_node)
                    .is_none_or(|value_type| info.value_type() == value_type)
                && info.is_readonly() == planned.readonly
                && info.declaration() == Some(planned.declaration)
                && info.index_symbol().is_none()
                && info.components().is_empty()
        })
    })
}

fn cached_planned_type_identity(store: &CanonicalTypeMapperStore, node: NodeRef) -> Option<TypeId> {
    let bootstrap = store.intrinsic_bootstrap()?;
    match store.source_node_kind(node)? {
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
        _ => store
            .type_node_links(node)
            .and_then(|links| links.resolved_type),
    }
}

fn cached_annotation_identity(
    store: &CanonicalTypeMapperStore,
    node: NodeRef,
    null_literal_identity: bool,
) -> Option<TypeId> {
    if null_literal_identity {
        store
            .intrinsic_bootstrap()
            .map(|bootstrap| bootstrap.null_type)
    } else {
        cached_planned_type_identity(store, node)
    }
}

fn peel_parenthesized_type(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    mut node: NodeRef,
) -> Result<NodeRef, PropertyObjectError> {
    loop {
        let record = preflight_node(store, host, node).map_err(|_| {
            PropertyObjectError::UnsupportedMember {
                node,
                kind: SyntaxKind::ParenthesizedType,
            }
        })?;
        let NodeData::ParenthesizedTypeNode(parenthesized) = &record.data else {
            return Ok(node);
        };
        if record.kind != SyntaxKind::ParenthesizedType {
            return Err(PropertyObjectError::UnsupportedMember {
                node,
                kind: record.kind,
            });
        }
        let inner = NodeRef::new(node.arena, node.file, parenthesized.type_);
        if preflight_node(store, host, inner)
            .map_err(|_| PropertyObjectError::UnsupportedMember {
                node: inner,
                kind: SyntaxKind::ParenthesizedType,
            })?
            .parent
            != Some(node.node)
        {
            return Err(PropertyObjectError::UnsupportedMember {
                node,
                kind: SyntaxKind::ParenthesizedType,
            });
        }
        node = inner;
    }
}

fn is_null_literal_type(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    node: NodeRef,
) -> Result<bool, PropertyObjectError> {
    let record =
        preflight_node(store, host, node).map_err(|_| PropertyObjectError::UnsupportedMember {
            node,
            kind: SyntaxKind::LiteralType,
        })?;
    let NodeData::LiteralTypeNode(literal) = &record.data else {
        return Ok(false);
    };
    if record.kind != SyntaxKind::LiteralType {
        return Err(PropertyObjectError::UnsupportedMember {
            node,
            kind: record.kind,
        });
    }
    let literal = NodeRef::new(node.arena, node.file, literal.literal);
    let literal_record = preflight_node(store, host, literal).map_err(|_| {
        PropertyObjectError::UnsupportedMember {
            node: literal,
            kind: SyntaxKind::LiteralType,
        }
    })?;
    if literal_record.parent != Some(node.node) || literal_record.range != record.range {
        return Err(PropertyObjectError::UnsupportedMember {
            node,
            kind: SyntaxKind::LiteralType,
        });
    }
    Ok(literal_record.kind == SyntaxKind::NullKeyword
        && matches!(literal_record.data, NodeData::KeywordExpression(_)))
}

fn object_literal_property_types(
    store: &CanonicalTypeMapperStore,
    object: &ObjectTypeData,
    plan: &PropertyObjectPlan,
) -> Option<Vec<TypeId>> {
    if !valid_object_tail(object)
        || object.structured.constrained != ConstrainedTypeData::default()
        || object.structured.signatures.is_some()
        || object.structured.call_signature_count != 0
        || object.structured.index_infos.is_some()
        || object
            .structured
            .object_type_without_abstract_construct_signatures
            .is_some()
        || !unresolved_property_links(store, plan)
    {
        return None;
    }
    let members = object.structured.members?;
    if Some(members) == plan.members {
        return None;
    }
    let table = store.symbol_table(members)?;
    if table.len() != plan.properties.len() {
        return None;
    }
    let property_symbols = match object.structured.properties.as_deref() {
        None if plan.properties.is_empty() => &[][..],
        Some(properties) if !properties.is_empty() && properties.len() == plan.properties.len() => {
            properties
        }
        _ => return None,
    };
    let mut seen = HashSet::with_capacity(property_symbols.len());
    let mut property_types = Vec::with_capacity(property_symbols.len());
    for (property, cloned_symbol) in plan.properties.iter().zip(property_symbols) {
        if !seen.insert(*cloned_symbol) || table.get_source(&property.name) != Some(*cloned_symbol)
        {
            return None;
        }
        property_types.push(valid_object_literal_property(
            store,
            plan.symbol,
            property,
            *cloned_symbol,
        )?);
    }
    Some(property_types)
}

fn valid_object_literal_property(
    store: &CanonicalTypeMapperStore,
    owner: SemanticSymbolId,
    property: &PlannedProperty,
    cloned_symbol: SemanticSymbolId,
) -> Option<TypeId> {
    if cloned_symbol == property.symbol
        || store.get_merged_symbol(cloned_symbol) != Some(cloned_symbol)
    {
        return None;
    }
    let bound = store.symbol(property.symbol)?;
    let cloned = store.symbol(cloned_symbol)?;
    if cloned.flags() != (bound.flags() | SymbolFlags::PROPERTY | SymbolFlags::TRANSIENT)
        || cloned.check_flags() != CheckFlags::NONE
        || cloned.name() != bound.name()
        || cloned.declarations() != bound.declarations()
        || cloned.value_declaration() != bound.value_declaration()
        || cloned.members().is_some()
        || cloned.exports().is_some()
        || cloned.parent() != bound.parent()
        || cloned.parent() != Some(owner)
        || cloned.export_symbol().is_some()
    {
        return None;
    }
    let links = store.value_symbol_links(cloned_symbol)?;
    let resolved_type = links.resolved_type?;
    let expected = ValueSymbolLinks {
        resolved_type: Some(resolved_type),
        target: Some(property.symbol),
        ..ValueSymbolLinks::default()
    };
    (links == &expected && store.type_payload(resolved_type).is_some()).then_some(resolved_type)
}

fn unresolved_property_links(store: &CanonicalTypeMapperStore, plan: &PropertyObjectPlan) -> bool {
    plan.properties.iter().all(|property| {
        store.symbol(property.symbol).is_some_and(|record| {
            let expected = source_property_check_flags(property.readonly);
            record.check_flags() == CheckFlags::NONE || record.check_flags() == expected
        }) && store
            .value_symbol_links(property.symbol)
            .is_none_or(|links| links == &ValueSymbolLinks::default())
    }) && plan.call_signatures.iter().all(|signature| {
        store
            .signature_links(signature.declaration)
            .is_none_or(|links| links == &SignatureLinks::default())
            && signature.parameters.iter().all(|parameter| {
                store
                    .value_symbol_links(parameter.symbol)
                    .is_none_or(|links| links == &ValueSymbolLinks::default())
            })
    })
}

fn resolved_property_links(store: &CanonicalTypeMapperStore, plan: &PropertyObjectPlan) -> bool {
    plan.properties.iter().all(|property| {
        store.symbol(property.symbol).is_some_and(|record| {
            record.check_flags() == source_property_check_flags(property.readonly)
        }) && store
            .value_symbol_links(property.symbol)
            .is_some_and(|links| {
                let expected = ValueSymbolLinks {
                    resolved_type: links.resolved_type,
                    ..ValueSymbolLinks::default()
                };
                links == &expected
                    && links
                        .resolved_type
                        .is_some_and(|type_| store.type_payload(type_).is_some())
            })
    }) && resolved_call_signature_ids(store, plan).is_some() != plan.call_signatures.is_empty()
}

fn resolved_call_signature_ids(
    store: &CanonicalTypeMapperStore,
    plan: &PropertyObjectPlan,
) -> Option<Vec<SignatureId>> {
    if plan.call_signatures.is_empty() {
        return None;
    }
    plan.call_signatures
        .iter()
        .map(|planned| validate_resolved_call_signature(store, planned))
        .collect()
}

fn validate_resolved_call_signature(
    store: &CanonicalTypeMapperStore,
    planned: &PlannedCallSignature,
) -> Option<SignatureId> {
    let links = store.signature_links(planned.declaration)?;
    let signature = match links.resolved_signature {
        ResolvedSignatureState::Resolved(signature)
            if links
                == &(SignatureLinks {
                    resolved_signature: ResolvedSignatureState::Resolved(signature),
                    ..SignatureLinks::default()
                }) =>
        {
            signature
        }
        _ => return None,
    };
    let record = store.signature(signature)?;
    let parameter_symbols = planned
        .parameters
        .iter()
        .map(|parameter| parameter.symbol)
        .collect::<Vec<_>>();
    let parameter_types = store.callable_signature_parameter_types(signature)?;
    let return_type = record.resolved_return_type()?;
    let minimum = i32::try_from(planned.parameters.len()).ok()?;
    if record.flags() != planned.flags
        || record.min_argument_count() != minimum
        || record.resolved_min_argument_count() != -1
        || record.declaration() != Some(planned.declaration)
        || !record.type_parameters().is_empty()
        || record.this_parameter().is_some()
        || record.parameters() != parameter_symbols.as_slice()
        || record.resolved_type_predicate().is_some()
        || record.target().is_some()
        || record.mapper().is_some()
        || record.isolated_signature_type().is_some()
        || record.composite().is_some()
        || store.signature_has_circular_return_type(signature)
        || store.function_signature_return_annotation(signature)
            != Some((
                planned.return_identity_node,
                planned.return_null_literal_identity,
            ))
        || cached_annotation_identity(
            store,
            planned.return_identity_node,
            planned.return_null_literal_identity,
        ) != Some(return_type)
        || parameter_types.len() != planned.parameters.len()
    {
        return None;
    }
    for (parameter, type_) in planned.parameters.iter().zip(parameter_types) {
        if cached_annotation_identity(
            store,
            parameter.identity_node,
            parameter.null_literal_identity,
        ) != Some(*type_)
            || store.value_symbol_links(parameter.symbol)
                != Some(&ValueSymbolLinks {
                    resolved_type: Some(*type_),
                    ..ValueSymbolLinks::default()
                })
        {
            return None;
        }
    }
    Some(signature)
}

pub(super) fn validate_resolved_property_types(
    store: &CanonicalTypeMapperStore,
    plan: &PropertyObjectPlan,
    property_types: &[TypeId],
) -> Result<(), PropertyObjectError> {
    let valid = if plan.kind == PropertyObjectKind::ObjectLiteral {
        store
            .type_node_links(plan.node)
            .and_then(|links| links.resolved_type)
            .and_then(|type_| store.type_payload(type_))
            .and_then(|record| match record.data() {
                TypeData::Object(object) => object_literal_property_types(store, object, plan),
                _ => None,
            })
            .is_some_and(|resolved| resolved == property_types)
    } else {
        property_types.len() == plan.properties.len()
            && plan
                .properties
                .iter()
                .zip(property_types)
                .all(|(property, type_)| {
                    store.symbol(property.symbol).is_some_and(|record| {
                        record.check_flags() == source_property_check_flags(property.readonly)
                    }) && store
                        .value_symbol_links(property.symbol)
                        .and_then(|links| links.resolved_type)
                        == Some(*type_)
                })
    };
    if !valid {
        let type_ = match plan.kind {
            PropertyObjectKind::TypeLiteral | PropertyObjectKind::ObjectLiteral => store
                .type_node_links(plan.node)
                .and_then(|links| links.resolved_type),
            PropertyObjectKind::Interface => store
                .declared_type_links(plan.symbol)
                .and_then(|links| links.declared_type),
        }
        .unwrap_or_else(|| {
            store
                .intrinsic_bootstrap()
                .expect("type queries require bootstrap")
                .error_type
        });
        return Err(invalid_cache(plan, type_));
    }
    Ok(())
}

pub(super) fn validate_resolved_declared_member_types(
    store: &CanonicalTypeMapperStore,
    plan: &PropertyObjectPlan,
    property_types: &[TypeId],
    index_types: &[(TypeId, TypeId)],
    call_types: &[ResolvedCallSignatureTypes],
) -> Result<(), PropertyObjectError> {
    validate_resolved_property_types(store, plan, property_types)?;
    let type_ = match plan.kind {
        PropertyObjectKind::TypeLiteral => store
            .type_node_links(plan.node)
            .and_then(|links| links.resolved_type),
        PropertyObjectKind::Interface => store
            .declared_type_links(plan.symbol)
            .and_then(|links| links.declared_type),
        PropertyObjectKind::ObjectLiteral => None,
    }
    .ok_or_else(|| invalid_plan(plan))?;
    let index_infos = store
        .type_payload(type_)
        .and_then(|record| record.data().structured())
        .and_then(|structured| structured.index_infos.as_deref())
        .unwrap_or_default();
    let valid = index_types.len() == plan.indexes.len()
        && index_infos.len() == index_types.len()
        && index_infos
            .iter()
            .zip(index_types)
            .all(|(id, (key_type, value_type))| {
                store.index_info(*id).is_some_and(|info| {
                    info.key_type() == *key_type && info.value_type() == *value_type
                })
            });
    let valid_calls = call_types.len() == plan.call_signatures.len()
        && plan
            .call_signatures
            .iter()
            .zip(call_types)
            .all(|(planned, resolved)| {
                validate_resolved_call_signature(store, planned).is_some_and(|signature| {
                    store.callable_signature_parameter_types(signature)
                        == Some(resolved.parameter_types.as_slice())
                        && store
                            .signature(signature)
                            .and_then(super::signatures::Signature::resolved_return_type)
                            == Some(resolved.return_type)
                })
            });
    if valid && valid_calls {
        Ok(())
    } else {
        Err(invalid_cache(plan, type_))
    }
}

#[cfg(test)]
pub(super) fn publish_property_members(
    store: &mut CanonicalTypeMapperStore,
    plan: &PropertyObjectPlan,
    state: PropertyObjectState,
    property_types: &[TypeId],
) -> Result<TypeId, PropertyObjectError> {
    if !plan.indexes.is_empty() {
        return Err(invalid_cache(plan, state.type_id()));
    }
    publish_declared_members(store, plan, state, property_types, &[], &[])
}

pub(super) fn publish_declared_members(
    store: &mut CanonicalTypeMapperStore,
    plan: &PropertyObjectPlan,
    state: PropertyObjectState,
    property_types: &[TypeId],
    index_types: &[(TypeId, TypeId)],
    call_types: &[ResolvedCallSignatureTypes],
) -> Result<TypeId, PropertyObjectError> {
    if plan.kind == PropertyObjectKind::ObjectLiteral {
        return Err(PropertyObjectError::InvalidObjectLiteral(plan.node));
    }
    let type_ = state.type_id();
    if state.is_resolved() {
        validate_resolved_declared_member_types(
            store,
            plan,
            property_types,
            index_types,
            call_types,
        )?;
        return Ok(type_);
    }
    if property_types.len() != plan.properties.len()
        || index_types.len() != plan.indexes.len()
        || call_types.len() != plan.call_signatures.len()
        || property_types
            .iter()
            .any(|type_| store.type_payload(*type_).is_none())
        || index_types.iter().any(|(key_type, value_type)| {
            store.type_payload(*key_type).is_none() || store.type_payload(*value_type).is_none()
        })
        || plan
            .call_signatures
            .iter()
            .zip(call_types)
            .any(|(planned, signature)| {
                signature.parameter_types.len() != planned.parameters.len()
                    || signature
                        .parameter_types
                        .iter()
                        .any(|type_| store.type_payload(*type_).is_none())
                    || store.type_payload(signature.return_type).is_none()
            })
        || !unresolved_property_links(store, plan)
    {
        return Err(invalid_cache(plan, type_));
    }

    let Some(bootstrap) = store.intrinsic_bootstrap() else {
        return Err(invalid_cache(plan, type_));
    };
    let mut seen_keys = HashSet::with_capacity(index_types.len());
    let valid_indexes = plan
        .indexes
        .iter()
        .zip(index_types)
        .all(|(planned, (key_type, _))| {
            let expected = match store.source_node_kind(planned.key_type_node) {
                Some(SyntaxKind::StringKeyword) => bootstrap.string_type,
                Some(SyntaxKind::NumberKeyword) => bootstrap.number_type,
                _ => return false,
            };
            *key_type == expected && seen_keys.insert(*key_type)
        });
    if !valid_indexes {
        return Err(invalid_cache(plan, type_));
    }
    if !store.try_reserve_index_infos(plan.indexes.len())
        || !store.try_reserve_signatures(plan.call_signatures.len())
        || !store.try_reserve_function_signature_return_annotations(plan.call_signatures.len())
        || !store.try_reserve_callable_signature_parameter_types(plan.call_signatures.len())
        || !store.try_reserve_declared_call_set_provenance(
            usize::from(!plan.call_signatures.is_empty()),
            plan.call_signatures.len(),
        )
    {
        return Err(PropertyObjectError::Capacity(plan.node));
    }

    for (planned, resolved) in plan.call_signatures.iter().zip(call_types) {
        if cached_annotation_identity(
            store,
            planned.return_identity_node,
            planned.return_null_literal_identity,
        ) != Some(resolved.return_type)
            || planned
                .parameters
                .iter()
                .zip(&resolved.parameter_types)
                .any(|(parameter, type_)| {
                    cached_annotation_identity(
                        store,
                        parameter.identity_node,
                        parameter.null_literal_identity,
                    ) != Some(*type_)
                })
        {
            return Err(invalid_cache(plan, type_));
        }
    }

    let index_infos = plan
        .indexes
        .iter()
        .zip(index_types)
        .map(|(planned, (key_type, value_type))| {
            store
                .alloc_index_info(
                    *key_type,
                    *value_type,
                    planned.readonly,
                    Some(planned.declaration),
                    Vec::new(),
                )
                .expect("the declared-index plan and reservation validated every identity")
        })
        .collect::<Vec<_>>();
    let published_index_infos = (!index_infos.is_empty()).then_some(index_infos);

    let signatures = plan
        .call_signatures
        .iter()
        .zip(call_types)
        .map(|(planned, resolved)| {
            store
                .alloc_signature(
                    planned.flags,
                    Some(planned.declaration),
                    Vec::new(),
                    None,
                    planned
                        .parameters
                        .iter()
                        .map(|parameter| parameter.symbol)
                        .collect(),
                    Some(resolved.return_type),
                    None,
                    i32::try_from(planned.parameters.len())
                        .expect("the call-signature plan validated its fixed arity"),
                )
                .expect("the declared-call plan and reservation validated every identity")
        })
        .collect::<Vec<_>>();
    if !signatures.is_empty() {
        assert!(store.set_declared_call_set_provenance(type_, &signatures));
    }
    for (planned, signature) in plan.call_signatures.iter().zip(&signatures) {
        assert!(store.set_function_signature_return_annotation(
            *signature,
            planned.return_identity_node,
            planned.return_null_literal_identity,
        ));
        assert!(store.set_signature_links(
            planned.declaration,
            SignatureLinks {
                resolved_signature: ResolvedSignatureState::Resolved(*signature),
                ..SignatureLinks::default()
            },
        ));
    }
    let published_signatures = (!signatures.is_empty()).then_some(signatures.clone());

    // All fallible checks precede publication.  The store setters below can
    // only reject foreign identities, all of which were validated above.
    for (property, property_type) in plan.properties.iter().zip(property_types) {
        assert!(
            store.set_source_property_readonly(property.symbol, property.readonly),
            "the declared-member plan validated a bound source property"
        );
        let links = ValueSymbolLinks {
            resolved_type: Some(*property_type),
            ..ValueSymbolLinks::default()
        };
        assert!(store.set_value_symbol_links(property.symbol, links));
    }
    match plan.kind {
        PropertyObjectKind::TypeLiteral => {
            assert!(store.set_structured_type_members(
                type_,
                plan.members,
                plan.expected_properties(),
                published_signatures.clone(),
                None,
                published_index_infos,
            ));
        }
        PropertyObjectKind::Interface => {
            assert!(store.set_interface_declared_members(
                type_,
                true,
                plan.members,
                published_signatures.clone(),
                None,
                published_index_infos.clone(),
            ));
            assert!(store.set_interface_base_resolution(type_, true, None, None));
            assert!(store.set_structured_type_members(
                type_,
                plan.members,
                plan.expected_properties(),
                published_signatures.clone(),
                None,
                published_index_infos,
            ));
        }
        PropertyObjectKind::ObjectLiteral => {
            unreachable!("object-literal plans were rejected before publication")
        }
    }
    if !signatures.is_empty() {
        assert!(
            store.set_callable_signature_parameter_types_batch(
                signatures
                    .iter()
                    .copied()
                    .zip(
                        call_types
                            .iter()
                            .map(|resolved| resolved.parameter_types.clone())
                    )
                    .collect(),
            )
        );
        for (planned, resolved) in plan.call_signatures.iter().zip(call_types) {
            for (parameter, type_) in planned.parameters.iter().zip(&resolved.parameter_types) {
                assert!(store.set_value_symbol_links(
                    parameter.symbol,
                    ValueSymbolLinks {
                        resolved_type: Some(*type_),
                        ..ValueSymbolLinks::default()
                    },
                ));
            }
        }
    }
    Ok(type_)
}

/// Publishes a generic interface's declared properties without resolving its
/// lazy instantiated member table.
///
/// The caller must resolve the interface's direct bases first. The publisher
/// checks the full binder-owned target and every planned property before it
/// allocates a declared member table or changes a property link.
pub(super) fn publish_generic_interface_declared_members(
    store: &mut CanonicalTypeMapperStore,
    plan: &PropertyObjectPlan,
    target: TypeId,
    property_types: &[TypeId],
) -> Result<TypeId, PropertyObjectError> {
    let invalid = || PropertyObjectError::InvalidCachedInterface {
        symbol: plan.symbol,
        type_: target,
    };
    if plan.kind != PropertyObjectKind::Interface
        || plan.heritage.is_some()
        || plan.alias_symbol.is_some()
        || !plan.indexes.is_empty()
        || !plan.call_signatures.is_empty()
        || plan.properties.len() != property_types.len()
        || property_types
            .iter()
            .any(|type_| store.type_payload(*type_).is_none())
    {
        return Err(invalid());
    }

    let record = store.type_payload(target).ok_or_else(invalid)?;
    let TypeData::Interface(interface) = record.data() else {
        return Err(invalid());
    };
    if !valid_generic_publication_target(store, plan, target, record, interface)
        || !valid_generic_property_types(store, plan, property_types)
    {
        return Err(invalid());
    }

    if interface.declared_members_resolved {
        let declared_members = interface.declared_members;
        if declared_members == plan.members
            || declared_members.is_some() == plan.properties.is_empty()
            || declared_members
                .and_then(|members| store.symbol_table(members))
                .is_some_and(|table| table.len() != plan.properties.len())
            || !valid_generic_structured_members(store, plan, target, interface)
            || !plan
                .properties
                .iter()
                .zip(property_types)
                .all(|(property, property_type)| {
                    declared_members
                        .and_then(|members| store.symbol_table(members))
                        .and_then(|members| members.get_source(&property.name))
                        == Some(property.symbol)
                        && store.value_symbol_links(property.symbol)
                            == Some(&ValueSymbolLinks {
                                resolved_type: Some(*property_type),
                                ..ValueSymbolLinks::default()
                            })
                        && store.symbol(property.symbol).is_some_and(|record| {
                            record.check_flags() == source_property_check_flags(property.readonly)
                        })
                })
        {
            return Err(invalid());
        }
        return Ok(target);
    }

    if record
        .object_flags()
        .contains(ObjectFlags::MEMBERS_RESOLVED)
        || interface.reference.object.structured != StructuredTypeData::default()
        || interface.declared_members.is_some()
        || !unresolved_property_links(store, plan)
    {
        return Err(invalid());
    }
    let prepared = if plan.properties.is_empty() {
        None
    } else {
        Some(
            PreparedSymbolTable::new(plan.properties.len())
                .ok_or(PropertyObjectError::Capacity(plan.node))?,
        )
    };
    let missing_links = plan
        .properties
        .iter()
        .filter(|property| store.value_symbol_links(property.symbol).is_none())
        .count();
    if !store.try_reserve_checker_symbol_allocations(0, usize::from(prepared.is_some()))
        || !store.try_reserve_value_symbol_links(missing_links)
    {
        return Err(PropertyObjectError::Capacity(plan.node));
    }
    let declared_members = prepared.map(|table| store.alloc_prepared_symbol_table(table));
    for (property, property_type) in plan.properties.iter().zip(property_types) {
        assert!(store.set_source_property_readonly(property.symbol, property.readonly));
        assert!(store.set_value_symbol_links(
            property.symbol,
            ValueSymbolLinks {
                resolved_type: Some(*property_type),
                ..ValueSymbolLinks::default()
            },
        ));
        assert_eq!(
            store.insert_symbol(
                declared_members.expect("a generic property owns a declared member table"),
                EscapedName::source(&property.name),
                property.symbol,
            ),
            Some(None)
        );
    }
    assert!(store.set_interface_declared_members(target, true, declared_members, None, None, None));
    Ok(target)
}

fn valid_generic_publication_target(
    store: &CanonicalTypeMapperStore,
    plan: &PropertyObjectPlan,
    target: TypeId,
    record: &TypeRecord,
    interface: &InterfaceTypeData,
) -> bool {
    let allowed_flags = ObjectFlags::INTERFACE
        | ObjectFlags::REFERENCE
        | ObjectFlags::MEMBERS_RESOLVED
        | ObjectFlags::COULD_CONTAIN_TYPE_VARIABLES
        | ObjectFlags::COULD_CONTAIN_TYPE_VARIABLES_COMPUTED;
    let Some(owner) = store.symbol(plan.symbol) else {
        return false;
    };
    let Some(raw_members) = plan.members else {
        return false;
    };
    let Some(raw_table) = store.symbol_table(raw_members) else {
        return false;
    };
    let Ok(reference) = validate_direct_generic_reference(store, target) else {
        return false;
    };
    if record.flags() != TypeFlags::OBJECT
        || record.object_flags() & ObjectFlags::OBJECT_TYPE_KIND_MASK
            != (ObjectFlags::INTERFACE | ObjectFlags::REFERENCE)
        || !(record.object_flags() & !allowed_flags).is_empty()
        || record.symbol() != Some(plan.symbol)
        || record.alias().is_some()
        || owner.flags() != SymbolFlags::INTERFACE
        || owner.check_flags() != CheckFlags::NONE
        || owner.declarations() != Some(&[plan.node])
        || owner.value_declaration().is_some()
        || owner.members() != Some(raw_members)
        || owner.exports().is_some()
        || owner.parent().is_some()
        || owner.export_symbol().is_some()
        || store.get_merged_symbol(plan.symbol) != Some(plan.symbol)
        || store
            .declared_type_links(plan.symbol)
            .and_then(|links| links.declared_type)
            != Some(target)
        || reference.target != target
        || reference.type_arguments.is_empty()
        || !interface.base_types_resolved
        || interface.resolved_base_constructor_type.is_some()
        || interface.resolved_base_types.is_some()
        || interface.declared_call_signatures.is_some()
        || interface.declared_construct_signatures.is_some()
        || interface.declared_index_infos.is_some()
        || raw_table.len() != reference.type_arguments.len() + plan.properties.len()
    {
        return false;
    }

    let mut symbols = HashSet::with_capacity(raw_table.len());
    for parameter in reference.type_arguments {
        let Some(symbol) = cached_ordinary_type_parameter_owner(store, parameter) else {
            return false;
        };
        let Some(record) = store.symbol(symbol) else {
            return false;
        };
        if record.parent() != Some(plan.symbol)
            || raw_table.get(record.name()) != Some(symbol)
            || !symbols.insert(symbol)
        {
            return false;
        }
    }
    let mut names = HashSet::with_capacity(plan.properties.len());
    let mut declarations = HashSet::with_capacity(plan.properties.len());
    for property in &plan.properties {
        let Some(record) = store.symbol(property.symbol) else {
            return false;
        };
        let expected_flags = SymbolFlags::PROPERTY
            | if property.optional {
                SymbolFlags::OPTIONAL
            } else {
                SymbolFlags::NONE
            };
        let expected_checks = source_property_check_flags(property.readonly);
        if record.flags() != expected_flags
            || record.check_flags() != CheckFlags::NONE && record.check_flags() != expected_checks
            || record.name().as_utf8() != Some(property.name.as_str())
            || record.declarations() != Some(&[property.declaration])
            || record.value_declaration() != Some(property.declaration)
            || record.parent() != Some(plan.symbol)
            || record.members().is_some()
            || record.exports().is_some()
            || record.export_symbol().is_some()
            || store.get_merged_symbol(property.symbol) != Some(property.symbol)
            || raw_table.get(record.name()) != Some(property.symbol)
            || store.source_node_parent(property.declaration)
                != Some(SourceNodeParent::Parent(plan.node))
            || store.source_node_parent(property.name_node)
                != Some(SourceNodeParent::Parent(property.declaration))
            || store.source_node_parent(property.type_node)
                != Some(SourceNodeParent::Parent(property.declaration))
            || !symbols.insert(property.symbol)
            || !names.insert(property.name.as_str())
            || !declarations.insert(property.declaration)
        {
            return false;
        }
    }
    raw_table.iter().all(|(name, symbol)| {
        symbols.contains(&symbol)
            && store
                .symbol(symbol)
                .is_some_and(|record| record.name() == name)
    })
}

fn valid_generic_property_types(
    store: &CanonicalTypeMapperStore,
    plan: &PropertyObjectPlan,
    property_types: &[TypeId],
) -> bool {
    let Some(bootstrap) = store.intrinsic_bootstrap() else {
        return false;
    };
    plan.properties
        .iter()
        .zip(property_types)
        .all(|(property, type_)| {
            if !bootstrap.options.strict_null_checks || !property.optional {
                return true;
            }
            let sentinel = bootstrap.undefined_or_missing_type;
            *type_ == sentinel
                || bootstrap.options.exact_optional_property_types
                    && *type_ == bootstrap.undefined_type
                || store.type_payload(*type_).is_some_and(|record| {
                    record.flags().intersects(TypeFlags::ANY_OR_UNKNOWN)
                        || matches!(
                            record.data(),
                            TypeData::Union(union)
                                if {
                                    let has_sentinel = union.union.types.contains(&sentinel);
                                    let has_undefined =
                                        union.union.types.contains(&bootstrap.undefined_type);
                                    if bootstrap.options.exact_optional_property_types {
                                        has_sentinel != has_undefined
                                    } else {
                                        has_sentinel
                                    }
                                }
                        )
                })
        })
}

fn valid_generic_structured_members(
    store: &CanonicalTypeMapperStore,
    plan: &PropertyObjectPlan,
    target: TypeId,
    interface: &InterfaceTypeData,
) -> bool {
    let structured = &interface.reference.object.structured;
    if !store.type_payload(target).is_some_and(|record| {
        record
            .object_flags()
            .contains(ObjectFlags::MEMBERS_RESOLVED)
    }) {
        return structured == &StructuredTypeData::default();
    }
    if structured.constrained != ConstrainedTypeData::default()
        || structured.signatures.is_some()
        || structured.call_signature_count != 0
        || structured.index_infos.is_some()
        || structured
            .object_type_without_abstract_construct_signatures
            .is_some()
    {
        return false;
    }
    let properties = structured.properties.as_deref().unwrap_or_default();
    if properties.len() != plan.properties.len()
        || properties.is_empty() != structured.properties.is_none()
        || properties
            .iter()
            .zip(&plan.properties)
            .any(|(actual, planned)| *actual != planned.symbol)
    {
        return false;
    }
    if properties.is_empty() {
        return structured.members.is_none();
    }
    structured
        .members
        .and_then(|members| store.symbol_table(members))
        .is_some_and(|table| {
            table.len() == properties.len()
                && plan
                    .properties
                    .iter()
                    .all(|property| table.get_source(&property.name) == Some(property.symbol))
        })
}

pub(super) fn publish_object_literal(
    store: &mut CanonicalTypeMapperStore,
    plan: &PropertyObjectPlan,
    property_types: &[TypeId],
) -> Result<TypeId, PropertyObjectError> {
    debug_assert_eq!(plan.kind, PropertyObjectKind::ObjectLiteral);
    if let Some(state) = object_literal_state(store, plan)? {
        validate_resolved_property_types(store, plan, property_types)?;
        return Ok(state.type_id());
    }
    if property_types.len() != plan.properties.len()
        || property_types
            .iter()
            .any(|type_| store.type_payload(*type_).is_none())
        || !unresolved_property_links(store, plan)
    {
        return Err(PropertyObjectError::InvalidObjectLiteral(plan.node));
    }
    let object_flags = expected_object_literal_flags(store, property_types)
        .ok_or(PropertyObjectError::InvalidObjectLiteral(plan.node))?;
    let cloned_symbol_data = plan
        .properties
        .iter()
        .map(|property| {
            let bound = store.symbol(property.symbol)?;
            let mut data = SymbolData::new(
                bound.flags() | SymbolFlags::PROPERTY | SymbolFlags::TRANSIENT,
                bound.name().to_owned(),
            );
            data.declarations = bound.declarations().map(<[NodeRef]>::to_vec);
            data.value_declaration = bound.value_declaration();
            data.parent = bound.parent();
            Some(data)
        })
        .collect::<Option<Vec<_>>>()
        .ok_or(PropertyObjectError::InvalidObjectLiteral(plan.node))?;
    if !store.try_reserve_types(1)
        || !store.try_reserve_checker_symbol_allocations(plan.properties.len(), 1)
    {
        return Err(PropertyObjectError::Capacity(plan.node));
    }

    let members = store.alloc_symbol_table();
    let mut cloned_properties = Vec::with_capacity(plan.properties.len());
    for ((property, property_type), data) in plan
        .properties
        .iter()
        .zip(property_types)
        .zip(cloned_symbol_data)
    {
        let cloned = store
            .alloc_symbol(data)
            .expect("the object-literal plan validated clone provenance");
        let links = ValueSymbolLinks {
            resolved_type: Some(*property_type),
            target: Some(property.symbol),
            ..ValueSymbolLinks::default()
        };
        assert!(store.set_value_symbol_links(cloned, links));
        assert_eq!(
            store.insert_symbol(members, EscapedName::source(&property.name), cloned),
            Some(None)
        );
        cloned_properties.push(cloned);
    }
    let type_ = store
        .alloc_plain_object_type(object_flags, Some(plan.symbol))
        .expect("the object-literal plan validated its symbol");
    assert!(store.set_structured_type_members(
        type_,
        Some(members),
        (!cloned_properties.is_empty()).then_some(cloned_properties),
        None,
        None,
        None,
    ));
    let mut links = store
        .type_node_links(plan.node)
        .cloned()
        .unwrap_or_default();
    links.resolved_type = Some(type_);
    assert!(store.set_type_node_links(plan.node, links));
    Ok(type_)
}

#[cfg(test)]
mod generic_publication_tests {
    use ts_ast::{FileId, NodeData, NodeRef};
    use ts_binder::{
        BoundFile, CanonicalBinder, CanonicalModuleState, CanonicalNameResolverOptions,
        CanonicalSourceFileFacts, CanonicalSourceLanguage, EscapedName,
    };
    use ts_parser::{ParseResult, parse_source_file};

    use super::*;
    use crate::semantic::{
        IntrinsicBootstrapOptions, declared::get_declared_class_interface_or_type_parameter,
        production::GlobalMergeCompletion,
    };

    struct Fixture {
        parsed: ParseResult,
        file: FileId,
        bound: BoundFile,
        store: CanonicalTypeMapperStore,
        symbol: SemanticSymbolId,
    }

    fn fixture() -> Fixture {
        let parsed = parse_source_file("interface Box<T> { value: T; readonly label: string }");
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(3_701);
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source("\"/generic-publication.ts\""),
                    CanonicalSourceLanguage::TypeScript,
                    false,
                    CanonicalModuleState::Script,
                ),
            )
            .unwrap();
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
        let (symbols, mut files) = binder.finish().try_into_parts().unwrap();
        let bound = files.remove(&file).unwrap();
        let declaration =
            parsed
                .arena
                .iter()
                .find_map(|(node, record)| {
                    matches!(record.data, NodeData::InterfaceDeclaration(_))
                        .then_some(NodeRef::new(parsed.arena.id(), file, node))
                })
                .unwrap();
        let symbol = bound.symbol(declaration).unwrap();
        let mut store = CanonicalTypeMapperStore::from_symbol_store(symbols);
        assert!(
            store
                .register_source_file(&parsed.arena, parsed.source_file, file)
                .is_some()
        );
        store
            .initialize_intrinsic_bootstrap(IntrinsicBootstrapOptions::default())
            .unwrap();
        let globals = store.intrinsic_bootstrap().unwrap().globals;
        store.merge_global_symbol(globals, symbol).unwrap();
        Fixture {
            parsed,
            file,
            bound,
            store,
            symbol,
        }
    }

    fn object_fixture(source: &str) -> (Fixture, NodeRef) {
        let parsed = parse_source_file(source);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(3_705);
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source("\"/object-property-forms.ts\""),
                    CanonicalSourceLanguage::TypeScript,
                    false,
                    CanonicalModuleState::Script,
                ),
            )
            .unwrap();
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
        let (symbols, mut files) = binder.finish().try_into_parts().unwrap();
        let bound = files.remove(&file).unwrap();
        let object = parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::ObjectLiteralExpression).then_some(NodeRef::new(
                    parsed.arena.id(),
                    file,
                    node,
                ))
            })
            .expect("fixture contains an object literal");
        let symbol = bound.symbol(object).unwrap();
        let mut store = CanonicalTypeMapperStore::from_symbol_store(symbols);
        assert!(
            store
                .register_source_file(&parsed.arena, parsed.source_file, file)
                .is_some()
        );
        store
            .initialize_intrinsic_bootstrap(IntrinsicBootstrapOptions::default())
            .unwrap();
        (
            Fixture {
                parsed,
                file,
                bound,
                store,
                symbol,
            },
            object,
        )
    }

    fn host<'a>(parsed: &'a ParseResult, bound: &'a BoundFile) -> DeclaredTypeHost<'a> {
        DeclaredTypeHost::new_after_global_merge(
            [(&parsed.arena, bound)],
            GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
        )
        .unwrap()
    }

    fn prepare(fixture: &mut Fixture) -> (PropertyObjectPlan, TypeId, Vec<TypeId>) {
        let host = host(&fixture.parsed, &fixture.bound);
        let plan = plan_generic_interface(&fixture.store, &host, fixture.symbol).unwrap();
        let flags = fixture.store.symbol(fixture.symbol).unwrap().flags();
        let target = get_declared_class_interface_or_type_parameter(
            &mut fixture.store,
            &host,
            fixture.symbol,
            flags,
        )
        .unwrap()
        .unwrap();
        let TypeData::Interface(interface) = fixture.store.type_payload(target).unwrap().data()
        else {
            panic!("generic declaration must produce an interface target")
        };
        let parameter = interface.all_type_parameters.as_ref().unwrap()[0];
        let string = fixture.store.intrinsic_bootstrap().unwrap().string_type;
        (plan, target, vec![parameter, string])
    }

    type GenericPublicationState = (
        ObjectFlags,
        InterfaceTypeData,
        Vec<(CheckFlags, Option<ValueSymbolLinks>)>,
        usize,
        [usize; 26],
    );

    fn state(
        store: &CanonicalTypeMapperStore,
        plan: &PropertyObjectPlan,
        target: TypeId,
    ) -> GenericPublicationState {
        let record = store.type_payload(target).unwrap();
        let TypeData::Interface(interface) = record.data() else {
            panic!("generic declaration must retain its interface target")
        };
        (
            record.object_flags(),
            interface.clone(),
            plan.properties
                .iter()
                .map(|property| {
                    (
                        store.symbol(property.symbol).unwrap().check_flags(),
                        store.value_symbol_links(property.symbol).cloned(),
                    )
                })
                .collect(),
            store.symbol_store().symbol_table_len(),
            store.checker_link_allocated_lengths(),
        )
    }

    #[test]
    fn object_literals_plan_shorthand_and_literal_computed_property_names() {
        let (mut fixture, object) = object_fixture(concat!(
            "const property = 1; const value = { property, ",
            "[\"literal\"]: 1, [2]: \"number\", [`template`]: true, ",
            "[\"i\\u0307spanyol\"]: \"spanish\" };",
        ));
        let host = host(&fixture.parsed, &fixture.bound);
        let plan = plan_object_literal(&fixture.store, &host, object).unwrap();
        assert_eq!(
            plan.properties
                .iter()
                .map(|property| property.name.as_str())
                .collect::<Vec<_>>(),
            ["property", "literal", "2", "template", "i\u{307}spanyol"]
        );
        assert_eq!(plan.properties[0].type_node, plan.properties[0].name_node);
        assert_eq!(
            fixture
                .parsed
                .arena
                .get(plan.properties[0].declaration.node)
                .unwrap()
                .kind,
            SyntaxKind::ShorthandPropertyAssignment
        );
        assert!(plan.properties[1..].iter().all(|property| {
            fixture
                .parsed
                .arena
                .get(property.name_node.node)
                .is_some_and(|record| record.kind == SyntaxKind::ComputedPropertyName)
        }));

        let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
        let property_types = [
            bootstrap.number_type,
            bootstrap.number_type,
            bootstrap.string_type,
            bootstrap.boolean_type,
            bootstrap.string_type,
        ];
        let type_ = publish_object_literal(&mut fixture.store, &plan, &property_types).unwrap();
        assert_eq!(
            publish_object_literal(&mut fixture.store, &plan, &property_types),
            Ok(type_)
        );
    }

    #[test]
    fn dynamic_computed_object_property_names_stay_unsupported() {
        let (fixture, object) =
            object_fixture("const key = 'property'; const value = { [key]: 1 };");
        let host = host(&fixture.parsed, &fixture.bound);
        assert!(matches!(
            plan_object_literal(&fixture.store, &host, object),
            Err(PropertyObjectError::UnsupportedMember {
                kind: SyntaxKind::ComputedPropertyName,
                ..
            })
        ));
    }

    #[test]
    fn unresolved_generic_bases_are_rejected_before_declared_member_publication() {
        let mut fixture = fixture();
        let (plan, target, property_types) = prepare(&mut fixture);
        let before = state(&fixture.store, &plan, target);

        assert_eq!(
            publish_generic_interface_declared_members(
                &mut fixture.store,
                &plan,
                target,
                &property_types,
            ),
            Err(PropertyObjectError::InvalidCachedInterface {
                symbol: fixture.symbol,
                type_: target,
            })
        );
        assert_eq!(state(&fixture.store, &plan, target), before);
        assert_eq!(fixture.bound.file_id(), fixture.file);
    }

    #[test]
    fn generic_publication_rejects_invalid_plans_and_warm_member_state_atomically() {
        let mut fixture = fixture();
        let (plan, target, property_types) = prepare(&mut fixture);
        assert!(fixture.store.publish_interface_no_base_resolution(target));

        let mut invalid_plan = plan.clone();
        invalid_plan.properties[1].symbol = invalid_plan.properties[0].symbol;
        let before = state(&fixture.store, &plan, target);
        assert_eq!(
            publish_generic_interface_declared_members(
                &mut fixture.store,
                &invalid_plan,
                target,
                &property_types,
            ),
            Err(PropertyObjectError::InvalidCachedInterface {
                symbol: fixture.symbol,
                type_: target,
            })
        );
        assert_eq!(state(&fixture.store, &plan, target), before);

        assert_eq!(
            publish_generic_interface_declared_members(
                &mut fixture.store,
                &plan,
                target,
                &property_types,
            ),
            Ok(target)
        );
        let warm = state(&fixture.store, &plan, target);
        assert_eq!(
            publish_generic_interface_declared_members(
                &mut fixture.store,
                &plan,
                target,
                &property_types,
            ),
            Ok(target)
        );
        assert_eq!(state(&fixture.store, &plan, target), warm);

        let original_flags = fixture.store.type_payload(target).unwrap().object_flags();
        assert!(
            fixture
                .store
                .add_type_object_flags(target, ObjectFlags::MEMBERS_RESOLVED)
        );
        let poisoned = state(&fixture.store, &plan, target);
        assert_eq!(
            publish_generic_interface_declared_members(
                &mut fixture.store,
                &plan,
                target,
                &property_types,
            ),
            Err(PropertyObjectError::InvalidCachedInterface {
                symbol: fixture.symbol,
                type_: target,
            })
        );
        assert_eq!(state(&fixture.store, &plan, target), poisoned);
        assert!(fixture.store.set_type_object_flags(target, original_flags));
        assert_eq!(
            publish_generic_interface_declared_members(
                &mut fixture.store,
                &plan,
                target,
                &property_types,
            ),
            Ok(target)
        );
    }

    #[test]
    fn ambient_namespace_interfaces_keep_their_namespace_owner() {
        let parsed = parse_source_file(
            "declare namespace JSX { interface IntrinsicElements { div: string } }",
        );
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(3_702);
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source("\"/namespace-interface.ts\""),
                    CanonicalSourceLanguage::TypeScript,
                    false,
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
        store
            .register_source_file(&parsed.arena, parsed.source_file, file)
            .unwrap();
        store
            .initialize_intrinsic_bootstrap(IntrinsicBootstrapOptions::default())
            .unwrap();
        let globals = store.intrinsic_bootstrap().unwrap().globals;
        let locals = bound.locals(bound.source_file()).unwrap();
        let namespace = store
            .symbol_table(locals)
            .and_then(|locals| locals.get_source("JSX"))
            .unwrap();
        store.merge_global_symbol(globals, namespace).unwrap();
        let declaration =
            parsed
                .arena
                .iter()
                .find_map(|(node, record)| {
                    matches!(record.data, NodeData::InterfaceDeclaration(_))
                        .then_some(NodeRef::new(parsed.arena.id(), file, node))
                })
                .unwrap();
        let symbol = bound.symbol(declaration).unwrap();
        let host = host(&parsed, &bound);

        let plan = plan_interface(&store, &host, symbol).unwrap();
        assert_eq!(plan.symbol, symbol);
        assert_eq!(store.symbol(symbol).unwrap().parent(), Some(namespace));
    }

    #[test]
    fn reopened_namespace_interfaces_follow_the_merged_namespace_parent() {
        let first = parse_source_file("declare namespace JSX { interface Element {} }");
        let second = parse_source_file(
            "declare namespace JSX { interface IntrinsicElements { div: string } }",
        );
        assert!(first.diagnostics.is_empty(), "{:?}", first.diagnostics);
        assert!(second.diagnostics.is_empty(), "{:?}", second.diagnostics);
        let first_file = FileId::new(3_703);
        let second_file = FileId::new(3_704);
        let mut binder = CanonicalBinder::new();
        for (parsed, file, path) in [
            (&first, first_file, "\"/namespace-first.ts\""),
            (&second, second_file, "\"/namespace-second.ts\""),
        ] {
            binder
                .bind_source_file_with_facts(
                    &parsed.arena,
                    parsed.source_file,
                    file,
                    CanonicalSourceFileFacts::new(
                        EscapedName::source(path),
                        CanonicalSourceLanguage::TypeScript,
                        false,
                        CanonicalModuleState::Script,
                    ),
                )
                .unwrap();
        }
        for (parsed, file) in [(&first, first_file), (&second, second_file)] {
            binder
                .bind_typescript_declaration_slice(&parsed.arena, file)
                .unwrap();
        }
        let (symbols, mut files) = binder.finish().try_into_parts().unwrap();
        let first_bound = files.remove(&first_file).unwrap();
        let second_bound = files.remove(&second_file).unwrap();
        let mut store = CanonicalTypeMapperStore::from_symbol_store(symbols);
        for (parsed, file) in [(&first, first_file), (&second, second_file)] {
            store
                .register_source_file(&parsed.arena, parsed.source_file, file)
                .unwrap();
        }
        store
            .initialize_intrinsic_bootstrap(IntrinsicBootstrapOptions::default())
            .unwrap();
        let globals = store.intrinsic_bootstrap().unwrap().globals;
        let first_namespace = first_bound
            .locals(first_bound.source_file())
            .and_then(|locals| store.symbol_table(locals))
            .and_then(|locals| locals.get_source("JSX"))
            .unwrap();
        let second_namespace = second_bound
            .locals(second_bound.source_file())
            .and_then(|locals| store.symbol_table(locals))
            .and_then(|locals| locals.get_source("JSX"))
            .unwrap();
        store.merge_global_symbol(globals, first_namespace).unwrap();
        let merged_namespace = store
            .merge_global_symbol(globals, second_namespace)
            .unwrap();
        let declaration =
            second
                .arena
                .iter()
                .find_map(|(node, record)| {
                    matches!(record.data, NodeData::InterfaceDeclaration(_))
                        .then_some(NodeRef::new(second.arena.id(), second_file, node))
                })
                .unwrap();
        let symbol = second_bound.symbol(declaration).unwrap();
        let host = DeclaredTypeHost::new_after_global_merge(
            [(&first.arena, &first_bound), (&second.arena, &second_bound)],
            GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
        )
        .unwrap();

        assert_eq!(
            store.symbol(symbol).unwrap().parent(),
            Some(second_namespace)
        );
        assert_ne!(second_namespace, merged_namespace);
        assert_eq!(store.get_parent_of_symbol(symbol), Some(merged_namespace));
        let plan = plan_interface(&store, &host, symbol).unwrap();
        assert_eq!(plan.symbol, symbol);
    }
}
